##
# @file

############################################################################
##    This file is part of OMTPlan.
##
##    OMTPlan is free software: you can redistribute it and/or modify
##    it under the terms of the GNU General Public License as published by
##    the Free Software Foundation, either version 3 of the License, or
##    (at your option) any later version.
##
##    OMTPlan is distributed in the hope that it will be useful,
##    but WITHOUT ANY WARRANTY; without even the implied warranty of
##    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##    GNU General Public License for more details.
##
##    You should have received a copy of the GNU General Public License
##    along with OMTPlan.  If not, see <https://www.gnu.org/licenses/>.
############################################################################
import os
import re
from z3 import *
from unified_planning.model.operators import *
from unified_planning.model.walkers import *
# import translate.pddl as pddl

import unified_planning

try:
    basestring
except NameError:
    basestring = str

def getDomainName(task_filename):
    """!
    Tries to find PDDL domain file when only problem file is supplied.

    @param task_filename: path to PDDL problem file.

    @return domain_filename: path to PDDL domain, if found.
    """

    dirname, basename = os.path.split(task_filename)
    ## look for domain in folder or  folder up
    domain_filename = os.path.join(dirname, "domain.pddl")
    os.path.exists(domain_filename)
    if not os.path.exists(domain_filename):
      domain_filename = os.path.join(dirname, "../domain.pddl")
    if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
      domain_filename = os.path.join(dirname, basename[:4] + "domain.pddl")
    if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
      domain_filename = os.path.join(dirname, basename[:3] + "-domain.pddl")
    if not os.path.exists(domain_filename):
      raise SystemExit("Error: Could not find domain file using "
                       "automatic naming rules.")
    return domain_filename

def getValFromModel(assignment):
    """!
        Extracts values from Z3 model
        making sure types are properly
        converted.

        @param assigment: variable assignment with Z3 type.
        @returns variable assignment with Python type.
    """

    if is_true(assignment) or is_false(assignment):
        return assignment
    if is_int_value(assignment):
        return assignment.as_long()
    elif is_algebraic_value(assignment):
        proxy = assignment.approx(20)
        return float(proxy.numerator_as_long())/float(proxy.denominator_as_long())
    elif is_rational_value(assignment):
        return float(assignment.numerator_as_long())/float(assignment.denominator_as_long())
    else:
        raise Exception('Unknown type for assignment')

def varNameFromNFluent(fluent):
    """!
        Returns variable name used for encoding
        numeric fluents in SMT.

        @param fluent: Numeric PDDL fluent
        @returns Z3 variable name.
    """

    args = [arg.name for arg in fluent.args]

    if len(args) == 0:
        return fluent.symbol
    return '{}_{}'.format(fluent.symbol,'_'.join(args))

def varNameFromBFluent(fluent):
    """!
        Returns variable name used for encoding
        boolean fluents in SMT.

        @param fluent: Propositional PDDL fluent.
        @return Z3 variable name.
    """

    args = [arg.name for arg in fluent.args]
    if len(args) == 0:
        return fluent.predicate
    return '{}_{}'.format(fluent.predicate,  '_'.join(args))

def isBoolFluent(fluent):
    """!
    Checks if fluent is propositional.

    @param fluent: PDDL fluent.
    @return Truth value.
    """
    return fluent.node_type in [OperatorKind.NOT, OperatorKind.FLUENT_EXP]

def isNumFluent(fluent):
    """!
    Checks if fluent is numeric.

    @param fluent: PDDL fluent.
    @return Truth value.
    """
    return fluent.node_type in [OperatorKind.INT_CONSTANT, OperatorKind.REAL_CONSTANT]

def inorderTraverse(root, z3_variable, numeric_constants):
    #if root is None,return
    if isinstance(root, list):
        subgoals = []
        for subgoal in root:
            subgoals.append(inorderTraverse(subgoal, z3_variable, numeric_constants))
        if root[0].node_type == OperatorKind.AND:
            return z3.And(subgoals) if len(subgoals) > 1 else subgoals[0]
        else:
            return z3.Or(subgoals) if len(subgoals) > 1 else subgoals[0]
    elif root.node_type in [OperatorKind.AND, OperatorKind.OR]:
        operands = []
        for arg in root.args:
            operands.append(inorderTraverse(arg, z3_variable, numeric_constants))
        if root.node_type == OperatorKind.AND:
            return z3.And(operands)
        else:
            return z3.Or(operands)
    elif root.node_type == OperatorKind.EQUALS:
        operand_1 = inorderTraverse(root.args[0], z3_variable, numeric_constants)
        operand_2 = inorderTraverse(root.args[1], z3_variable, numeric_constants)
        return operand_1 - operand_2 == z3.RealVal(0)
    elif root.node_type in IRA_RELATIONS:
        operand_1 = inorderTraverse(root.args[0], z3_variable, numeric_constants)
        operand_2 = inorderTraverse(root.args[1], z3_variable, numeric_constants)

        if root.node_type == OperatorKind.LE:
            return operand_1 <= operand_2
        elif root.node_type == OperatorKind.LT:
            return operand_1 < operand_2
        else:
            raise Exception("Unknown relation {}".format(root.node_type))

        left_expr = None
        right_expr = None

        if isinstance(operand_1, z3.z3.ArithRef) and isinstance(operand_2, z3.z3.ArithRef):
            left_expr = operand_1
            right_expr = operand_2
        elif isinstance(operand_1, z3.z3.ArithRef) and isinstance(operand_2, z3.z3.RatNumRef):
            left_expr =  z3.RealVal('0')
            right_expr = operand_2 - operand_1
        else:
            left_expr = operand_1 - operand_2
            right_expr = z3.RealVal('0') 

        if root.node_type == OperatorKind.LE:
            return left_expr <= right_expr
        elif root.node_type == OperatorKind.LT:
            return left_expr < right_expr
        else:
            raise Exception("Unknown relation {}".format(root.node_type))
    elif root.node_type in IRA_OPERATORS:
        operands = []
        for arg in root.args:
            operands.append(inorderTraverse(arg, z3_variable, numeric_constants))
        if root.node_type == OperatorKind.PLUS:
            expression = operands[0] + operands[1]
            for i in range(2, len(operands)):
                expression += operands[i]
        elif root.node_type == OperatorKind.MINUS:
            expression = operands[0] - operands[1]
            for i in range(2, len(operands)):
                expression -= operands[i]
        elif root.node_type == OperatorKind.MUL:
            expression = operands[0] * operands[1]
            for i in range(2, len(operands)):
                expression *= operands[i]
        elif root.node_type == OperatorKind.DIV:
            expression = operands[0] / operands[1]
            for i in range(2, len(operands)):
                expression /= operands[i]
        else:
            raise Exception("Unknown operator {}".format(root.node_type))
        return expression
    # these two should be retreived from the elements we already computed.
    elif root.node_type == OperatorKind.NOT:
        return z3.Not(z3_variable[str(root.args[0])])
    elif root.node_type in [OperatorKind.BOOL_CONSTANT, OperatorKind.FLUENT_EXP]:
        if str(root) in list(numeric_constants.keys()):
            return z3.RealVal(numeric_constants[str(root)])
        else:
            return z3_variable[str(root)]
    elif root.node_type in [OperatorKind.INT_CONSTANT, OperatorKind.REAL_CONSTANT]:
        return z3.RealVal(root)
    else:
        raise Exception("Unknown operator {}".format(root.node_type))

def parseMetric(encoder):
    """!
    Extracts variables appearing in PDDL metric.

    @param encoder.
    @return var_names: list of fluents used in the mertic.

    """
    metric = encoder.ground_problem.quality_metrics
    var_names = set()
    extractor = NamesExtractor()
    for exp in metric:
        for f in extractor.extract_names(exp.expression):
            var_names.add(f)
    return list(var_names)
    
# TODO: We need to fix this.
def buildMetricExpr(encoder):
    """!
    Builds Z3 expression of PDDL metric.

    @param encoder: encoder object.
    @return metricExpr: Z3 expression encoding metric.
    """

    metric = encoder.task.metric[1]
    fluents = encoder.numeric_variables[encoder.horizon]

    def inorderTraversal(metric):
        op = metric[0]

        if op in ['+','-','*','/']:
            l_expr = inorderTraversal(metric[1])

            r_expr = inorderTraversal(metric[2])

            if op == '+':
                return l_expr + r_expr
            elif op == '-':
                return l_expr - r_expr
            elif op == '*':
                return l_expr * r_expr
            elif op == '/':
                return l_expr / r_expr
            else:
                raise Exception('Operator not recognized')
        else:
            if isinstance(metric,basestring):
                return float(metric)

            else:
                return fluents['_'.join(metric)]


    if len(metric) == 1:
        metricExpr =  fluents[metric[0]]
    else:
        metricExpr = inorderTraversal(metric)

    return  metricExpr




# TODO: We need to delete this.
def inorderTraversal(encoder,nax, numeric_variables):
        """!
        Traverses the parsed domain as returned by TFD parser:

        See "Using the Context-enhanced Additive Heuristic for Temporal and Numeric Planning", Eyerich et al.

        @param encode object.
        @param nax: numeric axioms returned by parser.
        @param numeric_variables: Z3 numeric variables.

        @return Z3 arithmetic expression (simple expression).
        """

        for layer, lst in encoder.axioms_by_layer.items():
            if nax in lst:
                break

        if layer < 0:
            # it's a const, we're good
            assert len(nax.parts) == 1
            return nax.parts[0].value

        elif layer == 0:
            # variable assignment

            assert len(nax.parts) == 2
            # one part contains PDDL function, i.e, SMT  variable
            # the other contains either a PDDL function or a const

            if nax.parts[0] in encoder.numeric_fluents and not nax.parts[1] in encoder.numeric_fluents:
                fluent = nax.parts[0]
                var_name = varNameFromNFluent(fluent)
                l_expr = numeric_variables[var_name]
                const_ax = nax.parts[1]
                r_expr = inorderTraversal(encoder,encoder.axioms_by_name[const_ax],numeric_variables)

            elif nax.parts[1] in encoder.numeric_fluents and not nax.parts[0] in encoder.numeric_fluents:
                fluent = nax.parts[1]
                var_name = varNameFromNFluent(fluent)
                r_expr = numeric_variables[var_name]
                const_ax = nax.parts[0]
                l_expr = inorderTraversal(encoder,encoder.axioms_by_name[const_ax],numeric_variables)

            elif nax.parts[0] in encoder.numeric_fluents and nax.parts[1] in encoder.numeric_fluents:
                ## fluent 1
                l_fluent = nax.parts[0]
                var_name = varNameFromNFluent(l_fluent)
                l_expr = numeric_variables[var_name]

                ## fluent 2
                r_fluent = nax.parts[1]

                var_name = varNameFromNFluent(r_fluent)
                r_expr = numeric_variables[var_name]
            else:
                raise Exception('Axiom {} not recognized.'.format(nax))


            if nax.op == '+':
                return l_expr + r_expr
            elif nax.op == '-':
                return l_expr - r_expr
            elif nax.op == '*':
                return l_expr * r_expr
            elif nax.op == '/':
                return l_expr / r_expr
            else:
                raise Exception('Operator not recognized')


        else:
            # complex expression
            # if part is just a fluent, retrieve the corresponding SMT variable
            # otherwise go down the graph

            if nax.parts[0] in encoder.numeric_fluents and not nax.parts[0].symbol.startswith('derived!'):
                var_name = varNameFromNFluent(nax.parts[0])
                l_expr = numeric_variables[var_name]
            else:
                l_expr = inorderTraversal(encoder,encoder.axioms_by_name[nax.parts[0]],numeric_variables)


            if nax.parts[1] in encoder.numeric_fluents and not nax.parts[1].symbol.startswith('derived!'):
                var_name = varNameFromNFluent(nax.parts[1])
                r_expr = numeric_variables[var_name]
            else:
                r_expr = inorderTraversal(encoder,encoder.axioms_by_name[nax.parts[1]],numeric_variables)


            if nax.op == '+':
                return l_expr + r_expr
            elif nax.op == '-':
                return l_expr - r_expr
            elif nax.op == '*':
                return l_expr * r_expr
            elif nax.op == '/':
                return l_expr / r_expr
            else:
                raise Exception('Operator not recognized')
# TODO: We need to delete this.
def inorderTraversalFC(encoder,condition, numeric_variables):
        """!
            Inorder traversal for Comparison axioms -- see "Using the Context-enhanced Additive Heuristic for Temporal and Numeric Planning", Eyerich et al.
            Internally relies on inorderTraversal().

            @param encoder
            @param codnition: numeric PDDL condition.
            @param numeric_variables: dictionary with Z3 variables

            @return Z3 arithmetic expression (comparison).


        """

        assert len(condition.parts) == 2

        # if part is just a fluent, retrieve the corresponding SMT variable
        # otherwise go down the graph

        ## HACKISH check to discard derived axioms


        if condition.parts[0] in encoder.numeric_fluents and not condition.parts[0].symbol.startswith('derived!'):
            var_name = varNameFromNFluent(condition.parts[0])
            l_expr = numeric_variables[var_name]
        else:
            l_expr = inorderTraversal(encoder,encoder.axioms_by_name[condition.parts[0]],numeric_variables)


        if condition.parts[1] in encoder.numeric_fluents and not condition.parts[1].symbol.startswith('derived!'):
            var_name = varNameFromNFluent(condition.parts[1])
            r_expr = numeric_variables[var_name]
        else:
            r_expr = inorderTraversal(encoder,encoder.axioms_by_name[condition.parts[1]],numeric_variables)


        if condition.comparator == '=':
            return l_expr == r_expr
        elif condition.comparator == '<':
            return l_expr < r_expr
        elif condition.comparator == '<=':
            return l_expr <= r_expr
        elif condition.comparator == '>':
            return l_expr > r_expr
        elif condition.comparator == '>=':
            return l_expr >= r_expr
        else:
            raise Exception('Comparator not recognized')
# TODO: We need to delete this.
def extractVariables(encoder,nax,variables):
        """!
        Extracts variables contained in PDDL numeric expressions.

        @param encoder.
        @param nax: numeric axioms returned by TFD.
        @param variables: dictionary containing Z3 variables.

        @return variables: list of Z3 variables.
        """

        for layer, lst in encoder.axioms_by_layer.items():
            if nax in lst:
                break

        if layer < 0:
            return
        elif layer == 0:
            # variable assignment

            assert len(nax.parts) == 2
            # one part contains PDDL function, i.e, SMT  variable
            # the other contains either a PDDL function or a const

            if nax.parts[0] in encoder.numeric_fluents and not nax.parts[1] in encoder.numeric_fluents:
                fluent = nax.parts[0]
                variables.append(varNameFromNFluent(fluent))
                return

            elif nax.parts[1] in encoder.numeric_fluents and not nax.parts[0] in encoder.numeric_fluents:
                fluent = nax.parts[1]
                variables.append(varNameFromNFluent(fluent))
                return

            elif nax.parts[0] in encoder.numeric_fluents and nax.parts[1] in encoder.numeric_fluents:
                ## fluent 1
                l_fluent = nax.parts[0]
                variables.append(varNameFromNFluent(l_fluent))

                ## fluent 2
                r_fluent = nax.parts[1]
                variables.append(varNameFromNFluent(r_fluent))
                return

            else:
                raise Exception('Axiom {} not recognized.'.format(nax))

        else:
            # complex expression
            # if part is just a fluent, retrieve the corresponding SMT variable
            # otherwise go down the graph

            if nax.parts[0] in encoder.numeric_fluents and not nax.parts[0].symbol.startswith('derived!'):
                variables.append(varNameFromNFluent(nax.parts[0]))

            else:
                extractVariables(encoder,encoder.axioms_by_name[nax.parts[0]],variables)

            if nax.parts[1] in encoder.numeric_fluents and not nax.parts[1].symbol.startswith('derived!'):
                variables.append(varNameFromNFluent(nax.parts[1]))

            else:
                extractVariables(encoder,encoder.axioms_by_name[nax.parts[1]],variables)
# TODO: We need to delete this.
def extractVariablesFC(encoder,condition):
    """!
    Extracts variables contained in PDDL comparison axioms.

    @param encoder.
    @param condition: PDDL comparison axiom.

    @return variables: list of Z3 variables.
    """
    c = condition

    variables = []


    assert len(c.parts) == 2

    # if part is just a fluent, retrieve the corresponding SMT variable
    # otherwise go down the graph
    if c.parts[0] in encoder.numeric_fluents and not c.parts[0].symbol.startswith('derived!'):
        variables.append(varNameFromNFluent(c.parts[0]))
    else:
        extractVariables(encoder,encoder.axioms_by_name[c.parts[0]],variables)


    if c.parts[1] in encoder.numeric_fluents and not c.parts[1].symbol.startswith('derived!'):
        variables.append(varNameFromNFluent(c.parts[1]))
    else:
        extractVariables(encoder,encoder.axioms_by_name[c.parts[1]],variables)

    return variables




def printSMTFormula(formula,problem_name):
        """!
        Prints SMT planning formula in SMT-LIB syntax.

        @param formula
        @param problem_name
        """

        print('Printing SMT formula to {}.smt2'.format(problem_name))

        solver = Solver()

        # Assert subformulas in solver
        for _, sub_formula in formula.items():
            solver.add(sub_formula)

        with open('{}.smt2'.format(problem_name),'w') as fo:
            fo.write(solver.to_smt2())

def printOMTFormula(formula,problem_name):
        """!
        Prints OMT planning formula in SMT-LIB syntax.

        @param formula
        @param problem_name
        """

        print('Printing OMT formula to {}.smt2'.format(problem_name))

        solver = Optimize()

        # Assert subformulas in solver
        for label, sub_formula in formula.items():
            if label == 'objective':
                solver.minimize(sub_formula)
            else:
                solver.add(sub_formula)


        # sexpr() behaves differently for class Optimize
        # and already prints what Solver prints when to_smt2
        # is called
        
        with open('{}.smt2'.format(problem_name),'w') as fo:
            fo.write(solver.sexpr())
            

        
