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
from unified_planning.shortcuts import *

import unified_planning

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

def inorderTraverse(root, z3_variable, step, numeric_constants, z3_touched_variables = None):
    #if root is None,return
    if isinstance(root, list):
        subgoals = []
        for subgoal in root:
            subgoals.append(inorderTraverse(subgoal, z3_variable, step, numeric_constants, z3_touched_variables))
        if root[0].node_type == OperatorKind.AND:
            return z3.And(subgoals) if len(subgoals) > 1 else subgoals[0]
        else:
            return z3.Or(subgoals) if len(subgoals) > 1 else subgoals[0]
    elif isinstance(root, unified_planning.model.effect.Effect):
        if root.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
            operand_1 = inorderTraverse(root.fluent, z3_variable, step, numeric_constants, z3_touched_variables)
            operand_2 = inorderTraverse(root.value,  z3_variable, step, numeric_constants, z3_touched_variables)
            if root.kind == EffectKind.INCREASE:
                #self.numeric_variables[step+1][fluent_name] == self.numeric_variables[step][fluent_name] + add_var))
                return z3_variable[step+1][str(root.fluent)] == operand_1 + operand_2
            elif root.kind == EffectKind.DECREASE:
                return z3_variable[step+1][str(root.fluent)] == operand_1 - operand_2
            elif root.kind == EffectKind.ASSIGN:
                var = inorderTraverse(root.fluent, z3_variable, step+1, numeric_constants, z3_touched_variables)
                return var if root.value.is_true() else z3.Not(var)
    elif isinstance(root, unified_planning.model.fnode.FNode):
        if root.node_type in [OperatorKind.AND, OperatorKind.OR]:
            operands = []
            for arg in root.args:
                if z3_touched_variables is not None:
                    subgoal_z3 = inorderTraverse(arg, z3_variable, step, numeric_constants, z3_touched_variables)
                    touched_variables = []
                    for sg_fluent in FreeVarsExtractor().get(arg):
                        if str(sg_fluent) in z3_touched_variables:
                            touched_variables.append(z3_touched_variables[str(sg_fluent)])
                    operands.append(z3.Or(subgoal_z3, z3.Or(touched_variables) if len(touched_variables) > 1 else touched_variables[0]))
                else:
                    operands.append(inorderTraverse(arg, z3_variable, step, numeric_constants, z3_touched_variables))
            if root.node_type == OperatorKind.AND:
                return z3.And(operands)
            else:
                return z3.Or(operands)
        elif root.node_type == OperatorKind.EQUALS:
            operand_1 = inorderTraverse(root.args[0], z3_variable, step, numeric_constants, z3_touched_variables)
            operand_2 = inorderTraverse(root.args[1], z3_variable, step, numeric_constants, z3_touched_variables)
            return operand_1 - operand_2 == z3.RealVal(0)
        elif root.node_type in IRA_RELATIONS:
            operand_1 = inorderTraverse(root.args[0], z3_variable, step, numeric_constants, z3_touched_variables)
            operand_2 = inorderTraverse(root.args[1], z3_variable, step, numeric_constants, z3_touched_variables)

            if root.node_type == OperatorKind.LE:
                return operand_1 <= operand_2
            elif root.node_type == OperatorKind.LT:
                return operand_1 < operand_2
            else:
                raise Exception("Unknown relation {}".format(root.node_type))
        elif root.node_type in IRA_OPERATORS:
            operands = []
            for arg in root.args:
                operands.append(inorderTraverse(arg, z3_variable, step, numeric_constants, z3_touched_variables))
            if root.node_type == OperatorKind.PLUS:
                expression = operands[0] + operands[1]
                for i in range(2, len(operands)):
                    expression += operands[i]
            elif root.node_type == OperatorKind.MINUS:
                expression = operands[0] - operands[1]
                for i in range(2, len(operands)):
                    expression -= operands[i]
            elif root.node_type == OperatorKind.TIMES:
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
            return z3.Not(z3_variable[step][str(root.args[0])])
        elif root.node_type in [OperatorKind.BOOL_CONSTANT, OperatorKind.FLUENT_EXP]:
            if str(root) in list(numeric_constants.keys()):
                return z3.RealVal(numeric_constants[str(root)])
            elif root.node_type == OperatorKind.BOOL_CONSTANT:
                return z3.BoolVal(root)
            else:
                return z3_variable[step][str(root)]
        elif root.node_type in [OperatorKind.INT_CONSTANT, OperatorKind.REAL_CONSTANT]:
            return z3.RealVal(root)
        else:
            raise Exception("Unknown operator {}".format(root.node_type))
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
            

        
