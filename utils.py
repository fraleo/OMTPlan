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
        if root[0].node_type == OperatorKind.OR:
            return z3.Or(subgoals) if len(subgoals) > 1 else subgoals[0]
        else:
            return z3.And(subgoals) if len(subgoals) > 1 else subgoals[0]
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
                # Check the var type if it is boolean or numeric
                if z3.is_bool(var):
                    return var if root.value.is_true() else z3.Not(var)
                value = inorderTraverse(root.value, z3_variable, step, numeric_constants, z3_touched_variables)
                return z3_variable[step+1][str(root.fluent)] == value
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
            if root.node_type == OperatorKind.OR:
                return z3.Or(operands)
            else:
                return z3.And(operands)
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
            if root.args[0].node_type == OperatorKind.FLUENT_EXP:
                return z3.Not(z3_variable[step][str(root.args[0])])
            else:
                return z3.Not(inorderTraverse(root.args[0], z3_variable, step, numeric_constants, z3_touched_variables))
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


def inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants):
    #if root is None,return
    if isinstance(root, list):
        subgoals = []
        arithmetic_subgoals = []
        boolean_subgoals = []

        for subgoal in root:
            _subgoal = inorderTraverseRHDEffect(subgoal, z3_variable, step, numeric_constants)
            if z3.is_bool(_subgoal):
                boolean_subgoals.append(_subgoal)
            else:
                arithmetic_subgoals.append(_subgoal)
            subgoals.append(_subgoal)
        return arithmetic_subgoals, boolean_subgoals
        
    elif isinstance(root, unified_planning.model.effect.Effect):
        if root.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
            operand_1 = inorderTraverse(root.fluent, z3_variable, step, numeric_constants)
            operand_2 = inorderTraverse(root.value,  z3_variable, step, numeric_constants)
            if root.kind == EffectKind.INCREASE:
                #self.numeric_variables[step+1][fluent_name] == self.numeric_variables[step][fluent_name] + add_var))
                return operand_1 + operand_2
            elif root.kind == EffectKind.DECREASE:
                return operand_1 - operand_2
            elif root.kind == EffectKind.ASSIGN:
                var = inorderTraverse(root.fluent, z3_variable, step, numeric_constants)
                # Check the var type if it is boolean or numeric
                if z3.is_bool(var):
                    return var if root.value.is_true() else z3.Not(var)
                # There is a bug here.
                value = inorderTraverse(root.value, z3_variable, step, numeric_constants)
                return value
    elif isinstance(root, unified_planning.model.fnode.FNode):
        return inorderTraverse(root, z3_variable, step, numeric_constants)
    else:
        raise Exception('Unknown type for effect')

def getArithBoolExprs(root, z3_variable, step, numeric_constants):

    arith_ret_list = []
    bool_ret_list = []
    arit_subgoals, bool_subgoals = inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants)

    # there is no clean way to know where this ele is a boolean or arithmetic expression.
    for ele in root:
        z3_ele = inorderTraverseRHDEffect(ele, z3_variable, step, numeric_constants)
        for arith_subgoal in arit_subgoals:
            try:
                if z3_ele == arith_subgoal:
                    arith_ret_list.append((getZ3VariableName(ele.fluent), arith_subgoal))
                    break
            except:
                break
        for bool_subgoal in bool_subgoals:
            try:
                if z3_ele == bool_subgoal:
                    bool_ret_list.append((getZ3VariableName(ele.fluent), bool_subgoal))
                    break
            except:
                break

    return arith_ret_list, bool_ret_list
    return inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants)

def flattenEffect(eff, ret_list):
    if len(eff.children()) == 0:
        ret_list.append(eff)
    else:
        for child in eff.children():
            flattenEffect(child, ret_list)
    return

def getActionNameFromZ3Variable(expr):
    return str(expr).split('_$')[1]

def createZ3NameFrom(expr1, expr2, step):
    expr1str = str(expr1).replace(' ','_')
    expr2str = str(expr2).replace(' ','_')
    return f'{expr1str}_${expr2str}_${step}'

def getAllOperandsInExpression(expr):
    operandsnames = set()
    collectOperandsInExpression(expr, operandsnames)
    return operandsnames

def parseZ3FormulaAndReturnReplacementVariables(formula, chain_variable_list):
    operandsnames = getAllOperandsInExpression(formula)
    return_list = []
    for operand in operandsnames:
        operand_last_creation = []
        for step, vars_queue in chain_variable_list.items():
            if operand in vars_queue:
                operand_last_creation.append(vars_queue[operand][-1])
        if len(operand_last_creation) > 0:
            return_list.append((operand, getZ3VariableFromExpressionWithName(formula, operand), operand_last_creation))
    return return_list

def getZ3VariableFromExpressionWithName(expr, varname):
    
    expr_children = [expr] if len(expr.children()) == 0 else expr.children()
    for idx, child in enumerate(expr_children):
        # First lets loop on the children
        if is_const(child) and getZ3VariableName(child) == varname:
            return child
        elif is_const(child) and not getZ3VariableName(child) == varname:
            continue
        else:
            ret = getZ3VariableFromExpressionWithName(child, varname)
            if ret is not None:
                return ret

def collectOperandsInExpression(expr, variables):
    if is_const(expr) and expr.decl().kind() == Z3_OP_UNINTERPRETED:
        variables.add(getZ3VariableName(expr))
    elif is_app(expr):
        for arg in expr.children():
            collectOperandsInExpression(arg, variables)

def createZ3Name(var, actionname, step):
    return f'{var}_${actionname}_${step}'

def getZ3VariableName(fluent):
    """!
    Returns Z3 variable name for a given fluent.

    @param fluent: PDDL fluent.
    @return Z3 variable name.
    """
    return str(fluent).split('_$')[0].replace('Not(','').replace('))',')')

def getZ3Effect(root, z3_variable, step, numeric_constants):
    z3effect = inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants)
    return (getZ3VariableName(z3effect), z3effect)



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
    
def printSMTFormula(formula,problem_name, dump_to_dir):
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

        with open(os.path.join(dump_to_dir,'{}.smt2').format(problem_name),'w') as fo:
            fo.write(solver.to_smt2())

def printOMTFormula(formula,problem_name, dump_to_dir):
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
        
        with open(os.path.join(dump_to_dir,'{}.smt2').format(problem_name),'w') as fo:
            fo.write(solver.sexpr())
            
def printR2EFormula(formula,problem_name, dump_to_dir):
    """!
    Prints R2E planning formula in SMT-LIB syntax.

    @param formula
    @param problem_name
    """

    print('Printing R2E formula to {}.smt2'.format(problem_name))

    solver = Solver()

    # Assert subformulas in solver
    for _, sub_formula in formula.items():
        solver.add(sub_formula)

    with open(os.path.join(dump_to_dir,'{}.smt2').format(problem_name),'w') as fo:
        fo.write(solver.to_smt2())


def get_planning_problems(BASE_DIR):
    

    domains = {}

    domains['fo-coutners'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters/domain.pddl', 
                              'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters/instances/instance_<ADD>.pddl',
                              'from': 2, 'to': 21, 'name': 'fo-counters'}

    domains['fo-counters-inv'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-inv/domain.pddl',
                                  'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-inv/instances/instance_<ADD>.pddl',
                                  'from': 2, 'to': 21, 'name': 'fo-counters-inv'}

    domains['fo-counters-rnd'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-rnd/domain.pddl',
                                  'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-rnd/instances/instance_<ADD>.pddl',
                                  'from': 1, 'to': 60, 'name': 'fo-counters-rnd'}

    domains['fo-farmland-1']   = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-farmland/domain.pddl',
                                  'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-farmland/instances-small/instance_<ADD>.pddl',
                                  'from': 1, 'to': 20, 'name': 'fo-farmland'} 

    domains['fo-farmland-2']   = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-farmland/domain.pddl',
                                  'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-farmland/instances-other/instance_<ADD>.pddl',
                                  'from': 1, 'to': 30, 'name': 'fo-farmland'} 

    domains['fo-sailing']      = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-sailing/domain.pddl',
                                    'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-sailing/instances/instance_<ADD>.pddl',
                                    'from': 1, 'to': 20, 'name': 'fo-sailing'}

    domains['rover-linear'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/rover-linear/domain.pddl', 
                               'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/rover-linear/instances/pfile<ADD>.pddl',
                               'from': 1, 'to': 10, 'name': 'rover-linear'}
    
    domains['tpp-metric'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/tpp-metric/domain.pddl',
                             'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/tpp-metric/instances/p<ADD>.pddl',
                             'from': 1, 'to': 10, 'name': 'tpp-metric'}
    
    domains['zenotravle-linear'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/zenotravel-linear/domain.pddl',
                                    'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/zenotravel-linear/instances/pfile<ADD>.pddl',
                                    'from': 1, 'to': 10, 'name': 'zenotravle-linear'}

    domains['counters'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/counters/domain.pddl', 
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/counters/instances/instance_<ADD>.pddl',
                            'from': 2, 'to': 9, 'name': 'counters'}
    
    domains['depots'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/depots/domain.pddl',
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/depots/instances/pfile<ADD>.pddl',
                            'from': 1, 'to': 20, 'name': 'depots'}
    
    domains['farmland'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/farmland/domain.pddl',
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/farmland/instances/instance_<ADD>.pddl',
                            'from': 1, 'to': 30, 'name': 'farmland'}

    domains['gardening'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/gardening/domain.pddl',
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/gardening/instances/instance_<ADD>.pddl',
                            'from': 1, 'to': 63, 'name': 'gardening'}

    domains['rover-simple'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/rover/domain.pddl',
                               'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/rover/instances/pfile<ADD>.pddl',
                               'from': 1, 'to': 20, 'name': 'rover'}
    
    domains['sailing'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/sailing/domain.pddl',
                          'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/sailing/instances/instance_<ADD>.pddl',
                          'from': 1, 'to': 20, 'name': 'sailing'}
    
    domains['satellite'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/satellite/domain.pddl',
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/satellite/instances/pfile<ADD>.pddl',
                            'from': 1, 'to': 20, 'name': 'satellite'}

    domains['zenotravel-small'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/zenotravel-small/domain.pddl',
                                   'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/zenotravel-small/instances/pfile<ADD>.pddl',
                                   'from': 1, 'to': 10, 'name': 'zenotravel'}

    domains['block-grouping'] = {'domain': 'selected_domains_ipc_23/block-grouping/domain.pddl',
                                 'instances-file-name': 'selected_domains_ipc_23/block-grouping/instances/instance_<ADD>.pddl',
                                 'from': 1, 'to': 20, 'name': 'block-grouping'}
    
    domains['delivery'] = {'domain': 'selected_domains_ipc_23/delivery/domain.pddl',
                           'instances-file-name': 'selected_domains_ipc_23/delivery/instances/prob<ADD>.pddl',
                           'from': 1, 'to': 20, 'name': 'delivery'}
    
    domains['drone'] = {'domain': 'selected_domains_ipc_23/drone/domain.pddl',
                        'instances-file-name': 'selected_domains_ipc_23/drone/instances/problem_<ADD>.pddl',
                        'from': 1, 'to': 20, 'name': 'drone'}

    domains['expedition'] = {'domain': 'selected_domains_ipc_23/expedition/domain.pddl',
                             'instances-file-name': 'selected_domains_ipc_23/expedition/instances/pfile<ADD>.pddl',
                             'from': 1, 'to': 20, 'name': 'expedition'}

    domains['ext-plant-watering'] = {'domain': 'selected_domains_ipc_23/ext-plant-watering/domain.pddl',
                                     'instances-file-name': 'selected_domains_ipc_23/ext-plant-watering/instances/instance_<ADD>.pddl',
                                     'from': 1, 'to': 20, 'name': 'ext-plant-watering'}
    
    domains['hydropower'] = {'domain': 'selected_domains_ipc_23/hydropower/domain.pddl',
                             'instances-file-name': 'selected_domains_ipc_23/hydropower/instances/pfile<ADD>.pddl',
                             'from': 1, 'to': 20, 'name': 'hydropower'}
    
    domains['markettrader'] = {'domain': 'selected_domains_ipc_23/markettrader/domain.pddl',
                               'instances-file-name': 'selected_domains_ipc_23/markettrader/instances/pfile<ADD>.pddl',
                               'from': 1, 'to': 20, 'name': 'markettrader'}

    domains['mprime-1'] = {'domain': 'selected_domains_ipc_23/mprime/domain.pddl',
                           'instances-file-name': 'selected_domains_ipc_23/mprime/instances/pfile<ADD>.pddl',
                           'from': 1, 'to': 11, 'name': 'mprime'}

    domains['mprime-2'] = {'domain': 'selected_domains_ipc_23/mprime/domain.pddl',
                           'instances-file-name': 'selected_domains_ipc_23/mprime/instances/pfile<ADD>.pddl',
                           'from': 20, 'to': 28, 'name': 'mprime'}

    domains['pathwaysmetric'] = {'domain': 'selected_domains_ipc_23/pathwaysmetric/domain.pddl',
                                 'instances-file-name': 'selected_domains_ipc_23/pathwaysmetric/instances/pfile<ADD>.pddl',
                                 'from': 2, 'to': 21, 'name': 'pathwaysmetric'}

    domains['settlers'] = {'domain': 'selected_domains_ipc_23/settlers/settlersnumeric/domain.pddl',
                           'instances-file-name': 'selected_domains_ipc_23/settlers/settlersnumeric/instances/pfile<ADD>.pddl',
                           'from': 3, 'to': 22, 'name': 'settlers'}

    domains['sugar'] = {'domain': 'selected_domains_ipc_23/sugar/domain.pddl',
                        'instances-file-name': 'selected_domains_ipc_23/sugar/instances/pfile<ADD>.pddl',
                        'from': 1, 'to': 20, 'name': 'sugar'}
    
    domains['tpp'] = {'domain': 'selected_domains_ipc_23/tpp/domain.pddl',
                      'instances-file-name': 'selected_domains_ipc_23/tpp/instances/p<ADD>.pddl',
                      'from': 2, 'to': 21, 'name': 'tpp'}

    planning_problems = []
    for domain in domains.keys():
        for i in range(domains[domain]['from'], domains[domain]['to']+1):
            domaininfo = {}
            domaininfo['name']     = domains[domain]['name']
            domaininfo['domain']   = os.path.join(BASE_DIR, domains[domain]['domain'])
            domaininfo['instance'] = os.path.join(BASE_DIR, domains[domain]['instances-file-name'].replace('<ADD>', str(i))) 
            if not os.path.exists(domaininfo['instance']) or not os.path.exists(domaininfo['domain']):
                raise Exception('File not found: ' + domaininfo['instance'] + ' or ' + domaininfo['domain'])
            planning_problems.append(domaininfo)

    return planning_problems



