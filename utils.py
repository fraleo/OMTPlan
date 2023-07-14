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
            

def get_planning_problems(BASE_DIR):
    

    domains = {}

    domains['fo-coutners'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters/domain.pddl', 
                              'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters/instances/instance_<ADD>.pddl',
                              'from': 2, 'to': 21, 'name': 'fo-counters'}

    domains['fo-counters-inv'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-inv/domain.pddl',
                                  'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-inv/instances/instance_<ADD>.pddl',
                                  'from': 2, 'to': 21, 'name': 'fo-counters-inv'}

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
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/depots/instances/instance_<ADD>.pddl',
                            'from': 1, 'to': 20, 'name': 'depots'}
    
    domains['rover-'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/rover/domain.pddl',
                         'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/rover/instances/pfile<ADD>.pddl',
                         'from': 1, 'to': 20, 'name': 'rover'}
    
    domains['satellite'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/simple/satellite/domain.pddl',
                            'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/simple/satellite/instances/pfile<ADD>.pddl',
                            'from': 1, 'to': 20, 'name': 'satellite'}

    planning_problems = []
    for domain in domains.keys():
        for i in range(domains[domain]['from'], domains[domain]['to']+1):
            domaininfo = {}
            domaininfo['name'] = domains[domain]['name']
            domaininfo['domain'] = domains[domain]['domain']
            domaininfo['instance'] = domains[domain]['instances-file-name'].replace('<ADD>', str(i))
            planning_problems.append(domaininfo)


    # # Do this one manual.
    # domains['fo-counters-rnd'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-rnd/domain.pddl',
    #                               'instances-file-name': 'pddl_examples/benchmarks_IJCAI20/linear/fo-counters-rnd/instances/instance_<ADD>.pddl',}

    # domains['fo-farmland'] = {'domain': 'pddl_examples/benchmarks_IJCAI20/linear/fo-farmland/domain.pddl',}
    # 'fo-sailing'

    return planning_problems


    # domains["benchmarks_IJCAI20"] = {"domains" : [
    #                                     {'domain': 'grid-round-2-strips/domain.pddl',      'instances-dir': 'grid-round-2-strips/instances/'},
    #                                     {'domain': 'logistics-round-1-strips/domain.pddl', 'instances-dir': 'logistics-round-1-strips/instances/'},
    #                                     {'domain': 'logistics-round-2-strips/domain.pddl', 'instances-dir': 'logistics-round-2-strips/instances/'}
    #                                    ]}

    # domains["ipc-2000"] = {"domains" : [
    #                                     {'domain': 'elevator-strips-simple-typed/domain.pddl', 'instances-dir': 'elevator-strips-simple-typed/instances/'},
    #                                     {'domain': 'freecell-strips-typed/domain.pddl',        'instances-dir': 'freecell-strips-typed/instances/'},
    #                                     {'domain': 'logistics-strips-typed/domain.pddl',       'instances-dir': 'logistics-strips-typed/instances/'}
    #                                 ]}

    # domains["ipc-2002"] = {"domains" : [
    #                                      {'domain': 'depots-strips-automatic/domain.pddl',    'instances-dir': 'depots-strips-automatic/instances/'}, 
    #                                      {'domain': 'driverlog-strips-automatic/domain.pddl', 'instances-dir': 'driverlog-strips-automatic/instances/'},  
    #                                      {'domain': 'rovers-strips-automatic/domain.pddl',    'instances-dir': 'rovers-strips-automatic/instances/'},
    #                                      {'domain': 'satellite-strips-automatic/domain.pddl', 'instances-dir': 'satellite-strips-automatic/instances/'},
    #                                      {'domain': 'zenotravel-strips-automatic/domain.pddl','instances-dir': 'zenotravel-strips-automatic/instances/'}
    #                                 ]}
    

    # domains["ipc-2004"] = {"domains" : [
    #                                      {'domain': 'airport-nontemporal-strips/domain.pddl',               'instances-dir': 'airport-nontemporal-strips/instances/'},
    #                                      {'domain': 'pipesworld-no-tankage-nontemporal-strips/domain.pddl', 'instances-dir': 'pipesworld-no-tankage-nontemporal-strips/instances/'},
    #                                      {'domain': 'pipesworld-tankage-nontemporal-strips/domain.pddl',    'instances-dir': 'pipesworld-tankage-nontemporal-strips/instances/'},
    #                                      {'domain': 'satellite-strips/domain.pddl',                         'instances-dir': 'satellite-strips/instances/'},
    #                                      {'domain': 'settlers-strips/domain.pddl',                          'instances-dir': 'settlers-strips/instances/'}
    #                                 ]}
    
    # domains["ipc-2006"] = {"domains" : [
    #                                      {'domain': 'openstacks-propositional/domain.pddl', 'instances-dir': 'openstacks-propositional/instances/'},
    #                                      {'domain': 'pathways-propositional/domain.pddl',   'instances-dir': 'pathways-propositional/instances/'},
    #                                      {'domain': 'storage-propositional/domain.pddl',    'instances-dir': 'storage-propositional/instances/'},
    #                                      {'domain': 'tpp-propositional/domain.pddl',        'instances-dir': 'tpp-propositional/instances/'},
    #                                      {'domain': 'trucks-propositional/domain.pddl',     'instances-dir': 'trucks-propositional/instances/'}
    #                                 ]}

    # domains["ipc-2008"] = {"domains" : [
    #                                      {'domain': 'elevator-sequential-satisficing-strips/domain.pddl',      'instances-dir': 'elevator-sequential-satisficing-strips/instances/'},
    #                                      {'domain': 'scanalyzer-3d-sequential-satisficing-strips/domain.pddl', 'instances-dir': 'scanalyzer-3d-sequential-satisficing-strips/instances/'},
    #                                      {'domain': 'sokoban-sequential-satisficing-strips/domain.pddl',       'instances-dir': 'sokoban-sequential-satisficing-strips/instances/'},
    #                                      {'domain': 'transport-sequential-satisficing-strips/domain.pddl',     'instances-dir': 'transport-sequential-satisficing-strips/instances/'},
    #                                      {'domain': 'woodworking-sequential-satisficing-strips/domain.pddl',   'instances-dir': 'woodworking-sequential-satisficing-strips/instances/'}
    #                                 ]}

    # domains["ipc-2011"] = {"domains" : [
    #                                      {'domain': 'barman-sequential-satisficing/domain.pddl',     'instances-dir': 'barman-sequential-satisficing/instances/'},
    #                                      {'domain': 'floor-tile-sequential-satisficing/domain.pddl', 'instances-dir': 'floor-tile-sequential-satisficing/instances/'},
    #                                      {'domain': 'no-mystery-sequential-satisficing/domain.pddl', 'instances-dir': 'no-mystery-sequential-satisficing/instances/'},
    #                                      {'domain': 'parking-sequential-satisficing/domain.pddl',    'instances-dir': 'parking-sequential-satisficing/instances/'},
    #                                      {'domain': 'tidybot-sequential-satisficing/domain.pddl',    'instances-dir': 'tidybot-sequential-satisficing/instances/'}
    #                                 ]}

    # domains["ipc-2014"] = {"domains" : [
    #                                      {'domain': 'child-snack-sequential-satisficing/domain.pddl',           'instances-dir': 'child-snack-sequential-satisficing/instances/'},
    #                                      {'domain': 'city-car-sequential-satisficing/domain.pddl',              'instances-dir': 'city-car-sequential-satisficing/instances/'},
    #                                      {'domain': 'genome-edit-distances-sequential-satisficing/domain.pddl', 'instances-dir': 'genome-edit-distances-sequential-satisficing/instances/'},
    #                                      {'domain': 'hiking-sequential-satisficing/domain.pddl',                'instances-dir': 'hiking-sequential-satisficing/instances/'},
    #                                      {'domain': 'maintenance-sequential-satisficing/domain.pddl',           'instances-dir': 'maintenance-sequential-satisficing/instances/'},
    #                                      {'domain': 'parking-sequential-satisficing/domain.pddl',               'instances-dir': 'parking-sequential-satisficing/instances/'}
    #                                  ]}
    # planning_problems = []
    # for year in domains.keys():
    #     for domain in domains[year]['domains']:
    #         instancesdir = os.path.join(args.pddl_instances_dir, year, 'domains', domain['instances-dir'])
    #         for (dirpath, dirnames, instancefiles) in walk(instancesdir):
    #             for filename in instancefiles:
    #                 problemfile = os.path.join(instancesdir, filename)
    #                 if not os.path.exists(problemfile):
    #                     print("problem file {} does not exist".format(problemfile))
    #                 if problemfile.endswith('.pddl'):
    #                     planning_problem                    = {}
    #                     planning_problem['problem-info']    = "{}-{}".format(domain['domain'].split(os.sep)[-2], filename.split(os.sep)[-1])
    #                     planning_problem['domain']          = os.path.join(args.pddl_instances_dir, year, 'domains', domain['domain'])
    #                     planning_problem['problem']         = problemfile
    #                     # Removing states for now to test the whole framework.
    #                     planning_problem['metrics']         = ["stability", "uniqueness", "states", "stability-uniqueness", "stability-states", "states-uniqueness", "stability-uniqueness-states"] #
    #                     planning_problem["aggregator"]      = "min"
    #                     planning_problem["similarity"]      = "false"
    #                     planning_problem["use-limits"]      = "true"
    #                     planning_problem["time-limit-mins"] = 45
    #                     planning_problem["memory-limit-gb"] = 6
    #                     planning_problem["dump-dir"]        = os.path.join(args.sandbox_dir, "Generated-plans",  year, domain['instances-dir'], filename)
    #                     planning_problem["extract-dir"]     = os.path.join(args.sandbox_dir, "Extracted-plans",  year, domain['instances-dir'], filename)
    #                     planning_problem["translate-dir"]   = os.path.join(args.sandbox_dir, "Translated-plans", year)
    #                     planning_problem["q"]               = 2
    #                     planning_problem["generate-k"]      = 3000
    #                     planning_problem["select-k"]        = 0
    #                     planning_problem["step-k"]          = 5
    #                     planning_problems.append(planning_problem)
    # return planning_problems        


