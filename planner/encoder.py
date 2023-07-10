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

from z3 import *
from collections import defaultdict
from copy import deepcopy

from unified_planning.shortcuts import *
from unified_planning.engines import CompilationKind
from unified_planning.model.operators import *


import utils
import numpy as np
from . import loopformula

class Encoder:
    def __init__(self, task, modifier):
        self.task = task
        self.modifier = modifier

        self.ground_problem = self._ground()
        
        self.actions = deepcopy(self.ground_problem.actions)

        self.boolean_variables = defaultdict(dict)
        self.numeric_variables = defaultdict(dict)
        self.action_variables  = defaultdict(dict)
        

        self.problem_z3_variables = defaultdict(dict)

        self.all_problem_fluents = []

        if self.modifier.__class__.__name__ == "LinearModifier":
            self.mutexes = self._computeSerialMutexes()
        else:
            self.mutexes = self._computeParallelMutexes()
        
    def _ground(self):
        # Ground the task.

        with Compiler(problem_kind=self.task.kind, compilation_kind=CompilationKind.GROUNDING) as grounder:
            return grounder.compile(self.task, compilation_kind=CompilationKind.GROUNDING).problem
    
    def _computeSerialMutexes(self):
        """!
        Computes mutually exclusive actions for serial encodings,
        i.e., all actions are mutually exclusive

        @return mutex: list of tuples defining action mutexes
        """
        # Stores mutexes
        mutexes = []

        for a1 in self.ground_problem.actions:
            for a2 in self.ground_problem.actions:
                # Skip same action
                if not a1.name == a2.name:
                    mutexes.append((a1,a2))
        return mutexes

    def _computeParallelMutexes(self):
        """!
        Computes mutually exclusive actions:
        Two actions (a1, a2) are mutex if:
            - intersection pre_a1 and eff_a2 (or viceversa) is non-empty
            - intersection between eff_a1+ and eff_a2- (or viceversa) is non-empty
            - intersection between numeric effects is non-empty

        See, e.g., 'A Compilation of the Full PDDL+ Language into SMT'', Cashmore et al.

        @return mutex: list of tuples defining action mutexes
        """

        def get_add_del_effects(action):
            """!
            Returns a tuple (add, del) of lists of effects of the action
            """
            
            del_effects = []
            effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]

            add_effects = set([str(eff.fluent) for eff in effects_fluents if eff.value.is_true()])
            del_effects = set([str(eff.fluent) for eff in effects_fluents if not eff.value.is_true()])

            return (add_effects, del_effects)
        
        def get_numeric_effects(action):
            """!
            Returns a set of numeric effects of the action
            """            
            return set([str(effect.fluent) for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()])

        def get_preconditions(action):
            """!
            Returns a set of preconditions of the action
            """            
            preconditions = set()
            for pre in action.preconditions:
                for arg in pre.args:
                    if arg.node_type == OperatorKind.FLUENT_EXP:
                        preconditions.add(str(arg))
            return preconditions

        mutexes = set()
        
        for action_1 in self.ground_problem.actions:
            add_a1, del_a1 = get_add_del_effects(action_1)
            num_1 = get_numeric_effects(action_1)
            pre_1 = get_preconditions(action_1)

            for action_2 in self.ground_problem.actions:
                if not action_1.name == action_2.name:
                  
                    if action_1.name == 'authorize_d1_l1' and action_2.name == 'authorize_d1_l2':
                        print("debug")

                    add_a2, del_a2 = get_add_del_effects(action_2)
                    num_2 = get_numeric_effects(action_2)
                    pre_2 = get_preconditions(action_2)

                    ## Condition 1
                    if len(pre_1.intersection(add_a2)) > 0 or len(pre_1.intersection(del_a2)) > 0:
                        mutexes.add((action_1, action_2))

                    if len(pre_2.intersection(add_a1)) > 0 or len(pre_2.intersection(del_a1)) > 0:
                        mutexes.add((action_1, action_2))

                    ## Condition 2
                    if len(add_a1.intersection(del_a2)) > 0:
                        mutexes.add((action_1, action_2))
                    
                    if len(add_a2.intersection(del_a1)) > 0:
                        mutexes.add((action_1, action_2))

                    ## Condition 3
                    if num_1 & num_2:
                        mutexes.add((action_1, action_2))

                    pass

        return mutexes

    def createVariables(self):
        """!
        Creates state and action variables needed in the encoding.
        Variables are stored in dictionaries as follows:

        dict[step][variable_name] = Z3 variable instance

        """
        
        boolean_fluents = [f for f in self.ground_problem.fluents if f.type.is_bool_type()]
        for step in range(self.horizon+1):
            for fluent in boolean_fluents:
                self.boolean_variables[step][fluent.name] = z3.Bool('{}_{}'.format(fluent.name,step))
                self.problem_z3_variables[step][fluent.name] = z3.Bool('{}_{}'.format(fluent.name,step))

        
        # MF: I hate this but the only way to get the function and its variable through parsing the initial values for the 
        # numeric fluents.
        numeric_fluents = [f for f in self.ground_problem.initial_values if f.type.is_int_type() or f.type.is_real_type()]


        # The grounder does not replace the constants in the problem, therefore we can do that by listing the 
        # predicates that are not modified by any action.
        # We need to check the effects for each action and see if the predicate is modified.
        constant_fluents = [str(f) for f in numeric_fluents]
        for action in self.ground_problem.actions:
            for effect in action.effects:
                if effect.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
                    if str(effect.fluent) in constant_fluents:
                        constant_fluents.remove(str(effect.fluent))
        
        # TODO: get the values for those constants to replace them in the problem.

        # Now create z3 variables for the numeric fluents.
        for step in range(self.horizon+1):
            for fluent in numeric_fluents:
                if not str(fluent) in constant_fluents:
                    self.numeric_variables[step][str(fluent)] = z3.Real('{}_{}'.format(str(fluent),step))
                    self.problem_z3_variables[step][str(fluent)] = z3.Real('{}_{}'.format(str(fluent),step))

        self.all_problem_fluents.extend(boolean_fluents)
        self.all_problem_fluents.extend(numeric_fluents)


        # self.numeric_constants =
        x = self.ground_problem.initial_values[numeric_fluents[2]]
        
        for step in range(self.horizon+1):
            for action in self.ground_problem.actions:
                self.action_variables[step][action.name] = z3.Bool('{}_{}'.format(action.name,step))

        
    def encodeInitialState(self):
        """!
        Encodes formula defining initial state

        @return initial: Z3 formula asserting initial state
        """

        initial = []

        for fluent in self.ground_problem.initial_values:
            
            if fluent.type.is_bool_type():
                if self.ground_problem.initial_values[fluent].is_true():
                    initial.append(self.boolean_variables[0][str(fluent)])
                else:
                    initial.append(z3.Not(self.boolean_variables[0][str(fluent)]))
            elif fluent.type.is_int_type() or fluent.type.is_real_type():
                fluent_name = str(fluent)
                if fluent.node_type == OperatorKind.FLUENT_EXP:
                   initial.append(self.numeric_variables[0][fluent_name] == self.ground_problem.initial_values[fluent])
                else:
                    #throw an error
                    raise Exception("Fluent {} is not a fluent expression".format(fluent_name))
            else:
                # we skip initial facts that do not involve numeric fluents
                raise Exception("Fluent {} is not a boolean or numeric fluent".format(fluent_name))
        return initial

    def encodeGoalState(self):
        """!
        Encodes formula defining goal state

        @return goal: Z3 formula asserting propositional and numeric subgoals
        """
        return utils.inorderTraverse(self.ground_problem.goals, self.problem_z3_variables[self.horizon])
        
    def encodeActions(self):
        actions = []
        for step in range(self.horizon):
            for action in self.ground_problem.actions:
                # Append preconditions
                for pre in action.preconditions:
                    if pre.node_type in [OperatorKind.FLUENT_EXP, OperatorKind.NOT]:
                        fluent_name = str(pre.args[0])
                        if pre.node_type == OperatorKind.NOT:
                            actions.append(z3.Implies(self.action_variables[step][action.name], z3.Not(self.boolean_variables[step][fluent_name])))
                        else:
                            actions.append(z3.Implies(self.action_variables[step][action.name], self.boolean_variables[step][fluent_name]))
                    
                    elif pre.node_type in IRA_RELATIONS:
                        action_precondition_expr = utils.inorderTraverse(pre, self.problem_z3_variables[step])
                        actions.append(z3.Implies(self.action_variables[step][action.name], action_precondition_expr))

                    elif pre.node_type in [OperatorKind.AND, OperatorKind.OR]:
                        operand_list = []
                        for arg in pre.args:
                            if arg.node_type in [OperatorKind.FLUENT_EXP, OperatorKind.NOT]:
                                if arg.node_type == OperatorKind.NOT:
                                    operand_list.append(z3.Not(self.boolean_variables[step][str(arg.args[0])]))
                                else:
                                    operand_list.append(self.boolean_variables[step][str(arg)])
                            elif arg.node_type in IRA_RELATIONS:
                                operand_list.append(utils.inorderTraverse(arg, self.problem_z3_variables[step]))
                            else:
                                raise Exception("Unknown precondition type {}".format(arg.node_type))
                        
                        for ele in operand_list:
                            actions.append(z3.Implies(self.action_variables[step][action.name], ele))
                    else:
                        raise Exception("Unknown precondition type {}".format(pre.node_type))
                                   
                # Append add effects.
                for effect in action.effects:
                    if effect.kind == EffectKind.ASSIGN:
                        # Check if this effect is a boolean fluent.
                        fluent = str(effect.fluent)
                        is_boolean_fluent = fluent in self.boolean_variables[step]
                        if is_boolean_fluent:
                            # get the value of the fluent to know whether to add or remove it.
                            if effect.value.is_true():
                                actions.append(z3.Implies(self.action_variables[step][action.name], self.boolean_variables[step+1][fluent]))
                            else:
                                actions.append(z3.Implies(self.action_variables[step][action.name], z3.Not(self.boolean_variables[step+1][fluent])))
                        else:
                            actions.append(z3.Implies(self.action_variables[step][action.name], self.numeric_variables[step+1][fluent] == effect.value))
                    elif effect.kind in [EffectKind.INCREASE, EffectKind.DECREASE]:
                        fluent_name  = str(effect.fluent)
                        add_var_name = str(effect.value)

                        if effect.value.node_type in [OperatorKind.INT_CONSTANT, OperatorKind.REAL_CONSTANT]:
                            add_var = z3.Real(add_var_name)
                        else:
                            add_var = self.numeric_variables[step][add_var_name]

                        if effect.kind == EffectKind.INCREASE:
                            actions.append(z3.Implies(self.action_variables[step][action.name], self.numeric_variables[step+1][fluent_name] == self.numeric_variables[step][fluent_name] + add_var))
                        else:
                            actions.append(z3.Implies(self.action_variables[step][action.name], self.numeric_variables[step+1][fluent_name] == self.numeric_variables[step][fluent_name] - add_var))
                    else:
                        raise Exception("Unknown effect type {}".format(effect.kind))

                if len(action.conditional_effects) > 0:
                    raise Exception("Conditional effects are not supported yet")

        return actions

    def encodeFrame(self):
        """!
        Encode explanatory frame axioms: a predicate retains its value unless
        it is modified by the effects of an action.

        @return frame: list of frame axioms
        """

        frame = []

        # Create new object and use it as
        # inadmissible value to check if
        # variable exists in dictionary

        sentinel = object()

        for step in range(self.horizon):
            # Encode frame axioms for boolean fluents
            for fluent in self.all_problem_fluents:
                if fluent.type.is_bool_type():
                    fluent_pre  = self.boolean_variables[step].get(fluent.name, sentinel)
                    fluent_post = self.boolean_variables[step+1].get(fluent.name, sentinel)
                    # Encode frame axioms only if atoms have SMT variables associated
                    if fluent_pre is not sentinel and fluent_post is not sentinel:
                        action_add = []
                        action_del = []

                        for action in self.ground_problem.actions:
                            effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]
                            
                            for ele in effects_fluents:
                                if str(ele.fluent) == fluent.name:
                                    if ele.value.is_true():
                                        action_add.append(self.action_variables[step][action.name])
                                    else:
                                        action_del.append(self.action_variables[step][action.name])

                        frame.append(z3.Implies(z3.And(z3.Not(fluent_pre),fluent_post),z3.Or(action_add)))
                        frame.append(z3.Implies(z3.And(fluent_pre,z3.Not(fluent_post)),z3.Or(action_del)))

                elif fluent.type.is_int_type() or fluent.type.is_real_type():
                    fluent_pre  = self.numeric_variables[step].get(str(fluent), sentinel)
                    fluent_post = self.numeric_variables[step+1].get(str(fluent), sentinel)
                    if fluent_pre is not sentinel and fluent_post is not sentinel:
                        action_num = []
                        for action in self.ground_problem.actions:
                            effects_fluents = [effect for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()]
                            for ele in effects_fluents:
                                if str(ele.fluent) == str(fluent):
                                    action_num.append(self.action_variables[step][action.name])
                            
                        #TODO
                        # Can we write frame axioms for num effects in a more
                        # efficient way?
                        frame.append(z3.Or(fluent_post == fluent_pre, z3.Or(action_num)))
                else:
                    raise Exception("Unknown fluent type {}".format(fluent.type))

        return frame

    def encodeExecutionSemantics(self):
            """!
            Encodes execution semantics as specified by modifier class.

            @return axioms that specify execution semantics.
            """
            
            try:
                return self.modifier.do_encode(self.action_variables, self.horizon)
            except:
                return self.modifier.do_encode(self.action_variables, self.mutexes, self.horizon)

class EncoderSMT(Encoder):
    """
    Class that defines method to build SMT encoding.
    """

    def encode(self,horizon):
        """!
        Builds SMT encoding.

        @param horizon: horizon for bounded planning formula.
        @return formula: dictionary containing subformulas.
        """

        # initialize horizon
        self.horizon = horizon

        # Create variables
        self.createVariables()

        # Start encoding formula

        formula = defaultdict(list)

        # Encode initial state axioms

        formula['initial'] = self.encodeInitialState()

        # Encode goal state axioms

        formula['goal'] = self.encodeGoalState()

        # Encode universal axioms

        formula['actions'] = self.encodeActions()

        # Encode explanatory frame axioms

        formula['frame'] = self.encodeFrame()

        # Encode execution semantics (lin/par)

        formula['sem'] = self.encodeExecutionSemantics()

        return formula

class EncoderOMT(Encoder):
    """
    Class that defines method to build SMT encoding.
    """
    def encodeObjective(self):
        """!
        Encodes objective function. If domain is metric it builds a Z3 formula
        encoding the metric, otherwise it builds a pseudoboolean objective
        (i.e., we pay one each time an action is executed).

        @return objective: objective function.
        """

        if self.task.metric:
             objective = utils.buildMetricExpr(self)

        else:
            objective = []
            for step in range(self.horizon):
                for action in self.action_variables[step].values():
                    objective.append(If(action,1.0,0.0))

            objective = sum(objective)

        return objective

    def createAuxVariables(self):
        """
        Creates auxiliary variables used in relaxed suffix (see related paper).

        """

        # create relaxed state variables: x -> tx
        self.touched_variables = dict()

        step = self.horizon + 1

        for var_name in self.boolean_variables[0].keys():
            self.touched_variables[var_name] = Bool('t{}_{}'.format(var_name,self.horizon+1))

        for var_name in self.numeric_variables[0].keys():
            if not var_name in self.var_objective:
                self.touched_variables[var_name] = Bool('t{}_{}'.format(var_name,self.horizon+1))

        # create sets of relaxed action variables for
        # steps n, n+1

        self.auxiliary_actions = defaultdict(dict)

        for step in range(self.horizon,self.horizon+2):
            for action in self.actions:
                self.auxiliary_actions[step][action.name] = Bool('{}_{}'.format(action.name,step))

    def encodeRelaxedActions(self):
        """!
        Encodes relaxed universal axioms.

        @return relax: list of Z3 formulas
        """

        # dictionary used to store variables corresponding to concrete costs
        # at last step n

        self.final_costs = defaultdict(list)

        # list of relaxed universal axioms
        relax = []

        step = self.horizon

        for action in self.actions:

            # Encode concrete preconditions
            for pre in action.condition:
                if utils.isBoolFluent(pre):
                    var_name = utils.varNameFromBFluent(pre)
                    if pre.negated:
                        relax.append(Implies(self.auxiliary_actions[step][action.name],Not(self.boolean_variables[step][var_name])))
                    else:
                        relax.append(Implies(self.auxiliary_actions[step][action.name],self.boolean_variables[step][var_name]))

                elif isinstance(pre, pddl.conditions.FunctionComparison):
                    expr = utils.inorderTraversalFC(self,pre,self.numeric_variables[step])
                    relax.append(Implies(self.auxiliary_actions[step][action.name],expr))

                else:
                    raise Exception('Precondition \'{}\' of type \'{}\' not supported'.format(pre,type(pre)))

            # Encode abstract add effects
            for add in action.add_effects:
                if len(add[0]) == 0:
                    relax.append(Implies(self.auxiliary_actions[step][action.name],self.touched_variables[utils.varNameFromBFluent(add[1])]))
                elif len(add[0]) == 1:
                    relax.append(Implies(self.auxiliary_actions[step][action.name],self.touched_variables[utils.varNameFromBFluent(add[1])]))
                else:
                    raise Exception(' Action {} contains add effect not supported'.format(action.name))


            # Encode abstract delete effects
            for de in action.del_effects:
                if len(de[0]) == 0:
                    relax.append(Implies(self.auxiliary_actions[step][action.name], self.touched_variables[utils.varNameFromBFluent(de[1])]))
                elif len(de[0]) == 1:
                    relax.append(Implies(self.auxiliary_actions[step][action.name], self.touched_variables[utils.varNameFromBFluent(de[1])]))
                else:
                    raise Exception(' Action {} contains del effect not supported'.format(action.name))


            # Encode  abstract numeric effects

            for ne in action.assign_effects:
                if len(ne[0]) == 0:
                    if isinstance(ne[1], pddl.f_expression.FunctionAssignment):

                        ## Numeric effects have fluents on the left and either a const, a fluent
                        ## or a complex numeric expression on the right

                        ## Handle left side
                        # retrieve variable name
                        var_name = utils.varNameFromNFluent(ne[1].fluent)
                        if not var_name in self.var_objective:
                            relax.append(Implies(self.auxiliary_actions[step][action.name],self.touched_variables[var_name]))
                        else:

                            ## Handle right side

                            if ne[1].expression in self.numeric_fluents and not ne[1].expression.symbol.startswith('derived!'): ##don't consider variables added by TFD
                                # right side is a simple fluent
                                var_name = utils.varNameFromNFluent(ne[1].expression)
                                expr = self.numeric_variables[step][var_name]
                            else:
                                # retrieve axioms corresponding to expression
                                numeric_axiom = self.axioms_by_name[ne[1].expression]
                                # build SMT expression
                                expr = utils.inorderTraversal(self,numeric_axiom, self.numeric_variables[step])

                            self.final_costs[action.name].append(expr)

                    else:

                        raise Exception('Numeric effect {} not supported yet'.format(ne[1]))
                else:
                    raise Exception('Numeric conditional effects not supported yet')

        return relax

    def encodeTransitiveClosure(self):
        """!
        Encodes computation of transitive closure at step n+1  (see related paper).

        @return trac: Z3 formulas that encode computation of transitive closure.
        """

        trac = []

        step = self.horizon+1

        for action in self.actions:

            # Encode relaxed preconditions
            for pre in action.condition:

                if utils.isBoolFluent(pre):
                    var_name = utils.varNameFromBFluent(pre)
                    if pre.negated:
                        trac.append(Implies(self.auxiliary_actions[step][action.name],Or(Not(self.boolean_variables[step-1][var_name]),self.touched_variables[var_name])))
                    else:
                        trac.append(Implies(self.auxiliary_actions[step][action.name],Or(self.boolean_variables[step-1][var_name],self.touched_variables[var_name])))

                elif isinstance(pre, pddl.conditions.FunctionComparison):
                    expr = utils.inorderTraversalFC(self,pre,self.numeric_variables[step-1])

                    # extract touched variables
                    tvariables = []

                    for var_name in utils.extractVariablesFC(self,pre):
                        tvariables.append(self.touched_variables[var_name])

                    trac.append(Implies(self.auxiliary_actions[step][action.name],Or(expr,Or(tvariables))))

                else:
                    raise Exception('Precondition \'{}\' of type \'{}\' not supported'.format(pre,type(pre)))


            # Encode relaxed add effects
            for add in action.add_effects:
                if len(add[0]) == 0:
                    trac.append(Implies(self.auxiliary_actions[step][action.name],self.touched_variables[utils.varNameFromBFluent(add[1])]))
                else:
                    raise Exception(' Action {} contains add effect not supported'.format(action.name))


            # Encode relaxed delete effects
            for de in action.del_effects:
                if len(de[0]) == 0:
                    trac.append(Implies(self.auxiliary_actions[step][action.name], self.touched_variables[utils.varNameFromBFluent(de[1])]))
                else:
                    raise Exception(' Action {} contains del effect not supported'.format(action.name))


            # Encode relaxed numeric effects

            for ne in action.assign_effects:
                if len(ne[0]) == 0:
                    if isinstance(ne[1], pddl.f_expression.FunctionAssignment):

                        ## Numeric effects have fluents on the left and either a const, a fluent
                        ## or a complex numeric expression on the right

                        ## Handle left side
                        # retrieve variable name
                        var_name = utils.varNameFromNFluent(ne[1].fluent)
                        if not var_name in self.var_objective:
                            trac.append(Implies(self.auxiliary_actions[step][action.name],self.touched_variables[var_name]))

                    else:

                        raise Exception('Numeric effect {} not supported yet'.format(ne[1]))
                else:
                    raise Exception('Numeric conditional effects not supported yet')

        # Encode frame for relaxed propositional state variables
        # see eq. 11 in related paper

        sentinel = object()

        for fluent in self.boolean_fluents:
            var_name = utils.varNameFromBFluent(fluent)

            # Exclude aux variables added by TFD parser

            if self.boolean_variables[0].get(var_name, sentinel) is not sentinel:

                action_eff= []

                for action in self.actions:
                    add_eff = [add[1] for add in action.add_effects]
                    if fluent in add_eff:
                        action_eff.append(self.auxiliary_actions[step][action.name])
                        action_eff.append(self.auxiliary_actions[step-1][action.name])

                    del_eff = [de[1] for de in action.del_effects]
                    if fluent in del_eff:
                        action_eff.append(self.auxiliary_actions[step][action.name])
                        action_eff.append(self.auxiliary_actions[step-1][action.name])


                trac.append(Implies(self.touched_variables[var_name], Or(action_eff)))

        # Encode frame for relaxed numeric state variables
        for fluent in self.numeric_fluents:
            var_name = utils.varNameFromNFluent(fluent)

            if not var_name in self.var_objective:

                ## Exclude aux variables added by TFD parser

                if self.numeric_variables[0].get(var_name, sentinel) is not sentinel:

                    action_num = []

                    for action in self.actions:
                        num_eff = [ne[1].fluent for ne in action.assign_effects]

                        if fluent in num_eff:
                            action_num.append(self.auxiliary_actions[step][action.name])
                            action_num.append(self.auxiliary_actions[step-1][action.name])


                    trac.append(Implies(self.touched_variables[var_name],  Or(action_num)))


        return trac

    def encodeRelaxedGoal(self):
        """!
        Encodes relaxed goals.

        @return goal: relaxed goal formula
        """


        def _encodeRelPropositionalGoals(goal=None):
            """
            Encodes relaxed propositional subgoals.
            """

            propositional_subgoal = []

            # UGLY HACK: we skip atomic propositions that are added
            # to handle numeric axioms by checking names.
            axiom_names = [axiom.name for axiom in self.task.axioms]

            # Doing this as I might be calling this method
            # if I find a propositional subgoal in numeric conditions
            # see method below...

            if goal is None:
                goal = self.task.goal

            # Check if goal is just a single atom
            if isinstance(goal, pddl.conditions.Atom):
                if not goal.predicate in axiom_names:
                    if goal in self.boolean_fluents:
                        var_name = utils.varNameFromBFluent(goal)
                        if  goal.negated:
                            propositional_subgoal.append(Or(Not(self.boolean_variables[self.horizon][var_name]), self.touched_variables[var_name]))
                        else:
                            propositional_subgoal.append(Or(self.boolean_variables[self.horizon][var_name],self.touched_variables[var_name]))

            # Check if goal is a conjunction
            elif isinstance(goal,pddl.conditions.Conjunction):
                for fact in goal.parts:
                    var_name = utils.varNameFromBFluent(fact)
                    if  fact.negated:
                        propositional_subgoal.append(Or(Not(self.boolean_variables[self.horizon][var_name]),self.touched_variables[var_name]))
                    else:
                        propositional_subgoal.append(Or(self.boolean_variables[self.horizon][var_name],self.touched_variables[var_name]))

            else:
                raise Exception('Propositional goal condition \'{}\': type \'{}\' not recognized'.format(goal, type(goal)))

            return propositional_subgoal


        def _encodeRelNumericGoals():
            """
            Encodes relaxed numeric subgoals.
            """

            numeric_subgoal = []

            for axiom in self.task.axioms:
                condition = axiom.condition

                if isinstance(condition, pddl.conditions.FunctionComparison):
                    expression = utils.inorderTraversalFC(self, condition, self.numeric_variables[self.horizon])

                    # extract touched variables
                    tvariables = []

                    for var_name in utils.extractVariablesFC(self,condition):
                        tvariables.append(self.touched_variables[var_name])

                    numeric_subgoal.append(z3.Or(expression, z3.Or(tvariables)))

                elif isinstance(condition, pddl.conditions.Conjunction):

                    for part in condition.parts:
                        # Apparently boolean subgoal may still end up
                        # in numeric condition objects...
                        if utils.isBoolFluent(part):
                            propositional_subgoal = _encodeRelPropositionalGoals(part)
                            for sg in propositional_subgoal:
                                numeric_subgoal.append(sg)
                        if isinstance(part,pddl.conditions.FunctionComparison):

                            expression = utils.inorderTraversalFC(self, part, self.numeric_variables[self.horizon])

                            # extract touched variables
                            tvariables = []

                            for var_name in utils.extractVariablesFC(self,part):
                                tvariables.append(self.touched_variables[var_name])

                            numeric_subgoal.append(z3.Or(expression, z3.Or(tvariables)))

                else:
                    raise Exception('Numeric goal condition not recognized')
            return numeric_subgoal


        propositional_subgoal = _encodeRelPropositionalGoals()
        numeric_subgoal = _encodeRelNumericGoals()

        rel_goal = z3.And(z3.And(propositional_subgoal),z3.And(numeric_subgoal))

        return rel_goal

    def encodeAdditionalCosts(self):
        """!
        Encodes costs for relaxed actions that may be executed in the suffix.
        At each step, we define a cost variables that is equal to the summation of
        pseudoboolean terms (if action is executed we pay a price -- see paper)

        @return sum of additional costs
        @return cost contraints
        """

        costs = []
        constraints = []

        for step in range(self.horizon,self.horizon+2):
            cost = z3.Real('add_cost_{}'.format(step))
            total = []
            for a,v in self.auxiliary_actions[step].items():
                if self.task.metric:
                    total.append(z3.If(v,1.0*sum(self.final_costs[a]),0.0))
                else:
                    total.append(z3.If(v,1.0,0.0))
            constraints.append(cost == sum(total))
            costs.append(cost)

        constraints = z3.And(constraints)

        return sum(costs), constraints

    def encodeASAP(self):
        """!
        Encodes constraints that push execution of actions as early as possible.

        @return list of Z3 formulas.
        """

        # ASAP constraint are enforced both for concrete and relaxed actions
        all_actions  = self.action_variables.copy()
        all_actions.update(self.auxiliary_actions)


        c = []

        for step in range(self.horizon+1):
            for action in self.actions:
                # Condition 1: action already executed at
                # previous step

                act_pre = all_actions[step][action.name]

                # Condition 2: one of the prec of action was violated
                violated = []

                for pre in action.condition:
                    if utils.isBoolFluent(pre):
                        var_name = utils.varNameFromBFluent(pre)
                        if pre.negated:
                            violated.append(self.boolean_variables[step][var_name])
                        else:
                            violated.append(z3.Not(self.boolean_variables[step][var_name]))

                    elif isinstance(pre, pddl.conditions.FunctionComparison):
                        expr = utils.inorderTraversalFC(self,pre,self.numeric_variables[step])
                        violated.append(z3.Not(expr))

                    else:
                        raise Exception('Precondition \'{}\' of type \'{}\' not supported'.format(pre,type(pre)))


                # Condition 3: a mutex was executed a previous step

                # return all actions that are in mutex with the
                # current action
                mutex = [(lambda t:  t[1] if t[0] == action else t[0])(t) for t in self.mutexes if action in t]
                # fetch action variable
                mutex_vars = [all_actions[step][a.name] for a in mutex]

                # ASAP constraint

                act_post = all_actions[step+1][action.name]

                c.append(z3.Implies(act_post, z3.Or( act_pre, z3.Or(violated), z3.Or(mutex_vars))))

        return c

    def encodeOnlyIfNeeded(self):
        """!
        Enforces that auxiliary variables can be executed only ifall steps before
        the suffix are filled with at least one action.

        @return list of Z3 constraints.
        """

        c = []

        for step in range(self.horizon,self.horizon+2):
            rel_a = self.auxiliary_actions[step].values()
            actions = []
            for index in range(self.horizon):
                actions.append(z3.Or(self.action_variables[index].values()))
            c.append(z3.Implies(z3.Or(rel_a), z3.And(actions)))

        return c

    def encode(self,horizon):
        """!
        Builds OMT encoding.

        @param horizon: horizon for bounded planning formula.
        @return formula: dictionary containing subformulas.
        """

        self.horizon = horizon

        # Create variables
        self.createVariables()

        # Start encoding formula

        formula = defaultdict(list)

        # Encode initial state axioms

        formula['initial'] = self.encodeInitialState()

        # Encode universal axioms

        formula['actions'] = self.encodeActions()

        # Encode explanatory frame axioms

        formula['frame'] = self.encodeFrame()

        # Encode execution semantics (lin/par)

        formula['sem'] = self.encodeExecutionSemantics()

        #
        # Encode relaxed suffix
        #

        self.var_objective = utils.parseMetric(self)

        # Create auxiliary variables

        self.createAuxVariables()

        # Encode objective function

        formula['objective'] = self.encodeObjective()

        # Encode relaxed transition T^R

        formula['tr'] = self.encodeRelaxedActions()

        # Encode transitive closure

        formula['tc'] = self.encodeTransitiveClosure()

        # Encode ASAP constraints

        formula['asap'] = self.encodeASAP()

        # Encode relaxed  goal state axioms

        goal = self.encodeGoalState()

        formula['real_goal'] = goal

        abstract_goal = self.encodeRelaxedGoal()

        formula['goal'] = Or(goal,abstract_goal)

        # Encode loop formula

        formula['lf'] = loopformula.encodeLoopFormulas(self)

        # Encode additional cost for relaxed actions

        add_objective, add_constraints = self.encodeAdditionalCosts()

        formula['objective'] = formula['objective'] + add_objective

        formula['additional_constraints'] = add_constraints

        # Perform relaxed actions only if previous steps are filled

        formula['oin'] = self.encodeOnlyIfNeeded()

        return formula
