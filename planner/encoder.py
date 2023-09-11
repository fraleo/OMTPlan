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
from collections import deque

from unified_planning.shortcuts import *
from unified_planning.engines import CompilationKind
from unified_planning.model.operators import *
from unified_planning.model.walkers import *


import utils
import numpy as np
from . import loopformula

class Encoder:
    def __init__(self, task, modifier):
        self.task = task
        self.modifier = modifier

        self.ground_problem = self._ground()

        self.boolean_variables = defaultdict(dict)
        self.numeric_variables = defaultdict(dict)
        self.action_variables  = defaultdict(dict)
        

        self.problem_z3_variables = defaultdict(dict)
        self.problem_constant_numerics = defaultdict(dict)

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
        
        # MF: I hate this but the only way to get grounded functions parsing the initial values

        boolean_fluents = [f for f in self.ground_problem.initial_values if f.type.is_bool_type()]
        for step in range(self.horizon+1):
            for fluent in boolean_fluents:
                fluentname = str(fluent)
                self.boolean_variables[step][fluentname] = z3.Bool('{}_{}'.format(fluentname,step))
                self.problem_z3_variables[step][fluentname] = z3.Bool('{}_{}'.format(fluentname,step))
        
        numeric_fluents = [f for f in self.ground_problem.initial_values if f.type.is_int_type() or f.type.is_real_type()]

        # The grounder does not replace the constants in the problem, therefore we can do that by listing the 
        # predicates that are not modified by any action.
        # We need to check the effects for each action and see if the predicate is modified.
        constant_fluents = [f for f in numeric_fluents]
        for action in self.ground_problem.actions:
            for effect in action.effects:
                if effect.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
                    if effect.fluent in constant_fluents:
                        constant_fluents.remove(effect.fluent)
        
        # Get the values for those constants to replace them in the problem.
        self.problem_constant_numerics = {}
        for fluent in constant_fluents:
            # A hacky way to ge the value of the constant.
            self.problem_constant_numerics[str(fluent)] = float(str(self.ground_problem.initial_values[fluent]))

        # Now create z3 variables for the numeric fluents.
        for step in range(self.horizon+1):
            for fluent in numeric_fluents:
                if not fluent in constant_fluents:
                    self.numeric_variables[step][str(fluent)] = z3.Real('{}_{}'.format(str(fluent),step))
                    self.problem_z3_variables[step][str(fluent)] = z3.Real('{}_{}'.format(str(fluent),step))
        for step in range(self.horizon+1):
            for action in self.ground_problem.actions:
                self.action_variables[step][action.name] = z3.Bool('{}_{}'.format(action.name,step))


        self.all_problem_fluents.extend(boolean_fluents)
        self.all_problem_fluents.extend(numeric_fluents)
        # Now remove constant fluents from all_problem_fluents.
        for fluent in constant_fluents:
            self.all_problem_fluents.remove(fluent)
        


    def encodeInitialState(self):
        """!
        Encodes formula defining initial state

        @return initial: Z3 formula asserting initial state
        """
        initial = []

        for fluent in self.ground_problem.initial_values:
            if str(fluent) in list(self.problem_constant_numerics.keys()):
                continue
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
        return utils.inorderTraverse(self.ground_problem.goals, self.problem_z3_variables, self.horizon, self.problem_constant_numerics)
        
    def encodeActions(self):

        actions = []
        new_actions = []
        for step in range(self.horizon):
            for action in self.ground_problem.actions:
                # Append preconditions
                for pre in action.preconditions:
                    precondition = utils.inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
                    actions.append(z3.Implies(self.action_variables[step][action.name], precondition))

                # Append effects.
                for effect in action.effects:
                    _eff = utils.inorderTraverse(effect, self.problem_z3_variables, step, self.problem_constant_numerics)
                    actions.append(z3.Implies(self.action_variables[step][action.name], _eff))
                    
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
                    fluent_pre  = self.boolean_variables[step].get(str(fluent), sentinel)
                    fluent_post = self.boolean_variables[step+1].get(str(fluent), sentinel)
                    # Encode frame axioms only if atoms have SMT variables associated
                    if fluent_pre is not sentinel and fluent_post is not sentinel:
                        action_add = []
                        action_del = []

                        for action in self.ground_problem.actions:
                            effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]
                            
                            for ele in effects_fluents:
                                if str(ele.fluent) == str(fluent):
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

        # set the planner name.
        self.name = "smt"

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

        objective = []
        if len(self.ground_problem.quality_metrics) > 0:
            for metric in deepcopy(self.ground_problem.quality_metrics):
                objective.append(utils.inorderTraverse(metric.expression, self.problem_z3_variables, self.horizon, self.problem_constant_numerics) )
        else:
            objective = []
            for step in range(self.horizon):
                for action in self.action_variables[step].values():
                    objective.append(z3.If(action,1.0,0.0))
        objective = sum(objective) if len(objective) > 0 else objective
        return objective
        
    def createAuxVariables(self):
        """
        Creates auxiliary variables used in relaxed suffix (see related paper).

        """

        # create relaxed state variables: x -> tx
        self.touched_variables = dict()

        step = self.horizon + 1

        for var_name in self.boolean_variables[0].keys():
            self.touched_variables[var_name] = z3.Bool('t{}_{}'.format(var_name,self.horizon+1))

        for var_name in self.numeric_variables[0].keys():
            self.touched_variables[var_name] = z3.Bool('t{}_{}'.format(var_name,self.horizon+1))

        # create sets of relaxed action variables for
        # steps n, n+1

        self.auxiliary_actions = defaultdict(dict)

        for step in range(self.horizon,self.horizon+2):
            for action in self.ground_problem.actions:
                self.auxiliary_actions[step][action.name] = z3.Bool('{}_{}'.format(action.name,step))

    def encodeRelaxedGoal(self):
        """!
        Encodes relaxed goals.

        @return goal: relaxed goal formula
        """
        return utils.inorderTraverse(self.ground_problem.goals, self.problem_z3_variables, self.horizon, self.problem_constant_numerics, self.touched_variables) 

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
                if len(self.ground_problem.quality_metrics) > 0:
                    total.append(z3.If(v,1.0*sum(self.final_costs[a]),0.0))
                else:
                    total.append(z3.If(v,1.0,0.0))
            constraints.append(cost == sum(total))
            costs.append(cost)

        constraints = z3.And(constraints)

        return sum(costs), constraints

    def encodeOnlyIfNeeded(self):
        """!
        Enforces that auxiliary variables can be executed only ifall steps before
        the suffix are filled with at least one action.

        @return list of Z3 constraints.
        """

        c = []

        for step in range(self.horizon,self.horizon+2):
            rel_a = list(self.auxiliary_actions[step].values())
            actions = []
            for index in range(self.horizon):
                actions.append(z3.Or(list(self.action_variables[index].values())))
            c.append(z3.Implies(z3.Or(rel_a), z3.And(actions)))

        return c

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

        for action in self.ground_problem.actions:
            # Append preconditions
            for pre in action.preconditions:
                precondition = utils.inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
                relax.append(z3.Implies(self.auxiliary_actions[step][action.name], precondition))
                                
            # Append effects.
            for effect in action.effects:
                if str(effect.fluent) in self.touched_variables:
                    relax.append(z3.Implies(self.auxiliary_actions[step][action.name], self.touched_variables[str(effect.fluent)]))
                
        return relax

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
            for action in self.ground_problem.actions:
                # Condition 1: action already executed at
                # previous step
                act_pre = all_actions[step][action.name]

                # Condition 2: one of the prec of action was violated
                violated = []

                # Append preconditions
                for pre in action.preconditions:
                    precondition = utils.inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
                    violated.append(z3.Not(precondition))
            
                # Condition 3: a mutex was executed a previous step
                # return all actions that are in mutex with the
                # current action
                mutex = [(lambda t:  t[1] if t[0] == action else t[0])(t) for t in self.mutexes if action in t]
                # fetch action variable
                mutex_vars = [all_actions[step][a.name] for a in mutex]

                # ASAP constraint
                act_post = all_actions[step+1][action.name]
                c.append(z3.Implies(act_post, z3.Or(act_pre, z3.Or(violated), z3.Or(mutex_vars))))

        return c

    def encodeTransitiveClosure(self):
        """!
        Encodes computation of transitive closure at step n+1  (see related paper).

        @return trac: Z3 formulas that encode computation of transitive closure.
        """
        trac = []
        step = self.horizon+1

        for action in self.ground_problem.actions:
            # Append preconditions
            for pre in action.preconditions:
                touched_vars = []
                for var in FreeVarsExtractor().get(pre):
                    if str(var) in self.touched_variables:
                        touched_vars.append(self.touched_variables[str(var)])
                precondition = utils.inorderTraverse(pre, self.problem_z3_variables, step-1, self.problem_constant_numerics)
                trac.append(z3.Implies(self.auxiliary_actions[step][action.name], z3.Or(precondition, z3.Or(touched_vars))))
            
            # Append effects.
            for effect in action.effects:
                if str(effect.fluent) in self.touched_variables:
                    trac.append(z3.Implies(self.auxiliary_actions[step][action.name], self.touched_variables[str(effect.fluent)]))
        
        sentinel = object()
        # Encode frame axioms for boolean fluents
        for fluent in self.all_problem_fluents:
            if fluent.type.is_bool_type():
                # Encode frame axioms only if atoms have SMT variables associated
                action_eff = []
                for action in self.ground_problem.actions:
                    effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]
                    
                    for ele in effects_fluents:
                        if str(ele.fluent) == str(fluent):
                            if ele.value.is_true():
                                action_eff.append(self.auxiliary_actions[step][action.name])
                                action_eff.append(self.auxiliary_actions[step-1][action.name])
                            else:
                                action_eff.append(self.auxiliary_actions[step][action.name])
                                action_eff.append(self.auxiliary_actions[step-1][action.name])
                trac.append(z3.Implies(self.touched_variables[str(fluent)], z3.Or(action_eff)))

            elif fluent.type.is_int_type() or fluent.type.is_real_type():
                action_num = []
                for action in self.ground_problem.actions:
                    effects_fluents = [effect for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()]
                    for ele in effects_fluents:
                        if str(ele.fluent) == str(fluent):
                            action_num.append(self.auxiliary_actions[step][action.name])
                            action_num.append(self.auxiliary_actions[step-1][action.name])                      
                trac.append(z3.Implies(self.touched_variables[str(fluent)], z3.Or(action_num)))
            else:
                raise Exception("Unknown fluent type {}".format(fluent.type))

        return trac
        
    def encode(self,horizon):
        """!
        Builds OMT encoding.

        @param horizon: horizon for bounded planning formula.
        @return formula: dictionary containing subformulas.
        """

        self.horizon = horizon

        # set the planner name.
        self.name = "omt"

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

        # Remove this for now.
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

        formula['goal'] = z3.Or(goal,abstract_goal)

        # Encode loop formula

        formula['lf'] = loopformula.encodeLoopFormulas(self) # This needs to be fixed.

        # Encode additional cost for relaxed actions

        add_objective, add_constraints = self.encodeAdditionalCosts()

        formula['objective'] = formula['objective'] + add_objective

        formula['additional_constraints'] = add_constraints

        # Perform relaxed actions only if previous steps are filled

        formula['oin'] = self.encodeOnlyIfNeeded()

        return formula


class R2EEncoding:
    def __init__(self, task, dump_models = False) -> None:
        self.task = task
        self.grounding_results = self._ground()
        self.ground_problem = self.grounding_results.problem

        self.z3_action_variables          = defaultdict(dict)
        self.z3_problem_variables         = defaultdict(dict)
        self.z3_problem_constant_numerics = defaultdict(dict)

        self.z3_chain_variables_actions   = defaultdict(dict)

        self.z3_variables = defaultdict(dict)
        self.z3_constants = defaultdict(dict)

        self.dump_models = dump_models
        
    def _ground(self):
        # Ground the task.
        with Compiler(problem_kind=self.task.kind, compilation_kind=CompilationKind.GROUNDING) as grounder:
            self.groundername = grounder.name    
            return grounder.compile(self.task, compilation_kind=CompilationKind.GROUNDING)

    def getAction(self, step, name):
        return self.z3_action_variables[step][name]
    
    def createVariables(self, start_step, end_step):

        # MF: I hate this but the only way to get grounded functions parsing the initial values
        boolean_fluents = [f for f in self.ground_problem.initial_values if f.type.is_bool_type()]
        for step in range(start_step, end_step+1):
            for fluent in boolean_fluents:
                fluentname = str(fluent)
                self.z3_problem_variables[step][fluentname] = z3.Bool('{}_${}'.format(fluentname,step))
        
        numeric_fluents = [f for f in self.ground_problem.initial_values if f.type.is_int_type() or f.type.is_real_type()]

        # The grounder does not replace the constants in the problem, therefore we can do that by listing the 
        # predicates that are not modified by any action.
        # We need to check the effects for each action and see if the predicate is modified.
        constant_fluents = [f for f in numeric_fluents]
        for action in self.ground_problem.actions:
            for effect in action.effects:
                if effect.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
                    if effect.fluent in constant_fluents:
                        constant_fluents.remove(effect.fluent)
        
        # Get the values for those constants to replace them in the problem.
        for fluent in constant_fluents:
            # A hacky way to ge the value of the constant.
            self.z3_problem_constant_numerics[str(fluent)] = float(str(self.ground_problem.initial_values[fluent]))

        # Now create z3 variables for the numeric fluents.
        for step in range(start_step, end_step+1):
            for fluent in numeric_fluents:
                if not fluent in constant_fluents:
                    self.z3_problem_variables[step][str(fluent)] = z3.Real('{}_${}'.format(str(fluent),step))

        # self.z3_variables
        variable_numeric_fluents = [f for f in self.ground_problem.initial_values if f.type.is_int_type() or f.type.is_real_type()]
        variable_numeric_fluents = [ele for ele in variable_numeric_fluents if ele not in constant_fluents]
        variable_boolean_fluents = [f for f in self.ground_problem.initial_values if f.type.is_bool_type()]

        fluents_used_in_actions = set()

        for step in range(start_step, end_step+1):
            for action in self.ground_problem.actions:
                self.z3_action_variables[step][action.name] = z3.Bool('{}_${}'.format(action.name,step))
                if step == 1:
                    for pre in action.preconditions:
                        precondition = utils.inorderTraverse(pre, self.z3_problem_variables, 0, self.z3_problem_constant_numerics)
                        utils.collectOperandsInExpression(precondition, fluents_used_in_actions)
                    for eff in action.effects:
                        effect = utils.inorderTraverse(eff, self.z3_problem_variables, 0, self.z3_problem_constant_numerics)
                        utils.collectOperandsInExpression(effect, fluents_used_in_actions)

        for var in variable_numeric_fluents:
            if str(var) in fluents_used_in_actions:
                self.z3_variables[str(var)] = z3.Real(str(var))
        for var in variable_boolean_fluents:
            if str(var) in fluents_used_in_actions:
                self.z3_variables[str(var)] = z3.Bool(str(var))

        for const in constant_fluents:
            self.z3_constants[str(const)] = z3.RealVal(float(str(self.ground_problem.initial_values[const])))
      
    def encodeInitialState(self):

        initial = []

        for fluent in self.ground_problem.initial_values:
            if str(fluent) in list(self.z3_problem_constant_numerics.keys()):
                continue
            if fluent.type.is_bool_type():
                if self.ground_problem.initial_values[fluent].is_true():
                    initial.append(self.z3_problem_variables[0][str(fluent)])
                else:
                    initial.append(z3.Not(self.z3_problem_variables[0][str(fluent)]))
            elif fluent.type.is_int_type() or fluent.type.is_real_type():
                fluent_name = str(fluent)
                if fluent.node_type == OperatorKind.FLUENT_EXP:
                   initial.append(self.z3_problem_variables[0][fluent_name] == self.ground_problem.initial_values[fluent])
                else:
                    #throw an error
                    raise Exception("Fluent {} is not a fluent expression".format(fluent_name))
            else:
                # we skip initial facts that do not involve numeric fluents
                raise Exception("Fluent {} is not a boolean or numeric fluent".format(fluent_name))
           
        return initial
    
    def encodeGoalState(self, horizon):

        # Collect the chain variables.
        gchainvars = []
        for varname, var in self.z3_problem_variables[horizon].items():
            if varname in self.z3_chain_variables_actions[horizon-1]:
                gchainvars.append((var, self.z3_chain_variables_actions[horizon-1][varname][-1]))

        chained_goal_predicates = []
        goalstate = utils.inorderTraverse(self.ground_problem.goals, self.z3_problem_variables, horizon, self.z3_problem_constant_numerics)
        goal_predicates = [goalstate] #if len(self.ground_problem.goals) == 1 else goalstate
        for g in goal_predicates:
            for chainvar in gchainvars:
                g = z3.substitute(g, chainvar)
            chained_goal_predicates.append(g)

        # Now we need to link those predicates to the t+1 variables in the chain encoding.
        return chained_goal_predicates

    def getActionsList(self):
        # Later, we can implement a function that returns the ordering of the actions which could be 
        # informative. But for now, we will return a sorted action names.
        return sorted([action for action in self.ground_problem.actions], key=lambda x: x.name)

    def getActionIndex(self, action):
        actionlist = [a.name for a in self.getActionsList()]
        return actionlist.index(action)

    def encodeActionsChain(self, start_step, end_step):
        
        actions_chain_encoding = []
        actions_ordering = self.getActionsList()

        # Create the variables for the first step
        if start_step == 0:
            for varname, var in self.z3_variables.items():
                if not isinstance(var.sort(), z3.z3.BoolSortRef) and not isinstance(var.sort(), z3.z3.ArithSortRef):
                    raise Exception("Variable {} is not a boolean or numeric variable".format(varname))
                if not varname in self.z3_chain_variables_actions[-1]:
                    self.z3_chain_variables_actions[-1][varname] = deque()
                    self.z3_chain_variables_actions[-1][varname].append(self.z3_problem_variables[0][varname])

        for step in range(start_step, end_step):
            for idx, action in enumerate(actions_ordering):

                for pre in action.preconditions:
                    precondition = utils.inorderTraverse(pre, self.z3_problem_variables, step, self.z3_problem_constant_numerics)
                    # Update the precondition with the new variables.
                    vars_to_update = utils.parseZ3FormulaAndReturnReplacementVariables(precondition, self.z3_chain_variables_actions)
                    for _varname, exprvar, newvar in vars_to_update:
                        precondition = z3.substitute(precondition, (exprvar, newvar[-1]))

                    # Commented out for debugging.
                    actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], precondition))

                replacement_vars    = []
                for effect in action.effects:
                    newVariableName = utils.getZ3VariableName(effect.fluent)
                    
                    # 1. Create a new variable with this action name in this step.
                    if not newVariableName in self.z3_chain_variables_actions[step]:
                        self.z3_chain_variables_actions[step][newVariableName] = deque()
                        
                    if isinstance(self.z3_chain_variables_actions[step-1][newVariableName][-1].sort(), z3.z3.ArithSortRef):
                        _effz3var = z3.Real('{}_${}_${}'.format(newVariableName,action.name,step))  
                    else:
                        _effz3var = z3.Bool('{}_${}_${}'.format(newVariableName,action.name,step))
                    
                    # append if the created variable is not the same as the previous one.
                    if len(self.z3_chain_variables_actions[step][newVariableName]) == 0 or not self.z3_chain_variables_actions[step][newVariableName][-1] == _effz3var:
                        self.z3_chain_variables_actions[step][newVariableName].append(_effz3var)

                    # 2. Then for the R.H.S of the effect expression, we need to update the variables with
                    # the chained ones if available in this step of the pervious one.
                    # We can create a tuple with the old variable with the new one.

                    _tmp, z3EffectValue  = utils.getZ3Effect(effect, self.z3_problem_variables, step, self.z3_problem_constant_numerics)
                    operands = [z3EffectValue] if len(z3EffectValue.children()) == 0 else z3EffectValue.children()

                    # There could be the case where one of the operands is an arithmetic operation.
                    # We need to check that and add it to the operands list.
                    _expanded_list = []
                    utils.flattenEffect(z3EffectValue, _expanded_list)
                    for operand in _expanded_list:
                        # This operand could have been created in this step of the pervious one.
                        # We need to check that.
                        operandname = utils.getZ3VariableName(operand)
                        if operandname in self.z3_chain_variables_actions[step]:
                            if operandname == newVariableName and len(self.z3_chain_variables_actions[step][operandname]) > 1:
                                # This is the variable we just created.
                                # We need to update the expression with the new variable.
                                replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step][operandname][-2]))
                            elif operandname == newVariableName and len(self.z3_chain_variables_actions[step][operandname]) == 1:
                                # This is the variable we just created.
                                # We need to update the expression with the new variable.
                                replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step-1][operandname][-1]))
                            else:
                                # This is a variable that was created in a previous step.
                                # We need to update the expression with the new variable.
                                replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step][operandname][-1]))
                        elif operandname in self.z3_chain_variables_actions[step-1]:
                            # This is a variable that was created in a previous step.
                            # We need to update the expression with the new variable.
                            replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step-1][operandname][-1]))

                arithemtic_exprs, boolean_expr = utils.getArithBoolExprs(action.effects, self.z3_problem_variables, step, self.z3_problem_constant_numerics)

                # Now it is much easier to replace the variables.

                for arithmetic_expr in arithemtic_exprs:
                    # collect all replace vars for this expression.
                    varname = arithmetic_expr[0]
                    expr = arithmetic_expr[1]
                    replace_expr_list = [var for var in replacement_vars if var[0] == arithmetic_expr[0]]
                    for _varname, oldvar, newvar in replace_expr_list:
                        expr = z3.substitute(expr, (oldvar, newvar))
                    # Now we need to add the expression to the chain encoding.
                    actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], self.z3_chain_variables_actions[step][varname][-1] == expr))

                    if len(self.z3_chain_variables_actions[step][varname]) > 1:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step][varname][-2]))
                    else:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step-1][varname][-1]))

                for boolean_expr in boolean_expr:
                    # collect all replace vars for this expression.
                    varname = boolean_expr[0]
                    expr = boolean_expr[1]
                    replace_expr_list = [var for var in replacement_vars if var[0] == boolean_expr[0]]
                    for _varname, oldvar, newvar in replace_expr_list:
                        expr = z3.substitute(expr, (oldvar, newvar))
                    # Now we need to add the expression to the chain encoding.
                    # For booleans the variable should be the same as the expression.
                    
                    if expr.decl().kind() == z3.Z3_OP_NOT:
                        actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], self.z3_chain_variables_actions[step][varname][-1] == z3.BoolVal(False)))
                    else:
                        actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], self.z3_chain_variables_actions[step][varname][-1] == z3.BoolVal(True)))
                    
                    # Chaining the varibale if the action is not enabled.
                    if len(self.z3_chain_variables_actions[step][varname]) > 1:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step][varname][-2]))
                    else:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step-1][varname][-1]))

        return actions_chain_encoding

    def incremental_encoding(self, horizon):

        start_index = 0 if len(self.z3_problem_variables) == 0 else len(self.z3_problem_variables)-1      

        formula = defaultdict(list)
        # Note that we add a +1 to the horizon since the first iteration creates the chain variables list.
        self.createVariables(start_index, horizon)

        # Encode actions chain axioms
        formula['actions'] = self.encodeActionsChain(start_index, horizon)

        # Encode initial state axioms at the first instance.
        formula['initial'] = self.encodeInitialState()

        # Encode goal state axioms
        formula['goal'] = self.encodeGoalState(horizon)

        if start_index == 0:
            self.formula = formula
        else:
            for key in self.formula:
                # Skip the initial case
                if key == 'initial':
                    continue
                # if goal state then update it with the new goal state
                elif key == 'goal':
                    self.formula[key] = formula[key]
                else:
                    self.formula[key].extend(formula[key])
        # We want to return the extedned version of the formula.
        return formula, self.formula
