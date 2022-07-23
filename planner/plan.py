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
import subprocess


class Plan():

    def __init__(self):
        pass

    def _extractPlan(self, model, encoder):
        raise NotImplementedError

    def _extractCost(self, objective=None):
        """!
        Extracts cost of plan.

        @param objective: Z3 object that contains objective function (default None).

        @return cost: plan cost (metric value if problem is metric, plan length otherwise)
        """

        if objective:
            cost = objective.value()
        else:
            cost = len(self.plan)

        return cost


class SRPlan(Plan):
    """
    Plan objects are instances of this class.
    Defines methods to extract, validate and print plans.
    """

    def __init__(self, model, encoder, objective=None):
        super(SRPlan, self).__init__()

        self.plan = self._extractPlan(model, encoder)
        self.cost = self._extractCost(objective)

    def _extractPlan(self, model, encoder):
        """!
        Extracts plan from model of the formula.
        Plan returned is linearized.

        @param model: Z3 model of the planning formula.
        @param encoder: encoder object, contains maps variable/variable names.

        @return  plan: dictionary containing plan. Keys are steps, values are actions.
        """
        plan = {}
        index = 0

        ## linearize partial-order plan

        for step in range(encoder.horizon):
            for action in encoder.actions:
                if is_true(model[encoder.action_variables[step][action.name]]):
                    plan[index] = action.name
                    index = index + 1

        return plan

    def _extractCost(self, objective=None):
        """!
        Extracts cost of plan.

        @param objective: Z3 object that contains objective function (default None).

        @return cost: plan cost (metric value if problem is metric, plan length otherwise)
        """

        if objective:
            cost = objective.value()
        else:
            cost = len(self.plan)

        return cost

    def validate(self, val, domain, problem):
        """!
        Validates plan (when one is found).

        @param val: path to VAL executable.
        @param domain: path to PDDL domain file.
        @param problem: path to PDDL problem file.

        @return plan: string containing plan if plan found is valid, None otherwise.
        """

        from tempfile import NamedTemporaryFile

        print('Validating plan...')

        # Create string containing plan
        plan_to_str = '\n'.join('{}: {}'.format(key, val) for key, val in self.plan.items())

        # Create temporary file that contains plan to be
        # fed to VAL
        with NamedTemporaryFile(mode='w+') as temp:

            temp.write(plan_to_str)
            temp.seek(0)

            # Call VAL

            try:
                output = subprocess.check_output([val, domain, problem, temp.name])

            except subprocess.CalledProcessError as e:

                print('Unknown error, exiting now...')
                sys.exit()

        temp.close()

        # Prepare output depending on validation results

        plan = None

        if 'Plan valid' in output:
            plan = plan_to_str
            return plan
        else:
            return plan

    def pprint(self, dest):
        """!
        Prints plan to file.

        @param dest: path to destination folder.
        """

        # Default destination
        dest = dest + '/plan_file.txt'

        print('Printing plan to {}'.format(dest))

        # Create string containing plan

        plan_to_str = '\n'.join('{}: {}'.format(key, val) for key, val in self.plan.items())

        with open(dest, 'w') as f:
            f.write(plan_to_str)

    def general_failure_constraints_naive(self, model, encoder, plan, failed_step):
        """
        negate action under the same states
        """
        failed_action = encoder.action_variables[failed_step][plan[failed_step]]
        horizon_state = []
        for state in encoder.boolean_variables[failed_step].values():
            if model[state]:
                horizon_state.append(state)
            else:
                horizon_state.append(Not(state))
        # logger.info(f'naive general failure constraints')
        return [Implies(And(horizon_state), Not(failed_action))]

    def collision_generalization_constraints(self, objects, model, encoder, plan, failed_step):
        min_step = 0
        max_step = max(encoder.boolean_variables.keys())
        failed_action = encoder.action_variables[failed_step][plan[failed_step]]

        horizon_state = []
        horizon_action = []
        action_str = str(failed_action)[:-2]
        for i in range(max_step):
            horizon_state.append([])
            horizon_action.append(encoder.action_variables[int(i)][action_str])

        for state in encoder.boolean_variables[failed_step].values():
            state_str = str(state)[:-2]
            members = set(state_str.split('__'))
            if len(members.union(objects)) == 0:
                break
            for i in range(max_step):
                if model[state]:
                    horizon_state[i].append(encoder.boolean_variables[int(i)][state_str])
                else:
                    horizon_state[i].append(Not(encoder.boolean_variables[int(i)][state_str]))

        constraints = []
        for i in range(max_step):
            constraints.append(Implies(And(horizon_state[i]), Not(horizon_action[i])))
        return constraints

    # def general_failure_constraints(self, model, encoder, plan, failed_step):
    #     """
    #     negate action under the same states
    #     """
    #     min_step = 0
    #     max_step = max(encoder.boolean_variables.keys())
    #     failed_action = encoder.action_variables[failed_step][plan[failed_step]]
    #
    #     action_str = str(failed_action)[:str(failed_action).rfind('_')]
    #
    #     horizon_state = []
    #     horizon_action = []
    #     for i in range(max_step):
    #         horizon_state.append([])
    #         horizon_action.append(encoder.action_variables[int(i)][action_str])
    #
    #     for s in encoder.boolean_variables[failed_step].values():
    #         # state_str = str(s)[:-2]
    #         state_str = str(s)[:str(s).rfind('_')]
    #         for i in range(max_step):
    #             if model[s]:
    #                 horizon_state[i].append(encoder.boolean_variables[int(i)][state_str])
    #             else:
    #                 horizon_state[i].append(Not(encoder.boolean_variables[int(i)][state_str]))
    #
    #     constraints = []
    #     for i in range(max_step):
    #         constraints.append(Implies(And(horizon_state[i]), Not(horizon_action[i])))
    #     return constraints


class MRPlan(Plan):
    def __init__(self, model, encoder, objective=None):
        super(MRPlan, self).__init__()

        self.plan = self._extractPlan(model, encoder)
        self.cost = self._extractCost(objective)

    def _extractPlan(self, model, encoder):
        """!
        Extracts plan from model of the formula.
        Plan returned is parallel.

        @param model: Z3 model of the planning formula.
        @param encoder: encoder object, contains maps variable/variable names.

        @return  plan: dictionary containing plan. Keys are steps, values are actions.
        """
        plan = {}

        for step in range(encoder.horizon):
            for action in encoder.actions:
                if is_true(model[encoder.action_variables[step][action.name]]):
                    if step not in plan:
                        plan[step] = [action.name]
                    else:
                        plan[step].append(action.name)
        return plan

    def general_failure_constraints_naive(self, model, encoder, plan, failed_step):
        """
        negate action under the same states
        """
        failed_action_lst = [encoder.action_variables[failed_step][failed_sr_action]
                             for failed_sr_action in plan[failed_step]]
        horizon_state = []
        for state in encoder.boolean_variables[failed_step].values():
            if model[state]:
                horizon_state.append(state)
            else:
                horizon_state.append(Not(state))
        # logger.info(f'naive general failure constraints')
        return [Implies(And(horizon_state), Not(And(failed_action_lst)))]

    def task_plan_eliminate_constraints(self, model, encoder, plan, failed_step):
        """
        Add a constraint to eliminate the current plan.
        """
        each_step_action_selection = []
        for step in range(encoder.horizon):
            for current_step_action_var in encoder.action_variables[step].values():
                if model[current_step_action_var]:
                    each_step_action_selection.append(current_step_action_var)
                else:
                    each_step_action_selection.append(Not(current_step_action_var))

        return [Not(And(each_step_action_selection))]

    def process_action(self, action):
        args = action.strip()[1:-1].strip().split(' ')
        name = args[0]
        if 'handover' in name:
            pre_robot = args[1]
            manip_robot = args[2]
            movable = args[3]
            pre_grasp = args[4]
            manip_grasp = args[5]
            pre_region = args[6]
            manip_region = args[7]
        elif 'pickandplace' in name:
            pre_robot = args[1]
            manip_robot = args[1]
            movable = args[2]
            pre_grasp = args[3]
            manip_grasp = args[3]
            pre_region = args[4]
            manip_region = args[4]
        else:
            raise NotImplementedError("The action {} is not supported".format(name))

        return (pre_robot, movable, pre_grasp, pre_region), (manip_robot, movable, manip_grasp, manip_region)

    def informed_constraints(self, model, encoder, plan, failed_step, failure_info):
        # first we still use general constraints
        # For now, general failure constraints work better than task plan eliminate constraints
        # since it can find plans faster, although it has lower success rate.
        # constraints = self.general_failure_constraints_naive(model, encoder, plan, failed_step)
        constraints = []
        # constraints = self.task_plan_eliminate_constraints(model, encoder, plan, failed_step)
        # we then encode constraints in the failure info
        pre_mutexed_action_pairs, manip_mutexed_action_pairs, pre_never_actions, manip_never_actions, \
        pre_never_mr_actions, manip_never_mr_actions, pre_must_moved_movables, manip_must_moved_movables, \
        pre_mr_action_must_moved_movables, manip_mr_action_must_moved_movables = failure_info

        encoder.pre_mutexed_action_pairs.extend(pre_mutexed_action_pairs)
        encoder.manip_mutexed_action_pairs.extend(manip_mutexed_action_pairs)
        encoder.pre_never_actions.extend(pre_never_actions)
        encoder.manip_never_actions.extend(manip_never_actions)
        encoder.pre_never_mr_actions.extend(pre_never_mr_actions)
        encoder.manip_never_mr_actions.extend(manip_never_mr_actions)

        encoder.pre_must_moved_movables.update(pre_must_moved_movables)
        encoder.manip_must_moved_movables.update(manip_must_moved_movables)
        encoder.pre_mr_action_must_moved_movables.update(pre_mr_action_must_moved_movables)
        encoder.manip_mr_action_must_moved_movables.update(manip_mr_action_must_moved_movables)

        min_step = 0
        max_step = max(encoder.boolean_variables.keys())

        for i in range(min_step, max_step):
            # we first add mutexed actions constraints
            for pre_mutexed_action1, pre_mutexed_action2 in pre_mutexed_action_pairs:
                # we should find all actions that have the same pre action with pre_mutexed_action1
                # and all actions that have the same pre action with pre_mutexed_action2
                pre_info_m_a1, manip_info_m_a1 = self.process_action(pre_mutexed_action1)
                pre_info_m_a2, manip_info_m_a2 = self.process_action(pre_mutexed_action2)

                pre_mutexed_action1_lst = []
                pre_mutexed_action2_lst = []

                for action in encoder.actions:
                    pre_info_a, manip_info_a = self.process_action(action.name)

                    if pre_info_a == pre_info_m_a1:
                        pre_mutexed_action1_lst.append(action.name)
                    elif pre_info_a == pre_info_m_a2:
                        pre_mutexed_action2_lst.append(action.name)

                for pre_mutexed_action1_same in pre_mutexed_action1_lst:
                    for pre_mutexed_action2_same in pre_mutexed_action2_lst:
                        horizon_mutexed_action1_same = encoder.action_variables[int(i)][pre_mutexed_action1_same]
                        horizon_mutexed_action2_same = encoder.action_variables[int(i)][pre_mutexed_action2_same]
                        constraints.append(Implies(horizon_mutexed_action1_same, Not(horizon_mutexed_action2_same)))
                        constraints.append(Implies(horizon_mutexed_action2_same, Not(horizon_mutexed_action1_same)))

            # we then add never actions
            for pre_never_action in pre_never_actions:
                # first find all actions that have the same pre action with pre_never_action
                pre_info_n_a, _ = self.process_action(pre_never_action)

                for action in encoder.actions:
                    pre_info_a, _ = self.process_action(action.name)

                    if pre_info_a == pre_info_n_a:
                        horizon_never_action_same = encoder.action_variables[int(i)][action.name]
                        constraints.append(Not(horizon_never_action_same))

            for manip_never_action in manip_never_actions:
                # first find all actions that have the same manip action with manip_never_action
                _, manip_info_n_a = self.process_action(manip_never_action)

                for action in encoder.actions:
                    _, manip_info_a = self.process_action(action.name)

                    if manip_info_a == manip_info_n_a:
                        horizon_never_action_same = encoder.action_variables[int(i)][action.name]
                        constraints.append(Not(horizon_never_action_same))

            # we then add never mr actions
            for pre_never_mr_action in pre_never_mr_actions:
                if len(pre_never_mr_action) == 1:
                    involved_sr_action = pre_never_mr_action[0]
                    pre_info_n_a, _ = self.process_action(involved_sr_action)
                    for action in encoder.actions:
                        pre_info_a, _ = self.process_action(action.name)

                        if pre_info_a == pre_info_n_a:
                            horizon_never_action_same = encoder.action_variables[int(i)][action.name]
                            constraints.append(Not(horizon_never_action_same))
                elif len(pre_never_mr_action) == 2:
                    pre_mutexed_action1 = pre_never_mr_action[0]
                    pre_mutexed_action2 = pre_never_mr_action[1]

                    pre_info_m_a1, manip_info_m_a1 = self.process_action(pre_mutexed_action1)
                    pre_info_m_a2, manip_info_m_a2 = self.process_action(pre_mutexed_action2)

                    pre_mutexed_action1_lst = []
                    pre_mutexed_action2_lst = []

                    for action in encoder.actions:
                        pre_info_a, manip_info_a = self.process_action(action.name)

                        if pre_info_a == pre_info_m_a1:
                            pre_mutexed_action1_lst.append(action.name)
                        elif pre_info_a == pre_info_m_a2:
                            pre_mutexed_action2_lst.append(action.name)

                    for pre_mutexed_action1_same in pre_mutexed_action1_lst:
                        for pre_mutexed_action2_same in pre_mutexed_action2_lst:
                            horizon_mutexed_action1_same = encoder.action_variables[int(i)][pre_mutexed_action1_same]
                            horizon_mutexed_action2_same = encoder.action_variables[int(i)][pre_mutexed_action2_same]
                            constraints.append(Implies(horizon_mutexed_action1_same, Not(horizon_mutexed_action2_same)))
                            constraints.append(Implies(horizon_mutexed_action2_same, Not(horizon_mutexed_action1_same)))
                else:
                    raise NotImplementedError("We only support 2 robots for this baseline.")

            # we then add motion collisions
            # we assume monotone setup
            # then for the action we want to perform, all the collisions should be moved
            for action, must_move_movables in pre_must_moved_movables.items():
                pre_info_mu_a, _ = self.process_action(action)

                # find all actions with the same pre-action (will share the same pre_constrains)
                actions_same_pre = []
                for action_candidate in encoder.actions:
                    pre_info_ac, _ = self.process_action(action_candidate.name)
                    if pre_info_ac == pre_info_mu_a:
                        actions_same_pre.append(action_candidate.name)

                for action_same_pre in actions_same_pre:
                    constraint = Implies(encoder.action_variables[i][action_same_pre],
                                         And([encoder.boolean_variables[i]['moved_' + str(movable)] for movable in
                                              must_move_movables]))
                    constraints.append(constraint)

            # for manip
            # for action, must_move_movables in manip_must_moved_movables.items():
            #     _, manip_info_mu_a = self.process_action(action)
            #
            #     # find all actions with the same pre-action (will share the same pre_constrains)
            #     actions_same_after = []
            #     for action_candidate in encoder.actions:
            #         _, manip_info_ac = self.process_action(action_candidate.name)
            #         if manip_info_ac == manip_info_mu_a:
            #             actions_same_after.append(action_candidate.name)
            #
            #     for action_same_after in actions_same_after:
            #         constraint = Implies(encoder.action_variables[i][action_same_after],
            #                              And([encoder.boolean_variables[i]['moved_' + str(movable)] for movable in
            #                                   must_move_movables]))
            #         constraints.append(constraint)

            for pre_mr_action, pre_mr_action_must_moved_movable_lst in pre_mr_action_must_moved_movables.items():
                if len(pre_mr_action) == 1:
                    involved_sr_action = pre_mr_action[0]

                    pre_info_mu_a, _ = self.process_action(involved_sr_action)

                    # find all actions with the same pre-action (will share the same pre_constrains)
                    actions_same_pre = []
                    for action_candidate in encoder.actions:
                        pre_info_ac, _ = self.process_action(action_candidate.name)
                        if pre_info_ac == pre_info_mu_a:
                            actions_same_pre.append(action_candidate.name)

                    for action_same_pre in actions_same_pre:
                        constraint = Implies(encoder.action_variables[i][action_same_pre],
                                             And([encoder.boolean_variables[i]['moved_' + str(movable)] for movable in
                                                  pre_mr_action_must_moved_movable_lst]))
                        constraints.append(constraint)

                elif len(pre_mr_action) == 2:
                    involved_sr_action1 = pre_mr_action[0]
                    involved_sr_action2 = pre_mr_action[1]
                    pre_info_m_a1, _ = self.process_action(involved_sr_action1)
                    pre_info_m_a2, _ = self.process_action(involved_sr_action2)

                    pre_action1_lst = []
                    pre_action2_lst = []

                    for action in encoder.actions:
                        pre_info_a, manip_info_a = self.process_action(action.name)

                        if pre_info_a == pre_info_m_a1:
                            pre_action1_lst.append(action.name)
                        elif pre_info_a == pre_info_m_a2:
                            pre_action2_lst.append(action.name)

                    for pre_action1_same in pre_action1_lst:
                        for pre_action2_same in pre_action2_lst:
                            horizon_action1_same = encoder.action_variables[int(i)][pre_action1_same]
                            horizon_action2_same = encoder.action_variables[int(i)][pre_action2_same]
                            constraints.append(Implies(And(horizon_action1_same, horizon_action2_same),
                                                       And([encoder.boolean_variables[i]['moved_' + str(movable)] for
                                                            movable in
                                                            pre_mr_action_must_moved_movable_lst])))
                else:
                    raise NotImplementedError()

            # for manip_mr_action, manip_mr_action_must_moved_movable_lst in manip_mr_action_must_moved_movables.items():
            #     if len(manip_mr_action) == 1:
            #         involved_sr_action = manip_mr_action[0]
            #
            #         _, manip_info_mu_a = self.process_action(involved_sr_action)
            #
            #         # find all actions with the same pre-action (will share the same pre_constrains)
            #         actions_same_manip = []
            #         for action_candidate in encoder.actions:
            #             _, manip_info_ac = self.process_action(action_candidate.name)
            #             if manip_info_ac[:2] == manip_info_mu_a[:2]:
            #                 actions_same_manip.append(action_candidate.name)
            #
            #         for action_same_manip in actions_same_manip:
            #             constraint = Implies(encoder.action_variables[i][action_same_manip],
            #                                  And([encoder.boolean_variables[i]['moved_' + str(movable)] for movable in
            #                                       manip_mr_action_must_moved_movable_lst]))
            #             constraints.append(constraint)
            #     elif len(manip_mr_action) == 2:
            #         involved_sr_action1 = manip_mr_action[0]
            #         involved_sr_action2 = manip_mr_action[1]
            #         _, manip_info_m_a1 = self.process_action(involved_sr_action1)
            #         _, manip_info_m_a2 = self.process_action(involved_sr_action2)
            #
            #         manip_action1_lst = []
            #         manip_action2_lst = []
            #
            #         for action in encoder.actions:
            #             _, manip_info_a = self.process_action(action.name)
            #
            #             if manip_info_a[:2] == manip_info_m_a1[:2]:
            #                 manip_action1_lst.append(action.name)
            #             elif manip_info_a[:2] == manip_info_m_a2[:2]:
            #                 manip_action2_lst.append(action.name)
            #
            #         for manip_action1_same in manip_action1_lst:
            #             for manip_action2_same in manip_action2_lst:
            #                 horizon_action1_same = encoder.action_variables[int(i)][manip_action1_same]
            #                 horizon_action2_same = encoder.action_variables[int(i)][manip_action2_same]
            #                 constraints.append(Implies(And(horizon_action1_same, horizon_action2_same),
            #                                            And([encoder.boolean_variables[i]['moved_' + str(movable)] for
            #                                                 movable in
            #                                                 manip_mr_action_must_moved_movable_lst])))
            #     else:
            #         raise NotImplementedError()

        return constraints

    def collision_generalization_constraints(self, objects, model, encoder, plan, failed_step):
        min_step = 0
        max_step = max(encoder.boolean_variables.keys())
        failed_action = encoder.action_variables[failed_step][plan[failed_step]]

        horizon_state = []
        horizon_action = []
        action_str = str(failed_action)[:-2]
        for i in range(max_step):
            horizon_state.append([])
            horizon_action.append(encoder.action_variables[int(i)][action_str])

        for state in encoder.boolean_variables[failed_step].values():
            state_str = str(state)[:-2]
            members = set(state_str.split('__'))
            if len(members.union(objects)) == 0:
                break
            for i in range(max_step):
                if model[state]:
                    horizon_state[i].append(encoder.boolean_variables[int(i)][state_str])
                else:
                    horizon_state[i].append(Not(encoder.boolean_variables[int(i)][state_str]))

        constraints = []
        for i in range(max_step):
            constraints.append(Implies(And(horizon_state[i]), Not(horizon_action[i])))
        return constraints
