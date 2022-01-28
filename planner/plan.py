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
    """
    Plan objects are instances of this class.
    Defines methods to extract, validate and print plans.
    """

    def __init__(self, model, encoder, objective=None):
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
