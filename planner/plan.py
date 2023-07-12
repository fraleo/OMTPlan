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

import subprocess
from copy import deepcopy

from z3 import *
from unified_planning.shortcuts import *
from unified_planning.plans import SequentialPlan
from unified_planning.plans import ActionInstance
from unified_planning.engines.compilers.utils import *
from unified_planning.engines.results import *



class Plan():
    """
    Plan objects are instances of this class.
    Defines methods to extract, validate and print plans.
    """

    def __init__(self,model, encoder, objective=None):
        self.encoder = deepcopy(encoder)
        self.plan = self._extractPlan(model)
        self.cost = self._extractCost(objective)

    def _extractPlan(self, model):
        """!
        Extracts plan from model of the formula.
        Plan returned is linearized.

        @param model: Z3 model of the planning formula.
        @param encoder: encoder object, contains maps variable/variable names.

        @return  plan: dictionary containing plan. Keys are steps, values are actions.
        """
        plan = []
        index = 0

        ## linearize partial-order plan
        for step in range(self.encoder.horizon):
            for action in self.encoder.ground_problem.actions:
                if is_true(model[self.encoder.action_variables[step][action.name]]):
                    plan.append(ActionInstance(action))
        return SequentialPlan(plan, self.encoder.ground_problem.environment)


    def _extractCost(self, objective=None):
        """!
        Extracts cost of plan.

        @param objective: Z3 object that contains objective function (default None).

        @return cost: plan cost (metric value if problem is metric, plan length otherwise)
        """

        if objective:
            cost = objective.value()
        else:
            cost = len(self.plan.actions)

        return cost

    def validate(self):
        """!
        Validates plan (when one is found).

        @param val: path to VAL executable.
        @param domain: path to PDDL domain file.
        @param problem: path to PDDL problem file.

        @return plan: string containing plan if plan found is valid, None otherwise.
        """
        up.shortcuts.get_environment().credits_stream = None
        with PlanValidator(problem_kind=self.encoder.ground_problem.kind, plan_kind=self.plan.kind) as validator:
            if validator.validate(self.encoder.ground_problem, self.plan):
                print('The plan is valid')
            else:
                print('The plan is invalid')
        

    def pprint(self, dest):
        """!
        Prints plan to file.

        @param dest: path to destination folder.
        """

        # Default destination
        dest = dest+'/plan_file.txt'

        print('Printing plan to {}'.format(dest))

        # Create string containing plan

        plan_to_str = '\n'.join('{}: {}'.format(key, val) for key, val in self.plan.items())

        with open(dest,'w') as f:
            f.write(plan_to_str)
