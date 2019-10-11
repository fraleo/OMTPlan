from z3 import *
import subprocess



class Plan():
    """
    Plan objects are instances of this class.
    Defines methods to extract, validate and print plans.
    """

    def __init__(self,model, encoder, objective=None):
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
                    plan[index] =  action.name
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
        dest = dest+'/plan_file.txt'

        print('Printing plan to {}'.format(dest))

        # Create string containing plan

        plan_to_str = '\n'.join('{}: {}'.format(key, val) for key, val in self.plan.items())

        with open(dest,'w') as f:
            f.write(plan_to_str)
