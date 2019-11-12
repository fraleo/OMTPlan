#####
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

import sys
from . import arguments
import translate
import subprocess
import utils
from planner import encoder
from planner import modifier
from planner import search

val_path = '/bin/validate'

    
def main(BASE_DIR):
    """
    Main planning routine
    """

    # Parse planner args
    args = arguments.parse_args()


    # Run PDDL translator (from TFD)
    prb = args.problem
    if args.domain:
        domain = args.domain
        task = translate.pddl.open(prb, domain)
    else:
        task = translate.pddl.open(prb)
        domain = utils.getDomainName(prb)


    # Fetch upper bound for bounded search
    
    ub = args.b
    
    # Compose encoder and search
    # according to user flags

    if args.smt:

        if args.linear:

            e = encoder.EncoderSMT(task, modifier.LinearModifier())

            # Build SMT-LIB encoding and dump (no solving)
            if args.translate:
               formula = e.encode(args.translate)

               # Print SMT planning formula (linear) to file
               utils.printSMTFormula(formula,task.task_name)

            else:

                # Ramp-up search for optimal planning with unit costs
                s = search.SearchSMT(e,ub)
                plan = s.do_linear_search()

        elif args.parallel:
            print('\nWarning: optimal planning not supported for this configuration')
            print('Continue with satisficing planning...\n')

            # Parallel encodings, no optimal reasoning here!

            e = encoder.EncoderSMT(task, modifier.ParallelModifier())

            # Build SMT-LIB encoding and dump (no solving)
            if args.translate:
                formula = e.encode(args.translate)

                # Print SMT planning formula (parallel) to file
                utils.printSMTFormula(formula,task.task_name)
            else:
                s = search.SearchSMT(e,ub)
                plan = s.do_linear_search()

        else:
            print('No execution semantics specified, choose between linear or parallel.')
            print('Exiting now...')
            sys.exit()

    elif args.omt:

        if args.linear:

            e = encoder.EncoderOMT(task, modifier.LinearModifier())

            # Build SMT-LIB encoding and dump (no solving)
            if args.translate:
                
                formula = e.encode(args.translate)

                # Print OMT planning formula (linear) to file

                utils.printOMTFormula(formula,task.task_name)
                
            else:
                s = search.SearchOMT(e,ub)
                plan = s.do_search()

        elif args.parallel:
            e = encoder.EncoderOMT(task, modifier.ParallelModifier())

            # Build SMT-LIB encoding and dump (no solving)
            if args.translate:
                
                formula = e.encode(args.translate)

                # Print OMT planning formula (parallel) to file

                utils.printOMTFormula(formula,task.task_name)
                
            else:
                s = search.SearchOMT(e,ub)
                plan = s.do_search()


        else:
            print('No execution semantics specified, choose between linear or parallel.')
            print('Exiting now...')
            sys.exit()

        
    else:
        print('No solving technique specified, choose between SMT or OMT.')
        print('Exiting now...')
        sys.exit()


    # VALidate and print plan
    # Uses VAL, see https://github.com/KCL-Planning/VAL

    val = BASE_DIR+val_path

    if not args.translate:

        try:
            if plan.validate(val, domain, prb):
                print('\nPlan found!')
                print('\nCost: {}\n'.format(plan.cost))
                for k,v in plan.plan.items():
                    print('Step {}: {}'.format(k, v))
            else:
                print('Plan not valid, exiting now...')
                sys.exit()
        except:
            print('\nPlan could not be validated')
            if plan is not None:
                print('\nCost: {}\n'.format(plan.cost))
                for k,v in plan.plan.items():
                    print('Step {}: {}'.format(k, v))

        # Printing plan to file

        if args.pprint:
            if len(plan.plan) == 0:
                print('Warning: no plan found, nothing to print!')
            else:
                plan.pprint(BASE_DIR)

 
if __name__ == '__main__':
    main()
