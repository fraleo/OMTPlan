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

import subprocess
import utils
from copy import deepcopy
from planner import encoder
from planner import modifier
from planner import search

from unified_planning.io import PDDLReader
from unified_planning.shortcuts import *

val_path = '/bin/validate'

    
def main(BASE_DIR):
    """
    Main planning routine
    """

    # Parse planner args
    args = arguments.parse_args()

    # Compose encoder and search
    # according to user flags
    if not args.parallel and not args.linear:
        print('No execution semantics specified, choose between linear or parallel.')
        print('Exiting now...')
        sys.exit()

    # Parse PDDL problem
    reader = PDDLReader()
    task = reader.parse_problem(args.domain, args.problem)    

    if args.smt:
        
        if args.parallel:
            print('\nWarning: optimal planning not supported for this configuration')
            print('Continue with satisficing planning...\n')
        
        e = encoder.EncoderSMT(task, modifier.LinearModifier() if args.linear else modifier.ParallelModifier())

        # Build SMT-LIB encoding and dump (no solving)
        if args.translate:
            formula = e.encode(args.translate)
            # Print SMT planning formula (linear) to file
            utils.printSMTFormula(formula,task.name)
        else:
            # Ramp-up search for optimal planning with unit costs
            s = search.SearchSMT(e, args.b)
            plan = s.do_linear_search()

    elif args.omt:

        e = encoder.EncoderOMT(task, modifier.LinearModifier() if args.linear else modifier.ParallelModifier())
        
        # Build SMT-LIB encoding and dump (no solving)
        if args.translate:
            formula = e.encode(args.translate)
            # Print OMT planning formula (linear) to file
            utils.printOMTFormula(formula,task.name)            
        else:
            s = search.SearchOMT(e, args.b)
            plan = s.do_search()        
    else:
        print('No solving technique specified, choose between SMT or OMT.')
        print('Exiting now...')
        sys.exit()


    # VALidate and print plan
    # Uses VAL, see https://github.com/KCL-Planning/VAL

    val = BASE_DIR+val_path

    if not args.translate:
        plan.validate()

        

        # print("Use unified planning to validate plan")

        # TODO: Print plan using unified planning

        # try:
        #     if plan.validate(val, domain, prb):
        #         print('\nPlan found!')
        #         print('\nCost: {}\n'.format(plan.cost))
        #         for k,v in plan.plan.items():
        #             print('Step {}: {}'.format(k, v))
        #     else:
        #         print('Plan not valid, exiting now...')
        #         sys.exit()
        # except:
        #     print('\nThe following plan could not be validated.')
        #     if plan is not None:
        #         print('\nCost: {}\n'.format(plan.cost))
        #         for k,v in plan.plan.items():
        #             print('Step {}: {}'.format(k, v))

        # # Printing plan to file

        # if args.pprint:
        #     if len(plan.plan) == 0:
        #         print('Warning: no plan found, nothing to print!')
        #     else:
        #         plan.pprint(BASE_DIR)

 
if __name__ == '__main__':
    main()
