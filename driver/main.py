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
import os
from . import arguments

import subprocess
import utils
from copy import deepcopy
from planner import encoder
from planner import modifier
from planner import search

from unified_planning.io import PDDLReader
from unified_planning.shortcuts import *
    
def main(BASE_DIR):
    """
    Main planning routine
    """

    # Parse planner args
    args = arguments.parse_args()

    if args.testencoding or args.testsearch:
        failed_to_encode = []
        translate_dump_dir = os.path.join(BASE_DIR, 'translate_dump')
        if not os.path.exists(translate_dump_dir):
            os.makedirs(translate_dump_dir)
        problems = utils.get_planning_problems(BASE_DIR)
        for problem in problems:
            try:
                planning_task = PDDLReader().parse_problem(problem['domain'], problem['instance'])
                if args.smt:
                    if args.testencoding:
                        e = encoder.EncoderSMT(planning_task, modifier.LinearModifier() if args.linear else modifier.ParallelModifier())
                        print('SMT: Encoding problem: {}-{}'.format(problem['name'], planning_task.name))
                        formula = e.encode(1)
                        utils.printSMTFormula(formula, '{}-{}'.format(problem['name'], planning_task.name), translate_dump_dir)
                    elif args.testsearch:
                        print('SMT: Solving problem: {}-{}'.format(problem['name'], planning_task.name))
                        s = search.SearchSMT(e, args.b)
                        plan = s.do_linear_search()
                        if plan.validate():
                            print('SMT: Plan found valid!')
                        else:
                            raise Exception('SMT: Plan found invalid!')
                    else:
                        raise Exception('No test specified, use -testencoding or -testsearch')
                elif args.omt:
                    e = encoder.EncoderOMT(planning_task, modifier.LinearModifier() if args.linear else modifier.ParallelModifier())
                    if args.testencoding:
                        print('OMT: Encoding problem: {}-{}'.format(problem['name'], planning_task.name))
                        formula = e.encode(1)
                        utils.printOMTFormula(formula, '{}-{}'.format(problem['name'], planning_task.name), translate_dump_dir)
                    elif args.testsearch:
                        print('OMT: Solving problem: {}-{}'.format(problem['name'], planning_task.name))
                        s = search.SearchOMT(e, args.b)
                        plan = s.do_search()
                        if plan.validate():
                            print('OMT: Plan found valid!')
                        else:
                            raise Exception('OMT: Plan found invalid!')
                    else:
                        raise Exception('No test specified, use -testencoding or -testsearch')
            except Exception as error:
                logmsg = 'Error msg when encoding problem: {}-{}:{}'.format(problem['name'], planning_task.name, error)
                failed_to_encode.append(logmsg)
                
        # dump failed to encode problems to file.
        if len(failed_to_encode) > 0:
            with open(os.path.join(BASE_DIR, 'failed_to_encode.txt'), 'w') as f:
                for logmsg in failed_to_encode:
                    f.write(logmsg)
                    f.write('\n')
        exit()



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
            utils.printSMTFormula(formula,task.name, BASE_DIR)
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
            utils.printOMTFormula(formula,task.name, BASE_DIR)            
        else:
            s = search.SearchOMT(e, args.b)
            plan = s.do_search()        
    else:
        print('No solving technique specified, choose between SMT or OMT.')
        print('Exiting now...')
        sys.exit()

    if not args.translate:
        if plan.validate():
            print('The plan is valid')
            print(plan.plan)
        else:
            print('The plan is invalid')

if __name__ == '__main__':
    main()
