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

    if args.testencoding:
        translate_dump_dir = os.path.join(BASE_DIR, 'translate_dump')
        if not os.path.exists(translate_dump_dir):
            os.makedirs(translate_dump_dir)
        problems = utils.get_planning_problems(BASE_DIR)
        for problem in problems:
            planning_task = PDDLReader().parse_problem(problem['domain'], problem['instance'])
            print('Encoding problem: {}-{}'.format(problem['name'], planning_task.name))
            if args.smt:
                e = encoder.EncoderSMT(planning_task, modifier.LinearModifier() if args.linear else modifier.ParallelModifier())
                formula = e.encode(1)
                utils.printSMTFormula(formula, '{}-{}'.format(problem['name'], planning_task.name), translate_dump_dir)
            elif args.omt:
                e = encoder.EncoderOMT(planning_task, modifier.LinearModifier() if args.linear else modifier.ParallelModifier())
                formula = e.encode(1)
                utils.printOMTFormula(formula, '{}-{}'.format(problem['name'], planning_task.name), translate_dump_dir)
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
        else:
            print('The plan is invalid')

if __name__ == '__main__':
    main()
