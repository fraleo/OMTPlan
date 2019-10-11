#! /usr/bin/env python
# -*- coding: latin-1 -*-

from __future__ import with_statement
from collections import deque, defaultdict
import itertools
import time

import invariants
import pddl
import timers

class BalanceChecker(object):
    def __init__(self, task, reachable_action_params, safe=True):
        self.predicates_to_add_actions = defaultdict(set)
        self.action_name_to_heavy_action = {}
        for action in task.durative_actions:
            if safe:
                action = self.add_inequality_preconds(action, reachable_action_params)
                too_heavy_effects = [[],[]]
                create_heavy_act = False
            for time in xrange(2):
                for eff in action.effects[time]:
                    if isinstance(eff.peffect, pddl.Atom):
                            predicate = eff.peffect.predicate
                            self.predicates_to_add_actions[predicate].add(action)
                    if safe:
                        too_heavy_effects[time].append(eff)
                        if eff.parameters: # universal effect
                            create_heavy_act = True
                            too_heavy_effects[time].append(eff.copy())
            if safe:
                if create_heavy_act:
                    heavy_act = pddl.DurativeAction(action.name, 
                                                    action.parameters,
                                                    action.duration, 
                                                    action.condition, 
                                                    too_heavy_effects)
                    # heavy_act: duplicated universal effects and assigned unique
                    # names to all quantified variables (implicitly in constructor)
                    self.action_name_to_heavy_action[action.name] = heavy_act
                else:
                    self.action_name_to_heavy_action[action.name] = action

    def get_threats(self, predicate):
        return self.predicates_to_add_actions.get(predicate, set())

    def get_heavy_action(self, action_name):
        return self.action_name_to_heavy_action[action_name]

    def add_inequality_preconds(self, action, reachable_action_params):
        if reachable_action_params is None or len(action.parameters) < 2:
            return action
        new_cond_parts = []
        combs = itertools.combinations(range(len(action.parameters)), 2)
        for pos1, pos2 in combs:
            for params in reachable_action_params[action.name]:
                if params[pos1] == params[pos2]:
                    break
            else:
                param1 = pddl.Variable(action.parameters[pos1].name)
                param2 = pddl.Variable(action.parameters[pos2].name)
                new_cond = pddl.NegatedAtom("=", (param1, param2))
                new_cond_parts.append(new_cond)
        if new_cond_parts:
            new_cond = list(action.condition)
            for time in (0,2): # add inequalities to start and end condition
                cond_parts = list(action.condition[time].parts)
                if (isinstance(action.condition[time], pddl.Literal)
                    or isinstance(action.condition[time], pddl.FunctionComparison)):
                    cond_parts = [action.condition[time]]
                cond_parts.extend(new_cond_parts)
                cond = pddl.Conjunction(cond_parts)
                new_cond[time] = cond
            return pddl.DurativeAction(action.name, action.parameters,
                                       action.duration, new_cond,
                                       action.effects)
        else:
            return action

def get_fluents(task):
    fluent_names = set()
    for action in task.durative_actions:
        for timed_effects in action.effects:
            for eff in timed_effects:
                if isinstance(eff.peffect, pddl.Literal):
                    fluent_names.add(eff.peffect.predicate)
    return [pred for pred in task.predicates if pred.name in fluent_names]

def get_initial_invariants(task, safe):
    for predicate in get_fluents(task):
        all_args = range(len(predicate.arguments))
        for omitted_arg in [-1] + all_args:
            order = [i for i in all_args if i != omitted_arg]
            part = invariants.InvariantPart(predicate.name, order, omitted_arg)
            if safe:
                yield invariants.SafeInvariant((part,))
            else:
                yield invariants.UnsafeInvariant((part,))

# Input file might be grounded, beware of too many invariant candidates
MAX_CANDIDATES = 100000
MAX_TIME = 300

def find_invariants(task, safe, reachable_action_params):
    candidates = deque(get_initial_invariants(task, safe))
    print len(candidates), "initial candidates"
    seen_candidates = set(candidates)

    balance_checker = BalanceChecker(task, reachable_action_params, safe)

    def enqueue_func(invariant):
        if len(seen_candidates) < MAX_CANDIDATES and invariant not in seen_candidates:
            candidates.append(invariant)
            seen_candidates.add(invariant)

    start_time = time.clock()
    while candidates:
        candidate = candidates.popleft()
        if time.clock() - start_time > MAX_TIME:
            print "Time limit reached, aborting invariant generation"
            return
        if candidate.check_balance(balance_checker, enqueue_func):
            yield candidate

def useful_groups(invariants, initial_facts):
    predicate_to_invariants = defaultdict(list)
    for invariant in invariants:
        for predicate in invariant.predicates:
            predicate_to_invariants[predicate].append(invariant)

    nonempty_groups = set()
    overcrowded_groups = set()
    for atom in initial_facts:
        if not isinstance(atom,pddl.FunctionAssignment):
            for invariant in predicate_to_invariants.get(atom.predicate, ()):
                group_key = (invariant, tuple(invariant.get_parameters(atom)))
                if group_key not in nonempty_groups:
                    nonempty_groups.add(group_key)
                else:
                    overcrowded_groups.add(group_key)
    useful_groups = nonempty_groups - overcrowded_groups
    for (invariant, parameters) in useful_groups:
        yield [part.instantiate(parameters) for part in invariant.parts]

def get_groups(task, safe=True, reachable_action_params=None):
    with timers.timing("Finding invariants"):
        invariants = list(find_invariants(task, safe, reachable_action_params))
    invariants = sorted(invariants)
    with timers.timing("Checking invariant weight"):
        result = list(useful_groups(invariants, task.init))
    return result

if __name__ == "__main__":
    import pddl
    print "Parsing..."
    task = pddl.open()
    print "Finding invariants..."
    for invariant in find_invariants(task):
        print invariant
    print "Finding fact groups..."
    groups = get_groups(task)
    for group in groups:
        print "[%s]" % ", ".join(map(str, group))
