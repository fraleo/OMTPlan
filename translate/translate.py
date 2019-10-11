#! /usr/bin/env python
# -*- coding: latin-1 -*-
import sys

import axiom_rules
import fact_groups
import instantiate
import numeric_axiom_rules
import pddl
import sas_tasks
import simplify
import itertools

# TODO: The translator may generate trivial derived variables which are always true,
# for example if there ia a derived predicate in the input that only depends on
# (non-derived) variables which are detected as always true.
# Such a situation was encountered in the PSR-STRIPS-DerivedPredicates domain.
# Such "always-true" variables should best be compiled away, but it is
# not clear what the best place to do this should be. Similar
# simplifications might be possible elsewhere, for example if a
# derived variable is synonymous with another variable (derived or
# non-derived).

ALLOW_CONFLICTING_EFFECTS = False
USE_PARTIAL_ENCODING = True
WRITE_ALL_MUTEXES = True
USE_SAFE_INVARIANT_SYNTHESIS = True

def strips_to_sas_dictionary(groups, num_axioms, num_axiom_map, num_fluents):
    dictionary = {}

    # sort groups to get a deterministic output
    map(lambda g: g.sort(lambda x, y: cmp(str(x),str(y))),groups)
    groups.sort(lambda x, y: cmp((-len(x),str(x[0])),(-len(y),str(y[0]))))

    for var_no, group in enumerate(groups):
        for val_no, atom in enumerate(group):
            dictionary.setdefault(atom, []).append((var_no, val_no))
    if USE_PARTIAL_ENCODING:
        assert all(len(sas_pairs) == 1
                   for sas_pairs in dictionary.itervalues())

    redundant_axioms = []
    num_ax_count = 0
    for axiom in num_axioms:
        if axiom.effect in num_axiom_map:
            redundant_axioms.append(axiom.effect)
        else:
            dictionary.setdefault(axiom.effect,[]).append((num_ax_count + len(groups), -2))
            num_ax_count += 1
    for axiom_effect in redundant_axioms:
        dictionary[axiom_effect] = dictionary[num_axiom_map[axiom_effect].effect]

    ranges = [len(group) + 1 for group in groups] + [-1]*num_ax_count

    var_no = len(groups) + num_ax_count
    fluent_list = list(num_fluents)
    fluent_list.sort(lambda x,y: cmp(str(x), str(y)))
    for fluent in fluent_list: # are partially contained in num_axiom
        if fluent not in dictionary:
            dictionary.setdefault(fluent,[]).append((var_no, -2))
            var_no += 1
            ranges.append(-1)
        
    return ranges, dictionary

def translate_strips_conditions(conditions, dictionary, ranges, comp_axioms, 
                                temporal=False, true_atoms=(), false_atoms=()):
    """ Translate (possibly temporal) strips conditions to a list of conditions.
    
    If temporal, conditions is a list of (3) condition (lists).

    """
    if temporal:
        condition = [translate_strips_conditions_aux(conds, dictionary, ranges,
                                                     comp_axioms, true_atoms,
                                                     false_atoms) 
                     for conds in conditions]
        if None in condition:
            return None
        else:
            return condition
    else:
        return translate_strips_conditions_aux(conditions, dictionary, ranges,
                                               comp_axioms, true_atoms,
                                               false_atoms)


def translate_strips_conditions_aux(conditions, dictionary, ranges, comparison_axioms,
                                    true_atoms, false_atoms):
    """ Translate a strips condition.

    Translates the condition for a certain time point/period (at start, over
    all or at end), not a full temporal condition. So conditions must
    represent a conjunction of facts.

    Returns a list of conditions - commonly just 1 entry, but negated
    effects might result in a disjunction (represented as list) of multiple
    conditions. 

    """
    if not conditions:
        return [{}] # Quick exit for common case.

    condition = {}
    comp_axiom_dict = comparison_axioms[0]
    sas_comp_axioms = comparison_axioms[1]
    negated_facts = []

    for fact in conditions:
        if (isinstance(fact,pddl.FunctionComparison) or 
            isinstance(fact,pddl.NegatedFunctionComparison)):
            if fact not in dictionary:
                parts = [dictionary[part][0][0] for part in fact.parts]
                key = (fact.comparator, tuple(parts))
                negated = fact.negated
                if key in comp_axiom_dict:
                    fact = comp_axiom_dict[key]
                    if negated:
                        fact = fact.negate()
                else:
                    axiom = sas_tasks.SASCompareAxiom(fact.comparator, 
                                                      parts, len(ranges)) 
                    sas_comp_axioms.append(axiom)
                    if negated:
                        negfact = fact
                        posfact = fact.negate()
                    else:
                        posfact = fact
                        negfact = fact.negate()
                    comp_axiom_dict[key] = posfact
                    dictionary.setdefault(posfact,[]).append((len(ranges), 0))
                    dictionary.setdefault(negfact,[]).append((len(ranges), 1))
                    ranges.append(3)
            var, val = dictionary[fact][0]
            if (var in condition and val not in condition[var]):
                # Conflicting conditions on this variable: Operator invalid.
                return None
            condition[var] = set([val]) 
        else:
            # check atoms from constant axioms
            atom = pddl.Atom(fact.predicate, fact.args) # force positive
            if fact.negated:
                if atom in false_atoms:
                    continue
                if atom in true_atoms:
                    return None
            else:
                if atom in true_atoms:
                    continue
                if atom in false_atoms:
                    return None
            if fact.negated:
                negated_facts.append(fact)
                # we handle negative conditions later, because then we
                # can recognize when the negative condition is already
                # ensured by a positive condition
                continue
            try:
                for var, val in dictionary[fact]:
                    if var in condition and val not in condition[var]:
                        # Conflicting conditions on this variable: 
                        # Operator invalid.
                        return None
                    condition[var] = set([val])
            except KeyError as e:
                print "Atom not in dictionary: ", fact.dump()
                raise
    
    # Now deal with the negated conditions
    for fact in negated_facts:
                ## Note  Here we use a different solution than in Sec. 10.6.4
                ##       of the thesis. Compare the last sentences of the third
                ##       paragraph of the section.
                ##       We could do what is written there. As a test case,
                ##       consider Airport ADL tasks with only one airport, where
                ##       (occupied ?x) variables are encoded in a single variable,
                ##       and conditions like (not (occupied ?x)) do occur in
                ##       preconditions.
                ##       However, here we avoid introducing new derived predicates
                ##       by treat the negative precondition as a disjunctive precondition
                ##       and expanding it by "multiplying out" the possibilities.
                ##       This can lead to an exponential blow-up so it would be nice
                ##       to choose the behaviour as an option.
                done = False
                new_condition = {}
                atom = pddl.Atom(fact.predicate, fact.args) # force positive
                for var, val in dictionary.get(atom, ()):
                    # see comment (**) above
                    poss_vals = set(range(ranges[var]))
                    poss_vals.remove(val)
    
                    if condition.get(var) is None:
                        assert new_condition.get(var) is None
                        new_condition[var] = poss_vals
                    else:
                        # constrain existing condition on var
                        prev_possible_vals = condition.get(var)
                        done = True
                        prev_possible_vals.intersection_update(poss_vals)
                        if len(prev_possible_vals) == 0:
                            # Conflicting conditions on this variable:
                            # Operator invalid.
                            return None
    
                if not done and new_condition:
                    # we did not enforce the negative condition by constraining
                    # an existing condition on one of the variables representing
                    # this atom. So we need to introduce a new condition:
                    # We can select any from new_condition and currently prefer the
                    # smalles one.
                    candidates = sorted(new_condition.items(),
                                        lambda x,y: cmp(len(x[1]),len(y[1])))
                    var, vals = candidates[0]
                    condition[var] = vals
 
    def multiply_out(condition): # destroys the input
        sorted_conds = sorted(condition.items(),
                              lambda x,y: cmp(len(x[1]),len(y[1])))
        flat_conds = [{}]
        for var, vals in sorted_conds:
            if len(vals) == 1:
                for cond in flat_conds:
                    cond[var] = vals.pop() # destroys the input here
            else:
                new_conds = []
                for cond in flat_conds:
                    for val in vals:
                        new_cond = deepcopy(cond)
                        new_cond[var] = val
                        new_conds.append(new_cond)
                flat_conds = new_conds
        return flat_conds

    return multiply_out(condition)


def translate_operator_duration(duration, dictionary):
    sas_durations = []
    for timed_duration in duration:
        timed_sas_durations = []
        for dur in timed_duration:
            var, val = dictionary.get(dur[1])[0]
            timed_sas_durations.append(sas_tasks.SASDuration(dur[0],var))
        sas_durations.append(timed_sas_durations)
    return sas_durations

def mutex_conditions(cond_dict, condition, temporal):
    # return value True means that the conditions are mutex
    # return value False means that we don't know whether they are mutex
    if temporal:
        for time in range(3):
            for var,val in condition[time]:
                if var in cond_dict[time]:
                    if cond_dict[time][var] != val:
                        return True
    else:
        for var,val in condition:
            if var in cond_dict:
                if cond_dict[var] != val:
                    return True
    return False

def implies(condition, condition_list, global_cond, temporal):
    # True: whenever condition is true also at least one condition 
    # from condition_list is true (given global_cond)
    if temporal:
        if [[],[],[]] in condition_list:
            return True
        for cond in condition_list:
            triggers = True
            for time in range(3):
                for (var,val) in cond[time]:
                    if (var,val) not in condition[time] and global_cond[time].get(var)!=val:
                        triggers=False
                        break
                if not triggers:
                    break
            if triggers:
                return True
    else:
        if [] in condition_list:
            return True
        for cond in condition_list:
            triggers = True
            for (var,val) in cond:
                if (var,val) not in condition and global_cond.get(var)!=val:
                    triggers=False
                    break
            if triggers:
                return True
    return False

def translate_add_effects(add_effects, dictionary, ranges, comp_axioms,
                          temporal, true_atoms, false_atoms):
    assert temporal
    effect = {}
    possible_add_conflict = False

    for conditions, fact in add_effects:
        eff_condition_dict_list = translate_strips_conditions(conditions, dictionary, 
                                         ranges, comp_axioms, temporal, true_atoms,
                                         false_atoms)
        if eff_condition_dict_list is None: # Impossible condition for this effect.
            continue
        eff_condition_temporal_dicts = cartesian_product_temporal_conditions(eff_condition_dict_list)
        # now eff_condition_temporal_dicts is a list of temporal conditions        
        
        if temporal:
            eff_conditions = [[eff_dict.items() for eff_dict in eff_cond] 
                                for eff_cond in eff_condition_temporal_dicts]
        else:
            eff_conditions = [eff_dict.items() 
                                for eff_dict in eff_condition_temporal_dicts]

        for var, val in dictionary[fact]:
            hitherto_effect = effect.setdefault(var,{})
            for other_val in hitherto_effect:
                if other_val != val:
                    for other_cond in hitherto_effect[other_val]:
                        for eff_cond in eff_conditions:
                            #redictify
                            eff_cond_as_dict = [dict(eff_pairs)
                                                for eff_pairs in eff_cond]
                            if not mutex_conditions(eff_cond_as_dict, 
                                                other_cond, temporal):
                                possible_add_conflict = True
            hitherto_effect.setdefault(val,[]).extend(eff_conditions)
    return effect, possible_add_conflict

def translate_del_effects(del_effects,dictionary,ranges,effect,condition,
                          comp_axioms, temporal, time, true_atoms, false_atoms):
    assert temporal
    if temporal:
        assert time is not None
        cond_time = time*2 # start -> start condition, end -> end_condition

    for conditions, fact in del_effects:
        eff_condition_dict_list = translate_strips_conditions(conditions, dictionary,
                                                  ranges, comp_axioms, temporal,
                                                  true_atoms, false_atoms)
        if eff_condition_dict_list is None:
            continue
        eff_condition_temporal_dicts = cartesian_product_temporal_conditions(eff_condition_dict_list)
        # now eff_condition_temporal_dicts is a list of temporal conditions        
        
        if temporal:
            eff_conditions = [[eff_dict.items() for eff_dict in eff_cond] 
                              for eff_cond in eff_condition_temporal_dicts]
        else:
            eff_conditions = [eff_dict.items() 
                              for eff_dict in eff_condition_temporal_dicts]

        for var, val in dictionary[fact]:
            none_of_those = ranges[var] - 1
            hitherto_effects = effect.setdefault(var,{})
            
            for eff_condition in eff_conditions:
                eff_cond_as_dict = [ dict(eff_pairs) for eff_pairs in eff_condition ]
                # Look for matching add effect; ignore this del effect if found
                found_matching_add_effect = False
                uncertain_conflict = False
    
                for other_val, other_eff_conditions in hitherto_effects.items():
                    if other_val!=none_of_those:
                        if implies(eff_condition, other_eff_conditions, condition, temporal):
                            found_matching_add_effect = True
                            break
                        for cond in other_eff_conditions:
                            if not mutex_conditions(eff_cond_as_dict, 
                                                    cond, temporal): 
                                uncertain_conflict = True
                # del-effect can be ignored if some other value is added
                # or the variable already has the value none-of-those
                already_undefined = (condition[cond_time].get(var) == none_of_those or 
                                     eff_cond_as_dict[cond_time].get(var) == none_of_those)
                if found_matching_add_effect or already_undefined:
                    continue
                else:
                    assert not uncertain_conflict, "Uncertain conflict"
                    if (condition[cond_time].get(var) != val and 
                        eff_cond_as_dict[cond_time].get(var) != val):
                        # if the variable must have a different value whenever
                        # the operator is applied, we can ignore the delete
                        # effect
                        if (var in condition[cond_time] or
                            (cond_time == 2 and var in condition[1] and
                             condition[1][var] != val)):
                            continue
                        # Need a guard for this delete effect.
                        assert (var not in eff_condition[cond_time]), "Oops?"
                        eff_condition[cond_time].append((var, val))
    
                    del_eff_conditions = hitherto_effects.setdefault(none_of_those,[])
                    del_eff_conditions.append(eff_condition)

def translate_assignment_effects(assign_effects, dictionary, ranges, comp_axioms, 
                                 temporal, true_atoms, false_atoms):
    assert temporal
    effect = {}
    possible_assign_conflict = False

    for conditions, assignment in assign_effects:
        eff_condition_dict_list = translate_strips_conditions(conditions, dictionary, 
                                         ranges, comp_axioms, temporal, true_atoms,
                                         false_atoms)
        if eff_condition_dict_list is None: # Impossible condition for this effect.
            continue
        eff_condition_temporal_dicts = cartesian_product_temporal_conditions(eff_condition_dict_list)
        # now eff_condition_temporal_dicts is a list of temporal conditions        

        if temporal:
            eff_conditions = [[eff_dict.items() for eff_dict in eff_cond]
                              for eff_cond in eff_condition_temporal_dicts]
        else:
            eff_conditions = [eff_dict.items() 
                              for eff_dict in eff_condition_temporal_dicts]
        for var, _ in dictionary[assignment.fluent]:
            for expvar, _ in dictionary[assignment.expression]:
                val = (assignment.symbol, expvar)
                hitherto_effect = effect.setdefault(var,{})
                for other_val in hitherto_effect:
                    if other_val != val:
                        for other_cond in hitherto_effect[other_val]:
                            for eff_cond in eff_conditions:
                                # redictify
                                eff_cond_as_dict = [dict(eff_pairs) 
                                                    for eff_pairs in eff_cond]
                                if not mutex_conditions(eff_cond_as_dict,
                                                    other_cond, temporal):
                                    possible_assign_conflict = True
                hitherto_effect.setdefault(val,[]).extend(eff_conditions)
    return effect, possible_assign_conflict

def translate_strips_operator(operator, dictionary, ranges, comp_axioms):
    # NOTE: This function does not really deal with the intricacies of properly
    # encoding delete effects for grouped propositions in the presence of
    # conditional effects. It should work ok but will bail out in more
    # complicated cases even though a conflict does not necessarily exist.

    assert False, "Actions not supported, use durative actions"
    condition = translate_strips_conditions(operator.condition, dictionary, ranges, comp_axioms)
    if condition is None:
        return None

    effect, possible_add_conflict = translate_add_effects(operator.add_effects, 
                                                          dictionary, ranges, comp_axioms, False)
    translate_del_effects(operator.del_effects, dictionary, ranges, effect,
                          condition, comp_axioms, False, None)

    if possible_add_conflict:
        print operator.name
    assert not possible_add_conflict, "Conflicting add effects?"

    assign_effect, possible_assign_conflict = \
        translate_assignment_effects(operator.assign_effects, dictionary, ranges, comp_axioms, False)
    
    if possible_assign_conflict:
        print operator.name
    assert not possible_assign_conflict, "Conflicting assign effects?"

    pre_post = []
    for var in effect:
        for (post, eff_condition_lists) in effect[var].iteritems():
            pre = condition.get(var, -1)
            if pre != -1:
                del condition[var]
            for eff_condition in eff_condition_lists:
                pre_post.append((var, pre, post, eff_condition))
    prevail = condition.items()

    assign_effects = []
    for var in assign_effect:
        for ((op, valvar), eff_condition_lists) in assign_effect[var].iteritems():
            for eff_condition in eff_condition_lists:
                sas_effect = sas_tasks.SASAssignmentEffect(var, op, valvar, 
                                                       eff_condition)
                assign_effects.append(sas_effect)

    return sas_tasks.SASOperator(operator.name, prevail, pre_post, assign_effects)

def cartesian_product_temporal_conditions(conds):
    """ Expands disjunctive temporal conditions.

        Forms a disjunction as a list of temporal conditions (length 3 list)
        from a temporal condition where each entry is a disjunction as a list of
        conditions by applying the cartesian product.
        
    """
    assert len(conds) == 3, "Unexpected length for temporal condition"
    return [list(cond) for cond in itertools.product(*conds)]


def translate_temporal_strips_operator_aux(operator, dictionary, ranges,
                                           comp_axioms, condition, true_atoms,
                                           false_atoms):
    # NOTE: This function does not really deal with the intricacies of properly
    # encoding delete effects for grouped propositions in the presence of
    # conditional effects. It should work ok but will bail out in more
    # complicated cases even though a conflict does not necessarily exist.

    duration = translate_operator_duration(operator.duration, dictionary)

    if condition is None:
        print "operator condition is None (invalid)"
        return None

    effect = []
    possible_add_conflict = False
    for time in range(2):
        eff, poss_conflict = translate_add_effects(operator.add_effects[time], 
                                                   dictionary, ranges,
                                                   comp_axioms, True,
                                                   true_atoms, false_atoms)
        translate_del_effects(operator.del_effects[time], dictionary, ranges, 
                              eff, condition, comp_axioms, True, time,
                              true_atoms, false_atoms)
        effect.append(eff)
        possible_add_conflict |= poss_conflict

    if possible_add_conflict:
        print operator.name
    assert not possible_add_conflict

    assign_effect = []
    possible_assign_conflict = False
    for time in range(2):
        eff, conflict = translate_assignment_effects(operator.assign_effects[time], 
                                                     dictionary, ranges,
                                                     comp_axioms, True,
                                                     true_atoms, false_atoms)
        assign_effect.append(eff)
        possible_assign_conflict |= conflict
    
    if possible_assign_conflict:
        print operator.name
    assert not possible_assign_conflict

    pre_post = [[],[]]
    for time in range(2):
        cond_time = time*2 # start -> start condition, end -> end_condition
        for var in effect[time]:
            for (post, eff_condition_lists) in effect[time][var].iteritems():
                pre = condition[cond_time].get(var, -1)
                if pre != -1:
                    del condition[cond_time][var]

                # substitute normal effect for conditional effects if it has only
                # one at-start condition on a binary variable which is equivalent
                # to the effect variable
                # example: temporal effect 1 6 0 0 0 6 -1 1
                #          becomes 0 0 0 6 0 1 
                # NOTE: this changes the applicability of the action, because we 
                # introduce a "write operation" on the variable in the case, where 
                # the original conditional effect does not trigger (hence not 
                # affecting the variable)
                if len(eff_condition_lists) == 1: # only one conditon
                    eff_condition = eff_condition_lists[0]
                    if (eff_condition[1] == [] and eff_condition[2] == [] and
                        len(eff_condition[0]) == 1):
                        ecvar, ecval = eff_condition[0][0]
                        if ecvar == var and ranges[var] == 2:
                            eff_condition[0] = []
                for eff_condition in eff_condition_lists:
                    pre_post[time].append((var, pre, post, eff_condition))
    prevail = [cond.items() for cond in condition]

    assign_effects = [[],[]]
    for time in range(2):
        for var in assign_effect[time]:
            for ((op, valvar), eff_condition_lists) \
                in assign_effect[time][var].iteritems():
                for eff_condition in eff_condition_lists:
                    sas_effect = sas_tasks.SASAssignmentEffect(var, op, valvar, 
                                                           eff_condition, True)
                    assign_effects[time].append(sas_effect)

    return sas_tasks.SASTemporalOperator(operator.name, duration, 
                prevail, pre_post, assign_effects)

def translate_temporal_strips_operator(operator, dictionary, ranges,
                                       comp_axioms, true_atoms, false_atoms):
    condition = translate_strips_conditions(operator.conditions, dictionary,
                                            ranges, comp_axioms, True,
                                            true_atoms, false_atoms)
    if condition is None:
        return None
    # condition now is a list for at start/over all/at end where each entry is a
    # list of conditions forming a disjunction We handle the disjunctions by
    # forming one operator per disjunction. As we have three disjunctions for
    # the temporal operator, we need to combine them using the cartesian product
    # forming the resulting operators
    temp_conds = cartesian_product_temporal_conditions(condition)
    ops = []
    for temp_cond in temp_conds:
        op = translate_temporal_strips_operator_aux(operator, dictionary,
                                                    ranges, comp_axioms,
                                                    temp_cond, true_atoms,
                                                    false_atoms)
        if op is not None:
            ops.append(op)
    return ops

def translate_strips_axiom(axiom, dictionary, ranges, comp_axioms):
    # returns a list of axioms as condition might give a disjunction
    conditions = translate_strips_conditions(axiom.condition, dictionary, ranges, comp_axioms)
    if conditions is None:
        return []
    if axiom.effect.negated:
        [(var, _)] = dictionary[axiom.effect.positive()]
        effect = (var, ranges[var] - 1)
    else:
        [effect] = dictionary[axiom.effect]
    axioms = []
    for condition in conditions:
        axioms.append(sas_tasks.SASAxiom(condition.items(), effect))
    return axioms

def translate_numeric_axiom(axiom, dictionary):
    effect = dictionary.get(axiom.effect)[0][0]
    op = axiom.op
    parts = []
    for part in axiom.parts:
        if isinstance(part, pddl.PrimitiveNumericExpression):
            parts.append(dictionary.get(part)[0][0])
        else: # part is PropositionalNumericAxiom
            parts.append(dictionary.get(part.effect)[0][0])
    return sas_tasks.SASNumericAxiom(op, parts, effect)

def translate_strips_operators(actions, strips_to_sas, ranges, comp_axioms):
    result = []
    actions.sort(lambda x,y: cmp(x.name,y.name))
    for action in actions:
        sas_op = translate_strips_operator(action, strips_to_sas, ranges, comp_axioms)
        if sas_op:
            result.append(sas_op)
    return result

def translate_temporal_strips_operators(actions, strips_to_sas, ranges, comp_axioms,
        true_atoms, false_atoms):
    result = []
    actions.sort(lambda x,y: cmp(x.name,y.name))
    for action in actions:
        sas_ops = translate_temporal_strips_operator(action, strips_to_sas, 
                                                     ranges, comp_axioms, 
                                                     true_atoms, false_atoms)
        if sas_ops:
            result.extend(sas_ops)
    return result

def translate_strips_axioms(axioms, strips_to_sas, ranges, comp_axioms):
    result = []
    axioms.sort(lambda x,y: cmp(x.name,y.name))
    for axiom in axioms:
        sas_axioms = translate_strips_axiom(axiom, strips_to_sas, ranges, comp_axioms)
        if sas_axioms:
            result.extend(sas_axioms)
    return result

def translate_task(strips_to_sas, ranges, init, goals, actions, 
                   durative_actions, axioms, num_axioms, num_axioms_by_layer, 
                   max_num_layer, num_axiom_map, const_num_axioms):

    axioms, axiom_init, axiom_layer_dict, true_atoms, false_atoms = axiom_rules.handle_axioms(
      actions, durative_actions, axioms, goals)

    init = init + axiom_init

    # filter trivial true_atoms from goal
    goals = [g for g in goals if g not in true_atoms]   # FIXME: empty goal would be handled nicely by search
    # if any atom in goal is false, the task is unsolvable
    for fa in false_atoms:
        if fa in goals:
            print "False atom in goal:"
            fa.dump()
            return unsolvable_sas_task("False atom in goal")

    comp_axioms = [{},[]]
    goal_dict_list = translate_strips_conditions(goals, strips_to_sas, ranges, comp_axioms)
    assert len(goal_dict_list) == 1, "Negative goal not supported"
    ## we could substitute the negative goal literal in
    ## normalize.substitute_complicated_goal, using an axiom. We currently
    ## don't do this, because we don't run into this assertion, if the
    ## negative goal is part of finite domain variable with only two
    ## values, which is most of the time the case, and hence refrain from
    ## introducing axioms (that are not supported by all heuristics)
    goal_pairs = goal_dict_list[0].items()
    goal = sas_tasks.SASGoal(goal_pairs)

    # FIXME: remove this, defunct anyways
    operators = translate_strips_operators(actions, strips_to_sas, ranges, comp_axioms)
    temp_operators = translate_temporal_strips_operators(durative_actions, 
                                        strips_to_sas, ranges, comp_axioms,
                                        true_atoms, false_atoms)
    
    axioms = translate_strips_axioms(axioms, strips_to_sas, ranges, comp_axioms)
    sas_num_axioms = [translate_numeric_axiom(axiom,strips_to_sas) for axiom in num_axioms 
                      if axiom not in const_num_axioms and
                      axiom.effect not in num_axiom_map]


    axiom_layers = [-1] * len(ranges)
    
    ## each numeric axiom gets its own layer (a wish of a colleague for 
    ## knowledge compilation or search. If you use only the translator,
    ## you can change this)
    num_axiom_layer = 0
    for layer in num_axioms_by_layer:
        num_axioms_by_layer[layer].sort(lambda x,y: cmp(x.name,y.name))
        for axiom in num_axioms_by_layer[layer]:
            if axiom.effect not in num_axiom_map:
                [(var,val)] = strips_to_sas[axiom.effect]
                if layer == -1:
                    axiom_layers[var] = -1
                else:
                    axiom_layers[var] = num_axiom_layer
                    num_axiom_layer += 1
    for axiom in comp_axioms[1]:
        axiom_layers[axiom.effect] = num_axiom_layer
    for atom, layer in axiom_layer_dict.iteritems():
        assert layer >= 0
        [(var, val)] = strips_to_sas[atom]
        axiom_layers[var] = layer + num_axiom_layer + 1
    variables = sas_tasks.SASVariables(ranges, axiom_layers)

    init_values = [rang - 1 for rang in ranges]
    # Closed World Assumption: Initialize to "range - 1" == Nothing.
    for fact in init:
        if isinstance(fact,pddl.Atom):
            pairs = strips_to_sas.get(fact, [])  # empty for static init facts
            for var, val in pairs:
                assert init_values[var] == ranges[var] - 1, "Inconsistent init facts!"
                init_values[var] = val
        else: # isinstance(fact,pddl.FunctionAssignment)
            pairs = strips_to_sas.get(fact.fluent,[]) #empty for constant functions 
            for (var, _) in pairs:
                val = fact.expression.value
                assert init_values[var] == ranges[var] - 1, "Inconsistent init facts!"
                init_values[var]=val
    for axiom in const_num_axioms:
        var = strips_to_sas.get(axiom.effect)[0][0]
        val = axiom.parts[0].value
        init_values[var]=val
    init = sas_tasks.SASInit(init_values)

    return sas_tasks.SASTask(variables, init, goal, operators, 
                             temp_operators, axioms, sas_num_axioms, comp_axioms[1])

def unsolvable_sas_task(msg):
    print "%s! Generating unsolvable task..." % msg
    variables = sas_tasks.SASVariables([2], [-1])
    init = sas_tasks.SASInit([0])
    goal = sas_tasks.SASGoal([(0, 1)])
    operators = []
    temp_operators = []
    axioms = []
    num_axioms = []
    comp_axioms = []
    return sas_tasks.SASTask(variables, init, goal, operators,
            temp_operators, axioms, num_axioms, comp_axioms)

def pddl_to_sas(task):
    print "Instantiating..."
    (relaxed_reachable, atoms, num_fluents, actions, 
        durative_actions, axioms, num_axioms, 
        reachable_action_params) = instantiate.explore(task)

    if not relaxed_reachable:
        return unsolvable_sas_task("No relaxed solution")

    num_axioms = list(num_axioms)
    num_axioms.sort(lambda x,y: cmp(x.name,y.name))

    # HACK! Goals should be treated differently (see TODO file).
    # Update: This is now done during normalization. The assertions
    # are only left here to be on the safe side. Can be removed eventually
    if isinstance(task.goal, pddl.Conjunction):
        goal_list = task.goal.parts
    else:
        goal_list = [task.goal]
    for item in goal_list:
        assert isinstance(item, pddl.Literal)

    groups, mutex_groups, translation_key = fact_groups.compute_groups(
        task, atoms, reachable_action_params,
        return_mutex_groups=WRITE_ALL_MUTEXES,
        partial_encoding=USE_PARTIAL_ENCODING,
        safe=USE_SAFE_INVARIANT_SYNTHESIS)

    num_axioms_by_layer, max_num_layer, num_axiom_map, const_num_axioms = \
        numeric_axiom_rules.handle_axioms(num_axioms)

    print "Building STRIPS to SAS dictionary..."
    ranges, strips_to_sas = strips_to_sas_dictionary(groups, num_axioms, num_axiom_map, num_fluents)
     
    print "Translating task..."
    assert not actions, "There shouldn't be any actions - just temporal actions"
    sas_task = translate_task(strips_to_sas, ranges, task.init, goal_list,
                              actions, durative_actions, axioms, num_axioms,
                              num_axioms_by_layer, max_num_layer, num_axiom_map,
                              const_num_axioms)

    simplify.constrain_end_effect_conditions(sas_task)
    mutex_key = build_mutex_key(strips_to_sas, mutex_groups)

#    try:
#        simplify.filter_unreachable_propositions(
#            sas_task, mutex_key, translation_key)
#    except simplify.Impossible:
#        return unsolvable_sas_task("Simplified to trivially false goal")

    write_translation_key(strips_to_sas)
    if WRITE_ALL_MUTEXES:
        write_mutex_key(mutex_key)
    return sas_task

def build_mutex_key(strips_to_sas, groups):
    group_keys = []
    for group in groups:
        group_key = []
        for fact in group:
            if strips_to_sas.get(fact):
                for var, val in strips_to_sas[fact]:
                    group_key.append((var, val, str(fact)))
            else:
                print "not in strips_to_sas, left out:", fact
        group_keys.append(group_key)
    return group_keys

def write_translation_key(strips_to_sas):
    var_file = file("variables.groups", "w")
    vars = dict()
    for exp,[(var, val)] in strips_to_sas.iteritems():
        vars.setdefault(var, []).append((val, exp))
    for var in range(len(vars)):
        print >> var_file, "var%d" % var
        vals = sorted(vars[var]) 
        for (val, exp) in vals:
            print >> var_file, "   %d: %s" % (val, exp)
        if val != -2:
            print >> var_file, "   %d: <none of those>" % (val + 1)

def write_mutex_key(mutex_key):
    invariants_file = file("all.groups", "w")
    print >> invariants_file, "begin_groups"
    print >> invariants_file, len(mutex_key)
    for group in mutex_key:
        #print map(str, group)
        no_facts = len(group)
        print >> invariants_file, "group"
        print >> invariants_file, no_facts
        for var, val, fact in group:
            #print fact
            assert str(fact).startswith("Atom ")
            predicate = str(fact)[5:].split("(")[0]
            #print predicate
            rest = str(fact).split("(")[1]
            rest = rest.strip(")").strip()
            if not rest == "":
                #print "there are args" , rest
                args = rest.split(",")
            else:
                args = []
            print_line = "%d %d %s %d " % (var, val, predicate, len(args))
            for arg in args:
                print_line += str(arg).strip() + " "
            #print fact
            #print print_line
            print >> invariants_file, print_line
    print >> invariants_file, "end_groups"
    invariants_file.close()


if __name__ == "__main__":
    import pddl
    print "Parsing..."
    import __builtin__
    __builtin__.containsQuantifiedConditions = False
    task = pddl.open()
    if task.domain_name in ["protocol", "rover"]:
        # This is, of course, a HACK HACK HACK!
        # The real issue is that ALLOW_CONFLICTING_EFFECTS = True
        # is actually the correct semantics, but then we don't get to filter
        # out operators that are impossible to apply due to mutexes between
        # different SAS+ variables. For example,
        # ALLOW_CONFLICTING_EFFECTS = True does not filter on(a,a) in
        # blocksworld/4-0.
        ALLOW_CONFLICTING_EFFECTS = True

    # EXPERIMENTAL!
    # import psyco
    # psyco.full()

    print("Contains quantified condition(s): %r" % containsQuantifiedConditions)
    
    sas_task = pddl_to_sas(task)
    print "Writing output..."
    sas_task.output(file("output.sas", "w"))
    out_file = open("output.sas","a")
    out_file.write("%d\n" % containsQuantifiedConditions)
    out_file.close()

    print "Done!"
