# -*- coding: utf-8 -*-

from collections import defaultdict
import itertools

import constraints
import pddl
import tools

# Notes:
# All parts of an invariant always use all non-counted variables
# -> the arity of all predicates covered by an invariant is either the
# number of the invariant variables or this value + 1
#
# we currently keep the assumption that each predicate occurs at most once
# in every invariant.

def invert_list(alist):
    result = defaultdict(list)
    for pos, arg in enumerate(alist):
        result[arg].append(pos)
    return result


def instantiate_factored_mapping(pairs):
    part_mappings = [[zip(preimg, perm_img) for perm_img in tools.permutations(img)]
                     for (preimg, img) in pairs]
    return tools.cartesian_product(part_mappings)

                
def find_unique_variables(action, invariant):
    # find unique names for invariant variables
    params = set([p.name for p in action.parameters])
    for eff in action.effects[0]:
        params.update([p.name for p in eff.parameters])
    for eff in action.effects[1]:
        params.update([p.name for p in eff.parameters])
    inv_vars = []
    counter = itertools.count()
    for _ in xrange(invariant.arity()):
        while True:
            new_name = "?v%i" % counter.next()
            if new_name not in params:
                inv_vars.append(pddl.Variable(new_name))
                break
    return inv_vars


def get_literals(condition):
    if isinstance(condition, pddl.Literal):
        yield condition
    elif isinstance(condition, pddl.Conjunction):
        for literal in condition.parts:
            if isinstance(literal, pddl.Literal):
                yield literal


def ensure_conjunction_sat(system, *parts):
    """Modifies the constraint system such that it is only solvable if the
       conjunction of all parts is satisfiable. 

       Each part must be an iterator, generator, or an iterable over
       literals."""
    pos = defaultdict(set)
    neg = defaultdict(set)
    for literal in itertools.chain(*parts):
        if literal.predicate == "=": # use (in)equalities in conditions
            if literal.negated:
                n = constraints.NegativeClause([literal.args])
                system.add_negative_clause(n)
            else:
                a = constraints.Assignment([literal.args])
                system.add_assignment_disjunction([a])
        else:
            if literal.negated:
                neg[literal.predicate].add(literal)
            else:
                pos[literal.predicate].add(literal)

    for pred, posatoms in pos.iteritems():
        if pred in neg:
            for posatom in posatoms:
                for negatom in neg[pred]:
                    parts = zip(negatom.args, posatom.args)
                    if parts:
                        negative_clause = constraints.NegativeClause(parts)
                        system.add_negative_clause(negative_clause)


def ensure_cover(system, literal, invariant, inv_vars):
    """Modifies the constraint system such that it is only solvable if the
       invariant covers the literal"""
    a = invariant.get_covering_assignments(inv_vars, literal)
    system.add_assignment_disjunction(a)


def ensure_inequality(system, literal1, literal2):
    """Modifies the constraint system such that it is only solvable if the
       literal instantiations are not equal (ignoring whether one is negated and
       the other is not)"""
    if (literal1.predicate == literal2.predicate and
        literal1.parts):
        parts = zip(literal1.parts, literal2.parts)
        system.add_negative_clause(constraints.NegativeClause(parts))


class InvariantPart:
    def __init__(self, predicate, order, omitted_pos=-1):
        self.predicate = predicate
        self.order = order
        self.omitted_pos = omitted_pos

    def __eq__(self, other):
        # This implies equality of the omitted_pos component.
        return self.predicate == other.predicate and self.order == other.order

    def __ne__(self, other):
        return self.predicate != other.predicate or self.order != other.order

    def __hash__(self):
        return hash((self.predicate, tuple(self.order)))

    def __str__(self):
        var_string = " ".join(map(str, self.order))
        omitted_string = ""
        if self.omitted_pos != -1:
            omitted_string = " [%d]" % self.omitted_pos
        return "%s %s%s" % (self.predicate, var_string, omitted_string)

    def arity(self):
        return len(self.order)

    def get_assignment(self, parameters, literal):
        equalities = [(arg, literal.args[argpos]) 
                      for arg, argpos in zip(parameters, self.order)] 
        return constraints.Assignment(equalities)

    def get_parameters(self, literal):
        return [literal.args[pos] for pos in self.order]

    def instantiate(self, parameters):
        args = ["?X"] * (len(self.order) + (self.omitted_pos != -1))
        for arg, argpos in zip(parameters, self.order):
            args[argpos] = arg
        return pddl.Atom(self.predicate, args)

    def possible_mappings(self, own_literal, other_literal):
        allowed_omissions = len(other_literal.args) - len(self.order)
        if allowed_omissions not in (0, 1):
            return []
        own_parameters = self.get_parameters(own_literal)
        arg_to_ordered_pos = invert_list(own_parameters)
        other_arg_to_pos = invert_list(other_literal.args)
        factored_mapping = []

        for key, other_positions in other_arg_to_pos.iteritems():
            own_positions = arg_to_ordered_pos.get(key, [])
            len_diff = len(own_positions) - len(other_positions)
            if len_diff >= 1 or len_diff <= -2 or len_diff == -1 and not allowed_omissions:
                return []
            if len_diff:
                own_positions.append(-1)
                allowed_omissions = 0
            factored_mapping.append((other_positions, own_positions))
        return instantiate_factored_mapping(factored_mapping)

    def possible_matches(self, own_literal, other_literal):
        assert self.predicate == own_literal.predicate
        result = []
        for mapping in self.possible_mappings(own_literal, other_literal):
            new_order = [None] * len(self.order)
            omitted = -1
            for (key, value) in mapping:
                if value == -1:
                    omitted = key
                else:
                    new_order[value] = key
            result.append(InvariantPart(other_literal.predicate, new_order, omitted))
        return result

    def matches(self, other, own_literal, other_literal):
        return self.get_parameters(own_literal) == other.get_parameters(other_literal)


class Invariant(object):
    # An invariant is a logical expression of the type
    #   forall V1...Vk: sum_(part in parts) weight(part, V1, ..., Vk) <= 1.
    # k is called the arity of the invariant.
    # A "part" is a symbolic fact only variable symbols in {V1, ..., Vk, X};
    # the symbol X may occur at most once.

    def __init__(self, parts):
        self.parts = frozenset(parts)
        self.predicates = set([part.predicate for part in parts])
        self.predicate_to_part = dict([(part.predicate, part) for part in parts])
        assert len(self.parts) == len(self.predicates)
    
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.parts == other.parts
    
    def __ne__(self, other):
        return self.__class__ != other.__class__ or self.parts != other.parts
    
    def __hash__(self):
        return hash(self.parts)

    def __str__(self):
        return "{%s}" % ", ".join(map(str, self.parts))

    def arity(self):
        return iter(self.parts).next().arity()

    def get_parameters(self, atom):
        return self.predicate_to_part[atom.predicate].get_parameters(atom)

    def instantiate(self, parameters):
        return [part.instantiate(parameters) for part in self.parts]


class SafeInvariant(Invariant):
    def get_covering_assignments(self, parameters, atom):
        part = self.predicate_to_part[atom.predicate]
        return [part.get_assignment(parameters, atom)]
        # if there were more parts for the same predicate the list
        # contained more than one element

    def check_balance(self, balance_checker, enqueue_func):
        # Check balance for this hypothesis.
        actions_to_check = set()
        for part in self.parts:
            actions_to_check |= balance_checker.get_threats(part.predicate)

        temp_unbalanced_actions = set()
        for action in actions_to_check:
            heavy_action = balance_checker.get_heavy_action(action.name)
            if self.operator_too_heavy(heavy_action):
                return False
            unbalanced, new_candidates = self.operator_unbalanced(action,
                                                temp_unbalanced_actions)
            if unbalanced:
                for candidate in new_candidates:
                    enqueue_func(candidate)
                return False

        # special case (typical resource usage): no mutex check neccessary
        for action, effect, _ in temp_unbalanced_actions:
            if not self.conditions_require_weight_1(action, effect):
                break
        else:
            return True
        if len(temp_unbalanced_actions) > 1:
            # actually, here we would like to check that all these unbalanced
            # actions are mutex (cannot be executed concurrently), so if
            # somebody wants to implement that, go ahead.
            for _, _, candidates in temp_unbalanced_actions:
                for candidate in candidates:
                    enqueue_func(candidate)
            return False

        return True

    def operator_too_heavy(self, h_action):
        inv_vars = find_unique_variables(h_action, self)
        for time in xrange(2):
            cond_time = 2 * time
            add_effects = [eff for eff in h_action.effects[time] 
                           if isinstance(eff.peffect, pddl.Literal) and 
                              not eff.peffect.negated and
                              self.predicate_to_part.get(eff.peffect.predicate)]
          
            if len(add_effects) <= 1:
                continue
                
            for eff1, eff2 in itertools.combinations(add_effects, 2):
                system = constraints.ConstraintSystem()
                ensure_inequality(system, eff1.peffect, eff2.peffect)
                ensure_cover(system, eff1.peffect, self, inv_vars)
                ensure_cover(system, eff2.peffect, self, inv_vars)
                ensure_conjunction_sat(system, 
                                       get_literals(h_action.condition[cond_time]),
                                       get_literals(eff1.condition[cond_time]),
                                       get_literals(eff2.condition[cond_time]),
                                       [eff1.peffect.negate()],
                                       [eff2.peffect.negate()])
                if system.is_solvable():
                    return True
        return False
            
    def operator_unbalanced(self, action, temp_unbalanced_actions):
        inv_vars = find_unique_variables(action, self)
        relevant_effs = [[],[]]
        add_effects = [[],[]]
        del_effects = [[],[]]
        for time in xrange(2):
            relevant_effs[time] = [eff for eff in action.effects[time] 
                                   if isinstance(eff.peffect, pddl.Literal) and
                                   self.predicate_to_part.get(eff.peffect.predicate)]
            add_effects[time] = [eff for eff in relevant_effs[time]
                                 if not eff.peffect.negated]
            del_effects[time] = [eff for eff in relevant_effs[time]
                                 if eff.peffect.negated]
        for time in xrange(2):
            poss_temporary_cand = ((time == 1) and not len(add_effects[0]))
            for eff in add_effects[time]:
                unbal, new_candidates = self.add_effect_unbalanced(action,
                                                    eff, del_effects[time],
                                                    inv_vars, time)
                if unbal:
                    if not poss_temporary_cand:
                        return unbal, new_candidates

                    if poss_temporary_cand:
                        unbal, new_cands = self.add_effect_temporarily_unbalanced(action,
                                                eff, del_effects[0], inv_vars)
                        if unbal:
                            new_candidates += new_cands
                            return unbal, new_candidates

                        # add_effect is temporarily unbalanced
                        new_candidates = tuple(new_candidates)
                        temp_unbalanced_actions.add((action, eff,
                                                    new_candidates))
                    
        return False, None

    def minimal_covering_renamings(self, action, add_effect, inv_vars):
        """computes the minimal renamings of the action parameters such
           that the add effect is covered by the action. 
           Each renaming is an constraint system"""

        # add_effect must be covered
        assigs = self.get_covering_assignments(inv_vars, add_effect.peffect)

        minimal_renamings = []
        params = [p.name for p in action.parameters]
        for assignment in assigs:
            system = constraints.ConstraintSystem()
            system.add_assignment(assignment)
            # renaming of operator parameters must be minimal
            minimality_clauses = []
            mapping = assignment.get_mapping()
            if len(params) > 1:
                for (n1, n2) in itertools.combinations(params, 2):
                    if mapping.get(n1, n1) != mapping.get(n2, n2):
                        negative_clause = constraints.NegativeClause([(n1, n2)])
                        system.add_negative_clause(negative_clause)
            minimal_renamings.append(system)
        return minimal_renamings
    
    def add_effect_unbalanced(self, action, add_effect, del_effects, 
                              inv_vars, time):
        cond_time = 2 * time
        minimal_renamings = self.minimal_covering_renamings(action, add_effect,
                                                            inv_vars)
       
        lhs_by_pred = defaultdict(list)
        for lit in itertools.chain(get_literals(action.condition[cond_time]),
                                   get_literals(add_effect.condition[cond_time]),
                                   get_literals(add_effect.peffect.negate())):
            lhs_by_pred[lit.predicate].append(lit)

        for del_effect in del_effects:
            if (time == 1 and 
                (del_effect.condition[0] or del_effect.condition[1])):
               continue
            minimal_renamings = self.unbalanced_renamings(del_effect, add_effect,
                inv_vars, lhs_by_pred, time, minimal_renamings)
            if not minimal_renamings:
                return False, None

        # Otherwise, the balance check fails => Generate new candidates.
        return True, self.refine_candidate(add_effect, action, 0)
        
    def add_effect_temporarily_unbalanced(self, action, add_effect, start_del_effects, inv_vars):
        """at-end add effect has corresponding at-start del effect, so it could
        be balanced if no other action interferes"""
        minimal_renamings = self.minimal_covering_renamings(action, add_effect,
                                                            inv_vars)
       
        lhs_by_pred = defaultdict(list)
        for lit in itertools.chain(get_literals(action.condition[0]),
                                   get_literals(add_effect.condition[0]),
                                   get_literals(add_effect.peffect.negate())):
            lhs_by_pred[lit.predicate].append(lit)

        for del_effect in start_del_effects:
            minimal_renamings = self.temp_unbalanced_renamings(del_effect, add_effect,
                inv_vars, lhs_by_pred, minimal_renamings)
            if not minimal_renamings:
                return False, None

        # Otherwise, the balance check fails => Generate new candidates.
        return True, self.refine_candidate(add_effect, action, 0)

    def refine_candidate(self, add_effect, action, time):
        """refines the candidate for an add effect that is unbalanced in the
           action and adds the refined one to the queue"""
        new_candidates = []
        part = self.predicate_to_part[add_effect.peffect.predicate]
        for del_eff in [eff for eff in action.effects[time] 
                        if isinstance(eff.peffect, pddl.Literal) and 
                        eff.peffect.negated]:
            if del_eff.peffect.predicate not in self.predicate_to_part:
                for match in part.possible_matches(add_effect.peffect, 
                                                   del_eff.peffect):
                    new_candidates.append(SafeInvariant(self.parts.union((match,))))
        return new_candidates

    def temp_unbalanced_renamings(self, del_effect, add_effect,
        inv_vars, lhs_by_pred, unbalanced_renamings):
        """returns the renamings from unbalanced renamings for which
           the start_del_effect does not balance the end_add_effect."""
        system = constraints.ConstraintSystem()
        ensure_cover(system, del_effect.peffect, self, inv_vars)
       
        still_unbalanced = []
        for renaming in unbalanced_renamings:
            new_sys = system.combine(renaming)
            if self.lhs_satisfiable(renaming, lhs_by_pred):
                implies_system = self.imply_del_effect(del_effect, lhs_by_pred,
                                                       0)
                if not implies_system:
                    still_unbalanced.append(renaming)
                    continue
                new_sys = new_sys.combine(implies_system)
            if not new_sys.is_solvable():
                still_unbalanced.append(renaming)
        return still_unbalanced

    def unbalanced_renamings(self, del_effect, add_effect,
        inv_vars, lhs_by_pred, time, unbalanced_renamings):
        """returns the renamings from unbalanced renamings for which
           the del_effect does not balance the add_effect."""
        system = constraints.ConstraintSystem()
        ensure_inequality(system, add_effect.peffect, del_effect.peffect)
        ensure_cover(system, del_effect.peffect, self, inv_vars)
       
        still_unbalanced = []
        for renaming in unbalanced_renamings:
            new_sys = system.combine(renaming)
            if self.lhs_satisfiable(renaming, lhs_by_pred):
                implies_system = self.imply_del_effect(del_effect, lhs_by_pred,
                                                       time)
                if not implies_system:
                    still_unbalanced.append(renaming)
                    continue
                new_sys = new_sys.combine(implies_system)
            if not new_sys.is_solvable():
                still_unbalanced.append(renaming)
        return still_unbalanced

    def lhs_satisfiable(self, renaming, lhs_by_pred):
        system = renaming.copy()
        ensure_conjunction_sat(system, *itertools.chain(lhs_by_pred.values()))
        return system.is_solvable()

    def imply_del_effect(self, del_effect, lhs_by_pred, time):
        """returns a constraint system that is solvable if lhs implies
           the del effect (only if lhs is satisfiable). If a solvable
           lhs never implies the del effect, return None."""
        # del_effect.cond and del_effect.atom must be implied by lhs
        implies_system = constraints.ConstraintSystem()
        del_eff_condition = del_effect.condition[time * 2]
        for literal in itertools.chain(get_literals(del_eff_condition),
                                       [del_effect.peffect.negate()]):
            poss_assignments = []
            for match in lhs_by_pred[literal.predicate]:
                if match.negated != literal.negated:
                    continue
                else:
                    a = constraints.Assignment(zip(literal.args, match.args))
                    poss_assignments.append(a)
            if not poss_assignments:
                return None
            implies_system.add_assignment_disjunction(poss_assignments)
        return implies_system


    def conditions_require_weight_1(self, action, add_effect):
        inv_vars = find_unique_variables(action, self)
        minimal_renamings = self.minimal_covering_renamings(action, add_effect,
                                                            inv_vars)
        relevant_conditions = set(get_literals(action.condition[0]))
        relevant_conditions |= set(get_literals(add_effect.condition[0]))
        relevant_conditions = [atom for atom in relevant_conditions
                               if not atom.negated and
                                  self.predicate_to_part.get(atom.predicate)]

        negative_clauses = []
        for atom in relevant_conditions:
                a = self.get_covering_assignments(inv_vars, atom)[0]
                if not len(a.equalities):
                    return True
                negative_clauses.append(constraints.NegativeClause(a.equalities))
        for renaming in minimal_renamings:
            for clause in negative_clauses:
                system = renaming.copy()
                system.add_negative_clause(clause)
                if not system.is_solvable():
                    break
            else:
                return False
        return True


class UnsafeInvariant(Invariant):
  def check_balance(self, balance_checker, enqueue_func):
    # Check balance for this hypothesis.
    actions_to_check = set()
    for part in self.parts:
      actions_to_check |= balance_checker.get_threats(part.predicate)
    for action in actions_to_check:
      if not self.check_action_balance(balance_checker, action, enqueue_func):
        return False
    return True

  def check_action_balance(self, balance_checker, action, enqueue_func):
    # Check balance for this hypothesis with regard to one action.
    if isinstance(action,pddl.Action):
      del_effects = [eff for eff in action.effects if isinstance(eff.peffect,pddl.NegatedAtom)]
      add_effects = [eff for eff in action.effects if isinstance(eff.peffect,pddl.Atom)]
      matched_add_effects = []
      for eff in add_effects:
        part = self.predicate_to_part.get(eff.peffect.predicate)
        if part:
          for previous_part, previous_peffect in matched_add_effects:
            if previous_part.matches(part, previous_peffect, eff.peffect) \
               and previous_peffect != eff.peffect: # "Airport" has duplicate effects
              return False # operator too heavy
          if not self.find_matching_del_effect(part, eff, del_effects, enqueue_func):
            return False
          matched_add_effects.append((part, eff.peffect))
      return True
    else: #if isinstance(action,pddl.DurativeAction)
      start_del_effects = [eff for eff in action.effects[0] if isinstance(eff.peffect,pddl.NegatedAtom)]
      end_del_effects = [eff for eff in action.effects[1] if isinstance(eff.peffect,pddl.NegatedAtom)]
      start_add_effects = [eff for eff in action.effects[0] if isinstance(eff.peffect,pddl.Atom)]
      end_add_effects = [eff for eff in action.effects[1] if isinstance(eff.peffect,pddl.Atom)]

      matched_start_add_effects = []
      matched_end_add_effects = []
      for eff in start_add_effects:
        part = self.predicate_to_part.get(eff.peffect.predicate)
        if part:
          for previous_part, previous_peffect in matched_start_add_effects:
            if previous_part.matches(part, previous_peffect, eff.peffect) \
               and previous_peffect != eff.peffect: # "Airport" has duplicate effects
              return False # operator too heavy
          if not self.find_matching_del_effect(part, eff, start_del_effects, enqueue_func):
            return False
          matched_start_add_effects.append((part, eff.peffect))
      for eff in end_add_effects:
        part = self.predicate_to_part.get(eff.peffect.predicate)
        if part:
          check_all_del_effects = True
          found_start_del = False
          found_end_del = False
          for previous_part, previous_peffect in matched_end_add_effects:
            if previous_part.matches(part, previous_peffect, eff.peffect) \
               and previous_peffect != eff.peffect: # "Airport" has duplicate effects
              return False # operator too heavy
          for previous_part, previous_peffect in matched_start_add_effects:
            if previous_part.matches(part, previous_peffect, eff.peffect) \
               and previous_peffect != eff.peffect: # "Airport" has duplicate effects
              check_all_del_effects = False
              break
          if check_all_del_effects:
            found_start_del = self.find_matching_del_effect(part, eff, start_del_effects, 
                                                            enqueue_func, False)
          found_end_del = self.find_matching_del_effect(part, eff, end_del_effects, 
                                                            enqueue_func, False)
          if not (found_start_del or found_end_del):
            if not found_end_del:
              self.generate_new_candidates(part, eff, end_del_effects, enqueue_func)
            if check_all_del_effects and not found_start_del:
              self.generate_new_candidates(part, eff, start_del_effects, enqueue_func)
            return False
          matched_end_add_effects.append((part, eff.peffect))
      return True

  def find_matching_del_effect(self, part, add_effect, del_effects, enqueue_func, generate_new=True):
    # Check balance for this hypothesis with regard to one add effect.
    for del_eff in del_effects:
      del_part = self.predicate_to_part.get(del_eff.peffect.predicate)
      if del_part and part.matches(del_part, add_effect.peffect, del_eff.peffect):
        return True
    # Otherwise, no match => Generate new candidates.
    if generate_new:
      self.generate_new_candidates(part, add_effect, del_effects, enqueue_func)
    return False # Balance check failed.

  def generate_new_candidates(self, part, add_effect, del_effects, enqueue_func):
    for del_eff in del_effects:
      if del_eff.peffect.predicate not in self.predicate_to_part:
        for match in part.possible_matches(add_effect.peffect, del_eff.peffect):
          enqueue_func(UnsafeInvariant(self.parts.union((match,))))

