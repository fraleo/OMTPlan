#! /usr/bin/env python
# -*- coding: utf-8 -*-

import copy

import pddl

class ConditionProxy(object):
  def clone_owner(self):
    clone = copy.copy(self)
    clone.owner = copy.copy(clone.owner)
    return clone
    
class PreconditionProxy(ConditionProxy):
  def __init__(self, action):
    self.owner = action
    self.condition = action.condition
  def set(self, new_condition):
    self.owner.condition = self.condition = new_condition
  def register_owner(self, task):
    if isinstance(self.owner,pddl.DurativeAction):
        task.durative_actions.append(self.owner)
    else:
        task.actions.append(self.owner)
  def delete_owner(self, task):
    if isinstance(self.owner,pddl.DurativeAction):
        task.durative_actions.remove(self.owner)
    else:
        task.actions.remove(self.owner)
  def build_rules(self, rules, fluent_preds):
    action = self.owner
    for param in action.parameters:
        add_either_rules(param.type,rules)

    rule_head = get_action_predicate(action)

    # we completely use the start conditions.
    # from the other conditions, we use only
    # the types of existential parameters and
    # non-fluent atoms
    if isinstance(self.condition,list):
        rule_body = list(condition_to_rule_body(action.parameters,
                                      self.condition[0]))
        rule_body += list(condition_to_rule_body(action.parameters,
                                     self.condition[1],fluent_preds))
        rule_body += list(condition_to_rule_body(action.parameters,
                                     self.condition[2], fluent_preds))
    else: 
        rule_body = list(condition_to_rule_body(action.parameters,
                                            self.condition))
    rules.append((rule_body, rule_head))
  def get_type_map(self):
    return self.owner.type_map

class EffectConditionProxy(ConditionProxy):
  def __init__(self, action, effect, effecttime=None):
    self.action = action
    self.owner = effect
    self.condition = effect.condition
    self.effecttime = effecttime
  def set(self, new_condition):
    self.owner.condition = self.condition = new_condition
  def register_owner(self, task):
    self.action.effects.append(self.owner)
  def delete_owner(self, task):
    self.action.effects.remove(self.owner)
  def build_rules(self, rules, fluent_preds):
    effect = self.owner
    rule_head = effect.peffect
    fluent_head = None
    if not isinstance(rule_head,pddl.NegatedAtom):
      if isinstance(rule_head,pddl.FunctionAssignment):
        fluent = rule_head.fluent
        rule_head = get_function_predicate(fluent)
        fluent_head = get_fluent_function_predicate(fluent)
      rule_body = [get_action_predicate(self.action)]
      if self.effecttime != None:
        # we use the start condition in any case
        rule_body += condition_to_rule_body([], self.condition[0])
        # for end effects we use all conditions
        if self.effecttime == 1:
          rule_body += condition_to_rule_body([], self.condition[1])
          rule_body += condition_to_rule_body([], self.condition[2])
      else:
        rule_body += condition_to_rule_body([], self.condition)
      rules.append((rule_body, rule_head))
      if fluent_head:
        rules.append((rule_body, fluent_head))

  def get_type_map(self):
    return self.action.type_map

class AxiomConditionProxy(ConditionProxy):
  def __init__(self, axiom):
    self.owner = axiom
    self.condition = axiom.condition
  def set(self, new_condition):
    self.owner.condition = self.condition = new_condition
  def register_owner(self, task):
    task.axioms.append(self.owner)
  def delete_owner(self, task):
    task.axioms.remove(self.owner)
  def build_rules(self, rules, fluent_preds):
    axiom = self.owner
    app_rule_head = get_axiom_predicate(axiom)
    app_rule_body = list(condition_to_rule_body(axiom.parameters, self.condition))
    rules.append((app_rule_body, app_rule_head))
    eff_rule_head = pddl.Atom(axiom.name, [pddl.Variable(par.name) for par in axiom.parameters])
    eff_rule_body = [app_rule_head]
    rules.append((eff_rule_body, eff_rule_head))
  def get_type_map(self):
    return self.owner.type_map

class GoalConditionProxy(ConditionProxy):
  def __init__(self, task):
    self.owner = task
    self.condition = task.goal
  def set(self, new_condition):
    self.owner.goal = self.condition = new_condition
  def register_owner(self, task):
    # TODO: Implement with axioms.
    assert False, "Disjunctive goals not (yet) implemented."
  def delete_owner(self, task):
    # TODO: Implement with axioms.
    assert False, "Disjunctive goals not (yet) implemented."
  def build_rules(self, rules, fluent_preds):
    rule_head_name = "@goal-reachable"
    rule_head = pddl.Atom("@goal-reachable", [])
    rule_body = list(condition_to_rule_body([], self.condition))
    rules.append((rule_body, rule_head))
  def get_type_map(self):
    # HACK!
    # Method uniquify_variables HAS already been called (which is good).
    # We call it here again for its SIDE EFFECT of collecting the type_map
    # (which is bad). Having "top-level conditions" (currently, only goal
    # conditions, but might also include safety conditions and similar)
    # contained in a separate wrapper class that stores a type map might
    # be a better design.
    type_map = {}
    self.condition.uniquify_variables(type_map)
    return type_map

def get_action_predicate(action):
  name = action
  variables = [pddl.Variable(par.name) for par in action.parameters]
  if isinstance(action.condition,list):
    for condition in action.condition:
      if isinstance(condition, pddl.ExistentialCondition):
        variables += [pddl.Variable(par.name) for par in condition.parameters]
  if isinstance(action.condition, pddl.ExistentialCondition):
    variables += [pddl.Variable(par.name) for par in action.condition.parameters]
  return pddl.Atom(name, variables)

def get_axiom_predicate(axiom):
  name = axiom
  variables = [pddl.Variable(par.name) for par in axiom.parameters]
  if isinstance(axiom.condition, pddl.ExistentialCondition):
    variables += [pddl.Variable(par.name) for par in axiom.condition.parameters]
  return pddl.Atom(name, variables)

def all_conditions(task):
  for action in task.actions:
    yield PreconditionProxy(action)
    for effect in action.effects:
      yield EffectConditionProxy(action, effect)
  for action in task.durative_actions:
    yield PreconditionProxy(action)
    for time,timedeffects in enumerate(action.effects):
        for effect in timedeffects:
            yield EffectConditionProxy(action, effect, time)
  for axiom in task.axioms:
    yield AxiomConditionProxy(axiom)
  yield GoalConditionProxy(task)

# [1] Remove universal quantifications from conditions.
#
# Replace, in a top-down fashion, <forall(vars, phi)> by <not(not-all-phi)>,
# where <not-all-phi> is a new axiom.
#
# <not-all-phi> is defined as <not(forall(vars,phi))>, which is of course
# translated to NNF. The parameters of the new axioms are exactly the free
# variables of <forall(vars, phi)>.

def remove_universal_quantifiers(task):
  def recurse(condition):
    # Uses new_axioms_by_condition and type_map from surrounding scope.
    if isinstance(condition, pddl.UniversalCondition):
      axiom_condition = condition.negate()
      parameters = axiom_condition.free_variables()
      axiom = new_axioms_by_condition.get(axiom_condition)
      if not axiom:
        typed_parameters = [pddl.TypedObject(v, type_map[v]) for v in parameters]
        condition = recurse(axiom_condition)
        axiom = task.add_axiom(typed_parameters, condition)
        new_axioms_by_condition[condition] = axiom
      return pddl.NegatedAtom(axiom.name, [pddl.conditions.parse_term(par) for par in parameters]) 
    else:
      new_parts = [recurse(part) for part in condition.parts]
      return condition.change_parts(new_parts)

  new_axioms_by_condition = {}
  for proxy in tuple(all_conditions(task)):
    # Cannot use generator because we add new axioms on the fly.
    if isinstance(proxy.condition,list):
      change = False
      condition = []
      for cond in proxy.condition:
        if cond.has_universal_part():
          if not change:
            change = True
            type_map = proxy.get_type_map()
          condition.append(recurse(cond))
        else:
          condition.append(cond)
      if change:
        proxy.set(condition)
    elif proxy.condition.has_universal_part():
      type_map = proxy.get_type_map()
      proxy.set(recurse(proxy.condition))

    
# [2] Pull disjunctions to the root of the condition.
#
# After removing universal quantifiers, the (k-ary generalization of the)
# following rules suffice for doing that: 
# (1) or(phi, or(psi, psi'))      ==  or(phi, psi, psi')
# (2) exists(vars, or(phi, psi))  ==  or(exists(vars, phi), exists(vars, psi))
# (3) and(phi, or(psi, psi'))     ==  or(and(phi, psi), and(phi, psi'))
def build_DNF(task):
  def recurse(condition):
    disjunctive_parts = []
    other_parts = []
    for part in condition.parts:
      part = recurse(part)
      if isinstance(part, pddl.Disjunction):
        disjunctive_parts.append(part)
      else:
        other_parts.append(part)
    if not disjunctive_parts:
      return condition

    # Rule (1): Associativity of disjunction.
    if isinstance(condition, pddl.Disjunction):
      result_parts = other_parts
      for part in disjunctive_parts:
        result_parts.extend(part.parts)
      return pddl.Disjunction(result_parts)

    # Rule (2): Distributivity disjunction/existential quantification.
    if isinstance(condition, pddl.ExistentialCondition):
      parameters = condition.parameters
      result_parts = [pddl.ExistentialCondition(parameters, (part,))
                      for part in disjunctive_parts[0].parts]
      return pddl.Disjunction(result_parts)

    # Rule (3): Distributivity disjunction/conjunction.
    assert isinstance(condition, pddl.Conjunction)
    result_parts = [pddl.Conjunction(other_parts)]
    while disjunctive_parts:
      previous_result_parts = result_parts
      result_parts = []
      parts_to_distribute = disjunctive_parts.pop().parts
      for part1 in previous_result_parts:
        for part2 in parts_to_distribute:
          result_parts.append(pddl.Conjunction((part1, part2)))
    return pddl.Disjunction(result_parts)

  for proxy in all_conditions(task):
    if isinstance(proxy.condition,list):
      condition = []
      for cond in proxy.condition:
        if cond.has_disjunction():
          condition.append(recurse(cond).simplified())
        else:
          condition.append(cond.simplified())
      proxy.set(condition)
    elif proxy.condition.has_disjunction():
      proxy.set(recurse(proxy.condition).simplified())
    else:
      proxy.set(proxy.condition.simplified())

# [3] Split conditions at the outermost disjunction.
def split_disjunctions(task):
  for proxy in tuple(all_conditions(task)):
    # Cannot use generator directly because we add/delete entries.
    if isinstance(proxy.condition,list):
      change = False
      conditions = [[]]
      for cond in proxy.condition:
        if isinstance(cond, pddl.Disjunction):
          change = True
          old_conditions = conditions
          conditions = []
          for part in cond.parts:
            for condition in old_conditions:
              new_condition = copy.copy(condition)
              new_condition.append(part)
              conditions.append(new_condition)
        else:
          for condition in conditions:
            condition.append(cond)
      if change:
        for condition in conditions:
          new_proxy = proxy.clone_owner()
          new_proxy.set(condition)
          new_proxy.register_owner(task)
        proxy.delete_owner(task)
    elif isinstance(proxy.condition, pddl.Disjunction):
      for part in proxy.condition.parts:
        new_proxy = proxy.clone_owner()
        new_proxy.set(part)
        new_proxy.register_owner(task)
      proxy.delete_owner(task)

# [4] Pull existential quantifiers out of conjunctions and group them.
#
# After removing universal quantifiers and creating the disjunctive form,
# only the following (representatives of) rules are needed:
# (1) exists(vars, exists(vars', phi))  ==  exists(vars + vars', phi)
# (2) and(phi, exists(vars, psi))       ==  exists(vars, and(phi, psi)),
#       if var does not occur in phi as a free variable.
def move_existential_quantifiers(task):
  def recurse(condition):
    existential_parts = []
    other_parts = []
    for part in condition.parts:
      part = recurse(part)
      if isinstance(part, pddl.ExistentialCondition):
        existential_parts.append(part)
      else:
        other_parts.append(part)
    if not existential_parts:
      return condition

    # Rule (1): Combine nested quantifiers.
    if isinstance(condition, pddl.ExistentialCondition):
      new_parameters = condition.parameters + existential_parts[0].parameters
      new_parts = existential_parts[0].parts
      return pddl.ExistentialCondition(new_parameters, new_parts)

    # Rule (2): Pull quantifiers out of conjunctions.
    assert isinstance(condition, pddl.Conjunction)
    new_parameters = []
    new_conjunction_parts = other_parts
    for part in existential_parts:
      new_parameters += part.parameters
      new_conjunction_parts += part.parts
    new_conjunction = pddl.Conjunction(new_conjunction_parts)
    return pddl.ExistentialCondition(new_parameters, (new_conjunction,))

  for proxy in all_conditions(task):
    if isinstance(proxy.condition,list):
      condition = []
      for cond in proxy.condition:
        if cond.has_existential_part():
          condition.append(recurse(cond).simplified())
        else:
          condition.append(cond)
      proxy.set(condition)
    elif proxy.condition.has_existential_part():
      proxy.set(recurse(proxy.condition).simplified())

def remove_object_functions_from_durations(task):
    for act in task.durative_actions:
        used_variables = [var.name for var in act.parameters]
        for time in range(2):
            for index, (op, exp) in enumerate(act.duration[time]):
                typed_vars, function_terms, new_term = \
                    exp.compile_objectfunctions_aux(used_variables, 
                        recurse_object_terms=False)
                act.duration[time][index] = (op, new_term)
                act.parameters += typed_vars
                new_conditions = []
                assert len(typed_vars) == len(function_terms)
                new_conditions = [act.condition[time]]
                for var, term in zip(typed_vars, function_terms):
                    variable = pddl.Variable(var.name)
                    new_condition = pddl.Atom("=", [variable, term])
                    new_conditions.append(new_condition)
                act.condition[time] = pddl.Conjunction(new_conditions)
                

def remove_object_functions(task):
    def recurse(condition, used_variables):
        if isinstance(condition, pddl.Literal):
            typed_vars = []
            conjunction_parts = []
            new_args = []
            for term in condition.args:
                typed,parts,new_term = term.compile_objectfunctions_aux(used_variables)
                typed_vars += typed
                conjunction_parts += parts
                new_args.append(new_term)
            if conjunction_parts == []:
                return condition
            else:
                new_literal = condition.__class__(condition.predicate,new_args)
                conjunction_parts.append(new_literal)
                conjunction = pddl.Conjunction(conjunction_parts)
                return pddl.ExistentialCondition(typed_vars,[conjunction])
        elif isinstance(condition, pddl.FunctionComparison):
            typed_vars = []
            conjunction_parts = []
            new_parts = []
            for part in condition.parts:
                typed,parts,new_part = part.compile_objectfunctions_aux(used_variables)
                typed_vars += typed
                conjunction_parts += parts
                new_parts.append(new_part)
            if conjunction_parts == []:
                return condition
            else:
                new_comparison = condition.__class__(condition.comparator,new_parts)
                conjunction_parts.append(new_comparison)
                conjunction = pddl.Conjunction(conjunction_parts)
                return pddl.ExistentialCondition(typed_vars,[conjunction])
        else:
            new_parts = [recurse(part,used_variables) for part in condition.parts]
            return condition.change_parts(new_parts)
    
    remove_object_functions_from_durations(task)

    for proxy in tuple(all_conditions(task)):
        if isinstance(proxy.condition,list):
            condition = []
            used_variables = set()
            for cond in proxy.condition:
                used_variables |= cond.free_variables()
            used_variables = list(used_variables)
            for cond in proxy.condition:
                condition.append(recurse(cond,used_variables))
            proxy.set(condition)
        else:
            used_variables = list(proxy.condition.free_variables())
            proxy.set(recurse(proxy.condition,used_variables))

def remove_duration_variable(task):
    def recurse(condition, act, time, duration, pnes):
        if isinstance(condition, pddl.FunctionComparison):
            parts = [exp.remove_duration_variable(act, time, duration, pnes)
                        for exp in condition.parts]
            return condition.__class__(condition.comparator, parts)
            #return pddl.FunctionComparison(condition.comparator,parts)
        else:
            new_parts = [recurse(part, act, time, duration, pnes) for part in condition.parts]
            return condition.change_parts(new_parts)

    for act in task.durative_actions:
        assert len(act.duration[1]) == 0, "at end durations are not supported"
        assert len(act.duration[0]) == 1 and act.duration[0][0][0]=="="
        duration = act.duration[0][0][1]
        duration_functions = []

        # remove from action conditions
        condition = []
        for time, cond in enumerate(act.condition):
            condition.append(recurse(cond, act, time, duration, duration_functions))
        act.condition = condition

        for time in range(2):
            for eff in act.effects[time]:
                # remove from effect condition
                condition = []
                for eff_time, cond in enumerate(eff.condition):
                    condition.append(recurse(cond, act, eff_time, duration, duration_functions))
                eff.condition = condition
                # remove from effect
                if isinstance(eff.peffect,pddl.FunctionAssignment):
                    assign = eff.peffect
                    assign.expression = assign.expression.remove_duration_variable(act, 
                                                    time, duration, duration_functions)
        for pne in duration_functions:
            assign = pddl.Assign(pne,duration)
            condition = [pddl.Truth(),pddl.Truth(),pddl.Truth()]
            effect = pddl.Effect([],condition, assign)
            act.effects[0].append(effect)
            task.function_symbols[pne.symbol]="number"


def remove_arithmetic_expressions(task):
    def recurse(condition):
        if isinstance(condition, pddl.FunctionComparison) :
            parts = [task.function_administrator.get_derived_function(exp) for exp in condition.parts]
            if condition.negated:
                return pddl.NegatedFunctionComparison(condition.comparator,parts)
            else:
                return pddl.FunctionComparison(condition.comparator,parts)
        else:
            new_parts = [recurse(part) for part in condition.parts]
            return condition.change_parts(new_parts)

    # remove from conditions
    for proxy in tuple(all_conditions(task)):
        if isinstance(proxy.condition,list):
            condition = []
            for cond in proxy.condition:
                condition.append(recurse(cond))
            proxy.set(condition)
        else:
            proxy.set(recurse(proxy.condition))

    # remove from actions
    admin = task.function_administrator
    for act in task.actions:
        for eff in act.effects:
            if isinstance(eff.peffect,pddl.FunctionAssignment):
                assign = eff.peffect
                assign.expression = admin.get_derived_function(assign.expression)
    for act in task.durative_actions:
        act.duration = ([(op,task.function_administrator.get_derived_function(exp))
                            for (op,exp) in act.duration[0]],
                        [(op,task.function_administrator.get_derived_function(exp))
                            for (op,exp) in act.duration[1]])
        for tempeff in act.effects:
            for eff in tempeff:
                if isinstance(eff.peffect,pddl.FunctionAssignment):
                    assign = eff.peffect
                    assign.expression = admin.get_derived_function(assign.expression)

def substitute_complicated_goal(task):
  goal = task.goal
  if isinstance(goal, pddl.Literal):
    return
  elif isinstance(goal,pddl.Conjunction):
    simple_goal = True
    for item in goal.parts:
      if not isinstance(item,pddl.Literal):
        simple_goal = False
        break
    if simple_goal:
      return
  new_axiom = task.add_axiom([],goal)
  task.goal = pddl.Atom(new_axiom.name, new_axiom.parameters)
            
# Combine Steps [1], [2], [3], [4]
def normalize(task):
  remove_object_functions(task)
  substitute_complicated_goal(task)
  remove_universal_quantifiers(task)
  build_DNF(task)
  split_disjunctions(task)
  move_existential_quantifiers(task)
  remove_duration_variable(task)
  remove_arithmetic_expressions(task)

# [5] Build rules for exploration component.
def build_exploration_rules(task):
  result = []
  fluent_preds = get_fluent_predicates(task)
  
  for proxy in all_conditions(task):
    proxy.build_rules(result, fluent_preds)

  for axiom in task.function_administrator.get_all_axioms():
    # add rules to determine defined functions
    rule_head = get_function_axiom_predicate(axiom)
    rule_body = []
    for part in axiom.parts:
        if isinstance(part,pddl.PrimitiveNumericExpression):
            rule_body.append(get_function_predicate(part))
            
    result.append((rule_body, rule_head))
    rule_body = [rule_head]
    rule_head = get_function_predicate(axiom.get_head())
    result.append((rule_body, rule_head))

    # add rule to determine fluent functions
    rule_head = get_fluent_function_predicate(axiom.get_head())
    for part in axiom.parts:
        if isinstance(part,pddl.PrimitiveNumericExpression):
            new_rule_body = rule_body + [get_fluent_function_predicate(part)]
            result.append((new_rule_body, rule_head))
  return result

def condition_to_rule_body(parameters, condition, fluent_preds = None):
  for par in parameters:
    yield pddl.Atom(par.type, [pddl.Variable(par.name)])
  if not isinstance(condition, pddl.Truth):
    if isinstance(condition, pddl.ExistentialCondition):
      for par in condition.parameters:
        yield pddl.Atom(par.type, [pddl.Variable(par.name)])
      condition = condition.parts[0]
    if isinstance(condition, pddl.Conjunction):
      parts = condition.parts
    else:
      parts = (condition,)
    for part in parts:
      assert isinstance(part, pddl.Literal) or isinstance(part,pddl.FunctionComparison), "Condition not normalized"
      if isinstance(part, pddl.Literal):
        if not part.negated:
            if fluent_preds == None or part.predicate not in fluent_preds:
                yield part
      elif fluent_preds == None: # part is FunctionComparison
        primitives = part.primitive_numeric_expressions()
        for pne in primitives:
            yield get_function_predicate(pne)

def get_function_predicate(pne):
  name = "defined!%s" % pne.symbol
  return pddl.Atom(name, pne.args)

def get_fluent_function_predicate(pne):
  return pddl.Atom(pne,pne.args)

def get_function_axiom_predicate(axiom):
  name = axiom
  args = axiom.parameters
  for part in axiom.parts:
    if isinstance(part, pddl.PrimitiveNumericExpression):
        args += part.args
    elif isinstance(part, pddl.NumericAxiom):
        args += part.parameters
  return pddl.Atom(name, args)

def get_fluent_predicates(task):
  fluent_predicates = set()
  for action in task.actions:
    for effect in action.effects:
      if isinstance(effect.peffect,pddl.Literal):
        fluent_predicates.add(effect.peffect.predicate)
      else:
        predicate = get_function_predicate(effect.peffect.fluent).predicate
        fluent_predicates.add(predicate)
  for action in task.durative_actions:
    for effect in action.effects:
        for eff in effect:
          if isinstance(eff.peffect,pddl.Literal):
            fluent_predicates.add(eff.peffect.predicate)
          else:
            predicate = get_function_predicate(eff.peffect.fluent).predicate
            fluent_predicates.add(predicate)
  for axiom in task.axioms:
    fluent_predicates.add(axiom.name)
  return fluent_predicates 

def add_either_rules(type,rules):
  if isinstance(type,tuple):
    assert type[0]=="either"
    for subtype in type[1:]:
      add_either_rules(subtype,rules)
      rule_head = pddl.Atom(type, [pddl.Variable("?x")])
      rule_body = [pddl.Atom(subtype, [pddl.Variable("?x")])]
      rules.append((rule_body, rule_head))

if __name__ == "__main__":
  task = pddl.open()
  normalize(task)
  task.dump()
