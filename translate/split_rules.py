# split_rules: Split rules whose conditions fall into different "connected
# components" (where to conditions are related if they share a variabe) into
# several rules, one for each connected component and one high-level rule.

import copy

from translate.pddl_to_prolog import Rule, get_variables
import translate.graph as graph
import translate.greedy_join as greedy_join
from translate.pddl.actions import DurativeAction, Action, PropositionalAction, PropositionalDurativeAction
from translate.pddl.conditions import Literal, Atom, NegatedAtom, Falsity, Truth, Conjunction, Disjunction, \
    UniversalCondition, ExistentialCondition, FunctionComparison, NegatedFunctionComparison, FunctionTerm, \
    ObjectTerm, Variable, parse_term
from translate.pddl.f_expression import FunctionAssignment, Assign, NumericConstant, PrimitiveNumericExpression
from translate.pddl.pddl_types import Type, TypedObject
from translate.pddl.effects import Effect
from translate.pddl.axioms import NumericAxiom


def get_connected_conditions(conditions):
    agraph = graph.Graph(conditions)
    var_to_conditions = dict([(var, [])
                              for var in get_variables(conditions)])
    for cond in conditions:
        for var in cond.args:
            if isinstance(var, Variable):
                var_to_conditions[var].append(cond)

    # Connect conditions with a common variable
    for var, conds in var_to_conditions.items():
        for cond in conds[1:]:
            agraph.connect(conds[0], cond)
    return agraph.connected_components()


def project_rule(rule, conditions, name_generator):
    predicate = next(name_generator)
    effect_variables = set(rule.effect.args) & get_variables(conditions)
    effect = Atom(predicate, list(effect_variables))
    projected_rule = Rule(conditions, effect)
    return projected_rule


def split_rule(rule, name_generator):
    important_conditions, trivial_conditions = [], []
    for cond in rule.conditions:
        for term in cond.args:
            if isinstance(term, Variable):
                important_conditions.append(cond)
                break
        else:
            trivial_conditions.append(cond)

    # important_conditions = [cond for cond in rule.conditions if cond.args]
    # trivial_conditions = [cond for cond in rule.conditions if not cond.args]

    components = get_connected_conditions(important_conditions)
    if len(components) == 1 and not trivial_conditions:
        return split_into_binary_rules(rule, name_generator)

    projected_rules = [project_rule(rule, conditions, name_generator)
                       for conditions in components]
    result = []
    for proj_rule in projected_rules:
        result += split_into_binary_rules(proj_rule, name_generator)

    conditions = [proj_rule.effect for proj_rule in projected_rules] + \
                 trivial_conditions
    combining_rule = Rule(conditions, rule.effect)
    if len(conditions) >= 2:
        combining_rule.type = "product"
    else:
        combining_rule.type = "project"
    result.append(combining_rule)
    return result


def split_into_binary_rules(rule, name_generator):
    if len(rule.conditions) <= 1:
        rule.type = "project"
        return [rule]
    return greedy_join.greedy_join(rule, name_generator)
