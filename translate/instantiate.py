#! /usr/bin/env python
# -*- coding: latin-1 -*-

from collections import defaultdict

import translate.build_model as build_model
import translate.pddl_to_prolog as pddl_to_prolog
import translate.normalize as normalize  # because of "get_function_predicate"
from translate.pddl.actions import DurativeAction, Action, PropositionalAction, PropositionalDurativeAction
from translate.pddl.conditions import Literal, Atom, NegatedAtom, Falsity, Truth, Conjunction, Disjunction, \
    UniversalCondition, ExistentialCondition, FunctionComparison, NegatedFunctionComparison, FunctionTerm, \
    ObjectTerm, Variable, parse_term
from translate.pddl.f_expression import FunctionAssignment, Assign, NumericConstant, PrimitiveNumericExpression
from translate.pddl.pddl_types import Type, TypedObject
from translate.pddl.effects import Effect
from translate.pddl.axioms import NumericAxiom, Axiom


def get_fluent_facts(task, model):
    fluent_predicates = normalize.get_fluent_predicates(task)
    return set([fact for fact in model
                if fact.predicate in fluent_predicates])


def get_fluent_functions(model):
    fluent_pnes = set()
    for atom in model:
        if isinstance(atom.predicate, PrimitiveNumericExpression):
            fluent_pnes.add(PrimitiveNumericExpression(atom.predicate.symbol, atom.args))
    return fluent_pnes


def get_objects_by_type(typed_objects, types):
    type_dict = dict((type.name, type) for type in types)
    result = {}
    for obj in typed_objects:
        supertypes = type_dict[obj.type].supertype_names
        for type_name in [obj.type] + supertypes:
            result.setdefault(type_name, []).append(obj.name)
    return result


def init_function_values(init_facts):
    assignments = [func_assign for func_assign in init_facts
                   if isinstance(func_assign, FunctionAssignment)]
    init_values = {}
    for assignment in assignments:
        init_values[assignment.fluent] = assignment.expression
    return init_values


def instantiate(task, model):
    relaxed_reachable = False
    fluent_facts = get_fluent_facts(task, model)
    fluent_functions = get_fluent_functions(model)

    ## HACK: This is a not very clean way of initializing the previously
    ## added functions that store the duration of an action to a haphazardly value
    for atom in model:
        if isinstance(atom.predicate, str) and atom.predicate.startswith("defined!duration_"):
            pne = PrimitiveNumericExpression(atom.predicate.replace("defined!", "", 1), atom.args)
            value = NumericConstant(1.0)
            init_assign = Assign(pne, value)
            task.init.append(init_assign)

    init_facts = set(task.init)  # TODO adapt
    init_function_vals = init_function_values(init_facts)

    #  print "** fluent functions"
    #  for function in fluent_functions:
    #    function.dump()
    #  print "** fluent facts"
    #  for fact in fluent_facts:
    #    print fact
    #  print "** init facts"
    #  for fact in init_facts:
    #    print fact

    type_to_objects = get_objects_by_type(task.objects, task.types)

    instantiated_actions = []
    instantiated_durative_actions = []
    instantiated_axioms = []
    instantiated_numeric_axioms = set()
    new_constant_numeric_axioms = set()
    reachable_action_parameters = defaultdict(list)
    for atom in model:
        if isinstance(atom.predicate, Action):
            action = atom.predicate
            parameters = action.parameters
            if isinstance(action.condition, ExistentialCondition):
                parameters = list(parameters)
                parameters += action.condition.parameters
            variable_mapping = dict([(Variable(par.name), arg)
                                     for par, arg in zip(parameters, atom.args)])
            inst_action = action.instantiate(variable_mapping, init_facts,
                                             fluent_facts, init_function_vals, fluent_functions,
                                             task, new_constant_numeric_axioms, type_to_objects)
            if inst_action:
                instantiated_actions.append(inst_action)
        elif isinstance(atom.predicate, DurativeAction):
            action = atom.predicate
            parameters = action.parameters
            reachable_action_parameters[action.name].append(parameters)
            for condition in action.condition:
                if isinstance(condition, ExistentialCondition):
                    parameters = list(parameters)
                    parameters += condition.parameters
            variable_mapping = dict([(Variable(par.name), arg)
                                     for par, arg in zip(parameters, atom.args)])
            inst_action = action.instantiate(variable_mapping, init_facts, fluent_facts,
                                             init_function_vals, fluent_functions,
                                             task, new_constant_numeric_axioms, type_to_objects)
            if inst_action:
                instantiated_durative_actions.append(inst_action)
        elif isinstance(atom.predicate, Axiom):
            axiom = atom.predicate
            parameters = axiom.parameters
            if isinstance(axiom.condition, ExistentialCondition):
                parameters = list(parameters)
                parameters += axiom.condition.parameters
            variable_mapping = dict([(Variable(par.name), arg)
                                     for par, arg in zip(parameters, atom.args)])
            inst_axiom = axiom.instantiate(variable_mapping, init_facts, fluent_facts,
                                           fluent_functions, init_function_vals, task,
                                           new_constant_numeric_axioms)
            if inst_axiom:
                instantiated_axioms.append(inst_axiom)
        elif isinstance(atom.predicate, NumericAxiom):
            axiom = atom.predicate
            variable_mapping = dict([(Variable(par.name), arg)
                                     for par, arg in zip(axiom.parameters, atom.args)])
            new_constant_numeric_axioms = set()
            inst_axiom = axiom.instantiate(variable_mapping, fluent_functions, init_function_vals,
                                           task, new_constant_numeric_axioms)
            instantiated_numeric_axioms.add(inst_axiom)
        elif atom.predicate == "@goal-reachable":
            relaxed_reachable = True
        instantiated_numeric_axioms |= new_constant_numeric_axioms

    return (relaxed_reachable, fluent_facts, fluent_functions, instantiated_actions,
            instantiated_durative_actions, instantiated_axioms,
            instantiated_numeric_axioms, reachable_action_parameters)


def explore(task):
    prog = pddl_to_prolog.translate(task)
    model = build_model.compute_model(prog)
    return instantiate(task, model)
