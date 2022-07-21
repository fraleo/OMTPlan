#! /usr/bin/env python
# -*- coding: latin-1 -*-

import itertools

import translate.normalize as normalize
from translate.pddl.actions import DurativeAction, Action, PropositionalAction, PropositionalDurativeAction
from translate.pddl.conditions import Literal, Atom, NegatedAtom, Falsity, Truth, Conjunction, Disjunction, \
    UniversalCondition, ExistentialCondition, FunctionComparison, NegatedFunctionComparison, FunctionTerm, \
    ObjectTerm, Variable, parse_term
from translate.pddl.f_expression import FunctionAssignment, Assign, NumericConstant, PrimitiveNumericExpression
from translate.pddl.pddl_types import Type, TypedObject
from translate.pddl.effects import Effect
from translate.pddl.axioms import NumericAxiom


class PrologProgram:
    def __init__(self):
        self.facts = []
        self.rules = []
        self.objects = set()

        def predicate_name_generator():
            for count in itertools.count():
                yield "p$%d" % count

        self.new_name = predicate_name_generator()

    def add_fact(self, atom):
        self.facts.append(Fact(atom))
        self.objects |= set(atom.args)

    def add_rule(self, rule):
        self.rules.append(rule)

    def dump(self):
        for fact in self.facts:
            print(fact)
        for rule in self.rules:
            print(getattr(rule, "type", "none"), rule)

    def normalize(self):
        # Normalized prolog programs have the following properties:
        # 1. Each variable that occurs in the effect of a rule also occurs in its
        #    condition.
        # 2. The variables that appear in each effect or condition are distinct.
        # 3. There are no rules with empty condition.
        self.remove_free_effect_variables()
        self.split_duplicate_arguments()
        self.convert_trivial_rules()

    def split_rules(self):
        import translate.split_rules as split_rules
        # Splits rules whose conditions can be partitioned in such a way that
        # the parts have disjoint variable sets, then split n-ary joins into
        # a number of binary joins, introducing new pseudo-predicates for the
        # intermediate values.
        new_rules = []
        for rule in self.rules:
            new_rules += split_rules.split_rule(rule, self.new_name)
        self.rules = new_rules

    def remove_free_effect_variables(self):
        """Remove free effect variables like the variable Y in the rule
        p(X, Y) :- q(X). This is done by introducing a new predicate
        @object, setting it true for all objects, and translating the above
        rule to p(X, Y) :- q(X), @object(Y).
        After calling this, no new objects should be introduced!"""

        # Note: This should never be necessary for typed domains.
        # Leaving it in at the moment regardless.
        must_add_predicate = False
        for rule in self.rules:
            eff_vars = get_variables([rule.effect])
            cond_vars = get_variables(rule.conditions)
            if not eff_vars.issubset(cond_vars):
                must_add_predicate = True
                eff_vars -= cond_vars
                for var in eff_vars:
                    rule.add_condition(Atom("@object", [var]))
        if must_add_predicate:
            print("Unbound effect variables: Adding @object predicate.")
            self.facts += [Fact(Atom("@object", [obj])) for obj in self.objects]

    def split_duplicate_arguments(self):
        """Make sure that no variable occurs twice within the same symbolic fact,
        like the variable X does in p(X, Y, X). This is done by renaming the second
        and following occurrences of the variable and adding equality conditions.
        For example p(X, Y, X) is translated to p(X, Y, X@0) with the additional
        condition =(X, X@0); the equality predicate must be appropriately instantiated
        somewhere else."""
        printed_message = False
        for rule in self.rules:
            if rule.rename_duplicate_variables() and not printed_message:
                # print "Duplicate arguments: Adding equality conditions."
                printed_message = True

    def convert_trivial_rules(self):
        """Convert rules with an empty condition into facts.
        This must be called after bounding rule effects, so that rules with an
        empty condition must necessarily have a variable-free effect.
        Variable-free effects are the only ones for which a distinction between
        ground and symbolic atoms is not necessary."""
        must_delete_rules = []
        for i, rule in enumerate(self.rules):
            if not rule.conditions:
                assert not get_variables([rule.effect])
                self.add_fact(Atom(rule.effect.predicate, rule.effect.args))
                must_delete_rules.append(i)
        if must_delete_rules:
            # print "Trivial rules: Converted to facts."
            for rule_no in must_delete_rules[::-1]:
                del self.rules[rule_no]


def get_variables(symbolic_atoms):
    variables = set()
    for sym_atom in symbolic_atoms:
        # variables |= set([arg for arg in sym_atom.args if arg[0] == "?"])
        variables |= set([arg for arg in sym_atom.args if isinstance(arg, Variable)])
    return variables


class Fact:
    def __init__(self, atom):
        self.atom = atom

    def __str__(self):
        return "%s." % self.atom


class Rule:
    def __init__(self, conditions, effect):
        self.conditions = conditions
        self.effect = effect

    def add_condition(self, condition):
        self.conditions.append(condition)

    def get_variables(self):
        return get_variables(self.conditions + [self.effect])

    def _rename_duplicate_variables(self, atom, new_conditions):
        used_variables = set()
        new_args = list(atom.args)
        for i, var in enumerate(atom.args):
            if isinstance(var, Variable):
                if var in used_variables:
                    new_var_name = "%s@%d" % (var.name, len(new_conditions))
                    new_var = Variable(new_var_name)
                    new_args[i] = new_var
                    new_conditions.append(Atom("=", [var, new_var]))
                else:
                    used_variables.add(var)
        atom.args = tuple(new_args)

    def rename_duplicate_variables(self):
        new_conditions = []
        self._rename_duplicate_variables(self.effect, new_conditions)
        for condition in self.conditions:
            self._rename_duplicate_variables(condition, new_conditions)
        self.conditions += new_conditions
        return bool(new_conditions)

    def __str__(self):
        cond_str = ", ".join(map(str, self.conditions))
        return "%s :- %s." % (self.effect, cond_str)


def translate_typed_object(prog, obj, type_dict):
    supertypes = type_dict[obj.type].supertype_names
    for type_name in [obj.type] + supertypes:
        prog.add_fact(Atom(type_name, [ObjectTerm(obj.name)]))


def translate_init(prog, fact):
    if isinstance(fact, Atom):
        prog.add_fact(fact)
    elif isinstance(fact, FunctionAssignment):
        atom = normalize.get_function_predicate(fact.fluent)
        prog.add_fact(atom)
    else:
        assert False


def translate_facts(prog, task):
    type_dict = dict((type.name, type) for type in task.types)
    for obj in task.objects:
        translate_typed_object(prog, obj, type_dict)
    for fact in task.init:
        translate_init(prog, fact)


def translate(task):
    normalize.normalize(task)
    prog = PrologProgram()
    translate_facts(prog, task)
    for conditions, effect in normalize.build_exploration_rules(task):
        prog.add_rule(Rule(conditions, effect))
    prog.normalize()
    prog.split_rules()
    return prog


def test_normalization():
    prog = PrologProgram()
    prog.add_fact(Atom("at", ["foo", "bar"]))
    prog.add_fact(Atom("truck", ["bollerwagen"]))
    prog.add_fact(Atom("truck", ["segway"]))
    prog.add_rule(Rule([Atom("truck", ["?X"])], Atom("at", ["?X", "?Y"])))
    prog.add_rule(Rule([Atom("truck", ["X"]), Atom("location", ["?Y"])],
                       Atom("at", ["?X", "?Y"])))
    prog.add_rule(Rule([Atom("truck", ["?X"]), Atom("location", ["?Y"])],
                       Atom("at", ["?X", "?X"])))
    prog.add_rule(Rule([Atom("p", ["?Y", "?Z", "?Y", "?Z"])],
                       Atom("q", ["?Y", "?Y"])))
    prog.add_rule(Rule([], Atom("foo", [])))
    prog.add_rule(Rule([], Atom("bar", ["X"])))
    prog.normalize()
    prog.dump()
