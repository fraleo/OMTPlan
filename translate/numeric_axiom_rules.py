from translate.pddl.actions import DurativeAction, Action, PropositionalAction, PropositionalDurativeAction
from translate.pddl.conditions import Literal, Atom, NegatedAtom, Falsity, Truth, Conjunction, Disjunction, \
    UniversalCondition, ExistentialCondition, FunctionComparison, NegatedFunctionComparison, FunctionTerm, \
    ObjectTerm, Variable, parse_term
from translate.pddl.f_expression import FunctionAssignment, Assign, NumericConstant, PrimitiveNumericExpression
from translate.pddl.pddl_types import Type, TypedObject
from translate.pddl.effects import Effect
from translate.pddl.axioms import NumericAxiom


def handle_axioms(axioms):
    axiom_by_pne = axiom_by_PNE(axioms)
    constant_axioms = identify_constants(axioms, axiom_by_pne)
    axioms_by_layer, max_layer = compute_axiom_layers(axioms, constant_axioms, axiom_by_pne)
    axiom_map = identify_equivalent_axioms(axioms_by_layer, axiom_by_pne)
    return axioms_by_layer, max_layer, axiom_map, constant_axioms


def axiom_by_PNE(axioms):
    return dict([(axiom.effect, axiom) for axiom in axioms])


def identify_constants(axioms, axiom_by_pne):
    def is_constant(axiom):
        if isinstance(axiom, PrimitiveNumericExpression):
            if axiom in axiom_by_pne:
                axiom = axiom_by_pne[axiom]
            else:
                return (False, None)
        if (axiom.op == None and
                isinstance(axiom.parts[0], NumericConstant)):
            return (True, axiom.parts[0].value)
        else:
            all_constants = True
            values = []
            for part in axiom.parts:
                const, val = is_constant(part)
                if not const:
                    all_constants = False
                    break
                values.append(val)
            if all_constants:
                if len(values) == 1:
                    if axiom.op == "-":
                        new_value = -values[0]
                        axiom.op = None
                    else:
                        assert axiom.op == None
                        new_value = values[0]
                    axiom.parts = [NumericConstant(new_value)]
                    return (True, new_value)
                else:
                    calculation = axiom.op.join(map(str, values))
                    new_val = eval(calculation)
                    axiom.parts = [NumericConstant(new_val)]
                    axiom.op = None
                    return (True, new_val)
            else:
                return (False, None)

    constant_axioms = []
    for axiom in axioms:
        const, val = is_constant(axiom)
        if const:
            constant_axioms.append(axiom)
    return constant_axioms


def compute_axiom_layers(axioms, constant_axioms, axiom_by_pne):
    CONSTANT_OR_NO_AXIOM = -1
    UNKNOWN_LAYER = -2

    depends_on = {}
    for axiom in axioms:
        depends_on.setdefault(axiom, [])
        for part in axiom.parts:
            depends_on[axiom].append(part)

    layers = dict([(axiom, UNKNOWN_LAYER) for axiom in axioms])

    def compute_layer(axiom):
        if isinstance(axiom, PrimitiveNumericExpression):
            axiom = axiom_by_pne.get(axiom, None)

        layer = layers.get(axiom, CONSTANT_OR_NO_AXIOM)

        if layer == UNKNOWN_LAYER:
            if axiom in constant_axioms:
                layer = CONSTANT_OR_NO_AXIOM
            else:
                layer = 0
                for part in depends_on[axiom]:
                    layer = max(layer, compute_layer(part) + 1)
            layers[axiom] = layer
        return layer

    max_layer = -2
    for axiom in axioms:
        max_layer = max(max_layer, compute_layer(axiom))

    layer_to_axioms = {}
    for axiom in layers:
        layer_to_axioms.setdefault(layers[axiom], []).append(axiom)
    return layer_to_axioms, max_layer


def identify_equivalent_axioms(axioms_by_layer, axiom_by_pne):
    axiom_map = {}
    for layer, axioms in axioms_by_layer.items():
        axioms.sort(lambda x, y: cmp(str(x), str(y)))
        key_to_unique = {}
        for ax in axioms:
            mapped_args = []
            for p in ax.parts:
                if p in axiom_map:
                    mapped_args.append(axiom_map[p].effect)
                else:
                    mapped_args.append(p)
            key = (ax.op, tuple(mapped_args))
            if key in key_to_unique:  # there has already been an equivalent axiom
                axiom_map[ax.effect] = key_to_unique[key]
            else:
                key_to_unique[key] = ax
    return axiom_map
