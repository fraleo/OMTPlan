import pddl
import sas_tasks

from collections import defaultdict

def handle_axioms(operators, durative_operators, axioms, goals):
    print "Processing axioms..."

    axioms_by_atom = get_axioms_by_atom(axioms)

    axiom_literals = compute_necessary_axiom_literals(axioms_by_atom, operators, 
                                                      durative_operators, goals)
    axiom_init = get_axiom_init(axioms_by_atom, axiom_literals)
    axioms = simplify_axioms(axioms_by_atom, axiom_literals)

    axioms, true_atoms, false_atoms = compute_constant_axioms(axioms)
    # we moved some axioms (actually their heads) to true_atoms and false_atoms
    # (i.e. they are not axioms any more). now repair axioms_by_atom by
    # rebuilding it
    axioms_by_atom = get_axioms_by_atom(axioms)
    # the axiom_literals are only used to know which ones need to be negated, so
    # we remove the constant heads from those
    axiom_literals = [a for a in axiom_literals
                      if a.positive() not in true_atoms and
                         a.positive() not in false_atoms]
    # The same goes for init. The true_atoms and false_atoms should be handled
    # in the translation
    axiom_init = [a for a in axiom_init
                  if a.positive() not in true_atoms and
                     a.positive() not in false_atoms]

    axioms = compute_negative_axioms(axioms_by_atom, axiom_literals)
    # NOTE: compute_negative_axioms more or less invalidates axioms_by_atom.
    #       Careful with that axe, Eugene!
    axiom_layers = compute_axiom_layers(axioms, axiom_init)
    print "Found", len(true_atoms), "axioms that are always true and", len(false_atoms), "that are always false"
    return axioms, list(axiom_init), axiom_layers, true_atoms, false_atoms

def get_axioms_by_atom(axioms):
    axioms_by_atom = {}
    for axiom in axioms:
        axioms_by_atom.setdefault(axiom.effect, []).append(axiom)
    return axioms_by_atom

def compute_axiom_layers(axioms, axiom_init):
    NO_AXIOM = -1
    UNKNOWN_LAYER = -2
    FIRST_MARKER = -3

    depends_on = {}
    for axiom in axioms:
        effect_atom = axiom.effect.positive()
        effect_sign = not axiom.effect.negated
        effect_init_sign = effect_atom in axiom_init
        if effect_sign != effect_init_sign:
            depends_on.setdefault(effect_atom, set())
            for condition in axiom.condition:
                condition_atom = condition.positive()
                condition_sign = not condition.negated
                condition_init_sign = condition_atom in axiom_init
                if condition_sign == condition_init_sign:
                    depends_on[effect_atom].add((condition_atom, +1))
                else:
                    depends_on[effect_atom].add((condition_atom, +0))

    layers = dict([(atom, UNKNOWN_LAYER) for atom in depends_on])
    def find_level(atom, marker):
        layer = layers.get(atom, NO_AXIOM)
        if layer == NO_AXIOM:
            return 0

        if layer == marker:
            # Found positive cycle: May return 0 but not set value.
            return 0
        elif layer <= FIRST_MARKER:
            # Found negative cycle: Error.
            assert False, "Cyclic dependencies in axioms; cannot stratify."
        if layer == UNKNOWN_LAYER:
            layers[atom] = marker
            layer = 0
            for (condition_atom, bonus) in depends_on[atom]:
                layer = max(layer, find_level(condition_atom, marker - bonus) + bonus)
            layers[atom] = layer
        return layer
    for atom in depends_on:
        find_level(atom, FIRST_MARKER)

    #for atom, layer in layers.iteritems():
    #  print "Layer %d: %s" % (layer, atom)
    return layers

def compute_necessary_axiom_literals(axioms_by_atom, operators, 
                                     durative_operators, goal):
    necessary_literals = set()
    queue = []

    def register_literals(literals, negated):
        for literal in literals:
            if isinstance(literal,pddl.Literal):
                if literal.positive() in axioms_by_atom:   # This is an axiom literal
                    if negated:
                        literal = literal.negate()
                    if literal not in necessary_literals:
                        necessary_literals.add(literal)
                        queue.append(literal)

    # Initialize queue with axioms required for goal and operators.
    register_literals(goal, False)
    for op in operators:
        register_literals(op.condition, False)
        for (cond, _) in op.add_effects:
            register_literals(cond, False)
        for (cond, _) in op.del_effects:
            register_literals(cond, True)

    for op in durative_operators:
        for time in range(3):
            register_literals(op.conditions[time], False)
        for time in range(2):
            for (cond, _) in op.add_effects[time]:
                register_literals(cond, False)
            for (cond, _) in op.del_effects[time]:
                register_literals(cond, True)

    while queue:
        literal = queue.pop()
        axioms = axioms_by_atom[literal.positive()]
        for axiom in axioms:
            register_literals(axiom.condition, literal.negated)
    return necessary_literals

def get_axiom_init(axioms_by_atom, necessary_literals):
    result = set()
    for atom in axioms_by_atom:
        assert(not (atom in necessary_literals and atom.negate() in necessary_literals))
        if atom not in necessary_literals and atom.negate() in necessary_literals:
            # Initial value for axiom: False (which is omitted due to closed world
            # assumption) unless it is only needed negatively.
            result.add(atom)
    return result

def simplify_axioms(axioms_by_atom, necessary_literals):
    necessary_atoms = set([literal.positive() for literal in necessary_literals])
    new_axioms = []
    for atom in necessary_atoms:
        axioms = simplify(axioms_by_atom[atom])
        axioms_by_atom[atom] = axioms
        new_axioms += axioms
    return new_axioms

def remove_duplicates(alist):
    next_elem = 1
    for i in xrange(1, len(alist)):
        if alist[i] != alist[i - 1]:
            alist[next_elem] = alist[i]
            next_elem += 1
    alist[next_elem:] = []

def simplify(axioms):
    """Remove duplicate axioms, duplicates within axioms, and dominated axioms."""

    # Remove duplicates from axiom conditions.
    for axiom in axioms:
        axiom.condition.sort()
        remove_duplicates(axiom.condition)

    # Remove dominated axioms.
    axioms_by_literal = {}
    for axiom in axioms:
        for literal in axiom.condition:
            axioms_by_literal.setdefault(literal, set()).add(id(axiom))

    axioms_to_skip = set()
    for axiom in axioms:
        if id(axiom) in axioms_to_skip:
            continue   # Required to keep one of multiple identical axioms.
        if not axiom.condition: # empty condition: dominates everything
            return [axiom]
        literals = iter(axiom.condition)
        dominated_axioms = axioms_by_literal[literals.next()]
        for literal in literals:
            dominated_axioms &= axioms_by_literal[literal]
        for dominated_axiom in dominated_axioms:
            if dominated_axiom != id(axiom):
                axioms_to_skip.add(dominated_axiom)
    return [axiom for axiom in axioms if id(axiom) not in axioms_to_skip]


def compute_constant_axioms(axioms):
    """ Computes which axioms always evaluate to the same constant values """
    true_atoms = set()
    false_atoms = set()
    new_axioms = set(axioms)
    # this will be a subset of axioms, where some axioms have simpler conditions
    # the removed axiom's heads should appear in true_atoms or false_atoms

    axioms_by_condition = defaultdict(set)
    axioms_by_negated_condition = defaultdict(set)

    queue = [] # true literals that have not been processed, yet
    condition_counter = dict() 
    # number of unsatisfied conditions for each axiom
    axiom_counter = defaultdict(int) # number of axioms for each effect

    # initialize counters and queue
    for axiom in new_axioms:
        assert not axiom.effect.negated
        axiom_counter[axiom.effect] += 1
        if not axiom.condition:
            if axiom.effect not in true_atoms:
                true_atoms.add(axiom.effect)
                queue.append(axiom.effect)
        else:
            for cond in axiom.condition:
                axioms_by_condition[cond].add(axiom)
                axioms_by_negated_condition[cond.negate()].add(axiom)
            condition_counter[axiom] = len(set(axiom.condition))

    while queue:
        literal = queue.pop()
        for axiom in axioms_by_condition[literal]:
            condition_counter[axiom] -= 1
            if not condition_counter[axiom]:
                if axiom.effect not in true_atoms:
                    true_atoms.add(axiom.effect)
                    queue.append(axiom.effect)
        for axiom in axioms_by_negated_condition[literal]:
            # axiom can never trigger, so we remove it
            if axiom in new_axioms:
                new_axioms.remove(axiom)
                axiom_counter[axiom.effect] -= 1
                if not axiom_counter[axiom.effect]:
                    # axiom head can never become true
                    assert axiom.effect not in false_atoms
                    false_atoms.add(axiom.effect)
                    queue.append(axiom.effect.negate())

    # filter all axioms from new_atoms that have a constantly true
    # effect and simplify all other axiom conditions
    for axiom in list(new_axioms):
        assert not axiom.effect in false_atoms # should already be removed
        if axiom.effect in true_atoms:
            new_axioms.remove(axiom)
        else:
            axiom.condition = list(set(axiom.condition) - true_atoms)
    return list(new_axioms), list(true_atoms), list(false_atoms)


def compute_negative_axioms(axioms_by_atom, necessary_literals):
    new_axioms = []
    for literal in necessary_literals:
        if literal.negated:
            new_axioms += negate(axioms_by_atom[literal.positive()])
        else:
            new_axioms += axioms_by_atom[literal]
    return new_axioms

def negate(axioms):
    assert axioms
    result = [pddl.PropositionalAxiom(axioms[0].name, [], axioms[0].effect.negate())]
    for axiom in axioms:
        condition = axiom.condition
        assert len(condition) > 0, "Negated axiom impossible; cannot deal with that"
        if len(condition) == 1: # Handle easy special case quickly.
            new_literal = condition[0].negate()
            for result_axiom in result:
                result_axiom.condition.append(new_literal)
        else:
            new_result = []
            for literal in condition:
                literal = literal.negate()
                for result_axiom in result:
                    new_axiom = result_axiom.clone()
                    new_axiom.condition.append(literal)
                    new_result.append(new_axiom)
            result = new_result
    result = simplify(result)
    return result
