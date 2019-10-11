import itertools

import pddl_types
import f_expression
import tasks

def parse_condition(alist):
    condition = parse_condition_aux(alist, False)
    return condition

def parse_condition_aux(alist, negated):
    """Parse a PDDL condition. The condition is translated into NNF on the fly."""
    tag = alist[0]

    if is_function_comparison(alist):
        args = [f_expression.parse_expression(arg) for arg in alist[1:]]
        assert len(args) == 2, args
        if negated:
            return NegatedFunctionComparison(tag, args, True)
        else:
            return FunctionComparison(tag, args, True)
    elif tag in ("and", "or", "not", "imply"):
        args = alist[1:]
        if tag == "imply":
            assert len(args) == 2
        if tag == "not":
            assert len(args) == 1
            return parse_condition_aux(args[0], not negated)
    elif tag in ("forall", "exists"):
        import __builtin__
        __builtin__.containsQuantifiedConditions = True
        parameters = pddl_types.parse_typed_list(alist[1])
        args = alist[2:]
        assert len(args) == 1
    elif negated:
        return NegatedAtom(alist[0], [parse_term(term) for term in alist[1:]])
    else:
        return Atom(alist[0],[parse_term(term) for term in alist[1:]])


    if tag == "imply":
        parts = [parse_condition_aux(args[0], not negated),
                 parse_condition_aux(args[1], negated)]
        tag = "or"
    else:
        parts = [parse_condition_aux(part, negated) for part in args]
    if tag == "and" and not negated or tag == "or" and negated:
        return Conjunction(parts)
    elif tag == "or" and not negated or tag == "and" and negated:
        return Disjunction(parts)
    elif tag == "forall" and not negated or tag == "exists" and negated:
        return UniversalCondition(parameters, parts)
    elif tag == "exists" and not negated or tag == "forall" and negated:
        return ExistentialCondition(parameters, parts)

def parse_durative_condition(alist):
    """Parse a durative PDDL condition. i
       The condition is translated into NNF on the fly.
       Returns triple [start condition, over all condition, end condition]"""
    if len(alist)==0:
        return [Truth(), Truth(),Truth()]
    tag = alist[0]
    if tag == "and":
        args = alist[1:]
        parts = [parse_durative_condition(part) for part in args]
        parts_begin = [part[0] for part in parts]
        parts_end = [part[1] for part in parts]
        parts_all = [part[2] for part in parts]
        return [Conjunction(parts_begin),Conjunction(parts_end),Conjunction(parts_all)]
    elif tag == "forall":
        parameters = pddl_types.parse_typed_list(alist[1])
        args = alist[2:]
        assert len(args) == 1
        parts = [parse_durative_condition(part) for part in args]
        parts_begin = [part[0] for part in parts]
        parts_end = [part[1] for part in parts]
        parts_all = [part[2] for part in parts]
        return [UniversalCondition(parameters, parts_begin),
            UniversalCondition(parameters, parts_end),
            UniversalCondition(parameters, parts_all)]
    elif tag == "at":
        assert len(alist) == 3
        assert alist[1] in ("start", "end")
        condition = parse_condition_aux(alist[2], False)
        if alist[1] == "start":
            return [condition, Truth(), Truth()]
        else:
            return [Truth(), Truth(), condition]
    elif tag == "over":
        assert alist[1] == "all"
        assert len(alist) == 3
        condition = parse_condition_aux(alist[2], False)
        return [Truth(), condition, Truth()]

def is_function_comparison(alist):
    tag = alist[0]
    if tag in (">","<",">=","<="):
        return True
    if not tag == "=":
        return False

    # tag is '='
    symbol = alist[1]
    if isinstance(symbol,list):
        if symbol[0] in ("+","/","*","-"):
            return True
        symbol = symbol[0]
    if (tasks.Task.FUNCTION_SYMBOLS.get(symbol,"object")=="number" or 
        symbol.replace(".","").isdigit()):
        return True
    return False

def parse_literal(alist):
    if alist[0] == "not":
        assert len(alist) == 2
        alist = alist[1]
        return NegatedAtom(alist[0], [parse_term(term) for term in alist[1:]])
    else:
        return Atom(alist[0], [parse_term(term) for term in alist[1:]])

def parse_term(term):
    if isinstance(term, list):
        return FunctionTerm(term[0],[parse_term(t) for t in term[1:]])
    elif term.startswith("?"):
        return Variable(term)
    elif term in tasks.Task.FUNCTION_SYMBOLS:
        return FunctionTerm(term,[])
    else:
        return ObjectTerm(term)
        
def dump_temporal_condition(condition,indent="  "):
    assert len(condition)==3
    if not isinstance(condition[0],Truth):
        print "%sat start:" % indent
        condition[0].dump(indent+"  ")
    if not isinstance(condition[1],Truth):
        print "%sover all:" % indent
        condition[1].dump(indent+"  ")
    if not isinstance(condition[2],Truth):
        print "%sat end:" % indent
        condition[2].dump(indent+"  ")


# Conditions (of any type) are immutable, because they need to
# be hashed occasionally. Immutability also allows more efficient comparison
# based on a precomputed hash value.
#
# Careful: Most other classes (e.g. Effects, Axioms, Actions) are not!

class Condition(object):
    def __init__(self, parts):
        self.parts = tuple(parts)
        self.hash = hash((self.__class__, self.parts))
    def __hash__(self):
        return self.hash
    def __ne__(self, other):
        return not self == other
    def dump(self, indent="  "):
        print "%s%s" % (indent, self._dump())
        for part in self.parts:
            part.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def _postorder_visit(self, method_name, *args):
        part_results = [part._postorder_visit(method_name, *args)
                        for part in self.parts] 
        method = getattr(self, method_name, self._propagate)
        return method(part_results, *args)
    def _propagate(self, parts, *args):
        return self.change_parts(parts)
    def simplified(self):
        return self._postorder_visit("_simplified")
    def relaxed(self):
        return self._postorder_visit("_relaxed")
    def untyped(self):
        return self._postorder_visit("_untyped")

    def uniquify_variables(self, type_map, renamings={}):
        # Cannot used _postorder_visit because this requires preorder
        # for quantified effects.
        if not self.parts:
            return self
        else:
            return self.__class__([part.uniquify_variables(type_map, renamings)
                                   for part in self.parts])
    def to_untyped_strips(self):
        raise ValueError("Not a STRIPS condition: %s" % self.__class__.__name__)
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        raise ValueError("Cannot instantiate condition: not normalized")
    def free_variables(self):
        result = set()
        for part in self.parts:
            result |= part.free_variables()
        return result
    def has_disjunction(self):
        for part in self.parts:
            if part.has_disjunction():
                return True
        return False
    def has_existential_part(self):
        for part in self.parts:
            if part.has_existential_part():
                return True
        return False
    def has_universal_part(self):
        for part in self.parts:
            if part.has_universal_part():
                return True
        return False

class ConstantCondition(Condition):
    parts = ()
    def __init__(self):
        self.hash = hash(self.__class__)
    def change_parts(self, parts):
        return self
    def __eq__(self, other):
        return self.__class__ is other.__class__

class Impossible(Exception):
    pass

class Falsity(ConstantCondition):
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        raise Impossible()
    def negate(self):
        return Truth()

class Truth(ConstantCondition):
    def to_untyped_strips(self):
        return []
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        pass
    def negate(self):
        return Falsity()

class JunctorCondition(Condition):
    def __eq__(self, other):
        # Compare hash first for speed reasons.
        return (self.hash == other.hash and
                self.__class__ is other.__class__ and
                self.parts == other.parts)
    def change_parts(self, parts):
        return self.__class__(parts)

class Conjunction(JunctorCondition):
    def _simplified(self, parts):
        result_parts = []
        for part in parts:
            if isinstance(part, Conjunction):
                result_parts += part.parts
            elif isinstance(part, Falsity):
                return Falsity()
            elif not isinstance(part, Truth):
                result_parts.append(part)
        if not result_parts:
            return Truth()
        if len(result_parts) == 1:
            return result_parts[0]
        return Conjunction(result_parts)
    def to_untyped_strips(self):
        result = []
        for part in self.parts:
            result += part.to_untyped_strips()
        return result
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        assert not result, "Condition not simplified"
        for part in self.parts:
            part.instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                             fluent_functions, task, new_axiom, result)
    def negate(self):
        return Disjunction([p.negate() for p in self.parts])

class Disjunction(JunctorCondition):
    def _simplified(self, parts):
        result_parts = []
        for part in parts:
            if isinstance(part, Disjunction):
                result_parts += part.parts
            elif isinstance(part, Truth):
                return Truth()
            elif not isinstance(part, Falsity):
                result_parts.append(part)
        if not result_parts:
            return Falsity()
        if len(result_parts) == 1:
            return result_parts[0]
        return Disjunction(result_parts)
    def negate(self):
        return Conjunction([p.negate() for p in self.parts])
    def has_disjunction(self):
        return True

class QuantifiedCondition(Condition):
    def __init__(self, parameters, parts):
        self.parameters = tuple(parameters)
        self.parts = tuple(parts)
        self.hash = hash((self.__class__, self.parameters, self.parts))
    def __eq__(self, other):
        # Compare hash first for speed reasons.
        return (self.hash == other.hash and
                self.__class__ is other.__class__ and
                self.parameters == other.parameters and
                self.parts == other.parts)
    def _dump(self, indent="  "):
        arglist = ", ".join(map(str, self.parameters))
        return "%s %s" % (self.__class__.__name__, arglist)
    def _simplified(self, parts):
        if isinstance(parts[0], ConstantCondition):
            return parts[0]
        else:
            return self._propagate(parts)
    def uniquify_variables(self, type_map, renamings={}):
        renamings = dict(renamings) # Create a copy.
        new_parameters = [par.uniquify_name(type_map, renamings)
                          for par in self.parameters]
        new_parts = (self.parts[0].uniquify_variables(type_map, renamings),)
        return self.__class__(new_parameters, new_parts)

    def free_variables(self):
        result = Condition.free_variables(self)
        for par in self.parameters:
            result.discard(par.name)
        return result
    def change_parts(self, parts):
        return self.__class__(self.parameters, parts)

class UniversalCondition(QuantifiedCondition):
#    def _untyped(self, parts):
#        type_literals = [NegatedAtom(par.type, [par.name]) for par in self.parameters]
#        return UniversalCondition(self.parameters,
#                                  [Disjunction(type_literals + parts)])
    def negate(self):
        return ExistentialCondition(self.parameters, [p.negate() for p in self.parts])
    def has_universal_part(self):
        return True

class ExistentialCondition(QuantifiedCondition):
#    def _untyped(self, parts):
#        type_literals = [Atom(par.type, [par.name]) for par in self.parameters]
#        return ExistentialCondition(self.parameters,
#                                    [Conjunction(type_literals + parts)])
    def negate(self):
        return UniversalCondition(self.parameters, [p.negate() for p in self.parts])
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        assert not result, "Condition not simplified"
        self.parts[0].instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                                  fluent_functions, task, new_axiom, result)
    def has_existential_part(self):
        return True

class Literal(Condition):
    parts = []
    def __eq__(self, other):
        # Compare hash first for speed reasons.
        return (self.hash == other.hash and
                self.__class__ is other.__class__ and
                self.predicate == other.predicate and
                self.args == other.args)
    def __init__(self, predicate, args):
        self.predicate = predicate
        self.args = tuple(args)
        self.hash = hash((self.__class__, self.predicate, self.args))
    def __str__(self):
        return "%s(%s)" % (self.predicate,
                              ", ".join(map(str, self.args)))
    def dump(self, indent="  "):
        print "%s%s %s" % (indent, self._dump(), self.predicate)
        for arg in self.args:
            arg.dump(indent + "  ")
    def change_parts(self, parts):
        return self
    def uniquify_variables(self, type_map, renamings={}):
        if not self.args:
            return self
        else:
            return self.__class__(self.predicate,[arg.uniquify_variables(type_map, renamings)
                                                  for arg in self.args])
    def rename_variables(self, renamings):
        new_args = [arg.rename_variables(renamings) for arg in self.args]
        return self.__class__(self.predicate, new_args)
    def free_variables(self):
        result = set()
        for arg in self.args:
            result |= arg.free_variables()
        return result

class Atom(Literal):
    negated = False
    def to_untyped_strips(self):
        return [self]
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        args = [var_mapping.get(arg, arg) for arg in self.args]
        atom = Atom(self.predicate, args)
        if atom in fluent_facts:
            result.append(atom)
        elif atom not in init_facts:
            raise Impossible()
    def negate(self):
        return NegatedAtom(self.predicate, self.args)
    def positive(self):
        return self

class NegatedAtom(Literal):
    negated = True
    def _relaxed(self, parts):
        return Truth()
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        args = [var_mapping.get(arg, arg) for arg in self.args]
        atom = Atom(self.predicate, args)
        if atom in fluent_facts:
            result.append(NegatedAtom(self.predicate, args))
        elif atom in init_facts:
            raise Impossible()
    def negate(self):
        return Atom(self.predicate, self.args)
    positive = negate

class FunctionComparison(Condition): # comparing numerical functions
    negated = False
    def _relaxed(self, parts):
        return Truth()
    def __init__(self, comparator, parts, compare_to_zero = False):
        self.comparator = comparator
        assert len(parts) == 2
        if compare_to_zero:
            self.parts = (f_expression.Difference(parts), f_expression.NumericConstant(0))
        else:
            self.parts = tuple(parts)
        self.hash = hash((self.__class__, self.comparator, self.parts))
    def _dump(self, indent="  "):
        return "%s %s" % (self.__class__.__name__, self.comparator)
    def __eq__(self, other):
        # Compare hash first for speed reasons.
        return (self.hash == other.hash and
                self.__class__ is other.__class__ and
                self.comparator == other.comparator and
                self.parts == other.parts)
    def __str__(self):
        return "%s (%s %s)" % (self.__class__.__name__, self.comparator,
                              ", ".join(map(str, self.parts)))
    def uniquify_variables(self, type_map, renamings={}):
        return self.__class__(self.comparator,[part.rename_variables(renamings)
                                   for part in self.parts])
    def has_disjunction(self):
        return False
    def has_universal_part(self):
        return False
    def has_existential_part(self):
        return False
    def negate(self):
        return NegatedFunctionComparison(self.comparator, self.parts)
    def change_parts(self, parts):
        return self.__class__(self.comparator,parts)
    def primitive_numeric_expressions(self):
        result = set()
        for part in self.parts:
            result |= part.primitive_numeric_expressions()
        return result
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, result):
        instantiated_parts = [part.instantiate(var_mapping, fluent_functions, 
                                               init_function_vals, task, new_axiom) 
                                               for part in self.parts]
        #TODO: future work: eliminate non-fluent functions
        result.append(self.__class__(self.comparator,instantiated_parts))
    def positive(self):
        return self
        
    
class NegatedFunctionComparison(FunctionComparison):
    negated = True
    def negate(self):
        return FunctionComparison(self.comparator, self.parts)
    positive = negate

class Term(object):
    def dump(self, indent="  "):
        print "%s%s %s" % (indent, self._dump(), self.name)
        for arg in self.args:
            arg.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def __eq__(self, other):
        return (self.__class__ is other.__class__ and
                self.args == other.args)
    def uniquify_variables(self, type_map, renamings={}):
        if not self.args:
            return self
        else:
            return self.__class__(self.name,[arg.uniquify_variables(type_map, renamings)
                                             for arg in self.args])
    def compile_objectfunctions_aux(self, used_variables, recurse_object_terms=True):
        return ([],[],self)
    def rename_variables(self, renamings):
        new_args = [renamings.get(arg, arg) for arg in self.args]
        return self.__class__(self.name, new_args)
    def free_variables(self):
        result = set()
        for arg in self.args:
            result |= arg.free_variables()
        return result

class FunctionTerm(Term):
    def __init__(self, name, args=[]):
        self.name = name
        self.args = args
    def __str__(self):
        return "%s(%s)" % (self.name, ", ".join(map(str, self.args)))
    def compile_objectfunctions_aux(self, used_variables, recurse_object_terms=True):
    # could be done by postorder visit
        typed_vars = []
        conjunction_parts = []
        new_args = []
        for arg in self.args:
            if recurse_object_terms:
                typed,parts,new_term = arg.compile_objectfunctions_aux(used_variables)
                typed_vars += typed
                conjunction_parts += parts
                new_args.append(new_term)
    
        for counter in itertools.count(1):
            new_var_name = "?v" + str(counter)
            if new_var_name not in used_variables:
                used_variables.append(new_var_name)
                typed_vars.append(pddl_types.TypedObject(new_var_name, tasks.Task.FUNCTION_SYMBOLS[self.name]))
                new_var = Variable(new_var_name)
                break

        if recurse_object_terms:
            pred_name = function_predicate_name(self.name)
            new_args.append(new_var)
            atom = Atom(pred_name,new_args)
            conjunction_parts = [atom] + conjunction_parts
        else:
            conjunction_parts = [self] 
        return (typed_vars, conjunction_parts, new_var)
    
class Variable(Term):
    args = []
    def __init__(self, name):
        self.name = name
        self.hash = hash((self.__class__,self.name))
    def __eq__(self, other):
        return (self.__class__ is other.__class__ and
                self.name == other.name)
    def __cmp__(self,other):
        return cmp(self.name,other.name)
    def __hash__(self):
        return self.hash
    def __str__(self):
        return "<%s>" % self.name
    def uniquify_variables(self, type_map, renamings={}):
        return self.rename_variables(renamings)
    def rename_variables(self, renamings):
        return self.__class__(renamings.get(self.name,self.name))
    def free_variables(self):
        return set((self.name,))

class ObjectTerm(Term):
    args = []
    def __init__(self, name):
        self.name = name
        self.hash = hash((self.__class__,self.name))
    def __eq__(self, other):
        return (self.__class__ is other.__class__ and
                self.name == other.name)
    def __cmp__(self,other):
        return cmp(self.name,other.name)
    def __str__(self):
        return "<%s>" % self.name
    def __hash__(self):
        return self.hash
    def free_variables(self):
        return set()
    def rename_variables(self, renamings):
        return self

def function_predicate_name(functionname):
    return "%s!val" % functionname

