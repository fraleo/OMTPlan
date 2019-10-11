import string
import conditions

def isFloat(astring):
    try:
      float(astring)
    except ValueError:
      return False
    return True

def parse_expression(exp, durative=False):
    if isinstance(exp, list):
        alist = exp
        operator_or_functionsymbol = alist[0]
        if operator_or_functionsymbol in ("+","/","*","-"):
            args = [parse_expression(arg,durative) for arg in alist[1:]]
            operator = operator_or_functionsymbol
        elif operator_or_functionsymbol == "?duration":
            return DurationVariable()
        else:
            return PrimitiveNumericExpression(operator_or_functionsymbol,
                                              [conditions.parse_term(arg) for arg in alist[1:]])
        if operator == "+":
            return Sum(args)
        elif operator == "/":
            assert len(args) == 2
            return Quotient(args)
        elif operator == "*":
            return Product(args)
        else:
            if len(args) == 1:
                return AdditiveInverse(args)
            else:
                assert len(args) == 2
                return Difference(args)
    elif isFloat(exp):
        return NumericConstant(string.atof(exp))
    elif exp == "?duration":
        return DurationVariable()
    else:
        return PrimitiveNumericExpression(exp,[])

def parse_assignment(alist, durative=False):
    assert len(alist) == 3
    op = alist[0]
    head = parse_expression(alist[1])
    exp = parse_expression(alist[2],durative)
    if op == "assign" or op == "=":
        return Assign(head, exp)
    elif op == "scale-up":
        return ScaleUp(head, exp)
    elif op == "scale-down":
        return ScaleDown(head, exp)
    elif op == "increase":
        return Increase(head, exp)
    elif op == "decrease":
        return Decrease(head, exp)
    

class FunctionalExpression(object):
    def __init__(self,parts):
        self.parts = tuple(parts)
        self.hash = hash((self.__class__, self.parts))
    def __hash__(self):
        return self.hash
    def __ne__(self, other):
        return not self == other
    def free_variables(self):
        result = set()
        for part in self.parts:
            result |= part.free_variables()
        return result
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
    def primitive_numeric_expressions(self):
        result = set()
        for part in self.parts:
            result |= part.primitive_numeric_expressions()
        return result
    def compile_objectfunctions_aux(self,used_variables, recurse_object_terms=True):
        typed_vars = []
        conjunction_parts = []
        new_parts = []
        for part in self.parts:
            typed,parts,new_part = part.compile_objectfunctions_aux(used_variables,
                                                                    recurse_object_terms)
            typed_vars += typed
            conjunction_parts += parts
            new_parts.append(new_part)
        return (typed_vars,conjunction_parts,self.__class__(new_parts))
    def  instantiate(self, var_mapping, fluent_functions, 
                        init_function_vals, task, new_axioms=[]):
        print self.__class__.__name__
        raise ValueError("Cannot instantiate condition: not normalized")
        

class ArithmeticExpression(FunctionalExpression):
    def __eq__(self,other):
        return (self.hash == other.hash and
                self.__class__ == other.__class__ and
                self.parts == other.parts)
    def rename_variables(self, renamings={}):
        return self.__class__([part.rename_variables(renamings)
                               for part in self.parts])
    def change_parts(self, parts):
        return self.__class__(parts)
    def remove_duration_variable(self, action, time, duration, pnes):
        return self.__class__([part.remove_duration_variable(action, time, duration, pnes)
                               for part in self.parts])

class Quotient(ArithmeticExpression):
    op = "/"
    def __init__(self,parts):
        assert len(parts)==2
        ArithmeticExpression.__init__(self,parts)
    def _simplified(self, parts):
        if isinstance(parts[1], NumericConstant) and parts[1].value == 1:
            return parts[0]
        else:
            return self._propagate(parts)

class Difference(ArithmeticExpression):
    op = "-"
    def __init__(self,parts):
        assert len(parts)==2
        ArithmeticExpression.__init__(self,parts)
    def _simplified(self, parts):
        if isinstance(parts[1], NumericConstant) and parts[1].value == 0:
            return parts[0]
        else:
            return self._propagate(parts)

class AdditiveInverse(ArithmeticExpression):
    op = "-"
    def __init__(self,parts):
        assert len(parts)==1
        ArithmeticExpression.__init__(self,parts)
    def _simplified(self, parts):
        return self._propagate(parts)

class Sum(ArithmeticExpression):
    op = "+"
    def _simplified(self, parts):
        result_parts = []
        for part in parts:
            if isinstance(part, Sum):
                result_parts += part.parts
            elif not (isinstance(part, NumericConstant) and part.value == 0):
                result_parts.append(part)
        if not result_parts:
            return NumericConstant(0)
        if len(result_parts) == 1:
            return result_parts[0]
        return Sum(result_parts)

class Product(ArithmeticExpression):
    op = "*"
    def _simplified(self, parts):
        result_parts = []
        for part in parts:
            if isinstance(part, Product):
                result_parts += part.parts
            elif isinstance(part, NumericConstant) and part.value == 0:
                return NumericConstant(0)
            elif not (isinstance(part, NumericConstant) and part.value == 1):
                result_parts.append(part)
        if not result_parts:
            return NumericConstant(1)
        if len(result_parts) == 1:
            return result_parts[0]
        return Product(result_parts)

class NumericConstant(FunctionalExpression):
    parts = ()
    def __init__(self, value):
        self.value = value
        self.hash = hash((self.__class__, self.value))
    def __eq__(self, other):
        return (self.__class__ == other.__class__ and self.value == other.value)
    def __str__(self):
        return str(self.value)
    def _dump(self):
        return self.value
    def rename_variables(self, renamings={}):
        return self
    def  instantiate(self, var_mapping, fluent_functions, 
                        init_function_vals, task, new_axioms=[]):
        return self
    def change_parts(self, parts):
        return self
    def compile_objectfunctions_aux(self, used_variables, recurse_object_terms=True):
        return ([],[],self)
    def remove_duration_variable(self, action, time, duration, pnes):
        return self

class PrimitiveNumericExpression(FunctionalExpression):
    parts = ()
    def __init__(self, symbol, args):
        self.symbol = symbol
        self.args = tuple(args)
        self.hash = hash((self.__class__, self.symbol, self.args))
    def __str__(self):
        return "PNE %s(%s)" % (self.symbol, ", ".join(map(str, self.args)))
    def __eq__(self, other):
        return (self.__class__ is other.__class__ and
                self.hash == other.hash and
                self.symbol == other.symbol and 
                self.args == other.args) 
    def dump(self, indent="  "):
        print "%s%s" % (indent, self._dump())
        for arg in self.args:
            arg.dump(indent + "  ")
    def _dump(self):
        return str(self)
    def rename_variables(self, renamings):
        new_args = [renamings.get(arg, arg) for arg in self.args]
        return self.__class__(self.symbol, new_args)
    def free_variables(self):
        return set(arg.name for arg in self.args if isinstance(arg,conditions.Variable))
    def change_parts(self, parts):
        return self
    def primitive_numeric_expressions(self):
        return set([self])
    def compile_objectfunctions_aux(self, used_variables, recurse_object_terms=True):
        typed_vars = []
        conjunction_parts = []
        new_args = []
        for term in self.args:
            typed,parts,new_term = term.compile_objectfunctions_aux(used_variables,
                                                                    recurse_object_terms)
            typed_vars += typed
            conjunction_parts += parts
            new_args.append(new_term)
        return (typed_vars,conjunction_parts,self.__class__(self.symbol,new_args))
    def  instantiate(self, var_mapping, fluent_functions, 
                        init_function_vals, task, new_axioms=[]):
        args = [var_mapping.get(conditions.Variable(arg.name),arg) for arg in self.args]
        pne = PrimitiveNumericExpression(self.symbol, args)
        # TODO check whether this PNE is fluent. Otherwise substitute it by the
        # corresponding constant
        if fluent_functions!=None:
            if pne not in fluent_functions and not pne.symbol.startswith("derived!"):
                if pne not in init_function_vals:
                    raise ValueError("Cannot instantiate non-fluent PNE: no initial value given %s" % pne)
                constant =  init_function_vals[pne]
                new_axiom_predicate = task.function_administrator.get_derived_function(constant)
                new_axiom = task.function_administrator.functions[(constant.value,)]
                new_axiom = new_axiom.instantiate(var_mapping, fluent_functions,init_function_vals,
                            task, new_axioms)
                new_axioms.add(new_axiom)
                return new_axiom_predicate
        return pne
    def remove_duration_variable(self, action, time, duration, pnes):
        return self

class FunctionAssignment(object):
    def __init__(self, fluent, expression):
        self.fluent = fluent
        self.expression = expression
        self.hash = hash((self.__class__.__name__, self.fluent, self.expression))
    def __str__(self):
        return "%s %s %s" % (self.__class__.__name__, self.fluent, self.expression) 
    def __eq__(self, other):
        return (self.__class__ is other.__class__ and
                self.hash == other.hash and
                self.fluent == other.fluent and
                self.expression == other.expression)
    def dump(self, indent="  "):
        print "%s%s" % (indent, self._dump())
        self.fluent.dump(indent + "  ")
        self.expression.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def rename_variables(self, renamings):
        return self.__class__(self.fluent.rename_variables(renamings),
                              self.expression.rename_variables(renamings))
    def free_variables(self):
        return self.fluent.free_variables() | self.expression.free_variables()
    def  instantiate(self, var_mapping, init_facts, fluent_facts,
                        init_function_vals, fluent_functions, task, new_axioms, result):
        if not isinstance(self.expression,PrimitiveNumericExpression):
            raise ValueError("Cannot instantiate assignment: not normalized")
        fluent = self.fluent.instantiate(var_mapping, fluent_functions, 
                                         init_function_vals, task, new_axioms)
        expression = self.expression.instantiate(var_mapping, fluent_functions, 
                                         init_function_vals, task, new_axioms)
        result.append(self.__class__(fluent,expression))

class Assign(FunctionAssignment):
    symbol = "="
    def __str__(self):
        return "%s := %s" % (self.fluent, self.expression) 

class ScaleUp(FunctionAssignment):
    symbol = "*"
    pass

class ScaleDown(FunctionAssignment):
    symbol = "/"
    pass

class Increase(FunctionAssignment):
    symbol = "+"
    pass

class Decrease(FunctionAssignment):
    symbol = "-"
    pass

class DurationVariable(FunctionalExpression):
    parts = ()
    def __init__(self):
        self.hash = hash(self.__class__)
    def __str__(self):
        return "?duration"
    def _dump(self):
        return str(self)
    def rename_variables(self, renamings={}):
        return self
    def change_parts(self, parts):
        return self
    def compile_objectfunctions_aux(self, used_variables, recurse_object_terms=True):
        return ([],[],self)
    def remove_duration_variable(self, action, time, duration, pnes):
        if time == 0:
            return duration
        else:
            name = "duration_" + action.name
            params = [conditions.Variable(param.name) for param in action.parameters]
            duration_function = PrimitiveNumericExpression(name, params)
            pnes.append(duration_function)
            return duration_function

