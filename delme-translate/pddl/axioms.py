import conditions
import predicates
import f_expression

class Axiom(object):
  def __init__(self, name, parameters, condition):
    self.name = name
    self.parameters = parameters
    self.condition = condition
    self.uniquify_variables()
  def parse(alist):
    assert len(alist) == 3
    assert alist[0] == ":derived"
    predicate = predicates.Predicate.parse(alist[1])
    condition = conditions.parse_condition(alist[2])
    return Axiom(predicate.name, predicate.arguments, condition)
  parse = staticmethod(parse)
  def dump(self):
    print "Axiom %s(%s)" % (self.name, ", ".join(map(str, self.parameters)))
    self.condition.dump()
  def uniquify_variables(self):
    self.type_map = dict([(par.name, par.type) for par in self.parameters])
    self.condition = self.condition.uniquify_variables(self.type_map)
  def instantiate(self, var_mapping, init_facts, fluent_facts, 
                  fluent_functions, init_function_vals, task, new_constant_axioms):
    # The comments for Action.instantiate apply accordingly.
    arg_list = [var_mapping[conditions.Variable(par.name)].name for par in self.parameters]
    name = "(%s %s)" % (self.name, " ".join(arg_list))

    condition = []
    try:
      self.condition.instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                                 fluent_functions, task, new_constant_axioms, condition)
    except conditions.Impossible:
      return None

    effect_args = [var_mapping.get(conditions.Variable(arg.name), 
                                   conditions.Variable(arg.name)) for arg in self.parameters]
    effect = conditions.Atom(self.name, effect_args)
    return PropositionalAxiom(name, condition, effect)

class PropositionalAxiom:
  def __init__(self, name, condition, effect):
    self.name = name
    self.condition = condition
    self.effect = effect
  def clone(self):
    return PropositionalAxiom(self.name, list(self.condition), self.effect)
  def dump(self):
    if self.effect.negated:
      print "not",
    print self.name
    for fact in self.condition:
      print "PRE: %s" % fact
    print "EFF: %s" % self.effect

class NumericAxiom(object):
  def __init__(self, name, parameters, op, parts):
    self.name = name
    self.parameters = parameters
    self.op = op
    self.parts = parts # contains NumericAxioms, PrimitiveNumericExpressions or a NumericConstant
  def __str__(self):
    return "%s: %s(%s)" %(self.__class__.__name__, self.name, ", ".join(map(str, self.parameters)))
  def get_head(self):
    return f_expression.PrimitiveNumericExpression(self.name,self.parameters)
  def dump(self,indent):
    head = "(%s %s)" % (self.name, ", ".join(map(str, self.parameters)))
    op = ""
    if self.op:
        op = self.op + " "
    body = "%s" % " ".join(map(str, self.parts))
    print "%s%s -: %s%s" % (indent,head,op,body)
  def instantiate(self, var_mapping, fluent_functions, init_function_vals, task, new_constant_axioms):
    arg_list = [var_mapping[conditions.Variable(par.name)] for par in self.parameters]
    name = "(%s %s)" % (self.name, " ".join([arg.name for arg in arg_list]))
    parts = []
    for part in self.parts:
        if isinstance(part,f_expression.NumericConstant):
            parts.append(part)
        else:
            parts.append(part.instantiate(var_mapping, fluent_functions, 
                         init_function_vals, task, new_constant_axioms))
    effect = f_expression.PrimitiveNumericExpression(self.name, arg_list)
    return PropositionalNumericAxiom(name, self.op, parts, effect)

class PropositionalNumericAxiom(object):
  def __init__(self, name, op, parts, effect):
    self.name = name
    self.op = op
    self.parts = parts # contains PropositionalNumericAxioms, (instantiated) 
                       # PrimitiveNumericExpressions or a NumericConstant
    self.effect = effect
  def __str__(self):
    return self.name
  def __cmp__(self, other):
    return cmp((self.__class__, self.name), (other.__class__, other.name))
  def __hash__(self):
    return hash((self.__class__,self.name))
  def dump(self):
    print self.name
    print "OP: %s" % self.op
    for part in self.parts:
        print "PART: %s" % part
    print "EFF: %s" % self.effect

