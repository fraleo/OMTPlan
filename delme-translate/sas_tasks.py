class SASTask:
  def __init__(self, variables, init, goal, operators, 
        temp_operators,axioms, num_axioms, comp_axioms):
    self.variables = variables
    self.init = init
    self.goal = goal
    self.operators = operators
    self.temp_operators = temp_operators
    self.axioms = axioms
    self.num_axioms = num_axioms
    self.comp_axioms = comp_axioms
  def output(self, stream):
    self.variables.output(stream)
    self.init.output(stream)
    self.goal.output(stream)
    if len(self.operators) > 0:
        assert len(self.temp_operators) == 0
        print >> stream, len(self.operators)
        for op in self.operators:
            op.output(stream)
    else:
        print >> stream, len(self.temp_operators)
        for op in self.temp_operators:
          op.output(stream)
    print >> stream, len(self.axioms)
    for axiom in self.axioms:
      axiom.output(stream)
    print >> stream, len(self.comp_axioms)
    for axiom in self.comp_axioms:
      axiom.output(stream)
    print >> stream, len(self.num_axioms)
    for axiom in self.num_axioms:
      axiom.output(stream)

class SASVariables:
  def __init__(self, ranges, axiom_layers):
    self.ranges = ranges
    self.axiom_layers = axiom_layers
  def dump(self):
    for var, (rang, axiom_layer) in enumerate(zip(self.ranges, self.axiom_layers)):
      if axiom_layer != -1:
        axiom_str = " [axiom layer %d]" % axiom_layer
      else:
        axiom_str = ""
      print "v%d in {%s}%s" % (var, range(rang), axiom_str)
  def output(self, stream):
    print >> stream, "begin_variables"
    print >> stream, len(self.ranges)
    for var, (rang, axiom_layer) in enumerate(zip(self.ranges, self.axiom_layers)):
      print >> stream, "var%d %d %d" % (var, rang, axiom_layer)
    print >> stream, "end_variables"

class SASInit:
  def __init__(self, values):
    self.values = values
  def dump(self):
    for var, val in enumerate(self.values):
      if val != -1:
        print "v%d: %d" % (var, val)
  def output(self, stream):
    print >> stream, "begin_state"
    for val in self.values:
      print >> stream, val
    print >> stream, "end_state"

class SASGoal:
  def __init__(self, pairs):
    self.pairs = sorted(pairs)
  def dump(self):
    for var, val in self.pairs:
      print "v%d: %d" % (var, val)
  def output(self, stream):
    print >> stream, "begin_goal"
    print >> stream, len(self.pairs)
    for var, val in self.pairs:
      print >> stream, var, val
    print >> stream, "end_goal"

class SASOperator:
  def __init__(self, name, prevail, pre_post, assign_effects):
    self.name = name
    self.prevail = sorted(prevail)
    self.pre_post = sorted(pre_post)
    self.assign_effects = assign_effects
  def dump(self):
    print self.name
    print "Prevail:"
    for var, val in self.prevail:
      print "  v%d: %d" % (var, val)
    print "Pre/Post:"
    for var, pre, post, cond in self.pre_post:
      if cond:
        cond_str = " [%s]" % ", ".join(["%d: %d" % tuple(c) for c in cond])
      else:
        cond_str = ""
      print "  v%d: %d -> %d%s" % (var, pre, post, cond_str)
  def output(self, stream):
    print >> stream, "begin_operator"
    print >> stream, self.name[1:-1]
    print >> stream, len(self.prevail)
    for var, val in self.prevail:
      print >> stream, var, val
    num = len(self.pre_post) + len(self.assign_effects)
    print >> stream, num
    for var, pre, post, cond in self.pre_post:
      print >> stream, len(cond),
      for cvar, cval in cond:
        print >> stream, cvar, cval,
      print >> stream, var, pre, post
    for assignment in self.assign_effects:
      assignment.output(stream)
    print >> stream, "end_operator"

class SASTemporalOperator:
  def __init__(self, name, duration, prevail, pre_post, assign_effects):
    self.name = name

    ## Currently we assume in the knowledge compilation
    ## and search that there is a single exact at start
    ## duration constraint. If someone wants to change 
    ## this it is only necessary to adapt the output
    ## method and to remove this assertion
    assert (len(duration[1]) == 0 and len(duration[0]) == 1
            and duration[0][0].op == "="), \
            "unsupported duration constraint"
    self.duration = duration
    self.prevail = prevail
    self.pre_post = pre_post
    self.assign_effects = assign_effects
  def output(self, stream):
    print >> stream, "begin_operator"
    print >> stream, self.name[1:-1]
    self.duration[0][0].output(stream)
    for time in range(3):
        print >> stream, len(self.prevail[time])
        for var, val in self.prevail[time]:
            print >> stream, var, val
    for time in range(2):
        num = len(self.pre_post[time]) + len(self.assign_effects[time])
        print >> stream, num
        for var, pre, post, cond in self.pre_post[time]:
            for cond_time in range(3):
                print >> stream, len(cond[cond_time]),
                for cvar, cval in cond[cond_time]:
                    print >> stream, cvar, cval,
            print >> stream, var, pre, post
        for assignment in self.assign_effects[time]:
            assignment.output(stream)
    print >> stream, "end_operator"

class SASDuration:
  def __init__(self, op, var):
    self.op = op
    self.var = var
  def output(self, stream):
    print >> stream, self.op, self.var 

class SASAssignmentEffect:
  def __init__(self, var, op, valvar, prevail, temporal=False):
    self.var = var
    self.op = op
    self.valvar = valvar
    self.prevail = prevail
    self.temporal = temporal
  def output(self, stream):
    if self.temporal:
        for time in range(3):
            print >> stream, len(self.prevail[time]),
            for var, val in self.prevail[time]:
                print >> stream, var, val,
    else:
        print >> stream, len(self.prevail),
        for var, val in self.prevail:
            print >> stream, var, val,
    print >> stream, self.var, self.op, self.valvar

class SASAxiom:
  def __init__(self, condition, effect):
    self.condition = condition
    self.effect = effect
    assert self.effect[1] in (0, 1)

    for _, val in condition:
      assert val >= 0, condition
  def dump(self):
    print "Condition:"
    for var, val in self.condition:
      print "  v%d: %d" % (var, val)
    print "Effect:"
    var, val = self.effect
    print "  v%d: %d" % (var, val)
  def output(self, stream):
    print >> stream, "begin_rule"
    print >> stream, len(self.condition)
    for var, val in self.condition:
      print >> stream, var, val
    var, val = self.effect
    print >> stream, var, 1 - val, val
    print >> stream, "end_rule"

class SASCompareAxiom:
  def __init__(self, comp, parts, effect):
    self.comp = comp
    self.parts = parts
    self.effect = effect
  def dump(self):
    values = (self.effect, self.comp, 
        " ".join([str(var) for var in self.parts]))
    print "v%d: %s %s" % values
  def output(self, stream):
    values = (self.effect, self.comp, 
        " ".join([str(var) for var in self.parts]))
    print >> stream, "%d %s %s" % values

class SASNumericAxiom:
  def __init__(self, op, parts, effect):
    self.op = op
    self.parts = parts
    self.effect = effect

  def dump(self):
    values = (self.effect, self.op, 
        " ".join([str(var) for var in self.parts]))
    print "v%d: %s %s" % values
  def output(self, stream):
    values = (self.effect, self.op, 
        " ".join([str(var) for var in self.parts]))
    print >> stream, "%d %s %s" % values

