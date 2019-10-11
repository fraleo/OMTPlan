import conditions
import tasks
import f_expression
import pddl_types

def cartesian_product(*sequences):
  # TODO: Also exists in tools.py outside the pddl package (defined slightly
  #       differently). Not good. Need proper import paths.
  if not sequences:
    yield ()
  else:
    for tup in cartesian_product(*sequences[1:]):
      for item in sequences[0]:
        yield (item,) + tup

def parse_effects(alist, result):
    tmp_effect = parse_effect(alist)
    normalized = tmp_effect.normalize()
    if normalized.__class__.__name__ == "TmpEffect":
        for effect in normalized.effects:
            add_effect(effect,result)
    else:
        add_effect(normalized,result)

def parse_durative_effects(alist, result):
    tmp_effect = parse_effect(alist,True)
    normalized = tmp_effect.normalize()
    if normalized.__class__.__name__ == "TmpEffect":
        for effect in normalized.effects:
            add_effect(effect,result,True)
    else:
        add_effect(normalized,result,True)

# tmp_effect must be a normalized tmp_effect with only one effect
# or a primitive effect
def add_effect(tmp_effect, results, durative = False):
    time = None
    if durative:
        time = tmp_effect.time
    parameters = []
    if isinstance(tmp_effect, UniversalEffect):
        parameters = tmp_effect.parameters
        tmp_effect = tmp_effect.effects[0]
    if durative:
        condition = [conditions.Truth(),conditions.Truth(),conditions.Truth()]
    else: 
        condition = conditions.Truth()
    if isinstance(tmp_effect, ConditionalEffect):
        condition = tmp_effect.condition
        tmp_effect = tmp_effect.effects[0]
    if isinstance(tmp_effect, ConjunctiveEffect):
        assert len(tmp_effect.effects) == 1
        tmp_effect = tmp_effect.effects[0]
    assert not isinstance(tmp_effect,TmpEffect)
    if time=="start":
        results[0].append(Effect(parameters,condition,tmp_effect))
    elif time=="end":
        results[1].append(Effect(parameters,condition,tmp_effect))
    else:
        assert not durative
        results.append(Effect(parameters,condition,tmp_effect))

def parse_effect(alist,durative=False):
    tag = alist[0]
    if tag == "and":
        return TmpEffect([parse_effect(eff,durative) for eff in alist[1:]])
    elif tag == "forall":
        assert len(alist)==3
        return UniversalEffect(pddl_types.parse_typed_list(alist[1]),
                               parse_effect(alist[2],durative))
    elif tag == "when":
        assert len(alist)==3
        if durative:
            condition = conditions.parse_durative_condition(alist[1])
            effect = parse_timed_effect(alist[2])
        else:
            condition = conditions.parse_condition(alist[1])
            effect = parse_cond_effect(alist[2])
        return ConditionalEffect(condition,effect)
    elif tag == "at" and durative:
        return parse_timed_effect(alist)
    elif tag == "change":
        assert durative
        new_alist = ["and", ["at", "start", ["assign", alist[1], "undefined"]],
                           ["at", "end", ["assign", alist[1], alist[2]]]]
        return parse_effect(new_alist,durative)
    else:
        return parse_cond_effect(alist)

def parse_timed_effect(alist):
    assert len(alist)==3
    assert alist[0] == "at"
    time = alist[1]
    assert time in ("start","end")
    conjunctiveEffect = parse_cond_effect(alist[2],True)
    conjunctiveEffect.time = time
    return conjunctiveEffect

def parse_cond_effect(alist, durative=False):
    tag = alist[0]
    if tag == "and":
        return ConjunctiveEffect([parse_cond_effect(eff,durative) for eff in alist[1:]])
    elif tag in ("scale-up", "scale-down", "increase", "decrease"):
        return ConjunctiveEffect([f_expression.parse_assignment(alist,durative)])
    elif tag == "assign":
        symbol = alist[1]
        if isinstance(symbol,list):
            symbol = symbol[0]
        if tasks.Task.FUNCTION_SYMBOLS.get(symbol,"object")=="number":
            return ConjunctiveEffect([f_expression.parse_assignment(alist,durative)])
        else:
            return ConjunctiveEffect([ObjectFunctionAssignment(conditions.parse_term(alist[1]),conditions.parse_term(alist[2]))])
    else:
        return ConjunctiveEffect([conditions.parse_condition(alist)])
    
class Effect(object):
  def __init__(self, parameters, condition, peffect):
    self.parameters = parameters
    self.condition = condition
    self.peffect = peffect # literal or function assignment
  def __eq__(self, other):
    return (self.__class__ is other.__class__ and
            self.parameters == other.parameters and
            self.condition == other.condition and
            self.peffect == other.peffect)
  def dump(self):
    indent = "  "
    if self.parameters:
      print "%sforall %s" % (indent, ", ".join(map(str, self.parameters)))
      indent += "  "
    if ((isinstance(self.condition,list) and 
        self.condition != [conditions.Truth(),conditions.Truth(),conditions.Truth()])
       or (not isinstance(self.condition,list) and self.condition != conditions.Truth())):
      print "%sif" % indent
      if isinstance(self.condition,list):
        conditions.dump_temporal_condition(self.condition,indent + "  ")
      else:
        self.condition.dump(indent + "  ")
      print "%sthen" % indent
      indent += "  "
    self.peffect.dump(indent)
  def copy(self):
    return Effect(self.parameters, self.condition, self.peffect)
  def uniquify_variables(self, type_map):
    renamings = {}
    self.parameters = [par.uniquify_name(type_map, renamings)
                       for par in self.parameters]
    if isinstance(self.condition,list):
        self.condition = [cond.uniquify_variables(type_map, renamings) for 
                            cond in self.condition]
    else:
        self.condition = self.condition.uniquify_variables(type_map, renamings)
    self.peffect = self.peffect.rename_variables(renamings)
  def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                  fluent_functions, task, new_axiom, objects_by_type, result):
    if self.parameters:
      var_mapping = var_mapping.copy() # Will modify this.
      object_lists = [objects_by_type.get(par.type, [])
                      for par in self.parameters]
      for object_tuple in cartesian_product(*object_lists):
        for (par, obj) in zip(self.parameters, object_tuple):
          var_mapping[conditions.Variable(par.name)] = conditions.ObjectTerm(obj)
        self._instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                          fluent_functions, task, new_axiom, result)
    else:
      self._instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                          fluent_functions, task, new_axiom, result)
  def _instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                  fluent_functions, task, new_axiom, result):
    condition = []
    if isinstance(self.condition,list):
        condition = [[],[],[]]
        for time,cond in enumerate(self.condition):
            try:
                cond.instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                                 fluent_functions, task, new_axiom, condition[time])
            except conditions.Impossible:
                return
    else:
        try:
          self.condition.instantiate(var_mapping, init_facts, fluent_facts, init_function_vals,
                                     fluent_functions, task, new_axiom, condition)
        except conditions.Impossible:
          return
    effects = []
    self.peffect.instantiate(var_mapping, init_facts, fluent_facts, 
                             init_function_vals, fluent_functions, task,
                             new_axiom, effects)
    assert len(effects) <= 1
    if effects:
      result.append((condition, effects[0]))
#  def relaxed(self):
#    if self.peffect.negated:
#      return None
#    else:
#      return Effect(self.parameters, self.condition.relaxed(), self.peffect)
#  def simplified(self):
#    return Effect(self.parameters, self.condition.simplified(), self.peffect)

class TmpEffect(object):
    def __init__(self,effects,time=None):
        flattened_effects = []
        for effect in effects:
            if effect.__class__.__name__ == "TmpEffect":
                flattened_effects += effect.effects
            else:
                flattened_effects.append(effect)
        self.effects = flattened_effects
        self.time = time
    def dump(self, indent="  "):
        if self.time:
            print "%sat %s:" %(indent,self.time)
            indent += "  "
        print "%sand" % (indent)
        for eff in self.effects:
            eff.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def normalize(self):
        return TmpEffect([effect.normalize() for effect in self.effects])

class ConditionalEffect(TmpEffect):
    def __init__(self,condition,effect,time = None):
        if isinstance(effect,ConditionalEffect):
            assert len(condition) == len(effect.condition)
            if len(condition) == 1:
                self.condition = conditions.Conjunction([condition,effect.condition])
            else:
                new_condition = []
                for index,cond in enumerate(condition):
                    new_condition.append(conditions.Conjunction([cond,effect.condition[index]]))
                self.condition = new_condition
            self.effects = effect.effects
        else:
            self.condition = condition
            self.effects = [effect]
        self.time = time
        assert len(self.effects) == 1
    def dump(self, indent="  "):
        if self.time:
            print "%sat %s:" %(indent,self.time)
            indent += "  "
        print "%sif" % (indent)
        if isinstance(self.condition,list):
            conditions.dump_temporal_condition(self.condition,indent + "  ")
        else:
            self.condition.dump(indent + "  ")
        print "%sthen" % (indent)
        self.effects[0].dump(indent + "  ")
    def normalize(self):
        normalized = self.effects[0].normalize()
        if normalized.__class__.__name__ == "TmpEffect":
            effects = normalized.effects
        else:
            effects = [normalized]
        new_effects = []
        for effect in effects:
            assert effect.__class__.__name__ != "TmpEffect"
            if isinstance(effect,ConjunctiveEffect) or isinstance(effect,ConditionalEffect):
                new_effects.append(ConditionalEffect(self.condition,effect,effect.time))
            elif isinstance(effect,UniversalEffect):
                eff = ConditionalEffect(self.condition,effect.effects[0])
                new_effects.append(UniversalEffect(effect.parameters,eff,effect.time))
        if len(new_effects) == 1:
            return new_effects[0]
        else:
            return TmpEffect(new_effects)

class UniversalEffect(TmpEffect):
    def __init__(self,parameters,effect,time = None):
        if isinstance(effect,UniversalEffect):
            self.parameters = parameters + effect.parameters
            self.effects = effect.effects
        else:
            self.parameters = parameters
            self.effects = [effect]
        self.time = time
        assert len(self.effects) == 1
    def dump(self, indent="  "):
        if self.time:
            print "%sat %s:" %(indent,self.time)
            indent += "  "
        print "%sforall %s" % (indent, ", ".join(map(str, self.parameters)))
        self.effects[0].dump(indent + "  ")
    def normalize(self):
        effect = self.effects[0].normalize()
        if effect.__class__.__name__ == "TmpEffect":
            return TmpEffect([UniversalEffect(self.parameters,eff,eff.time) 
                                  for eff in effect.effects])
        return UniversalEffect(self.parameters,effect,effect.time) 

class ConjunctiveEffect(TmpEffect):
# effects are Literals and FunctionAssignments
    def __init__(self,effects,time=None):
        flattened_effects = []
        for effect in effects:
            if effect.__class__.__name__ == "ConjunctiveEffect":
                flattened_effects += effect.effects
            else:
                flattened_effects.append(effect)
        self.effects = flattened_effects
        self.time = time
    def normalize(self):
        effects = []
        for eff in self.effects:
            if isinstance(eff,ObjectFunctionAssignment):
                results = []
                eff.normalize(self.time,results)
                effects += results
            else:
                assert (isinstance(eff,f_expression.FunctionAssignment)
                        or isinstance(eff,conditions.Literal))
                used_variables = [eff.free_variables()]
                typed_vars = []
                conjunction_parts = []
                new_args = []
                if isinstance(eff,f_expression.FunctionAssignment):
                    args = [eff.fluent, eff.expression]
                else:
                    args = eff.args
                for arg in args:
                    typed,parts,new_arg = arg.compile_objectfunctions_aux(used_variables)
                    typed_vars += typed
                    conjunction_parts += parts
                    new_args.append(new_arg)
                if len(typed_vars) == 0:
                    effects.append(ConjunctiveEffect([eff],self.time))
                else:
                    if isinstance(eff,f_expression.FunctionAssignment):
                        new_eff = eff.__class__(*new_args)
                    else:
                        new_eff = eff.__class__(eff.predicate,new_args)
                    conjunction = conditions.Conjunction(conjunction_parts)
                    if self.time == "start":
                        condition = [conjunction,conditions.Truth(),conditions.Truth()]
                    elif self.time == "end":
                        condition = [conditions.Truth(),conditions.Truth(),conjunction]
                    else:
                        condition = conjunction
                    cond_eff = ConditionalEffect(condition,new_eff)
                    effects.append(UniversalEffect(typed_vars,cond_eff,self.time))
        return TmpEffect(effects)

class ObjectFunctionAssignment(object):
    def __init__(self,head,value):
        self.head = head    # term
        self.value = value  # term
    def dump(self, indent="  "):
        print "%sassign" % (indent)
        self.head.dump(indent + "  ")
        self.value.dump(indent + "  ")
    def rename_variables(self, renamings):
        return self.__class__(self.head.rename_variables(renamings),
                              self.value.rename_variables(renamings))
    def normalize(self,time,results): 
        used_variables = list(self.head.free_variables() | self.value.free_variables())
        typed1, conjunction_parts1, term1 = self.head.compile_objectfunctions_aux(used_variables)
        typed2, conjunction_parts2, term2 = self.value.compile_objectfunctions_aux(used_variables)
        assert isinstance(term1,conditions.Variable)
       
        add_params = set([typed for typed in typed1 if not typed.name==term1.name] + typed2)
        del_params = set(typed1 + typed2)
        
        add_conjunction_parts = conjunction_parts1[1:] + conjunction_parts2
        del_conjunction_parts = conjunction_parts1 + conjunction_parts2
        del_conjunction_parts = conjunction_parts1[1:] + conjunction_parts2
        # conjunctive_parts1[0] is left out because we do not need the condition 
        # that the atom in the del effect hast been true before

        # These conjunction parts are sufficient under the add-after-delete semantics.
        # Under the consistent effect semantics we need a further condition
        # that prevents deleting the added predicate.
        del_param = conjunction_parts1[0].args[-1]
        del_conjunction_parts.append(conditions.NegatedAtom("=",[del_param,term2]))

        del_effect = ConjunctiveEffect([conjunction_parts1[0].negate(),])
        atom_name = conjunction_parts1[0].predicate
        atom_parts = list(conjunction_parts1[0].args)
        atom_parts[-1] = term2
        add_effect = ConjunctiveEffect([conditions.Atom(atom_name,atom_parts),],time)

        add_conjunction = conditions.Conjunction(add_conjunction_parts)
        del_conjunction = conditions.Conjunction(del_conjunction_parts)
        if time == "start":
            del_condition = [del_conjunction,conditions.Truth(),conditions.Truth()]
            add_condition = [add_conjunction,conditions.Truth(),conditions.Truth()]
        elif time == "end":
            add_condition = [conditions.Truth(),conditions.Truth(),add_conjunction]
            del_condition = [conditions.Truth(),conditions.Truth(),del_conjunction]
        else:
            add_condition = add_conjunction
            del_condition = del_conjunction
        if len(add_conjunction_parts)>0:
            add_effect = ConditionalEffect(add_condition,add_effect,time)
        del_effect = ConditionalEffect(del_condition,del_effect)
        if len(add_params)>0:
            add_effect = UniversalEffect(add_params,add_effect,time)
        del_effect = UniversalEffect(del_params,del_effect,time)
        results.append(add_effect)
        results.append(del_effect)

        # value "undefined" must be treated specially because it has not the type
        # required in del_params
        if term2.name != "undefined":
            del_undef_params = set([typed for typed in del_params 
                                            if not typed.name==del_param.name])
            atom_parts = list(conjunction_parts1[0].args)
            atom_parts[-1] = conditions.ObjectTerm("undefined")
            del_undef_effect = ConjunctiveEffect([conditions.NegatedAtom(atom_name,atom_parts),],time)
            del_undef_conjunction_parts = del_conjunction_parts[:-1]
            del_undef_conjunction = conditions.Conjunction(del_undef_conjunction_parts)
            if time == "start":
                del_undef_condition = [del_undef_conjunction,conditions.Truth(),conditions.Truth()]
            elif time == "end":
                del_undef_condition = [conditions.Truth(),conditions.Truth(),del_undef_conjunction]
            else:
                del_undef_condition = del_undef_conjunction
            if len(del_undef_conjunction_parts)>0:
                del_undef_effect = ConditionalEffect(del_undef_condition,del_undef_effect,time)
            if len(del_undef_params)>0:
                del_undef_effect = UniversalEffect(del_undef_params,del_undef_effect,time)
            results.append(del_undef_effect)


