# -*- coding: latin-1 -*-

import copy

import conditions
import effects
import f_expression
import pddl_types

class Action(object):
    def __init__(self, name, parameters, precondition, effects):
        self.name = name
        self.parameters = parameters
        self.condition = precondition
        self.effects = effects
        self.uniquify_variables()
    def parse(alist):
        iterator = iter(alist)
        assert iterator.next() == ":action"
        name = iterator.next()
        parameters_tag_opt = iterator.next()
        if parameters_tag_opt == ":parameters":
            parameters = pddl_types.parse_typed_list(iterator.next(),
                                                     only_variables=True)
            precondition_tag_opt = iterator.next()
        else:
            parameters = []
            precondition_tag_opt = parameters_tag_opt
        if precondition_tag_opt == ":precondition":
            precondition = conditions.parse_condition(iterator.next())
            effect_tag = iterator.next()
        else:
            precondition = conditions.Conjunction([])
            effect_tag = precondition_tag_opt
        assert effect_tag == ":effect"
        effect_list = iterator.next()
        eff = []
        effects.parse_effects(effect_list,eff)
        for rest in iterator:
            assert False, rest
        return Action(name, parameters, precondition, eff)
    parse = staticmethod(parse)
    def dump(self):
        print "%s(%s)" % (self.name, ", ".join(map(str, self.parameters)))
        print "Precondition:"
        self.condition.dump()
        print "Effects:"
        for eff in self.effects:
            eff.dump()
    def uniquify_variables(self):
        self.type_map = dict([(par.name, par.type) for par in self.parameters])
        self.condition = self.condition.uniquify_variables(self.type_map)
        for effect in self.effects:
            effect.uniquify_variables(self.type_map)
    def relaxed(self):
        new_effects = []
        for eff in self.effects:
            relaxed_eff = eff.relaxed()
            if relaxed_eff:
                new_effects.append(relaxed_eff)
        return Action(self.name, self.parameters,
                      self.condition.relaxed().simplified(),
                      new_effects)
    def untyped(self):
        # We do not actually remove the types from the parameter lists,
        # just additionally incorporate them into the conditions.
        # Maybe not very nice.
        result = copy.copy(self)
        parameter_atoms = [par.to_untyped_strips() for par in self.parameters]
        new_precondition = self.condition.untyped()
        result.condition = conditions.Conjunction(parameter_atoms + [new_precondition])
        result.effects = [eff.untyped() for eff in self.effects]
        return result

    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, objects_by_type):
        """Return a PropositionalAction which corresponds to the instantiation of
        this action with the arguments in var_mapping. Only fluent parts of the
        conditions (those in fluent_facts) are included. init_facts are evaluated
        whilte instantiating.
        Precondition and effect conditions must be normalized for this to work.
        Returns None if var_mapping does not correspond to a valid instantiation
        (because it has impossible preconditions or an empty effect list.)"""
        arg_list = [var_mapping[conditions.Variable(par.name)].name for par in self.parameters]
        name = "(%s %s)" % (self.name, " ".join(arg_list))

        precondition = []
        try:
            self.condition.instantiate(var_mapping, init_facts, fluent_facts, 
                                       init_function_vals, fluent_functions, task,
                                       new_axiom, precondition)
        except conditions.Impossible:
            return None
        effects = []
        for eff in self.effects:
            eff.instantiate(var_mapping, init_facts, fluent_facts, 
                            init_function_vals, fluent_functions, task, 
                            new_axiom, objects_by_type, effects)
        if effects:
            return PropositionalAction(name, precondition, effects)
        else:
            return None

class DurativeAction(object):
    def __init__(self, name, parameters, duration, conditions, effects):
        self.name = name
        self.parameters = parameters
        self.orig_parameter_length = len(parameters)
        self.duration = duration
        self.condition = conditions
        assert len(effects)==2
        self.effects = effects
        self.uniquify_variables()
    def parse(alist):
        iterator = iter(alist)
        assert iterator.next() == ":durative-action"
        name = iterator.next()
        parameters_tag_opt = iterator.next()
        if parameters_tag_opt == ":parameters":
            parameters = pddl_types.parse_typed_list(iterator.next(),
                                                     only_variables=True)
            duration_tag = iterator.next()
        else:
            parameters = []
            duration_tag = parameters_tag_opt
        assert duration_tag == ":duration"
        duration_list = iterator.next()
        if duration_list[0] == "and":
            duration_list = duration_list[1:]
        else:
            duration_list = [duration_list]
        duration_start = []
        duration_end = []
        for item in duration_list: # each item is a simple-duration-constraint
            duration = duration_start
            if item[0] == "at":
                if item[1] == "end":
                    duration = duration_end
                item = item[2]
            assert item[0] in ("<=",">=","=")
            assert len(item) == 3
            assert item[1] == "?duration"
            op = item[0]
            value = f_expression.parse_expression(item[2])
            duration += [(op,value)]
        condition_tag = iterator.next()
        if condition_tag == ":condition":
            condition = conditions.parse_durative_condition(iterator.next())
            effect_tag = iterator.next()
        else:
            condition = conditions.parse_durative_condition([])
            effect_tag = condition_tag
        assert effect_tag == ":effect"

        effect_list = iterator.next()
        effect = [[],[]]
        effects.parse_durative_effects(effect_list, effect)
        for rest in iterator:
            assert False, rest
        return DurativeAction(name, parameters, (duration_start,duration_end), condition, effect)
    parse = staticmethod(parse)
    def dump(self):
        if self.orig_parameter_length != len(self.parameters):
            print "%s(%s, (%s))" % (self.name, 
                              ", ".join(map(str, self.parameters[0:self.orig_parameter_length])), 
                              ", ".join(map(str, self.parameters[self.orig_parameter_length:])))
        else:
            print "%s(%s)" % (self.name, ", ".join(map(str, self.parameters)))
        if len(self.duration[0]) > 0:
            print "duration (values from start):"
            for (op, val) in self.duration[0]:
                print "  " + op
                val.dump("    ")
        if len(self.duration[1]) > 0:
            print "duration (values from end):"
            for (op, val) in self.duration[1]:
                print "  " + op
                val.dump("    ")
        print "start condition:"
        self.condition[0].dump()
        print "over all condition:"
        self.condition[1].dump()
        print "end condition:"
        self.condition[2].dump()
        print "start effects:"
        for eff in self.effects[0]:
            eff.dump()
        print "end effects:"
        for eff in self.effects[1]:
            eff.dump()
    def __str__(self):
        return "<Action %s>" % self.name
    def uniquify_variables(self):
        self.type_map = dict([(par.name, par.type) for par in self.parameters])
        for index, condition in enumerate(self.condition):
            self.condition[index] = condition.uniquify_variables(self.type_map)
        for effects in self.effects:
            for effect in effects:
                effect.uniquify_variables(self.type_map)
    def instantiate(self, var_mapping, init_facts, fluent_facts, init_function_vals,
                    fluent_functions, task, new_axiom, objects_by_type):
        """Return a PropositionalDurativeAction which corresponds to the instantiation of
        this action with the arguments in var_mapping. Only fluent parts of the
        conditions (those in fluent_facts) are included. init_facts are evaluated
        whilte instantiating.
        Precondition and effect conditions must be normalized for this to work.
        Returns None if var_mapping does not correspond to a valid instantiation
        (because it has impossible preconditions or an empty effect list.)"""

        arg_list = [var_mapping[conditions.Variable(par.name)].name for par in self.parameters]
        name = "(%s %s)" % (self.name, " ".join(arg_list[:self.orig_parameter_length]))

        try:
            inst_duration = [[(op,pne.instantiate(var_mapping, fluent_functions, 
                                              init_function_vals, task, new_axiom)) 
                                              for op,pne in self.duration[0]],
                            [(op,pne.instantiate(var_mapping, fluent_functions, 
                                              init_function_vals, task, new_axiom)) 
                                              for op,pne in self.duration[1]]]
        except ValueError, e:
            print "dropped action %s" % name
            print "Error: %s" % e
            return None
        
        inst_conditions = [[],[],[]]
        for time,condition in enumerate(self.condition):
            try:
                condition.instantiate(var_mapping, init_facts, fluent_facts, 
                                      init_function_vals, fluent_functions, task,
                                      new_axiom, inst_conditions[time])
            except conditions.Impossible:
                return None
        effects = [[],[]]
        for time,timed_effects in enumerate(self.effects):
            for eff in timed_effects:
                eff.instantiate(var_mapping, init_facts, fluent_facts, 
                                init_function_vals, fluent_functions, task, 
                                new_axiom, objects_by_type, effects[time])
        if effects:
            return PropositionalDurativeAction(name, inst_duration, inst_conditions, effects)
        else:
            return None
#    def relaxed(self):
#        new_effects = []
#        for eff in self.effects:
#            relaxed_eff = eff.relaxed()
#            if relaxed_eff:
#                new_effects.append(relaxed_eff)
#        return Action(self.name, self.parameters,
#                      self.condition.relaxed().simplified(),
#                      new_effects)
#    def untyped(self):
#        # We do not actually remove the types from the parameter lists,
#        # just additionally incorporate them into the conditions.
#        # Maybe not very nice.
#        result = copy.copy(self)
#        parameter_atoms = [par.to_untyped_strips() for par in self.parameters]
#        new_precondition = self.condition.untyped()
#        result.condition = conditions.Conjunction(parameter_atoms + [new_precondition])
#        result.effects = [eff.untyped() for eff in self.effects]
#        return result

class PropositionalAction:
    def __init__(self, name, precondition, effects):
        self.name = name
        self.condition = precondition
        self.add_effects = []
        self.del_effects = []
        self.assign_effects = []
        for (condition, effect) in effects:
            if isinstance(effect,f_expression.FunctionAssignment):
                self.assign_effects.append((condition, effect))
            elif effect.negated:
                self.del_effects.append((condition, effect.negate()))
            else:
                self.add_effects.append((condition, effect))
    def dump(self):
        print self.name
        for fact in self.condition:
            print "PRE: %s" % fact
        for cond, fact in self.add_effects:
            print "ADD: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.del_effects:
            print "DEL: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.assign_effects:
            print "ASS: %s -> %s" % (", ".join(map(str, cond)), fact)

class PropositionalDurativeAction:
    def __init__(self, name, duration, conditions, effects):
        self.name = name
        self.duration = duration
        self.conditions = conditions
        self.add_effects = [[],[]]
        self.del_effects = [[],[]]
        self.assign_effects = [[],[]]
        for time in range(2):
            for (condition, effect) in effects[time]:
                if isinstance(effect,f_expression.FunctionAssignment):
                    self.assign_effects[time].append((condition, effect))
                elif effect.negated:
                    self.del_effects[time].append((condition, effect.negate()))
                else:
                    self.add_effects[time].append((condition, effect))
    def dump(self):
        print self.name
        for duration in self.duration[0]:
            print "START DUR: %s %s" % (duration[0],duration[1])
        for duration in self.duration[1]:
            print "END DUR: %s %s" % (duration[0],duration[1])
        for fact in self.conditions[0]:
            print "START COND: %s" % fact
        for fact in self.conditions[1]:
            print "OVER ALL COND: %s" % fact
        for fact in self.conditions[2]:
            print "END COND: %s" % fact
        for cond, fact in self.add_effects[0]:
            print "ADD START: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.add_effects[1]:
            print "ADD END: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.del_effects[0]:
            print "DEL START: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.del_effects[1]:
            print "DEL END: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.assign_effects[0]:
            print "ASS START: %s -> %s" % (", ".join(map(str, cond)), fact)
        for cond, fact in self.assign_effects[1]:
            print "ASS END: %s -> %s" % (", ".join(map(str, cond)), fact)
