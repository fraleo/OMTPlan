# -*- coding: latin-1 -*-

import invariant_finder
import pddl

def expand_group(group, task, reachable_facts):
    result = []
    for fact in group:
        try:
            pos = list(fact.args).index("?X")
        except ValueError:
            result.append(fact)
        else:
            # NOTE: This could be optimized by only trying objects of the correct
            #       type, or by using a unifier which directly generates the
            #       applicable objects. It is not worth optimizing this at this stage,
            #       though.
            for obj in task.objects + [pddl.ObjectTerm("undefined")]:
                newargs = list(fact.args)
                newargs[pos] = pddl.ObjectTerm(obj.name)
                atom = pddl.Atom(fact.predicate, newargs)
                if atom in reachable_facts:
                    result.append(atom)
    return result

def instantiate_groups(groups, task, reachable_facts):
    return [expand_group(group, task, reachable_facts) for group in groups]

class GroupCoverQueue:
    def __init__(self, groups, partial_encoding, unused_groups=[]):
        self.partial_encoding = partial_encoding
        if groups:
            self.max_size = max([len(group) for group in groups])
            self.groups_by_size = [[] for i in range(self.max_size + 1)]
            self.groups_by_fact = {}
            for group in groups:
                group = set(group) # Copy group, as it will be modified.
                self.groups_by_size[len(group)].append(group)
                for fact in group:
                    self.groups_by_fact.setdefault(fact, []).append(group)
            for group in unused_groups:
                for fact in group:
                    self.groups_by_fact.setdefault(fact, []).append(group)
            self._update_top()
        else:
            self.max_size = 0
    def __nonzero__(self):
        return self.max_size > 1
    def pop(self):
        result = list(self.top) # Copy; this group will shrink further.
        if self.partial_encoding:
            for fact in result:
                for group in self.groups_by_fact[fact]:
                    group.remove(fact)
        self._update_top()
        return result
    def _update_top(self):
        while self.max_size > 1:
            max_list = self.groups_by_size[self.max_size]
            while max_list:
                candidate = max_list.pop()
                if len(candidate) == self.max_size:
                    self.top = candidate
                    return
                self.groups_by_size[len(candidate)].append(candidate)
            self.max_size -= 1

def choose_groups(groups, reachable_facts, partial_encoding=True):
    queue = GroupCoverQueue(groups, partial_encoding=partial_encoding)
    uncovered_facts = reachable_facts.copy()
    result = []
    while queue:
        group = queue.pop()
        uncovered_facts.difference_update(group)
        result.append(group)
    print len(uncovered_facts), "uncovered facts"
    result += [[fact] for fact in uncovered_facts]
    return result

def choose_groups_with_object_fluents_first(synthesis_groups, object_fluent_groups, 
    reachable_facts, partial_encoding=True):
    uncovered_facts = reachable_facts.copy()
    result = []
   
    # use grous from object fluents first
    shrink_groups = [set(group) for group in synthesis_groups]
    queue = GroupCoverQueue(object_fluent_groups, partial_encoding=partial_encoding,
                            unused_groups=shrink_groups)
    while queue:
        group = queue.pop()
        uncovered_facts.difference_update(group)
        result.append(group)
    print len(uncovered_facts), \
          "uncovered facts (before using the results from the invariant synthesis)"
    
    # try to cover uncovered facts by using the groups from the 
    # invariant synthesis
    queue = GroupCoverQueue(shrink_groups, partial_encoding=partial_encoding)
    while queue:
        group = queue.pop()
        uncovered_facts.difference_update(group)
        result.append(group)

    print len(uncovered_facts), "uncovered facts"
    result += [[fact] for fact in uncovered_facts]
    return result

def build_translation_key(groups):
    group_keys = []
    for group in groups:
        group_key = [str(fact) for fact in group]
        group_key.append("<none of those>")
        group_keys.append(group_key)
    return group_keys

def collect_all_mutex_groups(groups, atoms):
    # NOTE: This should be functionally identical to choose_groups
    # when partial_encoding is set to False. Maybe a future
    # refactoring could take that into account.
    all_groups = []      
    uncovered_facts = atoms.copy()
    for group in groups:
        uncovered_facts.difference_update(group)
        all_groups.append(group)
    all_groups += [[fact] for fact in uncovered_facts]
    return all_groups

def create_groups_from_object_fluents(atoms): 
    # Build groups that correspond to original object fluents:
    # Find atoms marked with '!val' and build a corresponding
    # group by finding all atoms that differ only in the last
    # argument
    groupdict = {}
    for a in atoms:
        if a.predicate.find("!val") != -1:
            groupdict.setdefault(a.predicate+"_".join(map(str, a.args[:-1])), []).append(a)

    # Construct the groups
    groups = []
    for g in groupdict:
        tgroup = []
        for a in groupdict[g]:
            tgroup.append(a);
        groups.append(tgroup)
    return groups

def compute_groups(task, atoms, reachable_action_params,
    return_mutex_groups=True, partial_encoding=True, safe=True):
    ## NOTE: exactly one of the following options should be true
    # TODO: there should be a configure section for this kind of stuff
    
    # don't use the information from the object fluents at all
    no_objectfluents = False
    # use only information from objectfluents (all other variables will be
    # proposotional
    only_objectfluents = False
    # use both the information from the objectfluents and the information from
    # the invariant syntheses and choose the groups by size
    choose_groups_by_size = False
    # use first the information from the objectfluents. If there are
    # propositional variables left use the information from the invariant
    # syntheses to group them
    use_objectfluents_first = True

    objectfluent_groups = []
    groups = []
    mutex_groups = []

    if not no_objectfluents:
        objectfluent_groups = create_groups_from_object_fluents(atoms)
   
    if not only_objectfluents:
        print "Finding invariants..."
        groups = invariant_finder.get_groups(task, safe, reachable_action_params)
        groups = sorted(groups, cmp=lambda x,y: cmp(str([str(a) for a in x]), 
                                                    str([str(a) for a in y])))
        print "Instantiating groups..."
        groups = instantiate_groups(groups, task, atoms)
    
        if return_mutex_groups:
            mutex_groups = collect_all_mutex_groups(groups, atoms) + \
                           objectfluent_groups

    print "Choosing groups..."
    if use_objectfluents_first:
        groups = choose_groups_with_object_fluents_first(groups, objectfluent_groups,
                 atoms, partial_encoding=partial_encoding)
    else:
        if only_objectfluents:
            groups = objectfluent_groups
        elif choose_groups_by_size:
            groups = objectfluent_groups + groups # slightly prefer objectfluent groups
        groups = choose_groups(groups, atoms, partial_encoding=partial_encoding)

    print "Building translation key..."
    translation_key = build_translation_key(groups)
    return groups, mutex_groups, translation_key
