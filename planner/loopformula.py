##
# @file

############################################################################
##    This file is part of OMTPlan.
##
##    OMTPlan is free software: you can redistribute it and/or modify
##    it under the terms of the GNU General Public License as published by
##    the Free Software Foundation, either version 3 of the License, or
##    (at your option) any later version.
##
##    OMTPlan is distributed in the hope that it will be useful,
##    but WITHOUT ANY WARRANTY; without even the implied warranty of
##    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##    GNU General Public License for more details.
##
##    You should have received a copy of the GNU General Public License
##    along with OMTPlan.  If not, see <https://www.gnu.org/licenses/>.
############################################################################

import networkx as nx
import utils
import translate.pddl as pddl
from collections import defaultdict
from z3 import *
import itertools



def buildDTables(encoder):
    """!
    Extracts information needed to build dependency graph.

    @param encoder
    @return edges: edges of the dependency graph.
    @return table: datastructure containing info to build loop formula.
    """


    # Edges of dependency graph
    edges = []

    # Also builds lookup table
    # to store pre/eff for each action
    # needed to build loop formula

    table = defaultdict(dict)

    step = encoder.horizon+1

    for action in encoder.actions:
        # preconditions of action
        tpre = []

        # relaxed preconditions of action
        tpre_rel = []

        # effects of action
        teff = []

        ## Store preconditions (concrete and relaxed)
        for pre in action.condition:
            # propositional precondition
            if utils.isBoolFluent(pre):
                var_name = utils.varNameFromBFluent(pre)
                tpre.append(encoder.touched_variables[var_name])
                if pre.negated:
                    tmp = [Not(encoder.boolean_variables[step-1][var_name]),encoder.touched_variables[var_name]]
                else:
                    tmp = [encoder.boolean_variables[step-1][var_name],encoder.touched_variables[var_name]]

                tpre_rel.append(tuple(tmp))

            # numeric precondition
            elif isinstance(pre, pddl.conditions.FunctionComparison):
                expr = utils.inorderTraversalFC(encoder,pre,encoder.numeric_variables[step-1])

                tmp = [expr]

                for var_name in utils.extractVariablesFC(encoder,pre):
                    tpre.append(encoder.touched_variables[var_name])
                    tmp.append(encoder.touched_variables[var_name])

                tpre_rel.append(tuple(tmp))
            else:
                raise Exception('Precondition \'{}\' of type \'{}\' not supported'.format(pre,type(pre)))


        # Store add effects
        for add in action.add_effects:
            # check if effect is conditional
            if len(add[0])==0:
                var_name = utils.varNameFromBFluent(add[1])
                teff.append(encoder.touched_variables[var_name])
            else:
                raise Exception('Conditional effects not supported')


        # Store delete effects
        for de in action.del_effects:
            # check if effect is conditional
            if len(de[0]) == 0:
                var_name = utils.varNameFromBFluent(de[1])
                teff.append(encoder.touched_variables[var_name])
            else:
                raise Exception('Conditional effects not supported')

        # Store numeric effects

        for ne in action.assign_effects:
            #  check if effect is conditional
            if len(ne[0]) == 0:

                if isinstance(ne[1], pddl.f_expression.FunctionAssignment):

                    ## Numeric effects have fluents on the left and either a const, a fluent
                    ## or a complex numeric expression on the right

                    ## Handle left side
                    # retrieve variable name
                    var_name = utils.varNameFromNFluent(ne[1].fluent)
                    if not var_name in encoder.var_objective:
                        teff.append(encoder.touched_variables[var_name])

                else:

                    raise Exception('Numeric effect {} not supported yet'.format(ne[1]))
            else:
                raise Exception('Conditional effects not supported')


        ## Pupulate edges
        for p in tpre:
            for e in teff:
                edges.append((e,p))

        ## Fill lookup table

        table[action.name]['pre'] = tpre
        table[action.name]['pre_rel'] = tpre_rel
        table[action.name]['eff'] = teff

    ## Remove duplicate edges
    edges = set(edges)

    return edges, table


def computeSCC(edges):
    """!
    Computes Strongly Connected Components of graph.

    @param edges: edges of graph
    @return scc_purged: list of scc
    """

    g = nx.DiGraph()

    g.add_edges_from(edges)

    scc_original = nx.strongly_connected_components(g)

    self_loops = set([n for n in g.nodes_with_selfloops()])

    scc_purged = []

    for scc in scc_original:

        if len(scc) == 1:
            if len(scc & self_loops) > 0:
                scc_purged.append(scc)
        else:
            scc_purged.append(scc)

    return scc_purged


def encodeLoopFormulas(encoder):
    """!
    Builds loop formulas (see paper for description).

    @param encoder
    @return lf: list of loop formulas.
    """

    lf = []

    ## reverse map touched vars
    inv_touched_variables = {v: k for k, v in encoder.touched_variables.iteritems()}

    ## compute data to build loop formulas
    edges, table = buildDTables(encoder)

    # Loop formula for loop L: V L => V R(L)

    ## Compute SCC (i.e., loops)
    scc = computeSCC(edges)

    for loop in scc:

        L = []
        R = []

        # for each var in loop we check what actions can be added
        for variable in list(loop):

            # first build set L containing loop atoms
            z3_var = inv_touched_variables.get(variable,None)
            if z3_var is not None:
                L.append(encoder.touched_variables[z3_var])
            else:
                raise Exception("Could not find key to build loop formula")

        # for each action check if conditions to build R are met
        for action in table.keys():

            # variables appears in effect of action at step n

            if len(set(table[action]['eff']) & loop) > 0:

                # now check if variables appears in pre of action at step n+1

                # if list of precondition has length one: we just a simple condition
                # e.g. x v tx -> tuple(x,tx)
                # no need to check dnf
                # otherwise check all disjunct of dnf

                if len(table[action]['pre_rel']) == 1:

                    for cond in table[action]['pre_rel'][0]:
                        if cond in loop:
                            pass
                        else:
                            R.append(cond)

                else:
                    # if precondition has several terms, e.g. tx & (ty v tz),
                    # need to check for all possible combinations, i.e., tx & ty v tx & tz

                    dnf = list(itertools.product(*table[action]['pre_rel']))

                    for combo in dnf:
                        if len(set(combo) & loop) > 0:
                            pass
                        else:
                            R.append(And(combo))

        lf.append(Implies(Or(L), Or(set(R))))


    return lf
