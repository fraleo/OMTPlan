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


from z3 import *

class Modifier():
    """
    Modifier class.
    """

    def do_encode(self):
        """
        Basic encoding.
        """
        raise NotImplementedError

class LinearModifier(Modifier):
    """
    Linear modifier, contains method to implement sequential execution semantics.

    """

    def do_encode(self, variables, bound):
        """!
        Encodes sequential execution semantics (i.e., one action per step).

        @param  variables: Z3 variables.
        @param bound: planning horizon.

        @return c: constraints enforcing sequential execution
        """
        c = []

        for step in range(bound):
            pbc = [(var,1) for var in variables[step].values()]
            c.append(PbLe(pbc,1))

        return c

class ParallelModifier(Modifier):
    """
    Parallel modifier, contains method to implement parallel execution semantics.
    """

    def do_encode(self, variables, mutexes, bound):
        """!
        Encodes parallel execution semantics (i.e., multiple, mutex, actions per step).

        @param  variables: Z3 variables.
        @param mutexes: action mutexes.
        @param bound: planning horizon.

        @return c: constraints enforcing parallel execution
        """
        c = []

        for step in range(bound):
            for pair in mutexes:
                c.append(Or(Not(variables[step][pair[0].name]),Not(variables[step][pair[1].name])))

        return c
