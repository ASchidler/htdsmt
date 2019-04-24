#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2018

#

# *) is not allowed to contain parts of nuts ;P
#
# hypergraph.py is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.  hypergraph.py is distributed in
# the hope that it will be useful, but WITHOUT ANY WARRANTY; without
# even the implied warranty of MERCHANTABILITY or FITNESS FOR A
# PARTICULAR PURPOSE.  See the GNU General Public License for more
# details.  You should have received a copy of the GNU General Public
# License along with hypergraph.py.  If not, see
# <http://www.gnu.org/licenses/>.
# from __future__ import print_function
import networkx as nx

class Formula:

    def __init__(self, stream=None):
        self._clauses = 0
        self._vars = 0
        self._mapping = {}
        self._stream = stream

    @property
    def clauses(self):
        return self._clauses

    @property
    def variables(self):
        return self._vars

    @property
    def stream(self):
        return self._stream

    def writeHeader(self, safety=False):
        self._stream.seek(0)
        self._stream.write("p cnf {0} {1}{0}\n".format(self._vars, self._clauses, " " * 32 if safety else ""))

    def close(self):
        self._stream.close()

    @stream.setter
    def stream(self, stream):
        self._stream = stream

    def addClause(self, clause):
        self._stream.write("{0} 0\n".format(clause))
        self.__clauses += 1

    def map(self, var):
        if var in self._mapping:
            return self._mapping[var]
        else:
            self._mapping[var] = self._vars
            self._vars += 1
            return self._vars - 1

