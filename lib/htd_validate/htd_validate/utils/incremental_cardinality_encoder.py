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


class IncrementalCardinalityEncoder:
    def __init__(self, formula):
        self._formula = formula


