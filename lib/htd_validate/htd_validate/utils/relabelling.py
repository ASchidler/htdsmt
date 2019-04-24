#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017

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
from __future__ import print_function
import collections


def relabel_sequence(seq, substitution):
    return map(lambda v: substitution[v], seq)


def consecutive_substitution(seq):
    return {v: pos for pos, v in zip(xrange(1, len(seq) + 1), seq)}


def revert_substitution(substitution):
    return {v: k for k, v in substitution.iteritems()}


# TODO: probably replace (...) by tuple([...]) in inner tuple comprehension
def relabel_dict(thedict, substitution=None, substitution_keys=None, typ=tuple):
    assert (substitution is not None or substitution_keys is not None)

    def lab(substi, v): return substi[v] if substi is not None else v  # PEP says no lambda here :/

    def lab_val(substi, e): return typ(lab(substi, v) for v in e) if isinstance(e, collections.Iterable) else e

    return {lab(substitution_keys, k): lab_val(substitution, e) for (k, e) in thedict.iteritems()}
