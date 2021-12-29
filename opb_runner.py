#! /usr/bin/python3
from __future__ import absolute_import

import argparse
import sys
import logging
import opb_encoding as enc
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition
import time
import bounds.upper_bounds as bnd
from lib.htd_validate.htd_validate.utils import Hypergraph
import os

# End of imports

logging.disable(logging.FATAL)

parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')

parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')

parser.add_argument('-g', dest='ghtd', action='store_true', default=False,
                    help='Compute a generalized hypertree decomposition, instead of a hypertree decomposition')

parser.add_argument('-v', dest='verbose', action='store_false', default=True, help='Suppress output of decomposition')
parser.add_argument('-b', dest="sb", default=False, action='store_true', help="Activate symmetry breaking")
parser.add_argument('-t', dest="tmpdir", default="/tmp", type=str, help="The temporary directory to use")

args = parser.parse_args()

td = None
res = None
before_tm = time.time()
fl = 'solve_runner'

input_file = args.graph
hypergraph_in = Hypergraph.from_file(input_file, fischl_format=False)
hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True)

if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
    hypergraph_in = hypergraph2

current_bound = bnd.greedy(hypergraph_in, False, bb=False)

encoder = enc.HtdSatEncoding(hypergraph_in)
res = encoder.solve(current_bound, not args.ghtd, sb=args.sb, tmpdir=args.tmpdir)

valid = res.decomposition.validate(res.decomposition.hypergraph)
valid_ghtd = GeneralizedHypertreeDecomposition.validate(res.decomposition, res.decomposition.hypergraph)
valid_sc = res.decomposition.inverse_edge_function_holds()

sys.stdout.write("Result: {}\tValid:  {}\tSP: {}\tGHTD: {}\tin {}\n".format(
    res.size,
    valid,
    valid_sc,
    valid_ghtd,
    time.time() - before_tm
))

