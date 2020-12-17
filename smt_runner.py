#! /usr/bin/python3
from __future__ import absolute_import

import argparse
import sys
import logging
import smt_solver as solver
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition
import time
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
parser.add_argument('-z', dest="z3", default=False, action='store_true', help="Use Z3 solver instead of optimathsat")
parser.add_argument('-q', dest="clique", default=0, type=int, action='store', help="Clique mode, 0 is disabled")

args = parser.parse_args()

td = None
res = None
before_tm = time.time()
fl = 'solve_runner'

# Compute solution for GHTD
if args.ghtd:
    res = solver.solve(args.graph, htd=False, clique_mode=args.clique, sb=args.sb)
    td = res.decomposition if res is not None else None
else:
    res = solver.solve(args.graph, htd=True, clique_mode=args.clique, sb=args.sb)
    td = res.decomposition if res is not None else None

# Display result if available
if res is None:
    print("No model found.")
    exit(1)

# Display the HTD
valid = td.validate(td.hypergraph)
valid_ghtd = GeneralizedHypertreeDecomposition.validate(td, td.hypergraph)
valid_sc = td.inverse_edge_function_holds()

sys.stdout.write("Result: {}\tValid:  {}\tSP: {}\tGHTD: {}\tin {}\n".format(
    res.size,
    valid,
    valid_sc,
    valid_ghtd,
    time.time() - before_tm
))

if (args.ghtd and not valid_ghtd) or not valid:
    exit(1)

if args.verbose:
    mode = "ghtd" if args.ghtd else "htd"
    print(f"s {mode} {len(td.bags)} {res.size} {len(td.hypergraph.nodes())} {len(td.hypergraph.edges())}")

    # Output bags
    for k, v in td.bags.items():
        print("b {} {}".format(k, " ".join((str(x) for x in v))))
    print("")

    # Output edges
    for u, v in td.tree.edges:
        print(f"{u} {v}")
    print("")

    # Output edge function
    for k, v in td.hyperedge_function.items():
        for k2, v2 in v.items():
            print(f"w {k} {k2} {v2}")
