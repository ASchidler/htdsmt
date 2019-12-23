#! /usr/bin/python3
from __future__ import absolute_import

import argparse
import sys
import logging
import frasmt_solver as solver
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition
import time

# End of imports

logging.disable(logging.FATAL)

parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')

parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')

parser.add_argument('-s', dest='sb', action='store_false',
                   default=True,
                   help='Deactivate Symmetry Breaking')

parser.add_argument('-mode', dest='mode', type=int, default=3, choices=range(0, 5),
                    help='The mode:\n '
                         '0: Only compute a GHTD\n'
                         '1: Compute a GHTD and try to repair the bags for a HTD (bag repair).\n'
                         '2: Compute a GHTD and initialize HTD calculation with a partial result from the GHTD (SMT-repair).\n'
                         '3 (default): Compute the HTD from scratch\n'
                         '4: Portfolio mode, try 1->2->3 and stop on first valid decomposition')

parser.add_argument('-l', dest='force_lex', action='store_true', default=False,
                    help='Force lexicographic ordering withing equivalence groups (mode 2 only)')

parser.add_argument('-a', dest='use_arcs', action='store_true', default=False,
                    help='During SMT-Repair initialize HTD calculation with arcs.')

parser.add_argument('-t', dest='use_tree', action='store_false', default=True,
                    help='During SMT-Repair initialize HTD calculation with tree structure.')

parser.add_argument('-o', dest='use_ordering', action='store_true', default=False,
                    help='During SMT-Repair initialize HTD calculation with ordering.')

parser.add_argument('-b', dest='use_bags', action='store_true', default=False,
                    help='During SMT-Repair initialize HTD calculation with bags.')
parser.add_argument('-d', dest='tmp_dir', default='/tmp', help='Path for temporary files, defaults to /tmp')
parser.add_argument('-v', dest='verbose', action='store_false', default=True, help='Suppress output of decomposition')
parser.add_argument('-w', dest='weighted', action='store_true', default=False, help='Input hypergraph is weighted, optimize for these weights')

args = parser.parse_args()
tmp_dir = args.tmp_dir.strip()

# Use cliques only for GHTD. For HTD they even slow the heuristic methods down
clique_mode = 2 if args.mode == 0 else 0
# Use heuristic repair only for mode 1. In all other modes, the output is already a valid HTD
repair = args.mode == 1 or args.mode == 4

td = None
res = None
lb = None
before_tm = time.time()
fl = 'solve_runner'

# Compute solution for GHTD
if args.mode != 3:
    res = solver.solve(tmp_dir, fl, args.graph, htd=False, force_lex=False,
                       sb=args.sb if args.mode <= 1 else False, heuristic_repair=repair, clique_mode=clique_mode,
                       weighted=args.weighted)
    td = res.decomposition if res is not None else None
    if td is not None and GeneralizedHypertreeDecomposition.validate(td, td.hypergraph):
        lb = res.size

# Use stratified encoding
if args.mode == 2 and res is not None and not td.validate(td.hypergraph):
    td = res.decomposition
    arcs = res.arcs if args.use_arcs else None
    ordering = res.ordering if args.use_ordering else None
    result = res.size
    edges = [(i, j) for i, j in td.tree.edges] if args.use_tree else None
    bags = td.bags if args.use_bags else None

    # Compute stratified solution
    res = solver.solve(tmp_dir, fl, args.graph, htd=True, force_lex=False, edges=edges, fix_val=result,
                       bags=bags, order=ordering, arcs=arcs, heuristic_repair=False, weighted=args.weighted)
    td = res.decomposition if res is not None else None

# Use HTD encoding
if args.mode >= 3 and (td is None or not td.validate(td.hypergraph)):
    res = solver.solve(tmp_dir, fl, args.graph, htd=True, force_lex=args.force_lex, sb=args.sb,
                       heuristic_repair=False, lb=lb, weighted=args.weighted)
    td = res.decomposition

# Display result if available
if res is None:
    print("No model. For heuristic methods this can signal a failure. In case of a timeout used, this can mean "
          "the timeout has been reached. See output model and error file for potential error messages.")

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

if args.mode > 0 and not valid:
    exit(1)

if args.verbose:
    mode = "ghtd" if args.mode == 0 else "htd"
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
