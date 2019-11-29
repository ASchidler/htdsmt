#! /usr/bin/python3
from __future__ import absolute_import

import argparse
import sys
import inspect
import frasmt_solver
import os
import subprocess
import logging

from lib.htd_validate.htd_validate.utils import Hypergraph
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition

# End of imports
logging.disable(logging.FATAL)


parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')

parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')

parser.add_argument('-s', dest='sb', action='store_false',
                   default=True,
                   help='Deactivate Symmetry Breaking')

parser.add_argument('-mode', dest='mode', type=int, default=3, choices=range(0, 4),
                    help='The mode:\n 1: Compute a GHTD and try to repair the bags for a HTD (bag repair).\n'
                         '2: Compute a GHTD and initialize HTD calculation with a partial result from the GHTD (SMT-repair).\n'
                         '3 (default): Compute the HTD from scratch')

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

args = parser.parse_args()
tmp_dir = args.tmp_dir.strip()

# Filenames
inp_file = tmp_dir + '/slv.encode'
model_file = tmp_dir + '/slv.model'
err_file = tmp_dir + '/slv.err'

hypergraph = Hypergraph.from_file(args.graph, fischl_format=False)
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
src_path = os.path.realpath(os.path.join(src_path, '..'))

arcs = None
ordering = None
bags = None
result = None
edges = None
run = True
td = None
res = None

while run:
    run = False

    inpf = open(inp_file, "w+")
    modelf = open(model_file, "w+")
    errorf = open(err_file, "w+")

    # Create encoding of the instance
    enc = frasmt_solver.FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None)

    htd = args.mode == 3 or result is not None

    if result is not None:
        enc.solve(htd=True, force_lex=False, edges=edges, fix_val=result, bags=bags, order=ordering, arcs=arcs)
    else:
        enc.solve(htd=htd, force_lex=args.force_lex, sb=args.sb)

    # Solve using the SMT solver
    inpf.seek(0)
    p1 = subprocess.Popen(os.path.join(os.path.dirname(os.path.realpath(__file__)), 'optimathsat'), stdin=inpf, stdout=modelf, stderr=errorf, shell=True)
    p1.wait()

    # Retrieve the result
    modelf.seek(0)
    errorf.seek(0)
    outp = modelf.read()
    errp = errorf.read()

    inpf.close()
    modelf.close()
    errorf.close()

    solved = (len(errp) == 0)

    # Load the resulting model
    try:
        res = enc.decode(outp, False, htd=htd, repair=args.mode == 1)
    except ValueError:
        if args.mode == 2:
            sys.stdout.write("No model. Usually no HTD could be generated from GHTD. Check error log to make sure.")
        else:
            sys.stdout.write("No model. Check error log for more information. (May also occur in case SMT solver's output"
                       "format changed)\n")
        exit(2)

    # Display the HTD
    td = res['decomposition']

    # Run SMT-Repair
    if args.mode == 2 and result is None:
        run = True
        arcs = res['arcs'] if args.use_arcs else None
        ordering = res['ord'] if args.use_ordering else None
        result = res['objective']
        edges = [(i, j) for i, j in td.tree.edges] if args.use_tree else None
        bags = td.bags if args.use_bags else None

valid = td.validate(td.hypergraph)
valid_ghtd = GeneralizedHypertreeDecomposition.validate(td, td.hypergraph)
valid_sc = td.inverse_edge_function_holds()

sys.stdout.write("Result: {}\tValid:  {}\tSP: {}\tGHTD: {}\t\n".format(
    res['objective'],
    valid,
    valid_sc,
    valid_ghtd
))

if args.mode > 0 and not valid:
    exit(1)
