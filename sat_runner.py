import argparse
import os
import time

from pysat.solvers import Glucose3, Glucose4, Lingeling, Cadical, Minisat22, Maplesat

import bounds.upper_bounds as bnd
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from sat_encoding import HtdSatEncoding

parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')
parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')
parser.add_argument('-g', dest='ghtd', action='store_true', default=False,
                    help='Compute a GHTD instead of a HTD')
parser.add_argument('-d', dest='tmp_dir', default='/tmp', help='Path for temporary files, defaults to /tmp')

parser.add_argument('-s', dest="solver", default='0', type=int, help='The solver to use')
parser.add_argument('-b', dest="sb", default=False, action='store_true', help="Activate symmetry breaking")

args = parser.parse_args()
tmp_dir = args.tmp_dir
if "TMPDIR" in os.environ:
    tmp_dir = os.environ['TMPDIR']

# The solver to use
solvers = [
    lambda: Glucose4(incr=True),
    lambda: Glucose3(incr=True),
    Lingeling,
    Cadical,
    Minisat22,
    Maplesat
]
solver = solvers[args.solver]

input_file = args.graph
hypergraph_in = Hypergraph.from_file(input_file, fischl_format=False)
hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True)

if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
    hypergraph_in = hypergraph2

current_bound = bnd.greedy(hypergraph_in, False, bb=False)
timeout = 0
before_tm = time.time()

encoder = HtdSatEncoding(hypergraph_in)
decomp = encoder.solve(current_bound, not args.ghtd, solver, sb=args.sb)

print(f"Width : {decomp.size}")
print(f"Solved in: {time.time() - before_tm}")
