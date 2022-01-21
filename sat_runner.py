import argparse
import os
import time
import sys
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition

from networkx import Graph
from itertools import combinations
from networkx.algorithms.approximation import max_clique
from networkx.algorithms.clique import find_cliques
from pysat.solvers import Glucose3, Glucose4, Lingeling, Cadical, Minisat22, Maplesat, Gluecard3, Gluecard4, Mergesat3, MapleCM, MapleChrono, Minicard

import bounds.upper_bounds as bnd
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from sat_encoding import HtdSatEncoding
from sat_encoding2 import HtdSatEncoding2

parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')
parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')
parser.add_argument('-g', dest='ghtd', action='store_true', default=False,
                    help='Compute a GHTD instead of a HTD')

parser.add_argument('-s', dest="solver", default=0, type=int, help='The solver to use')
parser.add_argument('-b', dest="sb", default=False, action='store_true', help="Activate symmetry breaking")
parser.add_argument('-i', dest="incr", default=False, action="store_true", help="Activate incremental solving")
parser.add_argument('-c', dest="card", default=6, type=int, help="The cardinality encoding to use for non-incremental solving")
parser.add_argument('-q', dest="clique", default=0, type=int, help="The clique mode (0: off, 1: approx, 2: max cliques)")
parser.add_argument('-t', dest="tmpdir", default="/tmp", type=str, help="The temporary directory to use")
parser.add_argument('-m', dest="maxsat", default=False, action="store_true", help="Use MaxSAT")
parser.add_argument('-x', dest="external", default=None, action="store", type=str, help="Path to external solver")
parser.add_argument('-e', dest="encoding", default=0, type=int, choices=[0, 1], help="Encoding to use, 0=HtdLEO, 1=HtdEq")
args = parser.parse_args()


# The solver to use
solvers = [
    Glucose4,
    Glucose3,
    Lingeling,
    Cadical,
    Minisat22,
    Maplesat,
    MapleCM,
    MapleChrono,
    Mergesat3,
    Gluecard4,
    Gluecard3,
    Minicard
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

clique_mode = args.clique
clique = None
if clique_mode > 0:
    pv = Graph()
    for e in hypergraph_in.edges():
        # PRIMAL GRAPH CONSTRUCTION
        for u, v in combinations(hypergraph_in.get_edge(e), 2):
            pv.add_edge(u, v)

    if clique_mode == 1:
        clique = max_clique(pv)
    else:
        clique = max(find_cliques(pv), key=lambda x: len(x))

encoder = HtdSatEncoding(hypergraph_in) if args.encoding == 0 else HtdSatEncoding2(hypergraph_in)

res = encoder.solve(current_bound, not args.ghtd, solver, sb=args.sb, incremental=args.incr, enc_type=args.card, clique=clique,
                    maxsat=args.maxsat, tmpdir=args.tmpdir, external=args.external)

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
