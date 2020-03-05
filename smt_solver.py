import smt_encoding
import os
import subprocess
from shutil import which
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from networkx.algorithms.clique import find_cliques
from networkx.algorithms.approximation import max_clique
from networkx import Graph
from itertools import combinations

"""Starts the correct solver and returns the solver result"""


def solve(output_path, output_name, input_file, clique_mode=0, htd=True, lb=None,  fix_val=None, timeout=0):

    # Open output files, these are used to interface with the solver
    base_path = os.path.join(output_path, output_name)
    inpf = open(base_path + ".encoding", "w+")
    modelf = open(base_path + ".model", "w+")
    errorf = open(base_path + ".error", "w+")

    # Load graph. There is no working auto detect of encoding, so try both options
    hypergraph_in = Hypergraph.from_file(input_file, fischl_format=False)
    hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True)

    if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
        hypergraph_in = hypergraph2

    hypergraph = hypergraph_in

    # Find clique if requested
    clique = None
    if clique_mode > 0:
        pv = Graph()
        for e in hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for u, v in combinations(hypergraph.get_edge(e), 2):
                pv.add_edge(u, v)

        if clique == 1:
            clique = max_clique(pv)
        else:
            _, clique = max((len(x), x) for x in find_cliques(pv))

    # Create encoding
    ub = None
    # This computes an upper bound to use. In general it would be better to use ub-1 as an upper bound
    # if this fails, then the approximation is a solution, or if we have a ghtd with value ub, we also know
    # that the approximation is a valid upper bound
    # if fix_val is None and ub is None:
    #     ub = ubs.greedy(hypergraph, htd) if not weighted else wub.greedy(hypergraph)
    #     print(ub)
    enc = smt_encoding.HtdSmtEncoding(hypergraph, stream=inpf)
    enc.solve(htd=htd, fix_val=fix_val, clique=clique, lb=lb, ub=ub)

    inpf.seek(0)

    # Find and start solver, either in path or current directory
    executable = 'optimathsat' if which('optimathsat') is not None else os.path.join(os.path.dirname(os.path.realpath(__file__)), 'optimathsat')

    p1 = subprocess.Popen(executable, stdin=inpf, stdout=modelf, stderr=errorf, shell=True)
    if timeout == 0:
        p1.wait()
    else:
        try:
            p1.wait(timeout)
        except subprocess.TimeoutExpired:
            return None

    # Retrieve the result from files
    modelf.seek(0)
    outp = modelf.read()

    inpf.close()
    modelf.close()
    errorf.close()

    # Load the resulting model
    try:
        res = enc.decode(outp, False, htd=htd)
    except ValueError as ee:
        raise ee

    return res