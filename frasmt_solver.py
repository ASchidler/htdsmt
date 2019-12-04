import frasmt_encoding
import os
import subprocess
from shutil import which
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from networkx.algorithms.clique import find_cliques
from networkx.algorithms.approximation import max_clique
from networkx import Graph
from itertools import combinations

"""Starts the correct solver and returns the solver result"""


def solve(output_path, output_name, input_file, clique_mode=0, htd=True, lb=None, arcs=None, order=None, force_lex=False,
          fix_val=None, edges=None, bags=None, sb=True, timeout=0, heuristic_repair=True):

    # Open output files, these are used to interface with the solver
    base_path = os.path.join(output_path, output_name)
    inpf = open(base_path + ".encoding", "w+")
    modelf = open(base_path + ".model", "w+")
    errorf = open(base_path + ".error", "w+")

    # Load graph. There is no working auto detect of encoding, so try both options
    hypergraph = Hypergraph.from_file(input_file, fischl_format=False)
    hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True)

    if len(hypergraph2.edges()) > len(hypergraph.edges()):
        hypergraph = hypergraph2

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
    enc = frasmt_encoding.FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None)
    enc.solve(htd=htd, force_lex=force_lex, edges=edges, fix_val=fix_val, bags=bags, order=order, arcs=arcs,
              sb=sb, clique=clique, lb=lb)
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
        res = enc.decode(outp, False, htd=htd, repair=heuristic_repair)
    except ValueError:
        return None

    return res
