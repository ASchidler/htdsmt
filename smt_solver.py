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

import bounds.upper_bounds as ubs
import bounds.lower_bounds as lbs
import weighted.weight_upper_bound as wub


def solve(output_path, output_name, input_file, clique_mode=0, htd=True, lb=None, arcs=None, order=None, force_lex=False,
          fix_val=None, edges=None, bags=None, sb=True, timeout=0, heuristic_repair=True, weighted=False):

    # Open output files, these are used to interface with the solver
    base_path = os.path.join(output_path, output_name)
    inpf = open(base_path + ".encoding", "w+")
    modelf = open(base_path + ".model", "w+")
    errorf = open(base_path + ".error", "w+")

    # Load graph. There is no working auto detect of encoding, so try both options
    hypergraph_in = Hypergraph.from_file(input_file, fischl_format=False)
    hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True, weighted=weighted)

    if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
        hypergraph_in = hypergraph2

    # Check if the vertex label is continuous
   # hypergraph, reverse_mapping = check_hypergraph_continuity(hypergraph_in)
    hypergraph = hypergraph_in
    reverse_mapping = None
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
    enc = smt_encoding.HtdSmtEncoding(hypergraph, stream=inpf, checker_epsilon=None)
    enc.solve(htd=htd, force_lex=force_lex, edges=edges, fix_val=fix_val, bags=bags, order=order, arcs=arcs,
              sb=sb, clique=clique, lb=lb, ub=ub, weighted=weighted)
    # enc = frasmt_encoding2.FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None)
    # enc.solve(htd=htd)
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
        res = enc.decode(outp, False, htd=htd, repair=heuristic_repair, weighted=weighted)
    except ValueError as ee:
        raise ee
        return None

    if reverse_mapping:
        remap(res, reverse_mapping, hypergraph_in)

    return res


def check_hypergraph_continuity(hg):
    """Checks if the vertices are a continuous list of nodes, if not it is remapped"""

    found = False
    for i in range(1, hg.number_of_nodes() + 1):
        if i in hg.nodes():
            found = True
            break

    # If the list of vertices is continuous, nothing to do
    if not found:
        return hg, None

    # Create mapping
    mapping = dict()
    reverse_mapping = dict()
    nodes = list(hg.nodes())

    for i in range(1, len(nodes)+1):
        mapping[nodes[i-1]] = i
        reverse_mapping[i] = nodes[i-1]

    hypergraph = Hypergraph()

    for k, e in hg.edges().items():
        new_e = [mapping[x] for x in e]
        hypergraph.add_hyperedge(new_e, edge_id=k, weight=None if hg.weights() is None else hg.weights()[k])

    return hypergraph, reverse_mapping


def remap(result, reverse_mapping, original):
    """Given a mapping for the vertices, maps the result back to the original graph"""

    result.ordering = [reverse_mapping[x] for x in result.ordering]
    result.arcs = {reverse_mapping[n1]:
        {reverse_mapping[n2]: v2 for n2, v2 in v1.items()}
        for n1, v1 in result.arcs.items()}

    result.weights = {}
    for k in result.decomposition.bags.keys():
        result.decomposition.bags[k] = {reverse_mapping[x] for x in result.decomposition.bags[k]}

    result.decomposition.hypergraph = original
