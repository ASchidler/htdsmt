from networkx import Graph
from itertools import combinations
import bounds.upper_bounds as ub
from sys import maxsize


def greedy(g, bb=True):
    # Build primal graph
    pg = Graph()
    for e in g.edges():
        for u, v in combinations(g.get_edge(e), 2):
            pg.add_edge(u, v)

    ordering = ub.compute_ordering(pg)
    bags, tree, root = ub.ordering_to_decomp(pg, ordering)
    ub.improve_scramble(pg, ordering, bound=max(len(b) - 2 for b in bags.values()))
    ub.simplify_decomp(bags, tree)
    edge_cover = greedy_cover(g, bags)

    if bb:
        ub.bandb(g, bags, edge_cover)
    return max(sum(v.values()) for v in edge_cover.values())


def greedy_cover(g, bags):
    """Computes a cover by greedily packing the cheapest edge (per covered vertex)"""
    edge_cover = {n: {e: 0 for e in g.edges().keys()} for n in g.nodes()}
    w = g.weights()

    for k, v in bags.items():
        remaining = set(v)

        # cover bag, minimize cost per covered vertex
        while len(remaining) > 0:
            c_best = (maxsize, None, None)
            for e, ed in g.edges().items():
                ed = set(ed)

                intersect = len(remaining & ed)
                if intersect > 0:
                    ratio = w[e] * 1.0 / intersect
                    if ratio < c_best[0]:
                        c_best = (ratio, e, ed)

            _, e, ed = c_best
            remaining -= ed
            edge_cover[k][e] = w[e]

    return edge_cover

