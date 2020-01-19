from networkx import Graph, DiGraph, descendants, shortest_path
from itertools import combinations
from sys import maxsize
from random import randint

def compute_ordering(pg):
    # Build elimination ordering
    ordering = []
    g = pg.copy()

    while len(ordering) < len(pg.nodes):
        # Min Degree with random tiebreaker, tiebreak leads no irreproducibility
        # _, _, n = min((len(pv[x]), randint(0, 100), x) for x in pv.nodes)
        _, n = min((len(g[x]), x) for x in g.nodes)
        ordering.append(n)
        nb = g[n]
        for u in nb:
            for v in nb:
                if u > v:
                    g.add_edge(u, v)

        g.remove_node(n)

    return ordering
