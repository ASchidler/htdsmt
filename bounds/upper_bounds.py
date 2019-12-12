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


def greedy(g, htd):
    # Build primal graph
    pg = Graph()
    for e in g.edges():
        for u, v in combinations(g.get_edge(e), 2):
            pg.add_edge(u, v)

    ordering = compute_ordering(pg)
    bags, tree, root = ordering_to_decomp(pg, ordering)

    # In case of HTD we require to not violate the special condition
    if htd:
        simplify_decomp(bags, tree)
        edge_cover = cover_htd(g, bags, tree, root)
    else:
        edge_cover = cover_ghtd(g, bags)

    return max(sum(v.values()) for v in edge_cover.values())


def ordering_to_decomp(pg, ordering):
    """Converts an elimination ordering into a decomposition"""

    tree = DiGraph()
    ps = {x: ordering.index(x) for x in ordering}
    bags = {n: {n} for n in ordering}

    for u, v in pg.edges:
        if ps[v] < ps[u]:
            u, v = v, u
        bags[u].add(v)

    for n in ordering:
        A = set(bags[n])
        if len(A) > 1:
            A.remove(n)
            _, nxt = min((ps[x], x) for x in A)

            bags[nxt].update(A)
            tree.add_edge(nxt, n)

    return bags, tree, ordering[-1]


def simplify_decomp(bags, tree):
    """Simplifies the decomposition by eliminating subsumed bags. This usually results in fewer bags."""
    # Eliminate subsumed bags
    cnt = 0
    changed = True

    while changed:
        changed = False

        for n in list(tree.nodes):
            nb = list(tree.succ[n])
            nb.extend(tree.pred[n])

            nbag = bags[n]
            for u in nb:
                if bags[u].issubset(nbag) or bags[u].issuperset(nbag):
                    cnt += 1
                    for v in tree.succ[n]:
                        if u != v:
                            tree.add_edge(u, v)
                    for v in tree.pred[n]:
                        if u != v:
                            tree.add_edge(v, u)
                    if bags[u].issubset(nbag):
                        bags[u] = nbag

                    tree.remove_node(n)
                    changed = True
                    break


def cover_ghtd(g, bags):
    edge_cover = {n: {e: 0 for e in g.edges().keys()} for n in g.nodes()}

    for k, v in bags.items():
        remaining = set(v)

        # cover bag, maximize cover, minimize remainder
        while len(remaining) > 0:
            c_best = (0, None, None)
            for e, ed in g.edges().items():
                ed = set(ed)

                intersect = len(remaining & ed)
                if intersect > c_best[0]:
                    c_best = (intersect, e, ed)

            _, e, ed = c_best
            remaining -= ed
            edge_cover[k][e] = 1

    return edge_cover


def cover_htd(g, bags, tree, root):
    q1 = [root]
    q2 = []

    edge_cover = {n: {e: 0 for e in g.edges().keys()} for n in tree.nodes}
    while q1 or q2:
        if not q1:
            q1 = q2
            q2 = []

        n = q1.pop()
        for u in tree.successors(n):
            q2.append(u)

        bag = bags[n]
        desc = set(descendants(tree, n))

        while len(bag) > 0:
            c_best = (0, maxsize, None, None)
            for e, ed in g.edges().items():
                ed = set(ed)

                intersect = len(bag & ed)
                remainder = len((ed - bag) & desc)
                # Try to fill the bag with as few problematic vertices as possible
                # if intersect > c_best[0] or (intersect == c_best[0] and remainder < c_best[1]):
                if intersect > 0 and (
                        remainder < c_best[1] or (remainder == c_best[1] and intersect > c_best[0])):
                    c_best = (intersect, remainder, e, ed)

            _, _, e, ed = c_best
            bag -= ed
            edge_cover[n][e] = 1

            for u in (ed - bag) & desc:
                for v in shortest_path(tree, n, u):
                    if v != n:
                        bags[v].add(u)

    return edge_cover

