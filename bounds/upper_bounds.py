from networkx import Graph, DiGraph, descendants, shortest_path
from itertools import combinations
from sys import maxsize
from random import randint

def greedy(g, htd):
    #TODO: Avoid the many copies of the primal graph...

    # Build primal graph
    pv = Graph()
    for e in g.edges():
        # PRIMAL GRAPH CONSTRUCTION
        for u, v in combinations(g.get_edge(e), 2):
            pv.add_edge(u, v)

    # Build elimination ordering
    ordering = []
    pvo = pv.copy()

    while len(ordering) < len(pvo.nodes):
        # Min Degree with random tiebreaker, tiebreak leads no irrepdoducibility
        #_, _, n = min((len(pv[x]), randint(0, 100), x) for x in pv.nodes)
        _, n = min((len(pv[x]), x) for x in pv.nodes)
        ordering.append(n)
        nb = pv[n]
        for u in nb:
            for v in nb:
                if u > v:
                    pv.add_edge(u, v)

        pv.remove_node(n)

    bags = ordering_to_decomp(pvo, ordering)
    edge_cover = {n: {e: 0 for e in g.edges().keys()} for n in pvo.nodes}

    # In case of HTD we require to not violate the special condition
    if htd:
        tree = DiGraph()
        ps = {x: ordering.index(x) for x in ordering}
        for n in ordering:
            if n != ordering[len(ordering) - 1]:
                _, nxt = min((ps[x], x) for x in bags[n] if ps[x] > ps[n])
                tree.add_edge(nxt, n)
        edge_cover = ghtd_to_htd(tree, bags, g)
    else:
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

    return max(sum(v.values()) for v in edge_cover.values())


def ordering_to_decomp(g_in, ordering):
    """Converts an elimination ordering into a decomposition"""

    # TODO: Return full decomp, not only bags
    # ps = {x: ordering.index(x) for x in ordering}
    g = g_in.copy()
    bags = {}
    for n in ordering:
        bags[n] = {n}
        if len(g.nodes) > 1:
            bags[n].update(g[n])
            for u in g[n]:
                for v in g[n]:
                    if u < v:
                        g.add_edge(u, v)
            g.remove_node(n)

    return bags


def ghtd_to_htd(tree, bags, g):
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

    # Now that the tree is potentially simpler, try to cover the bags
    # Proceed top down
    # find root:
    c_root = next(tree.nodes.__iter__())
    while len(tree.pred[c_root]) > 0:
        c_root = next(tree.pred[c_root].__iter__())

    q1 = [c_root]
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

