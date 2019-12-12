from sys import maxsize
from itertools import chain, combinations


def mmd(g_in, ub=maxsize):
    # Copy hypergraph
    edges = {k: set(v) for k, v in g_in.edges().items()}
    adj = {x: {k for k, e in edges.items() if x in e} for x in g_in.nodes()}
    nodes = list(g_in.nodes())
    bound = 1

    pairwise = {n1: {n2: any(n1 in v and n2 in v for v in edges.values()) for n2 in nodes} for n1 in nodes}

    while len(nodes) > bound:
        # The degree is not a bound as in tw. The corresponding bound for ghtw (and therefore tw, as ghtw <= htw) is
        # the vertex with the smallest edge cover for itself and its adjacent vertices. As the optimal edge cover can
        # be time consuming to calculate, we use a lower bound for it.

        # Min and Second min
        cover = (maxsize, maxsize)
        min_nodes = (None, None)
        # TODO: The values should be cachable...
        for n in nodes:
            # Find all adjacent vertices
            nb = set(chain.from_iterable(edges[x] for x in adj[n]))

            # Now gather those adjacent vertices that occur in only one edge
            # occurrence = {x for x in nb if 1 == len([k for k, v in edges.items() if x in v])}
            #
            # # Count edges containing one of the unique vertices
            # estimate = len([k for k, v in edges.items() if len((v & occurrence)) > 0])

            nb.remove(n)

            estimate = 1
            start = 2

            found = True
            while found and start < cover[1]:
                found = False
                for comb in combinations(nb, start):
                    if all(not pairwise[x][y] for x in comb for y in comb if x > y):
                        estimate = start
                        start += 1
                        found = True
                        break

            if estimate < cover[0]:
                cover = (estimate, cover[0])
                min_nodes = (n, min_nodes[0])
            elif estimate < cover[1]:
                cover = (cover[0], estimate)
                min_nodes = (min_nodes[0], n)

        bound = max(bound, cover[0])

        # Find min common edges neighbor
        n = min_nodes[0]
        n_edges = set(adj[n])
        n_nb = set(chain.from_iterable(edges[x] for x in adj[n]))

        c_min = (maxsize, None)
        for u in n_nb:
            if u != n:
                val = len(n_edges & set(adj[u]))
                c_min = min(c_min, (val, u))

        # Contract
        u = c_min[1]
        for x in adj[n]:
            e = edges[x]
            e.remove(n)
            e.add(u)

            if len(e) > 1:
                adj[u].add(x)
            else:
                adj[u].discard(x)

        for x, tv in pairwise[n].items():
            if tv:
                pairwise[u][x] = True
                pairwise[x][u] = True

        # Cleanup redundant edges, either single vertex, or subsumed edges
        removal = set()
        for x1 in adj[u]:
            e1 = edges[x1]
            if len(e1) == 1:
                removal.add(x1)
                continue

            for x2 in adj[u]:
                if x2 > x1:
                    e2 = edges[x2]
                    if e2.issubset(e1):
                        removal.add(x2)
                    elif e1.issubset(e2):
                        removal.add(x1)

        for ek in removal:
            for x in edges[ek]:
                adj[x].remove(ek)

        adj.pop(n)
        nodes.remove(n)

    return bound
