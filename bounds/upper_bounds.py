from networkx import Graph, DiGraph, descendants, shortest_path
from itertools import combinations
from sys import maxsize
from random import randint


def compute_ordering(instance, criteria=lambda i, g: min((len(g[x]), x) for x in g.nodes)[1]):
    # Build elimination ordering
    ordering = []
    g = instance.pg.copy()

    while len(ordering) < len(instance.pg.nodes):
        # Min Degree with random tiebreaker, tiebreak leads no irreproducibility
        # _, _, n = min((len(pv[x]), randint(0, 100), x) for x in pv.nodes)
        n = criteria(instance, g)
        ordering.append(n)
        nb = g[n]
        for u in nb:
            for v in nb:
                if u > v:
                    g.add_edge(u, v)

        g.remove_node(n)

    return ordering


def greedy(instance, htd, bb=True):
    # Build primal graph
    ordering = compute_ordering(instance)
    bags, tree, root = ordering_to_decomp(instance, ordering)
    improve_scramble(instance, ordering, bound=max(len(b)-2 for b in bags.values()))

    # In case of HTD we require to not violate the special condition
    simplify_decomp(bags, tree)
    if htd:
        edge_cover = cover_htd(instance, bags, tree, root)
    else:
        edge_cover = cover_ghtd(instance, bags)
        if bb:
            bandb(instance, bags, edge_cover)

    return max(sum(v.values()) for v in edge_cover.values()), (tree, bags, edge_cover)


def improve_scramble(g, ordering, rounds=100, bound=maxsize, interval=15):
    """Tries to improve the bound by randomly scrambling the elements in an interval"""

    limit = len(ordering) - 1 - interval if len(ordering) > interval else 0
    interval = min(interval, len(ordering))

    for _ in range(0, rounds):
        index = randint(0, limit) if limit > 0 else 0

        old = ordering[index:index+interval]
        for c_i in range(0, interval-1):
            randindex = randint(0, interval - 1 - c_i) + index + c_i
            ordering[index + c_i], ordering[randindex] = ordering[randindex], ordering[index + c_i]

        result = max(len(x) for x in ordering_to_decomp(g, ordering)[0].values()) - 1

        # If the new bound is worse, restore
        if result > bound:
            for i in range(0, interval):
                ordering[index + i] = old[i]
        else:
            bound = result

    return bound


def ordering_to_decomp(instance, ordering):
    """Converts an elimination ordering into a decomposition"""

    tree = DiGraph()
    ps = {x: ordering.index(x) for x in ordering}
    bags = {n: {n} for n in ordering}

    for u, v in instance.pg.edges:
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


# TODO: Move this to some utility class
# TODO: Take care not to violate the special condition in case of HTD
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


def cover_ghtd(instance, bags):
    edge_cover = {n: {e: 0 for e in instance.hg.edges().keys()} for n in instance.hg.nodes()}

    # Establish a rank for each vertex, i.e. in how many hyperedges it occurs
    vertex_rank = {}

    for v in instance.hg.nodes():
        cnt = 0
        for e, ed in instance.hg.edges().items():
            if v in ed:
                cnt += 1
        vertex_rank[v] = cnt

    # Cover bags
    for k, v in bags.items():
        remaining = set(v)

        # cover bag, minimize cost per covered vertex
        while len(remaining) > 0:
            c_best = (0, None, None, maxsize)
            for e, ed in instance.hg.edges().items():
                intersect_vertices = set(ed) & remaining
                intersect = len(intersect_vertices)
                rank = sum(vertex_rank[v] for v in intersect_vertices)

                if intersect > c_best[0] or (intersect == c_best[0] and rank < c_best[3]):
                    c_best = (intersect, e, intersect_vertices, rank)

            _, e, ed, _ = c_best
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


def bandb_sub(b, edges, ub):
        """Recursive function that computes the cover. Use pos=-1 and value False for call. Returns maxsize of no better
        solution could be found."""
        q = [(b, 0, -1, False, [])]
        best = ub
        best_list = None

        while q:
            b, c, pos, val, e_list = q.pop()

            # Reached the end, but did not fill the bag, ignore solution
            if pos == len(edges):
                continue

            # If we should add the edge, add costs and remove from bag
            if val:
                e, ed = edges[pos]

                # Hyperedge does not contribute anything, adding it cannot be optimal
                if len(ed & b) == 0:
                    continue

                c = c + 1

                # Exceed upper bound -> suboptimal
                if c >= best:
                    continue

                b = b - ed
                # Copy list and add edge
                e_list = list(e_list)
                e_list.append(e)

                # Found a solution, store (we already know it's better than best from above)
                if len(b) == 0:
                    best = c
                    best_list = e_list

            # "Subcalls"
            q.append((b, c, pos + 1, False, e_list))
            q.append((b, c, pos + 1, True, e_list))

        # Return result if better has been found, otherwise return default value
        if best < ub:
            return best, best_list
        return maxsize, None


def bandb(instance, bags, cover, subcall=bandb_sub):
    """Tries to improve a given cover, by computing the optimal cover via branch and bound"""

    # Not execute the B&B for every bag. First calculate the width and process in reverse order
    # Using this ordering, we can stop whenever we cannot improve a bag, as subsequent improvement will not
    # decrease the width
    bounds_bags = [
        (sum(x for x in cover[k].values()), k, v) for k, v in bags.items()]

    bounds_bags.sort(reverse=True)

    c_global_ub = 0
    for b_ub, k, v in bounds_bags:
        # Global upper bound cannot be improved by improving this bag, nothing can be done
        if b_ub <= c_global_ub:
            return

        # Filter out only those edges that may cover the bag. Remove those that are subsumed
        relevant_edges = []
        for e, ed in instance.hg.edges().items():
            intersect = set(ed) & v
            if len(intersect) > 0:
                found = False
                for ce, ced in relevant_edges:
                    if intersect.issubset(ced):
                        found = True
                        break
                    if intersect.issuperset(ced):
                        ced.update(intersect)
                        found = True
                        break

                if not found:
                    relevant_edges.append((e, intersect))

        # Start recursive call
        res = subcall(v, relevant_edges, b_ub)

        # Apply new cover if better
        if res[0] < b_ub:
            cover[k] = {e: 1 for e in res[1]}

        # This is valid due to the sort order
        c_global_ub = min(res[0], b_ub)
