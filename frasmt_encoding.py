from __future__ import absolute_import

import re
from itertools import combinations
from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from decomposition_result import DecompositionResult
from bounds import upper_bounds
import networkx as nx


class FraSmtSolver:
    def __init__(self, hypergraph, stream, wprecision=20, timeout=0, checker_epsilon=None):
        self.__checker_epsilon = checker_epsilon
        self.hypergraph = hypergraph
        self.num_vars = 1
        self.num_cls = 0
        self.timeout = timeout
        self.ord = None
        self.arc = None
        self.weight = None

        self.__clauses = []
        self._vartab = {}
        self.stream = stream
        self.cards = []
        self.wprecision = wprecision
        self.stream.write('(set-option :print-success false)\n(set-option :produce-models true)\n')

    def prepare_vars(self, weighted):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # self.ord = np.zeros((n + 1, n + 1), dtype=int)
        self.ord = [[None for j in range(n + 1)] for i in range(n + 1)]
        # ordering
        for i in range(1, n + 1):
            # TODO: so far more variables
            for j in range(i + 1, n + 1):
                # for j in range(i + 1, n + 1):
                # (declare-const ord_ij Bool)
                self.ord[i][j] = self.add_var(name='ord_%s_%s' % (i, j))
                self.stream.write("(declare-const ord_{i}_{j} Bool)\n".format(i=i, j=j))

        # arcs
        self.arc = [[None for j in range(n + 1)] for i in range(n + 1)]
        # self.arc = np.zeros((n + 1, n + 1), dtype=int)
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # declare arc_ij variables
                self.arc[i][j] = self.add_var(name='arc_%s_%s' % (i, j))
                self.stream.write("(declare-const arc_{i}_{j} Bool)\n".format(i=i, j=j))

        # weights
        self.weight = [[None for ej in range(m + 1)]
                       for j in range(n + 1)]

        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                # (declare-const weight_j_e Real)
                self.weight[j][ej] = self.add_var(name='weight_%s_e%s' % (j, ej))

                # Int is probably faster, real is more generic...
                self.stream.write("(declare-const weight_{i}_e{ej} Int)\n".format(i=j, ej=ej))
                if weighted:
                    # TODO: Check for optimal encoding
                    self.stream.write("(assert ( or (= weight_{i}_e{ej} 0) (=  weight_{i}_e{ej} {w})))\n"
                                      .format(i=j, ej=ej, w=int(self.hypergraph.weights()[ej])))
                else:
                    # Worse, keep encoding below
                    # self.stream.write("(assert (or (= weight_{i}_e{ej} 0) (= weight_{i}_e{ej} 1)))\n".format(i=j, ej=ej))
                    self.stream.write("(assert (<= weight_{i}_e{ej} 1))\n".format(i=j, ej=ej))
                    self.stream.write("(assert (>= weight_{i}_e{ej} 0))\n".format(i=j, ej=ej))

    def add_cards(self, C):
        self.cards.append(C)

    # z3.Real
    def add_var(self, name):
        vid = self.num_vars

        self._vartab[vid] = name
        self.num_vars += 1
        # exit(1)
        return vid

    def literal_str(self, x):
        if x < 0:
            ret = '(not %s)' % self._vartab[abs(x)]
        else:
            ret = '%s' % self._vartab.get(x)
        return ret

    def add_clause(self, C):
        # C = map(neg, C)
        # self.stream.write("%s 0\n" %" ".join(map(str,C)))
        self.stream.write("(assert (or %s))\n" % (' '.join([self.literal_str(x) for x in C])))
        self.num_cls += 1

    # prepare variables
    def fractional_counters(self, m):
        n = self.hypergraph.number_of_nodes()

        for j in range(1, n + 1):
            weights = []
            for e in self.hypergraph.edges():
                assert (e > 0)
                weights.append("weight_{j}_e{e}".format(j=j, e=e))

            weights = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]

            self.stream.write("(assert (<= {weights} {m}))\n".format(weights=weights, m=m))

    def elimination_ordering(self, n):
        tord = lambda p, q: 'ord_{p}_{q}'.format(p=p, q=q) if p < q \
            else '(not ord_{q}_{p})'.format(p=p, q=q)

        # Some improvements
        for i in range(1, n + 1):
            for j in range(i+1, n + 1):
                # Arcs cannot go in both directions
                self.add_clause([-self.arc[j][i], -self.arc[i][j]])
                # Enforce arc direction from smaller to bigger ordered vertex
                self.add_clause([-self.ord[i][j], -self.arc[j][i]])
                self.add_clause([self.ord[i][j], -self.arc[i][j]])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.stream.write("(assert (=> {ordvar} (not arc_{j}_{i})))\n".format(i=i, j=j, ordvar=tord(i, j)))

                for l in range(1, n + 1):
                    if i == l or j == l:
                        continue
                    C = []
                    C.append(-self.ord[i][j] if i < j else self.ord[j][i])
                    C.append(-self.ord[j][l] if j < l else self.ord[l][j])
                    C.append(self.ord[i][l] if i < l else -self.ord[l][i])
                    self.add_clause(C)

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    # AS CLAUSE
                    self.add_clause([self.ord[i][j], self.arc[j][i]])
                    self.add_clause([-self.ord[i][j], self.arc[i][j]])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for l in range(j + 1, n + 1):
                    if i == l:
                        continue

                    # AS CLAUSE
                    # These to clauses are entailed by the improvement clauses and the next clause
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redundant
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.arc[j][l], self.arc[l][j]])

        # forbid self loops
        for i in range(1, n + 1):
            # self.__solver.add_assertion(Not(self.literal(self.arc[i][i])))
            # self.stream.write("(assert (not arc_{i}_{i}))\n".format(i=i))
            self.add_clause([-self.arc[i][i]])

    def cover(self, n, weighted):
        # If a vertex j is in the bag, it must be covered:

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                summed = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
                compared = f">= {summed} 1"

                self.stream.write(
                    "(assert (=> arc_{i}_{j} ({weights})))\n".format(i=i, j=j, weights=compared))

            # arc_ij then i most be covered by some edge (because i will end up in one bag)
            weights = []
            for e in self.hypergraph.incident_edges(i):
                weights.append("weight_{i}_e{e}".format(i=i, e=e))

            summed = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
            compared = f">= {summed} 1"

            self.stream.write(
                "(assert ({weights}))\n".format(i=i, weights=compared))

    def break_clique(self, clique):
        if clique:
            # Vertices not in the clique are ordered before the clique
            for i in self.hypergraph.nodes():
                if i in clique:
                    continue
                for j in clique:
                    if i < j:
                        self.add_clause([self.ord[i][j]])
                    else:
                        self.add_clause([-self.ord[j][i]])

            # Vertices of the clique are ordered lexicographically
            for i in clique:
                for j in clique:
                    if i != j:
                        if i < j:
                            self.add_clause([self.ord[i][j]])
                        # else:
                        #     self.add_clause([-self.ord[j][i]])

    # twins is a list of list of vertices that are twins
    def encode_twins(self, twin_iter, clique):
        if not clique:
            clique = []
        if twin_iter:
            # vertices of a twin class are order lexicographically
            for twins in twin_iter:
                if len(twins) <= 1:
                    continue
                for i in twins:
                    if i in clique:
                        continue
                    for j in twins:
                        if i != j:
                            if j in clique:
                                continue
                            if i < j:
                                self.add_clause([self.ord[i][j]])

    def break_order_symmetry(self):
        n = self.hypergraph.number_of_nodes()

        def tord(ix, jx):
            return 'ord_{}_{}'.format(ix, jx) if ix < jx else '(not ord_{}_{})'.format(jx, ix)

        for i in range(1, n+1):
            for j in range(i+1, n+1):
                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    self.stream.write("(declare-const block_{}_{}_{} Bool)\n".format(i, j, k))

        for i in range(1, n+1):
            vvars = []
            for j in range(i+1, n+1):
                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    self.stream.write(
                        f"(assert (or (not {tord(j, k)}) (not arc_{k}_{i}) block_{i}_{j}_{k}))\n"
                    )
                    self.stream.write(
                        "(assert (or (not block_{i}_{j}_{k}) {ord}))\n"
                            .format(i=i, j=j, k=k, ord=tord(j, k)))

                    self.stream.write(
                        "(assert (or (not block_{i}_{j}_{k}) arc_{k}_{i}))\n"
                            .format(i=i, j=j, k=k))

    def encode(self, clique=None, twins=None, htd=True, arcs=None, order=None, enforce_lex=True, edges=None, bags=None, sb=True, weighted=False):
        n = self.hypergraph.number_of_nodes()

        self.break_clique(clique=clique)
        self.elimination_ordering(n)
        self.cover(n, weighted)
        self.encode_twins(twin_iter=twins, clique=clique)
        if sb:
            self.break_order_symmetry()

        if htd:
            self.encode_htd2(n, weighted=weighted)

        if arcs:
            for i in range(1, n + 1):
                for j in range(1, n + 1):
                    if i == j:
                        continue

                    if arcs[i][j]:
                        self.stream.write("(assert (or arc_{i}_{j} arc_{j}_{i}))\n".format(i=i, j=j))

        if order:
            for i in order:
                for j in range(i+1, n+1):
                    if order.index(i) < order.index(j):
                        self.stream.write("(assert ord_{i}_{j})\n".format(i=i, j=j))
                    else:
                        self.stream.write("(assert (not ord_{i}_{j}))\n".format(i=i, j=j))

        if edges:
            for i, j in edges:
                self.stream.write("(assert (or is_pred_{i}_{j} is_pred_{j}_{i}))\n".format(i=i, j=j))

        if bags:
            for i, b in bags.iteritems():
                for j in b:
                    self.stream.write("(assert is_bag_{i}_{j})\n".format(i=i, j=j))

    def solve(self, clique=None, twins=None, optimize=True, htd=True, lb=None, ub=None, arcs=None, order=None, force_lex=True,
              fix_val=None, edges=None, bags=None, sb=True, weighted=False):
        var = self.add_var("m")
        m = self._vartab[var]

        self.stream.write("(declare-const m Int)\n")
        self.stream.write("(assert (>= m 1))\n")

        if fix_val:
            self.stream.write("(assert (= m {}))\n".format(fix_val))
        else:
            if ub:
                self.stream.write("(assert (<= m {}))\n".format(lb))
            if lb:
                self.stream.write("(assert (>= m {}))\n".format(lb))

        self.prepare_vars(weighted)

        self.encode(clique=clique, twins=twins, htd=htd, arcs=arcs, order=order, enforce_lex=force_lex, edges=edges, bags=bags, sb=sb, weighted=weighted)

        # assert(False)
        self.fractional_counters(m)
        # self.add_all_at_most(m)

        if optimize:
            self.stream.write("(minimize m)\n")
        self.stream.write("(check-sat)\n(get-model)\n")

    def decode(self, output, is_z3, htd=False, repair=True, weighted=False):
        model = {}

        if not is_z3:
            lines = re.findall('\(([^ ]+) ([a-zA-Z0-9\( \/\)]*)\)', output)

            for nm, val in lines:
                # Last entry sometimes has the closing ) in the line
                val = val.replace(")", "").strip()

                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                elif "/" in val:
                    str = val.replace("(", "").replace(")", "").replace("/", "").strip().split(" ")
                    model[nm] = int(str[0]) * 1.0 / int(str[1])
                else:
                    model[nm] = int(val)
        else:
            lines = re.findall('\(define\-fun ([^ ]*) \(\) [a-zA-Z]*\s*([a-zA-Z0-9]*)\)', output)

            for nm, val in lines:
                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                else:
                    model[nm] = int(val)

        try:
            ordering = self._get_ordering(model)
            weights = self._get_weights(model, ordering)
            arcs = self._get_arcs(model)

            htdd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                        weights=weights,
                                                        checker_epsilon=self.__checker_epsilon, htd=htd, repair=repair)

            # This "fixes" the HTD decomposition. The encoding allows the special condition to be violated in special
            # cases, i.e. if neighboring bags have the same cover and the bags are subsets
            if htd:
                for i in range(1, self.hypergraph.number_of_nodes()+1):
                    for j in range(1, self.hypergraph.number_of_nodes() + 1):
                        if i != j and arcs[i][j]:
                            htdd.bags[i].add(j)

                htdd.tree = nx.DiGraph()
                for i in range(0, len(ordering)):
                    n = ordering[i]
                    for j in range(i+1, len(ordering)):
                        v = ordering[j]
                        if arcs[n][v]:
                            htdd.tree.add_edge(v, n)
                            break

                # TODO: This is really inefficient
                # TODO: Add a debug check for the subset invariant
                root = [n for n in htdd.tree.nodes if len(list(htdd.tree.predecessors(n))) == 0][0]
                q = [root]
                while q:
                    n = q.pop()
                    q.extend(list(htdd.tree.successors(n)))
                    desc = set(nx.descendants(htdd.tree, n))
                    #omitted = htdd._B(n) - htdd.bags[n]
                    problem = (htdd._B(n) - htdd.bags[n]) & desc
                    while problem:
                        d = problem.pop()
                        pth = nx.shortest_path(htdd.tree, source=n, target=d)
                        pth.pop()
                        while pth:
                            c_node = pth.pop()

                            # We know that every bag on the bath from n to d is a subset of d
                            htdd.bags[c_node].update(htdd.bags[d])
                            htdd.hyperedge_function[c_node] = htdd.hyperedge_function[n]
            #upper_bounds.simplify_decomp(htdd.bags, htdd.tree, htdd.hyperedge_function)
        except KeyError:
            raise ValueError("Could not parse output. In case of mode 2 may indicate unsat, otherwise check error log.")

        # We can still simplify the HTD by merging subset-bags. But for HTDs we have to be careful. If we merge up in
        # the tree, two conditions must hold: 1. The neighbor is a subset, 2. The cover is a superset. Otherwise SP
        # might get violated. If we merge down, this is not problem and subset is enough.

        # if not htd.validate(self.hypergraph):
        #     raise RuntimeError("Found a GHTD that is not a HTD")

        return DecompositionResult(htdd.width(), htdd, arcs, ordering, weights)

    def _get_ordering(self, model):
        ordering = []
        for i in range(1, self.hypergraph.number_of_nodes() + 1):
            pos = 0
            for j in ordering:
                # We know j is smaller due to range processing
                if not model["ord_{}_{}".format(j, i)]:
                    break
                # Move current element one position forward
                pos += 1
            ordering.insert(pos, i)

        return ordering

    def _get_weights(self, model, ordering):
        ret = {}
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n + 1):
            # print 'bag %i'
            ret[i] = {}
            for e in self.hypergraph.edges():
                assert (e > 0)
                ret[i][e] = model["weight_{}_e{}".format(i, e)]

        last_vertex = ordering[-1]
        incident_edges = self.hypergraph.incident_edges(last_vertex).keys()
        if len(incident_edges) == 0:
            raise TypeError("Hypertree Decompositions for graphs with isolated vertices.")

        return ret

    def _get_arcs(self, model):
        n = self.hypergraph.number_of_nodes()
        ret = {}

        for i in range(1, n+1):
            ret[i] = {}
            #ret[i][i] = True
            for j in range(1, n+1):
                if i != j:
                    ret[i][j] = model["arc_{}_{}".format(i, j)]

        return ret

    def encode_htd2(self, n, weighted=False):
        m = self.hypergraph.number_of_edges()

        def tss(ni, nj):
            return "subset_{}_{}".format(nj, ni) if ni > nj else "subset_{}_{}".format(ni, nj)

        def tord(ix, jx):
            return 'ord_{}_{}'.format(ix, jx) if ix < jx else '(not ord_{}_{})'.format(jx, ix)

        def tf(ni, nj):
            return "is_forbidden_{}_{}".format(nj, ni) if ni > nj else "is_forbidden_{}_{}".format(ni, nj)

        # # Whenever a tree node covers an edge, it covers all of the edge's vertices
        for i in range(1, n+1):
            for j in range(i + 1, n + 1):
                self.stream.write("(declare-const is_forbidden_{}_{} Bool)\n".format(i, j))
                self.stream.write("(declare-const subset_{}_{} Bool)\n".format(i, j))

        for i in range(1, n+1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.stream.write(
                    f"(assert (=> (and {tord(i, j)} (not arc_{i}_{j})) (not {tss(i, j)})))\n")

                # Ensure identical covers
                if i < j:
                    for e in self.hypergraph.edges():
                        # = 1 is superior to > 0
                        self.stream.write(f"(assert (=> (not (= weight_{i}_e{e} weight_{j}_e{e})) "
                                          f"(not {tss(i, j)})))\n")

                for k in range(1, n + 1):
                    if k == i or k == j:
                        continue
                    # Ensure identical bags
                    self.stream.write(f"(assert (=> (and arc_{i}_{k} {tord(j, k)} (not arc_{j}_{k})) (not {tss(i, j)})))\n")
                    # Ensure that nodes in the path are also subsets
                    self.stream.write(f"(assert (=> (and (not {tss(j, k)}) arc_{i}_{j} arc_{j}_{k}) "
                                      f"(not {tss(i, k)})))\n")
                    # TODO: Actually the second part (the two arcs) now correlates with forbidden?
                    self.stream.write(f"(assert (=> (and (not {tss(i, j)}) arc_{i}_{j} arc_{j}_{k}) "
                                      f"(not {tss(i, k)})))\n")

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.stream.write(f"(assert (=> arc_{i}_{j} {tf(i, j)}))\n")

                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    self.stream.write(f"(assert (=> (and arc_{i}_{j} {tf(i, k)}) {tf(j, k)}))\n")

                for e in self.hypergraph.incident_edges(i):
                    self.stream.write(f"(assert (=> (and {tf(i, j)} {tord(i, j)} (not {tss(i, j)})) (= weight_{j}_e{e} 0)))\n")