from __future__ import absolute_import

import re
from itertools import combinations
from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from decomposition_result import DecompositionResult
from bounds import upper_bounds
import networkx as nx


class HtdSmtEncoding:
    def __init__(self, hypergraph, stream):
        self.hypergraph = hypergraph
        self.num_vars = 1
        self.num_cls = 0

        self.__clauses = []
        self._vartab = {}
        self.stream = stream
        self.cards = []
        self.stream.write('(set-option :print-success false)\n(set-option :produce-models true)\n')

    def prepare_vars(self, weighted):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # ordering
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                self.stream.write("(declare-const ord_{i}_{j} Bool)\n".format(i=i, j=j))

        # arcs
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # declare arc_ij variables
                self.stream.write("(declare-const arc_{i}_{j} Bool)\n".format(i=i, j=j))

        # weights
        for j in range(1, n + 1):
            for ej in range(1, m + 1):
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

    def literal_str(self, x):
        if x < 0:
            ret = '(not %s)' % self._vartab[abs(x)]
        else:
            ret = '%s' % self._vartab.get(x)
        return ret

    def add_clause(self, C):
        # C = map(neg, C)
        # self.stream.write("%s 0\n" %" ".join(map(str,C)))
        self.stream.write("(assert (or %s))\n" % (' '.join(C)))
        self.num_cls += 1

    # prepare variables
    def fractional_counters(self):
        n = self.hypergraph.number_of_nodes()

        for j in range(1, n + 1):
            weights = []
            for e in self.hypergraph.edges():
                assert (e > 0)
                weights.append("weight_{j}_e{e}".format(j=j, e=e))

            weights = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]

            self.stream.write("(assert (<= {weights} m))\n".format(weights=weights))

            # set optimization variable or value for SAT check

    def elimination_ordering(self, n):
        tord = lambda p, q: 'ord_{p}_{q}'.format(p=p, q=q) if p < q \
            else '(not ord_{q}_{p})'.format(p=p, q=q)

        # Some improvements
        for i in range(1, n + 1):
            for j in range(i+1, n + 1):
                # Arcs cannot go in both directions
                self.add_clause([f"(not arc_{j}_{i})", f"(not arc_{i}_{j})"])
                # Enforce arc direction from smaller to bigger ordered vertex
                self.add_clause([f"(not ord_{i}_{j})", f"(not arc_{j}_{i})"])
                self.add_clause([f"ord_{i}_{j}", f"(not arc_{i}_{j})"])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.stream.write("(assert (=> {ordvar} (not arc_{j}_{i})))\n".format(i=i, j=j, ordvar=tord(i, j)))

                for l in range(1, n + 1):
                    if i == l or j == l:
                        continue

                    C = []
                    C.append(f"(not ord_{i}_{j})" if i < j else f"ord_{j}_{i}")
                    C.append(f"(not ord_{j}_{l})" if j < l else f"ord_{l}_{j}")
                    C.append(f"ord_{i}_{l}" if i < l else f"(not ord_{l}_{i})")
                    self.add_clause(C)

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    # AS CLAUSE
                    self.add_clause([f"ord_{i}_{j}", f"arc_{j}_{i}"])
                    self.add_clause([f"(not ord_{i}_{j})", f"arc_{i}_{j}"])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for l in range(j + 1, n + 1):
                    if i == l or j == l:
                        continue

                    # AS CLAUSE
                    # These to clauses are entailed by the improvement clauses and the next clause
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redundant
                    self.add_clause([f"(not arc_{i}_{j})", f"(not arc_{i}_{l})", f"arc_{j}_{l}", f"arc_{l}_{j}"])

        # forbid self loops
        for i in range(1, n + 1):
            # self.__solver.add_assertion(Not(self.literal(self.arc[i][i])))
            # self.stream.write("(assert (not arc_{i}_{i}))\n".format(i=i))
            self.add_clause([f"(not arc_{i}_{i})"])

    def cover(self, n, weighted):
        # If a vertex j is in the bag, it must be covered:
        for i in range(1, n + 1):
            # arc_ij then i most be covered by some edge (because i will end up in one bag)
            weights = []
            for e in self.hypergraph.incident_edges(i):
                weights.append(f"weight_{i}_e{e}")

            summed = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
            compared = f">= {summed} 1"

            self.stream.write(
                "(assert ({weights}))\n".format(i=i,  weights=compared))

            for j in range(1, n + 1):
                if i == j:
                    continue

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                summed = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
                compared = f">= {summed} 1" if not weighted else f">= {summed} 1"

                self.stream.write(
                    "(assert (=> arc_{i}_{j} ({weights})))\n".format(i=i, j=j, weights=compared))

    def break_clique(self, clique):
        if clique:
            # Vertices not in the clique are ordered before the clique
            for i in self.hypergraph.nodes():
                if i in clique:
                    continue
                for j in clique:
                    if i < j:
                        self.add_clause([f"ord_{i}_{j}"])
                    else:
                        self.add_clause([f"(not ord_{j}_{i})"])

            # Vertices of the clique are ordered lexicographically
            for i in clique:
                for j in clique:
                    if i != j:
                        if i < j:
                            self.add_clause([f"ord_{i}_{j}"])
                        # else:
                        #     self.add_clause([-self.ord[j][i]])

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

    def encode(self, clique=None, htd=True, arcs=None, order=None, sb=True, weighted=False):
        n = self.hypergraph.number_of_nodes()

        self.break_clique(clique=clique)
        self.elimination_ordering(n)
        self.cover(n, weighted)

        if sb:
            self.break_order_symmetry()

        if htd:
            self.encode_htd2(n)

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

    def solve(self, clique=None, optimize=True, htd=True, lb=None, ub=None, arcs=None, order=None,
              fix_val=None, sb=True, weighted=False):
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

        self.encode(clique=clique, htd=htd, arcs=arcs, order=order, sb=sb, weighted=weighted)

        self.fractional_counters()

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
            #edges = self._get_edges(model) if htd else None
            edges = None
            bags = None #self._get_bags(model) if htd else None
            #edges = None
            #arcs = None
            #edges = None

            htdd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                        weights=weights,
                                                        checker_epsilon=None, edges=edges, bags=bags, htd=htd, repair=repair)

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

                    # Omitted intersected with descendants
                    problem = (htdd._B(n) - htdd.bags[n]) & desc
                    while problem:
                        d = problem.pop()
                        pth = nx.shortest_path(htdd.tree, source=n, target=d)
                        pth.pop()
                        while pth:
                            c_node = pth.pop()
                            # TODO: How can this happen? Maybe there are unecessary hyperedges in the cover?
                            # if len(htdd.bags[d] - htdd._B(c_node)) > 0:
                            #     pass
                            # We know that every bag on the bath from n to d is a subset of d
                            htdd.bags[c_node].update(htdd.bags[d])
                            htdd.hyperedge_function[c_node] = htdd.hyperedge_function[n]
        except RuntimeError:
            pass
        #except KeyError:
        # TODO: We can simplify the HTD, but here we have to take care, that even if neighboring bags are subsets, either
        # both bags have only one child or the cover is identical. Otherwise, the special condition may be violated.

        #    raise ValueError("Could not parse output. In case of mode 2 may indicate unsat, otherwise check error log.")

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
            raise TypeError("Fractional Hypertree Decompositions for graphs with isolated vertices.")

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

    def encode_htd2(self, n):
        # # Whenever a tree node covers an edge, it covers all of the edge's vertices
        for i in range(1, n+1):
            incident = set()
            for e in self.hypergraph.incident_edges(i):
                incident.update(self.hypergraph.get_edge(e))
            incident.remove(i)

            for j in incident:
                self.stream.write("(declare-const subset_{}_{} Bool)\n".format(i, j))

            for j in range(1, n+1):
                if i != j:
                    self.stream.write("(declare-const forbidden_{}_{} Bool)\n".format(i, j))

        for i in range(1, n+1):
            incident = set()
            for e in self.hypergraph.incident_edges(i):
                incident.update(self.hypergraph.get_edge(e))
            incident.remove(i)
            for j in incident:
                if i == j:
                    continue
                self.stream.write(f"(assert (=> subset_{j}_{i} arc_{i}_{j}))\n")

                for e in self.hypergraph.edges():
                    # = 1 is superior to > 0. Keeping these two clauses separate is faster than (= w1 w2)
                    # The first clause follows by optimality... Grants a great speedup...
                    # self.stream.write(f"(assert (=> (and subset_{i}_{j} (= weight_{j}_e{e} 0)) (= weight_{i}_e{e} 0)))\n")
                    self.stream.write(f"(assert (=> (and subset_{i}_{j} (= weight_{j}_e{e} 1)) (= weight_{i}_e{e} 1)))\n")

                for k in incident:
                    if k == i or k == j:
                        continue
                    self.stream.write("(assert (=> (and arc_{i}_{k} (not arc_{j}_{k})) (not subset_{i}_{j})))\n"
                                      .format(i=i, j=j, k=k))
                    # Subset must be true for every bag in the path
                    self.stream.write("(assert (=> (and subset_{k}_{i} arc_{i}_{j} arc_{j}_{k}) "
                                      "subset_{j}_{i}))\n"
                                      .format(i=i, j=j, k=k))

        for i in range(1, n + 1):
            incident = set()
            for e in self.hypergraph.incident_edges(i):
                incident.update(self.hypergraph.get_edge(e))
            incident.remove(i)

            for j in range(1, n + 1):
                if i == j:
                    continue

                if j not in incident:
                    self.stream.write(f"(assert (=> arc_{i}_{j} forbidden_{i}_{j}))\n")
                else:
                    if i < j:
                        self.stream.write(f"(assert (=> ord_{i}_{j} forbidden_{i}_{j}))\n")
                    else:
                        self.stream.write(f"(assert (=> (not ord_{j}_{i}) forbidden_{i}_{j}))\n")

                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    self.stream.write(f"(assert (=> (and arc_{j}_{k} forbidden_{i}_{j}) forbidden_{i}_{k}))\n")

            for e in self.hypergraph.incident_edges(i):
                for j in range(1, n + 1):
                    if i != j:
                        if j not in incident:
                            self.stream.write(f"(assert (=> forbidden_{i}_{j} (= weight_{j}_e{e} 0)))\n")
                        else:
                            self.stream.write(f"(assert (=> (and forbidden_{i}_{j} (not subset_{j}_{i}))  (= weight_{j}_e{e} 0)))\n")