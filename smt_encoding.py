from __future__ import absolute_import

import re
from itertools import combinations
from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from decomposition_result import DecompositionResult
from bounds import upper_bounds
import networkx as nx
from collections import defaultdict
import lib.optimathsat as optimathsat


def neg(var):
    if var.startswith("(not "):
        return var[4:-1]
    else:
        return f"(not {var})"


class HtdSmtEncoding:
    def __init__(self, hypergraph):
        self.hypergraph = hypergraph
        cfg = optimathsat.msat_create_config()
        optimathsat.msat_set_option(cfg, "model_generation", "true")
        #self.stream.write('(set-option :print-success false)\n(set-option :produce-models true)\n')
        self.env = optimathsat.msat_create_opt_env(cfg)
        self.int_tp = optimathsat.msat_get_integer_type(self.env)
        self.bool_tp = optimathsat.msat_get_bool_type(self.env)
        self.ord = defaultdict(dict)
        self.arc = defaultdict(dict)
        self.weight = defaultdict(dict)
        self.allowed = defaultdict(dict)
        self.ovars = []

    def _add_var(self, name, is_bool=True):
        self.ovars.append((name, optimathsat.msat_declare_function(self.env, name, self.bool_tp if is_bool else self.int_tp)))

    def _add_formula(self, formula):
        clause = optimathsat.msat_from_string(self.env, formula)
        optimathsat.msat_assert_formula(self.env, clause)

    def prepare_vars(self):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # ordering
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                self._add_var(f"ord_{i}_{j}")
                self.ord[i][j] = f"ord_{i}_{j}"
                self.ord[j][i] = f"(not ord_{i}_{j})"

        # arcs
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    # declare arc_ij variables
                    self._add_var(f"arc_{i}_{j}")
                    self.arc[i][j] = f"arc_{i}_{j}"

        # weights
        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                self._add_var(f"weight_{j}_e{ej}", is_bool=False)
                self.weight[j][ej] = f"weight_{j}_e{ej}"
                # Worse, keep encoding below
                # self.stream.write("(assert (or (= weight_{i}_e{ej} 0) (= weight_{i}_e{ej} 1)))\n".format(i=j, ej=ej))
                self._add_formula(f"(<= weight_{j}_e{ej} 1)")
                self._add_formula(f"(>= weight_{j}_e{ej} 0)")

    def add_clause(self, *C):
        self._add_formula("(or %s)" % (' '.join(C)))

    # prepare variables
    def fractional_counters(self):
        n = self.hypergraph.number_of_nodes()

        for j in range(1, n + 1):
            weights = []
            for e in self.hypergraph.edges():
                assert (e > 0)
                weights.append(self.weight[j][e])

            weights = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
            self._add_formula("(<= {weights} m)".format(weights=weights))

            # set optimization variable or value for SAT check

    def elimination_ordering(self, n):
        # Some improvements
        for i in range(1, n + 1):
            for j in range(i+1, n + 1):
                # Arcs cannot go in both directions
                self.add_clause(neg(self.arc[j][i]), neg(self.arc[i][j]))
                # Enforce arc direction from smaller to bigger ordered vertex
                self.add_clause(neg(self.ord[i][j]), neg(self.arc[j][i]))
                self.add_clause(neg(self.ord[j][i]), neg(self.arc[i][j]))

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.add_clause(neg(self.ord[i][j]), neg(self.arc[j][i]))

                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue
                    self.add_clause(neg(self.ord[i][j]), neg(self.ord[j][k]), self.ord[i][k])

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    # AS CLAUSE
                    self.add_clause(neg(self.ord[i][j]), self.arc[i][j])
                    self.add_clause(neg(self.ord[j][i]), self.arc[j][i])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for k in range(j + 1, n + 1):
                    if i == k or j == k:
                        continue

                    # AS CLAUSE
                    # These two clauses are entailed by the improvement clauses and the next clause
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    self.add_clause(neg(self.arc[i][j]), neg(self.arc[i][k]), self.arc[j][k], self.arc[k][j])

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:
        for i in range(1, n + 1):
            # arc_ij then i most be covered by some edge (because i will end up in one bag)
            weights = []
            for e in self.hypergraph.incident_edges(i):
                weights.append(self.weight[i][e])

            summed = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
            compared = f"(>= {summed} 1)"

            self.add_clause(compared)

            for j in range(1, n + 1):
                if i == j:
                    continue

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append(self.weight[i][e])

                summed = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]
                compared = f"(>= {summed} 1)"

                self.add_clause(neg(self.arc[i][j]), compared)

    def break_clique(self, clique):
        if clique:
            # Vertices not in the clique are ordered before the clique
            for i in self.hypergraph.nodes():
                if i in clique:
                    continue
                for j in clique:
                    self.add_clause(self.ord[i][j])

            # Vertices of the clique are ordered lexicographically
            for i in clique:
                for j in clique:
                    if i != j:
                        if i < j:
                            self.add_clause(self.ord[i][j])

    def encode(self, clique=None, htd=True):
        n = self.hypergraph.number_of_nodes()

        self.break_clique(clique=clique)
        self.elimination_ordering(n)
        self.cover(n)

        if htd:
            self.encode_htd(n)

    def solve(self, clique=None, htd=True, lb=None, ub=None, fix_val=None):
        self._add_var("m", is_bool=False)
        self._add_formula("(>= m 1)")

        if fix_val:
            self._add_formula(f"(= m {fix_val})")
        else:
            if ub:
                self._add_formula(f"(<= m {ub})")
            if lb:
                self._add_formula(f"(>= m {lb})")

        self.prepare_vars()

        self.encode(clique=clique, htd=htd)

        self.fractional_counters()

        m_obj = optimathsat.msat_make_minimize(self.env, optimathsat.msat_from_string(self.env, "m"))
        optimathsat.msat_assert_objective(self.env, m_obj)
        res = optimathsat.msat_solve(self.env)
        assert (res == optimathsat.MSAT_SAT)

        return self.decode(htd)

    def decode(self, htd):
        model = {}
        for vn, cn in self.ovars:
            cval = optimathsat.msat_get_model_value(self.env, optimathsat.msat_from_string(self.env, vn))
            try:
                model[vn] = int(f"{cval}")
            except ValueError:
                model[vn] = f"{cval}".find("true") > 0

        try:
            ordering = self._get_ordering(model)
            weights = self._get_weights(model, ordering)
            arcs = self._get_arcs(model)

            htdd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                        weights=weights)

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

                            # We know that every bag on the bath from n to d is a subset of d
                            htdd.bags[c_node].update(htdd.bags[d])

            return DecompositionResult(htdd.width(), htdd, arcs, ordering, weights)
        except RuntimeError:
            pass

        return None

    def _get_ordering(self, model):
        ordering = []
        for i in range(1, self.hypergraph.number_of_nodes() + 1):
            pos = 0
            for j in ordering:
                # We know j is smaller due to range processing
                if not model[self.ord[j][i]]:
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
                ret[i][e] = model[self.weight[i][e]]

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
            ret[i][i] = False
            for j in range(1, n+1):
                if i != j:
                    ret[i][j] = model[self.arc[i][j]]

        return ret

    def encode_htd(self, n):
        # # Whenever a tree node covers an edge, it covers all of the edge's vertices
        for i in range(1, n+1):
            for j in range(1, n+1):
                if i != j:
                    self._add_var(f"allowed_{i}_{j}")
                    self.allowed[i][j] = f"allowed_{i}_{j}"

        for i in range(1, n+1):
            for j in range(1, n+1):
                if i == j:
                    continue

                # These clauses are not strictly necessary, but makes the solving faster
                self.add_clause(neg(self.ord[i][j]), self.allowed[j][i])

                # Enforce subsets in arc-successors
                for e in self.hypergraph.edges():
                    # = 1 is superior to > 0. = 0 and = 1 (i.e. express it as or vs. =>) does have an impact on performance
                    # none is superior, it depends on the instance...
                    # TODO: This is a hack, but it is faster than using a clause...
                    self._add_formula(f"(=> (and {self.arc[i][j]} {self.allowed[i][j]} (= {self.weight[i][e]} 1)) (= {self.weight[j][e]} 1))")

                for k in range(1, n+1):
                    if j == k or i == k:
                        continue

                    # Subset condition must hold along the whole arc-path
                    self.add_clause(neg(self.arc[j][k]), self.allowed[i][j], neg(self.allowed[i][k]))
                    # Arc-paths are only possible among successors of i, if farther away -> forbidden
                    self.add_clause(neg(self.arc[i][j]), neg(self.arc[j][k]), self.arc[i][k], neg(self.allowed[i][k]))

            for e in self.hypergraph.incident_edges(i):
                for j in range(1, n + 1):
                    if i != j:
                        self.add_clause(self.allowed[i][j], f"(= {self.weight[j][e]} 0)")