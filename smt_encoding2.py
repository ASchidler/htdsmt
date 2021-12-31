from __future__ import absolute_import
from functools import cmp_to_key
import re
from itertools import combinations
from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from decomposition_result import DecompositionResult
from bounds import upper_bounds
import networkx as nx
from collections import defaultdict
import lib.optimathsat as optimathsat
import z3


class HtdSmtEncoding:
    def __init__(self, hypergraph, use_z3=False):
        self.hypergraph = hypergraph
        self.use_z3 = use_z3
        if use_z3:
            self.z3_solver = z3.Optimize()
        else:
            cfg = optimathsat.msat_create_config()
            optimathsat.msat_set_option(cfg, "model_generation", "true")
            self.env = optimathsat.msat_create_opt_env(cfg)
            self.int_tp = optimathsat.msat_get_integer_type(self.env)
            self.bool_tp = optimathsat.msat_get_bool_type(self.env)

        self.m = None
        self.ord = defaultdict(dict)
        self.arc = defaultdict(dict)
        self.weight = defaultdict(dict)
        self.eq = defaultdict(dict)
        self.arcp = defaultdict(dict)
        self.ovars = []
        # self.log = open("smt_encoding.log", "w")

    def _neg(self, var):
        if self.use_z3:
            return z3.Not(var)
        else:
            if var.startswith("(not "):
                return var[4:-1]
            else:
                return f"(not {var})"

    def _add_var(self, name, is_bool=True):
        if not self.use_z3:
            optimathsat.msat_declare_function(self.env, name, self.bool_tp if is_bool else self.int_tp)
            self.ovars.append(name)
            return name
        else:
            if not is_bool:
                return z3.Int(name)
            else:
                return z3.Bool(name)

    def _add_formula(self, formula):
        if not self.use_z3:
            clause = optimathsat.msat_from_string(self.env, formula)
            assert (not optimathsat.MSAT_ERROR_TERM(clause))
            optimathsat.msat_assert_formula(self.env, clause)
        else:
            self.z3_solver.add(formula)

        # This converst the SMT encoding into the same format as the SAT encoding, for comparison
        # if self.log:
        #     formula = formula.replace("_e", "_")
        #     m = re.search("\(not ([a-zA-Z_0-9)]*)\)", formula)
        #     while m is not None:
        #         formula = formula.replace(m.group(0), f"-{m.group(1)}")
        #         m = re.search("\(not ([a-zA-Z_0-9)]*)\)", formula)
        #     m = re.search("\(= ([a-zA-Z_0-9\- ]*) 1\)", formula)
        #     while m is not None:
        #         formula = formula.replace(m.group(0), f"{m.group(1)}")
        #         m = re.search("\(= ([a-zA-Z_0-9\- ]*) 1\)", formula)
        #     m = re.search("\(= ([a-zA-Z_0-9\- ]*) 0\)", formula)
        #     while m is not None:
        #         formula = formula.replace(m.group(0), f"-{m.group(1)}")
        #         m = re.search("\(= ([a-zA-Z_0-9\- ]*) 0\)", formula)
        #     m = re.search("\(>= \(\+ ([a-zA-Z_0-9\- ]*)\) 1\)", formula)
        #     if m is not None:
        #         formula = formula.replace(m.group(0), m.group(1))
        #     m = re.search("\(>= ([a-zA-Z_0-9\- ]*) 1\)", formula)
        #     if m is not None:
        #         formula = formula.replace(m.group(0), m.group(1))
        #     m = re.search("\(or ([a-zA-Z_0-9\- ]*)\)", formula)
        #     while m is not None:
        #         formula = formula.replace(m.group(0), m.group(1))
        #         m = re.search("\(or ([a-zA-Z_0-9\- ]*)\)", formula)
        #     m = re.search("\(=> \(and ([a-zA-Z_0-9\- ]*)\) ([a-zA-Z_0-9\- ]*)\)", formula)
        #     if m is not None:
        #         changed = m.group(1).replace(" ", " -")
        #         changed = "-" + changed
        #         formula = formula.replace(m.group(0), changed + " " + m.group(2))
        #         #(=> (and arc_2_5 allowed_2_5 weight_2_1) weight_5_1)
        #     formula = formula.replace("  ", " ")
        #     formula = formula.replace("  ", " ")
        #     m = re.search("^ ", formula)
        #     if m is not None:
        #         formula = formula[1:]
        #     m = re.search("([a-z])_", formula)
        #     while m is not None:
        #         formula = formula.replace(m.group(0), m.group(1))
        #         m = re.search("([a-z])_", formula)
        #     self.log_file.write(formula + "\n")

    def prepare_vars(self, htd):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        self.m = self._add_var("m", is_bool=False)
        self._add_formula(self._create_seq(1, self.m))

        # ordering
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                self.ord[i][j] = self._add_var(f"ord_{i}_{j}")
                self.ord[j][i] = self._neg(self.ord[i][j])

        # arcs
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    # declare arc_ij variables
                    self.arc[i][j] = self._add_var(f"arc_{i}_{j}")

        # weights
        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                self.weight[j][ej] = self._add_var(f"weight_{j}_e{ej}", is_bool=False)
                # Worse, keep encoding below
                # self.stream.write("(assert (or (= weight_{i}_e{ej} 0) (= weight_{i}_e{ej} 1)))\n".format(i=j, ej=ej))
                self._add_formula(self._create_seq(self.weight[j][ej], 1))
                self._add_formula(self._create_seq(0, self.weight[j][ej]))

        if htd:
            for i in range(1, n + 1):
                for j in range(i + 1, n + 1):
                    self.eq[i][j] = self._add_var(f"eq{i}_{j}")
                    self.eq[j][i] = self._add_var(f"eq{i}_{j}")

            # arcsp
            for i in range(1, n + 1):
                for j in range(1, n + 1):
                    if i != j:
                        # declare arc_ij variables
                        self.arcp[i][j] = self._add_var(f"arcp{i}_{j}")

    def _add_clause(self, *C):
        if self.use_z3:
            self.z3_solver.add(z3.Or(C))
        else:
            self._add_formula("(or %s)" % (' '.join(C)))

    def _create_sum(self, parts):
        if self.use_z3:
            return z3.Sum(parts)
        else:
            return f"(+ {' '.join(parts)})" if len(parts) > 1 else parts[0]

    def _create_seq(self, smaller, bigger):
        if self.use_z3:
            return bigger >= smaller
        else:
            return f"(>= {bigger} {smaller})"

    def _create_atmost(self, lst, bound):
        if not self.use_z3:
            raise RuntimeError("Atmost is only supported by Z3")
        # Does not work with variables, bound needs to be a constant
        return z3.AtMost(*lst, bound)

    def encode_cardinality(self):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()
        for j in range(1, n + 1):
            weights = [self.weight[j][ej] for ej in range(1, m+1)]
            weights = self._create_sum(weights)
            self._add_formula(self._create_seq(weights, self.m))

    def elimination_ordering(self, n, htd):
        # Some improvements
        for i in range(1, n + 1):
            for j in range(i+1, n + 1):
                if not htd:
                    # Arcs cannot go in both directions
                    self._add_clause(self._neg(self.arc[j][i]), self._neg(self.arc[i][j]))
                    # Enforce arc direction from smaller to bigger ordered vertex
                    self._add_clause(self._neg(self.ord[i][j]), self._neg(self.arc[j][i]))
                    self._add_clause(self._neg(self.ord[j][i]), self._neg(self.arc[i][j]))
                else:
                    self._add_clause(self.eq[i][j], self._neg(self.arc[j][i]), self._neg(self.arc[i][j]))
                    self._add_clause(self._neg(self.ord[i][j]), self.eq[i][j], self._neg(self.arc[j][i]))
                    self._add_clause(self._neg(self.ord[j][i]), self.eq[i][j], self._neg(self.arc[i][j]))

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                for ln in range(1, n + 1):
                    if i == ln or j == ln:
                        continue
                    self._add_clause(self._neg(self.ord[i][j]), self._neg(self.ord[j][ln]), self.ord[i][ln])
                    self._add_clause(self._neg(self.arc[i][j]), self._neg(self.arc[i][ln]), self.arc[j][ln], self.arc[ln][j])

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    # AS CLAUSE
                    self._add_clause(self._neg(self.ord[i][j]), self.arc[i][j])
                    self._add_clause(self._neg(self.ord[j][i]), self.arc[j][i])

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:
        for i in range(1, n + 1):
            # arc_ij then i most be covered by some edge (because i will end up in one bag)
            weights = []
            for e in self.hypergraph.incident_edges(i):
                weights.append(self.weight[i][e])

            summed = self._create_sum(weights)
            self._add_formula(self._create_seq(1, summed))

            for j in range(1, n + 1):
                if i == j:
                    continue

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append(self.weight[i][e])

                summed = self._create_sum(weights)
                compared = self._create_seq(1, summed)
                self._add_clause(self._neg(self.arc[i][j]), compared)

    def break_clique(self, clique, htd):
        if clique:
            # Vertices not in the clique are ordered before the clique

            if htd:
                standin = next(iter(clique))

                # Vertices are either completely before or after the clique
                for i in self.hypergraph.nodes():
                    if i in clique:
                        continue

                    for j in clique:
                        if j != standin:
                            self._add_clause(self._neg(self.ord[i][standin]), self.ord[i][j])
                            self._add_clause(self.ord[i][standin], self._neg(self.ord[i][j]))
            else:
                for i in self.hypergraph.nodes():
                    if i in clique:
                        continue
                    for j in clique:
                        self._add_clause(self.ord[i][j])

                # Vertices of the clique is ordered lexicographically
                for i in clique:
                    for j in clique:
                        if i < j:
                            self._add_clause(self.ord[i][j])

    def encode(self, clique=None, htd=True):
        n = self.hypergraph.number_of_nodes()

        self.break_clique(clique=clique, htd=htd)
        self.elimination_ordering(n, htd)
        self.cover(n)

        if htd:
            self.encode_htd(n)

    def solve(self, clique=None, htd=True, lb=None, ub=None, fix_val=None, sb=False):
        self.prepare_vars(htd)

        if self.use_z3:
            if fix_val:
                self.z3_solver.add(self.m == fix_val)
            else:
                if ub:
                    self.z3_solver.add(self.m <= ub)
                if lb:
                    self.z3_solver.add(self.m >= lb)
            self.z3_solver.minimize(self.m)
        else:
            m_obj = optimathsat.msat_make_minimize(self.env, optimathsat.msat_from_string(self.env, "m"))
            optimathsat.msat_assert_objective(self.env, m_obj)
            if fix_val:
                self._add_formula(f"(= m {fix_val})")
            else:
                if ub:
                    self._add_formula(f"(<= m {ub})")
                if lb:
                    self._add_formula(f"(>= m {lb})")

        self.encode(clique=clique, htd=htd)
        if sb:
            self._symmetry_breaking(self.hypergraph.number_of_nodes())

        self.encode_cardinality()

        if self.use_z3:
            self.z3_solver.check()
        else:
            m_obj = optimathsat.msat_make_minimize(self.env, optimathsat.msat_from_string(self.env, "m"))
            optimathsat.msat_assert_objective(self.env, m_obj)
            res = optimathsat.msat_solve(self.env)
            assert (res == optimathsat.MSAT_SAT)

        return self.decode(htd)

    def _symmetry_breaking(self, n):
        ls = {x: self._add_var(f"ls{x}") for x in range(1, n+1)}
        s = {x: {} for x in range(1, n+1)}
        for v in s.keys():
            s[v] = {x: self._add_var(f"s{v}_{x}") for x in range(1, n+1) if v != x}

        # Atmost 1
        for i in range(1, n+1):
            for j in range(i+1, n+1):
                self._add_clause(self._neg(ls[i]), self._neg(ls[j]))

        for i in range(1, n+1):
            for j in range(i+1, n+1):
                for k in range(1, n+1):
                    if i != k and j != k:
                        self._add_clause(self.ord[j][i], self.ord[k][j], self._neg(s[i][k]))

        for i in range(1, n+1):
            clause = [ls[i]]
            nbs = self.hypergraph.adjByNode(i, strict=True).keys()

            for j in nbs:
                clause.append(s[i][j])
                for k in nbs:
                    if j != k:
                        self._add_clause(self.ord[k][j], self._neg(s[i][k]))

            self._add_clause(*clause)

    def decode(self, htd):
        model = {}
        if self.use_z3:
            model = self.z3_solver.model()
        else:
            for vn in self.ovars:
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
                for i in range(1, self.hypergraph.number_of_nodes() + 1):
                    for j in range(1, self.hypergraph.number_of_nodes() + 1):
                        if i != j and ordering.index(i) > ordering.index(j):
                            if arcs[i][j]:
                                htdd.bags[i].add(j)

            return DecompositionResult(htdd.width(), htdd, arcs, ordering, weights)
        except RuntimeError:
            pass

        return None

    def _get_ordering(self, model):
        ordering = list(range(1, self.hypergraph.number_of_nodes() + 1))

        def find_ord(x, y):
            if x < y:
                return -1 if model[self.ord[x][y]] else 1
            else:
                return 1 if model[self.ord[y][x]] else -1
        ordering.sort(key=cmp_to_key(find_ord))

        return ordering
    
    def _get_weights(self, model, ordering):
        ret = {}
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n + 1):
            # print 'bag %i'
            ret[i] = {}
            for e in self.hypergraph.edges():
                assert (e > 0)
                if self.use_z3:
                    ret[i][e] = model[self.weight[i][e]].as_long()
                else:
                    ret[i][e] = model[self.weight[i][e]]

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
            ret[i][i] = False
            for j in range(1, n+1):
                if i != j:
                    ret[i][j] = model[self.arc[i][j]]

        return ret

    def encode_htd(self, n):
        # # Whenever a tree node covers an edge, it covers all the edge's vertices
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    self._add_clause(self._neg(self.arc[i][j]), self.arcp[i][j])
                    for k in range(1, n + 1):
                        if i != k and j != k:
                            self._add_clause(self._neg(self.arcp[i][j]), self._neg(self.arcp[j][k]), self.arcp[i][k])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    for e in self.hypergraph.incident_edges(i):
                        self._add_clause(self._neg(self.arcp[i][j]), f"(= {self.weight[j][e]} 0)", self.eq[i][j])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    self._add_clause(self._neg(self.eq[i][j]), self.arc[i][j])

                for k in range(1, n + 1):
                    if i != j and i != k and j != k:
                        self._add_clause(self._neg(self.eq[i][j]), self._neg(self.eq[j][k]), self.eq[i][k])
                        self._add_clause(self._neg(self.eq[i][k]), self._neg(self.arcp[i][j]), self._neg(self.arcp[j][k]), self.eq[i][j])
