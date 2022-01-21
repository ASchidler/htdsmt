from itertools import combinations
from pysat.formula import IDPool, CNF, WCNF
from pysat.card import ITotalizer, CardEnc, EncType
from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from decomposition_result import DecompositionResult
from functools import cmp_to_key
import networkx as nx
import subprocess
from os import getpid, path, remove

class HtdSatEncoding:
    def __init__(self, hypergraph):
        self.varcount = 0
        self.varmap = {}
        self.varrevmap = {}
        self.hypergraph = hypergraph
        self.formula = CNF()
        self.pool = IDPool()
        #self.log_file = open("sat_encoding.log", "w")

        n = self.hypergraph.number_of_nodes()

        self.arc = {i: {} for i in range(0, n+1)}
        self.ord = {i: {} for i in range(0, n+1)}
        self.weight = {i: {} for i in range(0, n+1)}
        self.allowed = {i: {} for i in range(0, n + 1)}

    def _add_clause(self, *args):
        #self.log_file.write(" ".join([f"{'-' if x < 0 else ''}{self.pool.id2obj[abs(x)]}" for x in args]) + "\n")
        self.formula.append([x for x in args])

    def _init_vars(self, htd):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # ordering
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                self.ord[i][j] = self.pool.id(f"ord{i}_{j}")
                self.ord[j][i] = -1 * self.ord[i][j]

        # arcs
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    # declare arc_ij variables
                    self.arc[i][j] = self.pool.id(f"arc{i}_{j}")

        # weights
        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                self.weight[j][ej] = self.pool.id(f"weight{j}_{ej}")

        if htd:
            for i in range(1, n + 1):
                for j in range(1, n + 1):
                    if i == j:
                        continue

                    self.allowed[i][j] = self.pool.id(f"allowed{i}_{j}")

    def elimination_ordering(self):
        n = self.hypergraph.number_of_nodes()
        #
        # # Some improvements
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                # Arcs cannot go in both directions
                self._add_clause(-self.arc[j][i], -self.arc[i][j])
                # Enforce arc direction from smaller to bigger ordered vertex
                self._add_clause(-self.ord[i][j], -self.arc[j][i])
                self._add_clause(-self.ord[j][i], -self.arc[i][j])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                for ln in range(1, n + 1):
                    if i == ln or j == ln:
                        continue

                    self._add_clause(-self.ord[i][j], -self.ord[j][ln], self.ord[i][ln])
                    self._add_clause(-self.arc[i][j], -self.arc[i][ln], self.arc[j][ln], self.arc[ln][j])

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    self._add_clause(-self.ord[i][j], self.arc[i][j])
                    self._add_clause(-self.ord[j][i], self.arc[j][i])

    def cover(self):
        n = self.hypergraph.number_of_nodes()

        # If a vertex j is in the bag, it must be covered:
        for i in range(1, n + 1):
            # arc_ij then i most be covered by some edge (because i will end up in one bag)
            weights = []
            for e in self.hypergraph.incident_edges(i):
                weights.append(self.weight[i][e])

            self._add_clause(*weights)

            for j in range(1, n + 1):
                if i == j:
                    continue

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = [-self.arc[i][j]]
                for e in self.hypergraph.incident_edges(j):
                    weights.append(self.weight[i][e])

                self._add_clause(*weights)

    def encode_htd(self):
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n+1):
            for j in range(1, n+1):
                if i == j:
                    continue

                # This clause is not required, but may speed things up (?) -- Not
                self._add_clause(-self.ord[i][j], self.allowed[j][i])

                for e in self.hypergraph.edges():
                    self._add_clause(-self.arc[i][j], -self.allowed[i][j], -self.weight[i][e], self.weight[j][e])

                for k in range(1, n+1):
                    if j == k or i == k:
                        continue

                    self._add_clause(-self.arc[j][k], self.allowed[i][j], -self.allowed[i][k])
                    self._add_clause(-self.arc[i][j], -self.arc[j][k], self.arc[i][k], -self.allowed[i][k])

                for e in self.hypergraph.incident_edges(i):
                    self._add_clause(self.allowed[i][j], -self.weight[j][e])

    def _encode_cardinality(self, ub, m, n):
        tots = []
        for i in range(1, n+1):
            lits = [self.weight[i][ej] for ej in range(1, m+1)]
            ubound = min(len(lits)-1, ub)

            tots.append(ITotalizer(lits=lits, ubound=ubound, top_id=self.pool.id(f"totalizer{i}")))
            self.pool.occupy(self.pool.top - 1, tots[-1].top_id)
            self.formula.extend(tots[-1].cnf)

        return tots

    def _symmetry_breaking(self, n):
        ls = {x: self.pool.id(f"ls{x}") for x in range(1, n+1)}
        s = {x: {} for x in range(1, n+1)}
        for v in s.keys():
            s[v] = {x: self.pool.id(f"s{v}_{x}") for x in range(1, n+1) if v != x}

        self.formula.extend(CardEnc.atmost(ls.values(), vpool=self.pool))

        for i in range(1, n+1):
            for j in range(i+1, n+1):
                for k in range(1, n+1):
                    if i != k and j != k:
                        self.formula.append([self.ord[j][i], self.ord[k][j], -s[i][k]])

        for i in range(1, n+1):
            clause = [ls[i]]
            nbs = self.hypergraph.adjByNode(i, strict=True).keys()

            for j in nbs:
                clause.append(s[i][j])
                for k in nbs:
                    if j != k:
                        self.formula.append([-self.ord[j][k], -s[i][k]])

            self.formula.append(clause)

    def solve(self, ub, htd, solver, incremental=True, enc_type=EncType.totalizer, sb=False, clique=None, maxsat=False, tmpdir=None):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()
        self._init_vars(htd)

        # Create Encoding
        self.break_clique(clique, htd)
        self.elimination_ordering()
        self.cover()
        if sb:
            self._symmetry_breaking(n)
        if htd:
            self.encode_htd()

        if ub > m:
            ub = m

        c_bound = ub
        increase = False
        c_lb = 0

        # TODO: Once we have solved the formula once, assumptions can be added as clauses
        if incremental:
            tots = self._encode_cardinality(ub, m, n)
            with solver() as slv:
                slv.append_formula(self.formula)

                while c_lb < ub:
                    if increase:
                        for c_tot in tots:
                            c_tot.increase(ubound=c_bound, top_id=self.pool.id(f"tots_{self.pool.top}"))
                            slv.append_formula(c_tot.cnf.clauses[-c_tot.nof_new:])
                            self.pool.occupy(self.pool.top - 1, tots[-1].top_id)

                    assps = [-t.rhs[c_bound] for t in tots if c_bound < len(t.lits)]
                    if slv.solve(assumptions=assps):
                        ub = c_bound
                        c_bound -= 1
                        best_model = self.decode(slv.get_model(), htd, m, n)
                    else:
                        c_lb = c_bound + 1
                        c_bound += 1
                        increase = True
                return best_model
        elif not maxsat:
            best_model = None

            while c_lb < ub:
                with solver() as slv:
                    slv.append_formula(self.formula)
                    c_top = self.pool.top
                    for i in range(1, n + 1):
                        lits = [self.weight[i][ej] for ej in range(1, m + 1)]

                        constr = CardEnc.atmost(lits, bound=c_bound, top_id=c_top, encoding=enc_type)
                        c_top = constr.nv
                        slv.append_formula(constr)

                    if slv.solve():
                        ub = c_bound
                        c_bound -= 1
                        best_model = self.decode(slv.get_model(), htd, m, n)
                    else:
                        c_lb = c_bound + 1
                        c_bound += 1
            return best_model
        else:
            # TODO: Case when UB is not a ubound for ghtw...
            # Maxsat
            ub = min(ub, m-1)
            tots = self._encode_cardinality(ub, m, n)
            maxsat_clauses = WCNF()
            for x in range(1, ub+1):
                var = self.pool.id(f"cards_{x}")
                maxsat_clauses.append([var], weight=1)
                c_clause = []
                for t in tots:
                    maxsat_clauses.append([-var, -t.rhs[x]])
                    c_clause.append(t.rhs[x])
            maxsat_clauses.extend(self.formula)

            enc_file = path.join(tmpdir, f"{getpid()}.cnf")
            maxsat_clauses.to_file(enc_file)

            #p = subprocess.Popen(["bin/uwrmaxsat", "-m", enc_file], stdout=subprocess.PIPE)
            p = subprocess.Popen(["bin/maxhs", "-no-printSoln-new-format", "-printBstSoln", "-printSoln", enc_file],
                                 stdout=subprocess.PIPE)
            r = p.communicate()[0].decode("utf-8")
            for cline in r.splitlines():
                if cline.startswith("v"):
                    # Uwrmaxsat
                    model = [int(x.replace("x", "")) for x in cline.split()[1:]]
                    # # MaxHS
                    # model = [(ix+1) * (1 if int(x) > 0 else - 1) for ix, x in enumerate(cline[1:].strip())]
                    return self.decode(model, htd, m, n)

    def decode(self, model, htd, m, n):
        model = {abs(x): x > 0 for x in model}
        ordering = list(range(1, n + 1))

        def find_ord(x, y):
            if x < y:
                return -1 if model[self.ord[x][y]] else 1
            else:
                return 1 if model[self.ord[y][x]] else -1
        ordering.sort(key=cmp_to_key(find_ord))

        weights = {x: {ej: 1 if model[self.weight[x][ej]] else 0 for ej in range(1, m+1)} for x in range(1, n+1)}
        arcs = {x: {y: model[self.arc[x][y]] for y in range(1, n+1) if x != y} for x in range(1, n+1)}

        htdd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                    weights=weights)

        if htd:
            for i in range(1, self.hypergraph.number_of_nodes() + 1):
                for j in range(1, self.hypergraph.number_of_nodes() + 1):
                    if i != j and arcs[i][j]:
                        htdd.bags[i].add(j)

            htdd.tree = nx.DiGraph()
            for i in range(0, len(ordering)):
                n = ordering[i]
                for j in range(i + 1, len(ordering)):
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

    def break_clique(self, clique, htd):
        if clique:
            if htd:
                smallest = min(clique)
                largest = max(clique)
                # Vertices are either completely before or after the clique
                for i in self.hypergraph.nodes():
                    if i in clique:
                        continue
                    self._add_clause(self.ord[i][smallest], self.ord[largest][i])
            else:
                # Vertices not in the clique are ordered before the clique
                for i in self.hypergraph.nodes():
                    if i in clique:
                        continue
                    for j in clique:
                        self._add_clause(self.ord[i][j])

            # Vertices of the clique are ordered lexicographically
            for i in clique:
                for j in clique:
                    if i < j:
                        self._add_clause(self.ord[i][j])
