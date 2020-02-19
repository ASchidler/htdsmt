from itertools import combinations

class HtdSatEncoding:
    def __init__(self, stream, hypergraph):
        self.varcount = 0
        self.varmap = {}
        self.varrevmap = {}
        self.stream = stream
        self.clausecount = 0
        self.hypergraph = hypergraph

        n = self.hypergraph.number_of_nodes()

        self.arc = {i: {} for i in range(0, n+1)}
        self.ord = {i: {} for i in range(0, n+1)}
        self.weight = {i: {} for i in range(0, n+1)}
        self.forbidden = {i: {} for i in range(0, n + 1)}
        self.subset = {i: {} for i in range(0, n + 1)}

    def _add_clause(self, *args):
        self.stream.write(' '.join([str(x) for x in args]))
        self.stream.write(" 0\n")
        self.clausecount += 1

    def _add_var(self):
        self.varcount += 1
        return self.varcount

    def _init_vars(self, htd):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # ordering
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                self.ord[i][j] = self._add_var()
                self.ord[j][i] = -1 * self.ord[i][j]

        # arcs
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # declare arc_ij variables
                self.arc[i][j] = self._add_var()

        # weights
        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                self.weight[j][ej] = self._add_var()

        if htd:
            for i in range(1, n + 1):
                incident = set()
                for e in self.hypergraph.incident_edges(i):
                    incident.update(self.hypergraph.get_edge(e))
                incident.remove(i)

                for j in incident:
                    self.subset[i][j] = self._add_var()

                for j in range(1, n + 1):
                    if i == j:
                        continue
                    self.forbidden[i][j] = self._add_var()

    def elimination_ordering(self):
        n = self.hypergraph.number_of_nodes()

        # Some improvements
        # for i in range(1, n + 1):
        #     for j in range(i + 1, n + 1):
        #         # Arcs cannot go in both directions
        #         self._add_clause(-self.arc[j][i], -self.arc[i][j])
        #         # Enforce arc direction from smaller to bigger ordered vertex
        #         self._add_clause(-self.ord[i][j], -self.arc[j][i])
        #         self._add_clause(self.ord[i][j], -self.arc[i][j])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self._add_clause(-self.ord[i][j], -self.arc[j][i])

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
                    self._add_clause(self.ord[i][j], self.arc[j][i])
                    self._add_clause(-self.ord[i][j], self.arc[i][j])

        # forbid self loops
        for i in range(1, n + 1):
            self._add_clause(-self.arc[i][i])

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
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append(self.weight[i][e])

                weights.append(-self.arc[i][j])
                self._add_clause(*weights)

    def encode_htd(self):
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n+1):
            incident = set()
            for e in self.hypergraph.incident_edges(i):
                incident.update(self.hypergraph.get_edge(e))
            incident.remove(i)
            for j in incident:
                if i == j:
                    continue

                self._add_clause(-self.subset[j][i], self.arc[i][j])

                for e in self.hypergraph.edges():
                    # = 1 is superior to > 0. Keeping these two clauses separate is faster than (= w1 w2)
                    # The first clause follows by optimality... Grants a great speedup...
                    # self.stream.write(f"(assert (=> (and subset_{i}_{j} (= weight_{j}_e{e} 0)) (= weight_{i}_e{e} 0)))\n")
                    self._add_clause(-self.subset[i][j], -self.weight[j][e], self.weight[i][e])

                for k in incident:
                    if k == i or k == j:
                        continue
                    self._add_clause(-self.arc[i][k], self.arc[j][k], -self.subset[i][j])
                    self._add_clause(-self.arc[i][j], -self.arc[j][k], -self.subset[k][i], self.subset[j][i])

        for i in range(1, n + 1):
            incident = set()
            for e in self.hypergraph.incident_edges(i):
                incident.update(self.hypergraph.get_edge(e))
            incident.remove(i)

            for j in range(1, n + 1):
                if i == j:
                    continue

                if j not in incident:
                    self._add_clause(-self.arc[i][j], self.forbidden[i][j])

                    for k in range(1, n + 1):
                        if j == k or i == k:
                            continue

                        self._add_clause(-self.arc[i][k], -self.ord[k][j], self.forbidden[i][j])
                else:
                    # TODO: This is for some reason faster than directly setting weight. Change this for SAT!
                    self._add_clause(-self.arc[i][j], self.subset[j][i], self.forbidden[i][j])

                for e in self.hypergraph.incident_edges(i):
                    self._add_clause(-self.forbidden[i][j], -self.weight[j][e])

    def _encode_cardinality(self, bound):
        """Enforces cardinality constraints. Cardinality of 2-D structure variables must not exceed bound"""
        # Counter works like this: ctr[i][j][0] states that an arc from i to j exists
        # These are then summed up incrementally edge by edge

        m = self.hypergraph.num_hyperedges()
        n = self.hypergraph.number_of_nodes()

        # Define counter variables ctr[i][j][l] with 1 <= i <= n, 1 <= j < n, 1 <= l <= min(j, bound)
        ctr = [[[self._add_var()
                 for _ in range(0, min(j, bound))]
                # j has range 0 to n-1. use 1 to n, otherwise the innermost number of elements is wrong
                for j in range(1, m)]
               for _ in range(0, n)]

        for i in range(0, n):
            for j in range(1, m - 1):
                # Ensure that the counter never decrements, i.e. ensure carry over
                for ln in range(0, min(len(ctr[i][j - 1]), bound)):
                    self._add_clause(-ctr[i][j - 1][ln], ctr[i][j][ln])

                # Increment counter for each arc
                for ln in range(1, min(len(ctr[i][j]), bound)):
                    self._add_clause(-self.weight[i+1][j+1], -ctr[i][j - 1][ln - 1], ctr[i][j][ln])

        # Ensure that counter is initialized on the first arc
        for i in range(0, n):
            for j in range(0, m - 1):
                self._add_clause(-self.weight[i+1][j+1], ctr[i][j][0])

        # Conflict if target is exceeded
        for i in range(0, n):
            for j in range(bound, m):
                # Since we start to count from 0, bound - 2
                self._add_clause(-self.weight[i+1][j+1], -ctr[i][j - 1][bound - 1])

    def encode(self, ub, htd):
        self._init_vars(htd)
        self.elimination_ordering()
        self.cover()
        if htd:
            self.encode_htd()
        self._encode_cardinality(ub)

    def decode(self, inp):
        is_unsat = inp.readline().lower().startswith("unsat")
        if is_unsat:
            return None

        # We could also filter only interesting vars, if necessary
        # We could also make this a list...
        model = {}
        buffer = []

        def buffer_val():
            val = int(''.join(buffer))
            if val < 0:
                model[-1 * val] = False
            else:
                model[val] = True

        while inp.readable():
            cc = inp.read(1)
            if cc == ' ':
                buffer_val()
                buffer.clear()
            elif cc == "":
                break
            else:
                buffer.append(cc)
        buffer_val()

        # Find weight
        width = 0

        for j in range(1, self.hypergraph.number_of_nodes() + 1):
            cwidth = 0
            for ej in range(1, self.hypergraph.number_of_edges() + 1):
                if model[self.weight[j][ej]]:
                    cwidth += 1
            width = max(width, cwidth)

        return width
