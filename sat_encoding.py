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
        self.allowed = {i: {} for i in range(0, n + 1)}

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

                for j in range(1, n + 1):
                    if i == j:
                        continue

                    self.allowed[i][j] = self._add_var()

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
                self._add_clause(self.ord[i][j], -self.arc[i][j])

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

                # This clause is not required, but may speed things up (?)
                self._add_clause(-self.ord[i][j], self.allowed[j][i])

                for e in self.hypergraph.edges():
                    self._add_clause(-self.arc[i][j], -self.allowed[i][j], -self.weight[i][e], self.weight[j][e])

                for k in range(1, n+1):
                    if k == i or k == j:
                        continue
                    self._add_clause(-self.arc[j][k], self.allowed[i][j], -self.allowed[i][k])
                    self._add_clause(-self.arc[i][j], -self.arc[j][k], self.arc[i][k], -self.allowed[i][k])

                for e in self.hypergraph.incident_edges(i):
                    self._add_clause(self.allowed[i][j], -self.weight[j][e])

    def _encode_cardinality(self, bound):
        """Enforces cardinality constraints. Cardinality of 2-D structure variables must not exceed bound"""
        # Counter works like this: ctr[i][j][0] states that an arc from i to j exists
        # These are then summed up incrementally edge by edge

        m = self.hypergraph.num_hyperedges()
        n = self.hypergraph.number_of_nodes()

        ctr = [[[self._add_var()
                 for _ in range(0, min(j, bound))]
                # j has range 0 to n-1. use 1 to n, otherwise the innermost number of elements is wrong
                for j in range(1, m)]
               for _ in range(0, n)]

        # Note that these vars are 0 based, while weight is 1 based, so add 1 to all indices when using weight
        for i in range(0, n):
            for j in range(1, m - 1):
                # Ensure that the counter never decrements, i.e. ensure carry over
                for ln in range(0, min(len(ctr[i][j - 1]), bound)):
                    self._add_clause(-ctr[i][j - 1][ln],  ctr[i][j][ln])
                    #self._add_clause( ctr[i][j - 1][ln], -ctr[i][j][ln], self.weight[i + 1][j + 1])

                # Increment counter for each arc
                for ln in range(1, min(len(ctr[i][j]), bound)):
                    self._add_clause(-ctr[i][j - 1][ln - 1],  ctr[i][j][ln], -self.weight[i+1][j+1])
                    #self._add_clause( ctr[i][j - 1][ln - 1], -ctr[i][j][ln])

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
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()
        self._init_vars(htd)

        # Write header placeholder
        estimated_vars = (1 + ub) * self.varcount
        # This is way too much, but better too many than too few: m * n^4 * 100
        estimated_clauses = 100 * m * n * n * n * n
        placeholder = f"p cnf {estimated_vars} {estimated_clauses}"
        self.stream.write(placeholder)
        self.stream.write("\n")

        # Create Encoding
        self.elimination_ordering()
        if htd:
            self.encode_htd()
        self.cover()
        self._encode_cardinality(ub)
        #self.break_order_symmetry()
        # Fill in correct header
        self.stream.seek(0)
        real_header = f"p cnf {self.varcount} {self.clausecount}"
        self.stream.seek(0)
        self.stream.write(real_header)
        for _ in range(len(real_header), len(placeholder)):
            self.stream.write(" ")

    def decode(self, inp):
        first_line = inp.readline().lower()
        is_unsat = first_line.startswith("unsat") or first_line.startswith("s unsat")

        if is_unsat:
            return None

        # glucose does not write sat/unsat in the first line... first char could also be a -, so check first and second
        if first_line[0].isdigit() or first_line[1].isdigit():
            inp.seek(0)

        # We could also filter only interesting vars, if necessary
        # We could also make this a list...
        model = {}
        buffer = []

        def buffer_val():
            str_val = ''.join(buffer)
            if str_val.strip() != "":
                val = int(str_val)
                if val < 0:
                    model[-1 * val] = False
                else:
                    model[val] = True

        while inp.readable():
            cc = inp.read(1)
            if cc == ' ' or cc == "\n":
                buffer_val()
                buffer.clear()
            elif cc == "v":
                pass
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

    def break_order_symmetry(self):
        n = self.hypergraph.number_of_nodes()

        def tord(ix, jx):
            return 'ord_{}_{}'.format(ix, jx) if ix < jx else '(not ord_{}_{})'.format(jx, ix)

        block = [None for _ in range(0, n+1)]
        for i in range(1, n+1):
            d = dict()
            block[i] = d
            for j in range(i+1, n+1):
                d[j] = [None for _ in range(0, n + 1)]
                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue
                    d[j][k] = self._add_var()

        for i in range(1, n+1):
            for j in range(i+1, n+1):
                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    self._add_clause(-self.ord[j][k], -self.arc[k][i], block[i][j][k])
                    self._add_clause(-block[i][j][k], self.ord[j][k])
                    self._add_clause(-block[i][j][k], self.arc[k][i])
                    # self.stream.write(
                    #     f"(assert (or (not {tord(j, k)}) (not arc_{k}_{i}) block_{i}_{j}_{k}))\n"
                    # )
                    # self.stream.write(
                    #     "(assert (or (not block_{i}_{j}_{k}) {ord}))\n"
                    #         .format(i=i, j=j, k=k, ord=tord(j, k)))
                    #
                    # self.stream.write(
                    #     "(assert (or (not block_{i}_{j}_{k}) arc_{k}_{i}))\n"
                    #         .format(i=i, j=j, k=k))
