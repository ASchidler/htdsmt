import os


class OpbFile:
    def __init__(self):
        self.clauses = []
        self.constraints = []
        self.variables = set()
        self.tmp_len = None
        self.minimize = None
        self.opt_target = None

    def append(self, literals, geq, degree):
        for cc in literals:
            self.variables.add(abs(cc[1]))

        self.constraints.append([literals, geq, degree])

    def append_clause(self, clause):
        literals = []
        for cl in clause:
            literals.append((1, cl))

        self.constraints.append([literals, True, 1])

    def to_file(self, path):
        with open(path, "w") as f:
            f.write(f"* #variable= {len(self.variables)} #constraint= {len(self.constraints)}"+os.linesep)

            if self.opt_target:
                f.write(f"{'min: ' if self.minimize else 'max: '}")
                for lit in self.opt_target:
                    f.write(f"{'1' if lit[0] > 0 else lit[0]} ")
                    if lit[1] > 0:
                        f.write(f"x{lit[1]} ")
                    else:
                        f.write(f"~x{abs(lit[1])} ")
                f.write(";" + os.linesep)

            for cc in self.constraints:
                for lit in cc[0]:
                    f.write(f"{'+1' if lit[0] > 0 else lit[0]} ")
                    if lit[1] > 0:
                        f.write(f"x{lit[1]} ")
                    else:
                        f.write(f"~x{abs(lit[1])} ")

                f.write(f"{'>= ' if cc[1] else '= '}")
                f.write(f"{cc[2]}" + os.linesep)

    def add_temporary(self, literals, geq, degree):
        if self.tmp_len is None:
            self.tmp_len = len(self.constraints)
        self.append(literals, geq, degree)

    def clear_temporary(self):
        if self.tmp_len is not None:
            while len(self.constraints) > self.tmp_len:
                self.constraints.pop()
            self.tmp_len = None

    def optimize(self, minimize, target):
        self.minimize = minimize
        self.opt_target = target
