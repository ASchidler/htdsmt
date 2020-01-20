import sys
import os
from collections import defaultdict

path = sys.argv[1]
output_path = sys.argv[2]

ratios = ["05", "10", "20", "30"]
heuristics = [
        "oblivious_g",
        "oblivious_b",
        "cfirst_g",
        "cfirst_b",
        "clast_g",
        "clast_b"
    ]
heuristics.sort()

def vts(val):
    return "{}".format(val) if val is not None and val != sys.maxsize else ""


class TypeResult:
    def __init__(self):
        self.results = [None for _ in ratios]


instance_results = defaultdict(TypeResult)

for r, d, f in os.walk(path):
    for file in f:
        # Only out files contain results
        if not file.endswith(".heuristic"):
            continue

        f_param = file.split('.')
        ratio = f_param[-2]

        instance_name = ".".join(f_param[0:-2])
        instance_obj = instance_results[instance_name]
        run_result = instance_results[instance_name].results[ratios.index(ratio)]

        with open(os.path.join(r, file), "r") as cf:
            for i, line in enumerate(cf):
                vals = line.split(";")
                if len(vals) == len(heuristics) * 2 + 2:
                    instance_results[instance_name].results[ratios.index(ratio)] = line.strip()
                break

with open(output_path, "w+") as op:
    op.write("instance")
    # Write header
    for rt in ratios:
        op.write(f";{rt}% overall min width;{rt}% overall min c")
        for h in heuristics:
            op.write(f";{rt}% {h} min width;{rt}% {h} min c")
    op.write(os.linesep)

    # Write results
    for instance, results in instance_results.items():
        op.write(instance)

        for rr in results.results:
            if rr is None:
                op.write(";;")
                for _ in heuristics:
                    op.write(";;")
            else:
                op.write(";")
                op.write(rr.replace(";{}".format(sys.maxsize), ";"))
        op.write(os.linesep)
