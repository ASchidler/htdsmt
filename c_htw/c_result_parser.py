import sys
import os
from collections import defaultdict

path = sys.argv[1]
output_path = sys.argv[2]

ratios = ["05", "10", "20", "30"]


def vts(val):
    return "{}".format(val) if val is not None else ""


class RunResult:
    def __init__(self):
        self.min_c = None
        self.max_w = None
        self.max_c = None
        self.min_w = None
        self.base_c = None


class TypeResult:
    def __init__(self):
        self.width = None
        self.results = [RunResult() for _ in ratios]


class InstanceResult:
    def __init__(self):
        self.htd = TypeResult()
        self.ghtd = TypeResult()


instance_results = defaultdict(InstanceResult)

for r, d, f in os.walk(path):
    for file in f:
        # Only out files contain results
        if not file.endswith(".result"):
            continue

        f_param = file.split('.')
        ratio = f_param[-2]
        cfirst = f_param[-3] == "c"

        instance_name = ".".join(f_param[0:-4])
        instance_obj = instance_results[instance_name].htd if f_param[-4] == "htd" \
            else instance_results[instance_name].ghtd

        run_result = instance_obj.results[ratios.index(ratio)]

        with open(os.path.join(r, file), "r") as cf:
            ln = cf.readline()
            vals = ln.split()
            if len(vals) != 8:
                continue

            c_w = int(vals[1])
            c_c = int(vals[3])
            b_w = int(vals[5])
            b_c = int(vals[7])

            if instance_obj.width is not None and instance_obj.width != b_w:
                print(f"Error: {instance_name} width was {instance_obj.width} should be set to {b_w}")
            instance_obj.width = b_w

            if run_result.base_c is not None and run_result.base_c != b_c:
                print(f"Error: {instance_name} base C was {run_result.base_c} should be set to {b_c}")
            run_result.base_c = b_c

            if cfirst:
                run_result.min_c = c_c
                run_result.max_w = c_w
            else:
                run_result.max_c = c_c
                run_result.min_w = c_w

with open(output_path, "w+") as op:
    # Write header
    op.write("instance;")

    for tp in ["htd", "ghtd"]:
        if tp == "ghtd":
            op.write(";")
        op.write(f"{tp} width")

        for rt in ratios:
            op.write(";{tp} {rt}% obl c;{tp} {rt}% min c;{tp} {rt}% max c;{tp} {rt}% max width".format(tp=tp, rt=rt))
    op.write(os.linesep)

    # Write results
    for instance, results in instance_results.items():
        op.write(instance + ";")
        for i in range(0, 2):
            obj = results.htd if i == 0 else results.ghtd
            if i > 0:
                op.write(";")
            op.write(f"{vts(obj.width)}")

            for rr in obj.results:
                if rr.min_w is not None and rr.min_w != obj.width:
                    print(f"Error: {instance} has width {obj.width} but min width was {rr.min_w}")
                op.write(f";{vts(rr.base_c)};{vts(rr.min_c)};{vts(rr.max_c)};{vts(rr.max_w)}")
        op.write(os.linesep)
