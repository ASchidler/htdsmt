import sys
import os
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from c_htw.c_encoding import CHtwEncoding
from frasmt_encoding import FraSmtSolver
from shutil import which
import subprocess
import random

input_file = sys.argv[1]
output_path = sys.argv[2]
result_path = sys.argv[3]
output_name = "slv"
ratios = [0.05, 0.1, 0.2, 0.3]
timeout = 1800

_, instance_name = os.path.split(input_file)


def compute_decomp(use_c, htd, cfirst, cld):
    base_path = os.path.join(output_path, output_name)
    inpf = open(base_path + ".encoding", "w+")
    modelf = open(base_path + ".model", "w+")
    errorf = open(base_path + ".error", "w+")

    # Produce encoding
    enc = CHtwEncoding(FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None), inpf, cld)
    enc.solve(cfirst=cfirst, htd=htd, sb=False, use_c=use_c)
    inpf.seek(0)

    # Find and start solver, either in path or current directory
    executable = 'optimathsat' if which('optimathsat') is not None \
        else os.path.join(os.path.dirname(os.path.realpath(__file__)), '../optimathsat')

    p1 = subprocess.Popen(executable, stdin=inpf, stdout=modelf, stderr=errorf, shell=True)

    try:
        p1.wait(timeout)
    except subprocess.TimeoutExpired:
        return None

    # Retrieve the result from files
    modelf.seek(0)
    outp = modelf.read()

    inpf.close()
    modelf.close()
    errorf.close()

    # Load the resulting model
    return enc.decode(outp, htd=htd)

# Load graph. There is no working auto detect of encoding, so try both options
hypergraph = Hypergraph.from_file(input_file, fischl_format=True)

# Random sort edges, use fixed seed for reproducibility
random.seed(len(hypergraph.edges()) + len(hypergraph.nodes()))
he = list(hypergraph.edges())
for i in range(0, len(he)-1):
    nxt = random.randint(i, len(he)-1)
    he[i], he[nxt] = he[nxt], he[i]

for use_htd in [False, True]:
    base = compute_decomp(False, use_htd, False, set())
    if base is None:
        continue

    for ratio in ratios:
        colored = {he[x] for x in range(0, int(len(he) * ratio + 1))}

        for optc in [True, False]:
            res = compute_decomp(True, use_htd, optc, colored)
            result_file = instance_name
            result_file += ".htd" if use_htd else ".ghtd"
            result_file += ".c" if optc else ".w"
            result_file += ("%.2f" % ratio)[1:]

            with open(os.path.join(result_path, result_file + ".result"), "w+") as result_f:
                base_c = max(len([x for x in colored if cv[x] > 0]) for cv in base.result.weights.values())
                result_f.write(f"wc {res.result.size} cc {res.c} wo {base.result.size} co {base_c}\n")

            with open(os.path.join(result_path, result_file + ".red"), "w+") as result_f:
                for ce in colored:
                    result_f.write(f"{ce}\n")

            with open(os.path.join(result_path, result_file + ".decomp"), "w+") as result_f:
                mode = "ghtd" if not use_htd else "htd"
                result_f.write(f"s {mode} {len(res.result.decomposition.bags)} {res.result.size} {len(res.result.decomposition.hypergraph.nodes())} "
                      f"{len(res.result.decomposition.hypergraph.edges())}\n")

                # Output bags
                for k, v in res.result.decomposition.bags.items():
                    result_f.write("b {} {}\n".format(k, " ".join((str(x) for x in v))))
                result_f.write("\n")

                # Output edges
                for u, v in res.result.decomposition.tree.edges:
                    result_f.write(f"{u} {v}")
                result_f.write("\n")

                # Output edge function
                for k, v in res.result.decomposition.hyperedge_function.items():
                    for k2, v2 in v.items():
                        result_f.write(f"w {k} {k2} {v2}")
