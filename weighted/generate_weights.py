import os
import random
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
import sys


def generate(path_in, path_out, seed, suffix=".w1"):
    random.seed = seed
    in_abs = os.path.abspath(path_in)
    out_abs = os.path.abspath(path_out)
    for r, d, f in os.walk(path_in):
        f.sort()
        new_path = os.path.abspath(r)
        new_path = new_path.replace(in_abs, out_abs)
        if not os.path.exists(new_path):
            os.mkdir(new_path)

        for file in f:
            f_in = os.path.join(r, file)
            f_out = os.path.join(new_path, file + suffix)
            modify_file_uniform(f_in, f_out)
            print(f"Finished {f_in}")


def modify_file_uniform(file_in, file_out, low=1, high=7):
    with open(file_in) as f:
        hg = Hypergraph.fromstream_fischlformat(f)

    with open(file_out, "w+") as f:
        cnt = 0
        for k, e in hg.edges().items():
            cnt += 1
            edge = ','.join((str(x)) for x in e)
            f.write(f"{k}({edge}) {random.randint(low, high)}")
            if cnt < hg.num_hyperedges():
                f.write(",")
            else:
                f.write(".")
            f.write("\n")


def modify_file_dechter(file_in, file_out, low=1, high=7, low_quota=0.66):
    """Assigns a fixed percentage of edges a low weight and the others a high weight. Edges are chosen randomly"""

    with open(file_in) as f:
        hg = Hypergraph.fromstream_fischlformat(f)

    hyperedges = [(k, e) for k, e in hg.edges().items()]

    # Shuffle edges:
    for i in range(0, len(hyperedges)):
        target = random.randint(i, len(hyperedges) - 1)
        # Swap elements
        hyperedges[i], hyperedges[target] = hyperedges[target], hyperedges[i]

    # Cutoff index for low weights
    cutoff = int(len(hyperedges) * low_quota)

    with open(file_out, "w+") as f:
        cnt = 0
        for k, e in hyperedges:
            cnt += 1
            weight = low if cnt <= cutoff else high

            edge = ','.join((str(x)) for x in e)
            f.write(f"{k}({edge}) {weight}")
            if cnt < hg.num_hyperedges():
                f.write(",")
            else:
                f.write(".")
            f.write("\n")


path_in = sys.argv[1]
path_out = sys.argv[2]

generate(path_in, path_out, 1000)
