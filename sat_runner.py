import argparse
import io
import subprocess
import sys

import bounds.upper_bounds as bnd
from lib.htd_validate.htd_validate.utils import Hypergraph
from sat_encoding import HtdSatEncoding

parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')
parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')

args = parser.parse_args()

input_file = args.graph_file
hypergraph_in = Hypergraph.from_file(input_file, fischl_format=False)
hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True)

if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
    hypergraph_in = hypergraph2

known_ub = None
known_lb = None
current_bound = bnd.greedy(hypergraph_in, False, bb=False)
timeout = 0

while known_lb is None or known_ub is None or known_lb != known_ub:
    with io.StringIO() as enc:
        encoder = HtdSatEncoding(enc, hypergraph_in)
        encoder.encode_htd()

        with io.StringIO() as model:
            with io.StringIO as error:
                p1 = subprocess.Popen('minisat', stdin=enc, stdout=model, stderr=error, shell=True)
                if timeout == 0:
                    p1.wait()
                else:
                    try:
                        p1.wait(timeout)
                    except subprocess.TimeoutExpired:
                        print(f"Timeout exceed, bounds {known_lb} to {known_ub}")

                # Check if errors
                error_str = error.read(None)
                if len(error_str) > 0:
                    sys.stderr.write(error_str)
                    sys.stderr.write("\n")

            result = encoder.decode(model)
            if result is None:
                known_lb = current_bound + 1
            else:
                known_ub = result

            if known_ub is not None:
                current_bound = known_ub - 1
            else:
                current_bound = known_lb + 1

print(f"Width : {known_ub}")
