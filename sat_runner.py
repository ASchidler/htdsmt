import argparse
import subprocess
import os
import time
from shutil import which
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
import bounds.upper_bounds as bnd

from sat_encoding import HtdSatEncoding

parser = argparse.ArgumentParser(description='Calculate the hypertree decomposition for a given hypergraph')
parser.add_argument('graph', metavar='graph_file', type=str,
                   help='The input file containing the hypergraph')
parser.add_argument('-g', dest='ghtd', action='store_true', default=False,
                    help='Compute a GHTD instead of a HTD')
parser.add_argument('-d', dest='tmp_dir', default='/tmp', help='Path for temporary files, defaults to /tmp')

parser.add_argument('-s', dest="solver", default='glucose', help='The solver to use')

args = parser.parse_args()
tmp_dir = args.tmp_dir
if "TMPDIR" in os.environ:
    tmp_dir = os.environ['TMPDIR']

# The solver to use
solver = 'glucose'

# Executable is in path
executable = None
if which(solver) is not None:
    executable = solver
else:
    executable = os.path.join(os.path.dirname(os.path.realpath(__file__)), solver)


input_file = args.graph
hypergraph_in = Hypergraph.from_file(input_file, fischl_format=False)
hypergraph2 = Hypergraph.from_file(input_file, fischl_format=True)

if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
    hypergraph_in = hypergraph2

known_ub = None
known_lb = 1

current_bound = bnd.greedy(hypergraph_in, False, bb=False)
timeout = 0
before_tm = time.time()

while known_lb is None or known_ub is None or known_lb != known_ub:
    print(f"Current bound: {current_bound}")
    tmpin = os.path.join(tmp_dir, str(os.getpid()) + ".in")
    tmpout = os.path.join(tmp_dir, str(os.getpid()) + ".out")
    with open(tmpin, "w") as instr:
        encoder = HtdSatEncoding(instr, hypergraph_in)
        encoder.encode(current_bound, not args.ghtd)

    with open(tmpout, "w") as outf:
        #p1 = subprocess.Popen(['./lingeling', "-q", "--witness", tmpin], stdout=outf)
        p1 = subprocess.Popen([executable, "-verb=0", tmpin, tmpout])
        #p1 = subprocess.Popen(['minisat', '-verb=0', tmpin, tmpout])
    error_str = None

    if timeout == 0:
        p1.wait()
    else:
        try:
            p1.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            print(f"Timeout exceed, bounds {known_lb} to {known_ub}")
            exit(1)
    os.remove(tmpin)

    with open(tmpout, "r") as model_file:
        result = encoder.decode(model_file)
    os.remove(tmpout)

    if result is None:
        known_lb = current_bound + 1
    else:
        known_ub = result

    if known_ub is not None:
        current_bound = known_ub - 1
    else:
        current_bound = known_lb + 1

print(f"Width : {known_ub}")
print(f"Solved in: {time.time() - before_tm}")
