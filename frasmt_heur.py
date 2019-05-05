from __future__ import absolute_import

import sys
import select
import inspect
import frasmt_solver
import os
import subprocess
import solver_decoder
import logging
import signal

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from htd_validate import Hypergraph

# End of imports
# Use z3 or mathsat?
is_z3 = False
# Filenames and paths to use
inp_file = '/tmp/slv.encode'
model_file = '/tmp/slv.model'
err_file = '/tmp/slv.err'

# Disable logging, otherwise PACE runs fail... Exceptions will still terminate the run
logging.disable(logging.FATAL)

# Encode solver as string, uncomment before submitting!
if is_z3:
    solver_decoder.encode_z3()
else:
    solver_decoder.encode_ms()

# Load graph from input
hypergraph = None
if not select.select([sys.stdin, ], [], [], 0.0)[0]:
    if len(sys.argv) == 2:
        hypergraph = Hypergraph.from_file(sys.argv[1], fischl_format=False)
    else:
        print "Please provide the input via STDIN or as a filename as the first and only argument"
        exit(1)
else:
    hypergraph = Hypergraph.fromstream_dimacslike(sys.stdin)

# Load solver and check permissions
slv = solver_decoder.decode()

# Launch SMT solver
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
src_path = os.path.realpath(os.path.join(src_path, '..'))

# Create temporary files
inpf = open(inp_file, "w+")

# Create encoding of the instance
enc = frasmt_solver.FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None)
enc.solve(optimize=False)

res = None

# Loop to find better and better results
cont_run = True
p1 = None


def handle(signum, fame):
    global cont_run, p1
    cont_run = False
    if p1:
        try:
            p1.kill()
        except:
            pass


signal.signal(signal.SIGTERM, handle)


while cont_run:
    inpf.seek(0)
    modelf = open(model_file, "w+")
    errorf = open(err_file, "w+")

    if is_z3:
        p1 = subprocess.Popen([slv, '-smt2', '-in'], stdin=inpf, stdout=modelf, stderr=errorf)
    else:
        p1 = subprocess.Popen(slv, stdin=inpf, stdout=modelf, stderr=errorf, shell=True)

    p1.wait()

    if not cont_run:
        break

    # Retrieve the result
    modelf.seek(0)
    errorf.seek(0)
    outp = modelf.read()
    errp = errorf.read()

    modelf.close()
    errorf.close()

    if len(errp) > 0:
        break

    if outp.startswith("unsat"):
        break

    # Load the resulting model
    res = enc.decode(outp, is_z3)
    inpf.seek(0)
    inpf.seek(inpf.read().index("(check-sat)"))
    inpf.truncate()
    inpf.write("(assert (< m {}))\n".format(res['objective']))
    inpf.write("(check-sat)\n(get-model)\n")


inpf.close()

# Display the HTD
td = res['decomposition']
num_edges = len(td.T.edges)

sys.stdout.write('s htd {} {} {} {}\n'.format(len(td.bags), res['objective'], td.num_vertices,
                                              # Last one is the number of hyperedges
                                              len(next(iter(td.hyperedge_function.itervalues())))))

# Print bag information
for edge, _ in td.hyperedge_function.iteritems():
    sys.stdout.write('b {}'.format(edge))

    for vx in td.bags.get(edge):
        sys.stdout.write(' {}'.format(vx))
    sys.stdout.write('\n')

# Print edges
for v1, v2 in td.tree.edges:
    sys.stdout.write('{} {}\n'.format(v1, v2))

# Print mapping
for v1, vals in td.hyperedge_function.iteritems():
    for v2, val in vals.iteritems():
        sys.stdout.write('w {} {} {}\n'. format(v1, v2, val))
