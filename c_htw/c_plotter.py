import pandas as pd
import sys
import matplotlib.pyplot as plt
from collections import defaultdict
import math

inp = sys.argv[1]

## CHTW Exact
start_column = 18
ratio = 3
start_column_limit = 3
sf = 75
# c values
cols = [("Maximal C", start_column + ratio * 4 + 3), ("Oblivious C", start_column + ratio * 4 + 1)]
# width
#cols = [("ghtw", start_column), ("10% max width", start_column + 8), ("30% max width", start_column + 16)]

## CHTW Heuristic
start_column = 1
offset = 1
start_column_limit = 3
ratio = 3
sf = 1.5
#
#bnb
cols = [("C-Last", start_column + ratio * 14 + 1 * 4 + 2 + offset), ("Oblivious", start_column + ratio * 14 + 2 * 4 + 2 + offset), ("c-first", start_column + ratio * 14 + 0 * 4 + 2 + offset)]
#greedy
#cols = [("Greedy", start_column + ratio * 14 + 0 * 4 + 2 + offset), ("Oblivious", start_column + ratio * 14 + 2 * 4 + 2 + offset)]

# CTW Heuristic
# start_column = 1
# start_column_limit = 12
# ratio = 3
# offset = 1
#
# cols = [("min c", start_column + ratio * 14 + 6 + offset), ("oblivious", start_column + ratio * 14 + 8 + offset), ("incremental", start_column + ratio * 14 + 4 + offset) ]

# CTW Exact
start_column = 1
offset = 1
start_column_limit = 12
ratio = 1
sf = 1.5

# C
#cols = [("Maximal C", start_column + ratio * 4 + 3), ("Oblivious C", start_column + ratio * 4 + 1)]
# k
cols = [("tw", start_column), ("10% max width", start_column + 8), ("30% max width", start_column + 16)]

results = []
with open(inp, "r") as inpf:
    for i, ln in enumerate(inpf):
        # ignore header
        if i > 0:
            f_cols = ln.split(";")
            try:
                if int(f_cols[start_column]) > start_column_limit:
                    c_results = []
                    for k, v in cols:
                        c_results.append(int(f_cols[v]))
                    results.append(c_results)
            except ValueError:
                pass

results.sort()

frames = []
names = []

for i in range(0, len(cols)):
    vals = [x[i] for x in results]
    #vals.sort()
    frames += [pd.DataFrame(vals)]
    names.append(cols[i][0])

frame = pd.concat(frames, ignore_index=True, axis=1)
frame.cumsum()
ax = frame.plot(style=['bs-', 'ro-', 'y^-', 'g*-'], figsize=(10, 5), linewidth=0, markersize=2, alpha=0.5)
ax = frame.plot(style='x-', figsize=(10, 5), linewidth=0, markersize=2)
ax = frame.plot(figsize=(10, 5), linewidth=2)
ax.legend(names)

axes = plt.axes()
axes.set_xlabel("instances")
axes.set_ylabel("k")
#axes.set_xlim(0, 2000)

plt.savefig("plot.png")
plt.show()


###########################################
## Scatter
# values = defaultdict(lambda: 0)
# for r in results:
#     values[(r[0], r[1])] += 1
#
# x = []
# y = []
# s = []
# n = []
#
# maxval = 0
# for (v1, v2), v3 in values.items():
#     x.append(v1)
#     maxval = max(maxval, v1)
#     y.append(v2)
#     maxval = max(maxval, v2)
#     s.append(sf * v3)
#     n.append(str(v3))
#
# fig, ax = plt.subplots()
# ax.scatter(x, y, s=s, edgecolor='black', color='white',
#            alpha=1)
#
# plt.xlabel(cols[0][0])
# plt.ylabel(cols[1][0])
# plt.xlim(-0.4, maxval)
# plt.ylim(-0.2, maxval + 0.4)
# plt.plot(list(range(0, maxval+1)), color='black', linewidth=0.5)
# #ax.legend()
# ax.grid(True)
#
# #for i, txt in enumerate(n):
# #    ax.annotate(txt, (x[i] + math.sqrt(s[i]) / 230.0, y[i] + math.sqrt(s[i]) / 230.0))
#
# plt.savefig("plot.png")
# plt.show()