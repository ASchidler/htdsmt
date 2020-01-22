import pandas as pd
import sys
import matplotlib.pyplot as plt
from collections import defaultdict
import math
from matplotlib.ticker import MaxNLocator

inp = sys.argv[1]

## CHTW Exact
start_column = 18
ratio = 3
start_column_limit = 3
sf = 5
# c values
#cols = [("Aware", start_column + ratio * 4 + 3), ("Oblivious", start_column + ratio * 4 + 1)]
cols = [("Aware", start_column + ratio * 4 + 3), ("Optimized", start_column + ratio * 4 + 2)]
# width
#cols = [("ghtw", start_column), ("10% max width", start_column + 8)]
#cols = [("GHTW", start_column), ("Optimized", start_column + 16)]


## CHTW Heuristic
# start_column = 1
# offset = 0
# start_column_limit = 3
# ratio = 3
# sf = 0.5
#
# #cfirst
# cols = [("Optimizing B&B", start_column + ratio * 14 + 0 * 4 + 2 + offset), ("Oblivious B&B", start_column + ratio * 14 + 2 * 4 + 2 + offset)]
#clast
#cols = [("Aware B&B", start_column + ratio * 14 + 1 * 4 + 2 + offset), ("Oblivious B&B", start_column + ratio * 14 + 2 * 4 + 2 + offset)]
#greedy
#cols = [("Optimizing Greedy", start_column + ratio * 14 + 0 * 4 + 2 + offset + 2), ("Oblivious Greedy", start_column + ratio * 14 + 2 * 4 + 2 + offset + 2)]

#CTW Heuristic
start_column = 1
start_column_limit = 12
ratio = 3
offset = 0
#
# cols = [("Optimized", start_column + ratio * 14 + 6 + offset), ("Aware", start_column + ratio * 14 + 4 + offset), ("Oblivious", start_column + ratio * 14 + 8 + offset) ]

CTW Exact
start_column = 1
start_column_limit = 12
ratio = 3
sf = 1.6
#
# # C
# #cols = [("Aware", start_column + ratio * 4 + 3), ("Optimized", start_column + ratio * 4 + 2)]
# #cols = [("Aware", start_column + ratio * 4 + 3), ("Oblivious", start_column + ratio * 4 + 1)]
# # k
cols = [("Treewidth", start_column), (f"Optimized", start_column + ratio * 4 + 4)]

results = []
missed = 0
missed2 = 0
header = False
with open(inp, "r") as inpf:
    for ln in inpf:
        # ignore header
        if not header:
            header = True
            continue

        f_cols = ln.split(";")
        try:
            if int(f_cols[start_column]) > start_column_limit:
                c_results = []
                for k, v in cols:
                    c_results.append(int(f_cols[v]))
                results.append(c_results)
            else:
                missed2 += 1
        except ValueError:
            if (f_cols[start_column].strip != "" and f_cols[33].strip() == ""):
                missed += 1
            pass

results.sort()
# results.sort(key=lambda x: (x[2], x[1], x[0]))
#
# frames = []
# names = []
#
# for i in range(0, len(cols)):
#     vals = [x[i] for x in results]
#     #vals.sort()
#     frames += [pd.DataFrame(vals)]
#     names.append(cols[i][0])
#
# frame = pd.concat(frames, ignore_index=True, axis=1)
# frame.cumsum()
# #ax = frame.plot(style=['bs-', 'ro-', 'y^-', 'g*-'], figsize=(10, 5), linewidth=0, markersize=2, alpha=0.5)
# ax = frame.plot(style=['bs-', 'ro-', 'y^-', 'g*-'], figsize=(2.5, 2), linewidth=0, markersize=0.3)
# #ax = frame.plot(figsize=(10, 5), linewidth=2)
# ax.legend(names, frameon=False, fontsize="x-small", loc=4, markerfirst=False, markerscale=10, borderpad=0, handletextpad=0, borderaxespad=0)
# #ax.legend(names, frameon=False, fontsize="x-small", loc=1, markerfirst=False, markerscale=10, borderpad=0, handletextpad=0, borderaxespad=0.5)
# axes = plt.axes()
# axes.set_yscale("log")
# plt.ylim(0, 10**3)
# axes.set_xlabel("Instances")
# axes.set_ylabel("Load")
# #axes.set_xlim(0, 2000)
#
# plt.savefig("plot.png")
# plt.show()


###########################################
## Scatter
values = defaultdict(lambda: 0)
for r in results:
    values[(r[0], r[1])] += 1

x = []
y = []
s = []
n = []

maxval = 0
minval = sys.maxsize
for (v1, v2), v3 in values.items():
    maxval = max(maxval, v2)
    maxval = max(maxval, v1)
    minval = min(minval, v2)
    minval = min(minval, v1)
    x.append(v1)
    y.append(v2)
    s.append(sf * v3)
    n.append(str(v3))

fig, ax = plt.subplots(figsize=(2.5, 2.5), dpi=80)
ax.set_axisbelow(True)
#ax.yaxis.grid(color='gray', linestyle='dashed')
#ax.yaxis.grid(color='gray', linestyle='dashed')
ax.grid(True)
ax.scatter(x, y, s=s, edgecolor='black', color='white',
           alpha=1)

plt.xlabel(cols[0][0])
plt.ylabel(cols[1][0])
plt.xlim(minval-0.8, maxval + 0.1)
plt.ylim(minval-0.8, maxval + 0.1)

plt.plot(list(range(0, maxval+1)), color='black', linewidth=0.5, linestyle='dashed')
#plt.yticks(list(range(minval, maxval + 1)))
#plt.xticks(list(range(minval, maxval + 1)))
#ax.legend()

ax.yaxis.set_major_locator(MaxNLocator(integer=True))
ax.xaxis.set_major_locator(MaxNLocator(integer=True))

#for i, txt in enumerate(n):
#    ax.annotate(txt, (x[i] + math.sqrt(s[i]) / 230.0, y[i] + math.sqrt(s[i]) / 230.0))

plt.gcf().subplots_adjust(bottom=0.18, left=0.2)
plt.savefig("plot.png")
plt.show()
