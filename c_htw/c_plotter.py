import pandas as pd
import sys
import matplotlib.pyplot as plt

inp = sys.argv[1]

## CHTW Exact
start_column = 18
ratio = 3
start_column_limit = 3
# c values
cols = [("Minimal C", start_column + ratio * 4 + 2), ("Maximal C", start_column + ratio * 4 + 3), ("Oblivious C", start_column + ratio * 4 + 1)]
# width
#cols = [("ghtw", start_column), ("5% max width", start_column + 4), ("10% max width", start_column + 8), ("20% max width", start_column + 12), ("30% max width", start_column + 16)]

## CHTW Heuristic
start_column = 1
offset = 3
start_column_limit = 3
ratio = 3
#
# #bnb
#cols = [("c-first", start_column + ratio * 14 + 0 * 4 + 2 + offset), ("c-last", start_column + ratio * 14 + 1 * 4 + 2 + offset), ("oblivious", start_column + ratio * 14 + 2 * 4 + 2 + offset)]
# #greedy
cols = [("oblivious", start_column + ratio * 14 + 2 * 4 + 2 + offset), ("greedy", start_column + ratio * 14 + 0 * 4 + 2 + offset)]

# CTW Heuristic
# start_column = 1
# start_column_limit = 12
# ratio = 3
# offset = 1
#
# cols = [("min c", start_column + ratio * 14 + 6 + offset), ("oblivious", start_column + ratio * 14 + 8 + offset), ("incremental", start_column + ratio * 14 + 4 + offset) ]


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
#ax = frame.plot(style=['bs-', 'ro-', 'y^-', 'g*-'], figsize=(10, 5), linewidth=0, markersize=2, alpha=0.5)
ax = frame.plot(style='x-', figsize=(10, 5), linewidth=0, markersize=2)
#ax = frame.plot(figsize=(10, 5), linewidth=2)
ax.legend(names)

axes = plt.axes()
axes.set_xlabel("instances")
axes.set_ylabel("k")
#axes.set_xlim(0, 2000)

plt.savefig("plot.png")
plt.show()


