import sys
import os
from collections import defaultdict

from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from itertools import combinations
import matplotlib.pyplot as plt

pth = sys.argv[1]
results = []
instance_data = []

colors = ['black', '#bb5566', '#004488', '#228833', '#eecc66']
# colors = ['black', '#bb5566', '#004488']
symbols = ['d', 'x', 's', 'v', 'o']

if not os.path.exists("graph_data.csv"):
    groups = defaultdict(list)
    with open("Type_of.csv") as tf:
        for i, cl in enumerate(tf):
            if i > 0:
                cf = cl.strip().split(",")
                groups[cf[0]].append(cf[1])

    with open("graph_data.csv", "w") as gdf:
        with open("results_download.csv") as ipf:
            for i, cl in enumerate(ipf):
                if i > 1:
                    cf = cl.strip().split(";")
                    hg = Hypergraph.from_file(os.path.join(sys.argv[1], cf[0]), fischl_format=True)
                    e_cnt = 0
                    width = None
                    for e in hg.edges():
                        # PRIMAL GRAPH CONSTRUCTION
                        for i, j in combinations(hg.get_edge(e), 2):
                            e_cnt += 1
                            # if i > j:
                            #     i, j = j, i
                            # if i < j:
                            #     self._add_clause(-self.ord[i][j], self.arc[i][j])
                            #     self._add_clause(-self.ord[j][i], self.arc[j][i])

                    fields = []
                    c_start = 1
                    slv = 0
                    for cm in range(0, 5):
                        if cf[c_start+2].strip() == "":
                            fields.append(False)
                        else:
                            fields.append(float(cf[c_start].strip()))
                            if width is None:
                                width = int(cf[c_start+2].strip())
                            slv += 1
                        c_start += 3
                    gdf.write(f"{cf[0]};{'' if not fields[1] else fields[1]};{'' if not fields[3] else fields[3]};{hg.number_of_nodes()};{e_cnt};{width};"
                              f"{'' if not fields[0] else fields[0]};{'' if not fields[2] else fields[2]};{'' if not fields[4] else fields[4]};{','.join(groups[cf[0]])}{os.linesep}")
                    results.append(fields)
                    instance_data.append([hg.number_of_nodes(), width, e_cnt])

X = [[], [], [], []]
Y = [[], [], [], []]
W = [[], [], [], []]
# X = [defaultdict(list), defaultdict(list), {}, {}]

group_results = defaultdict(lambda: [0, 0, 0, 0, 0, 0])
with open("graph_data.csv") as gdf:
    for cl in gdf:
        cf = cl.strip().split(";")
        for cg in cf[-1].strip().split(","):
            group_results[cg][0] += 1
            for cgm, c_idx in enumerate([1, 7, 2, 8, 6,]):
                if cf[c_idx] != "":
                    group_results[cg][cgm+1] += 1
        # Graph size
        # idx = -1
        # if cf[1] != "" and cf[2] != "":
        #     idx = 1
        # elif cf[1] != "":
        #     idx = 2
        # elif cf[2] != "":
        #     idx = 3
        # elif cf[1] == "" and cf[2] == "":
        #     idx = 0
        # legend = ['None', 'Both', 'SAT', 'SMT']
        # if idx != -1:
        #     X[idx].append(int(cf[3]))
        #     Y[idx].append(int(cf[4]))

        # Width runtime
        # legend = ['SAT', 'SMT']
        # if cf[1] != "":
        #     X[0][int(cf[5])].append(float(cf[1]))
        # if cf[2] != "":
        #     X[1][int(cf[5])].append(float(cf[2]))

        # Nodes runtime
        legend = ['SAT', 'SMT']
        if cf[1] != "":
            Y[0].append(float(cf[1]))
            X[0].append(int(cf[3]))
            W[0].append(int(cf[5]) ** 1.5)
        if cf[2] != "":
            Y[1].append(float(cf[2]))
            X[1].append(int(cf[3]))
            W[1].append(int(cf[5]) ** 1.5)

print("Group& Total & P SAT&P MaxSAT&P SMT&A SAT&DetK\\\\")
for cg, cel in sorted(group_results.items()):
    print(f"{cg} & {'&'.join([str(x) for x in cel])}\\\\")

# max_y = max(max_y, max(y))
# min_y = min(min_y, min(y))
fig, ax = plt.subplots(figsize=(4, 2.5), dpi=300)
for c_idx in range(0, 4):
    if len(X[c_idx]) == 0:
        continue

    ax.scatter(X[c_idx], Y[c_idx], marker=symbols.pop(), s=W[c_idx], alpha=0.7, color=colors.pop())
#ax.boxplot(X[1].values())

# ax.set_axisbelow(True)
# names = []
#
ax.set_xlabel('Width')
ax.set_ylabel('Runtime [s]')
# # ax.set_title('scatter plot')
# plt.rcParams["legend.loc"] = 'lower right'
plt.rcParams['savefig.pad_inches'] = 0
plt.autoscale(tight=True)
plt.legend(legend)
# plt.xscale("log")
# plt.yscale("log")
# if field_idx == 0 or field_idx == 3:
#     plt.xlim(min_x - 1, max_x + 1)
#     plt.ylim(min_y - 1, max_y + 1)
# if field_idx == 1:
#     plt.xlim(min_x-10, max_x+500)
#     plt.ylim(min_y-10, max_y+500)
# if field_idx == 2:
#     plt.xlim(min_x-0.01, max_x+0.01)
#     plt.ylim(min_y-0.01, max_y+0.01)
# ax.axline([0, 0], [1, 1], linestyle="--", color="grey", zorder=0)
#
plt.savefig(f"scatter.pdf", bbox_inches='tight')
plt.show()
#
#
# for cm in range(0, 5):
#     cnt = 0
#     for centry in results:
#         if centry[cm]:
#             cnt += 1
#
#     print(f"{cnt}")


#
# for r, d, f in os.walk(pth):
#     for c_file in f:
#         if c_file.endswith(".hg"):
#             hg = Hypergraph.from_file(os.path.join(r, c_file), fischl_format=True)
#             e_cnt = 0
#             for e in hg.edges():
#                 # PRIMAL GRAPH CONSTRUCTION
#                 for i, j in combinations(hg.get_edge(e), 2):
#                     e_cnt += 1
#                     # if i > j:
#                     #     i, j = j, i
#                     # if i < j:
#                     #     self._add_clause(-self.ord[i][j], self.arc[i][j])
#                     #     self._add_clause(-self.ord[j][i], self.arc[j][i])
#             print(f"{c_file};{hg.number_of_nodes()};{hg.number_of_edges()};{e_cnt}")
