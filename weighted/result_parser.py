import os
import re
import sys

pth = sys.argv[1]
outp = sys.argv[2]
benchmarks = ["GHTW1", "WGHTW1", "GHTW2", "WGHTW2"]
results = {x:  (0, 0, 0, 0) for x in benchmarks}

with open(outp, "w") as output:
    for name in benchmarks:
        output.write(f"{name} width;{name} weight;{name} time;")
    output.write(os.linesep)

    for r, d, f in os.walk(pth):
        for file in f:
            f_result = {}

            with open(os.path.join(r, file)) as c_file:
                content = c_file.readlines()

                for line in content:
                    for name, (cnt, width, weight, time) in results.items():
                        if line.strip().startswith(name):
                            m = re.match(f"{name}: ([0-9]+) - width: ([0-9]+) in (.*)$", line)
                            weight = int(m.group(1))
                            width = int(m.group(2))
                            tm = float(m.group(3))
                            f_result[name] = (width, weight, tm)
                            results[name] = (cnt + 1, width + width, weight + weight, time + tm)
                            break

                for name in benchmarks:
                    if name in f_result:
                        width, weight, tm = f_result[name]
                        output.write(f"{width};{weight};{tm};")
                    else:
                        output.write(";;;")

    for name, (cnt, width, weight, time) in results.items():
        if cnt == 0:
            print(f"{name}\tsolved: 0\twidth: NA\tweight: NA\ttime: NA")
        else:
            print(f"{name}\tsolved: {cnt}\twidth: {width * 1.0 / cnt}\tweight: {weight * 1.0 / cnt}\ttime: {time / cnt}")
