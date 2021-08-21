from minizinc import Instance, Model, Solver
import datetime
import colorsys
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Rectangle
from src.smt import *



def plot(file, width, height, blocks):
    _, ax = plt.subplots()
    for w,h,x,y,c in blocks:
        ax.add_patch(Rectangle((x,y), w, h, facecolor=c, lw=1))

    ax.set_ylim(0, height)
    ax.set_xlim(0, width)
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_xticks(range(width+1))
    ax.set_yticks(range(height+1))
    ax.grid(color = 'black')
    plt.savefig('out/out-'+file+'.png')

times_cp = []
times_smt = []
MAX = 5
for i in range(1,MAX+1):
    file = str(i)
    with open('ins/ins-'+file+'.txt', 'r') as infile:
        chip_w = int(infile.readline().strip())
        n = int(infile.readline().strip())
        inst_x = []
        inst_y = []
        line = infile.readline()
        while line.strip():
            line_split = (line.strip().split(' '))
            inst_x.append(int(line_split[0]))
            inst_y.append(int(line_split[1]))
            line = infile.readline()

    model = Model("src/m1.mzn")
    solver = Solver.lookup("gecode")
    instance = Instance(solver, model)
    instance['chip_w'] = chip_w
    instance['n'] = n
    instance['inst_x'] = inst_x
    instance['inst_y'] = inst_y

    result = instance.solve(timeout=datetime.timedelta(seconds=300))

    chip_h_cp = result['objective']
    bl_x_cp = result['bl_x']
    bl_y_cp = result['bl_y']

    time_cp = result.statistics['time'].total_seconds()
    times_cp.append(time_cp)

    output_cp = str(chip_w) + " " + str(chip_h_cp) + "\n" + str(n) + "\n"
    for j in range(n):
        output_cp += str(inst_x[j]) + " " + str(inst_y[j]) + " " + str(bl_x_cp[j]) + " " + str(bl_y_cp[j]) + "\n"

    with open('out/out-'+file+'-cp.txt', 'w') as outfile:
        outfile.write(output_cp)

    plot(file+'-cp', chip_w, chip_h_cp, [(inst_x[j], inst_y[j], bl_x_cp[j], bl_y_cp[j], tuple(value/255 for value in colorsys.hsv_to_rgb(j/n,0.75,191))) for j in range(n)])

    chip_h_sat, bl_x_sat, bl_y_sat, time_smt = smt(chip_w, n, inst_x, inst_y)
    times_smt.append(time_smt)
    output_sat = str(chip_w) + " " + str(chip_h_sat) + "\n" + str(n) + "\n"
    for j in range(n):
        output_sat += str(inst_x[j]) + " " + str(inst_y[j]) + " " + str(bl_x_sat[j]) + " " + str(bl_y_sat[j]) + "\n"

    with open('out/out-'+file+'-smt.txt', 'w') as outfile:
        outfile.write(output_sat)

    plot(file+'-smt', chip_w, chip_h_sat, [(inst_x[j], inst_y[j], bl_x_sat[j], bl_y_sat[j], tuple(value/255 for value in colorsys.hsv_to_rgb(j/n,0.75,191))) for j in range(n)])


_, ax = plt.subplots()
ax.bar(np.arange(1,MAX+1)-0.2,times_cp,0.4,label='cp')
ax.bar(np.arange(1,MAX+1)+0.2,times_smt,0.4,label='smt')
ax.set_xticks(range(1,MAX+1))
ax.grid(True)
ax.set_xlabel('instance')
ax.set_ylabel('seconds')
plt.legend(loc='best')
plt.savefig('out/times.png')
