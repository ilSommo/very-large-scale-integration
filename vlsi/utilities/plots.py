__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'

import colorsys

from matplotlib.patches import Rectangle
import matplotlib.pyplot as plt
import numpy as np


def plot_chip(file, width, height, blocks, min_index):
    _, ax = plt.subplots()
    index = 1
    n = len(list(blocks))
    c = [tuple(value / 255 for value in colorsys.hsv_to_rgb(k / n, 0.75,191)) for k in range(n)]
    for (w, h, x, y), c in zip(blocks,c):
        ax.add_patch(Rectangle((x, y), w, h, facecolor=c))
        ax.add_patch(Rectangle((x, y), w, h, fill=None, ls='-', lw=2))
        index += 1
    plt.plot(blocks[min_index][2]+0.5*blocks[min_index][0], blocks[min_index][3]+0.5*blocks[min_index][1],'o',color='white',zorder=3)
    # ax.add_patch(Rectangle((0, 0), width/2, height/2, fill=None, ls='--', lw=2,color='white',zorder=3))
    ax.set_xlim(0, width)
    ax.set_ylim(0, height)
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.set_xticks(range(width + 1))
    ax.set_yticks(range(height + 1))
    ax.grid(color='black',zorder=0)
    ax.plot([0,width/2], [height/2, height/2],ls='--', lw=2,color='white',zorder=3)
    ax.plot([width/2,width/2], [0, height/2],ls='--', lw=2,color='white',zorder=3)
    plt.title(str(file))
    plt.savefig("out/out-" + file + ".png")
    plt.close()

TOTAL_WIDTH = 0.75
def plot_times(times, min_ins, max_ins, top, normal, rotation):
    labels = ["cp","cp-rot","sat","sat-rot","smt","smt-rot"]
    colors = plt.rcParams['axes.prop_cycle'].by_key()['color']
    if normal and rotation:
        width = TOTAL_WIDTH/6
        offsets = [-2.5*width,-1.5*width,-0.5*width,0.5*width,1.5*width,2.5*width]
        indexes = range(6)
    else:
        width = TOTAL_WIDTH/3
        offsets = [-width,-width,0,0,width,width]
        indexes = [0,2,4] if normal else [1,3,5]
    _, ax = plt.subplots(1, 1, figsize=(12.8, 7.2))
    ax.set_axisbelow(True)
    for i in indexes:
        ax.bar(np.arange(min_ins, max_ins + 1) + offsets[i], top, width, color=colors[i], alpha=0.2)    
        ax.bar(np.arange(min_ins, max_ins + 1) + offsets[i], times[i], width, label=labels[i], color=colors[i])    
    ax.set_xticks(range(min_ins, max_ins + 1))
    ax.grid(axis='y', which='both')
    ax.set_xlabel("instance")
    ax.set_ylabel("seconds")
    plt.yscale('log')
    ax.set_xlim(min_ins-(1-TOTAL_WIDTH/2),max_ins+(1-TOTAL_WIDTH/2))
    ax.set_ylim(top=top)
    plt.tick_params(axis='y', which='both')
    plt.legend(loc='best')
    plt.title("Times")
    plt.savefig("out/times.png")
    plt.close()