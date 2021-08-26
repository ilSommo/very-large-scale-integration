__version__ = '1.0.0-rc.4'
__author__ = 'Giacomo Berselli, Martino Pulici'


import colorsys

from matplotlib.patches import Rectangle
import matplotlib.pyplot as plt
import numpy as np


# Width of each instance in the bar plot
TOTAL_WIDTH = 0.75


def plot_chip(file, width, height, blocks, min_index):
    """Plots a chip configuration.

    Parameters
    ----------
    file : str
        File name.
    width : int
        Chip width.
    height : int
        Chip height.
    blocks : tuple
        List of the blocks to plot.
    min_index : int
        Index of the smallest block.
    """
    # Number of blocks
    n = len(list(blocks))
    # Color list
    c = [
        tuple(
            value /
            255 for value in colorsys.hsv_to_rgb(
                k /
                n,
                0.75,
                191)) for k in range(n)]
    # Create plot
    _, ax = plt.subplots()
    # Cycle to draw blocks
    for (w, h, x, y), c in zip(blocks, c):
        # Create colored rectangle
        ax.add_patch(Rectangle((x, y), w, h, facecolor=c))
        # Create rectangle border
        ax.add_patch(Rectangle((x, y), w, h, fill=None, ls='-', lw=2))
    # Create dot for symmetry breaking
    ax.plot(
        blocks[min_index][2] +
        0.5 *
        blocks[min_index][0],
        blocks[min_index][3] +
        0.5 *
        blocks[min_index][1],
        'o',
        color='white',
        zorder=3)
    # Create dashed lines for symmetry breaking
    ax.plot([0, width / 2], [height / 2, height / 2],
            ls='--', lw=2, color='white', zorder=3)
    ax.plot([width / 2, width / 2], [0, height / 2],
            ls='--', lw=2, color='white', zorder=3)
    # Set ax parameters
    ax.set_xlim(0, width)
    ax.set_ylim(0, height)
    ax.set_xticks(range(width + 1))
    ax.set_yticks(range(height + 1))
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    # Draw grid
    ax.grid(color='black', zorder=0)
    # Set plot title
    plt.title(str(file))
    # Save plot
    plt.savefig("out/out-" + file + ".png")
    # Close plot
    plt.close()


def plot_times(times, min_ins, max_ins, top, normal, rotation):
    """Plots the time graph.

    Parameters
    ----------
    times : list
        Times to plot.
    min_ins : int
        Minimum instance to plot.
    max_ins : int
        Maximum instance to plot.
    top : int
        Time limit.
    normal : bool
        Flag to plot normal times.
    rotation : bool
        Flag to plot rotation times.
    """
    # Bar labels
    labels = ["cp", "cp-rot", "sat", "sat-rot", "smt", "smt-rot"]
    # Bar colors
    colors = plt.rcParams['axes.prop_cycle'].by_key()['color']
    # Enter for single configuration
    if normal and rotation:
        # Set plot parameters
        width = TOTAL_WIDTH / 6
        offsets = [-2.5 * width, -1.5 * width, -0.5 *
                   width, 0.5 * width, 1.5 * width, 2.5 * width]
        indexes = range(6)
    # Enter for double configuration
    else:
        # Set plot parameters
        width = TOTAL_WIDTH / 3
        offsets = [-width, -width, 0, 0, width, width]
        indexes = [0, 2, 4] if normal else [1, 3, 5]
    # Create plot
    _, ax = plt.subplots(1, 1, figsize=(12.8, 7.2))
    # Cycle to draw bars
    for i in indexes:
        # Plot instance times
        ax.bar(
            np.arange(
                min_ins,
                max_ins +
                1) +
            offsets[i],
            top,
            width,
            color=colors[i],
            alpha=0.2)
        ax.bar(
            np.arange(
                min_ins,
                max_ins +
                1) +
            offsets[i],
            times[i],
            width,
            label=labels[i],
            color=colors[i])
    # Set ax parameters
    plt.yscale('log')
    plt.tick_params(axis='y', which='both')
    ax.set_xlim(min_ins - (1 - TOTAL_WIDTH / 2),
                max_ins + (1 - TOTAL_WIDTH / 2))
    ax.set_ylim(top=top)
    ax.set_xticks(range(min_ins, max_ins + 1))
    ax.set_xlabel("instance")
    ax.set_ylabel("seconds")
    ax.grid(axis='y', which='both')
    ax.set_axisbelow(True)
    # Plot legend
    plt.legend(loc='best')
    # Set plot title
    plt.title("Times")
    # Save plot
    plt.savefig("out/times.png")
    # Close plot
    plt.close()
