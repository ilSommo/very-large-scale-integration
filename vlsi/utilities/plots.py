__version__ = '1.0.2'
__author__ = 'Giacomo Berselli, Martino Pulici'


import colorsys

from matplotlib.patches import Rectangle
import matplotlib.pyplot as plt
import numpy as np


# Width of each instance in the bar plot
TOTAL_WIDTH = 0.75


def plot_chip(file, width, height, circuits, min_index):
    """Plots a chip configuration.

    Parameters
    ----------
    file : str
        File name.
    width : int
        Chip width.
    height : int
        Chip height.
    circuits : tuple
        List of the circuits to plot.
    min_index : int
        Index of the smallest circuit.
    """
    # Number of circuits
    n = len(list(circuits))
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
    _, ax = plt.subplots(1, 1, figsize=(width / 2, height / 2))
    # Cycle to draw circuits
    for (w, h, x, y), c in zip(circuits, c):
        # Create colored rectangle
        ax.add_patch(Rectangle((x, y), w, h, facecolor=c))
        # Create rectangle border
        ax.add_patch(Rectangle((x, y), w, h, fill=None, ls='-', lw=2))
    # Create dot for symmetry breaking
    ax.plot(
        circuits[min_index][2] +
        0.5 *
        circuits[min_index][0],
        circuits[min_index][3] +
        0.5 *
        circuits[min_index][1],
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
    ax.set_xlabel('x')
    ax.set_ylabel('y')
    # Draw grid
    ax.grid(color='black', zorder=0)
    # Set plot title
    plt.title(str(file))
    # Save plot
    plt.savefig('out/out-' + file + '.png')
    # Close plot
    plt.close()


def plot_configuration(times, normal, rotation):
    """Gives a plot configuration.

    Parameters
    ----------
    times : list
        List of times lists.
    normal : bool
        Flag for normal.
    rotation : bool
        Flag for rotation.

    Returns
    -------
    width : float
        Width of each bar.
    offsets : list
        List of bar offsets.
    indexes : list
        Indexes of bars to plot.
    """
    # Enter for given configurations
    if normal and rotation:
        # Set plot parameters
        if any(times[0]) and any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 6
            offsets = [-2.5 * width, -1.5 * width, -0.5 *
                       width, 0.5 * width, 1.5 * width, 2.5 * width]
            indexes = range(6)
        if not any(times[0]) and any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 4
            offsets = [0, 0, -1.5 * width, -0.5 *
                       width, 0.5 * width, 1.5 * width]
            indexes = [2, 3, 4, 5]
        if any(times[0]) and not any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 4
            offsets = [-1.5 * width, -0.5 * width,
                       0, 0, 0.5 * width, 1.5 * width]
            indexes = [0, 1, 4, 5]
        if any(times[0]) and any(times[2]) and not any(times[4]):
            width = TOTAL_WIDTH / 4
            offsets = [-1.5 * width, -0.5 * width,
                       0.5 * width, 1.5 * width, 0, 0]
            indexes = [0, 1, 2, 3]
        if any(times[0]) and not any(times[2]) and not any(times[4]):
            width = TOTAL_WIDTH / 2
            offsets = [-0.5 * width, 0.5 * width, 0, 0, 0, 0]
            indexes = [0, 1]
        if not any(times[0]) and any(times[2]) and not any(times[4]):
            width = TOTAL_WIDTH / 2
            offsets = [0, 0, -0.5 * width, 0.5 * width, 0, 0]
            indexes = [2, 3]
        if not any(times[0]) and not any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 2
            offsets = [0, 0, 0, 0, -0.5 * width, 0.5 * width]
            indexes = [4, 5]

    # Enter for given configurations
    if normal and not rotation:
        # Set plot parameters
        if any(times[0]) and any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 3
            offsets = [-width, -width, 0, 0, width, width]
            indexes = [0, 2, 4]
        if not any(times[0]) and any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 2
            offsets = [0, 0, -0.5 * width, -0.5 *
                       width, 0.5 * width, 0.5 * width]
            indexes = [2, 4]
        if any(times[0]) and not any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 2
            offsets = [-0.5 * width, -0.5 * width,
                       0, 0, 0.5 * width, 0.5 * width]
            indexes = [0, 4]
        if any(times[0]) and any(times[2]) and not any(times[4]):
            width = TOTAL_WIDTH / 2
            offsets = [-0.5 * width, -0.5 * width,
                       0.5 * width, 0.5 * width, 0, 0]
            indexes = [0, 2]
        if any(times[0]) and not any(times[2]) and not any(times[4]):
            width = TOTAL_WIDTH / 1
            offsets = [0, 0, 0, 0, 0, 0]
            indexes = [0]
        if not any(times[0]) and any(times[2]) and not any(times[4]):
            width = TOTAL_WIDTH / 1
            offsets = [0, 0, 0, 0, 0, 0]
            indexes = [2]
        if not any(times[0]) and not any(times[2]) and any(times[4]):
            width = TOTAL_WIDTH / 1
            offsets = [0, 0, 0, 0, 0, 0]
            indexes = [4]

    # Enter for given configurations
    if not normal and rotation:
        # Set plot parameters
        if any(times[1]) and any(times[3]) and any(times[5]):
            width = TOTAL_WIDTH / 3
            offsets = [-width, -width, 0, 0, width, width]
            indexes = [1, 3, 5]
        if not any(times[1]) and any(times[3]) and any(times[5]):
            width = TOTAL_WIDTH / 2
            offsets = [0, 0, -0.5 * width, -0.5 *
                       width, 0.5 * width, 0.5 * width]
            indexes = [3, 5]
        if any(times[1]) and not any(times[3]) and any(times[5]):
            width = TOTAL_WIDTH / 2
            offsets = [-0.5 * width, -0.5 * width,
                       0, 0, 0.5 * width, 0.5 * width]
            indexes = [1, 5]
        if any(times[1]) and any(times[3]) and not any(times[5]):
            width = TOTAL_WIDTH / 2
            offsets = [-0.5 * width, -0.5 * width,
                       0.5 * width, 0.5 * width, 0, 0]
            indexes = [1, 3]
        if any(times[1]) and not any(times[3]) and not any(times[5]):
            width = TOTAL_WIDTH / 1
            offsets = [0, 0, 0, 0, 0, 0]
            indexes = [1]
        if not any(times[1]) and any(times[3]) and not any(times[5]):
            width = TOTAL_WIDTH / 1
            offsets = [0, 0, 0, 0, 0, 0]
            indexes = [3]
        if not any(times[1]) and not any(times[3]) and any(times[5]):
            width = TOTAL_WIDTH / 1
            offsets = [0, 0, 0, 0, 0, 0]
            indexes = [5]

    return width, offsets, indexes


def plot_times(times, min_ins, max_ins, top, normal, rotation, name):
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
    labels = ['cp', 'cp-rot', 'sat', 'sat-rot', 'smt', 'smt-rot']
    # Bar colors
    colors = plt.rcParams['axes.prop_cycle'].by_key()['color']
    # Plot configuration
    width, offsets, indexes = plot_configuration(times, normal, rotation)

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
    ax.set_ylim(0.001, top)
    ax.set_xticks(range(min_ins, max_ins + 1))
    ax.set_xlabel('instance')
    ax.set_ylabel('seconds')
    ax.grid(axis='y', which='both')
    ax.set_axisbelow(True)
    # Plot legend
    plt.legend(loc='best')
    # Set plot title
    plt.title('Times')
    # Save plot
    plt.savefig('out/times' + name + '.png')
    # Close plot
    plt.close()
