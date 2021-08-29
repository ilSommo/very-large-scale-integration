__version__ = '1.0.2'
__author__ = 'Giacomo Berselli, Martino Pulici'


import numpy as np


def compute_max_h(chip_w, inst_x, inst_y):
    """Calculates maximum chip height.

    Parameters
    ----------
    chip_w : int
        Chip width.
    inst_x : list
        Circuits' widths.
    inst_y : list
        Circuits' heights.

    Returns
    -------
    max_h : int
        Maximum chip height.
    """
    # Maximum height
    max_h = 0
    # Circuits' widths and heights
    inst = zip(inst_x, inst_y)
    # Cycle while there are circuits left
    while inst:
        # Sort circuits according to height and width
        inst = sorted(inst, key=lambda tup: tup[0], reverse=True)
        inst = sorted(inst, key=lambda tup: tup[1], reverse=True)
        # Width left
        chip_cumulative = chip_w
        # Circuit index
        k = 0
        # Heights list
        heights = []
        # Cycle while there are circuits
        while k < len(inst):
            # Enter if there is space for the circuit
            if inst[k][0] <= chip_cumulative:
                # Subtract width
                chip_cumulative -= inst[k][0]
                # Append circuit height
                heights.append(inst[k][1])
                # Remove used circuit
                del inst[k]
            else:
                # Increase index
                k += 1
        # Increase maximum height
        max_h += max(heights)

    return max_h


def preprocessing(file):
    """Preprocesses the file.

    Parameters
    ----------
    file : str
        File name.

    Returns
    -------
    data : dict
        Processed data.
    """
    # Open input file
    with open('ins/ins-' + file + '.txt', 'r') as infile:
        # Width of chip
        chip_w = int(infile.readline().strip())
        # Number of circuits
        n = int(infile.readline().strip())
        # Circuits' widths and heigths
        inst_x = []
        inst_y = []
        line = infile.readline()
        # Read circuits' widths and heigths
        while line.strip():
            line_split = (line.strip().split(' '))
            inst_x.append(int(line_split[0]))
            inst_y.append(int(line_split[1]))
            line = infile.readline()

    # Index of smallest circuit
    min_index = int(np.argmin([inst_x[k] * inst_y[k] for k in range(n)]))
    # Minimum height of chip
    min_h = sum([inst_x[k] * inst_y[k] for k in range(n)]) // chip_w
    # Maximum height of chip
    max_h = compute_max_h(chip_w, inst_x, inst_y)

    # Data dictionary
    data = {}
    data['chip_w'] = chip_w
    data['n'] = n
    data['inst_x'] = inst_x
    data['inst_y'] = inst_y
    data['min_h'] = min_h
    data['max_h'] = max_h
    data['min_index'] = min_index

    return(data)
