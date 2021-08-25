__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


import numpy as np

def preprocessing(file):
    with open("ins/ins-" + file + ".txt", 'r') as infile:
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

    min_index = int(np.argmin([inst_x[k]*inst_y[k] for k in range(n)]))

    total_area = sum([inst_x[k]*inst_y[k] for k in range(n)])

    min_h = total_area // chip_w
    
    max_h = 0
    inst = zip(inst_x, inst_y)
    while inst:
        inst = sorted(inst, key=lambda tup: tup[0], reverse=True)
        inst = sorted(inst, key=lambda tup: tup[1], reverse=True)
        chip_cumulative = chip_w
        tiles = 0
        k = 0
        heights = []
        while k < len(inst):
            if inst[k][0] <= chip_cumulative:
                chip_cumulative -= inst[k][0]
                tiles += 1
                heights.append(inst[k][1])
                del inst[k]
            else:
                k += 1
        max_h += max(heights)
    data={}
    data['chip_w'] = chip_w
    data['n'] = n
    data['inst_x'] = inst_x
    data['inst_y'] = inst_y
    data['min_h'] = min_h
    data['max_h'] = max_h
    data['min_index'] = min_index
    return(data)