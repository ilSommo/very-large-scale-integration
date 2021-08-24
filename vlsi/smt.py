__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


import time

import z3

def smt(chip_w, n, inst_x, inst_y, max_h, timeout):
    opt = z3.Optimize()
    opt.set('timeout', timeout*1000)
    chip_h = z3.Int("chip_h")

    total_area = 0

    bl_x = z3.IntVector("bl_x", n)
    bl_y = z3.IntVector("bl_y", n)

    for k in range(n):
        total_area += inst_x[k]*inst_y[k]
        opt.add(bl_x[k] >=0)
        opt.add(bl_x[k] <= chip_w - min(inst_x))
        opt.add(bl_y[k] >=0)
        opt.add(bl_y[k] <= chip_w - min(inst_y))
        opt.add(bl_x[k]+inst_x[k] <= chip_w)
        opt.add(chip_h>=bl_y[k] + inst_y[k])
        for l in range(n):
            if k != l:
                opt.add(z3.Or((bl_x[l]+inst_x[l] <= bl_x[k]),(bl_x[l] >= bl_x[k]+inst_x[k]),(bl_y[l]+inst_y[l] <= bl_y[k]),(bl_y[l] >= bl_y[k]+inst_y[k])))

    min_h = total_area / chip_w

    opt.add(chip_h <= max_h)
    opt.add(chip_h >= min_h)
    
    opt.minimize(chip_h)
    start = time.time() 
    opt.check()
    end = time.time()
    model=opt.model()
    result_x=[]
    result_y=[]
    try:
        for k in range(n):
            result_x.append(int(str(model.evaluate(bl_x[k]))))
            result_y.append(int(str(model.evaluate(bl_y[k]))))
        chip_h_int = int(str(model.evaluate(chip_h)))
    except:
        chip_h_int = 0

    return chip_h_int, result_x, result_y, end-start