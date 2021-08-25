__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


import time

import z3

def smt(data, timeout, rotation):

    chip_w = data['chip_w']
    n = data['n']
    inst_x =  data['inst_x']
    inst_y = data['inst_y']
    min_h = data['min_h']
    max_h = data['max_h']
    min_index = data['min_index']

    opt = z3.Optimize()
    opt.set('timeout', timeout*1000)
    chip_h = z3.Int("chip_h")

    bl_x = z3.IntVector("bl_x", n)
    bl_y = z3.IntVector("bl_y", n)
    
    if rotation == True:
        rotated = z3.BoolVector("rotated", n)
        new_inst_x = [z3.If(rotated[k], inst_y[k], inst_x[k]) for k in range(n)]
        new_inst_y = [z3.If(rotated[k], inst_x[k], inst_y[k]) for k in range(n)]
    else:
        new_inst_x = inst_x
        new_inst_y = inst_y


    for k in range(n):
        opt.add(bl_x[k] >=0)
        opt.add(bl_x[k]+new_inst_x[k] <= chip_w)
        opt.add(bl_y[k] >=0)
        opt.add(bl_y[k] + new_inst_y[k]<=chip_h)
        for l in range(n):
            if k != l:
                opt.add(z3.Or((bl_x[l]+new_inst_x[l] <= bl_x[k]),(bl_x[l] >= bl_x[k]+new_inst_x[k]),(bl_y[l]+new_inst_y[l] <= bl_y[k]),(bl_y[l] >= bl_y[k]+new_inst_y[k])))

    opt.add(chip_h <= max_h)
    opt.add(chip_h >= min_h)
    
    # symmetry breaking
    opt.add(z3.And(((2*bl_x[min_index]+new_inst_x[min_index])<=chip_w),((2*bl_y[min_index]+new_inst_y[min_index])<=chip_h)))

    opt.minimize(chip_h)
    start = time.time() 
    check = opt.check()
    end = time.time()
    model=opt.model()
    result_x=[]
    result_y=[]
    result_inst_x=[]
    result_inst_y=[]
    if check == z3.sat:
        for k in range(n):
            result_x.append(int(str(model.evaluate(bl_x[k]))))
            result_y.append(int(str(model.evaluate(bl_y[k]))))
            result_inst_x.append(int(str(model.evaluate(new_inst_x[k]))) if rotation == True else new_inst_x[k])
            result_inst_y.append(int(str(model.evaluate(new_inst_y[k]))) if rotation == True else new_inst_y[k])
        chip_h_int = int(str(model.evaluate(chip_h)))
    else:
        chip_h_int = None

    return chip_h_int, result_x, result_y, result_inst_x, result_inst_y, end-start