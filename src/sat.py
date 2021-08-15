from z3 import *
import sys
import json

file = str(sys.argv[1])

opt = Optimize()

with open('ins/ins-' +file+'.json', 'r') as infile:
    data = json.load(infile)


chip_w = data['chip_w']
n = data['n']
inst_x = data['inst_x']
inst_y = data['inst_y']
max_h = sum(inst_y) - min(inst_y)

bl_x = IntVector('bl_x', n)
bl_y = IntVector('bl_y', n)
b = [[Int("b_%s_%s" % (i, j)) for j in range(max_h) ] for i in range(chip_w)]

for x, y in zip(bl_x, bl_y):
    opt.add(x >=0)
    opt.add(x <= chip_w - min(inst_x))
    opt.add(y >=0)
    opt.add(y <= chip_w - min(inst_y))

for row in b:
    for elem in row:
        opt.add(elem >= 0)
        opt.add(elem <= n)

for i in range(chip_w):
    for j in range(max_h):
        for v in range(n):
            opt.add((b[i][j] == v) == And(i>bl_x[v], i<=bl_x[v]+inst_x[v], j>bl_y[v], j<=bl_y[v]+inst_y[v]))

for i in range(n):
    opt.add(bl_x[i]+inst_x[i] <= chip_w)

chip_h = Int('chip_h')

for i in range(n):
    opt.add(chip_h>=bl_y[i] + inst_y[i])

opt.minimize(chip_h)
opt.check()
model=opt.model()
result_x=[]
result_y=[]
for i in range(n):
    result_x.append(model.evaluate(bl_x[i]))
    result_y.append(model.evaluate(bl_y[i]))

output = str(chip_w) + " " + str(model.evaluate(chip_h)) + "\n" + str(n) + "\n"
for i in range(n):
    output += str(inst_x[i]) + " " + str(inst_y[i]) + " " + str(result_x[i]) + " " + str(result_y[i]) + "\n"

with open('out/out-'+file+'-sat.txt', 'w') as outfile:
    outfile.write(output)
