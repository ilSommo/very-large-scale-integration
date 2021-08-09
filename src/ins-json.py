import json

for i in range(1,11):
    file = 'ins/ins-' + str(i)
    with open(file+'.txt', 'r') as infile:
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
        data = {
            "chip_w": chip_w,
            "n": n,
            "inst_x": inst_x,
            "inst_y": inst_y
        }
    with open(file+'.json', 'w') as outfile:
        json.dump(data, outfile)




