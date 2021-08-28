__version__ = '1.0.0-rc.4'
__author__ = 'Giacomo Berselli, Martino Pulici'


from minizinc import Model, Solver

from vlsi.utilities.plots import plot_times
from vlsi.utilities.preprocessing import preprocessing
from vlsi.utilities.wrappers import cp_wrapper, sat_wrapper, smt_wrapper

REPORT = True

TIMEOUT_CP_NORMAL = 300
TIMEOUT_CP_ROTATION = 300
TIMEOUT_SAT_NORMAL = 300
TIMEOUT_SAT_ROTATION = 300
TIMEOUT_SMT_NORMAL = 300
TIMEOUT_SMT_ROTATION = 300


LIST_CP_NORMAL = list(range(1,39+1))
LIST_CP_ROTATION = list(range(1,21+1))+[23,24]+list(range(26,29+1))+[31]+list(range(33,36+1))
LIST_SAT_NORMAL = range(1,10+1)
LIST_SAT_ROTATION = range(1,10+1)
LIST_SMT_NORMAL = range(1,40+1)
LIST_SMT_ROTATION = range(1,40+1)

timeouts = [TIMEOUT_CP_NORMAL,TIMEOUT_CP_ROTATION,TIMEOUT_SAT_NORMAL,TIMEOUT_SAT_ROTATION,TIMEOUT_SMT_NORMAL,TIMEOUT_SMT_ROTATION]
lists = [LIST_CP_NORMAL,LIST_CP_ROTATION,LIST_SAT_NORMAL,LIST_SAT_ROTATION,LIST_SMT_NORMAL,LIST_SMT_ROTATION]

mins = []
maxs = []
for i in range(6):
    if timeouts[i] == 0:
        lists[i] = []
    else:
        mins.append(min(lists[i]))
        maxs.append(max(lists[i]))

# Minimum instance
min_ins = min(mins)
max_ins = max(maxs)

# Time lists
times_cp_normal = []
times_cp_rotation = []
times_sat_normal = []
times_sat_rotation = []
times_smt_normal = []
times_smt_rotation = []

times_null = []

# Minizinc solver
solver = Solver.lookup("chuffed")

# Enter if normal configuration is enabled
if TIMEOUT_CP_NORMAL !=0:
    # Minizinc normal model
    model_normal = Model("src/cp/cp_normal.mzn")

# Enter if rotation configuration is enabled
if TIMEOUT_CP_ROTATION !=0:
    # Minizinc rotation model
    model_rotation = Model("src/cp/cp_rotation.mzn")

# Cycle instances
for i in range(min_ins, max_ins + 1):
    # File name
    file = str(i)
    # Data dictionary
    data = preprocessing(file)

    if i in lists[0]:
        # Solve normal CP
        time = cp_wrapper(
            file,
            data,
            solver,
            model_normal,
            timeouts[0],
            rotation=False)
        times_cp_normal.append(time)
    else:
        times_cp_normal.append(0)

    if i in lists[1]:
        # Solve rotation CP
        time = cp_wrapper(
            file,
            data,
            solver,
            model_rotation,
            timeouts[1],
            rotation=True)
        times_cp_rotation.append(time)
    else:
        times_cp_rotation.append(0)

    if i in lists[2]:
        # Solve normal SAT
        time = sat_wrapper(file, data, timeouts[2], rotation=False)
        times_sat_normal.append(time)
    else:
        times_sat_normal.append(0)

    if i in lists[3]:
        # Solve rotation CP
        time = sat_wrapper(file, data, timeouts[3], rotation=True)
        times_sat_rotation.append(time)
    else:
        times_sat_rotation.append(0)

    if i in lists[4]:
        # Solve normal SMT
        time = smt_wrapper(file, data, timeouts[4], rotation=False)
        times_smt_normal.append(time)
    else:
        times_smt_normal.append(0)

    if i in lists[5]:
        # Solve rotation SMT
        time = smt_wrapper(file, data, timeouts[5], rotation=True)
        times_smt_rotation.append(time)
    else:
        times_smt_rotation.append(0)

    times_null.append(0)

# Time limit
top = max(timeouts)
# Computation times
times = [
    times_cp_normal,
    times_cp_rotation,
    times_sat_normal,
    times_sat_rotation,
    times_smt_normal,
    times_smt_rotation]
# Plot computation times
if timeouts[0] or timeouts[2] or timeouts[4]:
    normal = True
if timeouts[1] or timeouts[3] or timeouts[5]:
    rotation = True
if REPORT == False:
    plot_times(times, min_ins, max_ins, top, normal, rotation,'')
else:
    plot_times(times, min_ins, max_ins, top, normal, rotation,'')
    plot_times([times_cp_normal,times_cp_rotation,times_null,times_null,times_null,times_null], min_ins, max_ins, top, True, True,'-cp')
    plot_times([times_null,times_null,times_sat_normal,times_sat_rotation,times_null,times_null], min_ins, max_ins, top, True, True,'-sat')
    plot_times([times_null,times_null,times_null,times_null,times_smt_normal,times_smt_rotation], min_ins, max_ins, top, True, True,'-smt')
    plot_times([times_cp_normal,times_null,times_sat_normal,times_null,times_smt_normal,times_null], min_ins, max_ins, top, True, False,'-normal')
    plot_times([times_null,times_cp_rotation,times_null,times_sat_rotation,times_null,times_smt_rotation], min_ins, max_ins, top, False, True,'-rotation')
