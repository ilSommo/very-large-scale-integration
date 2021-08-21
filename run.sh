#!/bin/bash
MAX=$1
for file in $(seq 1 $MAX)
do
    python src/ins-json.py $file
	minizinc --solver Gecode src/m1.mzn ins/ins-$file.json -o out/out-$file-cp.txt --soln-sep "" --search-complete-msg "" --solver-time-limit 300000
    python src/printer.py out/out-$file-cp
    python src/sat.py $file
    python src/printer.py out/out-$file-sat
    rm ins/ins-$file.json
done