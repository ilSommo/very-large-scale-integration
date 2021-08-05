include "globals.mzn";

int: chip_w; % Width of the chip
int: max_h = (sum(i in 1..n)(inst_y[i])) - min(inst_y); % Maximum height of the chip
int: n; % Number of circuits
array[1..n] of int: inst_x; % Horizontal dimension of the i-th piece
array[1..n] of int: inst_y; % Vertical dimension of the i-th piece

% Primal problem: the i-th element of each array contains one (X/Y) coordinate of the bottom-left corner of the i-th piece
array[1..n] of var 0..(chip_w - min(inst_x)): bl_x;
array[1..n] of var 0..max_h: bl_y;
% Dual problem: each cell in the 2D grid contains the number of the piece it belongs
array[1..chip_w, 1..max_h] of var 0..n: B;

% Channelling constraint
constraint forall(i in 1..chip_w, j in 1..max_h, v in 1..n) (
  B[i, j] = v <-> i > bl_x[v] /\ i <= bl_x[v] + inst_x[v] /\ j > bl_y[v] /\ j <= bl_y[v] + inst_y[v]
);

% Non overlapping constraint
constraint forall(i,j in 1..n where i<j) (
  min(bl_x[i] + inst_x[i],bl_x[j] + inst_x[j]) <= max(bl_x[i],bl_x[j]) \/
  min(bl_y[i] + inst_y[i],bl_y[j] + inst_y[j]) <= max(bl_y[i],bl_y[j])
);

% Boundaries consistency constraint
constraint forall(i in 1..n) (
  bl_x[i] + inst_x[i] <= chip_w
);

% Implied constraints
constraint forall(i in 1..chip_w) (
  among([B[i, j] | j in 1..max_h], 1..n) <= chip_w % returns the number of variables in B[i,:] that takes one of the values in 1..n
);
constraint forall(j in 1..max_h) (
  among([B[i, j] | i in 1..chip_w], 1..n) <= max_h % returns the number of variables in B[:,j] that takes one of the values in 1..n
);

% Cumulative constraint (fundamental for the minimization of the height)
constraint cumulative(bl_y, inst_y, inst_x, chip_w);
constraint cumulative(bl_x, inst_x, inst_y, max_h);

% Symmetry breaking ('greatereq' because upper tiles are 0's, so we want lower tiles to be bigger)
constraint symmetry_breaking_constraint(
  lex_greatereq(array1d(B), [B[i, j] | i in reverse(1..chip_w), j in 1..max_h]) % vertical flip
  /\ lex_greatereq(array1d(B), [B[i, j] | i in 1..chip_w, j in reverse(1..max_h)]) % horizontal flip
  /\ lex_greatereq(array1d(B), [B[i, j] | i in reverse(1..chip_w), j in reverse(1..max_h)]) % vertical + horizontal flip
);

% chip_h as objective function
var int: chip_h = max(i in 1..n)(bl_y[i] + inst_y[i]);

solve minimize chip_h;

output ["Chip width: \(chip_w)\n"] ++ 
       ["Chip height: \(chip_h)\n"] ++
       ["Corners:\n"] ++ ["W:\(inst_x[i]) H:\(inst_y[i]) -> (\(bl_x[i]),\(bl_y[i]))\n" | i in 1..n]
%       ["B :\n"] ++ ["\(show(B[i,j]) ++ if j mod max_h == 0 then "\t" else "\n" endif)" |i in 1..chip_w, j in 1..max_h]