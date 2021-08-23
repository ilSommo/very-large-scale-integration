include "globals.mzn";
% include "chuffed.mzn"; % for LNS

int: chip_w; % Width of the chip
int: n; % Number of circuits
set of int: RANGE = 1..n;
array[RANGE] of int: inst_x; % Horizontal dimension of the i-th piece
array[RANGE] of int: inst_y; % Vertical dimension of the i-th piece
int: max_h = sum(i in RANGE)(inst_y[i]); % Maximum height of the chip
int: min_h = (sum(i in RANGE)(inst_x[i]*inst_y[i])) div chip_w;

% Primal problem: the i-th element of each array contains one (X/Y) coordinate of the bottom-left corner of the i-th piece
array[RANGE] of var 0..(chip_w - min(inst_x)): bl_x;
array[RANGE] of var 0..(max_h - min(inst_y)): bl_y;
% Dual problem: each cell in the 2D grid contains the number of the piece it belongs
% array[1..chip_w, 1..max_h] of var 0..n: B;

% Channelling constraint
% constraint forall(i in 1..chip_w, j in 1..max_h, v in RANGE) (
%   B[i, j] = v <-> i > bl_x[v] /\ i <= bl_x[v] + inst_x[v] /\ j > bl_y[v] /\ j <= bl_y[v] + inst_y[v]
% %   i > bl_x[v] /\ i <= bl_x[v] + inst_x[v] /\ j > bl_y[v] /\ j <= bl_y[v] + inst_y[v] -> B[i,j] = v 
% );

% Non overlapping constraint (v1)
% constraint forall(i,j in RANGE where i<j) (
%   min(bl_x[i] + inst_x[i],bl_x[j] + inst_x[j]) <= max(bl_x[i],bl_x[j]) \/
%   min(bl_y[i] + inst_y[i],bl_y[j] + inst_y[j]) <= max(bl_y[i],bl_y[j])
% );

% No-overlapping constraint (v2) (better not use OR) (P.1)
constraint diffn(bl_x, bl_y, inst_x, inst_y);

% constraint disjunctive([disjunctive([bl_x[i] | i in RANGE], [inst_x[i] | i in RANGE])],
%                        [disjunctive([bl_y[i] | i in RANGE], [inst_y[i] | i in RANGE])]);

% Boundaries consistency constraint (P.1)
constraint forall(i in RANGE) (
  bl_x[i] + inst_x[i] <= chip_w /\ bl_y[i] + inst_y[i] <= max_h
);

% Implied constraints
% constraint forall(i in 1..chip_w) (
%   among([B[i, j] | j in 1..max_h], RANGE) <= chip_w % returns the number of variables in B[i,:] that takes one of the values in RANGE
% );
% constraint forall(j in 1..max_h) (
%   among([B[i, j] | i in 1..chip_w], RANGE) <= max_h % returns the number of variables in B[:,j] that takes one of the values in RANGE
% );

% Cumulative constraint (fundamental for the minimization of the height) (P.2)
constraint cumulative(bl_y, inst_y, inst_x, chip_w);
constraint cumulative(bl_x, inst_x, inst_y, max_h);

% Symmetry breaking ('greatereq' because upper tiles are 0's, so we want lower tiles to be bigger)
% constraint symmetry_breaking_constraint(
%   lex_greatereq(array1d(B), [B[i, j] | i in reverse(1..chip_w), j in 1..max_h]) % vertical flip
%   /\ lex_greatereq(array1d(B), [B[i, j] | i in 1..chip_w, j in reverse(1..max_h)]) % horizontal flip
%   /\ lex_greatereq(array1d(B), [B[i, j] | i in reverse(1..chip_w), j in reverse(1..max_h)]) % vertical + horizontal flip
% );

% chip_h as objective function
var min_h..max_h: chip_h = max(i in RANGE)(bl_y[i] + inst_y[i]);

% Parameters to control the search heuristic and restart strategy
int: search_type = 2;
int: restart_type = 4;

ann: search_ann = 
  if search_type == 1 then int_search([chip_h], input_order, indomain_min)
  elseif search_type == 2 then int_search([chip_h], first_fail, indomain_min)
  elseif search_type == 3 then int_search([chip_h], dom_w_deg, indomain_min)
  elseif search_type == 4 then int_search([chip_h], input_order, indomain_random)
  elseif search_type == 5 then int_search([chip_h], first_fail, indomain_random)
  else int_search([chip_h], dom_w_deg, indomain_random)
  endif;

ann: restart_ann =
  if restart_type == 1 then restart_constant(750)
  elseif restart_type == 2 then restart_linear(20)
  elseif restart_type == 3 then restart_geometric(1.5, 500)
  else restart_luby(250)
  endif;

% solve :: search_ann :: restart_ann :: relax_and_reconstruct([chip_h], 70) minimize chip_h;
solve :: search_ann :: restart_ann minimize chip_h;
% solve minimize chip_h;


% output ["Chip width: \(chip_w)\n"] ++ 
%       ["Chip height: \(chip_h)\n"] ++
%       ["Corners:\n"] ++ ["W:\(inst_x[i]) H:\(inst_y[i]) -> (\(bl_x[i]),\(bl_y[i]))\n" | i in RANGE]
%       ["B :\n"] ++ ["\(show(B[i,j]) ++ if j mod max_h == 0 then "\t" else "\n" endif)" |i in 1..chip_w, j in 1..max_h]

% output ["\(chip_w) \(chip_h)\n"] ++
%       ["\(n)\n"] ++
%       ["\(inst_x[i]) \(inst_y[i]) \(bl_x[i]) \(bl_y[i])\n" | i in RANGE]