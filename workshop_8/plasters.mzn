
int: length; % length of Huang Gai's back
set of int: LENGTH = 1..length;
int: width; % width of Huang Gai's back
set of int: WIDTH = 1..width;

array[LENGTH,WIDTH] of bool: wound; % wound positions
int: total_wounds = sum(array1d(wound));

int: ntypes;  % number of types of plaster
set of int: TYPE = 1..ntypes;
array[TYPE] of int: number;          % number of plaster available
array[TYPE,1..2] of int: dim;        % dimensions of plaster
int: maxdim = max(array1d(dim));
array[TYPE] of int: price;

int: total = sum(number);
set of int: PLASTER = 1..total;
array[TYPE] of int: psum = [ sum(i in 1..t-1)(number[i]) | t in TYPE ];
array[PLASTER] of TYPE: t = [max(t in TYPE)(t*(p > psum[t])) | p in PLASTER];
array[PLASTER] of var LENGTH:  x;
array[PLASTER] of var WIDTH:   y;
enum USAGE = { Long, Wide, Not };
array[PLASTER] of var USAGE:   u;
array[PLASTER] of var 0..length : actual_length = [if u[p]=Long then dim[t[p],1] else 
                                        if u[p]=Wide then dim[t[p],2] else 0
                                        endif endif | p in PLASTER];
array[PLASTER] of var 0..width : actual_width = [if u[p]=Long then dim[t[p],2] else 
                                        if u[p]=Wide then dim[t[p],1] else 0
                                        endif endif | p in PLASTER];
constraint forall(p in PLASTER)(let {
    var int : xend = x[p]+actual_length[p]-1 ; 
    var int : yend = y[p]+actual_width[p]-1 }
    in xend<=length /\ yend<=width);

predicate is_covered(var int : l, var int :w) =
    exists(p in PLASTER where u[p]!=Not)
            (x[p]<=l /\ x[p]+actual_length[p]-1>=l /\ 
            y[p]<=w /\ y[p]+actual_width[p]-1>=w);

constraint forall(l in LENGTH, w in WIDTH)
        (wound[l,w]->is_covered(l,w));

array[int,int] of var bool : is_covered = 
        array2d(LENGTH, WIDTH,[exists(p in PLASTER where u[p]!=Not)
            (x[p]<=i /\ x[p]+actual_length[p]-1>=i /\ 
            y[p]<=j /\ y[p]+actual_width[p]-1>=j) | i in LENGTH, j in WIDTH]);

% output["\(fix(x[i])) \(fix(y[i])) \(fix(actual_length[i])) \(fix(actual_width[i])) \n"| i in PLASTER where fix(u[i])!=Not];
% output["\(wound[i,j]/\(not is_covered[i,j])) " | i in LENGTH, j in WIDTH];

include "diffn.mzn";
constraint diffn(x,y,actual_length, actual_width);

array[TYPE] of var 0..max(number): used;
constraint forall (tp in TYPE)(used[tp]=count(p in PLASTER)(t[p]=tp /\ u[p]!=Not));
constraint used[2] <= number[2] - 1 
        /\ used[3] <= number[3] - 1
        /\ used[4] <= number[4] - 1 -> used[5] = 0;

var int : cost ;
constraint cost=sum(t in TYPE)(used[t] * price[t]);
solve minimize cost;














% array[int, int] of int : rect_size =array2d(1..2*ntypes,1..2,[[dim[i,1],dim[i,2],dim[i,2],dim[i,1]][ind] | i in TYPE, ind in 1..4]);
% array[int, int] of int : rect_offset =array2d(1..2*ntypes,1..2,[0 | i in 1..4*ntypes]);
% array[int] of set of int : shape = [{i} | i in 1..2*ntypes];
% array[TYPE] of set of int : valid_shapes = [{i,i+1} | i in TYPE];

% array[PLASTER,1..2] of var int : pos ;
% array[PLASTER] of var int : kind ;

% constraint geost(2, rect_size, rect_offset, shape, pos, kind) ;
% constraint forall(p in PLASTER)(kind[p] in valid_shapes[t[p]]);