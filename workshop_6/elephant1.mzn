int: T; % maximum time allowed;
set of int: TIME = 1..T;
set of int: TIME0 = 0..T;
int: G; % number of guards
int: F; 
int: W;

array[TIME] of var -F..F: move_food;      % move food +ve bank to boat, -ve boat to bank
array[TIME] of var -W..W: move_water;     % move water +ve bank to boat, -ve boat to bank
var 1..T-1: end;                            % end time;

array[TIME0] of var 0..F: food_on_boat;
array[TIME0] of var 0..W: water_on_boat;
enum POS = {bank, boat};
array[TIME0] of var POS : elephant_pos;

constraint elephant_pos[0] = bank ;
constraint food_on_boat[0] = 0 ;
constraint water_on_boat[0] = 0 ;

predicate move(var 0..F : food_here, var 0..W : water_here) =
    let {var 0..F : food_there = F - food_here;
        var 0..W : water_there = W - water_here} in
        (water_there=food_there /\ water_there>water_here /\ food_there>food_here);

predicate eats_or_drinks(var 0..F : food_here, var 0..W : water_here) =
    (
        (food_here > 0 /\ water_here = 0 \/ food_here = 0 /\ water_here > 0) /\
        not move(food_here, water_here)
    ) ;

% resources
constraint forall(t in TIME)
    (
        food_on_boat[t] = food_on_boat[t-1] + move_food[t] /\
        water_on_boat[t] = water_on_boat[t-1] + move_water[t] /\
        move_food[t]*move_water[t]>=0 /\
        abs(move_food[t] + move_water[t]) <= G /\
        let {var 0..F : food_here = if elephant_pos[t]=boat then food_on_boat[t] else F-food_on_boat[t] endif ;
            var 0..F : water_here = if elephant_pos[t]=boat then water_on_boat[t] else W-water_on_boat[t] endif} in
        not eats_or_drinks(food_here, water_here)
    );


% elephant position
constraint forall(t in TIME)
    (elephant_pos[t] = 
        if (
            (elephant_pos[t-1]= bank /\ move(F-food_on_boat[t-1],W-water_on_boat[t-1]))
            \/ elephant_pos[t-1]= boat /\ not move(food_on_boat[t-1],water_on_boat[t-1]) 
        ) then boat else bank endif);


% end conditions
constraint forall(t in TIME where t>end)
    (food_on_boat[t] + water_on_boat[t] + abs(move_food[t]) + abs(move_water[t]) = 0);

constraint elephant_pos[end]=boat;

solve minimize end;