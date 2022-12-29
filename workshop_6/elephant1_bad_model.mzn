int: T; % maximum time allowed;
set of int: TIME = 1..T;
int: G; % number of guards
int: F; 
int: W;

array[TIME] of var -F..F: move_food;      % move food +ve bank to boat, -ve boat to bank
array[TIME] of var -W..W: move_water;     % move water +ve bank to boat, -ve boat to bank
var 1..T: end;                            % end time;

array[TIME] of var 0..F: food_on_bank;
array[TIME] of var 0..F: food_on_boat;
constraint food_on_bank[1] = F;
constraint forall(t in TIME)(food_on_bank[t]+food_on_boat[t]=F);
constraint forall(t in 1..T-1)(food_on_bank[t+1]=food_on_bank[t]-move_food[t]);

array[TIME] of var 0..W: water_on_bank;
array[TIME] of var 0..W: water_on_boat;
constraint water_on_bank[1] = W;
constraint forall(t in TIME)(water_on_bank[t]+water_on_boat[t]=W);
constraint forall(t in 1..T-1)(water_on_bank[t+1]=water_on_bank[t]-move_water[t]);


array[TIME] of var bool : elephant_on_boat;
constraint elephant_on_boat[1]=false;
constraint forall(t in 1..T-1)
    (   
        (elephant_on_boat[t+1] = (elephant_on_boat[t] /\ not go_to_bank(t)) \/ go_to_boat(t))
    );

predicate go_to_boat(int : t) = 
    (not elephant_on_boat[t]) /\
    food_on_boat[t] = water_on_boat[t] /\
    food_on_boat[t] > food_on_bank[t] /\
    water_on_boat[t] > water_on_bank[t] ;

predicate go_to_bank(int : t) = 
    elephant_on_boat[t] /\
    food_on_bank[t] = water_on_bank[t] /\
    food_on_boat[t] < food_on_bank[t] /\
    water_on_boat[t] < water_on_bank[t] ;

predicate eats_or_drinks(int : t) =
    (
        elephant_on_boat[t] /\
        (
            (food_on_boat[t] = 0 /\ water_on_boat[t] > 0) \/
            (water_on_boat[t] = 0 /\ food_on_boat[t] > 0)
        ) /\
        not go_to_bank(t)
    ) 
    \/
    (
        (not elephant_on_boat[t]) /\
        (
            (food_on_bank[t] = 0 /\ water_on_bank[t] > 0) \/
            (water_on_bank[t] = 0 /\ food_on_bank[t] > 0)
        ) /\
        not go_to_boat(t)
    ) ;

constraint forall(t in TIME)
    (
        (move_food[t] * move_water[t] >= 0) /\
        (abs(move_food[t] + move_water[t]) <= G) /\
        (not eats_or_drinks(t))
    );

constraint forall(t in TIME where t>end)
    (move_food[t]=0 /\ move_water[t]=0 /\ 
    food_on_boat[t]=0 /\ water_on_boat[t]=0);

constraint elephant_on_boat[end+1]=true;

solve minimize end;