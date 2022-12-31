enum PERSON; % set of people to be visited

array[PERSON] of int: duration;    % duration of visit
array[PERSON] of bool: on_weekend; % can the person be visited over weekends
array[PERSON] of int: rank;        % rank of person

array[int,1..2] of PERSON: prec;   % precedences between visits
set of int: PREC = index_set_1of2(prec); 

0..6: starting_day; % which day of the week is day 0 in the schedule
                    % 0 Monday, 1 Tuesday, ..., 5 Saturday, 6 Sunday

% upper bound on the amount of time needed: total duration plus 1 week
% per person who cant be visited on the weekend
int: total = sum(duration) + 7*sum(p in PERSON)(on_weekend[p] = false);
set of int: TIME = 0..total;

array[PERSON] of var TIME: start;

% for multiple modeling
% array[TIME] of var 0..card(PERSON): pers;
% constraint forall(p in PERSON)
            % (forall(t in start[p]..start[p]+duration[p]-1)  
                % (if t<total then pers[t]=p endif));

var TIME: end;
var 0..card(PERSON)^2 : rank_violations;
constraint rank_violations = count(p1, p2 in PERSON where rank[p1]>rank[p2])
                                (start[p1]<start[p2]);

include "disjunctive.mzn";
constraint disjunctive(start,duration);

% precedences
constraint forall(p in index_set_1of2(prec))
        (let {array[1..2] of PERSON : r = row(prec,p)} in start[r[1]]<start[r[2]]);

% weekends
constraint forall(p in PERSON)
    (not on_weekend[p] -> 
        forall(t in start[p]..start[p]+duration[p]-1)((starting_day+t) mod 7 < 5));


constraint end = max(p in PERSON)(start[p]+duration[p]);
solve minimize end + rank_violations;