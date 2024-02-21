% For SICStus, uncomment line below: (needed for member/2)
%:- use_module(library(lists)).

% Load model, initial state and formula from file.
verify(Input) :-
    see(Input),  
    read(T),     
    read(L),   
    read(S),     
    read(F),     
    seen,      
    check(T, L, S, [], F).  % Initiate the model checking process

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists.
% L - The labeling.
% S - Current state.
% U - Currently recorded states.
% F - CTL Formula to check.

% Literals - find labeling list for current state, and check if X is in the list.
check(_, L, S, [], X) :- 
    member([S, Labels], L),  
    member(X, Labels).       

check(_, L, S, [], neg(X)) :- 
    member([S, Labels], L),  
    \+ member(X, Labels).    % Checks that literal X is not in the list

% And - check if F and G hold
check(T, L, S, [], and(F, G)) :- 
    check(T, L, S, [], F),  
    check(T, L, S, [], G).  

% Or - check if F or G hold
check(T, L, S, [], or(F, _)) :- 
    check(T, L, S, [], F). 

check(T, L, S, [], or(_, G)) :- 
    check(T, L, S, [], G).

% AX (For All Next) - For all next states, F holds 
check(T, L, S, U, ax(F)) :- 
    findall(Next, (member([S, NextStates], T), member(Next, NextStates)), NextStates), % find all next states from S
    forall(member(Next, NextStates), check(T, L, Next, U, F)). % check F in all next states of S

% EX (Exists Next) - There exists at least one next state in which F holds
check(T, L, S, [], ex(F)) :-  % find next states for S, select a next state and check if F holds in that state
    member([S, NextStates], T),  
    member(Next, NextStates), 
    check(T, L, Next, [], F).    

% AG (For All Globaly) -  In all possible paths and in all states along those paths, F holds.
check(_, _, S, U, ag(_)) :- member(S, U).  % base case: if the current state has been visited, AG is satisfied
check(T, L, S, U, ag(F)) :-                
    \+ member(S, U),                       % otherwise if it has not been visited
    check(T, L, S, [], F),                 % check F in current state
    findall(Next, (member([S, NextStates], T), member(Next, NextStates)), NextStates),  % find all next states from S and recursively check AG in all next states
    forall(member(Next, NextStates), check(T, L, Next, [S|U], ag(F))).  

% EG (Exists Globally) - There exists a path where in all states along that path, F hold.
check(_, _, S, U, eg(_)) :-  % base case: if the current state has been visited EG is satisfied
    member(S, U).  
check(T, L, S, U, eg(F)) :-  % check F in current state, find next states, recursively check EG in next state
    \+ member(S, U),                     
    check(T, L, S, [], F),          
    member([S, NextStates], T),         
    member(Next, NextStates),              
    check(T, L, Next, [S|U], eg(F)).        

% AF (For All Finally) - In all possible paths there is some state along those paths where F holds.
check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    ( % OR condition
      check(T, L, S, [], F) % check if F holds in current state
      ; 
      member([S, NextStates], T), % find all next states from S, check AF and add to visited states
      forall(member(Next, NextStates), check(T, L, Next, [S|U], af(F)))
    ).

% EF (Exists Finally) - There exists a path where at some state along that path, F holds.
check(T, L, S, U, ef(F)) :-
    \+ member(S, U),
    ( % start of OR 
      check(T, L, S, [], F) % check if F holds in current state
      ;
      findall(Next, (member([S, NextStates], T), member(Next, NextStates)),  NextStates),  % find all next states reachable from the current state S      
      member(Next, NextStates), 
      check(T, L, Next, [S|U], ef(F)) 
    ). 
