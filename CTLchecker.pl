% For SICStus, uncomment line below: (needed for member/2)
%:- use_module(library(lists)).

% Load model, initial state and formula from file.
verify(Input) :-
    see(Input),  % Opens the specified input file for reading.
    read(T),     % Reads the transition model (T) from the file.
    read(L),     % Reads the labeling (L) from the file.
    read(S),     % Reads the initial state (S) from the file.
    read(F),     % Reads the CTL formula (F) to be checked from the file.
    seen,        % Closes the input file.
    check(T, L, S, [], F).  % Initiates the model checking process with the given inputs.

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists.
% L - The labeling.
% S - Current state.
% U - Currently recorded states.
% F - CTL Formula to check.

% Literals
check(_, L, S, [], X) :- 
    member([S, Labels], L),  
    member(X, Labels).       

check(_, L, S, [], neg(X)) :- 
    member([S, Labels], L), 
    \+ member(X, Labels).  

% And
check(T, L, S, [], and(F, G)) :- 
    check(T, L, S, [], F),  
    check(T, L, S, [], G).  

% Or
check(T, L, S, [], or(F, _)) :- 
    check(T, L, S, [], F).

check(T, L, S, [], or(_, G)) :- 
    check(T, L, S, [], G). 

% AX
check(T, L, S, U, ax(F)) :-
    findall(Next, (member([S, NextStates], T), member(Next, NextStates)), NextStates),  
    forall(member(Next, NextStates), check(T, L, Next, U, F)). 

% EX
check(T, L, S, [], ex(F)) :- 
    member([S, NextStates], T),  
    member(Next, NextStates),   
    check(T, L, Next, [], F).   

% AG
check(_, _, S, U, ag(_)) :- member(S, U).  
check(T, L, S, U, ag(F)) :-
    \+ member(S, U),                     
    check(T, L, S, [], F),            
    findall(Next, (member([S, NextStates], T), member(Next, NextStates)), NextStates),  
    forall(member(Next, NextStates), check(T, L, Next, [S|U], ag(F))).  

% EG
check(_, _, S, U, eg(_)) :- 
    member(S, U).  
check(T, L, S, U, eg(F)) :-
    \+ member(S, U),                       
    check(T, L, S, [], F),                  
    member([S, NextStates], T),         
    member(Next, NextStates),          
    check(T, L, Next, [S|U], eg(F)).     

% AF
check(T, L, S, U, af(F)) :-
  
    \+ member(S, U),
    ( 
      
      check(T, L, S, [], F) ;
      member([S, NextStates], T),
      forall(member(Next, NextStates), check(T, L, Next, [S|U], af(F)))
    ).

% EF
check(T, L, S, U, ef(F)) :-

    \+ member(S, U),
    
    ( % start of OR 
      
      % First condition: Check if the formula F is true in the current state S.
      check(T, L, S, [], F) 

      ; % OR

      % Second condition: Find all next states reachable from the current state S.
      findall(Next, 
            (member([S, NextStates], T), 
            member(Next, NextStates)),  
            NextStates),                
            member(Next, NextStates), 
      check(T, L, Next, [S|U], ef(F)) 

    ). % End of the disjunction
