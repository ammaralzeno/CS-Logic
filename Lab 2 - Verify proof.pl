
verify(InputFileName) :-
    see(InputFileName),                 % Open file for reading
    read(Prems), read(Goal), read(Proof), % Read premises, goal, and proof from the file
    seen,                               % Close the file
    valid_proof(Prems, Goal, Proof).     % Check the validity of the proof



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% goal %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Check that the goal of the proof is the conclusion of the last line in the proof
% and that the last line is not an assumption
valid_goal(Goal, Proof) :-
    last(Proof, [_Row, Goal, Rule]),  
    Rule \= assumption.              


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% valid_proof %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Base case for valid_proof: a proof is valid if it is empty and the last validated line achieves the goal
valid_proof(_Prems, Goal, [], [[_Row, Goal, _Rule]|_Validated]).


% Main function to validate the proof
valid_proof(Prems, Goal, Proof) :-
    valid_goal(Goal, Proof),      
    valid_proof_lines(Prems, Proof, []).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% valid_proof_lines %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The base case for an empty proof (no more lines to validate)
valid_proof_lines(_Prems, [], _ValidatedLines).

% Handling regular proof lines (non-box)
valid_proof_lines(Prems, [ProofLine | RestOfProof], ValidatedLines) :-
    valid_line(Prems, ProofLine, ValidatedLines), % Validate the current line of the proof
    valid_proof_lines(Prems, RestOfProof, [ProofLine | ValidatedLines]). % Recursively validate the rest of the proof


% Extend valid_proof_lines to handle boxes
valid_proof_lines(Prems, [[[Row, Assumption, assumption] | BoxTail] | ProofTail], ValidatedLines) :-
    valid_proof_lines(Prems, BoxTail, [[Row, Assumption, assumption] | ValidatedLines]), % Validate the lines inside the box
    valid_proof_lines(Prems, ProofTail, [[[Row, Assumption, assumption] | BoxTail] | ValidatedLines]). % Continue validating lines after the box


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% find_line %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Helper predicate to find a line in the validated lines, including within boxes
find_line(Nr, [Line|_], Line) :-       % Base case: Line is the first element in the list
    Line = [Nr, _, _].                   
find_line(Nr, [Box|_], Line) :-        % Case for finding a line within a box (nested list)
    is_list(Box),                        
    member(Line, Box),                  
    Line = [Nr, _, _].                   
find_line(Nr, [_|Rest], Line) :-       % Recursive case: Line not found in the first element or first box
    find_line(Nr, Rest, Line).            

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% find_line_in_box %%%%%%%%%%%%%%%%%%%%%%%%%%%

% Helper predicate to find a line in a specific box
find_line_in_box(Start, End, ValidatedLines, [StartStatement, EndStatement]) :-
    member(Box, ValidatedLines),          
    is_list(Box),                         % Check if the current element is a list (box)
    member([Start, StartStatement, _], Box), % Find the start line in the box
    member([End, EndStatement, _], Box).  % Find the end line in the box


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% valid_line %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Implementation for the premise rule
valid_line(Prems, [_Row, Statement, premise], _ValidatedLines) :-
    member(Statement, Prems). 

% Implementation for the copy(x) rule
valid_line(_Prems, [_Row, Statement, copy(X)], ValidatedLines) :-
    member([X, Statement, _], ValidatedLines). 

% Implementation for the andel1(x) rule
valid_line(_Prems, [_Row, Statement1, andel1(X)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, and(Statement1, _), _]). 

% Implementation for the andel2(x) rule
valid_line(_Prems, [_Row, Statement2, andel2(X)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, and(_, Statement2), _]).  

% Implementation for the orint1(x) rule
valid_line(_Prems, [_Row, or(Statement, _), orint1(X)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, Statement, _]). 

% Implementation for the orint2(x) rule
valid_line(_Prems, [_Row, or(_, Statement), orint2(X)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, Statement, _]). 

% Implementation for the orel(x,y,u,v,w) rule
valid_line(_Prems, [_Row, Conclusion, orel(X, Y, U, V, W)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, or(Statement1, Statement2), _]), 
    find_line_in_box(Y, U, ValidatedLines, [Statement1, Conclusion]),  
    find_line_in_box(V, W, ValidatedLines, [Statement2, Conclusion]).  

% Implementation for the impint(x,y) rule, ensuring both x and y are within the same box
valid_line(_Prems, [_Row, imp(Assumption, Conclusion), impint(X, Y)], ValidatedLines) :-
    member(Box, ValidatedLines),
    is_list(Box),                
    member([X, Assumption, assumption], Box), 
    last(Box, [Y, Conclusion, _]).  

% Implementation for the impel(x,y) rule
% Ensuring x is a valid premise and y is an implication that implies the conclusion.
valid_line(_Prems, [_Row, Conclusion, impel(X, Y)], ValidatedLines) :-
    member([X, Premise, _], ValidatedLines), \+ is_list(Premise), 
    member([Y, imp(Premise, Conclusion), _], ValidatedLines).     

% Implementation for the negint(x,y) rule
valid_line(_Prems, [_Row, neg(Assumption), negint(X, Y)], ValidatedLines) :-
    find_line_in_box(X, Y, ValidatedLines, [Assumption, cont]).  

% Implementation for the negel(x,y) rule
valid_line(_Prems, [_Row, cont, negel(X, Y)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, Statement, _]),           
    find_line(Y, ValidatedLines, [Y, neg(Statement), _]).       
 
% Implementation for the contel(x) rule
valid_line(_Prems, [_Row, _Conclusion, contel(X)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, cont, _]).                  

% Implementation for the negnegint(x) rule
valid_line(_Prems, [_Row, neg(neg(Statement)), negnegint(X)], ValidatedLines) :-
    member([X, Statement, _], ValidatedLines), \+ is_list(Statement).  

% Implementation for the negnegel(x) rule
valid_line(_Prems, [_Row, Statement, negnegel(X)], ValidatedLines) :-
    member([X, neg(neg(Statement)), _], ValidatedLines), \+ is_list(neg(neg(Statement))). 

% Implementation for the mt(x,y) rule
valid_line(_Prems, [_Row, neg(Antecedent), mt(X, Y)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, imp(Antecedent, Consequent), _]),  
    find_line(Y, ValidatedLines, [Y, neg(Consequent), _]).               

% Implementation for the pbc(x,y) rule
valid_line(_Prems, [_Row, Conclusion, pbc(X, Y)], ValidatedLines) :-
    find_line_in_box(X, Y, ValidatedLines, [neg(Conclusion), cont]).

% Implementation for the lem rule
valid_line(_Prems, [_Row, or(Statement, neg(Statement)), lem], _ValidatedLines). 

% Implementation for andint. Considers the scope of assumptions and boxes 
valid_line(_Prems, [_Row, and(Statement1, Statement2), andint(X, Y)], ValidatedLines) :-
    find_line(X, ValidatedLines, [X, Statement1, _]),           % Find Statement1 on line X
    find_line(Y, ValidatedLines, [Y, Statement2, _]),           % Find Statement2 on line Y
    % Check the scope of assumptions and boxes for X and Y
    (
        \+ (member(Box, ValidatedLines), is_list(Box), (member([X, _, _], Box); member([Y, _, _], Box)))
    ;
        member(Box, ValidatedLines), is_list(Box),
        find_line_in_box(X, Y, ValidatedLines, [Statement1, Statement2])
    ;
        (member([X, _, assumption], ValidatedLines), Y > X) ;
        (member([Y, _, assumption], ValidatedLines), X > Y)
    ).


























