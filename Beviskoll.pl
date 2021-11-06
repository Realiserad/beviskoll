% Validation of proof in natural deduction.
% Bastian Fredriksson 3/11-13
% Tested with swipl 6.2.6
% http://www.csc.kth.se/utbildning/kth/kurser/DD1350/logik13/labbar/labb1/labb1.pdf

% Compile with qsave_program('Beviskoll.exe', [goal(main), stand_alone(true)]).
main:-
	write('Beviskoll v3.1 (c) Bastian Fredriksson'), nl
	write('Verify proofs in natural deduction.'), nl,
	write('Do -? help for instructions.'), nl.

help:-
	write('Create a proof and save as file.txt'), nl,
	write('then do ?- verify(\'file.txt\')'), nl,
	write('To perform a batch test, compress all'), nl
	write('files in tests.zip and run -? test.'), nl
	write('Name all files that you want to check'), nl
	write('for validity with file names starting'), nl
	write('with lowercase v, i.e valid01, valid02...'), nl.

% Run all test cases in tests.zip
test:-
	make_directory('./tests'),
	archive_extract('tests.zip', './tests', []),
	directory_files('./tests', DirectoryFiles),
	subtract(DirectoryFiles, [.,..], Files),
	run_tests(Files),
	delete_directory_and_contents('./tests').
	
test:- delete_directory_and_contents('./tests'), fail.

run_tests([]):-	write('All tests passed!'), nl.

run_tests([File|Files]):-
	sub_atom(File, 0, 1, _, v),
	string_to_atom('./tests/', Dir),
	atom_concat(Dir, File, Path),
	write('Testing valid proof: '), write(File), write('...'), nl,
	verify(Path),
	run_tests(Files).
	
run_tests([File|Files]):-
	string_to_atom('./tests/', Dir),
	atom_concat(Dir, File, Path),
	write('Testing invalid proof: '), write(File), write('...'), nl,
	\+verify(Path),
	run_tests(Files).
	
% Read premises, goal and proof from file.
verify(File):-
	see(File),
	read(Prems), read(Goal), read(Proof),
	seen,
	\+empty(Proof),
	check_goal(Prems, Goal),
	check_conclusion(Proof, Goal), !,
	verify_proof(Prems, Goal, [], Proof, Proof).

% Check if the proof is empty.
empty([]).

% Make sure the proof ends with goal as formula, fail if not
check_conclusion(Proof, Goal):-
	reverse(Proof, [[_, Goal, _]|_]).

% Warn if the goal is one of the premises.
check_goal(Prems, Goal):-
	\+member(Goal, Prems);
	print('WARNING! Goal is a premise, proof is obsolete.'), nl.

% Verify a proof in natural deduction. Please note the cuts, it
% is important to cut all branches that verify_proof might leave
% behind. If we fail in one branch (one row in the proof is incorrect)
% then the whole proof is incorrect.
% verify_proof(+Premises, +Goal, +RowsChecked, +RowsNotChecked, +AllRows)

% No rows left to check.
verify_proof(_, _, _, [], _).

% Open a box, make sure that the first row contains an assumption.
verify_proof(Prems, Goal, RowsChecked, [[[Index, A, assumption]|Box]|Rest], Proof):-
	!,
	% Verify the rest of the proof first, then verify the box.
	verify_proof(Prems, Goal, RowsChecked, Rest, Proof), 
	!,
	verify_proof(Prems, Goal, [[Index, A, assumption]|RowsChecked], Box, Proof).

% An assumption is made without opening a box, invalid proof.
verify_proof(_, _, _, [[_, _, assumption]|_], _):- !, fail.

% A box is opened but it contains nothing, warn.
verify_proof(Prems, Goal, RowsChecked, [[]|RowsNotChecked], Proof):-
	print('WARNING! Empty box detected.'), nl, 
	!,
	verify_proof(Prems, Goal, RowsChecked, RowsNotChecked, Proof).

% Inspect next row in the box.
verify_proof(Prems, Goal, RowsChecked, [[Index, Formula, Rule]|Rest], Proof):-
	!,
	check_rule(Proof, RowsChecked, Prems, Formula, Rule, Index),
	% Inspect the rest of the proof.
	verify_proof(Prems, Goal, [[Index, Formula, Rule]|RowsChecked], Rest, Proof).

% Extract formula and rule with index Index from a given proof table.
% get_line(+ProofTable, +Index, -Formula, -Rule)

% Proof table is empty.
get_line([], _, _, _):- !, fail.

% First row in box matches Index.
get_line([[[Index, Formula, Rule]|_]|_], Index, Formula, Rule).

% Look through the box or the rest of the proof.
get_line([[_|Box]|Rest], Index, Formula, Rule):-
	get_line(Box, Index, Formula, Rule);
	get_line(Rest, Index, Formula, Rule).

% Next row in proof table matches Index.
get_line([[Index, Formula, Rule]|_], Index, Formula, Rule).

% Look through the rest of the proof.
get_line([_|Rest], Index, Formula, Rule):-
	get_line(Rest, Index, Formula, Rule).
	
% This predicate will succeed if I1 and I2 are the first and 
% last row indexes of two rows in the same box.
same_box(AllRows, I1, I2, CurrIndex):-
	I1=<I2,
	check_indexes(AllRows, I1, I2, CurrIndex).

% No appropriate box found.
check_indexes([], _, _, _):- fail.

% Next element in proof table is a box and first index match.
check_indexes([[[I1, _, _]|T]|Rest], I1, I2, CurrIndex):-
	% Check if second index matches end of box.
	reverse([[I1, _, _]|T], [[I2, _, _]|_]),
	inside_scope(Rest, CurrIndex).

% Next element in proof table is a box, but first index does
% not match, search the box and maybe the rest of the proof.
check_indexes([[[_, _, _]|RestOfBox]|RestOfProof], I1, I2, CurrIndex):-
	check_indexes(RestOfBox, I1, I2, CurrIndex);
	check_indexes(RestOfProof, I1, I2, CurrIndex).
	
% Next element is a row, continue to inspect the rest of the proof.
check_indexes([[_, _, _]|T], I1, I2, CurrIndex):-
	check_indexes(T, I1, I2, CurrIndex).
	
% Make sure CurrIndex is a row inside the scope of the referred box.

% Last row in box, check scope.
inside_scope([[LastRowIndex, _, _]|[]], CurrIndex):-
	LastRowIndex>=CurrIndex.
	
% Last element in box is a box, look through the box.
inside_scope([[[A, B, C]|Box]|[]], CurrIndex):-
	inside_scope([[A, B, C]|Box], CurrIndex).
	
% Not the last element, get the next row.
inside_scope([_|T], CurrIndex):-
	inside_scope(T, CurrIndex).

% Rules for natural deduction.
% check_rule(+AllRows, +CheckedRows, +Premises, +Formula, +Rule, +CurrIndex)

% Premise, valid if premise exists.
check_rule(_, _, Prems, Formula, premise, _):-
	member(Formula, Prems).

% Copy, valid if the formula exists in an open box.
check_rule(_, CheckedRows, _, Formula, copy(Index), _):-
	get_line(CheckedRows, Index, Formula, _).

% Elimination of second conjunct. P is valid if P and Q.
check_rule(_, CheckedRows, _, Formula, andel1(Index), _):-
	get_line(CheckedRows, Index, and(Formula, _), _).

% Elimination of first conjunct. Q is valid if P and Q.
check_rule(_, CheckedRows, _, Formula, andel2(Index), _):-
	get_line(CheckedRows, Index, and(_, Formula), _).
	
% Elimination of disjunct. X is valid if we know that P or Q is valid,
% we have assumed P and derived X, and we have assumed Q and derived X.
check_rule(AllRows, _, _, Formula, orel(Index, B1B, B1E, B2B, B2E), CurrIndex):-
	% Extract disjuncts D1 and D2 given the index Index
	get_line(AllRows, Index, or(D1, D2), _),
	% Check that we assumed the first disjunct in the first box, and
	% derived Formula
	get_line(AllRows, B1B, D1, assumption),
	get_line(AllRows, B1E, Formula, _),
	same_box(AllRows, B1B, B1E, CurrIndex),
	% Do the same thing for the second disjunct.
	get_line(AllRows, B2B, D2, assumption),
	get_line(AllRows, B2E, Formula, _),
	same_box(AllRows, B2B, B2E, CurrIndex).

% Introduction of negation. Not P is valid if we assumed P and derived
% bottom.
check_rule(AllRows, _, _, neg(Formula), negint(BB, BE), CurrIndex):-
	get_line(AllRows, BB, Formula, assumption),
	get_line(AllRows, BE, cont, _),
	same_box(AllRows, BB, BE, CurrIndex).

% Elimination of negation. Bottom is valid if we have assumed 
% P and derived not P.
check_rule(_, CheckedRows, _, cont, negel(I1, I2), _):-
	get_line(CheckedRows, I1, Formula, _),
	get_line(CheckedRows, I2, neg(Formula), _).
	
% Elimination of bottom. If we have concluded bottom, we can derive anything.
check_rule(_, CheckedRows, _, _, contel(Index), _):-
	get_line(CheckedRows, Index, cont, _).

% Modus tollens. Not P is valid if P -> Q and we know that Q is false.
check_rule(_, CheckedRows, _, neg(Formula), mt(I1, I2), _):-
	get_line(CheckedRows, I1, imp(Formula, B), _),
	get_line(CheckedRows, I2, neg(B), _).
	
% Lemma. We can always construct the disjunction of P and its inverse.
check_rule(_, _, _, or(Formula, neg(Formula)), lem, _).

% Introduction of a conjunction. If P is valid and Q is valid
% then P and Q is valid.
check_rule(_, CheckedRows, _, and(F1, F2), andint(I1, I2), _):-
	get_line(CheckedRows, I1, F1, _),
	get_line(CheckedRows, I2, F2, _).

% Introduction of a disjunct to the right. If P is valid
% then P or Q is valid.
check_rule(_, CheckedRows, _, or(Formula, _), orint1(Index), _):-
	get_line(CheckedRows, Index, Formula, _).

% Introduction of a disjunct to the left. If Q is valid
% then P or Q is valid.
check_rule(_, CheckedRows, _, or(_, Formula), orint2(Index), _):-
	get_line(CheckedRows, Index, Formula, _).

% Introduction of implication. P -> Q is valid if we assumed
% P and derived Q.
check_rule(AllRows, _, _, imp(P1, P2), impint(I1, I2), CurrIndex):-
	get_line(AllRows, I1, P1, assumption),
	get_line(AllRows, I2, P2, _),
	same_box(AllRows, I1, I2, CurrIndex).

% Elimination of implication. Q is valid if we know that P is
% valid and P -> Q.
check_rule(_, CheckedRows, _, Formula, impel(I1, I2), _):-
	get_line(CheckedRows, I1, P, _),
	get_line(CheckedRows, I2, imp(P, Formula), _).

% Elimination of double negation. If not not P then P.
check_rule(_, CheckedRows, _, Formula, neconsultgnegel(Index), _):-
	get_line(CheckedRows, Index, neg(neg(Formula)), _).

% Introduction of double negation. If P then not not P.
check_rule(_, CheckedRows, _, neg(neg(Formula)), negnegint(Index), _):-
	get_line(CheckedRows, Index, Formula, _).

% Proof by contradiction. P is valid if we assume not P and 
% derive bottom.
check_rule(AllRows, _, _, Formula, pbc(I1, I2), CurrIndex):-
	get_line(AllRows, I1, neg(Formula), assumption),
	get_line(AllRows, I2, cont, _),
	same_box(AllRows, I1, I2, CurrIndex).
check_rule(AllRows, _, _, neg(Formula), pbc(I1, I2), CurrIndex):-
	get_line(AllRows, I1, Formula, assumption),
	get_line(AllRows, I2, cont, _),
	same_box(AllRows, I1, I2, CurrIndex).
