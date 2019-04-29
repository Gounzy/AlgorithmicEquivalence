% pdt_reload:pdt_reload('C:/DocumentsUnamur/GitHub/AlgorithmicEquivalence/src/main.pl').

% working_directory(_, 'C:/Users/User/ownCloud/GitHub/AlgorithmicEquivalence/src').
% working_directory(_, 'C:/DocumentsUnamur/GitHub/AlgorithmicEquivalence/src').

:-module(main,[]).

:-use_module(utils).
:-use_module(input).
:-use_module(pprint).
:-use_module(db).
:-use_module(au_complexity).
:-use_module(generalization_utils).
:-use_module(mcg).
:-use_module(exhaustive_renamings).
:-use_module(generalization_abstraction).

prepare(File1, File2, OutClauses1, OutClauses2):-
	working_directory(CWD, CWD),
 	sub_string(CWD, _, _, _ , 'clp'),
 	!,
	db:init,
	input:load_file(File1, Clauses1),
	input:load_file(File2, Clauses2),
	mix_clauses(Clauses1, OutClauses1),
	mix_clauses(Clauses2, OutClauses2).

prepare(File1, File2, OutClauses1, OutClauses2):-
 	working_directory(CWD, CWD),
 	concat(CWD, '/clp', NCWD),
 	working_directory(CWD, NCWD),
	db:init,
	input:load_file(File1, Clauses1),
	input:load_file(File2, Clauses2),
	mix_clauses(Clauses1, OutClauses1),
	mix_clauses(Clauses2, OutClauses2).

test_class_1(K):-
	format('~n --------------Class 1 : '),
	db:class_4(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalization(K, Matrix, [], Sol)),
	format('~n Généralisation : ~w', [Sol]),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	matrix_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(mcg_exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(mcg_exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).
test_class_2(D,K):-
	retractall(max_distance(_)),
	assert(max_distance(D)),
	format('~n --------------Class 2 : '),
	db:class_2(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalize_poly(CurrentK, Atoms1, Atoms2, Matrix, Sol)),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	get_mappings(Mcg, MMCG),
	variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).
test_class_3(D,K):-
	retractall(max_distance(_)),
	assert(max_distance(D)),
	format('~n --------------Class 1 : '),
	db:class_3(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalize_poly(CurrentK, Atoms1, Atoms2, Matrix, Sol)),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	get_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).

test_class_4(D,K):-
	retractall(max_distance(_)),
	assert(max_distance(D)),
	format('~n --------------Class 1 : '),
	db:class_4(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalize_poly(CurrentK, Atoms1, Atoms2, Matrix, Sol)),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	get_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).

test_class_5(D,K):-
	retractall(max_distance(_)),
	assert(max_distance(D)),
	format('~n --------------Class 1 : '),
	db:class_1(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalize_poly(CurrentK, Atoms1, Atoms2, Matrix, Sol)),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	get_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).

test_class_5(D,K):-
	retractall(max_distance(_)),
	assert(max_distance(D)),
	format('~n --------------Class 1 : '),
	db:class_1(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalize_poly(CurrentK, Atoms1, Atoms2, Matrix, Sol)),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	get_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).

test_class_6(D,K):-
	retractall(max_distance(_)),
	assert(max_distance(D)),
	format('~n --------------Class 1 : '),
	db:class_1(Atoms1, Atoms2),
	build_matrix(Atoms1, Atoms2, Matrix),
	time(generalize_poly(CurrentK, Atoms1, Atoms2, Matrix, Sol)),
	length(Atoms1, L1),
	length(Atoms2, L2),
	time(mcg(Matrix, Mcg)),
	get_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	(L1 =< L2 -> time(exhaustive_renamings(Atoms1, Atoms2, McgVars, McgVarsMapping)) ; time(exhaustive_renamings(Atoms2, Atoms1, McgVars, McgVarsMapping))),
	format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, McgVars, Accuracy),
	format('~nAccuracy: ~w ', [Accuracy]).

compare_generalizations:-
	compare_generalizations_loop(100, [], Accuracies),
	format('~n Accuracies: ~w', [Accuracies]),
	sum(Accuracies,S), length(Accuracies,L), M is S/L,
	format('~n Accuracy: ~w', [M]).

sum(Xs, S):- sum(Xs, 0, S).
sum([], Acc, Acc).
sum([X|Xs], Acc, S):-
	NAcc is Acc + X,
	sum(Xs, NAcc, S).

accuracy(_, [], 1):-!.
accuracy(Gen1, Gen2, Accuracy):-
	length(Gen1, L1),
	length(Gen2, L2),
	Accuracy is L1/L2.

generalize_poly(K, Atoms1, Atoms2, _, Solution) :-
	generalize_poly(K, Atoms1, Atoms2,  [], [], [], Solution, Rho),
	variable_to_numeric_mapping(Rho1, Rho),
	format('~nGénéralisation D-bounded k-swap :  ~w avec renaming ~w', [Solution, Rho1]).

generalize_poly(K, Atoms1, Atoms2, CurrentGen1, CurrentRho, CurrentGen2, Solution, Rho) :-
	gp(K, Atoms1, Atoms2, CurrentGen1, CurrentRho, CurrentGen2, Solution, Rho).

gp(K, Atoms1, Atoms2, CurrentGen1, CurrentRho, CurrentGen2, Solution, Rho) :-
	%format('~n CurrentGen1: ~w', [CurrentGen1]),
	zip(CurrentGen1, CurrentGen2, ZippedCurrentGen),
	build_matrices(Atoms1, Atoms2, TotalMatrix, TotalMatrixScores, Atoms2, 0, 0),
	%mega_mean(ZippedCurrentGen, TotalMatrix, TotalMatrixScores, MM),
	%format('~n MegaMean : ~w', [MM]),
	length(CurrentGen2, N),
	remove_all(Atoms1, CurrentGen1, NAtoms1),
	%format('~n NAtoms1: ~w', [NAtoms1]),
	remove_all(Atoms2, CurrentGen2, NAtoms2),
	build_matrices(NAtoms1, NAtoms2, Matrix, MatrixScores, NAtoms2, 0, 0),
	%setof(A, take_up_to_random(K, NAtoms1, Matrix, MatrixScores, A), A1s),
  setof(A, take_up_to_random(1, Atoms1, A), A1s),
  enforce_atoms(CurrentGen1, [], Atoms2, [], NewCurrentRho),
	!,
	%format('~n A1s: ~w', [A1s]),
	member(A1, A1s),
	%format('~n A1: ~w', [A1]),
	enforce_atoms(A1, CurrentGen1, Atoms2, NewCurrentRho, NewRho),
	%format('~n NewRho: ~w', [NewRho]),
	gen(NewRho, Atoms1, Atoms2, NewGen1),
  length(NewGen1, N1),
  N1 > N,
	apply_subst(NewGen1, NewRho, NewGen2),
	%zip(NewGen1, NewGen2, ZippedGen),
	%format('~n NewGen1: ~w', [NewGen1]),
	%format('~n NewGen2: ~w', [NewGen2]),
	%Mega_mean(ZippedGen, TotalMatrix, TotalMatrixScores, MM1),
	%better_stats(N, N1, MM, MM1),
	!,
	%format('~n New Mega Mean: ~w & newSize : ~w', [MM1, N1]),
	generalize_poly(K, Atoms1, Atoms2, NewGen1, NewRho, NewGen2, Solution, Rho).
generalize_poly(_, _, _, CurrentGen1, CurrentRho, _, CurrentGen1, CurrentRho).

take_up_to_random(UpTo, List, Out):-
  take_up_to_random(1, UpTo, List, Out).

take_up_to_random(N, UpTo, _, _):- N > UpTo, !, false.
take_up_to_random(N, UpTo, List, Out):-
  N1 is N + 1,
  take_up_to_random(N1, UpTo, List, Out).
take_up_to_random(N, UpTo, List, Out):-
  N =< UpTo,
  db:take_random(N, List, Out).

take_up_to(N, List, Matrix, ScoresMatrix, OutList):-
	take_up_to(1, N, List, Matrix, ScoresMatrix, OutList).
take_up_to(N, NMax, _, _, _, _):-
	 N > NMax, !, false.
take_up_to(N, NMax, Atoms, Matrix, ScoresMatrix, Out):-
	N1 is N + 1,
	take_up_to(N1, NMax, Atoms, Matrix, ScoresMatrix, Out).
take_up_to(N, _, Atoms, Matrix, ScoresMatrix, Out):-
	 fetch_n_best_scores(N, Matrix, ScoresMatrix, MatrixOut),
	 ensure_injective(MatrixOut, IMatrixOut),
	 extract_corresponding_atoms(Atoms, IMatrixOut, Out).

ensure_injective([], []).
ensure_injective([Symb/N/M/Mapping|Matrix], [Symb/N/M/Mapping|MatrixOut]):-
	get_int_mappings(Matrix, IMappings),
	renaming_with_vars_names(IMapping, Mapping),
	compatible(IMapping, IMappings),
	not(member(Symb/N/_/_, Matrix)),
	not(member(Symb/_/M/_, Matrix)),
	!,
	ensure_injective(Matrix, MatrixOut).
ensure_injective([_|Matrix], MatrixOut):-
	ensure_injective(Matrix, MatrixOut).

take(N, _, Xs) :- N =< 0, !, N =:= 0, Xs = [].
take(_, [], []).
take(N, [X|Xs], [X|Ys]) :- M is N-1, take(M, Xs, Ys).

sort_scores(Matrix, MatrixSorted):-
	q_sort(Matrix,[],MatrixSorted).

q_sort([],Acc,Acc).
q_sort([(H-Score)|T],Acc,Sorted):-
    pivoting(Score,T,L1,L2),
    q_sort(L1,Acc,Sorted1),
    q_sort(L2,[(H-Score)|Sorted1],Sorted).

pivoting(_,[],[],[]).
pivoting(Score,[(M1-Score1)|T],[(M1-Score1)|L],G):-Score1 =< Score,pivoting(Score,T,L,G).
pivoting(Score,[(M1-Score1)|T],L,[(M1-Score1)|G]):-Score1 > Score,pivoting(Score,T,L,G).

extract_corresponding_atoms(_, [], []).
extract_corresponding_atoms(Atoms, [_/N/_/_|Matrix], [O|Out]):-
	nth0(N, Atoms, O),
	!,
	extract_corresponding_atoms(Atoms, Matrix, Out).

take_random(N, List, OutList):-
	all_members(OutList, List),
	length(List, N).

enforce_atoms([], _, _, CurrentRho, CurrentRho).
enforce_atoms([A|TomsToEnforce], Atoms, AtomsFromGoal2, CurrentRho, EnforcingRho):-
	member(A2, AtomsFromGoal2),
	renaming_apart(A, A2, Sigma),
	enforce_renaming(CurrentRho, Sigma, EnforcingRho1),
	gen(EnforcingRho1, Atoms, AtomsFromGoal2, Gen),
	enforce_atoms(TomsToEnforce, Gen, AtomsFromGoal2, EnforcingRho1, EnforcingRho).

enforce_renaming(Sigma, Rho, NewSigma):-
	take_only_compatible(Sigma, Rho, NewSigma1),
	append(NewSigma1, Rho, NewSigma2),
	sort(NewSigma2, NewSigma),
	!.

take_only_compatible([], _, []).
take_only_compatible([S|Sigma], Rho, [S|OnlyCompatible]):-
	compatible([S], Rho),
	!,
	take_only_compatible(Sigma, [S|Rho], OnlyCompatible).
take_only_compatible([_|Sigma], Rho, OnlyCompatible):-
	take_only_compatible(Sigma, Rho, OnlyCompatible).

renaming_with_vars_names([], []).
renaming_with_vars_names([I-J|Rho], ['$VAR'(I)-'$VAR'(J)|RhoL]):-
	renaming_with_vars_names(Rho, RhoL).

atoms_vars([], []).
atoms_vars([A|Toms], AtomsVars):-
	atom_vars(A, AtomVars),
	atoms_vars(Toms, AVS),
	append(AtomVars, AVS, AtomsVars1),
	sort(AtomsVars1, AtomsVars).

atom_vars(Atom, AtomVars):-
	Atom =.. [_|Vars],
	sort(Vars, AtomVars).

k_swap_poly(K, Phi, Phi2):-
	sort(Phi, Phi1),
	length(Phi1, L1),
	common_list(Phi1, Phi2, CommonPhi),
	sort(CommonPhi,CP),
	length(CP, LC),
	K1 is L1 - LC,
	K1 =< K.

renaming_apart(Atom1, Atom2, SigmaOut) :-
	Atom1 =.. [F|Args1],
	Atom2 =.. [F|Args2],
	renaming_apart_args(Args1, Args2, Sigma),
	compatible(Sigma, Sigma),
	sort(Sigma, SigmaOut).

renaming_apart_args([], [], []).
renaming_apart_args(['$VAR'(I)|Args1], ['$VAR'(J)|Args2], [I-J|Sigma]):-
	I =\= J,
	renaming_apart_args(Args1, Args2, Sigma).
renaming_apart_args(['$VAR'(I)|Args1], ['$VAR'(I)|Args2], Sigma):-
	renaming_apart_args(Args1, Args2, Sigma).
