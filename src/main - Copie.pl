% pdt_reload:pdt_reload('C:/DocumentsUnamur/GitHub/AlgorithmicEquivalence/src/main.pl').
   
% working_directory(_, 'C:/Users/User/ownCloud/GitHub/AlgorithmicEquivalence/src').
% working_directory(_, 'C:/DocumentsUnamur/GitHub/AlgorithmicEquivalence/src').

:-module(main,[]).

:-use_module(utils). 
:-use_module(input). 
:-use_module(pprint).  
:-use_module(db).

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

compare_generalizations(K):- 
	compare_generalizations_loop(K, 10).   
	
compare_generalizations_loop(_, 0). 
compare_generalizations_loop(K, N):- 
	N1 is N - 1, 
	compare_generalizations_loop(K, N1),   
	db:generate_clp_atoms(UAtoms1, UAtoms2),
	sort(UAtoms1, Atoms1), 
	sort(UAtoms2, Atoms2), 
	time(generalize(K, Atoms1, Atoms2, _)), 
	time(generalize_poly(K, Atoms1, Atoms2, _)). 
 
generalize_poly(K, Atoms1, Atoms2, Solution) :- 
	generalize_poly(K, Atoms1, Atoms2, [], [], Solution),
	format('~n~n--------------------------------'),  
	format('~n--------------------------------'), 
	format('~nR�sultat (polynomial)'), 
	format('~n--------------------------------'), 
	format('~n--------------------------------'), 
	format('~n~w', [Solution]).
	
generalize_poly(K, Atoms1, Atoms2, Phi, S, Solution) :-
	remove_all(Atoms1, S, NAtoms1),
		format('~nNAtoms1: ~w', [NAtoms1]),
	apply_subst(S, Phi, S2),   
		format('~nS2: ~w:', [S2]),
	remove_all(Atoms2, S2, NAtoms2),
		format('~nNAtoms2: ~w', [NAtoms2]), 
	select(A, NAtoms1, _), 
	select(A2, NAtoms2, _), 
		format('~nA: ~w, A2:~w', [A, A2]),
	renaming_apart(A, A2, Sigma), 
		format('~nSigma: ~w', [Sigma]),
	atom_vars(A, Vars1), 
		format('~nVars1: ~w', [Vars1]),
	atom_vars(A2, Vars2),
		format('~nVars2: ~w', [Vars2]),
	renaming_from(Vars1, Vars2, Phi2), % 2-3 r�p�titions
	k_swap_poly(K, Phi, Phi2), 
		format('~nPhi2: ~w', [Phi2]),
	compatible(Sigma, Phi2),
	gen(Phi, Atoms1, Atoms2, OldGen), 
		format('~nOldGen: ~w', [OldGen]),
	length(OldGen, N),
		format('~nN: ~w', [N]), 
	union(Sigma, Phi2, PhiSigma), 
	gen(PhiSigma, Atoms1, Atoms2, NewGen),
		format('~nNewGen: ~w', [NewGen]), 
	length(NewGen, N2),
		format('~nN2: ~w', [N2]), 
	N < N2, 
	!,
	generalize_poly(K, Atoms1, Atoms2, PhiSigma, NewGen, Solution).

generalize_poly(_, _, _, _, S, S). 

gen(Phi, Atoms1, Atoms2, S):-
	apply_subst(Atoms1, Phi, NAtoms1), 
	common_list(NAtoms1, Atoms2, S), 
	!. 

union(Rho1, Rho2, Rho):-
	append(Rho1, Rho2, Rho3), 
	sort(Rho3, Rho). 
compatible(Rho1, Rho2):- 
	not(not_compatible(Rho1, Rho2)). 
	
not_compatible([I-J|_], Rho2):-
	member(I-J2, Rho2), 
	J2 =\= J.  
not_compatible([I-J|_], Rho2):-
	member(I2-J, Rho2), 
	I2 =\= I. 
not_compatible([_|Rho1], Rho2):-
	not_compatible(Rho1, Rho2). 
	
renaming_from(_, _, []). 
renaming_from(Vars1, Vars2, [I-J|Rho]):-
	select('$VAR'(I), Vars1, NVars1), 
	select('$VAR'(J), Vars2, NVars2), 
	renaming_from(NVars1, NVars2, Rho).
	
atom_vars(Atom, AtomVars):- 
	Atom =.. [_|Vars],
	sort(Vars, AtomVars).
	
k_swap_poly(K, Phi, Phi2):- 
	length(Phi, L1), 
	common_list(Phi, Phi2, CommonPhi), 
	length(CommonPhi, L2), 
	K1 is L1 - L2, 
	K1 =< K. 
	
common_list([], _, []). 
common_list([X|List], List2, [X|CommonList]):- 
	select(X, List2, NList2),  
	common_list(List, NList2, CommonList). 
common_list([X|List], List2, CommonList):-
	not(member(X, List2)),
	common_list(List, List2, CommonList). 
	
renaming_apart(Atom1, Atom2, Sigma) :-
	Atom1 =.. [F|Args1], 
	Atom2 =.. [F|Args2],
	renaming_apart_args(Args1, Args2, Sigma). 
	
renaming_apart_args([], [], []). 
renaming_apart_args(['$VAR'(I)|Args1], ['$VAR'(J)|Args2], [I-J|Sigma]):-
	I =\= J, 
	renaming_apart_args(Args1, Args2, Sigma).
renaming_apart_args(['$VAR'(I)|Args1], ['$VAR'(I)|Args2], Sigma):-
	renaming_apart_args(Args1, Args2, Sigma). 

remove_all([], _, []).
remove_all([A|Toms], S, [A|NAtoms]):- 
	not(member(A, S)),
	remove_all(Toms, S, NAtoms). 
remove_all([A|Toms], S, NAtoms):-
	member(A, S),
	remove_all(Toms, S, NAtoms). 
  
apply_subst(Atoms, [], Atoms). 
apply_subst([], _, []). 
apply_subst([A|Toms], Phi, [NA|NAtoms]):-
	apply_subst_atom(A, Phi, NA), 
	apply_subst(Toms, Phi, NAtoms). 
	
apply_subst_atom(Atom, Phi, NAtom):-
	Atom =.. [F|Args],
	apply_subst_args(Args, Phi, NArgs), 
	NAtom =.. [F|NArgs]. % todo functors

apply_subst_args([], _, []). 
apply_subst_args(['$VAR'(I)|Args], Phi, ['$VAR'(I)|NArgs]):-
	not(member(I-_, Phi)),  
	apply_subst_args(Args, Phi, NArgs).  
apply_subst_args(['$VAR'(I)|Args], Phi, ['$VAR'(J)|NArgs]):-
	member(I-J, Phi), 
	apply_subst_args(Args, Phi, NArgs).  
	
generalize_random_clauses(K) :-   
	db:generate_clp_atoms(Atoms1, Atoms2),
	setof(O, generalize(K, Atoms1, Atoms2,  O), Os), 
	format('~n~n--------------------------------'),  
	format('~n--------------------------------'), 
	format('~nR�sultats (exponentiel)'), 
	format('~n--------------------------------'), 
	format('~n--------------------------------'), 
	format('~n~w', [Os]).

generalize_files(K) :- 
	setof(O, generalize_files(K, O), Os), 
	format('~n~n--------------------------------'), 
	format('~n--------------------------------'), 
	format('~nR�sultats (exponentiel)'), 
	format('~n--------------------------------'), 
	format('~n--------------------------------'), 
	format('~n~w', [Os]). 

generalize_files(K, Output):- 
	prepare('test.clp', 'test2.clp', [cl(_, Atoms1)], [cl(_, Atoms2)]),
	generalize(K, Atoms1, Atoms2, Output).
	
generalize(K, Atoms1, Atoms2, Output) :- 
	assert(max_encountered_length(0)),
	update_max_length(0), 
	format('Atomes de la clause 1 : '), 
	pprint:print_list(Atoms1),
	format('~nAtomes de la clause 2 : '), 
	pprint:print_list(Atoms2), 
	
	order_atoms(Atoms1, SAtoms1), 
	order_atoms(Atoms2, SAtoms2),
	
	format('~nAtomes de la clause 1 tri�s : '), 
	pprint:print_list(SAtoms1),
	format('~nAtomes de la clause 2 tri�s : '), 
	pprint:print_list(SAtoms2),
	
	build_matrices(SAtoms1, SAtoms2, Matrix, SAtoms2, 0, 0),
	
	format('~nMatrice de similarit� : '), 
	format('~w', [Matrix]),
	
	injective_generalization(Matrix, Output1), 
	not(k_swap_unstable_naive(K, Matrix, Output1)), 
	
	sort(Output1, Output), 
	
	format('~n~n--------------------------------'), 
	format('~n--------------------------------'), 
	format('~nR�sultat (exponentiel)'), 
	format('~n--------------------------------'), 
	format('~n--------------------------------'), 
	format('~n~w', [Output]).
	
injective_generalization(Matrix, Output):-
	all_members(Output, Matrix), 
	length(Output, Length), 
	max_encountered_length(MinLength), 
	Length >= MinLength, 
	no_collisions(Output),
	update_max_length(Length). 
 
update_max_length(X):- 
	max_encountered_length(L), 
	X > L,
	!,
	retractall(max_encountered_length(_)),
	assert(max_encountered_length(X)). 
update_max_length(X):- 
	max_encountered_length(L), 
	X =< L,
	!. 
update_max_length(X):-
	assert(max_encountered_length(X)). 

all_members([], _).
all_members([X|Xs], List) :-
	select(X, List, List2), 
	all_members(Xs, List2). 

k_swap_unstable_naive(K, Matrix, Gen):-
	is_k_swap_unstable(K, Matrix, Gen). 
	 
is_k_swap_unstable(K, Matrix, Gen1):-  
	injective_generalization(Matrix, Gen2),
	has_more_atoms(Gen2, Gen1),
	k_swap(K, Gen1, Gen2),  
	format('~n Gen2 : ~w is ~w-swap from Gen1 : ~w', [Gen2, K, Gen1]).
	 
k_swap(K, Gen1, Gen2):-
	k_swap(K, Gen1, Gen2, Swaptable), 
	sort(Swaptable, ST),
	k_swap_with_identities(Gen2, ST, SwaptableOut),
	sort(SwaptableOut, STOut), 
	append(ST, STOut, STFinal),
	length(STFinal, K1), 
	K1 =< K, 
	format('~n SwapTable : ~w', [STFinal]).
	
k_swap_with_identities(Gen2, SwaptableIn, SwaptableOut):-
	get_mappings(Gen2, Mappings),
	k_swap_with_identities_mapping(Mappings, SwaptableIn, SwaptableOut). 
	
k_swap_with_identities_mapping([], _, []).
k_swap_with_identities_mapping(Mappings, SwaptableIn, ['$VAR'(I)-'$VAR'(J)|SwaptableOut]):- 
	select('$VAR'(I)-'$VAR'(J), Mappings, NMappings),
	not(member('$VAR'(I)-'$VAR'(_), SwaptableIn)), 
	append(['$VAR'(I)-'$VAR'(J)], SwaptableIn, NSIN),
	k_swap_with_identities_mapping(NMappings, NSIN, SwaptableOut). 
k_swap_with_identities_mapping([_|Mappings], STin, STout) :- 
	k_swap_with_identities_mapping(Mappings, STin, STout). 

get_mappings([], []).
get_mappings([_/_/_/Mapping|List], SM) :-
	get_mappings(List, M2), 
	append(Mapping, M2, Mappings), 
	sort(Mappings, SM).

k_swap(_, [], _, []). 
k_swap(K, [_/_/_/Mapping|List], Gen2, Swaptable):-  
	k_swap_mapping(Mapping, Gen2, Swaptable1), 
	k_swap(K, List, Gen2, Swaptable2),
	append(Swaptable1, Swaptable2, Swaptable).

k_swap_mapping([], _, []). 
k_swap_mapping([A-B|Mapping], [Symb/N/M/Mapping2|List], Swaptable) :- 
	k_swap_mapping_mapping(A-B, Mapping2, Swaptable1),
	k_swap_mapping(Mapping, [Symb/N/M/Mapping2|List], Swaptable2),
	append(Swaptable1, Swaptable2, Swaptable). 
	 
k_swap_mapping_mapping(_, [], []).
k_swap_mapping_mapping('$VAR'(I)-'$VAR'(J), ['$VAR'(I)-'$VAR'(J2)|Mapping], ['$VAR'(I)-'$VAR'(J2)|Swaptable]):- 
	J =\= J2, 
	!, 
	k_swap_mapping_mapping('$VAR'(I)-'$VAR'(J), Mapping, Swaptable). 
k_swap_mapping_mapping(A-B, [_|Mapping], Swaptable):-
	k_swap_mapping_mapping(A-B, Mapping, Swaptable).
	
% G1 is strictly more specific than G2
is_strictly_more_specific(Gen1, Gen2):-
	has_same_atoms(Gen1, Gen2),
	has_more_atoms(Gen1, Gen2). 
	
has_same_atoms(_, []).
has_same_atoms(Gen1, [Symb/_/_/_|List]) :- 
	select(Symb/_/_/_, Gen1, NGen1),
	has_same_atoms(NGen1, List).
	
has_more_atoms(Gen1, Gen2) :-
	length(Gen1, L1), 
	length(Gen2, L2),
	L1 > L2.

no_collisions([]). 
no_collisions([_/N/M/Mapping|List]):- 
	not_generalized_n_m(N, M, List),
	injectivity_ok(Mapping, List), 
	no_collisions(List). 
	
not_generalized_n_m(_,_, []). 
not_generalized_n_m(N, M, [_/N1/M1/_|List]):- 
	N1 =\= N,  
	M1 =\= M, 
	not_generalized_n_m(N, M, List). 

injectivity_ok([], _). 
injectivity_ok([A-B|Mapping], List):-
	injectivity_ok_a_b(A, B, List), 
	injectivity_ok_a_b_mapping(A,B,Mapping), 
	injectivity_ok(Mapping, List).
	
injectivity_ok_a_b(_, _, []). 
injectivity_ok_a_b(A, B, [_/_/_/Mapping|List]):- 
	injectivity_ok_a_b_mapping(A, B, Mapping), 
	injectivity_ok_a_b(A, B, List).  

injectivity_ok_a_b_mapping(_, _, []). 
injectivity_ok_a_b_mapping('$VAR'(I), '$VAR'(J), ['$VAR'(I)-'$VAR'(J)|Mapping]) :- 
	!,
	injectivity_ok_a_b_mapping('$VAR'(I), '$VAR'(J), Mapping). 
injectivity_ok_a_b_mapping('$VAR'(I), '$VAR'(J), ['$VAR'(I1)-'$VAR'(J1)|Mapping]) :- 
	I =\= I1, 
	J =\= J1, 
	injectivity_ok_a_b_mapping('$VAR'(I), '$VAR'(J), Mapping). 

order_atoms([], []).  
order_atoms(Atoms, NAtoms):- 
	sort(Atoms, NAtoms).

build_matrices(_, [], [], _, _, _).
build_matrices([], _, [], _, _, _). 

build_matrices([A1|Atoms1], [A2|Atoms2], MatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb|_],
		A2 =..[Symb|_],
		map_variables(A1, A2, Mapping),
		not(consistent_mapping(Mapping, [])), 
		!,
		M1 is M + 1,
		build_matrices([A1|Atoms1], Atoms2, MatrixSimilarities, AllAtoms2, N, M1).

build_matrices([A1|Atoms1], [A2|Atoms2], NMatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb|_],
		A2 =..[Symb|_],
		map_variables(A1, A2, Mapping1),
		sort(Mapping1, Mapping),
		consistent_mapping(Mapping, []),   
		append([Symb/N/M/Mapping], MatrixSimilarities, NMatrixSimilarities),
		M1 is M + 1,
		build_matrices([A1|Atoms1], Atoms2, MatrixSimilarities, AllAtoms2, N, M1).
	
build_matrices([A1|Atoms1], [A2|_], MatrixSimilarities, AllAtoms2, N, _):-
		A1 =..[Symb1|_],
		A2 =..[Symb2|_],
		Symb1 @< Symb2,
		N1 is N + 1,
		build_matrices(Atoms1, AllAtoms2, MatrixSimilarities, AllAtoms2, N1, 0).
	
build_matrices([A1|Atoms1], [A2|Atoms2], MatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb1|_],
		A2 =..[Symb2|_],
		Symb1 @> Symb2,
		M1 is M + 1,
		build_matrices([A1|Atoms1], Atoms2, MatrixSimilarities, AllAtoms2, N, M1).
	
consistent_mapping([], _). 
consistent_mapping([A-B|Mapping], ConstructedMapping):-
	not(non_injective_appearance(A-B, ConstructedMapping)),
	append(ConstructedMapping, [A-B], NConstructedMapping),
	consistent_mapping(Mapping, NConstructedMapping). 
	
non_injective_appearance('$VAR'(I)-'$VAR'(J), Mapping):- 
	member('$VAR'(K)-'$VAR'(J), Mapping),
	K =\= I. 
non_injective_appearance('$VAR'(I)-'$VAR'(J), Mapping):- 
	member('$VAR'(I)-'$VAR'(K), Mapping),
	K =\= J. 
	 
map_variables(A1, A2, Mapping):- 
	A1 =..[_|Args1],
	A2 =..[_|Args2],
	zip(Args1, Args2, Mapping). 
	
zip([], [], []).
zip([], [_|_], []).
zip([_|_], [], []).
zip([X|Xs], [Y|Ys], [X-Y|XYs]) :-
   zip(Xs, Ys, XYs).

mix_clauses([], []). 
mix_clauses([C|Cs], [NC|NCs]):- 
	mix_clause(C, NC), 
	mix_clauses(Cs, NCs).
	
mix_clause(cl(H, C, B), cl(H, Atoms)):- 
	append(C, B, Atoms).  
	