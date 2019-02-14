:-module(main,[]).

:-use_module(utils). 
:-use_module(input).
:-use_module(pprint).  
:-use_module(db).

generalize(Length):- 
	prepare('test.clp', 'test2.clp', [cl(_, Atoms1)], [cl(_, Atoms2)]),
	format('Atomes de la clause 1 : '), 
	pprint:print_list(Atoms1),
	format('~nAtomes de la clause 2 : '), 
	pprint:print_list(Atoms2), 
	
	db:fresh_rename(Atoms1, RAtoms1), 
	db:fresh_rename(Atoms2, RAtoms2), 
	
	format('~nAtomes de la clause 1 renomm�s : '), 
	pprint:print_list(RAtoms1),
	format('~nAtomes de la clause 2 renomm�s : '), 
	pprint:print_list(RAtoms2),
	
	order_atoms(RAtoms1, SAtoms1), 
	order_atoms(RAtoms2, SAtoms2),
	
	format('~nAtomes de la clause 1 tri�s : '), 
	pprint:print_list(SAtoms1),
	format('~nAtomes de la clause 2 tri�s : '), 
	pprint:print_list(SAtoms2),
	
	build_matrices(SAtoms1, SAtoms2, Matrix, SAtoms2, 0, 0),
	
	format('~nMatrice de similarit� : '), 
	format('~w', [Matrix]),

	k_swap_stable_naive(1, Matrix, Length, Output), 
	
	format('~n R�sultat :'), 
	format('~n~w', [Output]).
	
test_variable('$VAR'(N)):- 
	print(N). 
	
k_swap_stable_naive(K, Matrix, MinLength, Output):-
	injective_generalization(Matrix, MinLength, Output),
	not(is_k_swap_unstable(K, Output, Matrix, MinLength)). 

injective_generalization(Matrix, MinLength, Output):-
	all_members(Output, Matrix), 
	length(Output, Length), 
	Length >= MinLength,
	no_collisions(Output).

all_members([], _).
all_members([X|Xs], List) :-
	select(X, List, List2), 
	all_members(Xs, List2). 

is_k_swap_unstable(K, Gen1, Matrix, Length):- 
	injective_generalization(Matrix, Length, Gen2),
	k_swap(K, Gen1, Gen2, []), 
	is_strictly_more_specific(Gen2, Gen1).
	
k_swap(K, [], _, Swaptable):- sort(Swaptable, ST), length(ST, K). 
k_swap(K, [Symb/N/M/Mapping|List], Gen2, Swaptable):- 
	k_swap_mapping(Mapping, Gen2, Swaptable1), 
	append(Swaptable, Swaptable1, Swaptable2),
	k_swap(K, List, Gen2, Swaptable2).   

k_swap_mapping([], _, []). 
k_swap_mapping([A-B|Mapping], [Symb/N/M/Mapping2|List], Swaptable) :- 
	k_swap_mapping_mapping(A-B, Mapping2, Swaptable1),
	k_swap_mapping(Mapping, [Symb/N/M/Mapping2|List], Swaptable2),
	append(Swaptable1, Swaptable2, Swaptable). 
	 
k_swap_mapping_mapping(_, [], []). 
k_swap_mapping_mapping('$VAR'(I)-'$VAR'(J), ['$VAR'(I)-'$VAR'(J2)|Mapping], ['$VAR'(I)-'$VAR'(J)/'$VAR'(I)-'$VAR'(J2)|Swaptable]):- 
	J =\= J2, 
	!, 
	k_swap_mapping_mapping('$VAR'(I)-'$VAR'(J), Mapping, Swaptable). 
k_swap_mapping_mapping(A, B, [_|Mapping]):-
	k_swap_mapping_mapping(A, B, Mapping).
	
% G1 is strictly more specific than G2
is_strictly_more_specific(Gen1, Gen2):-
	has_same_atoms(Gen1, Gen2),
	has_more_atoms(Gen1, Gen2). 
	
has_same_atoms(_, []).
has_same_atoms(Gen1, [Symb/N/M/Mapping2|List]) :- 
	select(Symb/N1/M1/Mapping1, Gen1, NGen1),
	has_same_atoms(NGen1, List).
	
has_more_atoms(Gen1, Gen2) :-
	length(Gen1, L1), 
	length(Gen2, L2),
	L1 > L2.

no_collisions([]). 
no_collisions([Symb/N/M/Mapping|List]):- 
	not_generalized_n_m(N, M, List),
	injectivity_ok(Mapping, List), 
	no_collisions(List). 
	
not_generalized_n_m(N, M, []). 
not_generalized_n_m(N, M, [Symb/N1/M1/Mapping|List]):- 
	N1 =\= N,  
	M1 =\= M, 
	not_generalized_n_m(N, M, List). 

injectivity_ok([], _). 
injectivity_ok([A-B|Mapping], List):-
	injectivity_ok_a_b(A, B, List), 
	injectivity_ok_a_b_mapping(A,B,Mapping), 
	injectivity_ok(Mapping, List).
	
injectivity_ok_a_b(A, B, []). 
injectivity_ok_a_b(A, B, [Symb/N1/M1/Mapping|List]):- 
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

build_matrices([A1|Atoms1], [A2|Atoms2], NMatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb|_],
		A2 =..[Symb|_],
		map_variables(A1, A2, Mapping),
		append([Symb/N/M/Mapping], MatrixSimilarities, NMatrixSimilarities),
		M1 is M + 1,
		build_matrices([A1|Atoms1], Atoms2, MatrixSimilarities, AllAtoms2, N, M1)
	.
	
build_matrices([A1|Atoms1], [A2|_], MatrixSimilarities, AllAtoms2, N, _):-
		A1 =..[Symb1|_],
		A2 =..[Symb2|_],
		Symb1 @< Symb2,
		N1 is N + 1,
		build_matrices(Atoms1, AllAtoms2, MatrixSimilarities, AllAtoms2, N1, 0)
	.
	
build_matrices([A1|Atoms1], [A2|Atoms2], MatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb1|_],
		A2 =..[Symb2|_],
		Symb1 @> Symb2,
		M1 is M + 1,
		build_matrices([A1|Atoms1], Atoms2, MatrixSimilarities, AllAtoms2, N, M1)
	.
	
map_variables(A1, A2, Mapping):- 
	A1 =..[_|Args1],
	A2 =..[_|Args2],
	zip(Args1, Args2, Mapping). 
	
zip([], [], []).
zip([], [_|_], []).
zip([_|_], [], []).
zip([X|Xs], [Y|Ys], [X-Y|XYs]) :-
   zip(Xs, Ys, XYs).
   
prepare(File1, File2, OutClauses1, OutClauses2):-
	working_directory(CWD, CWD), 
 	sub_string(CWD, _, _, _ , 'clp'),
 	!, 
	db:init,
	input:load_file(File1, Clauses1),
	format('Loading file 1 done ! ~n'), 
	input:load_file(File2, Clauses2),
	format('Loading file 2 done ! ~n'), 
	mix_clauses(Clauses1, OutClauses1),
	mix_clauses(Clauses2, OutClauses2).     

prepare(File1, File2, OutClauses1, OutClauses2):-
 	working_directory(CWD, CWD), 
 	concat(CWD, '/clp', NCWD), 
 	working_directory(CWD, NCWD), 
	db:init,
	input:load_file(File1, Clauses1),
	format('Loading file 1 done ! ~n'), 
	input:load_file(File2, Clauses2),
	format('Loading file 2 done ! ~n'), 
	mix_clauses(Clauses1, OutClauses1),
	mix_clauses(Clauses2, OutClauses2). 

mix_clauses([], []). 
mix_clauses([C|Cs], [NC|NCs]):- 
	mix_clause(C, NC), 
	mix_clauses(Cs, NCs).
	
mix_clause(cl(H, C, B), cl(H, Atoms)):- 
	append(C, B, Atoms).  
	