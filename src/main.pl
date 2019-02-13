:-module(main,[]).

:-use_module(utils). 
:-use_module(input).
:-use_module(pprint).  
:-use_module(db).

generalize:- 
	prepare('test.clp', 'test2.clp', [cl(_, Atoms1)], [cl(_, Atoms2)]),
	format('Atomes de la clause 1 : '), 
	pprint:print_list(Atoms1),
	format('~nAtomes de la clause 2 : '), 
	pprint:print_list(Atoms2), 
	
	order_atoms(Atoms1, SAtoms1), 
	order_atoms(Atoms2, SAtoms2),
	
	format('~nAtomes de la clause 1 triés : '), 
	pprint:print_list(SAtoms1),
	format('~nAtomes de la clause 2 triés : '), 
	pprint:print_list(SAtoms2),
	
	
	build_matrices(SAtoms1, SAtoms2, Matrix, SAtoms2, 0, 0),
	
	format('~nMatrice de similarité : '), 
	format('~w', [Matrix])
	.

order_atoms([], []). 
order_atoms(Atoms, NAtoms):- 
	sort(Atoms, NAtoms).


build_matrices(_, [], [], _, _, _).
build_matrices([], _, [], _, _, _). 

build_matrices([A1|Atoms1], [A2|Atoms2], NMatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb|_],
		A2 =..[Symb|_],
		map_variables(A1, A2, Mapping),
		append([N/M/Mapping], MatrixSimilarities, NMatrixSimilarities),
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
	working_directory(_, 'C:/Users/gyernaux/workspace/Generalization/src/CLP'),
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
	