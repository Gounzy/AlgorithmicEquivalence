:-module(generalization_utils, [
		combination/3,
		perm/2,
		gen/4,
		apply_subst/3,
		zip/3,
		build_matrix/3,
		inverse_renaming/2,
		no_collisions/1,
		is_strictly_more_specific/2,
		compatible/2,
		matrix_mappings/2,
		variable_to_numeric_mapping/2,
		variable_to_numeric_mappings/2,
		remove_all/3
] ).

combination(0, _, []) :-
    !.
combination(N, L, [V|R]) :-
    N > 0,
    NN is N - 1,
    unknown(V, L, Rem),
    combination(NN, Rem, R).

unknown(X,[X|L],L).
unknown(X,[_|L],R) :-
		unknown(X,L,R).

perm([X|Y],Z) :- perm(Y,W), takeout(X,Z,W).
perm([],[]).

takeout(X,[X|R],R).
takeout(X,[F |R],[F|S]) :- takeout(X,R,S).

gen(Phi, _, _, []):-
	is_not_injective(Phi),
	!.
gen(Phi, Atoms1, Atoms2, S2):-
	apply_subst(Atoms1, Phi, NAtoms1),
	common_list(NAtoms1, Atoms2, S),
	inverse_renaming(Phi, Phi2),
	apply_subst(S, Phi2, S2),
	!.

is_not_injective(Rho):-
	member(K-J, Rho),
	member(I-J, Rho),
	K =\= I.
is_not_injective(Rho):-
	member(I-J, Rho),
	member(I-K, Rho),
	K =\= J.

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

build_matrix(Atoms1, Atoms2, Matrix):-
	build_matrices(Atoms1, Atoms2, Matrix, _, Atoms2, 0, 0).

build_matrices(Atoms1, Atoms2, MatrixSimilarities, MatrixScores, AllAtoms2, N, M) :-
	build_matrices(Atoms1, Atoms2, MatrixSimilarities, AllAtoms2, N, M),
	compute_scores(MatrixSimilarities, MatrixScores).

build_matrices([], _, [], _, _, _).
build_matrices([_|Atoms1], [], MatrixSimilarities, AllAtoms2, N, _):-
	N1 is N + 1,
	build_matrices(Atoms1, AllAtoms2, MatrixSimilarities, AllAtoms2, N1, 0).
build_matrices([A1|Atoms1], [A2|Atoms2], NMatrixSimilarities, AllAtoms2, N, M):-
		A1 =..[Symb|_],
		A2 =..[Symb|_],
		map_variables(A1, A2, Mapping1),
		sort(Mapping1, Mapping),
		consistent_mapping(Mapping, []),
		!,
		M1 is M + 1,
		build_matrices([A1|Atoms1], Atoms2, MatrixSimilarities, AllAtoms2, N, M1),
		append([Symb/N/M/Mapping], MatrixSimilarities, NMatrixSimilarities).
build_matrices(Atoms1, [_|Atoms2], MatrixSimilarities, AllAtoms2, N, M):-
		M1 is M + 1,
		build_matrices(Atoms1, Atoms2, MatrixSimilarities, AllAtoms2, N, M1).

compute_scores(Matrix, ScoresMatrix) :-
	compute_scores(Matrix, Matrix, ScoresMatrix).

compute_scores([], _, []).
compute_scores([M|Matrix], AllMatrix, [Score|ScoresMatrix]):-
	matrix_score(M, AllMatrix, Score),
	compute_scores(Matrix, AllMatrix, ScoresMatrix).

matrix_score(Symb/N/M/Rho, AllMatrix, Score):-
	Calc is N - M,
	Score is abs(Calc) + 1.

matrix_mappings([], []).
matrix_mappings([_/_/_/Mapping|List], SM) :-
	matrix_mappings(List, M2),
	append(Mapping, M2, Mappings),
	sort(Mappings, SM).

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
zip([X|Xs], [Y|Ys], [X-Y|XYs]) :-
   zip(Xs, Ys, XYs).

unzip([], []).
unzip([X-_|List], [X|Out]):-
	unzip(List, Out).


inverse_renaming([], []).
inverse_renaming([A-B|Rho], [B-A|RhoI]):-
	inverse_renaming(Rho, RhoI).

common_list([], _, []).
common_list([X|List], List2, [X|CommonList]):-
	select(X, List2, NList2),
	common_list(List, NList2, CommonList).
common_list([X|List], List2, CommonList):-
	not(member(X, List2)),
	common_list(List, List2, CommonList).

extract_matrix_variables(Matrix, Variables1, Variables2):-
	extract_matrix_variables(Matrix, [], Variables1, [], Variables2).
extract_matrix_variables([], Acc1, Acc1Sorted, Acc2, Acc2Sorted):-
	sort(Acc1, Acc1Sorted),
	sort(Acc2, Acc2Sorted).
extract_matrix_variables([F/N/M/Mapping|Matrix], Acc1, Variables1, Acc2, Variables2):-
	extract_vars_mapping(Mapping, NVars1, NVars2),
	append(Acc1, NVars1, NAcc1),
	append(Acc2, NVars2, NAcc2),
	extract_matrix_variables(Matrix, NAcc1, Variables1, NAcc2, Variables2).

extract_vars_mapping([], [], []).
extract_vars_mapping([A-B|Mapping], [A|Vars1], [B|Vars2]):-
	extract_vars_mapping(Mapping, Vars1, Vars2).

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
order_atoms([], []).
order_atoms(Atoms, NAtoms):-
	sort(Atoms, NAtoms).

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

print_graph(Atoms1, Atoms2, [_|Openings]):-
	length(Atoms1, L1),

	format('<?xml version="1.0" encoding="UTF-8"?>
		<gexf xmlns:viz="http:///www.gexf.net/1.1draft/viz" version="1.1" xmlns="http://www.gexf.net/1.1draft">
		<meta lastmodifieddate="2010-03-03+23:44">
		<creator>Gephi 0.7</creator>
		</meta>
		<graph defaultedgetype="undirected" idtype="string" type="static">
		<nodes count="~w">', [L1]),

	atoms_id_list(1, Atoms1, List1),

	print_nodes(List1),

	format('</nodes>'),

	length(Openings, L4),
	format('<edges count="~w">', [L4]),

	print_edges(Openings, List1, 1),

	format('</edges>
  			</graph>
			</gexf>').


atoms_id_list(_, [], []).
atoms_id_list(Begin, [A|Atoms], [Begin-A|List]):-
	Begin1 is Begin + 1,
	atoms_id_list(Begin1, Atoms, List).

print_nodes([]).
print_nodes([Id-Atom|List]):-
	format('<node id="~w.0" label="~w"/>', [Id, Atom]),
	print_nodes(List).

print_edges([], _, _).
print_edges([A1-A2|Openings], IdList, Count):-
	member(Id1-A1, IdList),
	member(Id2-A2, IdList),
	format('<edge id="~w" source="~w.0" target="~w.0"/>', [Count, Id1, Id2]),
	Count1 is Count + 1,
	print_edges(Openings, IdList, Count1).

sigmas_openings(Sigmas, Openings):-
	sigmas_openings(Sigmas, Sigmas, Openings).
sigmas_openings([], _, []).
sigmas_openings([A-Sigma|Sigmas], AllSigmas, OpeningsOut):-
	format('~n ~nSigmas openings for ~w ~n ---------------------~n', [A]),
	setof(O, opening(A-Sigma, AllSigmas, O), Openings),
	sigmas_openings(Sigmas, AllSigmas, Openingss),
	append(Openingss, Openings, Openingsss),
	sort(Openingsss, OpeningsOut).

opening(A-Sigma, AllSigmas, Opening):-
	member(A2-Sigma2, AllSigmas),
	A2 \= A,
	member(S, Sigma),
	member(S2, Sigma2),
	compatible(S, S2),
	format('~w~n', [A2]),
	Opening = A-A2.
opening(_, _, []).

first_line_csv_matrix([]):- !, format('~n').
first_line_csv_matrix([A|Atoms]):-
	format(';~w', [A]),
	first_line_csv_matrix(Atoms).

csv_matrix(_, [], []):-!.
csv_matrix([], _, []):-!.
csv_matrix([A|Atoms1], Atoms2, [A-Sigma|Sigmas]):-
	format('~w', [A]),
	line_csv_matrix(A, Atoms2, Sigma1),
	sort(Sigma1, Sigma),
	format(';~w ~n', [Sigma]),
	csv_matrix(Atoms1, Atoms2, Sigmas).

line_csv_matrix(_, [], []):- !.
line_csv_matrix(A, [A2|Atoms], [Sigma|SigmaOut]):-
 	renaming_apart(A, A2, Sigma),
 	!,
 	variable_to_numeric_mapping(Rho, Sigma),
 	format(';~w', [Rho]),
 	line_csv_matrix(A, Atoms, SigmaOut).
line_csv_matrix(A, [A2|Atoms], SigmaOut):-
	format(';[]'),
	line_csv_matrix(A, Atoms, SigmaOut).

variable_to_numeric_mappings([], []).
variable_to_numeric_mappings([Mapping|Mappings], [NumericMapping|NumericMappings]):-
	variable_to_numeric_mapping(Mapping, NumericMapping),
	variable_to_numeric_mappings(Mappings, NumericMappings).

variable_to_numeric_mapping([], []).
variable_to_numeric_mapping(['$VAR'(I)-'$VAR'(J)|Vars], [I-J|Nums]):-
	variable_to_numeric_mapping(Vars, Nums).

remove_all([], _, []).
remove_all([X|Xs], RemoveList, Result):-
	 member(X, RemoveList),
	 !,
	 remove_all(Xs, RemoveList, Result).
remove_all([X|Xs], RemoveList, [X|Result]):-
	not(member(X, RemoveList)),
	!,
	remove_all(Xs, RemoveList, Result).
