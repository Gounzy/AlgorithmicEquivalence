:-module(exhaustive_renamings, [
		mcg_exhaustive_renamings/4,
		mcg_exhaustive_renamings3/4
]).
:-use_module(generalization_utils).

mcg_exhaustive_renamings3(Atoms1, Atoms2, Mcg, Mapping):-
	build_matrix(Atoms1, Atoms2, Matrix),
	matrix_mappings2(Matrix, PossibleMappings),
	%format('~n PossibleMappings : ~w', [PossibleMappings]),
	sort(PossibleMappings, SPossibleMappings),
	mcg_ex_best_mapping3(SPossibleMappings, Atoms1, Atoms2, [], Mcg, Mapping).

mcg_ex_best_mapping3([], Atoms1, Atoms2, Mapping, Mcg, Mapping):-
	gen(Mapping, Atoms1, Atoms2, Mcg).
mcg_ex_best_mapping3([Mapping|Mappings], Atoms1, Atoms2, SoFarMapping, Mcg, OutMapping):-
	mcg_ex_best_mapping3(Mappings, Atoms1, Atoms2, SoFarMapping, Mcg1, Mapping1),
	%format('~n Mcg1 : ~w et Mapping1 : ~w', [Mcg1, Mapping1]),
	append(Mapping, SoFarMapping, NSoFarMapping),
	%format('~nNSoFarMapping : ~w', [NSoFarMapping]),
	remove_collisions_mappings3(Mappings, Mapping, NMappings),
	%format('~n NMappings : ~w', [NMappings]),
	mcg_ex_best_mapping3(NMappings, Atoms1, Atoms2, NSoFarMapping, Mcg2, Mapping2),
	%format('~n Mcg2 : ~w et Mapping2 : ~w', [Mcg2, Mapping2]),
	length(Mcg1, L1),
	length(Mcg2, L2),
	(L1 >= L2 -> (Mcg = Mcg1, OutMapping = Mapping1) ; (Mcg = Mcg2, OutMapping = Mapping2)).

mcg_exhaustive_renamings(Atoms1, Atoms2, Mcg, Mapping) :-
	build_matrix(Atoms1, Atoms2, Matrix),
	matrix_mappings(Matrix, AllMappings),
	%format('~n AllMappings : ~w ', [AllMappings]),
	variable_to_numeric_mapping(AllMappings, NumericMappings),
	%format('~n NumericMappings : ~w ', [NumericMappings]),
	mcg_ex_best_mapping(NumericMappings, Atoms1, Atoms2, [], Mcg, Mapping).

mcg_ex_best_mapping([], Atoms1, Atoms2, SoFarMapping, Mcg, SoFarMapping):-
	gen(SoFarMapping, Atoms1, Atoms2, Mcg).
mcg_ex_best_mapping([M|Mappings], Atoms1, Atoms2, SoFarMapping, Mcg, Mapping):-
	mcg_ex_best_mapping(Mappings, Atoms1, Atoms2, SoFarMapping, Mcg1, Mapping1),
	remove_collisions_mappings(Mappings, M, NMappings),
	mcg_ex_best_mapping(NMappings, Atoms1, Atoms2, [M|SoFarMapping], Mcg2, Mapping2),
	length(Mcg1, L1),
	length(Mcg2, L2),
	(L1 >= L2 -> (Mcg = Mcg1, Mapping = Mapping1) ; (Mcg = Mcg2, Mapping = Mapping2)).

remove_collisions_mappings3(AllMappings, Mapping, NMapping):-
	remove_collisions_mappings3(AllMappings, Mapping, [], NMapping).

remove_collisions_mappings3([], _, Mappings, Mappings).
remove_collisions_mappings3([M|AllMappings], Mapping,CurrentMappings, NMappings):-
	collisions_mappings(M, Mapping),
	!,
	remove_collisions_mappings3(AllMappings, Mapping, CurrentMappings, NMappings).
remove_collisions_mappings3([M|AllMappings], Mapping, CurrentMappings, NMappings):-
	remove_collisions_mappings3(AllMappings, Mapping, [M|CurrentMappings], NMappings).

remove_collisions_mappings([], _, []).
remove_collisions_mappings([X-Z|Mappings], X-Y, NMappings):-
	!,
	remove_collisions_mappings(Mappings, X-Y, NMappings).
remove_collisions_mappings([Z-Y|Mappings], X-Y, NMappings):-
	!,
	remove_collisions_mappings(Mappings, X-Y, NMappings).
remove_collisions_mappings([X2-Y2|Mappings], X-Y, [X2-Y2|NMappings]):-
	remove_collisions_mappings(Mappings, X-Y, NMappings).

no_collisions_mapping([]).
no_collisions_mapping([X-Y|Mappings]):-
	not(collisions_mapping(X-Y, Mappings)),
	no_collisions_mapping(Mappings).

collisions_mappings(Xs, Mappings):-
	member(X, Xs),
	collisions_mapping(X, Mappings).

collisions_mapping(X-Y, Mappings) :-
	member(X-Z, Mappings),
	Z =\= Y.
collisions_mappings(X-Y, Mappings) :-
	member(Z-Y, Mappings),
	Z =\= X.

mcg_exhaustive_renamings2(Atoms1, Atoms2, Mcg, Mapping):-
	atoms_vars(Atoms1, Vars1),
	atoms_vars(Atoms2, Vars2),
	length(Vars1, L1),
	length(Vars2, L2),
	(L1 > L2 -> (RVars1 = Vars2, RVars2 = Vars1, RAtoms1 = Atoms2, RAtoms2 = Atoms1) ; (RVars1 = Vars1, RVars2 = Vars2, RAtoms1 = Atoms1, RAtoms2 = Atoms2)),
	setof(X, perm(RVars1, X), Xs),
  format('~n Xs : ~w', [Xs]),
  length(RVars1, RL1),
	setof(Y, combination(RL1, RVars2, Y), Ys),
  format('~n Ys : ~w', [Ys]),
	zipAll(Xs, Ys, AllZipped),
  variable_to_numeric_mappings(AllZipped, AllZippeds),
  %format('~n ZippedAll : ~w', [AllZippeds]),
	get_best_exhaustive(AllZippeds, RAtoms1, RAtoms2, Mcg, Mapping).

get_best_exhaustive(AllZipped, Atoms1, Atoms2, Mcg, Mapping):-
	get_best_exhaustive(AllZipped, Atoms1, Atoms2, [], [], Mcg, Mapping).

get_best_exhaustive([], Atoms1, Atoms2, Mcg, Mapping, Mcg, Mapping).
get_best_exhaustive([Mapping1|AllZipped], Atoms1, Atoms2, BestMcg, BestMapping, Mcg, Mapping):-
	gen(Mapping1, Atoms1, Atoms2, NewMcg),
	length(NewMcg, L1),
	length(BestMcg, L2),
(L1 >= L2 -> get_best_exhaustive(AllZipped, Atoms1, Atoms2, NewMcg, Mapping1, Mcg, Mapping) ; get_best_exhaustive(AllZipped, Atoms1, Atoms2, BestMcg, BestMapping, Mcg, Mapping)).

zipAll(Xs, Ys, AllZipped):-
	zipAll(Xs, Ys, Ys, AllZipped).
zipAll([], _, _, []):- !.
zipAll([_|Xs], [], Ys, AllZipped):-
	zipAll(Xs, Ys, Ys, AllZipped).
zipAll([X|Xs], [Y|Ys], Yss, [Zs|AllZipped]):-
	zip(X, Y, Zs),
	!,
	zipAll([X|Xs], Ys, Yss, AllZipped).
zipAll([X|Xs], [Y|Ys], Yss, AllZipped):-
	zipAll([X|Xs], Ys, Yss, AllZipped).

atoms_vars([], []).
atoms_vars([A|Toms], AtomsVars):-
	atom_vars(A, AtomVars),
	atoms_vars(Toms, AVS),
	append(AtomVars, AVS, AtomsVars1),
	sort(AtomsVars1, AtomsVars).

atom_vars(Atom, AtomVars):-
	Atom =.. [_|Vars],
	sort(Vars, AtomVars).
