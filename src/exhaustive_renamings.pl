:-module(exhaustive_renamings, [mcg_exhaustive_renamings/4]).
:-use_module(generalization_utils).

mcg_exhaustive_renamings(Atoms1, Atoms2, Mcg, Mapping):-
	atoms_vars(Atoms1, Vars1),
	atoms_vars(Atoms2, Vars2),
	setof(X, perm(Vars1, X), Xs),
%  format('~n Xss : ~w', [Xs]),
  length(Vars1, L1),
	setof(Y, combination(L1, Vars2, Y), Ys),
%  format('~n Ys : ~w', [Ys]),
	zipAll(Xs, Ys, AllZipped),
  variable_to_numeric_mappings(AllZipped, AllZippeds),
%  format('~n ZippedAll : ~w', [AllZippeds]),
	get_best_exhaustive(AllZippeds, Atoms1, Atoms2, Mcg, Mapping).

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
