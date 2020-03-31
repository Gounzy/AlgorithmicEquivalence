:-module(generalization_predicates, []).
:-use_module(generalization_utils).
:-use_module(generalization_abstraction).
:-use_module(db).
:-use_module(utils).
:-use_module(pprint).
:-use_module(input).

% Génération de prédicats et tests en série svp
% débug 

test_gen_preds:-
  db:init,
  working_directory(_, 'C:/Users/User/ownCloud/GitHub/AlgorithmicEquivalence/src'),
  %input:load_file('CLP/test.clp', Clauses1),
  db:generate_clp_preds(Clauses1, Clauses2),
  format('~n Clauses1 : ~w', [Clauses1]),
  %input:load_file('CLP/test2.clp', Clauses2),
  format('~n Clauses2 : ~w', [Clauses2]),
  gen_preds(Clauses1, Clauses2, Pred),
  !,
  format('~n-------------------~n~n Resulting pred :'),
  pp_print_clauses(Pred).

gen_preds(Clauses1, Clauses2, NPred) :-
  args_associations(Clauses1, Clauses2, ArgsAssociations),
    format('~n Argument associations : ~w', [ArgsAssociations]),
  clauses_associations(Clauses1, Clauses2, ClausesAssociations),
    format('~n Clause associations : ~w', [ClausesAssociations]),
  try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, BestAAssoc, _, Pred),
  back_to_variables_table(Pred, BestAAssoc, BackToVariablesTable),
  replace(Pred, BackToVariablesTable, NPred),
  true.

args_associations([cl(H1,_,_)|_], [cl(H2,_,_)|_], ArgsAssociations):-
  !,
  args_associations(H1, H2, ArgsAssociations).
args_associations(H1, H2, ArgsAssociations):-
  H1 =..[_|Args1],
  H2 =..[_|Args2],
  get_associations(Args1, Args2, ArgsAssociations).

clauses_associations(Clauses1, Clauses2, ClausesAssociations):-
  length(Clauses1, L1),
  length(Clauses2, L2),
  intlist(L1, List1),
  intlist(L2, List2),
  get_associations(List1, List2, ClausesAssociations).

intlist(0, []):-!.
intlist(N, List):-
  N1 is N - 1,
  intlist(N1, List1),
  append(List1, [N], List).

get_associations(List1, List2, Associations):-
  product(List1, List2, Product),
  create_associations_from_cartesian_product(Product, Associations).

create_associations_from_cartesian_product(Product, Associations):-
  findall(Ass, create_associations_from_cartesian_product(Product, [], Ass), Associations).
create_associations_from_cartesian_product([], As, As):-!.
create_associations_from_cartesian_product([[E1, _]|Es], CurrentAs, As):-
  member([E1,_], CurrentAs),
  !,
  create_associations_from_cartesian_product(Es, CurrentAs, As).
create_associations_from_cartesian_product([[_, E2]|Es], CurrentAs, As):-
  member([_,E2], CurrentAs),
  !,
  create_associations_from_cartesian_product(Es, CurrentAs, As).
create_associations_from_cartesian_product([[E1, E2]|Es], CurrentAs, As):-
  create_associations_from_cartesian_product(Es, [[E1,E2]|CurrentAs], As).
create_associations_from_cartesian_product([[_,_]|Es], CurrentAs, As):-
  create_associations_from_cartesian_product(Es, CurrentAs, As).

product(L1,L2,L3):- product(L1,L2,L3,L1).
% stop when both List1 and List2 are empty
product(_, [], [], _):-!.
% first list is empty, recreate it and work it again with the next element of second list (and shorten memory)
product([], [_|T2], List3, L4):-
    !,
    product(L4, T2, List3, L4).
%go through first list and always first element of second list to our answer
product([H1|T1], [H2|T2], [[H1,H2]|T3], List4):-
    !,
    product(T1, [H2|T2], T3, List4).

try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, BestA, BestC, Pred):-
  try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, ClausesAssociations, []-[], 0, BestA, BestC, Pred).

try_all_associations(Clauses1, Clauses2, [], _, _, BestAssoc, _, BestA, BestC, Pred) :-
  !,
  format('~n Best associations : ~w', [BestAssoc]),
  BestAssoc = BestA-BestC,
  au_pred(Clauses1, Clauses2, BestAssoc, Pred, _).

try_all_associations(Clauses1, Clauses2, [_|ArgsAssociations], [], AllClausesAssociations, BestAssoc, BestScore, BestA, BestC, Pred):-
  !,
  try_all_associations(Clauses1, Clauses2, ArgsAssociations, AllClausesAssociations, AllClausesAssociations, BestAssoc, BestScore, BestA, BestC, Pred).

try_all_associations(Clauses1, Clauses2, [A|ArgsAssociations], [C|ClausesAssociations], AllClausesAssociations, BestAssoc, BestScore, BestA, BestC, Pred):-
  au_pred(Clauses1, Clauses2, A-C, _, Score),
  (Score > BestScore -> NBestScore is Score, NBestAssoc = A-C
                     ; NBestScore is BestScore, NBestAssoc = BestAssoc),
  try_all_associations(Clauses1, Clauses2, [A|ArgsAssociations], ClausesAssociations, AllClausesAssociations, NBestAssoc, NBestScore, BestA, BestC, Pred).

au_pred(Clauses1, Clauses2, A-C, Pred, Score):-
  extract_clauses_from_mapping(Clauses1, Clauses2, C, ClauseCouples),
  merge_arguments_from_mapping(ClauseCouples, A, ClauseCouplesMerged),
  au_pred(ClauseCouplesMerged, Pred),
  score_pred(Pred, Score).

back_to_variables_table([], _, []).
back_to_variables_table([cl(H,_,_)|_], ArgumentsMapping, Table):-
  H =..[_|Args],
  map_to_variables(Args, ArgumentsMapping, Table).

map_to_variables([], _, []).
map_to_variables(['$VAR'(_)|Args], ArgumentsMapping, Table):-
  !,
  map_to_variables(Args, ArgumentsMapping, Table).
map_to_variables([N|Args], ArgumentsMapping, [(N,Var)|Table]):-
  merge_atom(Var, ArgumentsMapping, N),
  map_to_variables(Args, ArgumentsMapping, Table).

extract_clauses_from_mapping(Clauses1, Clauses2, C, ClauseCouples):-
  extract_clauses_from_mapping(Clauses1, Clauses2, C, [], ClauseCouples).
extract_clauses_from_mapping(_, _, [], Extracted, Extracted).
extract_clauses_from_mapping(Clauses1, Clauses2, [[N1,N2]|C], Extracted, ClauseCouples):-
  nth1(N1, Clauses1, Clause1),
  nth1(N2, Clauses2, Clause2),
  extract_clauses_from_mapping(Clauses1, Clauses2, C, [Clause1-Clause2|Extracted], ClauseCouples).

merge_arguments_from_mapping(ClausesCouples, A, ClauseCouplesMerged):-
  merge_arguments_from_mapping(ClausesCouples, A, [], ClauseCouplesMerged).
merge_arguments_from_mapping([], _, ClauseCouplesMerged, ClauseCouplesMerged).
merge_arguments_from_mapping([Clause1-Clause2|ClauseCouples], A, Merged, ClauseCouplesMerged):-
  merge_clause(Clause1, A, Merged1),
  merge_clause(Clause2, A, Merged2),
  merge_arguments_from_mapping(ClauseCouples, A, [Merged1-Merged2|Merged], ClauseCouplesMerged).

merge_clause(cl(H, Cs, Bs), ArgsAssociation, cl(HMerged, Cs, BsMerged)):-
  merge_atom(H, ArgsAssociation, HMerged),
  merge_atoms(Bs, ArgsAssociation, BsMerged).

merge_atoms([], _, []).
merge_atoms([B|Bs], ArgsAssociation, [BMerged|BsMerged]):-
  merge_atom(B, ArgsAssociation, BMerged),
  merge_atoms(Bs, ArgsAssociation, BsMerged).

merge_atom('$VAR'(I), ArgsAssociation, BMerged):-
  member(['$VAR'(I),'$VAR'(J)], ArgsAssociation),
  unique_number(I, J, N),
  atom_number(BMerged, N),
  !.
merge_atom('$VAR'(I), ArgsAssociation, BMerged):-
  member(['$VAR'(J),'$VAR'(I)], ArgsAssociation),
  unique_number(J, I, N),
  atom_number(BMerged, N).
merge_atom('$VAR'(I), _, '$VAR'(I)):-!.
merge_atom(B, ArgsAssociation, BMerged):-
  B =..[F|Args],
  !,
  merge_atoms(Args, ArgsAssociation, ArgsMerged),
  BMerged =..[F|ArgsMerged].

unique_number(I, J, N):-
  number_string(I, IS),
  number_string(J, JS),
  string_concat(IS, "000", ISC),
  string_concat(ISC, JS, JSC),
  number_string(N, JSC).

au_pred(ClauseCouples, Pred):-
  au_pred(ClauseCouples, [], Pred).
au_pred([], Pred, Pred).
au_pred([C1-C2|ClauseCouples], CurrentPred, Pred):-
  au_clauses(C1, C2, AUClause),
  au_pred(ClauseCouples, [AUClause|CurrentPred], Pred).

au_clauses(cl(H1, C1, B1), cl(_,_,B2), cl(H1,C1, AUBs)):-
  au_atoms(B1,B2,AUBs).

au_atoms(B1, B2, BsOut):-
  %format('~n--- ATOMS1 : ~w ~n--- ATOMS 2 : ~w', [Atoms1, Atoms2]),
  build_matrix(B1, B2, Matrix),
  %format('~n---Matrix : ~w', [Matrix]),
  generalization(2, 2, Matrix, [], Bs),
  take_based_on_positions(B1, Bs, BsOut).

take_based_on_positions(_, [], []).
take_based_on_positions(Atoms, [_/Position/_/_|PositionsList], [Atom|AtomsOut]):-
  nth0(Position, Atoms, Atom),
  take_based_on_positions(Atoms, PositionsList, AtomsOut).

score_pred([], 0).
score_pred([Cl|Clauses], Score):-
  score_clause(Cl, ScoreCl),
  score_pred(Clauses, Score1),
  Score is Score1 + ScoreCl.

score_clause(cl(_,_,B), Score):-
  length(B, Score).
