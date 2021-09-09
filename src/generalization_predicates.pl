:-module(generalization_predicates, [
  gen_preds/4, 
  try_all_associations/7, 
  back_to_variables_table/3,
  clauses_associations/3,
  score_pred/2]).
:-use_module(generalization_utils).
:-use_module(generalization_abstraction).
:-use_module(db).
:-use_module(utils).
:-use_module(pprint).
:-use_module(input).
:-use_module(assignment).

test:-
  set_prolog_stack(global, limit(100 000 000 000)),
  test(1).

test(0).
test(N):- format('~n ~n ------ ~n TEST ~w ~n ------ ~n', [N]),test_gen_preds, N1 is N - 1, test(N1).

test_gen_preds:-
  db:init,
  %working_directory(_, 'C:/Users/User/ownCloud/GitHub/AlgorithmicEquivalence/src'),
  %input:load_file('CLP/test.clp', Clauses1),
  db:generate_clp_preds(Clauses1, Clauses2),
  format('~n Clauses1 : ~w', [Clauses1]),
  %input:load_file('CLP/test2.clp', Clauses2),
  format('~n Clauses2 : ~w', [Clauses2]),
  gen_preds(Clauses1, Clauses2, Pred, _),
  !,
  format('~n-------------------~n~n Resulting pred :'),
  pp_print_clauses(Pred).

gen_preds(Clauses1, Clauses2, NPred, BestAAssoc) :-
  args_associations(Clauses1, Clauses2, ArgsAssociations),
    length(ArgsAssociations, LA),
    format('~n Number of argument associations : ~w', [LA]),
  clauses_associations(Clauses1, Clauses2, ClausesAssociations),
  first(Clauses1, First1),
  first(Clauses2, First2),
  clause_arity(First1, A1),
  clause_arity(First2, A2),
  random_element(ClausesAssociations, CA),
    length(ClausesAssociations, LC),
    format('~n Number of clause associations : ~w', [LC]),
  build_preds_matrix(Clauses1, Clauses2, Matrix),
    %format('~n Matrix : ~w', [Matrix]),
    %print_preds_matrix(Matrix),
    %format('~n CA : ~w', [CA]),
  get_best_ma_for_mc(Matrix, A1, A2, CA, MA),
    %format('~n Best: ~w', [MA]),
  try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, BestAAssoc, _, Pred),
  back_to_variables_table(Pred, BestAAssoc, BackToVariablesTable),
  replace(Pred, BackToVariablesTable, NPred).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, BestA, BestC, Pred):-
  try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, ClausesAssociations, []-[], 0, BestA, BestC, Pred).

try_all_associations(Clauses1, Clauses2, [], _, _, BestAssoc, _, BestA, BestC, Pred) :-
  !,
  %format('~n Best associations : ~w', [BestAssoc]),
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
  %firsts(ClauseCouplesMerged, ClauseCouplesMergedFirsts),
  %pp_print_clauses(ClauseCouplesMergedFirsts),
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

merge_clause(cl(H, Cs, Bs), ArgsAssociation, cl(HMerged, CsMerged, BsMerged)):-
  merge_atom(H, ArgsAssociation, HMerged),
  merge_constraints(Cs, ArgsAssociation, CsMerged),
  merge_atoms(Bs, ArgsAssociation, BsMerged).

merge_constraints([], _, []).
merge_constraints([C|Cs], ArgsAssociation, [CMerged|CsMerged]):-
  merge_constraint(C, ArgsAssociation, CMerged),
  merge_constraints(Cs, ArgsAssociation, CsMerged).

merge_constraint('$VAR'(I), ArgsAssociation, CMerged):-
  member(['$VAR'(I),'$VAR'(J)], ArgsAssociation),
  unique_number(I, J, N),
  atom_number(CMerged, N),
  !.
merge_constraint('$VAR'(I), ArgsAssociation, CMerged):-
  member(['$VAR'(J),'$VAR'(I)], ArgsAssociation),
  unique_number(J, I, N),
  atom_number(CMerged, N).
merge_constraint('$VAR'(I), _, '$VAR'(I)):-!.
merge_constraint(C, ArgsAssociation, CMerged):-
  C =..[F|Args],
  !,
  merge_constraints(Args, ArgsAssociation, ArgsMerged),
  CMerged =..[F|ArgsMerged].

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

au_clauses(cl(H1, C1, B1), cl(_,C2,B2), cl(H1, AUCs, AUBs)):-
  au_constraints(C1,C2,AUCs),
  au_atoms(B1,B2,AUBs).

au_constraints(C1, C2, CsOut):-
  !,
  %format('~n--- Constraints 1 : ~w ~n--- Constraints 2 : ~w', [C1, C2]),
  build_matrix(C1, C2, Matrix),
  %format('~n---Matrix : ~w', [Matrix]),
  generalization(2, 2, Matrix, [], Cs),
  take_based_on_positions(C1, Cs, CsOut).

au_atoms(B1, B2, BsOut):-
  !,
  %format('~n--- ATOMS1 : ~w ~n--- ATOMS 2 : ~w', [B1, B2]),
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

score_clause(cl(_,C,B), Score):-
  length(B, Score1),
  length(C, Score2),
  Score is Score1+Score2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_best_ma_for_mc(Matrix, Arity1, Arity2, MC, MA):-
  extract_mc_all(Matrix, Arity1, Arity2, MC, AssignmentProblem),
  %format('~n Assignment Problem: ~w',[AssignmentProblem]),
  make_square(AssignmentProblem, AP),
  %format('~n AP : ~w', [AP]), 
  set_unmarked(AP, AAP),
  %format('~n AAP: ~w', [AAP]),
  solve_assignment_problem(AAP, MA),
  %format('~n MA: ~w', [MA]),
  true.

make_square([], []).
make_square(Matrix, Matrix):-
   length(Matrix, L),
   first(Matrix, F),
   length(F, LF),
   L = LF,
   !.
make_square(Matrix, SquareMatrix):-
  length(Matrix, L),
  first(Matrix, F),
  length(F, LF),
  L < LF,
  !,
  N is LF - L,
  create_n_zero_lines(N, LF, Lines),
  append(Matrix, Lines, SquareMatrix).
make_square(Matrix, SquareMatrix):-
  length(Matrix, L),
  first(Matrix, F),
  length(F, LF),
  L > LF,
  !,
  N is L - LF,
  append_n_zeroes_to_lines(N, Matrix, SquareMatrix).

create_n_zero_lines(0, _, []):-!.
create_n_zero_lines(N, L, [Line|Lines]):-
  N > 0, !,
  N1 is N - 1,
  create_zero_line(L, Line),
  create_n_zero_lines(N1, L, Lines).
create_zero_line(0, []).
create_zero_line(Size, [0|Line]):-
  Size > 0,
  Size1 is Size - 1,
  create_zero_line(Size1, Line).

append_n_zeroes_to_lines(_, [], []).
append_n_zeroes_to_lines(N, [Line|Lines], [NLine|NLines]):-
  create_zero_line(N, ZeroLine),
  append(Line, ZeroLine, NLine),
  append_n_zeroes_to_lines(N, Lines, NLines).


extract_mc_all(Matrix, Arity1, Arity2, MC, AssignmentProblem):-
  extract_mc(Matrix, Arity1, Arity2, MC, All),
    %format('~n All : ~w', [All]),
  aggregate_mc(All, AssignmentProblem).

extract_mc(_, _, _, [], []).
extract_mc(Matrix, Arity1, Arity2, [[N,M]|ClausesAssociations], [SubMatrix|Out]):-
  NMin is Arity1 * (N - 1) + 1,
  NMax is NMin + Arity1,
  MMin is Arity2 * (M - 1) + 1,
  MMax is MMin + Arity2,
  extract_between(Matrix, NMax, NMin, MMin, MMax, [], SubMatrix),
    %format('~n SubMatrix : ~w', [SubMatrix]),
  extract_mc(Matrix, Arity1, Arity2, ClausesAssociations, Out).

extract_between(_, NMax, NMax, _, _, SubMatrix, SubMatrix):-
   !.
extract_between(Matrix, NMax, NCurrent, MMin, MMax, CurrentMatrix, SubMatrix):-
      %format('~n NCurrent : ~w', [NCurrent]),
      %format('~n Matrix : ~w', [Matrix] ),
    nth0(NCurrent, Matrix, List),
      %format('~n List from nth0 : ~w', [List]),
    extract_from_list(MMin, MMax, List, NLine),
      %format('~n Extracted line: ~w', [NLine]),
    NCurrent1 is NCurrent + 1,
    append(CurrentMatrix, [NLine], NCurrentMatrix),
    extract_between(Matrix, NMax, NCurrent1, MMin, MMax,  NCurrentMatrix, SubMatrix).

extract_from_list(Max, Max, _, []).
extract_from_list(Current, Max, List, [Elem|SubList]):-
  NCurrent is Current + 1,
  nth0(Current, List, Elem),
  extract_from_list(NCurrent, Max, List, SubList).

aggregate_mc([], []).
aggregate_mc([SubMatrix], SubMatrix).
aggregate_mc([SubMatrix1,SubMatrix2|SubMatrixes], Aggregated):-
  sum_matrices(SubMatrix1, SubMatrix2, NSubMatrix),
  %format('~n NSubMatrix : ~w', [NSubMatrix]),
  aggregate_mc([NSubMatrix|SubMatrixes], Aggregated).

sum_matrices([], [], []).
sum_matrices([Line1|Matrix1], [Line2|Matrix2], [Line|Matrix]) :-
  sum_lines(Line1, Line2, Line),
  %format('~n Sum lines: ~w', [Line]), 
  sum_matrices(Matrix1, Matrix2, Matrix).

sum_lines([], [], []).
sum_lines([Elem1|Line1], [Elem2|Line2], [ElemSum|LineSum]):-
  ElemSum is Elem1 + Elem2,
  sum_lines(Line1,Line2,LineSum).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
build_preds_matrix(Clauses1, Clauses2, Matrix):-
  build_first_line(Clauses2, Line1),
  build_preds_matrix(Clauses1, Clauses2, 1, [], Matrix1),
  append_all(Line1, Matrix1, Matrix).
build_preds_matrix([], _, _, Matrix, Matrix):-!.
build_preds_matrix([cl(H,_,_)|Clauses1], Clauses2, NC, MatrixSoFar, Matrix):-
  H =..[_|Args1],
  build_lines(Args1, NC, Clauses2, Line),
  append(MatrixSoFar, [Line], NMatrix),
  NC1 is NC + 1,
  build_preds_matrix(Clauses1, Clauses2, NC1, NMatrix, Matrix).

append_all(List1, [], List1).
append_all(List1, [List2|Lists], Out):-
  append(List1, List2, List3),
  append_all(List3, Lists, Out).

build_first_line(Clauses, [FirstLine]):-
  build_first_line(Clauses, 1, Line),
  append([' '], Line, FirstLine).
build_first_line([], _, []).
build_first_line([cl(H,_,_)|Clauses], N, Line):-
  H =..[_|Args],
  get_args_line(Args, N, 1, ArgsLine),
  N1 is N + 1,
  build_first_line(Clauses, N1, ArgsLines),
  append(ArgsLine, ArgsLines, Line).

get_args_line([], _, _, []).
get_args_line([_|Args], NC, NA, [Elem|Line]):-
  string_concat("y_", NC, Str1),
  string_concat(Str1, "^", Str2),
  string_concat(Str2, NA, Elem),
  NNA is NA + 1,
  get_args_line(Args, NC, NNA, Line).

build_lines(_, _, [], []).
build_lines(Args1, NC, Clauses, Lines):-
  all_args_clauses(Clauses, Args2),
  build_lines_clauses(Args1, Args2, NC, 1, Lines).
  %build_lines(Args1, NC, Clauses, Rest),
  %append(Lines, Rest, Line).

all_args_clauses([], []).
all_args_clauses([cl(H,_,_)|Clauses], Args):-
  all_args_clauses(Clauses, As1),
  H =..[_|As2],
  append(As1, As2, Args).

build_lines_clauses([], _, _, _, []).
build_lines_clauses([A1|Args1], Args2, NC, NA, [[Elem|Line]|Lines]):-
  build_line_clauses(A1, Args2, Line),
  string_concat("x_", NC, Str1),
  string_concat(Str1, "^", Str2),
  string_concat(Str2, NA, Elem),
  NA1 is NA + 1,
  build_lines_clauses(Args1, Args2, NC, NA1, Lines).

build_line_clauses(_, [], []).
build_line_clauses(A1, [_|Args2], [1|Line]):-
  build_line_clauses(A1, Args2, Line).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

random_element(Strs, X):-
  length(Strs, L),
  random(0, L, Index),
  nth0(Index, Strs, X).

first([H|_], H).

clause_arity(cl(H,_,_), A):-
  H =..[_|Args],
  length(Args, A).