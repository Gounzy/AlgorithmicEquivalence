:-module(generalization_abstraction, [generalization/5]).
:-use_module(generalization_utils).
:-use_module(db).
:-use_module(utils).

test_swaps(Atoms1, Atoms2):-
  Atoms1 = [g('$VAR'(0),'$VAR'(0)),g('$VAR'(0),'$VAR'(2)),g('$VAR'(2),'$VAR'(1)),g('$VAR'(3),'$VAR'(1)),g('$VAR'(9),'$VAR'(2))],
  Atoms2 = [g('$VAR'(4),'$VAR'(6)),g('$VAR'(6),'$VAR'(5)),g('$VAR'(6),'$VAR'(8)),g('$VAR'(7),'$VAR'(8)),g('$VAR'(8),'$VAR'(8))].

test(C, K, W):-
  set_prolog_stack(global, limit(100 000 000 000)),
  db:class(C, Atoms1, Atoms2),
  format('~n---Atoms 1 : ~w', [Atoms1]),
  format('~n---Atoms 2 : ~w', [Atoms2]),
  build_matrix(Atoms1, Atoms2, Matrix),
  generalization(K, W, Matrix, [], Generalization),
  format('~n----Généralisation : ~w', [Generalization]),
  sequence(Generalization, Sequence),
  format('~n----Sequence : ~w', [Sequence]),
  exists_best_sequence(Matrix, Sequence, Output),
  sequence(Output, SequenceO),
  format('~n------>Found generalization ~w~n------>with sequence ~w', [Output, SequenceO])
  .
test(C, K, W):- test(C, K, W).
% quality_matrix(QualityMatrix):-
%    s(S),
%    total_matrix(TotalMatrix),
%    build_quality_matrix(TotalMatrix, S, QualityMatrix).

sort_quality_matrix(SortedMatrix):-
  quality_matrix(QualityMatrix),
  sort_quality_matrix(QualityMatrix, SortedMatrix).

sort_quality_matrix(QualityMatrix, SortedMatrix):-
  q_sort(QualityMatrix, SortedMatrix).

build_quality_matrix(Matrix, QualityMatrix):-
  build_quality_matrix(Matrix, Matrix, QualityMatrix).

build_quality_matrix([], _, []).
build_quality_matrix([M|Matrix], TotalMatrix, [M-Q|QualityMatrix]):-
  quality(M, TotalMatrix, Q),
  build_quality_matrix(Matrix, TotalMatrix, QualityMatrix).

quality(M, Matrix, Q):-
  incompatibles(M, Matrix, Incompatibles),
  length(Incompatibles, L),
  Q is 1/(L+0.000001).

incompatibles(_, [], []).
incompatibles(M, [M1|Matrix], Incompatibles):-
  no_collisions([M1,M]),
  !,
  incompatibles(M, Matrix, Incompatibles).
incompatibles(M, [M1|Matrix], [M1|Incompatibles]):-
  incompatibles(M, Matrix, Incompatibles).

generalization(K, W, TotalMatrix, CurrentPhi, Generalization) :-
  asserta(total_matrix(TotalMatrix):-!),
  build_quality_matrix(TotalMatrix, QualityMatrix1),
  %format('~n Quality Matrix before sorting : ~w', [QualityMatrix1]),
  sort_quality_matrix(QualityMatrix1, QualityMatrix),
  %format('~n Quality Matrix after sorting : ~w', [QualityMatrix]),
  asserta(quality_matrix(QualityMatrix):-!),
  firsts(QualityMatrix, TotalMatrixFirts),
  generalization1(K, W, TotalMatrixFirts, CurrentPhi, Generalization).

generalization1(K, W, TotalMatrix, CurrentPhi, Generalization) :-
  %format('~n CurrentPhi : ~w', [CurrentPhi]),
  remove_all(TotalMatrix, CurrentPhi, AvailableMatrix),
  !,
  main_loop(AvailableMatrix, AvailableMatrix, K, W, TotalMatrix, CurrentPhi, Generalization),
  !.

main_loop([], _, _, _, _, CurrentPhi, CurrentPhi).
main_loop([A|AvailableMatrix], WholeAvailableMatrix, K, W, TotalMatrix, CurrentPhi, Generalization):-
  select(A, WholeAvailableMatrix, S),
  %format('~n A : ~w', [A]),
  enforce(A, CurrentPhi, EnforcedPhi, PhiS),
  %format('~nEnforcedPhi : ~w', [EnforcedPhi]),
  %format('~nPhiS: ~w', [PhiS]),
  while_1(CurrentPhi, WholeAvailableMatrix, A, [], PhiS, S, K, W, [], [], NPhiG, NPhiS),
  %format('~n--- END WHILE 1 : NPhiS = ~w, NPhiG = ~w', [NPhiS, NPhiG]),
  length(NPhiS, LS),
  length(NPhiG, LG),
  remove_all(CurrentPhi, NPhiS, NCurrentPhi),
  append(NCurrentPhi, NPhiG, NewPhi),
  LS == LG,
  !,
  generalization1(K, W, TotalMatrix, [A|NewPhi],Generalization).
main_loop([_|AvailableMatrix], WholeAvailableMatrix, K, W, TotalMatrix, CurrentPhi, Generalization):-
  main_loop(AvailableMatrix, WholeAvailableMatrix, K, W, TotalMatrix, CurrentPhi, Generalization).


while_1(_, _, _, PhiG, PhiS, _, _, _, _, _, PhiG, PhiS):-
  length(PhiG, LG),
  length(PhiS, LG),
  !.
while_1(_, _, _, PhiG, PhiS, _, K, _, _, _, PhiG, PhiS):-
  length(PhiS, K1),
  K1 > K,
  !.
while_1(CurrentPhi, AvailableMatrix, A, PhiG, PhiS, S, K, W, GS, BS, OutPhiG, OutPhiS):-
  remove_all(CurrentPhi, PhiS, PhiSetMinusPhiS),
  %format('~nPhiSetMinusPhiS : ~w', [PhiSetMinusPhiS]),

  %remove_all(S, PhiS, SSetMinusPhiS),
  %comp([A|PhiG], SSetMinusPhiS, Comp),
  %asserta(s(Comp):-!),
  %format('~n While 1, Comp = ~w', [Comp]),

  while_2([A|PhiSetMinusPhiS], W, PhiG, PhiS, S, GS, NPhiG, NS, NewGS),
  %format('~n ------ END WHILE 2 : NPhiG = ~w, NS = ~w, NewGS = ~w', [NPhiG, NS, NewGS]),

  %remove_all(NS, PhiS, SSetMinusPhiS2),
  %format('~n SSetMinusPhiS2 : ~w', [SSetMinusPhiS2]),
  %comp([A|NPhiG], SSetMinusPhiS2, Comp2),
  %format('~n Comp2 : ~w', [Comp2]),
  %asserta(s(Comp2):-!),
  if_1(W, CurrentPhi, AvailableMatrix, A, NPhiG, PhiS, NS, BS, NewPhiG, NewPhiS, NewS, NewBS, Bottom),
  %format('~n End IF 1 : Bottom = ~w, NewPhiG = ~w, NewPhiS = ~w, NewBS = ~w', [Bottom, NewPhiG, NewPhiS, NewBS]),
  (Bottom-> (OutPhiS = PhiS, OutPhiG = PhiG) ; while_1(CurrentPhi, AvailableMatrix, A, NewPhiG, NewPhiS, NewS, K, W, NewGS, NewBS, OutPhiG, OutPhiS)).

while_2(_, _, PhiG, PhiS, S, GS, PhiG, S, GS):-
  length(PhiG, LG),
  length(PhiS, LG),
  %format('~n While_2 first branch succeeded'),
  !.
while_2(PhiSetMinusPhiS, _, PhiG, _, S, GS, PhiG, S, GS):-
  comp(PhiSetMinusPhiS, S, Comp1),
  %format('~n Comp1 : ~w ', [Comp1]),
  comp(PhiG, Comp1, Comp),
  %format('~n Comp : ~w ', [Comp]),
  length(Comp, 0), length(GS, 0),
  %format('~nWhile_2 second branch succeeded'),
  !.
while_2(PhiSetMinusPhiS, W, PhiG, PhiS, S, GS, NewPhiG, NewS, NewGS):-
  comp(PhiSetMinusPhiS, S, Comp1),
  %format('~n [1]'),
  comp(PhiG, Comp1, Comp),
    %format('~n [2]'),
  remove_duplicates(Comp, NComp),
    %format('~n [3]'),
  %%format('~n Removed duplicates: ~w', [NComp]),
  omega_max(NComp, W, R),
  %format('~n R WITH OMEGA MAX : ~w ', [R]),
  push_all(R, GS, PhiG, S, NGS),
  !,
  %format('~n Pushed ; now GS is like this : ~w', [NGS]),
  pop(NGS, NPhiG, NS, NNGS),
  %format('~n Popped ; now GS is like this : ~w', [NNGS]),
  !,
  while_2(PhiSetMinusPhiS, W, NPhiG, PhiS, NS, NNGS, NewPhiG, NewS, NewGS).
  %format('~n Inner While_2 end').

if_1(_, _, _, _, PhiG, PhiS, S, BS, PhiG, PhiS, S, BS, false):-
  length(PhiG, L),
  length(PhiS, L),
  !.
if_1(W, CurrentPhi, AvailableMatrix, A1, PhiG, PhiS, S, BS, NewPhiG, NewPhiS, NewS, NewBS, Bottom):-
  remove_all(CurrentPhi, PhiS, PhiSetMinusPhiS),
  omega_min(PhiSetMinusPhiS, W, R),
  enter_all(R, BS, PhiS, NBS),
  !,
  %format('~n Entered ; now BS is like this : ~w', [NBS]),
  if_2(NBS, AvailableMatrix, A1, PhiG, PhiS, S, NewPhiG, NewPhiS, NewS, NewBS, Bottom).

if_2([], _, _, PhiG, PhiS, S, PhiG, PhiS, S, [], true) :-!.
if_2(BS, AvailableMatrix, A1, _, _, _, [], PhiS, S, NewBS, false):-
  exit(BS, PhiS, NewBS),
  %format('~n Exited ; now BS is like this : ~w', [NewBS]),
  select(A1, AvailableMatrix, S).
  %format('~n After select, S = ~w', [S]).

enforce(M, Matrix, NewMatrix, ExpulsedElements):-
  add_if_compatible(Matrix, [M], [], NewMatrix, ExpulsedElements).

add_if_compatible([], CurrentMatrix, CurrentExpulsed, CurrentMatrix, CurrentExpulsed).
add_if_compatible([M1|Matrix], CurrentMatrix, CurrentExpulsed, NewMatrix, ExpulsedElements):-
  (no_collisions([M1|CurrentMatrix]) -> add_if_compatible(Matrix, [M1|CurrentMatrix], CurrentExpulsed, NewMatrix, ExpulsedElements)
   ; add_if_compatible(Matrix, CurrentMatrix, [M1|CurrentExpulsed], NewMatrix, ExpulsedElements)).

comp([], S, S):-!.
comp(_, [], []):-!.
comp(Phi, S, Comp):-
  get_all_compatibles(Phi, S, Comp).

get_all_compatibles(Phi, S, Comp):-
  get_all_compatibles(Phi, S, [], Comp).
get_all_compatibles(_, [], Acc, Acc):-!.
get_all_compatibles(Phi, [S|Ss], Acc, Comp):-
  append(Phi, [S], TestPhi),
  no_collisions(TestPhi),
  !,
  append(Acc, [S], NAcc),
  get_all_compatibles(Phi, Ss, NAcc, Comp).
get_all_compatibles(Phi, [_|Ss], Acc, Comp):-
  get_all_compatibles(Phi, Ss, Acc, Comp).

omega_max(Phi, W, R):-
  map_quality(Phi, PhiQuality),
  (W == 1 -> only_maxima_1(PhiQuality, R) ; only_maxima(PhiQuality, W, R)).

omega_min(Phi, W, R):-
  map_quality(Phi, PhiQuality),
  (W == 1 -> only_minima_1(PhiQuality, R) ; only_minima(PhiQuality, W, R)).

map_quality([], []).
map_quality([Phi|Ps], [Phi-Quality|Qs]):-
  quality_matrix(QM),
  member(Phi-Quality, QM),
  map_quality(Ps, Qs).

only_maxima(PhiQuality, W, R):-
  only_maxima(PhiQuality, W, [], R).

only_maxima([], _, Current, R):-
  q_sort(Current, CurrentS),
  firsts(CurrentS, R).
only_maxima([Phi-Q|PhiQuality], W, Current, R):-
  add_if_eligible_maxima(Phi-Q, W, Current, NewCurrent),
  only_maxima(PhiQuality, W, NewCurrent, R).

add_if_eligible_maxima(Phi-Q, _, Current, NewCurrent):-
  member(_-Q, Current),
  !,
  NewCurrent = [Phi-Q|Current].
add_if_eligible_maxima(Phi-Q, W, Current, NewCurrent):-
  seconds(Current, Qs),
  sort(Qs, QsSorted),
  length(QsSorted, L),
  L < W,
  !,
  NewCurrent = [Phi-Q|Current].
add_if_eligible_maxima(Phi-Q, W, Current, NewCurrent):-
  w_only_maxima([Phi-Q|Current], W, NewCurrent).

w_only_maxima(PhiQuality, W, R):-
  w_only_maxima(PhiQuality, W, [], R).
w_only_maxima([], _, Current, Current):- !.
w_only_maxima(_, W, Current, Current):- W =< 0, !.
w_only_maxima(PhiQuality, W, Current, R):-
  only_maxima_1(PhiQuality, R1),
  append(Current, R1, NewCurrent),
  %format('~n Added ~w to current maxima', [R1]),
  remove_all(PhiQuality, R1, NewPhiQuality),
  W1 is W - 1,
  w_only_maxima(NewPhiQuality, W1, NewCurrent, R).

only_minima(PhiQuality, W, R):-
  only_minima(PhiQuality, W, [], R).

only_minima([], _, Current, R):-
  q_sort(Current, CurrentS),
  firsts(CurrentS, R).
only_minima([Phi-Q|PhiQuality], W, Current, R):-
  add_if_eligible_minima(Phi-Q, W, Current, NewCurrent),
  only_minima(PhiQuality, W, NewCurrent, R).

add_if_eligible_minima(Phi-Q, _, Current, NewCurrent):-
  member(_-Q, Current),
  !,
  NewCurrent = [Phi-Q|Current].
add_if_eligible_minima(Phi-Q, W, Current, NewCurrent):-
  seconds(Current, Qs),
  sort(Qs, QsSorted),
  length(QsSorted, L),
  L < W,
  !,
  NewCurrent = [Phi-Q|Current].
add_if_eligible_minima(Phi-Q, W, Current, NewCurrent):-
  w_only_minima([Phi-Q|Current], W, NewCurrent).

w_only_minima(PhiQuality, W, R):-
  w_only_minima(PhiQuality, W, [], R).
w_only_minima([], _, Current, Current):- !.
w_only_minima(_, W, Current, Current):- W =< 0, !.
w_only_minima(PhiQuality, W, Current, R):-
  only_minima_1(PhiQuality, R1),
  append(Current, R1, NewCurrent),
  remove_all(PhiQuality, R1, NewPhiQuality),
  W1 is W - 1,
  w_only_minima(NewPhiQuality, W1, NewCurrent, R).

only_maxima_1(PhiQuality, R):-
  only_maxima_1(PhiQuality, [], R).
only_maxima_1([], Current, Current).
only_maxima_1([Phi-Q|PhiQuality], [], R):-
  only_maxima_1(PhiQuality, [Phi-Q], R).
only_maxima_1([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q == Q2,
  only_maxima_1(PhiQuality, [Phi-Q|[Phi2-Q2|Current]], R).
only_maxima_1([_-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q < Q2,
  only_maxima_1(PhiQuality, [Phi2-Q2|Current], R).
only_maxima_1([Phi-Q|PhiQuality], [_-Q2|_], R):-
  Q > Q2,
  only_maxima_1(PhiQuality, [Phi-Q], R).

only_minima_1(PhiQuality, R):-
  only_minima_1(PhiQuality, [], R).

only_minima_1([], Current, Current).
only_minima_1([Phi-Q|PhiQuality], [], R):-
  only_minima_1(PhiQuality, [Phi-Q], R).
only_minima_1([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q == Q2,
  only_minima_1(PhiQuality, [Phi-Q|[Phi2-Q2|Current]], R).
only_minima_1([_-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q > Q2,
  only_minima_1(PhiQuality, [Phi2-Q2|Current], R).
only_minima_1([Phi-Q|PhiQuality], [_-Q2|_], R):-
  Q < Q2,
  only_minima_1(PhiQuality, [Phi-Q], R).

push_all([], GS, _, _, GS).
push_all([R|Rs], GS, PhiG, S, NewGS):-
  remove_all(S, [R], SSetMinusR),
   %no_collisions([R|PhiG]) ->
    NGS = [[R|PhiG]-SSetMinusR|GS],
    %NGS = GS),
  push_all(Rs, NGS, PhiG, S, NewGS).

pop([PhiG-S|Gs], PhiG, S, Gs).

enter_all([], BS, _, BS).
enter_all([R|Rs], BS, PhiS, NewBS):-
    append(BS, [[R|PhiS]], NBS),
    %format('~n NBS : ~w', [NBS]),
    enter_all(Rs, NBS, PhiS, NewBS).

exit(BS, PhiS, NBS):-
  append([PhiS], NBS, BS).

sequence(Matrix, Sequence) :-
  map_quality(Matrix, MatrixQualities),
  %format('~n MatrixQualities : ~w', [MatrixQualities]),
  seconds(MatrixQualities, Seconds),
  %format('~n Seconds : ~w', [Seconds]),
  sort(0, @>=, Seconds, Sequence).

best_sequence_than(Sequence, TestedSequence):-
  length(Sequence, L1),
  length(TestedSequence, L2),
  L1 > L2,
  !.
%best_sequence_than([_|_], []):-!.
%best_sequence_than([A|Sequence], [A|TestedSequence]):-
%  best_sequence_than(Sequence, TestedSequence).
%best_sequence_than([A|_], [B|_]):-
%  A > B.

exists_best_sequence(Matrix, Sequence, Output):-
	mcg_sequence(Matrix, Sequence, [], Output, true).

mcg_sequence([], TestedSequence, SoFar, SoFar, IsBetter):-
  !,
  sequence(SoFar, Sequence),
  (best_sequence_than(Sequence, TestedSequence) -> IsBetter = true ; IsBetter = false).
mcg_sequence([M|Matrix], TestedSequence, SoFar, Output, IsBetter) :-
		no_collisions([M|SoFar]),
		!,
		mcg_sequence(Matrix, TestedSequence, SoFar, Output1, IsBetter1),
		mcg_sequence(Matrix, TestedSequence, [M|SoFar], Output2, IsBetter2),
    (or(IsBetter1, IsBetter2) -> IsBetter = true ; IsBetter = false),
    (IsBetter1 -> Output = Output1 ; Output = Output2).
mcg_sequence([_|Matrix], TestedSequence, SoFar, Output, IsBetter):-
	mcg_sequence(Matrix, TestedSequence, SoFar, Output, IsBetter).

or(A, _):-
  A.
or(_, B):-
  B.
