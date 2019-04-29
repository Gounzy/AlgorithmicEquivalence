:-module(generalization_abstraction, [generalization/4]).
:-use_module(generalization_utils).
:-use_module(db).

test:-
  db:class_2(Atoms1, Atoms2),
  build_matrix(Atoms1, Atoms2, Matrix),
  build_quality_matrix(Matrix, QualityMatrix),
  asserta(quality_matrix(QualityMatrix):-!),
  generalization(4, Matrix, [], Generalization),
  format('~n Généralisation : ~w', [Generalization]).

build_quality_matrix(Matrix, QualityMatrix):-
  build_quality_matrix(Matrix, Matrix, QualityMatrix).

build_quality_matrix([], _, []).
build_quality_matrix([M|Matrix], TotalMatrix, [M-Q|QualityMatrix]):-
  quality(M, TotalMatrix, Q),
  build_quality_matrix(Matrix, TotalMatrix, QualityMatrix).

quality(M, Matrix, Q):-
  incompatibles(M, Matrix, Incompatibles),
  length(Incompatibles, L),
  Q is 1/L.

incompatibles(M, [], []).
incompatibles(M, [M1|Matrix], Incompatibles):-
  no_collisions([M1,M]),
  !,
  incompatibles(M, Matrix, Incompatibles).
incompatibles(M, [M1|Matrix], [M1|Incompatibles]):-
  incompatibles(M, Matrix, Incompatibles).

generalization(K, TotalMatrix, CurrentPhi, Generalization) :-
  format('~n CurrentPhi : ~w', [CurrentPhi]),
  remove_all(TotalMatrix, CurrentPhi, AvailableMatrix),
  !,
  main_loop(AvailableMatrix, AvailableMatrix, K, TotalMatrix, CurrentPhi, Generalization).

main_loop([], WholeAvailableMatrix, K, TotalMatrix, CurrentPhi, CurrentPhi).
main_loop([A|AvailableMatrix], WholeAvailableMatrix, K, TotalMatrix, CurrentPhi, Generalization):-
  select(A, WholeAvailableMatrix, S),
  %format('~n A : ~w', [A]),
  enforce(A, CurrentPhi, EnforcedPhi, PhiS),
  %format('~nEnforcedPhi : ~w', [EnforcedPhi]),
  %format('~nPhiS: ~w', [PhiS]),
  while_1(CurrentPhi, AvailableMatrix, A, [], PhiS, S, K, [], [], NPhiG, NPhiS),
  %format('~nNPhiS: ~w', [NPhiS]),
  %format('~nNPhiG: ~w', [NPhiG]),
  length(NPhiS, LS),
  length(NPhiG, LG),
  remove_all(CurrentPhi, NPhiS, NCurrentPhi),
  append(NCurrentPhi, NPhiG, NewPhi),
  LS == LG,
  !,
  generalization(K, TotalMatrix, [A|NewPhi],Generalization).
main_loop([_|AvailableMatrix], WholeAvailableMatrix, K, TotalMatrix, CurrentPhi, Generalization):-
  main_loop(AvailableMatrix, WholeAvailableMatrix, K, TotalMatrix, CurrentPhi, Generalization).

enforce(M, Matrix, NewMatrix, ExpulsedElements):-
  add_if_compatible(Matrix, [M], [], NewMatrix, ExpulsedElements).

add_if_compatible([], CurrentMatrix, CurrentExpulsed, CurrentMatrix, CurrentExpulsed).
add_if_compatible([M1|Matrix], CurrentMatrix, CurrentExpulsed, NewMatrix, ExpulsedElements):-
  (no_collisions([M1|CurrentMatrix]) -> add_if_compatible(Matrix, [M1|CurrentMatrix], CurrentExpulsed, NewMatrix, ExpulsedElements) ; add_if_compatible(Matrix, CurrentMatrix, [M1|CurrentExpulsed], NewMatrix, ExpulsedElements)).

while_1(CurrentPhi, AvailableMatrix, A1, PhiG, PhiS, S, K, GS, BS, PhiG, PhiS):-
  length(PhiG, LG),
  length(PhiS, LG),
  !.
while_1(CurrentPhi, AvailableMatrix, A1, PhiG, PhiS, S, K, GS, BS, PhiG, PhiS):-
  length(PhiS, K),
  !.
while_1(CurrentPhi, AvailableMatrix, A1, PhiG, PhiS, S, K, GS, BS, OutPhiG, OutPhiS):-
  remove_all(CurrentPhi, PhiS, PhiSetMinusPhiS),
  %format('~nPhiSetMinusPhiS : ~w', [PhiSetMinusPhiS]),
  while_2(PhiSetMinusPhiS, PhiG, PhiS, S, GS, NPhiG, NS, NewGS),
  if_1(CurrentPhi, AvailableMatrix, A1, NPhiG, PhiS, NS, BS, NewPhiG, NewPhiS, NewS, NewBS, Bottom),
  (Bottom-> OutPhiS = NewPhiS, OutPhiG = NewPhiG ; while_1(CurrentPhi, AvailableMatrix, A1, NewPhiG, NewPhiS, NewS, K, NewGS, NewBS, OutPhiG, OutPhiS)).

while_2(PhiSetMinusPhiS, PhiG, PhiS, S, GS, PhiG, S, GS):-
  length(PhiG, LG),
  length(PhiS, LG),
  !.
while_2(PhiSetMinusPhiS, PhiG, PhiS, S, GS, PhiG, S, GS):-
  comp(PhiSetMinusPhiS, S, Comp1),
  comp(PhiG, Comp1, Comp),
  (length(Comp, 0) -> true ; length(GS, 0)),
  !.
while_2(PhiSetMinusPhiS, PhiG, PhiS, S, GS, NewPhiG, NewS, NewGS):-
  comp(PhiSetMinusPhiS, S, Comp1),
  comp(PhiG, Comp1, Comp),
  omega_max(Comp, R),
  push_all(R, GS, PhiG, S, NGS),
  !,
  %format('~n Pushed ; now GS is like this : ~w', [NGS]),
  pop(NGS, NPhiG, NS, NNGS),
  %format('~n Popped ; now GS is like this : ~w', [NNGS]),
  !,
  while_2(PhiSetMinusPhiS, NPhiG, PhiS, NS, NNGS, NewPhiG, NewS, NewGS).

if_1(CurrentPhi, AvailableMatrix, A1, PhiG, PhiS, S, BS, PhiG, PhiS, S, BS, false):-
  length(PhiG, L),
  length(PhiS, L),
  !.
if_1(CurrentPhi, AvailableMatrix, A1, PhiG, PhiS, S, BS, NewPhiG, NewPhiS, NewS, NewBS, Bottom):-
  remove_all(CurrentPhi, PhiS, PhiSetMinusPhiS),
  omega_min(PhiSetMinusPhiS, R),
  enter_all(R, BS, PhiS, NBS),
  !,
  %format('~n Entered ; now BS is like this : ~w', [NBS]),
  if_2(NBS, AvailableMatrix, A1, PhiG, PhiS, S, NewPhiG, NewPhiS, NewS, NewBS, Bottom).

if_2([], _, _, PhiG, PhiS, S, PhiG, PhiS, S, [], true) :-!.
if_2(BS, AvailableMatrix, A1, _, _, _, [], PhiS, S, NewBS, false):-
  exit(BS, PhiS, NewBS),
  %format('~n Exited ; now BS is like this : ~w', [NewBS]),
  select(A1, AvailableMatrix, S).

comp(Phi, S, Comp):-
  add_if_compatible(S, Phi, [], Comp, _).

omega_max(Phi, R):-
  map_quality(Phi, PhiQuality),
  only_maxima(PhiQuality, R).

omega_min(Phi, R):-
  map_quality(Phi, PhiQuality),
  only_minima(PhiQuality, R).

map_quality([], []).
map_quality([Phi|Ps], [Phi-Quality|Qs]):-
  quality_matrix(QM),
  member(Phi-Quality, QM),
  map_quality(Ps, Qs).

only_maxima(PhiQuality, R):-
  only_maxima(PhiQuality, [], R).

only_maxima([], Current, R):-
  firsts(Current, R).
only_maxima([Phi-Q|PhiQuality], [], R):-
  only_maxima(PhiQuality, [Phi-Q], R).
only_maxima([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q == Q2,
  only_maxima(PhiQuality, [Phi-Q|[Phi2-Q2|Current]], R).
only_maxima([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q < Q2,
  only_maxima(PhiQuality, [Phi2-Q2|Current], R).
only_maxima([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q > Q2,
  only_maxima(PhiQuality, [Phi-Q], R).

only_minima(PhiQuality, R):-
  only_minima(PhiQuality, [], R).

only_minima([], Current, R):-
  firsts(Current, R).
only_minima([Phi-Q|PhiQuality], [], R):-
  only_minima(PhiQuality, [Phi-Q], R).
only_minima([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q == Q2,
  only_minima(PhiQuality, [Phi-Q|[Phi2-Q2|Current]], R).
only_minima([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q > Q2,
  only_minima(PhiQuality, [Phi2-Q2|Current], R).
only_minima([Phi-Q|PhiQuality], [Phi2-Q2|Current], R):-
  Q < Q2,
  only_minima(PhiQuality, [Phi-Q], R).

firsts([], []).
firsts([A-_|Zipped], [A|Firsts]):-
  firsts(Zipped, Firsts).

push_all([], GS, _, _, GS).
push_all([R|Rs], GS, PhiG, S, NewGS):-
  remove_all(S, [R], SSetMinusR),
  sort([R|PhiG], NPhiG),
  (no_collisions(NPhiG) -> NGS = [NPhiG-SSetMinusR|GS] ; NGS = GS),
  push_all(Rs, NGS, PhiG, S, NewGS).

pop([PhiG-S|Gs], PhiG, S, Gs).

enter_all([], BS, _, BS).
enter_all([R|Rs], BS, PhiS, NewBS):-
    append(BS, [R|PhiS], NBS),
    enter_all(Rs, NBS, PhiS, NewBs).

exit(BS, PhiS, NBS):-
  append(NBS, [PhiS], BS).
