:-module(main,[]).

:-use_module(utils).
:-use_module(db).
:-use_module(au_complexity).
:-use_module(generalization_utils).
:-use_module(mcg).
:-use_module(exhaustive_renamings).
:-use_module(generalization_abstraction).
:-use_module(arguments_analysis).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Tests for arguments analysis
%%%%%%%%%%%%%%%%%%%%%%%%




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests for k-swap 
%%%%%%%%%%%%%%%%%%%%%%%%
call_time(G,T) :-
   statistics(runtime,[T0|_]),
   G,
   statistics(runtime,[T1|_]),
   T is T1 - T0.

test_class(C, K, W, N):-
	test_class(C, K, W, N, _, _).

test_class(C, K, W, N, TR, AR):-
	test_class(C, K, W, N, [], [], TR, AR).

test_class(C, K, W, 0, CTR, CAR, CTR, CAR):-
	format('~n --------------Class ~w, K = ~w, W = ~w : ', [C, K, W]),
	%format('~n Time Results : ~w', [CTR]),
	%format('~n Accuracy Results : ~w', [CAR]),
	mean_time_results(CTR, MCTR),
	format('~n Mean time results: ~w', [MCTR]),
	sum(CAR,S), length(CAR,L), MCAR is S/L,
	format('~n Mean accuracy results: ~w', [MCAR]),
	count_ones(CAR, Ones),
	NOnes is Ones / L,
	format('~n Proportion of MCG found: ~w', [NOnes]),
	format('~n').
test_class(C, K, W, N, CurrentTimeResults, CurrentAccuracyResults, TimeResults, AccuracyResults):-
	N > 0,
	set_prolog_stack(global, limit(100 000 000 000)),
	db:class(C, Atoms1, Atoms2),
	%format('~n--- ATOMS1 : ~w ~n--- ATOMS 2 : ~w', [Atoms1, Atoms2]),
	build_matrix(Atoms1, Atoms2, Matrix),
	%format('~n---Matrix : ~w', [Matrix]),
	call_time(generalization(K, W, Matrix, [], Sol), TimeGen),
	%format('~n Abstraction : ~w', [Sol]),
	length(Atoms1, L1),
	length(Atoms2, L2),
	call_time(mcg(Matrix, Mcg), TimeMcg),
	matrix_mappings(Mcg, MMCG),variable_to_numeric_mapping(MMCG, MMCGNUM),
	gen(MMCGNUM, Atoms1, Atoms2, MAXGEN),
	%format('~nMCG: ~w avec renaming ~w', [MAXGEN, MMCGNUM]),
	call_time(mcg_exhaustive_renamings3(Atoms1, Atoms2, McgVars, McgVarsMapping), TimeMcgV),
	%format('~nMCG (vars) : ~w avec renaming ~w', [McgVars, McgVarsMapping]),
	accuracy(Sol, MAXGEN, Accuracy),
	%format('~nAccuracy: ~w ', [Accuracy]),
	!,
	N1 is N - 1,
	test_class(C, K, W, N1, [TimeGen-TimeMcg-TimeMcgV|CurrentTimeResults], [Accuracy|CurrentAccuracyResults], TimeResults, AccuracyResults).

mean_time_results(TimeResults, Mean1-Mean2-Mean3):-
	firsts(TimeResults, Firsts),
	seconds(TimeResults, Seconds),
	thirds(TimeResults, Thirds),
	sum(Firsts,S1), length(Firsts,L1), Mean1 is S1/L1,
	sum(Seconds,S2), length(Firsts,L2), Mean2 is S2/L2,
	sum(Thirds,S3), length(Thirds,L3), Mean3 is S3/L3.

count_ones(List, NOnes):-
	count_ones(List, 0, NOnes).
count_ones([], NOnes, NOnes).
count_ones([1|Ls], Acc, NOnes):-
	!,
	NAcc is Acc + 1,
	count_ones(Ls, NAcc, NOnes).
count_ones([_|Ls], Acc, NOnes):-
	count_ones(Ls, Acc, NOnes).

accuracy(_, [], 1):-!.
accuracy(Gen1, Gen2, Accuracy):-
	length(Gen1, L1),
	length(Gen2, L2),
	Accuracy is L1/L2.
