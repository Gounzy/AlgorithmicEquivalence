:-module(mcg, [mcg/2]).

:-use_module(generalization_utils).

mcg(Matrix, Output):-
	mcg(Matrix, [], Output).

mcg([],SoFar, SoFar):-!.
mcg([M|Matrix],  SoFar, Output) :-
		no_collisions([M|SoFar]),
		!,
		mcg(Matrix, SoFar, Output1),
		mcg(Matrix, [M|SoFar], Output2),
		length(Output1, L1),
		length(Output2, L2),
		(L1 >= L2 -> Output = Output1 ; Output = Output2).
mcg([M|Matrix], SoFar, Output):-
	mcg(Matrix, SoFar, Output).
