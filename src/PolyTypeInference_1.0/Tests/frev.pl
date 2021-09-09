rev([],X,X).
rev([X|Xs],Ys,Zs) :-
	rev(Xs,Ys,[X|Zs]).

