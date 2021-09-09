p([X]).
p([s(s(X)), Y|Xs]) :-
	p([X,Y|Xs]),
	p([s(s(s(s(Y))))|Xs]).
p([0|Xs]) :-
	p(Xs).
