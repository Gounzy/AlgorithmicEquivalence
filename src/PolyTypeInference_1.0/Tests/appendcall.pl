
app([],Ys,Ys).
app([X|Xs],Ys,[X|Zs]) :-
	%p2(X),
	app(Xs,Ys,Zs).

p(R) :-
	app([a],[b],M),
	app([M],[M],R).