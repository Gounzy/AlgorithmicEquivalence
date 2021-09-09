
app([],Ys,Ys).
app([X|Xs],Ys,[X|Zs]) :-
	app(Xs,Ys,Zs).
