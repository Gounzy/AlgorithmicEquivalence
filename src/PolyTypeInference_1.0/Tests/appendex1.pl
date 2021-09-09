
p(R) :- app([a],[b],M), app([M],[M],R).

app([],Ys,Ys).
app([X|Xs],Ys,[X|Zs]) :-
	app(Xs,Ys,Zs).



p1(R) :- app1([a],[b],M), app2([M],[M],R).

app1([],Ys,Ys).
app1([X|Xs],Ys,[X|Zs]) :-
	app1(Xs,Ys,Zs).
	
app2([],Ys,Ys).
app2([X|Xs],Ys,[X|Zs]) :-
	app2(Xs,Ys,Zs).