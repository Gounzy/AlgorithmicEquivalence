

parse(Xs,T) :-
 append(As,[a,s(A,B,C),b|Bs],Xs),
 append(As,[s(a,s(A,B,C),b)|Bs],Ys),
 parse(Ys,T).

parse(Xs,T) :-
 append(As,[a,s(A,B),b|Bs],Xs),
 append(As,[s(a,s(A,B),b)|Bs],Ys),
 parse(Ys,T).

parse(Xs,T) :-
 append(As,[a,b|Bs],Xs),
 append(As,[s(a,b)|Bs],Ys),
 parse(Ys,T).

parse([s(A,B)],s(A,B)).
parse([s(A,B,C)],s(A,B,C)).

append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]) :-
	append(Xs,Ys,Zs).
