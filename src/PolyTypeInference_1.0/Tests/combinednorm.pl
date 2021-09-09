p([X]).
p([s(s(X)), Y|Xs]) :-
	p([X,Y|Xs]),
	p([s(s(s(s(Y))))|Xs]).
p([0|Xs]) :-
	p(Xs).



transpose(A,B) :-
	transpose_aux(A,[],B).

transpose_aux([R|Rs],_,[C|Cs]) :-
	row2col(R,[C|Cs],Cols1,[],Accm),
	transpose_aux(Rs,Accm,Cols1).
transpose_aux([],X,X).

row2col([X|Xs], [[X|Ys]|Cols], [Ys|Cols1],A,B) :-
	row2col(Xs, Cols, Cols1,[[]|A],B).
row2col([], [], [],A,A).
	

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


ackermann(0,N,s(N)).
ackermann(s(M),0,Res) :-
	ackermann(M,s(0),Res).
ackermann(s(M),s(N),Res) :-
	ackermann(s(M),N,Res1),
	ackermann(M,Res1,Res).
