

literal(z0).
literal(z1).
literal(z2).
literal(z3).
literal(z4).
literal(z5).
literal(z6).
literal(z7).
literal(z8).
literal(z9).
literal(n(X))  :-  literal(X).


norm(X, X)  :- literal(X).
norm(o(X, Y), o(X, Y))  :- literal(X), literal(Y).
norm(a(X, Y), a(X, Y))  :- literal(X), literal(Y).


norm(o(X, Y), o(X1, Y))  :-
           literal(Y),
           norm(X, X1).
norm(o(X, o(Y, Z)), W)  :-
           norm(o(o(X, Y), Z), W).
norm(o(X, a(Y1, Y2)), o(X1, Y12))  :-
           norm(X, X1),
           norm(a(Y1, Y2), Y12).


norm(a(X, Y), a(X1, Y))  :-
           literal(Y),
           norm(X, X1).
norm(a(X, a(Y, Z)), W)  :-
           norm(a(a(X, Y), Z), W).
norm(a(X, o(Y1, Y2)), a(X1, Y12))  :-
           norm(X, X1),
           norm(o(Y1, Y2), Y12).



dnf(X, X)  :-  literal(X).
dnf(o(X, Y), o(X, Y))  :-  literal(X), literal(Y).
dnf(a(X, Y), a(X, Y))  :-  literal(X), literal(Y).


dnf(n(n(X)), W)  :-  dnf(X, W).
dnf(n(o(X, Y)), W)  :-  dnf(a(n(X), n(Y)), W).
dnf(n(a(X, Y)), W)  :-  dnf(o(n(X), n(Y)), W).

dnf(o(X, Y), W)  :-
           dnf(X, X1),
           dnf(Y, Y1),
           norm(o(X1, Y1), W).
dnf(a(X, Y), a(a(X1, X2), Y))  :-
           literal(Y),
           dnf(X, a(X1, X2)).
dnf(a(X, Y), a(a(Y1, Y2), X))  :- 
	     literal(X),
           dnf(Y, a(Y1, Y2)).
dnf(a(X, Y), W)  :-
           dnf(X, a(X1, X2)),
           dnf(Y, a(Y1, Y2)),
           norm(a(a(X1, X2), a(Y1, Y2)), W).
dnf(a(X, Y), W)  :-
           dnf(X, o(X1, X2)),
           dnf(Y, Y1),
           dnf(o(a(X1, Y1), a(X2, Y1)), W).
dnf(a(X, Y), W)  :-
           dnf(X, X1),
           dnf(Y, o(Y1, Y2)),
           dnf(o(a(X1, Y1), a(X1, Y2)), W).



ex :- dnf(_,a(z1, o(z2,z3))).
