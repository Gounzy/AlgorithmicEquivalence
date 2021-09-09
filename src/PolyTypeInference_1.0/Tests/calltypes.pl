ap1([]).
ap1([X|Y]) :- x(X),ap1(Y).

ap3([X|Y]) :- x(X),ap3(Y).
%
ap2(X) :- ap3(X).

ap1c([]).
ap1c([X|Y]) :- xc(X),ap1c(Y).

ap3c([X|Y]) :- xc(X),ap3c(Y).
%

ap2c(X) :- ap3c(X).

ap1c([a]).
ap2c([b]).
ap3c(X) :- m(X).

ap1c([X]) :- m(X).
ap2c([X]) :- m(X).

ap3c(X).

%ap1(X) :- ap1c(X).
%ap2(X) :- ap2c(X).
%ap3(X) :- ap3c(X).

x(X) :- ap3(X).
