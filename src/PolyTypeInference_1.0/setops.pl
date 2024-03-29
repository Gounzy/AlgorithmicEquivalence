% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
:- module(setops, [setintersect/3,setunion/3,setdiff/3,makeset/2,insertVal/3]).
:- use_module(library(lists)).

setintersect([],_,[]).
setintersect([X|Xs],Vs,[X|Ws]) :-memb3(X,Vs),!,setintersect(Xs,Vs,Ws).
setintersect([_|Xs],Vs,Ws) :-setintersect(Xs,Vs,Ws).

setunion([],X,X).
setunion([X|Xs],Vs,Ws) :-memb3(X,Vs),!,setunion(Xs,Vs,Ws).
setunion([X|Xs],Vs,[X|Ws]) :-setunion(Xs,Vs,Ws).

setdiff([],_,[]).
setdiff([X|Xs],Ys,Zs) :-memb3(X,Ys),!,setdiff(Xs,Ys,Zs).
setdiff([X|Xs],Ys,[X|Zs]) :-setdiff(Xs,Ys,Zs).

makeset(S1,S2) :- makeset3(S1,[],S2).
makeset3([],S,S).
makeset3([X|Xs],S0,S2) :- insertVal(X,S0,S1), makeset3(Xs,S1,S2).

memb3(X,[X1|_]) :-X == X1,!.
memb3(X,[_|Xs]) :-memb3(X,Xs).

insertVal(X,L,L) :- memb3(X,L),!.
insertVal(X,L,[X|L]).
