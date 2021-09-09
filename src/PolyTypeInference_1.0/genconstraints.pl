% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
:- module(genconstraints, [
	genconstraints/3]).


:- use_module(readprog).
:- use_module(library(lists)).
:- use_module(canonical).


genconstraints(F,Cs,Signatures) :-
	readprog(F,Cls),
	genConstraints(Cls,Cs,1,1,_,Signatures). 	% initialise clause and variable counters
	
genConstraints([predicates(Ps)|Cls],Cs0,1,V0,V2,Signatures) :-
	makeSignatures(Ps,Signatures),
	genConstraints1(Cls,Cs0,1,V0,V2).
genConstraints1([Cl|Cls],[clauseConstraints(Cs1)|Cs0],K,V0,V4) :-
	melt(Cl,clause((H :- B),Ws)),
	renameAndApply(Ws,K),
	renameAnonVars((H :- B),V0,V1),
	genAtomConstraints(H,Cs1,Cs2,V1,V2),
	genBodyConstraints(B,Cs2,[],V2,V3),
	K1 is K+1,
	genConstraints1(Cls,Cs0,K1,V3,V4).
genConstraints1([],[],_,V,V).


genAtomConstraints(X=Y,Cs0,Cs1,V0,V1) :-	%  constraints on =/2 args
	!,
	genEqConstraints(X,Y,Cs0,Cs1,V0,V1).
genAtomConstraints(A,Cs0,Cs1,V0,V0) :-
	functor(A,P,N),
	genArgConstraints(1,N,A,P/N,Cs0,Cs1).
	
genBodyConstraints(true,Cs,Cs,V0,V0) :-
	!.
genBodyConstraints((B,Bs),Cs0,Cs2,V0,V2) :-
	!,
	genAtomConstraints(B,Cs0,Cs1,V0,V1),
	genBodyConstraints(Bs,Cs1,Cs2,V1,V2). 
genBodyConstraints(B,Cs0,Cs1,V0,V1) :-
	genAtomConstraints(B,Cs0,Cs1,V0,V1). 
	
genEqConstraints(X,Y,[X=Y|Cs0],Cs0,V0,V0) :-
	varType(X),
	varType(Y),
	!.
genEqConstraints(X,Y,[X>=Y|Cs0],Cs0,V0,V0) :-
	varType(X),
	!.
genEqConstraints(X,Y,[Y>=X|Cs0],Cs0,V0,V0) :-
	varType(Y),
	!.
genEqConstraints(X,Y,[Z>=X, Z>=Y|Cs0],Cs0,V0,V1) :-	
	newVarName('Eq_',V0,Z),
	V1 is V0+1.
	
genArgConstraints(J,N,_,_,Cs,Cs) :-
	J > N.
genArgConstraints(J,N,A,P,[C|Cs0],Cs1) :-
	J =< N,
	J1 is J+1,
	genArgConstraint(A,J,P,C),
	genArgConstraints(J1,N,A,P,Cs0,Cs1).
	
genArgConstraint(A,J,P,T=X) :-
	arg(J,A,X),
	varType(X),
	!,
	typeName(P,J,T).
genArgConstraint(A,J,P,T >= F ) :-
	arg(J,A,F),
	%functor(F,Q,M),
	%Q/M \== 'TYPEVAR'/1,
	typeName(P,J,T).
	
makeSignatures([],[]).
makeSignatures([P/N|Ps],[PSig|Signatures]) :-
	functor(PSig,P,N),
	argTypes(1,N,P/N,PSig),
	makeSignatures(Ps,Signatures).
	
argTypes(J,N,_,_) :-
	J > N.
argTypes(J,N,P/N,PSig) :-
	J =< N,
	J1 is J+1,
	arg(J,PSig,T),
	typeName(P/N,J,T),
	argTypes(J1,N,P/N,PSig).
	
typeName(P/N,J,'TYPEVAR'(T)) :-
	typeNamePrefix(P,N,Prefix),
	name(J,JN),
	append(Prefix,JN,TName),
	name(T,TName).
	
typeNamePrefix(P,N,Prefix) :-
	name(P,PName),
	capitalize(PName,PName1),
	name(N,NName),
	name('_',Underscore),
	append(NName,Underscore,Y),
	append(PName1,Y,Prefix).
	
capitalize([P|Ps],[P1|Ps]) :-
	lowercase(P),
	!,
	P1 is P-32.
capitalize([P|Ps],[P|Ps]) :-
	uppercase(P),
	!.
capitalize(Ps,UPs) :- 	% for non-standard predicate names
	name('Type',T),
	append(T,Ps,UPs).
	
lowercase(X) :-
	X >= 95, 
	X =< 122.
	
uppercase(X) :-
	X >= 65, 
	X =< 90.
	
renameAndApply([],_).
renameAndApply([V='TYPEVAR'(V1)|Ws],K) :-
	name(V,NV),
	name(K,NK),
	append(NV,[95|NK],NV1),
	name(V1,NV1),
	renameAndApply(Ws,K).
	
renameAnonVars(T,V0,V1) :-
	var(T),
	!,
	V1 is V0+1,
	newVarName('Anon_', V0,T).
renameAnonVars(T,V0,V1) :-
	T =..[_|Xs],
	renameEachAnon(Xs,V0,V1).
	
renameEachAnon([],V0,V0).
renameEachAnon([X|Xs],V0,V2) :-
	renameAnonVars(X,V0,V1),
	renameEachAnon(Xs,V1,V2).
	
newVarName(N,J,'TYPEVAR'(V)) :-
	name(N,NN),
	name(J,JN),
	append(NN,JN,VN),
	name(V,VN).

	

varType('TYPEVAR'(X)) :-
	atom(X).