% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
:- module(solveconstraints, [
	solveconstraints/7]).


:- use_module(library(lists)).
:- use_module(timer_ciao).
:- use_module(scc).
:- use_module(setops).
:- use_module(balanced_tree).

solveconstraints(Cs,Ss,Ts0,TDefs1,Sigs0,Sigs3,Count) :-
	start_time,
	solveLocalConstraints(Cs,Ss1),
	tidyUp(Ss1,Ss),
	end_time('Time to solve local equations: ', user_output),
	buildMaxTypes(Ss,Is1,Sigs0,Sigs1),
	genMinTypeDefs(Is1,root,Ts0),
	length(Is1,Count1),
	end_time('Time to generate unnormalised type definitions: ', user_output),
	normaliseTypes(Ts0,Ts1,Sigs1,Sigs2,Count2),
	end_time('Time to normalise: ', user_output),
	Count is Count1+Count2,
	parameterise(Ts1,TDefs1,Sigs2,Sigs3),
	end_time('Time to parametrise: ', user_output).
	
solveLocalConstraints([clauseConstraints(Cs1)|Cs0],Ss2) :-
	findEqs(Cs1,Es),
	elimEqs(Es,Cs1,Ss0,[]),
	solveLocalConstraints(Cs0,Ss1),
	append(Ss0,Ss1,Ss2).
solveLocalConstraints([],[]).
	
findEqs([],[]).
findEqs([X=Y|Cs],[X=Y|Es]) :-
	findEqs(Cs,Es).
findEqs([_ >= _|Cs],Es) :-
	findEqs(Cs,Es).
	
separateEqs([],[],[]).
separateEqs([X=Y|Cs],[X=Y|Es],Is) :-
	separateEqs(Cs,Es,Is).
separateEqs([X >= Y|Cs],Es,[X >= Y|Is]) :-
	separateEqs(Cs,Es,Is).
	
% Eliminate equations by substituting Y by X, where X=Y is the equation

elimEqs([],Cs,Cs,_).
elimEqs([Y=Y|Es],Cs,Ss,Ys) :-
	!,
	elimEqs(Es,Cs,Ss,Ys).
elimEqs([_=Y|Es],Cs,Ss,Ys) :-
	member(Y,Ys),
	!,
	elimEqs(Es,Cs,Ss,Ys).
elimEqs([X=Y|Es],Cs,Ss,Ys) :-
	substituteType(Y,X,Cs,Cs1),
	elimEqs(Es,Cs1,Ss,[Y|Ys]).
	
buildMaxTypes(Ss,Is1,Sigs0,Sigs1) :-
	separateEqs(Ss,Es,Is),
	equivClasses(Es,EquivCls),
	end_time('Time to find equivalence classes: ', user_output),
	substClasses(Is,Is1,EquivCls),
	substClasses(Sigs0,Sigs1,EquivCls).
	
substClasses(X,Y,Es0) :- % members of same class identified
	varType(X),
	findSimple(0,X,Es0,Y), 	
	!.
substClasses(Y,Y,_) :-	
	varType(Y),
	!.
substClasses(F,F1,Es) :-
	F =.. [P|Xs],
	substEachClasses(Xs,Xs1,Es),
	F1 =.. [P|Xs1].
	
substEachClasses([],[],_).
substEachClasses([X|Xs],[X1|Xs1],Es) :-
	substClasses(X,X1,Es),
	substEachClasses(Xs,Xs1,Es).
	
equivClasses(Es,EquivCls) :-
	makeEqualitiesGraph(Es,G),
	scc_sharir(G,EquivCls1),
	returnSccs(EquivCls1,EquivCls2),
	makeEquivClassIndex(EquivCls2,root,EquivCls).
	
	
makeEquivClassIndex([],T,T).
makeEquivClassIndex([[E|Es]|Cs],T0,T2) :-
	addClassNodes([E|Es],E,T0,T1),
	makeEquivClassIndex(Cs,T1,T2).
	
addClassNodes([],_,T0,T0).
addClassNodes([E|Es],R,T0,T2) :-
	insert_tree(T0,E,R,T1),
	addClassNodes(Es,R,T1,T2).
	
returnSccs([],[]).
returnSccs([(_,C)|Cs],[C|Cs1]) :-
	returnSccs(Cs,Cs1).
	
substituteType(Y,X,Y,X) :-
	varType(Y),
	!.
substituteType(Y,X,F,F1) :-
	F =.. [P|Xs],
	substEach(Xs,Y,X,Xs1),
	F1 =.. [P|Xs1].
	
substEach([],_,_,[]).
substEach([Z|Xs],Y,X,[Z1|Xs1]) :-
	substituteType(Y,X,Z,Z1),
	substEach(Xs,Y,X,Xs1).
	
tidyUp([],[]).
tidyUp([X=X|Ss],Ss1) :-	% remove identity equations
	!,
	tidyUp(Ss,Ss1).
tidyUp([X|Ss],[X|Ss1]) :-
	tidyUp(Ss,Ss1).
	
genMinTypeDefs([],Ts,Ts).
genMinTypeDefs([X>=T|Ss],Ts0,Ts2) :-
	insertCase(Ts0,X,T,Ts1,_),
	genMinTypeDefs(Ss,Ts1,Ts2).
	
insertCase(Ts0,X,T,Ts1,Chs) :-
	search_tree(Ts0,X,_),
	!,
	search_replace_tree(Ts0,X,XDefs,Ts1,XDefs1),
	insertIfNew(T,XDefs,XDefs1),
	nonNormal(XDefs1,X,Chs).
insertCase(Ts0,X,T,Ts1,[]) :-
	insert_tree(Ts0,X,[T],Ts1).
	
insertIfNew(T,Cs,Cs) :-
	member(T,Cs),
	!.
insertIfNew(T,Cs,[T|Cs]).

% Normalise types by eliminating definitions t --> ...; f(..); f(..); ...

normaliseTypes(TDefs,TList3,Sigs1,Sigs2,Count) :-
	traverse_tree(TDefs,TypeDefs),
	findAllTypes(TypeDefs,Ts,root,ECls0),
	makeNormal(Ts,TDefs,TDefs1,ECls0,ECls1,1,_,0,Count),
	%write('Finished normalising '),nl,
	traverse_tree(TDefs1,TList1),
	makeTypeDefList(TList1,TList2),
	substClasses(TList2,TList3,ECls1),
	substClasses(Sigs1,Sigs2,ECls1).

	
makeNormal([],TDefs,TDefs,ECls,ECls,J,J,N,N).
makeNormal([T|Ts],TDefs,TDefs1,ECls0,ECls2,J,J1,N0,N1) :-
	find(0,T,ECls0,ECls1,T1),
	getDef(TDefs,T1,TCases),
	!,	
	checkNormal(TCases,Ts,T1,TDefs,TDefs1,ECls1,ECls2,J,J1,N0,N1).
makeNormal([_|Ts],TDefs0,TDefs1,ECls0,ECls1,J0,J1,N0,N1) :-
	makeNormal(Ts,TDefs0,TDefs1,ECls0,ECls1,J0,J1,N0,N1).
	
findAllTypes([],[],As,As).
findAllTypes([rec(T,Fs)|TDefs],[T|Ts],As0,As3) :-
	addToTree(T,As0,As1),
	addCaseTypes(Fs,As1,As2),
	findAllTypes(TDefs,Ts,As2,As3).
	
addCaseTypes(X,As0,As1) :- 
	varType(X),
	!,
	addToTree(X,As0,As1).	
addCaseTypes(F,As0,As1) :-
	F =.. [_|Xs],
	addEachCaseTypes(Xs,As0,As1).
	
addEachCaseTypes([],As,As).
addEachCaseTypes([X|Xs],As0,As2) :-
	addCaseTypes(X,As0,As1),
	addEachCaseTypes(Xs,As1,As2).
	
addToTree(T,As0,As0) :-
	search_tree(As0,T,_),
	!.
addToTree(T,As0,As1) :-
	make(T,As0,As1).
	
getDef(Ts,T,Cs) :-
	search_tree(Ts,T,Cs).
	
removeDef(Ts0,T,Cs,Ts1) :-
	%search_tree(Ts0,T,Cs),
	search_replace_tree(Ts0,T,Cs,Ts1,removed).

checkNormal(TCases,Ts,T1,TDefs0,TDefs4,ECls0,ECls3,J0,J2,N0,N2) :-
	duplicateFunctor(TCases,F1,F2,TCases1),
	!,
	%write('Normalising '), write(T1),nl,
	makeNewCase(F1,F2,F,NewConstraints,NewEqs,J0,J1),
	length(NewConstraints,Count1),
	length(NewEqs,Count2),
	N1 is N0+Count1+Count2,
	rewriteDef(TDefs0,T1,[F|TCases1],TDefs1,Chs1),
	newContainments(NewConstraints,ECls0,ECls1,TDefs1,TDefs2,Chs2),
	updateEquivDefs(NewEqs,ECls1,ECls2,TDefs2,TDefs3,Chs3),
	setunion(Chs1,Ts,Chs4),
	setunion(Chs2,Chs4,Chs5),
	setunion(Chs3,Chs5,Ts1),
	makeNormal(Ts1,TDefs3,TDefs4,ECls2,ECls3,J1,J2,N1,N2).
checkNormal(_,Ts,_,TDefs0,TDefs1,ECls0,ECls1,J0,J1,N0,N1) :-
	%write('Skipping '),
	makeNormal(Ts,TDefs0,TDefs1,ECls0,ECls1,J0,J1,N0,N1).

updateEquivDefs([X=X|NewEqs],Es0,Es1,TDefs0,TDefs1,Chs) :-
	!,
	updateEquivDefs(NewEqs,Es0,Es1,TDefs0,TDefs1,Chs).
updateEquivDefs([X=Y|NewEqs],Es0,Es4,Ts0,Ts2,Chs) :-
	find(0,X,Es0,Es1,RX),
	find(0,Y,Es1,Es2,RY),
	mergeDefsIfAny(RX,RY,Ts0,Ts1,Chs1),		% merge equivalent defs
	link(RX,RY,Es2,Es3),				% merge equiv classes
	updateEquivDefs(NewEqs,Es3,Es4,Ts1,Ts2,Chs2),
	setunion(Chs1,Chs2,Chs).
updateEquivDefs([],Es,Es,TDefs,TDefs,[]).
	
newContainments([],Es0,Es0,TDefs,TDefs,[]).
newContainments([X>=T|NewCs],Es0,Es2,TDefs0,TDefs2,Chs) :-
	find(0,X,Es0,Es1,R),
	!,
	insertCase(TDefs0,R,T,TDefs1,Chs1),
	newContainments(NewCs,Es1,Es2,TDefs1,TDefs2,Chs2),
	setunion(Chs1,Chs2,Chs).
newContainments([X>=T|NewCs],Es0,Es2,TDefs0,TDefs2,Chs) :-
	make(X,Es0,Es1),
	insertCase(TDefs0,X,T,TDefs1,Chs1),
	newContainments(NewCs,Es1,Es2,TDefs1,TDefs2,Chs2),
	setunion(Chs1,Chs2,Chs).


mergeDefsIfAny(X,X,Ts,Ts,[]) :-
	!.
mergeDefsIfAny(RX,RY,Ts0,Ts2,Chs) :-
	removeDef(Ts0,RX,RXDef,Ts1),
	!,
	mergeDefsIntoX(RX,RY,RXDef,Ts1,Ts2,Chs).
mergeDefsIfAny(RX,RY,Ts0,Ts2,[]) :-
	removeDef(Ts0,RY,RYDef,Ts1),
	!,
	insert_tree(Ts1,RX,RYDef,Ts2).
mergeDefsIfAny(_,_,Ts,Ts,[]).

mergeDefsIntoX(RX,RY,RXDef,Ts0,Ts2,Chs) :-
	removeDef(Ts0,RY,RYDef,Ts1),
	!,
	setunion(RXDef,RYDef,XYDef),
	search_replace_tree(Ts1,RX,_,Ts2,XYDef),
	nonNormal(XYDef,RX,Chs).
mergeDefsIntoX(RX,_,RXDef,Ts0,Ts1,[]) :-
	search_replace_tree(Ts0,RX,_,Ts1,RXDef).


duplicateFunctor([F1|TCases],F1,F2,TCases1) :-
	functor(F1,P,N),
	nonTypeVar(F1),
	removeSameFunctor(TCases,P/N,F2,TCases1),
	!.
duplicateFunctor([F|TCases],F1,F2,[F|TCases1]) :-
	duplicateFunctor(TCases,F1,F2,TCases1).
	
removeSameFunctor([F2|TCases],P/N,F2,TCases) :-
	functor(F2,P,N),
	nonTypeVar(F2),
	!.
removeSameFunctor([F|TCases],P/N,F2,[F|TCases1]) :-
	removeSameFunctor(TCases,P/N,F2,TCases1).
	
rewriteDef(Ts0,T,Cs,Ts1,Ch) :-
	search_replace_tree(Ts0,T,_,Ts1,Cs),
	nonNormal(Cs,T,Ch).
	
nonNormal(Cs,T,[T]) :-
	duplicateFunctor(Cs,_,_,_),
	!.
nonNormal(_,_,[]).
	
makeNewCase(F1,F2,F,NewConstraints,NewEqs,J0,J1) :-
	F1 =.. [P|Xs],
	F2 =.. [P|Ys],
	compareArgs(Xs,Ys,Zs,NewConstraints,NewEqs,J0,J1),
	F =.. [P|Zs].
	
compareArgs([],[],[],[],[],J,J).
compareArgs([X|Xs],[Y|Ys],[X|Zs],[X>=Y|NewCs],NewEqs,J0,J1) :-
	varType(X),
	nonTypeVar(Y),
	compareArgs(Xs,Ys,Zs,NewCs,NewEqs,J0,J1).
compareArgs([X|Xs],[Y|Ys],[Y|Zs],[Y>=X|NewCs],NewEqs,J0,J1) :-
	nonTypeVar(X),
	varType(Y),
	compareArgs(Xs,Ys,Zs,NewCs,NewEqs,J0,J1).
compareArgs([X|Xs],[Y|Ys],[X|Zs],NewCs,[X=Y|NewEqs],J0,J1) :-
	varType(X),
	varType(Y),
	compareArgs(Xs,Ys,Zs,NewCs,NewEqs,J0,J1).
compareArgs([X|Xs],[Y|Ys],[NewT|Zs],[NewT>=X, NewT>=Y|NewCs],NewEqs,J0,J2) :-
	nonTypeVar(X),
	nonTypeVar(Y),
	makeNewType(J0,NewT,J1),
	compareArgs(Xs,Ys,Zs,NewCs,NewEqs,J1,J2).
	
makeNewType(J,'TYPEVAR'(T),J1) :-
	J1 is J+1,
	name('NewType_',NN),
	name(J,JN),
	append(NN,JN,TN),
	name(T,TN).
	

nonTypeVar(T) :-
	functor(T,P,N),
	v(V),
	P/N \== V/1,
	!.
nonTypeVar('TYPEVAR'(X)) :-
	\+ atom(X).

v('TYPEVAR').

varType('TYPEVAR'(X)) :-
	atom(X).

% Find the type parameters and reformulate type definitions.

parameterise(TList,TDefs1,Sigs0,Sigs1) :-
	rebuildDefTree(TList,root,Ts0),
	digraph(TList,root,Ds),
	typeSubterms(Sigs0,[],SigVs),
	stripTypeVar(SigVs,SigAs),
	findParams(TList,Ts0,Ds,root,PolyTypes, root, TypeNames,1,K),
	insertParams(SigAs,TypeNames,TypeNames1,K,_),	% include vars that appear in Sigs0
	substPolyTypeDefs(TList,TDefs1,PolyTypes,TypeNames1),
	substPolyTypeDefs(Sigs0,Sigs1,PolyTypes,TypeNames1).
	
makeTypeDefList([],[]).
makeTypeDefList([rec(_,removed)|Ts],TDefs0) :-
	!,
	makeTypeDefList(Ts,TDefs0).
makeTypeDefList([rec(T,Fs)|Ts],[typedef(T,Fs)|TDefs0]) :-
	makeTypeDefList(Ts,TDefs0).
	
rebuildDefTree([],Ts0,Ts0).
rebuildDefTree([typedef(T,Fs)|TList],Ts0,Ts2) :-
	insert_tree(Ts0,T,Fs,Ts1),
	rebuildDefTree(TList,Ts1,Ts2).

digraph([typedef(T,Cs)|Ts],Ds0,Ds2) :-
	typeSubterms(Cs,[],Ss),
	insertLinks(Ss,T,Ds0,Ds1),
	digraph(Ts,Ds1,Ds2).
digraph([],Ds,Ds).

typeSubterms(T,S,S1) :-
	varType(T),
	!,
	insertIfNew(T,S,S1).
typeSubterms(F,S0,S1) :-
	F =.. [_|Xs],
	typeSubtermsList(Xs,S0,S1).
	
typeSubtermsList([],S,S).
typeSubtermsList([X|Xs],S0,S2) :-
	typeSubterms(X,S0,S1),
	typeSubtermsList(Xs,S1,S2).
	
insertLinks([],_,Ds,Ds).
insertLinks([C|Cs],T,Ds0,Ds2) :-
	insertLink(Ds0,T,C,Ds1),
	insertLinks(Cs,T,Ds1,Ds2).
	
insertLink(Ds0,X,T,Ds1) :-
	search_replace_tree(Ds0,X,Ls,Ds1,Ls1),
	!,
	insertIfNew(T,Ls,Ls1).
insertLink(Ds0,X,T,Ds1) :-
	insert_tree(Ds0,X,[T],Ds1).
	
findParams([typedef(T,_)|Ts],TDefs,Ds,PTypes0,PTypes2,Names0,Names3,K,K3) :-
	reachable([T],Ds,[],As1),
	undefinedTypes(As1,TDefs,As),
	stripTypeVar(As,As2),
	arg(1,T,Type),
	P =.. [Type|As2],
	insert_tree(PTypes0,T,P,PTypes1),
	newShortName(K,'t',TK,K1),
	insert_tree(Names0,Type,TK,Names1),
	insertParams(As2,Names1,Names2,K1,K2),
	findParams(Ts,TDefs,Ds,PTypes1,PTypes2,Names2,Names3,K2,K3).
findParams([],_,_,Ps,Ps,Ns,Ns,K,K).

insertParams([],Ns,Ns,K,K).
insertParams([A|As],Names0,Names1,K0,K1) :-
	search_tree(Names0,A,_),
	!,
	insertParams(As,Names0,Names1,K0,K1).
insertParams([A|As],Names0,Names2,K0,K2) :-
	newShortName(K0,'X',AK0,K1),
	insert_tree(Names0,A,AK0,Names1),
	insertParams(As,Names1,Names2,K1,K2).
	
newShortName(K,Y,YK,K1) :-
	K1 is K+1,
	name(K,KN),
	name(Y,YN),
	append(YN,KN,YKN),
	name(YK,YKN).

reachable([T|Ts],Ds,Rs0,Rs1) :-
	member(T,Rs0),
	!,
	reachable(Ts,Ds,Rs0,Rs1).
reachable([T|Ts],Ds,Rs0,Rs1) :-
	links(Ds,T,Vs),
	append(Vs,Ts,Ts1),
	reachable(Ts1,Ds,[T|Rs0],Rs1).
reachable([],_,Rs,Rs).

links(Ds,T,Vs) :-
	search_tree(Ds,T,Vs),
	!.
links(_,_,[]).
	
undefinedTypes([A|As],DefinedTypes, Us) :-
	definedType(A,DefinedTypes),
	!,
	undefinedTypes(As,DefinedTypes, Us).
undefinedTypes([A|As],DefinedTypes, [A|Us]) :-
	undefinedTypes(As,DefinedTypes, Us).
undefinedTypes([],_,[]).

definedType(A,Ts) :-
	search_tree(Ts,A,_).

stripTypeVar([],[]).
stripTypeVar(['TYPEVAR'(A)|As],[A|As1]) :-
	stripTypeVar(As,As1).
	
substitutePolyType(X,TK,Es0,Ns0) :- 
	varType(X),
	search_tree(Es0,X,P), 	
	!,
	P =.. Xs,
	renameTypes(Xs,Ns0,Zs),
	TK =.. Zs.
substitutePolyType('TYPEVAR'(Y),Z,_,Ns0) :-
	varType('TYPEVAR'(Y)),
	!,
	search_tree(Ns0,Y,Z).
substitutePolyType(F,F1,Es,Ns0) :-
	F =.. [P|Xs],
	substPolyTypeDefs(Xs,Xs1,Es,Ns0),
	F1 =.. [P|Xs1].
	
substPolyTypeDefs([X|Xs],[X1|Xs1],PolyTypes,Ns0) :-
	substitutePolyType(X,X1,PolyTypes,Ns0),
	substPolyTypeDefs(Xs,Xs1,PolyTypes,Ns0).
substPolyTypeDefs([],[],_,_).

renameTypes([],_,[]).
renameTypes([X|Xs],Ns0,[Z|Zs]) :-
	search_tree(Ns0,X,Z),
	renameTypes(Xs,Ns0,Zs).
	

	
% union-find operations

find(N,T,Es0,Es1,R) :-
	search_tree(Es0,T,PT),
	N1 is N+1,
	checkRoot(N1,PT,T,R,Es0,Es1).
	
findSimple(N,T,Es0,R) :-
	search_tree(Es0,T,PT),
	N1 is N+1,
	checkRootSimple(N1,PT,T,R,Es0).
	
checkRoot(_N1,T,T,T,Es,Es) :-
	%write(N1), write('steps for find '), nl,
	!.
checkRoot(N,PT,T,R,Es0,Es2) :-
	N1 is N+1,
	find(N1,PT,Es0,Es1,R),
	search_replace_tree(Es1,T,_,Es2,R).
	
checkRootSimple(_N1,T,T,T,_) :-
	%write(N1), write('steps for simple find '), nl,
	!.
checkRootSimple(N,PT,_,R,Es0) :-
	N1 is N+1,
	findSimple(N1,PT,Es0,R).
	
make(X,Es0,Es1) :-
	insert_tree(Es0,X,X,Es1).
	
merge(X,Y,Es0,Es3) :-
	find(0,X,Es0,Es1,RX),
	find(0,Y,Es1,Es2,RY),
	search_replace_tree(Es2,RY,_,Es3,RX). 
	
link(X,X,Es,Es) :-
	!.
link(RX,RY,Es0,Es1) :-
	search_replace_tree(Es0,RY,_,Es1,RX). 