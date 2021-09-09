% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
:- module(readprog, [readprog/2, 
		sortClauses/3, 
		user_clauses/3]).


:- op(750,fx,type).
% 
% Limitations.  Input program consists of definite clauses.
%               Doesn't handle metagoals like if-then-else, disjunction, bagof etc.
%               Maybe the ciaopp program parser will enable this later.

% Usage 1
% readprog(+File,-Program).

% +File - a filename containing the program to be transformed
% -Program - a list containing the program clauses.
%            - first element of list a term predicates(Ps) where Ps
%              is a list of the predicates in the transformed program.
%            - remaining elements, terms clause((H :- B), Vs) where H:-B
%              is a clause, Vs is a binding list with the
%              original variable names.
%           
%
% Example query (using naive reverse program)
%
%       ?- readprog('rev.pl', Cls).
%
% Ps = [predicates([rev/2,app/3]),
%       cl((rev([],[]):-true),[]),
%       cl((rev([_B|_C],_D):-rev(_C,_A),app(_A,[_B],_D)),
%              ['Ws'=_A,'X'=_B,'Xs'=_C,'Ys'=_D]),
%       cl((app([],_E,_E):-true),['Ys'=_E]),
%       cl((app([_F|_G],_H,[_F|_I]):-app(_G,_H,_I)),
%              ['X'=_F,'Xs'=_G,'Ys'=_H,'Zs'=_I])] 




:- use_module(library(lists)).
:- use_module(canonical).



readprog(F,Prog) :-
	open(F,read,Stream),
	readprog1(Stream,  _ClauseCount, Prog),
	close(Stream).
	%write(user_output,'Finished reading '),
	%write(user_output,F),
	%nl(user_output),
	%write(user_output,'Number of clauses: '), 
	%write(user_output,ClauseCount),
	%nl(user_output).


readprog1(Stream, Clausecount,[predicates(Ps)|Prog]) :-
	read_clause1(Stream, C),
	read_clauses(Stream, C,Ps,0, Clausecount,Prog),
	!.
readprog1(_,0,[]) :-
	write(user_error,'Problems while reading file '), 
	nl(user_error).

read_clauses(_,cl(end_of_file,_),Ps,N,N,[]) :- 
	!,
	close_list(Ps).
	%write(user_output,'Number of predicates: '), 
	%length(Ps, PN),
	%write(user_output,PN),
	%nl(user_output).
read_clauses(Stream,cl((:- module(_,_)),_),Ps,K,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,K,M,Out).
read_clauses(Stream,cl((:- include(_)),_),Ps,K,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,K,M,Out).
read_clauses(Stream,cl((:- use_module(_,_)),_),Ps,K,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,K,M,Out).
read_clauses(Stream,cl((:- use_module(_)),_),Ps,K,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,K,M,Out).
read_clauses(Stream,cl((:- entry(_,_)),_),Ps,N,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,N,M,Out).
read_clauses(Stream,cl((:- multifile _),_),Ps,N,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,N,M,Out).
read_clauses(Stream,cl((:- filter(F)),Vs),Ps,N,M,
				[clause((filter(F) :- true),Vs)|Out]) :-
	!,
	canonical(F),
	memb1(filter/1,Ps),
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,N,M,Out).
read_clauses(Stream,cl((:-residual(F)),Vs),Ps,N,M,
				[clause((residual(F) :- true),Vs)|Out]) :-
	!,
	canonical(F),
	memb1(residual/1,Ps),
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,N,M,Out).
read_clauses(Stream,cl((:- type(_)),_),Ps,K,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,K,M,Out).


read_clauses(Stream,cl((:- dynamic(_)),_),Ps,K,M,Out) :-
	!,
	read_clause1(Stream,C1),
	read_clauses(Stream,C1,Ps,K,M,Out).
read_clauses(Stream,cl((:- Dir),_),Ps,N,M,Out) :- 
	!,
	call(Dir),
	read_clause1(Stream,C1),
	!,
	read_clauses(Stream,C1,Ps,N,M,Out).
read_clauses(Stream,cl((H :- B),Vs),Ps,N,M,[clause((H :- B),Vs)|Out]) :- 
	!,
	canonical((H:-B)),
	get_pred_name((H :- B),Pred,Bodypreds),
	each_memb1([Pred|Bodypreds],Ps),
	N1 is N+1,
	read_clause1(Stream,C1),
	!,
	read_clauses(Stream,C1,Ps,N1,M,Out).
read_clauses(Stream,cl(H,Vs),Ps,N,M,[clause((H :- true),Vs)|Out]) :- 
	!,
	canonical(H),
	get_pred_name((H :- true),Pred,Bodypreds),
	each_memb1([Pred|Bodypreds],Ps),
	N1 is N+1,
	read_clause1(Stream,C1),
	!,
	read_clauses(Stream,C1,Ps,N1,M,Out).
read_clauses(_,_,_,_,_,[]) :-
	write(user_error,'Error reading program.'),
	nl(user_error).


get_pred_name((H :- B),P/N,BPs) :-
	!,
	functor(H,P,N),
	body_preds(B,BPs).
get_pred_name(H ,P/N,[]) :-
	functor(H,P,N).

body_preds(true,[]) :-
	!.
body_preds((\+ B,Bs),Ps) :-
	!,
	body_preds((B,Bs),Ps).
body_preds((B,Bs),[P/N|Ps]) :-
	!,
	functor(B,P,N),
	body_preds(Bs,Ps).
body_preds(\+ B,Ps) :-
	!,
	body_preds(B,Ps).
body_preds(B,[P/N]) :-
	functor(B,P,N).

each_memb1([],_).
each_memb1([P|Ps],S) :-
	memb1(P,S),
	each_memb1(Ps,S).
	
memb1(X,[X|_]) :-
	!.
memb1(X,[_|Xs]) :-
	memb1(X,Xs).


file_suffix([],X,X).
file_suffix([X|Xs],Ys,[X|Zs]) :-
	file_suffix(Xs,Ys,Zs).

close_list([]) :-
	!.
close_list([_|X]) :-
	close_list(X).



read_clause1(S,cl(C,Vs)) :-
	read_term(S,C,[variable_names(Vs)]).

	

sortClauses([predicates(Ps)|Cls], Ps,Procs) :-
	initProcs(Ps,Procs0),
	buildProcs(Cls,Procs0,Procs).

initProcs([],[]).
initProcs([P/N|Ps], [proc(P/N,[])|Procs]) :-
	initProcs(Ps,Procs).
	
buildProcs([],Pr,Pr).
buildProcs([clause((H :- B), Vs)|Cls], Procs0, Procs2) :-
	functor(H,P,N),
	insertClause(Procs0,P/N,H,B,Vs,Procs1),
	buildProcs(Cls, Procs1, Procs2).
	
insertClause([proc(Pred,Cls)|Procs0],Pred,H,B,Vs,[proc(Pred,Cls1)|Procs0]) :-
	!,
	append(Cls,[clause((H :- B), Vs)],Cls1).
insertClause([Proc|Procs0],Pred,H,B,Vs,[Proc|Procs1]) :-
	insertClause(Procs0,Pred,H,B,Vs,Procs1).
	

user_clauses([],_,[]).
user_clauses([proc(P/N,Cls)|_],P/N,Cls1) :-
	!,
	returnCls(Cls,Cls1).
user_clauses([_|Prcs],P/N,Cls) :-
	user_clauses(Prcs,P/N,Cls).

returnCls([],[]).
returnCls([clause(C,_)|Cls],[C|Cls1]) :-
	returnCls(Cls,Cls1).


