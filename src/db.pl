:-module(db,[init/0, generate_clp_atoms/2, different_vars/1, increment_var_counter/0, set_var_counter/1, fresh_rename/2, fresh_rename/3, get_vars/2,construct_final_renaming/2,replace/3]).

:-use_module(utils). 

:-dynamic var_counter/1.
:-dynamic pred_counter/1.

different_vars(4).
possible_predicates([f/1, g/2, h/3, i/4, j/5, k/6, l/5, m/4, n/3, o/2, p/1]).  
few_predicates([f/1, g/2, h/3, i/2]). 

%%%%
init:-
	retractall(var_counter(_)),
	different_vars(X),
	assert(var_counter(X)), % Do not touch
	retractall(pred_counter(_)),
	assert(pred_counter(1)).
	
increment_var_counter:-
	var_counter(X), 
	retractall(var_counter(_)),
	Y is X + 1, 
	assert(var_counter(Y)).
	
set_var_counter(Y):-
	retractall(var_counter(_)),
	assert(var_counter(Y)).
	
%%%
generate_clp_atoms(Atoms1, Atoms2) :-
	few_predicates(Ps),
	R1 is random(5), % # preds clause 1
	R2 is random(5), % # preds clause 2
	R11 is R1 + 4, 
	R22 is R2 + 4, 
	R111 is random(R11), 
	R222 is random(R22), 
	N is R1 + R111 + 10, 
	M is R2 + R222 + 10, 
	take_random(N, Ps, Rs1), 
	take_random(M, Ps, Rs2), 
	init, 
	different_vars(X),
	set_var_counter(X), 
	associate_vars(Rs1, X, Atoms1), 
	associate_vars(Rs2, X, RAtoms2),
	fresh_rename(RAtoms2, Atoms2).
	
take_random(0, _, []). 
take_random(N, Xs, [X|Rs]):- 
	N > 0,
	random:random_member(X, Xs),
	N1 is N - 1,
	take_random(N1, Xs, Rs). 
	
associate_vars([], _, []). 
associate_vars([P/Arity|PredList], MaxVar, [NP|NPredList]):-
	associate_vars_pred(Arity, MaxVar, VarList), 
	NP =..[P|VarList],
	associate_vars(PredList, MaxVar, NPredList). 
	
associate_vars_pred(0, _, []). 
associate_vars_pred(Arity, MaxVar, ['$VAR'(I)|Vs]):-
	Arity > 0,
	I is random(MaxVar),
	Arity1 is Arity - 1, 
	associate_vars_pred(Arity1, MaxVar, Vs). 
%%%
replace('$VAR'(N1),Ren,T0):-
  member(('$VAR'(N1),T0),Ren), 
  !.
replace(Term1,Ren,Term0):-
  Term1 =..[F|Args],
  replace_list(Args,Ren,NArgs),
  Term0 =..[F|NArgs].

replace_list([],_,[]).
replace_list([T|Ts],Ren,[T0|Ts0]):-
  replace(T,Ren,T0),
  replace_list(Ts,Ren,Ts0).

get_vars(Term,VarList):-
  vars(Term,VL),
  sort(VL,VarList). % dups are removed

vars(Term,[Term]):-Term='$VAR'(_),!.
vars(Term,VarList):-
  Term=..[_|Args],
  varss(Args,VarList).
varss([],[]).
varss([T|Ts],VL):-
  vars(T,VL1),
  varss(Ts,VL2),
  append(VL1,VL2,VL).

get_var_renaming(VarList,NewVarList):-
  different_vars(X), 
  (var_counter(_) -> true ; assert(var_counter(X))),
  retract(var_counter(N)),
  construct_renaming(VarList,N,NewVarList,NN),
  assert(var_counter(NN)).

construct_renaming([],N,[],N).
construct_renaming([V|Vs],N,[(V,NV)|NVs],NN):-
  NV='$VAR'(N),
  N1 is N + 1,
  construct_renaming(Vs,N1,NVs,NN).

fresh_rename(Term1,Term0):-
  get_vars(Term1,VList1),
  get_var_renaming(VList1,Ren),
  replace(Term1,Ren,Term0).
  
  % Utilisé pour garder la substitution
fresh_rename(Term1,Term0, Ren):-
  get_vars(Term1,VList1),
  get_var_renaming(VList1,Ren),
  replace(Term1,Ren,Term0).
  
construct_final_renaming(cl(H,C,B),Ren):-
  vars(cl(H,C,B),VarList),
  construct_fr(VarList,0,[],Ren).

construct_fr([],_,Ren,Ren).
construct_fr([V|Vs],N,Ren1,Ren0):-
  ( member((V,_),Ren1)
  ->
  construct_fr(Vs,N,Ren1,Ren0)
  ;
  N1 is N+1,
  construct_fr(Vs,N1,[(V,'$VAR'(N))|Ren1],Ren0)).
	