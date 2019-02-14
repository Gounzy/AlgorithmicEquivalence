:-module(db,[init/0, increment_var_counter/0, set_var_counter/1, fresh_rename/2, fresh_rename/3, get_vars/2,construct_final_renaming/2,replace/3]).

:-use_module(utils). 

:-dynamic var_counter/1.
:-dynamic pred_counter/1.

%%%%
init:-
	retractall(var_counter(_)),
	assert(var_counter(0)), % Do not touch
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
  (var_counter(_) -> true ; assert(var_counter(100))),
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
	