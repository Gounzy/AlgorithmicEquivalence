:-module(db,[init/0, generate_clp_atoms/2, different_vars/1, increment_var_counter/0, set_var_counter/1, fresh_rename/2, fresh_rename/3, get_vars/2,construct_final_renaming/2,replace/3, class_1/2, class_2/2, class_3/2, class_4/2,class_5/2, class_6/2]).

:-use_module(utils).
:-use_module(au_complexity).
:-use_module(generalization_utils).

:-dynamic var_counter/1.
:-dynamic pred_counter/1.

different_vars(10).
possible_predicates([f/1, g/2, h/3, i/4, m/4, n/3, o/2, p/1]).
few_predicates([g/2, f/1, h/3]).

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
	R1 is random(20), % # preds clause 1
	R2 is random(20), % # preds clause 2
	take_random(R1, Ps, Rs1),
	take_random(R2, Ps, Rs2),
	init,
	different_vars(X),
	set_var_counter(X),
	associate_vars(Rs1, X, Atoms1),
	associate_vars(Rs2, X, RAtoms2),
	fresh_rename(RAtoms2, Atoms2).

generate_few_atoms(Atoms1, Atoms2, NPredMin, NPredMax, MinVars, MaxVars, CoeffMin, CoeffMax, VCMin, VCMax):-
	few_predicates(Ps),
	R1 is random(NPredMax), % # preds clause 1
	R2 is random(NPredMax), % # preds clause 2
	R11 is max(R1, NPredMin),
	R22 is max(R2, NPredMin),
	take_random(R11, Ps, Rs1),
	take_random(R22, Ps, Rs2),
	init,
	Vars is random(MaxVars - MinVars),
	Varss is Vars + MinVars,
	set_var_counter(Varss),
	associate_vars(Rs1, Varss, LAtoms1),
	associate_vars(Rs2, Varss, LAtoms2),
	sort(LAtoms1, Atoms1),
	sort(LAtoms2, RAtoms2),
	fresh_rename(RAtoms2, Atoms2),
	anti_unification_coefficient(Atoms1, Atoms2, Coeff),
	%format('~n Coeff: ~w', [Coeff]),
	Coeff =< CoeffMax,
	Coeff >= CoeffMin,
	build_matrix(Atoms1, Atoms2, Matrix),
	variables_coefficient(Matrix, VC),
	%format('~n VC: ~w', [VC]),
	VC =< VCMax,
	VC >= VCMin,
	!.
generate_few_atoms(Atoms1, Atoms2, NPredMin, NPredMax, MinVars, MaxVars, CoeffMin, CoeffMax, VCMin, VCMax):-generate_few_atoms(Atoms1, Atoms2, NPredMin, NPredMax, MinVars, MaxVars, CoeffMin, CoeffMax, VCMin, VCMax).

class(C, Atoms1, Atoms2):-
	(C == 1 -> generate_few_atoms(Atoms1, Atoms2, 5, 15, 1, 10, 1, 41472, 1, 60480) ; true),
	(C == 2 -> generate_few_atoms(Atoms1, Atoms2, 10, 15, 6, 10, 41473, 207360, 60481, 362880) ; true),
	(C == 3 -> generate_few_atoms(Atoms1, Atoms2, 10, 15, 9, 15, 207361, 9072000, 362881, 3628799) ; true),
	(C == 4 -> generate_few_atoms(Atoms1, Atoms2, 15, 20, 9, 15, 9072001, 17418240, 3628800, 17418240) ; true),
	(C == 5 -> generate_few_atoms(Atoms1, Atoms2, 15, 20, 9, 15, 17418241, 174182400, 17418241, 174182400) ; true),
	(C == 6 -> generate_few_atoms(Atoms1, Atoms2, 15, 22, 9, 18, 174182401, 1741824000, 174182401, 1741824000) ; true).

class_0(Atoms1, Atoms2):-
	Atoms1 = [f('$VAR'(8), '$VAR'(8)),f('$VAR'(6), '$VAR'(8)),f('$VAR'(4), '$VAR'(8)),f('$VAR'(10), '$VAR'(8))],
	Atoms2 = [f('$VAR'(1), '$VAR'(1)),f('$VAR'(3), '$VAR'(2)),f('$VAR'(5), '$VAR'(2)),f('$VAR'(7), '$VAR'(2))].

class_1(Atoms1, Atoms2):-
	Atoms1 = [f('$VAR'(8)),f('$VAR'(6)),i('$VAR'(4),'$VAR'(10))],
	Atoms2 = [f('$VAR'(16)),f('$VAR'(13)),f('$VAR'(20)),h('$VAR'(15),'$VAR'(14),'$VAR'(13)),h('$VAR'(20),'$VAR'(12),'$VAR'(20)),h('$VAR'(17),'$VAR'(21),'$VAR'(15)),g('$VAR'(17),'$VAR'(21)),g('$VAR'(15),'$VAR'(11)),g('$VAR'(20),'$VAR'(14)),f('$VAR'(14)),i('$VAR'(11),'$VAR'(13)),g('$VAR'(15),'$VAR'(16)),g('$VAR'(14),'$VAR'(14)),i('$VAR'(21),'$VAR'(16)),i('$VAR'(17),'$VAR'(17)),i('$VAR'(12),'$VAR'(16))].

class_2(Atoms1, Atoms2):-
	Atoms1 = [h('$VAR'(9),'$VAR'(4),'$VAR'(1)),i('$VAR'(9),'$VAR'(9)),g('$VAR'(2),'$VAR'(6)),f('$VAR'(5)),h('$VAR'(2),'$VAR'(8),'$VAR'(6)),h('$VAR'(7),'$VAR'(8),'$VAR'(10)),g('$VAR'(10),'$VAR'(4)),h('$VAR'(3),'$VAR'(6),'$VAR'(8)),f('$VAR'(9)),g('$VAR'(4),'$VAR'(10)),f('$VAR'(6)),h('$VAR'(9),'$VAR'(1),'$VAR'(7)),g('$VAR'(1),'$VAR'(8)),g('$VAR'(6),'$VAR'(4)),g('$VAR'(9),'$VAR'(8)),f('$VAR'(7))],
	Atoms2 = [g('$VAR'(13),'$VAR'(12)),i('$VAR'(16),'$VAR'(17)),g('$VAR'(15),'$VAR'(11)),g('$VAR'(20),'$VAR'(14)),g('$VAR'(14),'$VAR'(12))].

class_3(Atoms1, Atoms2):-
	Atoms1 =  [f('$VAR'(6)),f('$VAR'(6)),f('$VAR'(4)),i('$VAR'(7),'$VAR'(3)),i('$VAR'(2),'$VAR'(9)),h('$VAR'(2),'$VAR'(5),'$VAR'(2)),i('$VAR'(5),'$VAR'(2)),f('$VAR'(7)),i('$VAR'(10),'$VAR'(2)),h('$VAR'(7),'$VAR'(1),'$VAR'(7)),f('$VAR'(3)),h('$VAR'(5),'$VAR'(6),'$VAR'(2)),g('$VAR'(2),'$VAR'(8)),g('$VAR'(4),'$VAR'(9)),h('$VAR'(9),'$VAR'(3),'$VAR'(8))],
	Atoms2 =  [f('$VAR'(16)),f('$VAR'(14)),i('$VAR'(12),'$VAR'(11)),i('$VAR'(13),'$VAR'(16)),f('$VAR'(15)),i('$VAR'(13),'$VAR'(16)),g('$VAR'(16),'$VAR'(12))].

class_4(Atoms1, Atoms2):-
	Atoms1 =  [i('$VAR'(8),'$VAR'(6)),i('$VAR'(6),'$VAR'(9)),i('$VAR'(4),'$VAR'(2)),h('$VAR'(8),'$VAR'(8),'$VAR'(10)),h('$VAR'(4),'$VAR'(10),'$VAR'(2)),g('$VAR'(9),'$VAR'(3)),i('$VAR'(9),'$VAR'(4)),h('$VAR'(5),'$VAR'(3),'$VAR'(2)),g('$VAR'(7),'$VAR'(9)),i('$VAR'(1),'$VAR'(9)),f('$VAR'(9)),g('$VAR'(4),'$VAR'(10)),f('$VAR'(2)),h('$VAR'(3),'$VAR'(3),'$VAR'(5)),h('$VAR'(5),'$VAR'(6),'$VAR'(8)),g('$VAR'(6),'$VAR'(5)),f('$VAR'(4))],
	Atoms2 =  [f('$VAR'(14)),f('$VAR'(16)),g('$VAR'(16),'$VAR'(20)),g('$VAR'(21),'$VAR'(15)),i('$VAR'(17),'$VAR'(13)),g('$VAR'(16),'$VAR'(17)),h('$VAR'(11),'$VAR'(21),'$VAR'(13)),f('$VAR'(21)),i('$VAR'(12),'$VAR'(17)),i('$VAR'(21),'$VAR'(14)),g('$VAR'(13),'$VAR'(16)),h('$VAR'(17),'$VAR'(14),'$VAR'(16)),f('$VAR'(16))].

class_5(Atoms1, Atoms2):-
	Atoms1 =  [f('$VAR'(6)),f('$VAR'(1)),h('$VAR'(9),'$VAR'(7),'$VAR'(3)),h('$VAR'(7),'$VAR'(4),'$VAR'(3)),f('$VAR'(2)),f('$VAR'(4)),g('$VAR'(5),'$VAR'(10)),h('$VAR'(5),'$VAR'(1),'$VAR'(8)),h('$VAR'(6),'$VAR'(2),'$VAR'(10)),h('$VAR'(5),'$VAR'(6),'$VAR'(1)),h('$VAR'(4),'$VAR'(7),'$VAR'(2)),i('$VAR'(3),'$VAR'(6)),f('$VAR'(10)),f('$VAR'(1)),f('$VAR'(2)),i('$VAR'(2),'$VAR'(8))],
	Atoms2 =  [h('$VAR'(15),'$VAR'(20),'$VAR'(21)),i('$VAR'(17),'$VAR'(21)),g('$VAR'(16),'$VAR'(14)),h('$VAR'(14),'$VAR'(17),'$VAR'(22)),g('$VAR'(13),'$VAR'(15)),
	h('$VAR'(11),'$VAR'(11),'$VAR'(16)),f('$VAR'(12)),h('$VAR'(22),'$VAR'(22),'$VAR'(21)),g('$VAR'(12),'$VAR'(13)),f('$VAR'(22)),h('$VAR'(16),'$VAR'(12),'$VAR'(16)),g('$VAR'(12),'$VAR'(20)),f('$VAR'(15)),i('$VAR'(12),'$VAR'(14)),g('$VAR'(16),'$VAR'(11)),h('$VAR'(14),'$VAR'(17),'$VAR'(16)),f('$VAR'(21)),i('$VAR'(14),'$VAR'(17)),h('$VAR'(16),'$VAR'(21),'VAR'(17))].

class_6(Atoms1, Atoms2):-
	Atoms1 =  [g('$VAR'(7),'$VAR'(2)),g('$VAR'(9),'$VAR'(2)),i('$VAR'(6),'$VAR'(4)),f('$VAR'(7)),i('$VAR'(2),'$VAR'(6)),f('$VAR'(10)),h('$VAR'(8),'$VAR'(5),'$VAR'(7)),g('$VAR'(5),'$VAR'(8)),h('$VAR'(8),'$VAR'(4),'$VAR'(8)),h('$VAR'(7),'$VAR'(7),'$VAR'(10)),h('$VAR'(10),'$VAR'(3),'$VAR'(6)),h('$VAR'(1),'$VAR'(8),'$VAR'(9)),g('$VAR'(10),'$VAR'(1)),g('$VAR'(10),'$VAR'(6)),g('$VAR'(1),'$VAR'(6)),i('$VAR'(8),'$VAR'(10)),i('$VAR'(1),'$VAR'(2)),h('$VAR'(3),'$VAR'(5),'$VAR'(8))],
	Atoms2 =  [g('$VAR'(12),'$VAR'(13)),g('$VAR'(12),'$VAR'(11)),i('$VAR'(11),'$VAR'(16)),h('$VAR'(16),'$VAR'(14),'$VAR'(21)),h('$VAR'(16),'$VAR'(17),'$VAR'(14)),g('$VAR'(13),'$VAR'(15)),g('$VAR'(14),'$VAR'(16)),g('$VAR'(14),'$VAR'(16)),g('$VAR'(16),'$VAR'(13)),f('$VAR'(20)),g('$VAR'(16),'$VAR'(20)),f('$VAR'(20)),h('$VAR'(11),'$VAR'(14),'$VAR'(17)),h('$VAR'(16),'$VAR'(14),'$VAR'(21)),g('$VAR'(14),'$VAR'(13)),h('$VAR'(14),'$VAR'(11),'$VAR'(12)),i('$VAR'(20),'$VAR'(15)),f('$VAR'(16))].

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
