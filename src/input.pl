%%% Lit un fichier .clp
%% Les contraintes doivent �tres entour�es de {}, sauf s'il n'y en a pas : alors rien du tout ou {} sont tous les deux valides.

:- module(input,[load_file/2]).

:- use_module(utils).

% Charge le fichier F et retient toutes ses clauses
load_file(F, Clauses) :-
	see(F),
	remember_all(Clauses),
	seen,
	db:set_var_counter_to_next.

remember_all(Clauses) :-
	read(C),
	(
	    C == end_of_file -> Clauses = []
	;
	    remember_clause(C, Cl),
	    Clauses = [Cl | Rest],
	    remember_all(Rest)
	).

remember_clause((A :- B), Cl) :-
	!,
    tuple2list(B,BL),
    parse_body(BL,CL,AL),
    db:var_counter(X),
    numbervars(cl(A,CL,AL),X,Y),
    db:set_next_var_counter(Y),
    Cl = cl(A,CL,AL).
remember_clause(Clause, Cl):-
	remember_clause((Clause :- ([], [])), Cl).

parse_body([{}|Bs],[],Bs):- !.
parse_body([{C}|Bs],CL,Bs):- !, tuple2list(C,CL).
parse_body(Bs, [], Bs).
