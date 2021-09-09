%% Affichage de clauses / de sliceparts

:- module(pprint,[pp_print_clauses/1, pp_print_slice_parts/2, pp_print_arg_tuple/1]).

:- use_module(utils).

pp_print_slice_parts([], []).
pp_print_slice_parts([Vars|VarsList], [Clauses|ClausesList]):-
	format('------- Slice part ------- ~n'),
	format('~w ~n', [Vars]),
	pp_print_clauses(Clauses),
	pp_print_slice_parts(VarsList, ClausesList).

pp_print_clauses(Clauses):-
	maplist(print_clause, Clauses).

print_clause(cl(H, C, B)):-
	format("~n"),
	pp_print_atom(0, H),
	format(" :- "),
	pp_print_constraints(0,C),
	%format("~n"),
	pp_print_body(0,B).

pp_print_atom(Ind,A):-
	print_indent(Ind),
	format("~w",[A]).

pp_print_constraints(_, []):-
	!.
pp_print_constraints(Ind,Cs):-
	print_indent(Ind),
	format("{"),
	print_list(Cs),
	format("}, ").

print_list([]).
print_list([T]):- !, format("~w",[T]).
print_list([T|Ts]):-format("~w, ",[T]), print_list(Ts).

pp_print_body(Ind,Bs):-
	print_indent(Ind),
	format("{"),
	print_list(Bs),
	format("}.").


print_indent(0):-!.
print_indent(N):-
	N > 0,
	NN is N - 1,
	write(' '),
	print_indent(NN).

pp_print_arg_tuple([]):- format('~n'). 
pp_print_arg_tuple([Pred->Var->Tuple|AT]):- 
	format('~n ~w ~t ~w ~t ---> <', [Pred, Var]),
	pp_print_tuple(Tuple), 
	format('>'),
	pp_print_arg_tuple(AT). 

pp_print_tuple([]). 
pp_print_tuple([F-Val|Tuple]):-
	format('(~w:~w)', [F, Val]),
	(Tuple \= [] -> format(', ') ; true),
	pp_print_tuple(Tuple). 
	