%%%%%%%%%%%%%%
%
% UTILS - pr�dicats utiles
% Donc si appel bizarre dans un autre module, �a doit �tre un pr�dicat d'ici !
%
%%%%%%%%%%%%%%

:-module(utils, [
	list_to_tuple/2,
	member_pos/3,
	member_pos/4,
	same_pred/2,
	take/4,
	take/5,
	total_n_args/2,
	all_args/2,
	all_args/3,
	all_different_elems/1,
	empty_or_true/1,
	at_least_one_member/2,
	all_members/2,
	none_member/2,
	tuple2list/2,
	unify/2,
	not_only_trues/1,
	remove_trues/2,
	remove_trues_and_empties/2,
	both_empty/2,
	appendall/3,
	allFirst/2,
	allSecond/2,
	firsts/2,
	seconds/2,
	thirds/2,
	sum/2
]).

list_to_tuple([X|[]], (X)).
list_to_tuple([X|Xs], Y) :-
	!,
	list_to_tuple(Xs, Y1),
	Y = (X,Y1).

member_pos(X, Xs, Pos):- member_pos(X, Xs, 1, Pos).
member_pos(X, [X|_], I, I):-!.
member_pos(X, [_|Xs], I, Pos):-
	J is I + 1,
	member_pos(X, Xs, J, Pos).

% True iff same args
same_pred(P1, P1):-!.
same_pred(_, _):- fail.

take(N, Xs, Taken, Other):- take(N, Xs, [], Taken, Other).
take(0, Xs, Taken, Taken, Xs):-!.
take(N, [X|Xs], CurrentTaken, Taken, Other):-
	N1 is N - 1,
	append(CurrentTaken, [X], NewCurrentTaken),
	take(N1, Xs, NewCurrentTaken, Taken, Other).

total_n_args([], 0).
total_n_args([Call|Calls], N):-
	Call =..[_|Args],
	length(Args, N1),
	total_n_args(Calls, N2),
	N is N1 + N2.

all_args(Calls, AllArgs):-all_args(Calls, [], AllArgs).
all_args([], CA, CA).
all_args([true|Bs], CurrentArgs, Args):- !,
	all_args(Bs, CurrentArgs, Args).
all_args([B|Bs], CurrentArgs, Args):-
	B =..[_|ArgsB],
	append(ArgsB, CurrentArgs, NewCurrentArgs),
	all_args(Bs, NewCurrentArgs, Args).

all_different_elems([]).
all_different_elems([A|As]):-
	not(member(A,As)),
	all_different_elems(As).

empty_or_true([true]):-!.
empty_or_true(true):-!.
empty_or_true([]):-!.
empty_or_true([B|Bs]):-
	empty_or_true(B),
	empty_or_true(Bs).

all_members([], _).
all_members([X|Xs], List):-
	member(X, List),
	all_members(Xs, List).

at_least_one_member([X|_], List):-
	 member(X, List),
	 !.
at_least_one_member([X|Xs], List):-
	not(member(X, List)),
	at_least_one_member(Xs, List).

none_member([], _).
none_member([X|L1], L2):-
	 not(member(X, L2)),
	 none_member(L1, L2).

tuple2list((A,As),[A|LAs]) :-
	!,
	tuple2list(As,LAs).
tuple2list(A,[A]).

unify(Call, Head):-
	Call=..[Pred|Args],
	Head=..[Pred|Args2],
	length(Args, Arity),
	length(Args2, Arity).

not_only_trues(Xs):-
	remove_trues(Xs, Result),
	Result \= [].

remove_trues(Xs, Result):-
	member(true, Xs),
	select(true, Xs, Result1),
	remove_trues(Result1, Result).
remove_trues(Xs, Xs):-
	not(member(true, Xs)).

remove_trues_and_empties([], []).
remove_trues_and_empties([[]|Ls], NLs):- !, remove_trues_and_empties(Ls, NLs).
remove_trues_and_empties([true|Ls], NLs):- !, remove_trues_and_empties(Ls, NLs).
remove_trues_and_empties([L|Ls], [L|NLs]):- remove_trues_and_empties(Ls, NLs).

both_empty([], []).

appendall(_, [], []).
appendall(List1, [Elem1|List2], [Append1|Appends]):-
	is_list(Elem1), % souper importantzzzzz
	!,
	append(List1, Elem1, Append1),
	appendall(List1, List2, Appends).
appendall(List1, [Elem1|List2], [Append1|Appends]):-
	append(List1, [Elem1], Append1),
	appendall(List1, List2, Appends).

allFirst([], []).
allFirst([(First,_)|Others], NFirsts):-
	allFirst(Others, NFirsts1),
	append(First, NFirsts1, NFirsts).

allSecond([], []).
allSecond([(_,Second)|Others], NSeconds):-
	allSecond(Others, NSeconds1),
	append(Second, NSeconds1, NSeconds).

firsts([], []).
firsts([A-_-_|Triplets], [A|Firsts]):-
	firsts(Triplets, Firsts).
firsts([A-_|Duos], [A|Firsts]):-
	firsts(Duos, Firsts).

seconds([], []).
seconds([_-B-_|Triplets], [B|Seconds]):-
	seconds(Triplets, Seconds).
seconds([_-B|Duos], [B|Seconds]):-
	seconds(Duos, Seconds).

thirds([], []).
thirds([_-_-C|Triplets], [C|Thirds]):-
	thirds(Triplets, Thirds).

sum(Xs, S):- sum(Xs, 0, S).
sum([], Acc, Acc).
sum([X|Xs], Acc, S):-
	NAcc is Acc + X,
	sum(Xs, NAcc, S).
