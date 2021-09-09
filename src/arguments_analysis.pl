:- module(arguments_analysis, [argtupling/0]).
:- use_module(input).
:- use_module(pprint).
:- use_module(db). 
:- use_module(utils). 
:- use_module(generalization_predicates).

% todo :
% 1) implem génération de préds arbitraires + expérimenter, observer (sur des préds arbitraires ?)
% 2) définir le domaine abstrait : garder le tuple ou bien passer à autre chose ?
% 3) checker la littérature à ce niveau pour trouver des idées

argtupling:- 
    set_prolog_stack(global, limit(100 000 000 000)),
    It is 20, 
    argtupling(It, Scores, TargetScores), 
    utils:sum(Scores, SumScores),
    utils:sum(TargetScores, SumTargetScores),
    Mean is (SumScores / max(SumTargetScores, 1)) * 100, 
    format('~n ~n Result over ~w iterations : ~w %', [It, Mean]).


argtupling(0, [], []):- !. 
argtupling(TuplingIterations, [Score2|Scores], [Score1|TargetScores]):- 
    db:set_var_counter(0),
    working_directory(Z,Z), 
    %atom_concat(Z, 'src/CLP/arguments/test1.clp', File),
    %input:load_file(File, Clauses), 
    db:generate_preds(Clauses1, Clauses2),
    pp_print_clauses(Clauses1), 
    format('~n'),
    pp_print_clauses(Clauses2), 
    
    % Extract all vars into VarsP and VarsQ
    extract_pred_follow_links(p, Clauses1, ClausesP, NbLinksP),
    extract_pred_follow_links(p, Clauses2, ClausesQ, NbLinksQ),
    append(ClausesP, ClausesQ, Clauses),
    empty_arg_tuple(Clauses, [], EmptyTuple),
    format('~n Empty arg tuple : ~w', [EmptyTuple]), 
    extract_vars(ClausesP, VarsP), 
    extract_vars(ClausesQ, VarsQ),
    format('~n Variables from p : ~w', [VarsP]),
    format('~n Variables from q : ~w', [VarsQ]),

    % Extract args into ArgsP and ArgsQ
    head(ClausesP, cl(Hp,_,_)),
    format('~n Hp : ~w', [Hp]),
    extract_vars_rec(Hp, ArgsP),
    extract_pred_name(Hp, PredP),
    head(ClausesQ, cl(Hq,_,_)),
    format('~n Hq : ~w', [Hq]),
    extract_vars_rec(Hq, ArgsQ),
    extract_pred_name(Hq, PredQ),
    format('~n Arguments from p : ~w', [ArgsP]),
    format('~n Arguments from q : ~w', [ArgsQ]),
    !,

    extract_preds_with_arity(ClausesP, PredsWithArityP),
    extract_preds_with_arity(ClausesQ, PredsWithArityQ),
    format('~n Preds from program 1: ~w ~n Preds from program 2: ~w ~n', [PredsWithArityP, PredsWithArityQ]), 
    
    clone_tuple_var_times_preds(EmptyTuple, ClausesP, PredsWithArityP, InitialTuplesP),
    clone_tuple_var_times_preds(EmptyTuple, ClausesQ, PredsWithArityQ, InitialTuplesQ),
    format('~n Initial tuples p : ~w', [InitialTuplesP]),
    format('~n Initial tuples q : ~w', [InitialTuplesQ]),
    !,

    argtupling_iterate(2, ClausesP, InitialTuplesP, NewTuplesP),
    format('~n Done with p~n'),
    argtupling_iterate(2, ClausesQ, InitialTuplesQ, NewTuplesQ),
    format('~n Done with q~n'),

    get_tuples_relative(PredP, ArgsP, NewTuplesP, RelevantTuplesP),
    get_tuples_relative(PredQ, ArgsQ, NewTuplesQ, RelevantTuplesQ),
    format('~n relevant tuples p : ~n'),
    pp_print_arg_tuple(RelevantTuplesP),
    format('~n relevant tuples q : ~n'),
    pp_print_arg_tuple(RelevantTuplesQ),
    !,

    find_matches(RelevantTuplesP, RelevantTuplesQ, MatchesPQ),
    %build_translation_table(0, MatchesPQ, TranslationP, TranslationQ),     
    format('~n Matches found: ~w ~n', [MatchesPQ]),

    extract_pred(PredP, ClausesP, ClausesPredP), 
    extract_pred(PredQ, ClausesQ, ClausesPredQ),

    %translate_clauses(ClausesPredP, TranslationP, TranslatedClausesP),
    %translate_clauses(ClausesPredQ, TranslationQ, TranslatedClausesQ),

    gen_preds(ClausesPredP, ClausesPredQ, ResultingPred, BestMatches), 
    !,
    
    tovars(MatchesPQ, VarsMatchesPQ), 
    get_resulting_pred(ClausesPredP, ClausesPredQ, [VarsMatchesPQ], ResultingPred2),
    !, 

    format('~n-------------------~n~n Resulting pred (exhaustive) :'),
    pp_print_clauses(ResultingPred),
    format('~n Best matches: ~w~n', [BestMatches]),
    format('~n-------------------~n~n Resulting pred (analysis) :'),
    pp_print_clauses(ResultingPred2),
    format('~n Matches found: ~w ~n', [VarsMatchesPQ]),

    score_pred(ResultingPred, Score1), 
    score_pred(ResultingPred2, Score2), 

    Score is (Score2/max(1,Score1)) * 100, 

    format('~n Score: ~w %', [Score]), 

    TuplingIterations1 is TuplingIterations - 1, 
    argtupling(TuplingIterations1, Scores, TargetScores),

    true. 

%%%%%%%
tovars([], []). 
tovars([I-J|Matches], [['$VAR'(I),'$VAR'(J)]|MatchesVars]):-
    tovars(Matches,MatchesVars). 

%%%%%%%%%%%%%%%%%%%%%%
find_matches(RelevantTuplesP, RelevantTuplesQ, MatchesPQ):- 
    order_tuples(RelevantTuplesP, OrderedTuplesP), 
    %format('~n Ordered tuples P : ~w ~n', [OrderedTuplesP]),
    order_tuples(RelevantTuplesQ, OrderedTuplesQ), 
    %format('~n Ordered tuples Q : ~w ~n', [OrderedTuplesP]),
    compute_all_distances(OrderedTuplesP, OrderedTuplesQ, Distances), 
    match_best_distances(Distances, MatchesPQ). 

order_tuples(Tuples, OrderedTuples):- 
    key_tuples(Tuples, KeyTuples), 
    keysort(KeyTuples, OrderedTuples).

key_tuples([], []).
key_tuples([_->'$VAR'(I)->Tuple|Tuples], [I-Tuple|KeyTuples]):-
    key_tuples(Tuples,KeyTuples).

compute_all_distances(Tuples1, Tuples2, Distances):-
    compute_all_distances(Tuples1,Tuples2, [], Distances). 

compute_all_distances([], _, Distances, Distances). 
compute_all_distances([Tuple1|Tuples1], Tuples2, CurrentDistances, Distances):-
    compute_distances(Tuple1,Tuples2,NewDistances), 
    %format('~n NewDistances : ~w', [NewDistances]),
    append(CurrentDistances,NewDistances, NewCurrentDistances),
    compute_all_distances(Tuples1,Tuples2,NewCurrentDistances, Distances).

compute_distances(_, [], []).
compute_distances(I-Tuple1, [J-Tuple2|Tuples2], [I-J-D|Distances]):-
    compute_distance(Tuple1,Tuple2,D),
    %format('~n Distance : ~w', [D]), 
    compute_distances(I-Tuple1,Tuples2,Distances).

compute_distance(Tuple1, Tuple2, D):- 
    sums_distances(Tuple1, Tuple2, S), 
    D is sqrt(S).

sums_distances([], [], 0). 
sums_distances([_-Val1|Vals1], [_-Val2|Vals2], Sum):-
    sums_distances(Vals1, Vals2, Sum1), 
    Sqr is ((Val1-Val2)*(Val1-Val2)), 
    %format('~n Sqr: ~w', [Sqr]),
    Sum is Sqr + Sum1. 

match_best_distances([], []):-!.
match_best_distances(Distances, [I-J|Matches]):- 
    find_lowest_distance(Distances, max, 100, 100, I, J),
    %format('~n Lowest distances: ~w, ~w', [I,J]),
    remove_distances(Distances, I, J, NDistances),
    %format('~n Lowest removed: ~w', [NDistances]),
    match_best_distances(NDistances, Matches),
    %format('~n Matches: ~w', [Matches]),
    true.

find_lowest_distance([], _, I, J, I, J). 
find_lowest_distance([I-J-D|Distances], CurrentMin, CurrentI, CurrentJ, BestI, BestJ):- 
    (CurrentMin = max -> (NCurrentI = I, (NCurrentJ = J, NCurrentMin = D)) ; (D < CurrentMin -> (NCurrentI = I, (NCurrentJ = J, NCurrentMin = D)) ; NCurrentI = CurrentI, (NCurrentJ = CurrentJ, NCurrentMin = CurrentMin))),
    find_lowest_distance(Distances,NCurrentMin, NCurrentI, NCurrentJ, BestI, BestJ).

remove_distances([], _, _, []). 
remove_distances([I-_-_|Distances], I, J, Removed):- 
    !,
    remove_distances(Distances, I, J, Removed). 
remove_distances([_-J-_|Distances], I, J, Removed):- 
    !,
    remove_distances(Distances, I, J, Removed). 
remove_distances([K-L-D|Distances], I, J, [K-L-D|Removed]):-
    remove_distances(Distances, I, J, Removed). 
%%%%%%%%%%%%%%%%%%%%

get_resulting_pred(Clauses1, Clauses2, ArgsAssociations, NPred) :- 
    clauses_associations(Clauses1, Clauses2, ClausesAssociations),
    try_all_associations(Clauses1, Clauses2, ArgsAssociations, ClausesAssociations, BestAAssoc, _, Pred),
    back_to_variables_table(Pred, BestAAssoc, BackToVariablesTable),
    replace(Pred, BackToVariablesTable, NPred).

%%%%%%%%%%%%%%%%%%%%%%
argtupling_iterate(0, _, Tuples, Tuples). 
argtupling_iterate(N, Clauses, Tuples, NewTuples) :- 
    N > 0, 
    N1 is N - 1,
    argtupling_iteration(Clauses, Tuples, NewTuples1),
    %format('~n New arg tuples : '), 
    pp_print_arg_tuple(NewTuples1),
    argtupling_iterate(N1, Clauses, NewTuples1, NewTuples).

argtupling_iteration([], Tuples, Tuples). 
argtupling_iteration([Cl|Clauses],Tuples,NewTuples):-
    argtupling_iteration_clause(Cl, Tuples, NTuples), 
    argtupling_iteration(Clauses, NTuples, NewTuples). 
    
argtupling_iteration_clause(cl(H,C,B), Tuples, NTuples):-
    H =.. [Pred|_],  
    argtupling_iteration_constraints(C, Pred, Tuples, NTuples1), 
    argtupling_iteration_body(B, Pred, NTuples1, NTuples).

argtupling_iteration_constraints([], _, Tuples, Tuples). 
argtupling_iteration_constraints([C|Cs], Pred, Tuples, NewTuples):- 
    argtupling_iteration_constraint(C, Pred, Tuples, Tuples1),
    argtupling_iteration_constraints(Cs, Pred, Tuples1, NewTuples). 

argtupling_iteration_constraint(C, Pred, Tuples, [Pred->Var->NewTuple|OtherTuples]):- 
    C =.. [_,Var|Args],
    % On suppose que les contraintes ont tjs une variable à gauche
    extract_var_tuple(Pred, Var, Tuples, Tuple, OtherTuples), 
    update_var_tuple(Pred, Var, Tuple, Tuples, Args, NewTuple).

update_var_tuple(_, _, Tuple, _, [], Tuple). 
update_var_tuple(Pred, Var, Tuple, OtherTuples, [Arg|Args], NewTuple) :- 
    Arg = '$VAR'(_),
    %format('~n ~n Var : ~w  Arg : ~w', [Var, Arg]),
    !,
    extract_var_tuple(Pred, Arg, OtherTuples, ArgTuple, _),
    (Var \= Arg -> sum_tuple(Tuple, ArgTuple, NVarTuple) ; NVarTuple = Tuple), 
    update_var_tuple(Pred, Var, NVarTuple, OtherTuples, Args, NewTuple). 
update_var_tuple(Pred, Var, Tuple, OtherTuples, [Arg|Args], NewTuple) :- 
    Arg =..[F|Fs],
    Fs \= [], !,
    append(Fs, Args, NArgs), % ici on se contente d'un flatten, voir s'il faut traiter les choses différemment
    update_var_tuple(Pred, Var, Tuple, OtherTuples, [F|NArgs], NewTuple).
update_var_tuple(Pred, Var, Tuple, OtherTuples, [Arg|Args], NewTuple) :- 
    Arg =..[F],
    %format('~n~n F : ~w ~n~n', [F]),
    increment_tuple_functor(Tuple, F, NTuple),
    update_var_tuple(Pred, Var, NTuple, OtherTuples, Args, NewTuple).

increment_tuple_functor([F-N|Tuple], F, [F-N1|Tuple]):- 
    !,
    N1 is N + 1. 
increment_tuple_functor([T|Tuple], F, [T|NTuple]) :-
    increment_tuple_functor(Tuple, F, NTuple). 

extract_var_tuple(Pred,V, Tuples, Tuple, OtherTuples):-
    select(Pred->V->Tuple, Tuples, OtherTuples).

argtupling_iteration_body([], _, Tuples, Tuples). 
argtupling_iteration_body([B|Bs], Pred, Tuples, NewTuples):- 
    B =..[PredB|ArgsB], 
    argtupling_iteration_atom(0, Pred, PredB, ArgsB, Tuples, NewTuples1), 
    argtupling_iteration_body(Bs, Pred, NewTuples1, NewTuples).

argtupling_iteration_atom(_, _, _, [], Tuples, Tuples).
argtupling_iteration_atom(N, PredA, PredB, [ArgB|ArgsB], Tuples, NewTuples) :-
    extract_var_tuple(PredA, ArgB, Tuples, TupleA, OtherTuples), 
    extract_var_tuple(PredB, '$VAR'(N), Tuples, TupleB, _), 
    sum_tuple(TupleA, TupleB, NTupleA), 
    N1 is N + 1, 
    argtupling_iteration_atom(N1, PredA, PredB, ArgsB, [PredA->ArgB->NTupleA|OtherTuples], NewTuples).  

sum_tuple([], [], []). 
sum_tuple([F-N1|Tuple1], [F-N2|Tuple2], [F-N3|SumTuple]):-
    N3 is N1 + N2,
    sum_tuple(Tuple1,Tuple2,SumTuple).  

%%%%%%%%%%%%%%%%%%%%%%
build_translation_table(_, [], [], []). 
build_translation_table(N, [P-Q|MatchesPQ], [P-FString|TranslationP], [Q-FString|TranslationQ]):- 
    number_string(N,NString),
    string_concat('f', NString, FString), 
    N1 is N + 1,
    build_translation_table(N1, MatchesPQ, TranslationP, TranslationQ). 

translate_clauses([], _, []). 
translate_clauses([Clause|Clauses], TranslationTable, [NewClause|NewClauses]):- 
    translate_clause(Clause,TranslationTable, NewClause),
    translate_clauses(Clauses, TranslationTable, NewClauses).

translate_clause(cl(H,C,B), TranslationTable, cl(NH,NC,NB)):-
    translate_head(H,TranslationTable,NH),
    translate_list(C,TranslationTable,NC),
    translate_list(B,TranslationTable,NB). 

translate_head(H, TranslationTable, NH):- 
    H =..[Pred|Args],
    remove_translated(Args, TranslationTable, NArgs),
    NH =..[Pred|NArgs]. 

remove_translated([], _, []). 
remove_translated([A|Args], TranslationTable, NArgs):-
    member(A-_, TranslationTable), 
    !, 
    remove_translated(Args, TranslationTable, NArgs).
remove_translated([_|Args], TranslationTable, NArgs):-
    remove_translated(Args, TranslationTable, NArgs).

translate_list([], _, []).
translate_list(List, TranslationTable, TranslatedList). 

%%%%%%%%%%%%%%%%%%%%%%
get_tuples_relative(_, _, [], []).
get_tuples_relative(Pred, Vars, [Pred->Var->Tuple|Tuples], [Pred->Var->Tuple|ExtractedTuples]):-
    member(Var, Vars), 
    !,
    get_tuples_relative(Pred, Vars, Tuples, ExtractedTuples). 
get_tuples_relative(Pred, Vars, [_|Tuples], ExtractedTuples):-
    get_tuples_relative(Pred, Vars, Tuples, ExtractedTuples). 

%%%%%%%%%%%%%%%%%%%%%%
clone_tuple_var_times_preds(_, _, [], []).   
clone_tuple_var_times_preds(Tuple, Clauses, [Pred/_|PredsWithArity], ClonedTuples):-
    extract_pred(Pred, Clauses, ClausesPred),
    extract_vars(ClausesPred, VarsPred), 
    clone_tuple_var_times(Tuple, Pred, VarsPred, ClonedTuplesPred), 
    clone_tuple_var_times_preds(Tuple, Clauses, PredsWithArity, ClonedTuplesRec),
    append(ClonedTuplesPred, ClonedTuplesRec, ClonedTuples). 


clone_tuple_var_times(_, _, [], []).
clone_tuple_var_times(Tuple, Pred, [Var|Vars], [Pred->Var->Tuple|Others]):-
    clone_tuple_var_times(Tuple, Pred, Vars, Others). 

%%%%%%%%%%%%%%%%%%%%%%
empty_arg_tuple([], EAT, EAT). 
empty_arg_tuple([cl(_, Constr, _)|Clauses], CurrentArgTuple, CompleteArgTuple):- 
    add_all_functors_constraints(Constr, CurrentArgTuple, NCurrentArgTuple), 
    empty_arg_tuple(Clauses, NCurrentArgTuple, CompleteArgTuple). 

add_all_functors_constraints([], CA, CA). 
add_all_functors_constraints([C|Constr], CA, NCA):- 
    add_all_functors_constraint(C, CA, CA1), 
    add_all_functors_constraints(Constr, CA1, NCA).

add_all_functors_constraint(C, CA, CA1):-
    C =..[_|Args], 
    add_all_functors_constraint_args(Args, CA, CA1). 

add_all_functors_constraint_args([], CA, CA). 
add_all_functors_constraint_args([Arg|Args], CA, CA1):-
    add_all_functors_constraint_arg(Arg, CA, CA0),
    add_all_functors_constraint_args(Args, CA0, CA1). 

add_all_functors_constraint_arg('$VAR'(_), CA, CA):-!.
add_all_functors_constraint_arg(Arg, CA, CA0):- 
    Arg =.. [F],
    add_functor(F, CA, CA0). 
add_all_functors_constraint_arg(Arg, CA, CA0):- 
    Arg =.. [F|Args],
    add_functor(F, CA, CA00),
    add_all_functors_constraint_args(Args, CA00, CA0).

add_functor(F, CA, CA):- 
    member(F-_, CA),
    !.
add_functor(F, CA, [F-0|CA]).  

%%%%%%%%%%%%%%%%%%%%%
extract_pred_follow_links(P, Clauses, ClausesExtracted, NbLinks):-
    extract_pred(P, Clauses, ClausesP), 
    extract_from_links([P], ClausesP, Clauses, ClausesExtracted1, 1, NbLinks), 
    append(ClausesP,ClausesExtracted1,ClausesExtracted). 
 
extract_pred(_, [], []). 
extract_pred(P, [C|Clauses], [C|ClausesP]):- 
    C =..[cl,A|_],
    A =..[P|_],
    !,
    extract_pred(P, Clauses, ClausesP). 
extract_pred(P, [_|Clauses], ClausesP):-
    extract_pred(P,Clauses,ClausesP). 

extract_from_links(_, [], _, [], NbLinks, NbLinks). 
extract_from_links(BlackList, [cl(_,_,Bs)|Clauses], AllClauses, ClausesExtracted, CurrentLinks, NbLinks):-
    extract_from_atoms(BlackList, Bs, AllClauses, NBlackList, [], Extracted, CurrentLinks, NbLinks1),
    extract_from_links(NBlackList, Clauses, AllClauses, Extracted1, NbLinks1, NbLinks), 
    append(Extracted1, Extracted, ClausesExtracted). 

extract_from_atoms(BlackList, [], _, BlackList, Extracted, Extracted, NbLinks, NbLinks). 
extract_from_atoms(BlackList, [B|Bs], Clauses, NBlackList, CurrentExtracted, Extracted, CurrentLinks, NbLinks):- 
    B =..[Pred|_],
    member(Pred, BlackList),
    !,
    extract_from_atoms(BlackList, Bs, Clauses, NBlackList, CurrentExtracted, Extracted, CurrentLinks, NbLinks). 
extract_from_atoms(BlackList, [B|Bs], Clauses, NBlackList, CurrentExtracted, Extracted, CurrentLinks, NbLinks):- 
    B =..[Pred|_],
    CurrentLinks1 is CurrentLinks + 1,
    extract_pred(Pred, Clauses, Extracted1), 
    append(Extracted1, CurrentExtracted, NCurrentExtracted),
    extract_atoms(Extracted1, [], Bs1), 
    append(Bs, Bs1, NBs),
    extract_from_atoms([Pred|BlackList], NBs, Clauses, NBlackList, NCurrentExtracted, Extracted, CurrentLinks1, NbLinks).

extract_atoms([], Bs, Bs).
extract_atoms([cl(_,_,Bs)|Clauses], CurrentBs, Bss):-
    append(Bs, CurrentBs, NCurrentBs), 
    extract_atoms(Clauses, NCurrentBs, Bss).


extract_preds_with_arity(Clauses,PredsWithArity):- extract_preds_with_arity(Clauses, [], PredsWithArity). 
extract_preds_with_arity([], PredsWithArity, PredsWithArity). 
extract_preds_with_arity([cl(H,_,_)|Clauses], CurrentPreds, PredsWithArity):-
    H =..[Pred|Args], 
    length(Args, A), 
    member(Pred/A, CurrentPreds), 
    !, 
    extract_preds_with_arity(Clauses, CurrentPreds, PredsWithArity).
extract_preds_with_arity([cl(H,_,_)|Clauses], CurrentPreds, PredsWithArity):-
    H =..[Pred|Args], 
    length(Args, A), 
    extract_preds_with_arity(Clauses, [Pred/A|CurrentPreds], PredsWithArity).


%%%%%%%%%%%%%%%%%%%%%
extract_vars([], []). 
extract_vars([cl(H,C,B)|Clauses], Vars):-
    extract_vars_rec(H, VarsH),
    extract_vars_rec(C, VarsC),
    extract_vars_rec(B, VarsB), 
    append(VarsH, VarsC, VarsHC),
    append(VarsHC, VarsB, VarsHCB),
    extract_vars(Clauses, VarsClauses),
    append(VarsHCB,VarsClauses, AllVars),
    sort(AllVars, Vars). 

extract_vars_rec('$VAR'(I), ['$VAR'(I)]):-!.
extract_vars_rec([], []):-!.
extract_vars_rec([T1|Ts], Vars):- 
    !,
    extract_vars_rec(T1, Vars1), 
    extract_vars_rec(Ts, Vars2), 
    append(Vars1,Vars2,Vars).
extract_vars_rec(Term, Vars):-
    %format('~nTerm: ~w', [Term]),
    Term =..[F|Args], 
    (F = '$VAR'(_) -> extract_vars_rec(F, Vars1) ; true), 
    (Args \= [] -> extract_vars_rec(Args, Vars2) ; true), 
    append(Vars1, Vars2, Vars). 
    
extract_pred_name(H, Pred):-
    H =..[Pred|_]. 