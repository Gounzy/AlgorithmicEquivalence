:- module(assignment, [solve_assignment_problem/2, set_unmarked/2, print_preds_matrix/1]).

solve_assignment_problem([], []).
solve_assignment_problem(Matrix, MA):-
  length(Matrix, N),
  substract_minima_rows(Matrix, NMatrix),
  substract_minima_cols(NMatrix, NNMatrix),
  draw_few_lines(NNMatrix, NNNMatrix, NLines),
  %print_preds_matrix(NNNMatrix),
  %format('~n NLines: ~w', [NLines]),
  (NLines = N -> get_ma_from_ap(NNNMatrix, MA) ; solve_assignment_problem_laststep(NNNMatrix, N, MA)).

solve_assignment_problem_laststep(Matrix, N, MA):-
  substract_minima_cols(Matrix, NMatrix),
  draw_few_lines(NMatrix, NNMatrix, NLines),
  %print_preds_matrix(NNMatrix),
  %format('~n NLines: ~w', [NLines]),
  (NLines = N -> get_ma_from_ap(NNMatrix, MA)).

get_ma_from_ap(NMatrix, MA) :-
  format('~n get_ma_from_ap : ~w ', [NMatrix]).


draw_few_lines(Matrix, MarkedMatrix, NLines):-
  set_unmarked(Matrix, VirginMatrix),
  assign_as_much_as_possible(VirginMatrix, [], NMatrix),
  mark_rows_with_no_assignments(NMatrix, NNMatrix),
  loop_draw_marks(NNMatrix, OutMatrix, NLines),
  sanitize_matrix(OutMatrix, MarkedMatrix).

sanitize_matrix([], []).
sanitize_matrix([assigned(Line)|List], [Line|ListOut]):-
  sanitize_matrix(List,ListOut).
sanitize_matrix([unassigned(Line)|List], [Line|ListOut]):-
  sanitize_matrix(List,ListOut).

loop_draw_marks(Matrix, MarkedMatrix, NLines) :-
    mark_columns_having_zeros(Matrix, Matrix, NMatrix, 0, NMarks1),
    mark_rows_having_assignments(NMatrix, NMatrix, NNMatrix, 0, NMarks2),
    NMarks is NMarks1 + NMarks2,
    (NMarks > 0 -> loop_draw_marks(NNMatrix, MarkedMatrix, NLines) ; MarkedMatrix = NNMatrix),
    (NMarks = 0 -> count_lines(NNMatrix, NLines)).

count_lines(Matrix, NLines):-
  count_marked_columns(Matrix, NColumns),
  count_unmarked_rows(Matrix, NRows),
  NLines is NRows + NColumns.

count_marked_columns([], 0).
count_marked_columns(Matrix, N):-
  extract_column(Matrix, Column, Rest),
  (is_marked(Column) -> N1 is 1 ; N1 is 0),
  count_marked_columns(Rest, N2),
  N is N1 + N2.

extract_nth_column([], _, []).
extract_nth_column([Line|Matrix], N, [Elem|Column]):-
  nth1(N, Line, Elem),
  extract_nth_column(Matrix, N, Column).

extract_column([], [], []).
extract_column([Line|Matrix], Column, RestMatrix):-
  (is_list(Line) -> X = Line ; Line =..[_|[X]]),
  X = [], 
  !,
  extract_column(Matrix,Column,RestMatrix).
extract_column([Line|Matrix], [Elem|Column], [RestLine|RestMatrix]):-
  (is_list(Line) -> X = Line ; Line =..[_|[X]]),
  select(Elem, X, RestLine),
  !,
  extract_column(Matrix,Column,RestMatrix).

count_unmarked_rows(Matrix, N):- count_unmarked_rows(Matrix, 0, N).
count_unmarked_rows([], C, C).
count_unmarked_rows([FLine|Matrix], Counter, N):-
  FLine =..[_,Line],
  is_marked(Line),
  !,
  count_unmarked_rows(Matrix,Counter,N).
count_unmarked_rows([_|Matrix], Counter, N):-
  Counter1 is Counter + 1,
  count_unmarked_rows(Matrix, Counter1, N).

mark_rows_having_assignments([], _, [], Counter, Counter).
mark_rows_having_assignments([unassigned(Line)|Matrix], WholeMatrix, [unassigned(Line)|NMatrix], Counter, NLines):-
  mark_rows_having_assignments(Matrix,WholeMatrix,NMatrix,Counter,NLines).
mark_rows_having_assignments([assigned(Line)|Matrix], WholeMatrix, [assigned(NLine)|NMatrix], Counter, NLines):-
  has_marked_zero(Line),
  !,
  mark_line(Line,NLine),
  Counter1 is Counter + 1,
  mark_rows_having_assignments(Matrix,WholeMatrix,NMatrix,Counter1,NLines).
mark_rows_having_assignments([assigned(Line)|Matrix], WholeMatrix, [assigned(Line)|NMatrix], Counter, NLines):-
  mark_rows_having_assignments(Matrix, WholeMatrix, NMatrix, Counter, NLines).

mark_columns_having_zeros([], Matrix, Matrix, Counter, Counter).
mark_columns_having_zeros([Line|Lines], WholeMatrix, NMatrix, Counter, N):-
  is_marked(Line),
  has_zero(Line, Position),
  extract_nth_column(Position, WholeMatrix, Column),
  not(is_marked(Column)),
  !,
  mark_column(Position, WholeMatrix, NewWholeMatrix),
  Counter1 is Counter + 1,
  mark_columns_having_zeros(Lines, NewWholeMatrix, NMatrix, Counter1, N).
mark_columns_having_zeros([_|Lines], WholeMatrix, NMatrix, Counter, N):-
  mark_columns_having_zeros(Lines, WholeMatrix,NMatrix, Counter, N).

is_marked([]).
is_marked([marked(_)|List]):- is_marked(List).

mark_rows_with_no_assignments([], []).
mark_rows_with_no_assignments([assigned(Line)|Matrix], [assigned(Line)|NMatrix]) :- !,
  mark_rows_with_no_assignments(Matrix, NMatrix).
mark_rows_with_no_assignments([unassigned(Line)|Matrix], [unassigned(NLine)|NMatrix]) :- !,
  mark_line(Line, NLine),
  mark_rows_with_no_assignments(Matrix, NMatrix).

assign_as_much_as_possible([], _, []).
assign_as_much_as_possible([Line|Lines], CrossedPositions, [assigned(Line)|AssignedLines]):-
  has_zero(Line, Position),
  not(member(Position, CrossedPositions)),
  !,
  assign_as_much_as_possible(Lines, [Position|CrossedPositions], AssignedLines).
assign_as_much_as_possible([Line|Lines], CrossedPositions, [unassigned(Line)|AssignedLines]):-
  assign_as_much_as_possible(Lines, CrossedPositions, AssignedLines).

has_marked_zero([marked(0)|_]):-!.
has_marked_zero([_|Line]):-has_marked_zero(Line).

has_zero(Line, Position):- has_zero(Line, 1, Position).
has_zero([marked(0)|_], CurrentPosition, CurrentPosition):-!.
has_zero([unmarked(0)|_], CurrentPosition, CurrentPosition):-!.
has_zero([_|Line], CurrentPosition, Position):-
  CurrentPosition1 is CurrentPosition + 1,
  has_zero(Line, CurrentPosition1, Position).

substract_minima_rows([], []).
substract_minima_rows([Line|Matrix], [LineSubstracted|NMatrix]):-
  substract_minimum_row(Line,LineSubstracted),
  substract_minima_rows(Matrix,NMatrix).

substract_minimum_row(Line, LineSubstracted):-
  minimum(Line, Min),
  substract_row(Line, Min, LineSubstracted).

minimum(List, Min):-
  minimum(List, 500000, Min).

minimum([], Min, Min).
minimum([E|List], CurrentMin, Min):-
  E =..[_,Val],
  Val < CurrentMin,
  !,
  minimum(List, Val, Min).
minimum([_|List], CurrentMin, Min):-
  minimum(List, CurrentMin, Min).

substract_row([], _, []).
substract_row([E|List], Value, [NE|NList]):-
  E =..[F,Val],
  NVal is Val - Value,
  NE =..[F,NVal],
  substract_row(List, Value, NList).

substract_minima_cols(Matrix, SubstractedMatrix):-
  length(Matrix, L),
  substract_minima_cols(Matrix, 1, L, SubstractedMatrix).

substract_minima_cols(Matrix, N, NMax, Matrix):- N > NMax,!.
substract_minima_cols(Matrix, NCol, NMax, SubstractedMatrix):-
  NCol =< NMax,
  find_minimum_col(NCol, Matrix, Min),
  substract_minimum_col(NCol, Min, Matrix, NMatrix),
  NCol1 is NCol + 1,
  substract_minima_cols(NMatrix, NCol1, NMax, SubstractedMatrix).

find_minimum_col(Idx, Matrix, Min):-
  find_minimum_col(Idx, Matrix, 500000, Min).

find_minimum_col(_, [], CurrentMin, CurrentMin).
find_minimum_col(Idx, [Line|Lines], CurrentMin, Min):-
  nth1(Idx, Line, Elem),
  Elem =..[_,Val],
  (Val < CurrentMin -> find_minimum_col(Idx, Lines, Val, Min) ; find_minimum_col(Idx, Lines, CurrentMin, Min)).


set_unmarked([], []).
set_unmarked([Line|Matrix], [MarkedLine|MarkedMatrix]):-
  unmark_line(Line,MarkedLine),
  set_unmarked(Matrix,MarkedMatrix).

unmark_line([], []).
unmark_line([marked(Elem)|Line],[unmarked(Elem)|LineUnMarked]):- !,
  unmark_line(Line, LineUnMarked).
unmark_line([unmarked(Elem)|Line],[unmarked(Elem)|LineUnMarked]):- !,
  unmark_line(Line, LineUnMarked).
unmark_line([Elem|Line],[unmarked(Elem)|LineUnMarked]):-
  unmark_line(Line, LineUnMarked).


mark_line([], []).
mark_line([marked(Elem)|Line], [marked(Elem)|LineMarked]):- !,
  mark_line(Line, LineMarked).
mark_line([unmarked(Elem)|Line], [marked(Elem)|LineMarked]):- !,
  mark_line(Line, LineMarked).
mark_line([Elem|Line], [marked(Elem)|LineMarked]):-
  mark_line(Line, LineMarked).

mark_column(_, [], []).
mark_column(Idx, [assigned(Line)|Matrix], [assigned(MarkedLine)|MarkedMatrix]):-
  mark_nth(Idx, 1, Line, MarkedLine),
  mark_column(Idx,Matrix,MarkedMatrix).
mark_column(Idx, [unassigned(Line)|Matrix], [unassigned(MarkedLine)|MarkedMatrix]):-
  mark_nth(Idx, 1, Line, MarkedLine),
  mark_column(Idx,Matrix,MarkedMatrix).
mark_column(Idx, [Line|Matrix], [MarkedLine|MarkedMatrix]):-
  mark_nth(Idx, 1, Line, MarkedLine),
  mark_column(Idx,Matrix,MarkedMatrix).

mark_nth(_, _, [], []).
mark_nth(N, Counter, Line, Line):-
  Counter > N, !.
mark_nth(N, Counter, [Elem|Line], [Elem|LineMarked]):-
  Counter < N, !,
  Counter1 is Counter + 1,
  mark_nth(N, Counter1, Line, LineMarked).
mark_nth(N, N, [unmarked(Elem)|Line], [marked(Elem)|Line]):-!.
mark_nth(N, N, Line, Line):-!.


substract_minimum_col(_, _, [], []).
substract_minimum_col(Idx, Value, [Line|Matrix], [NLine|NMatrix]):-
  Idx1 is Idx - 1,
  take_n(Line, Idx1, FirstElems, [Elem|Rest]),
  Elem =..[F,Val],
  NVal is Val - Value,
  NElem =..[F,NVal],
  append(FirstElems, [NElem|Rest], NLine),
  substract_minimum_col(Idx, Value, Matrix, NMatrix).

take_n([], _, [], []).
take_n(List, N, [], List):-N =< 0, !.
take_n([Elem|List], N, [Elem|Taken], Rest):-
  N1 is N - 1,
  take_n(List,N1,Taken, Rest).


print_preds_matrix([]).
print_preds_matrix([Line|Matrix]):-
  format('~n'),
  print_line_matrix(Line,1),
  print_preds_matrix(Matrix).

print_line_matrix([], _).
print_line_matrix([Elem|Line], N):-
  Tab is N * 10,
  N1 is N + 1,
  format('|~w~t~*|', [Elem, Tab]),
  print_line_matrix(Line, N1).