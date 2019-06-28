:-module(au_complexity, [
    anti_unification_coefficient/3,
    variables_coefficient/3,
    variables_coefficient/2
]).

:-use_module(generalization_utils).

anti_unification_coefficient(Atoms1, Atoms2, Coeff):-
	anti_unification_coefficients(Atoms1, Atoms2, Coeffs),
	agregate_coeffs(Coeffs, Coeff).

anti_unification_coefficients([], _, []).
anti_unification_coefficients([A1|Atoms1], Atoms2, [L1-L2|Coeffs]):-
	configuration(A1, Config),
	 %format("~n Configuration en cours d'extraction : ~w", [Config]),
	extract_configuration(Atoms1, Config, A1s, Others1),
	append([A1], A1s, Atoms1WithConfig),
	extract_configuration(Atoms2, Config, Atoms2WithConfig, Others2),
	length(Atoms1WithConfig, L1),
	length(Atoms2WithConfig, L2),
 %	format("... ~w atomes dans la clause 1, ~w atomes dans la clause 2", [L1, L2]),
	anti_unification_coefficients(Others1, Others2, Coeffs).

extract_configuration([], _, [], []).
extract_configuration([A|Atoms], Config, [A|OutAtoms], Others):-
		configuration(A, Config),
		!,
		extract_configuration(Atoms,Config,OutAtoms, Others).
extract_configuration([A|Atoms], Config, OutAtoms, [A|Others]):-
	extract_configuration(Atoms, Config, OutAtoms, Others).

configuration(A1, F-ArgsConfig):-
	 A1 =..[F|Args],
	 args_to_config(Args, ArgsConfig).

args_to_config(Args, ArgsConfig):-
	args_to_config(Args, [], [], ArgsConfig).
args_to_config([], _, ArgsConfig, ArgsConfig).
args_to_config(['$VAR'(I)|Args], AccConfigComplete, AccConfig, ArgsConfig):-
	member(I-J, AccConfigComplete),
	!,
	append(AccConfigComplete, [I-J], NAccConfigComplete),
	append(AccConfig, [J], NAccConfig),
	args_to_config(Args, NAccConfigComplete, NAccConfig, ArgsConfig).
args_to_config(['$VAR'(I)|Args], AccConfigComplete, AccConfig, ArgsConfig):-
	max_l(AccConfig, J1),
	J is J1 + 1,
	append(AccConfigComplete, [I-J], NAccConfigComplete),
	append(AccConfig, [J], NAccConfig),
	args_to_config(Args, NAccConfigComplete, NAccConfig, ArgsConfig).

max_l([], 0).
max_l([X],X) :- !.
max_l([X|Xs], M):- max_l(Xs, M), M >= X.
max_l([X|Xs], X):- max_l(Xs, M), X >  M.

agregate_coeffs(Coeffs, Coeff):-
	agregate_coeffs(Coeffs, 1, Coeff).
agregate_coeffs([], Coeff, Coeff).
agregate_coeffs([L1-L2|Coeffs], Acc, Coeff):-
  LMAX is max(L1,L2),
  LMIN is min(L1,L2),
  LMAX2 is LMAX + LMIN,
	fact_comb(LMIN, LMAX2, FC),
	Acc1 is Acc * FC,
	agregate_coeffs(Coeffs, Acc1, Coeff).

variables_coefficient(Atoms1, Atoms2, VariablesCoefficient):-
  build_matrix(Atoms1, Atoms2, Matrix),
  variables_coefficient(Matrix, VariablesCoefficient).
variables_coefficient(Matrix, VariablesCoefficient):-
  extract_matrix_variables(Matrix, Variables1, Variables2),
	!,
	length(Variables1, L1),
	length(Variables2, L2),
	fact_comb(L1,L2,VariablesCoefficient).

fact_comb(L1, L2, FC):-
	L1 =< L2,
	fact(L1, F),
	comb(L1, L2, C),
	FC is C * F.
fact_comb(L1, L2, FC):-
	L1 > L2,
	fact(L2, F),
	comb(L2, L1, C),
	FC is C * F.

comb(L1, L2, Comb) :-
		fact(L2, F2),
		fact(L1, F1),
		L3 is L2 - L1,
		fact(L3, F3),
		Num is F3 * F1,
		Comb is F2 / Num.

fact(0,Result) :-
    Result is 1.
fact(N,Result) :-
    N > 0,
    N1 is N-1,
    fact(N1,Result1),
    Result is Result1*N.
