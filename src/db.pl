:-module(db,[init/0, increment_var_counter/0, set_var_counter/1]).

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
	