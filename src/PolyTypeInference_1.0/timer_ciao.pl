% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
:- module(timer_ciao, [start_time/0, end_time/1, end_time/2]).

%:- use_module(library(prolog_sys)).  % Ciao library - not needed for SICStus

start_time :-
        statistics(runtime,_).

end_time(_,_) :-
        !.
end_time(Message, S) :- 
        statistics(runtime,[_,T1]),
        Time is T1/1000,
        write(S, Message),
        write(S, Time),
        write(S, ' secs.'),
        nl(S).

end_time(S) :-
        end_time('Analysis Time: ',S).
