% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
:- module(types, [types/1, types1/7, test/0, main/1]).


:- use_module(library(lists)).
:- use_module(genconstraints).
:- use_module(solveconstraints).
%:- use_module(writeTerminWeb).

main([F]) :-
        types(F).
        
types(F) :-
        types1(F,_Cs,_Ss,Ts1,Ts2,Signatures,_Count),
        
        %length(Ss,LocalsCount),
        %write(user_output, 'No of Generated constraints'), 
        %write(user_output,LocalsCount), nl(user_output),
        %write(user_output, 'Generated constraints'), nl(user_output),
        %writeConstraints(Cs,user_output),
        %write(user_output, 'Solved constraints'), nl(user_output),
        %writeConstraints(Ss,user_output),
        %write(user_output, 'Type definitions'), nl(user_output),
        %writeTypeDefs(Ts1,user_output),
        %nl(user_output),
        
        %open('type.out',write,Stream),
        Stream=user_output,
        write(Stream, 'Normalised Type definitions'), nl(user_output),
        writeTypeDefs(Ts2,Stream),
        nl(Stream),
        write(Stream, 'Signatures'), nl(Stream),
        writeConstraints(Signatures,Stream),
        nl(Stream),
        %write(Stream,'Number of constraints = '),
        %write(Stream,Count),
        nl(Stream).
        %close(Stream).
        %write(user_output, 'TerminWeb'), nl(user_output),
        %writeTerminWeb(Ts2,Signatures,user_output).
        
        
types1(F,Cs,Ss,Ts1,Ts2,Signatures,Count) :-
        genconstraints(F,Cs,Sigs0),
        solveconstraints(Cs,Ss,Ts1,Ts2,Sigs0,Signatures,Count).
        
        
%--------------
        
writeTypeDefs([],_).
writeTypeDefs([typedef(T,Cs)|Ts],S) :-
        write(S,T),
        write(S,' --> '),
        writeCases(Cs,S),
        nl(S),
        writeTypeDefs(Ts,S).
        
writeCases([],_).
writeCases([C],S) :-
        write(S,C).
writeCases([C1,C2|Cs],S) :-
        write(S,C1),
        write(S,'; '),
        writeCases([C2|Cs],S).
        
writeConstraints([],S) :-
        nl(S).
writeConstraints([C|Cs],S) :-
        write(S,C),
        nl(S),
        writeConstraints(Cs,S).
        
%---tests-------------
        
test :-
        write('==================='),nl,
        write('Tests/append.pl'),nl,
        write('==================='),nl,
        types('Tests/append.pl'),
        
        write('==================='),nl,
        write('Tests/rev.pl'),nl,
        write('==================='),nl,
        types('Tests/rev.pl'),
        
        write('==================='),nl,
        write('Tests/trans.pl'),nl,
        write('==================='),nl,
        types('Tests/trans.pl'),
        
        write('==================='),nl,
        write('Tests/frev.pl'),nl,
        write('==================='),nl,
        types('Tests/frev.pl'),
        
        write('==================='),nl,
        write('Tests/pq.pl'),nl,
        write('==================='),nl,
        types('Tests/pq.pl'),
        
        write('==================='),nl,
        write('Example from Combined Norms paper'),nl,
        write('==================='),nl,
        types('Tests/combinednorm_p.pl'),
        
        write('==================='),nl,
        write('Transpose from Combined Norms paper'),nl,
        write('==================='),nl,
        types('Tests/combinednorm_trans.pl'),
        
        write('==================='),nl,
        write('parse from Combined Norms paper'),nl,
        write('==================='),nl,
        types('Tests/parse.pl'),
        
        write('==================='),nl,
        write('Ackermann'),nl,
        write('==================='),nl,
        types('Tests/combinednorm_ack.pl'),
        
        write('==================='),nl,
        write('Tests/dnf.pl'),nl,
        write('==================='),nl,
        types('Tests/dnf.pl'),
        
        write('==================='),nl,
        write('Tests/qsort.pl'),nl,
        write('==================='),nl,
        types('Tests/qsort.pl').
        
