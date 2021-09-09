
conc3(A,B,C,Appended):- {A = nil, B = nil}, Appended = C.
conc3(A, B, C, Appended):- {A = nil}.

app3(A, B, C, Appended):- {C = nil, B = nil, Appended = A}.
app3(A, B, C, Appended):- {C = nil, B = cons(B1,RestB)}, app(A, RestB, NewC).
app3(A, B, C, Appended):- {A = cons(A1, RestA)}.


app3(A, B, C, Appended):- {A = nil, B = nil, C = nil, Appended = nil}.
app3(A, B, C, Appended):- {A = cons(A1, RestA), Appended = cons(A, RestAppended)}, app3(RestA, B, C, RestAppended).
app3(A, B, C, Appended):- {A = nil, B = cons(B1, RestB), Appended = cons(B1, RestAppended)}, app3(A, RestB, ).