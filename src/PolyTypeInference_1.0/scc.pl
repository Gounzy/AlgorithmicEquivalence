% Type inference system (designed by M. Bruynooghe and J. Gallagher)
% Version 1.0 created by jpg on 12/04/2005
% (c) Roskilde University
 
% Strongly connected components based
% on depth-first search of a graph.
% Algorithm by M. Sharir, adapted from
% Baase and Van Gelder, Chapter 7.5
% JPG 20/8/01

:- module(scc, [scc_sharir/2,makeEqualitiesGraph/2]).


:- use_module(balanced_tree).
:- use_module(setops).
:- use_module(library(lists)).




% scc_sharir: the SCC procedure.

scc_sharir(root,[]) :-
	!.
scc_sharir(Graph,SCCs) :-
	phase1(Graph,Stack),
	phase2(Stack,Graph, SCCs),
	!,
	recursive_classify(SCCs,Graph).
	
phase1(Graph,Stack) :-
	traversekey_tree(Graph,Nodes),
	dfsSweep(Nodes,Graph,root,_,[],Stack).

dfsSweep([], _, MarkList, MarkList, Stack, Stack).
dfsSweep([N|Ns], Graph, MarkListIn, MarkListOut, StackIn, StackOut) :-
	search_tree(MarkListIn,N,black),   % N already visited
	!,
	dfsSweep(Ns, Graph, MarkListIn, MarkListOut, StackIn, StackOut).
dfsSweep([N|Ns], Graph, MarkListIn, MarkListOut, StackIn, StackOut) :-
	dfsNode(Graph, N, MarkListIn, MarkListMid, StackIn, StackMid),
	dfsSweep(Ns, Graph, MarkListMid, MarkListOut, StackMid, StackOut).

dfsNode(Graph,N,M0,M2,S0,S1) :-
	insert_tree(M0,N,black,M1),   % mark node as visited
	find_succs(Graph,N,SuccList),
	dfs_each(SuccList,Graph,N,M1,M2,S0,S1).

find_succs(Graph,N,SuccList) :-
	search_tree(Graph,N,links(SuccList,_)),
	!.
find_succs(_,_,[]).

dfs_each([],_,Par,M,M,S,[Par|S]).
dfs_each([N|Ns],G,Par,M0,M1,S0,S1) :-
	search_tree(M0,N,black),
	!,
	dfs_each(Ns,G,Par,M0,M1,S0,S1).
dfs_each([N|Ns],G,Par,M0,M2,S0,S2) :-
	dfsNode(G,N,M0,M1,S0,S1),
	dfs_each(Ns,G,Par,M1,M2,S1,S2).

% phase 2:  use the depth-first ordering from phase 1
% to traverse the transposed graph.

phase2(Nodes,Graph,SCCs) :-
	dfsSweep2(Nodes,Graph,root,_,[],SCCs).

dfsSweep2([], _, MarkList, MarkList, S,S).
dfsSweep2([N|Ns], Graph, MarkListIn, MarkListOut, S0,S1) :-
	search_tree(MarkListIn,N,black),  % N already visited
	!,
	dfsSweep2(Ns, Graph, MarkListIn, MarkListOut, S0,S1).
dfsSweep2([N|Ns], Graph, MarkListIn, MarkListOut, S0,S2) :-
	dfsNode2(Graph, N, N,MarkListIn, MarkListMid,[],S1),
	dfsSweep2(Ns, Graph, MarkListMid, MarkListOut, [(_,S1)|S0],S2).

dfsNode2(Graph,N,L,M0,M2,S0,S1) :-
	insert_tree(M0,N,black,M1),  % mark node as visited
	search_tree(Graph,N,links(_,PrecList)),
	dfs_each2(PrecList,Graph,N,L,M1,M2,[N|S0],S1).

dfs_each2([],_,_,_,M,M,S,S).
dfs_each2([N|Ns],G,L,Par,M0,M1,S0,S1) :-
	search_tree(M0,N,black),
	!,
	dfs_each2(Ns,G,Par,L,M0,M1,S0,S1).
dfs_each2([N|Ns],G,Par,L,M0,M2,S0,S2) :-
	dfsNode2(G,N,L,M0,M1,S0,S1),
	dfs_each2(Ns,G,L,Par,M1,M2,S1,S2).

recursive_classify([],_).
recursive_classify([(recursive,[_,_|_])|Cs],G) :-
	!,
	recursive_classify(Cs,G).
recursive_classify([(recursive,[P])|Cs],G) :-
	direct_recursive(P,G),
	!,
	recursive_classify(Cs,G).
recursive_classify([(non_recursive,_)|Cs],G) :-
	recursive_classify(Cs,G).

direct_recursive(P,G) :-
	search_tree(G,P,links(Ss,_)),
	member(P,Ss).



% test
% graph [a-b,a-c,a-f,b-c,b-d,d-a,d-c,e-c,e-g,f-a,f-c,g-d,g-e]
% SCCs = [(non_recursive,[c]),(recursive,[f,b,d,a]),(recursive,[g,e])]



% starting from a list of links,
% make an adjacency list representation of the graph 
% and the transposed graph (reversing links).

makeEqualitiesGraph([],root).
makeEqualitiesGraph([A=B|Ls],G) :-
	makeEqualitiesGraph(Ls,G1),
	insert_succ_link(A,B,G1,G2),
	insert_succ_link(B,A,G2,G3),
	insert_pred_link(B,A,G3,G4),
	insert_pred_link(A,B,G4,G).

insert_succ_link(Q,P,G0,G1) :-
	search_replace_tree(G0,Q,links(Ps,Ss),G1,links(Ps1,Ss)),
	!,
	setunion([P],Ps,Ps1).
insert_succ_link(Q,P,G0,G1) :-
	insert_tree(G0,Q,links([P],[]),G1).

insert_pred_link(Q,P,G0,G1) :-
	search_replace_tree(G0,Q,links(Ps,Ss),G1,links(Ps,Ss1)),
	!,
	setunion([P],Ss,Ss1).
insert_pred_link(Q,P,G0,G1) :-
	insert_tree(G0,Q,links([],[P]),G1).

