:- [read_line].

%%%% read in processor data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%sentence
sentence(ID, C, A, D) --> word, word, typeID(ID), word, numCores(C), 
						  word, comma, word, numArea(A), 
						  word, word, comma, word, word, numDollars(D), word, period.

%parts of the sentence
word --> [processor] | [type] | [has] | [cores] | [uses] | [square] | 
		 [centimeters] | [and] | [costs] | [dollars].
comma --> [,].
period --> [.].

typeID(A) --> [A], 
	{b_getval(processors, P), append(P, [[A]], PAppd), b_setval(processors, PAppd)}, 
	{write('ID   > processors: '), b_getval(processors, PP), write(PP), nl},
	{write('ID: '), write(A), nl}.
	
numCores(A) --> [A], 
	{b_getval(processors, P), last(P, PLast), append(PLast, [A], TAppd), delete(P, PLast, H), append(H, [TAppd], PAppd), b_setval(processors, PAppd)}, 
	{write('CORE > processors: '), b_getval(processors, PP), write(PP), nl},
	{write('Cores: '), write(A), nl}.

numArea(A) --> [A], 
	{b_getval(processors, P), last(P, PLast), append(PLast, [A], TAppd), delete(P, PLast, H), append(H, [TAppd], PAppd), b_setval(processors, PAppd)}, 
	{write('Area > processors: '), b_getval(processors, PP), write(PP), nl},
	{write('Area: '), write(A), nl}.

numDollars(A) --> [A], 
	{b_getval(processors, P), last(P, PLast), append(PLast, [A], TAppd), delete(P, PLast, H), append(H, [TAppd], PAppd), b_setval(processors, PAppd)}, 
	{write('$$$  > processors: '), b_getval(processors, PP), write(PP), nl},
	{write('$$$: '), write(A), nl}.


%%%% read in constraint data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%shared constraint grammar
attribute(core) --> [core], {b_setval(workingConstraintAttr, core), write('core attr'), nl}.  %, {write('core count'), nl}.
attribute(area) --> [area], {b_setval(workingConstraintAttr, area), write('area attr'), nl}.  %, {write('area count'), nl}.
attribute(cost) --> [cost], {b_setval(workingConstraintAttr, cost), write('cost attr'), nl}.  %, {write('cost count'), nl}.

imperative --> ([must] | [is]).


%read comparison constraint
compConstraint(A, C, V) --> ([the] | []), attribute(A), ([count] | []), %attribute
					  imperative, ([to] | []), [be], 					%imperative
					  comparison(C), ([to] | [than]), 					%comparison
					  value(V), period.									%value

comparison(equal) --> [equal], % add list name to buffer
	{b_setval(workingConstraintComp, compConstraintsEqual)}.
comparison(greater) --> [greater],
	{b_setval(workingConstraintComp, compConstraintsGreater)}.
comparison(less) --> [less],
	{b_setval(workingConstraintComp, compConstraintsLesser)}.


value(A) --> [A], 
	{b_getval(workingConstraintComp, CC), 					%gets global compConstraintsEqual/compConstraintsGreater/compConstraintsLesser
	 b_getval(CC, CompCons), 								%gets lists from global
	 b_getval(workingConstraintAttr, Attr), 				%gets Attribute
	 append(CompCons, [[Attr, A]], CCAppd), 				%appends [attribute, value] and set global to new list
	 b_setval(CC, CCAppd)}.
	%{write('value: '), write(A), nl}.


%read range constraint
rangeConstraint(A, LB, UB) --> ([the] | []), {write('---got to before attribute')}, {write(A)}, attribute(A), {write('---completed attribute')}, ([count] | []), 	  %attribute
					  imperative, ([to] | []), [be],					   	  %imperative
					  [in], [the], ([range] | [interval]), [of], 		   	  %interval
					  lowerBoundValue(LB), [to], upperBoundValue(UB), period. %range


lowerBoundValue(LB) --> [LB], 
	{write('lower bound not set yet but will be soon'), b_setval(workingRangeLB, LB), write('lower bound set'), nl}.
	%{write('value1: '), write(LB), nl}.

upperBoundValue(UB) --> [UB], 
	{b_getval(workingRangeLB, LB), 						%get lower bound
	 b_getval(workingConstraintAttr, Attr),				%get attribute 
	 b_getval(rangeConstraints, RC),					%get global rangeConstraints
	 write('-----------'), write(Attr),write(LB),write(UB),
	 append(RC, [Attr, LB, UB], RCAppd),				%appends [attribute, lower bound, upper bound] and set global to new list
	 b_setval(rangeConstraints, RCAppd)}. 					
	%{write('value2: '), write(UB), nl}.


%%%% determine type of sentence %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%unifies the size of a list with L
size([], 0).
size([H|T], L) :- size(T, TL), L is TL+1.

parseSentence([H|T]) :- H == processor, !, %list outlines a processor?
						write('processor sentence: '), write([H|T]), nl, sentence(ID, C, A, D, [H|T], []), nl.

parseSentence([H|T]) :- size([H|T], S), S1 is (S-3), nth0(S1,[H|T],B), %setup
						B == to, !,  %list is an interval?
						write('Range Constraint sentence: '), write([H|T]), nl, rangeConstraint(A, LB, UB, [H|T], []), nl.

parseSentence([H|T]) :- write('Comparison Constraint sentence: '), write([H|T]), nl, compConstraint(A, C, V, [H|T], []), nl.


%%%% read loop  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

read_loop :-
	write('@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@'), nl,
	read_line(Line),
	parseSentence(Line),
	
	length(Line, Len),
	(
		Len > 0,
		%write(Line), nl,
		read_loop;
		%Len =< 0,
		write('Read last line.'), nl
	).




%%%% you will never guess what this section does %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
main :-
	% %%% set globals %%%
	b_setval(processors, []), %each entry will be [id, core count, size, cost]

	%attribute buffer
	b_setval(workingConstraintAttr, none),

	%comparison buffer
	b_setval(workingConstraintComp, none),

	%each entry is [attribute, value]
	b_setval(compConstraintsGreater, []), 
	b_setval(compConstraintsEqual, []),
	b_setval(compConstraintsLesser, []),

	%range buffer
	b_setval(workingRangeLB, none),

	b_setval(rangeConstraints, []), %each entry is [attribute, lower bound, upper bound]
	
	%%% loop %%%
	write('not main'), nl,		
	read_loop,
	
	write('Processes:   '), b_getval(processors, PEnd),
	write(PEnd), nl, nl,
	
	b_getval(compConstraintsGreater, GConstraint),
	write('Greater than '), write(GConstraint), nl,
	b_getval(compConstraintsEqual, EConstraint),
	write('Equal to     '), write(EConstraint), nl,
	b_getval(compConstraintsLesser, LConstraint),
	write('Less than    '), write(LConstraint), nl,

	b_getval(rangeConstraints, RConstraint),
	write('Ranges       '), write(RConstraint), nl.


	% b_setval(processorCount, 3), %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%SET TO LENGTH OF processors
	% testCombos([b,c], [0], 0, 1).



	%%% Constraint Calculations %%%
	
	%nth0(0,PEnd, A), nth0(1, A, ACore), write(ACore),

% satisfiesConstraints(ProcsCount) :- 
% 	for constrant in [all constraints]:
% 	  if constraint is cost:
% 			cost(ProcsCount) < cost
% 	  if area:
% 	  if core count:
% 	 satisfiesConstraints(ProcsCount).


testCombos(ProcsList, ProcsCount, N, NumProcsCounted) :-
	ProcsList == [], N < 4, !,

	write(ProcsCount), nl,

	%iterate processor count
	M is N+1,
	nth1(NumProcsCounted, ProcsCount, _, ProcsCountNonTail),
	append(ProcsCountNonTail, [M], IteratedProcsCount),
	N < 4,
	testCombos(ProcsList, IteratedProcsCount, M, NumProcsCounted).

testCombos(ProcsList, ProcsCount, N, NumProcsCounted) :-
	N < 4,

	%begin the recursive generation of the next processor with the previous processor's counts
	%that'll be doing [a, b, ..., n, 0], [a, b, ..., n, 1], ...
	nth0(0, ProcsList, First),
	delete(ProcsList, First, NextProcsList),
	append(ProcsCount, [0], NextProcsCount),
	NPCNext is NumProcsCounted+1,
	not(testCombos(NextProcsList, NextProcsCount, 0, NPCNext)),

	%iterate count of current processor [a, b, ..., n+1] where 0 <= a-z <= 16
	M is N+1,
	nth1(NumProcsCounted, ProcsCount, _, ProcsCountNonTail),
	append(ProcsCountNonTail, [M], IteratedProcsCount),
	testCombos(ProcsList, IteratedProcsCount, M, NumProcsCounted).


	






	%sentence(ID, C, A, D, [has,has,a,has,2,has,,,has,2,has,has,,,has,has,2,has,.], []).
	%read_loop.
