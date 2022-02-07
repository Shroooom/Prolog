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
	{b_getval(processors, P), append(P, [[A]], PAppd), b_setval(processors, PAppd)}.
	%{write('ID   > processors: '), b_getval(processors, PP), write(PP), nl},
	%{write('ID: '), write(A), nl}.
	
numCores(A) --> [A], 
	{b_getval(processors, P), last(P, PLast), append(PLast, [A], TAppd), delete(P, PLast, H), append(H, [TAppd], PAppd), b_setval(processors, PAppd)}.
	%{write('CORE > processors: '), b_getval(processors, PP), write(PP), nl},
	%{write('Cores: '), write(A), nl}.

numArea(A) --> [A], 
	{b_getval(processors, P), last(P, PLast), append(PLast, [A], TAppd), delete(P, PLast, H), append(H, [TAppd], PAppd), b_setval(processors, PAppd)}.
	%{write('Area > processors: '), b_getval(processors, PP), write(PP), nl},
	%{write('Area: '), write(A), nl}.

numDollars(A) --> [A], 
	{b_getval(processors, P), last(P, PLast), append(PLast, [A], TAppd), delete(P, PLast, H), append(H, [TAppd], PAppd), b_setval(processors, PAppd)}.
	%{write('$$$  > processors: '), b_getval(processors, PP), write(PP), nl},
	%{write('$$$: '), write(A), nl}.


%%%% read in constraint data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%shared constraint grammar
attribute(core) --> [core], {b_setval(workingConstraintAttr, core)}.  %, {write('core count'), nl}.
attribute(area) --> [area], {b_setval(workingConstraintAttr, area)}.  %, {write('area count'), nl}.
attribute(cost) --> [cost], {b_setval(workingConstraintAttr, cost)}.  %, {write('cost count'), nl}.

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
rangeConstraint(A, LB, UB) --> ([the] | []), attribute(A), ([count] | []), 	  %attribute
					  imperative, ([to] | []), [be],					   	  %imperative
					  [in], [the], ([range] | [interval]), [of], 		   	  %interval
					  lowerBoundValue(LB), [to], upperBoundValue(UB), period. %range


lowerBoundValue(LB) --> [LB], 
	{b_getval(compConstraintsGreater, GreaterConstraints), b_getval(workingConstraintAttr, Attr), LBVal is LB-1, append(GreaterConstraints, [[Attr, LBVal]], GCAppd), b_setval(compConstraintsGreater, GCAppd)}.
	%{write('value1: '), write(LB), nl}.

upperBoundValue(UB) --> [UB], 
	{b_getval(compConstraintsLesser, LesserConstraints), b_getval(workingConstraintAttr, Attr), UBVal is UB+1, append(LesserConstraints, [[Attr, UBVal]], LCAppd), b_setval(compConstraintsLesser, LCAppd)}.
				
	%{write('value2: '), write(UB), nl}.


%%%% determine type of sentence %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%unifies the size of a list with L
size([], 0).
size([_|T], L) :- size(T, TL), L is TL+1.

parseSentence([H|T]) :- H == processor, !, %list outlines a processor?
						write('a processor description: '), write([H|T]), nl, sentence(_, _, _, _, [H|T], []).

parseSentence([H|T]) :- size([H|T], S), S1 is (S-3), nth0(S1,[H|T],To), %setup
						S2 is (S-4), nth0(S2,[H|T],Equal),
						To == to, not(Equal == equal), !,  %list is an interval?
						write('a range constraint:      '), write([H|T]), nl, rangeConstraint(_, _, _, [H|T], []).

parseSentence([H|T]) :- write('a comparison constraint: '), write([H|T]), nl, compConstraint(_, _, _, [H|T], []).


%%%% read loop  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

read_loop :-
	write('>>> Reading new line, '),
	read_line(Line),
	parseSentence(Line),
	
	length(Line, Len),
	(
		Len > 0,
		%write(Line), nl,
		read_loop;
		%Len =< 0,
		write('the last line.'), nl
	).


%%%% constraint satisfaction  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

metricID(core, 1).
metricID(area, 2).
metricID(cost, 3).

%Sums a metric from a list of processor counts (indexed in same order as processors)
%  Metric is 1 for core count, 2 for size, 3 for cost. use metricID above to translate from atom attribute to this metric id int
sumProcessMetric([], [], Metric, 0).
sumProcessMetric([HCount|TCount], [HProcessor|TProcessor], Metric, Sum) :- 
	nth0(Metric, HProcessor, MetricVal),
	Val is MetricVal*HCount,
	sumProcessMetric(TCount, TProcessor, Metric, IncompleteSum),
	Sum is IncompleteSum + Val.


%these iterate through all constraints, checking each to see if satisfied. if all are satisfied, Result is set to true, otherwise false.
satisfiesGreaterConstraints(ProcsCount, [], true).
satisfiesGreaterConstraints(ProcsCount, [Constraint|T], Result) :- satisfiesGC(Constraint, ProcsCount, SatisC), 
																   satisfiesGreaterConstraints(ProcsCount, T, PriorResult),
																   (PriorResult == false -> Result = PriorResult ; Result = SatisC).
satisfiesEqualConstraints(ProcsCount, [], true).
satisfiesEqualConstraints(ProcsCount, [Constraint|T], Result) :- satisfiesEC(Constraint, ProcsCount, SatisC), 
																 satisfiesEqualConstraints(ProcsCount, T, PriorResult),
																 (PriorResult == false -> Result = PriorResult ; Result = SatisC).		
satisfiesLesserConstraints(ProcsCount, [], true).
satisfiesLesserConstraints(ProcsCount, [Constraint|T], Result) :- satisfiesLC(Constraint, ProcsCount, SatisC), 
																  satisfiesLesserConstraints(ProcsCount, T, PriorResult),
																  (PriorResult == false -> Result = PriorResult ; Result = SatisC).																										

%returns true is a constraint ([Attr, Val]) is satisfied by ProcsCount, false otherwise
satisfiesGC([Attr, Val], ProcsCount, Result) :-
	b_getval(processors, Processors),
	metricID(Attr, AttrID),
	sumProcessMetric(ProcsCount, Processors, AttrID, Sum),
	(Sum > Val -> Result = true ; Result = false).

satisfiesEC([Attr, Val], ProcsCount, Result) :-
	b_getval(processors, Processors),
	metricID(Attr, AttrID),
	sumProcessMetric(ProcsCount, Processors, AttrID, Sum),
	(Sum == Val -> Result = true ; Result = false).


satisfiesLC([Attr, Val], ProcsCount, Result) :-
	b_getval(processors, Processors),
	metricID(Attr, AttrID),
	sumProcessMetric(ProcsCount, Processors, AttrID, Sum),
	(Sum < Val -> Result = true ; b_setval(stopIterFlag, true), Result = false).


%prints a list of processor counts with the corresponding processor IDs
printResult([]).
printResult([ProcCount|PCT], [Proc|PT]) :-
	nth0(0, Proc, PID),
	write(PID), write(' = '), write(ProcCount),
	(PCT == [] -> write(';'), nl ; write(', ')),
	printResult(PCT, PT).


%produces lists of all processor count combinations (N^17 of them where N is the number of processors)
% ProcsList should be initialized to size N-1
% ProcsCount should be initialized to [0]
testCombos(ProcsList, ProcsCount, N, NumProcsCounted) :-
	ProcsList == [], !,

	b_getval(compConstraintsGreater, GCs),
	b_getval(compConstraintsEqual, ECs),
	b_getval(compConstraintsLesser, LCs),

	b_getval(processors, Processors),
	b_setval(stopIterFlag, false),

	satisfiesGreaterConstraints(ProcsCount, GCs, GCResult),
	satisfiesEqualConstraints(ProcsCount, ECs, ECResult),
	satisfiesLesserConstraints(ProcsCount, LCs, LCResult),

	(GCResult == true, ECResult == true, LCResult == true -> not(printResult(ProcsCount, Processors)) ; write('')),

	%if an attribute breaks a less than constraint, no reason to try adding more processors
	b_getval(stopIterFlag, StopIterFlag),
	(StopIterFlag == true ->
		M is N+9000, b_setval(stopIterFlag, false)
	;
		write('')
	),
	M is N+1,	

	%iterate processor count
	M < 18,
	nth1(NumProcsCounted, ProcsCount, _, ProcsCountNonTail),
	append(ProcsCountNonTail, [M], IteratedProcsCount),
	testCombos(ProcsList, IteratedProcsCount, M, NumProcsCounted).

testCombos(ProcsList, ProcsCount, N, NumProcsCounted) :-
	N < 17,

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


%%%% you will never guess what this section does %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% (it's main) %%%%%%%%%%%
main :-
	%%% set globals %%%
	b_setval(processors, []), %each entry will be [id, core count, size, cost]

	%attribute buffer
	b_setval(workingConstraintAttr, none),

	%comparison buffer
	b_setval(workingConstraintComp, none),

	%each entry is [attribute, value]
	b_setval(compConstraintsGreater, []), 
	b_setval(compConstraintsEqual, []),
	b_setval(compConstraintsLesser, []),

	
	%%% data read loop %%%
	nl,
	write('%%%%% Reading in data %%%%%'), nl,
	write('%%%%%%%%%%%%%%%%%%%%%%%%%%%'), nl,		
	read_loop,
	
	%%% print data info %%%
	nl, nl,
	write('%%%%%% Data Summary %%%%%%'), nl,
	write('%%%%%%%%%%%%%%%%%%%%%%%%%%'), nl,
	write('Processes:   '), b_getval(processors, Processors),
	write(Processors), nl, nl,
	
	b_getval(compConstraintsGreater, GConstraint),
	write('Constraints:'),nl,
	write(' | X > '), write(GConstraint), nl,
	b_getval(compConstraintsEqual, EConstraint),
	write(' | X = '), write(EConstraint), nl,
	b_getval(compConstraintsLesser, LConstraint),
	write(' | X < '), write(LConstraint), nl,


	%%% Constraint Calculations %%%
	nl, nl,
	write('%%%%% Testing Combos %%%%%'), nl,
	write('%%%%%%%%%%%%%%%%%%%%%%%%%%'), nl,
	nth0(0, Processors, _, AllPButFirst),
	not(testCombos(AllPButFirst, [0], 0, 1)).