:- [windsor, relations].

main :-
	write("Now running some queries for Part 1..."),
	nl,
	(
		write('Edward VIII and George VI are siblings... '),
		(
			siblings(edward_viii, george_vi), write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('Anne Princess-Royal and Lady Sarah are first cousins... '),
		(
			firstCousins(princess_anne_royal, lady_sarah), write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('Victoria is an ancestor of Prince Charles... '),
		(
			hasAncestor(prince_charles, victoria), write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('Mary of Teck is not a descendant of Edward VII... '),
		(
			\+(hasDescendant(edward_vii, mary_of_teck)),
			write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('George V\'s ancestors are Victoria, Prince Albert, Edward VII, and Alexandra... '),
		(
			listAncestors(george_v, A),
			member(victoria, A), member(prince_albert, A),
			member(edward_vii, A), member(alexandra, A),
			length(A, 4),
			write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('George VI\'s descendants are Elizabeth II, Princess Margaret, David Earl-of-Snowden, Lady Sarah, Prince Charles, Anne Princess-Royal, Prince Andrew, and Prince Edward... '),
		(
			listDescendants(george_vi, D),
			member(elizabeth_ii, D), member(princess_margaret, D),
			member(david_earl_of_snowdon, D), member(lady_sarah, D),
			member(prince_charles, D), member(princess_anne_royal, D),
			member(prince_andrew, D), member(prince_edward, D),
			length(D, 8),
			write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('Edward VIII is the heir to George V... '),
		(
			hasHeir(george_v, edward_viii), write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	), nl,
	(
		write('Both Edward VIII and George VI are successors to George V... '),
		(
			hasSuccessor(george_v, edward_viii),
			hasSuccessor(george_v, george_vi),
			write('True.');
			write('False... (but it should be true, check your code)')
		),
		nl
	),
	halt.

