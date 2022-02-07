% Person and Sibling have same parents and are not the same person
siblings(Person, Sibling) :-
	Person \== Sibling,
	parentOf(Parent, Person),
	parentOf(Parent, Sibling).

% Person and Cousin's parents are siblings
firstCousins(Person, Cousin) :-
	parentOf(First, Person),
	parentOf(Second, Cousin),
	siblings(First, Second).

% Person is a descendant of Ancestor
hasAncestor(Person, Ancestor) :-
	parentOf(Ancestor, Person).
hasAncestor(Person, Ancestor) :-
	parentOf(Parent, Person),
	hasAncestor(Parent, Ancestor).

% Person is an ancestor of Desendant
hasDescendant(Person, Descendant) :-
	childOf(Descendant, Person).
hasDescendant(Person, Descendant) :-
	childOf(Child, Person),
	hasDescendant(Child, Descendant).

% Lists all Ancestors of Person
listAncestors(Person, Ancestors) :-
	findall(Parent, hasAncestor(Person, Parent), Ancestors).

% Lists all Descendants of Person
listDescendants(Person, Descendants) :-
	findall(Child, hasDescendant(Person, Child), Descendants).

%Helper function to compare ages and return oldest person (lowest year)
ch_compare(C, Person1, Person2) :- 
	birthYear(Person1, Age1), 
	birthYear(Person2, Age2), 
	compare(C, Age1, Age2).

% Finds eldest child of Person -> Heir
hasHeir(Person, Heir) :-
	monarch(Person),
	findall(C, childOf(C, Person), Children),
	predsort(ch_compare, Children, Sorted), 
	nth1(1, Sorted, Heir).

% Has a child that was a monarch
hasSuccessor(Person, Successor) :-
	childOf(Successor, Person),
	monarch(Successor).

% returns True if Person's original heir was their successor
heirIsSuccessor(Person) :-
	hasHeir(Person, Heir),
	hasSuccessor(Person, Heir).

