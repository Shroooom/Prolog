spouse(Person, Spouse) :-
	married(Person, Spouse);
	married(Spouse, Person).

childOf(Child, Parent) :-
	parentOf(Parent, Child).

parentOf(victoria, empress_victoria).
parentOf(victoria, edward_vii).
parentOf(victoria, princess_alice).
parentOf(victoria, prince_alfred).
parentOf(victoria, princess_helena).
parentOf(victoria, princess_louise).
parentOf(victoria, prince_arthur).
parentOf(victoria, prince_leopold).
parentOf(victoria, princess_beatrice).
parentOf(prince_albert, empress_victoria).
parentOf(prince_albert, edward_vii).
parentOf(prince_albert, princess_alice).
parentOf(prince_albert, prince_alfred).
parentOf(prince_albert, princess_helena).
parentOf(prince_albert, princess_louise).
parentOf(prince_albert, prince_arthur).
parentOf(prince_albert, prince_leopold).
parentOf(prince_albert, princess_beatrice).

parentOf(edward_vii, prince_albert_victor).
parentOf(edward_vii, george_v).
parentOf(edward_vii, princess_louise_royal).
parentOf(edward_vii, princess_victoria).
parentOf(edward_vii, princess_maud).
parentOf(alexandra, prince_albert_victor).
parentOf(alexandra, george_v).
parentOf(alexandra, princess_louise_royal).
parentOf(alexandra, princess_victoria).
parentOf(alexandra, princess_maud).

parentOf(george_v, edward_viii).
parentOf(george_v, george_vi).
parentOf(george_v, princess_mary_royal).
parentOf(george_v, prince_henry).
parentOf(george_v, prince_george).
parentOf(george_v, prince_john).
parentOf(mary_of_teck, edward_viii).
parentOf(mary_of_teck, george_vi).
parentOf(mary_of_teck, princess_mary_royal).
parentOf(mary_of_teck, prince_henry).
parentOf(mary_of_teck, prince_george).
parentOf(mary_of_teck, prince_john).

parentOf(george_vi, elizabeth_ii).
parentOf(george_vi, princess_margaret).
parentOf(elizabeth_bowes_lyon, elizabeth_ii).
parentOf(elizabeth_bowes_lyon, princess_margaret).

parentOf(elizabeth_ii, prince_charles).
parentOf(elizabeth_ii, princess_anne_royal).
parentOf(elizabeth_ii, prince_andrew).
parentOf(elizabeth_ii, prince_edward).
parentOf(prince_philip, prince_charles).
parentOf(prince_philip, princess_anne_royal).
parentOf(prince_philip, prince_andrew).
parentOf(prince_philip, prince_edward).

parentOf(princess_margaret, david_earl_of_snowdon).
parentOf(princess_margaret, lady_sarah).
parentOf(antony_earl_of_snowdon, david_earl_of_snowdon).
parentOf(antony_earl_of_snowdon, lady_sarah).

married(victoria, prince_albert).
married(alexandra, edward_vii).
married(mary_of_teck, george_v).
married(elizabeth_bowes_lyon, george_vi).
married(elizabeth_ii, prince_philip).
married(princess_margaret, antony_earl_of_snowdon).

birthYear(victoria, 1819).
birthYear(prince_albert, 1819).

birthYear(empress_victoria, 1840).
birthYear(edward_vii, 1841).
birthYear(princess_alice, 1843).
birthYear(prince_alfred, 1844).
birthYear(princess_helena, 1846).
birthYear(princess_louise, 1848).
birthYear(prince_arthur, 1850).
birthYear(prince_leopold, 1853).
birthYear(princess_beatrice, 1857).
birthYear(alexandra, 1844).

birthYear(prince_albert_victor, 1864).
birthYear(george_v, 1865).
birthYear(princess_louise_royal, 1867).
birthYear(princess_victoria, 1868).
birthYear(princess_maud, 1869).
birthYear(mary_of_teck, 1867).

birthYear(edward_viii, 1894).
birthYear(george_vi, 1895).
birthYear(princess_mary_royal, 1897).
birthYear(prince_henry, 1900).
birthYear(prince_george, 1902).
birthYear(prince_john, 1905).
birthYear(elizabeth_bowes_lyon, 1900).

birthYear(elizabeth_ii, 1926).
birthYear(princess_margaret, 1930).
birthYear(prince_philip, 1921).
birthYear(antony_earl_of_snowdon, 1930).

birthYear(prince_charles, 1948).
birthYear(princess_anne_royal, 1950).
birthYear(prince_andrew, 1960).
birthYear(prince_edward, 1964).
birthYear(david_earl_of_snowdon, 1961).
birthYear(lady_sarah, 1964).

monarch(victoria).
monarch(edward_vii).
monarch(george_v).
monarch(edward_viii).
monarch(george_vi).
monarch(elizabeth_ii).

