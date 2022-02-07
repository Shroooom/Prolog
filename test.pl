schedule(monday, science).
schedule(tuesday, science).
schedule(wednesday, math).
schedule(monday, math).

difficulty(science, easy).
difficulty(math, hard).

classinformation(Day, Class, Diff) :-
    schedule(Day, Class),
    difficulty(Class, Diff).
