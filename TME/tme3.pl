/* Exercice 1

[a, [b, c], d] = [X].
false.

Faux car [X] est une liste d'un seul élément.


[a, [b, c], d] = [X, Y, Z].
X = a,
Y = [b, c],
Z = d.

Vrai car 3 éléments dans la liste


[a, [b, c], d] = [a | L].
L = [[b, c], d].

Vrai car la liste commence par a et est suivi d'une suite de termes.

[a, [b, c], d] = [X, Y].
false.

Faux car il n'y a pas exactement 2 éléments dans la liste.

[a, [b, c], d] = [X | Y].
X = a,
Y = [[b, c], d].

Vrai car commence par un terme et fini par des termes.

[a, [b, c], d] = [a,b | L].
false.

Faux car ne commence pas par a,b.

[a, b, [c, d]] = [a,b | L].
L = [[c, d]].

Vrai car commence par a et b et fini par 1 liste.

[a, b ,c, d | L1] = [a,b | L2].
L2 = [c, d|L1].

Vrai car commence par a,b et fini par une suite de termes.

*/

/* Exercice 2*/

concatene([ X | R ],L2,[ X | Lres]) :- concatene(R, L2, Lres).
concatene([], L2, L2). 
/*[trace]  ?- concatene([a,b],[c,d],L).
   Call: (7) concatene([a, b], [c, d], _G3567) ? creep
   Call: (8) concatene([b], [c, d], _G3649) ? creep
   Call: (9) concatene([], [c, d], _G3652) ? creep
   Exit: (9) concatene([], [c, d], [c, d]) ? creep
   Exit: (8) concatene([b], [c, d], [b, c, d]) ? creep
   Exit: (7) concatene([a, b], [c, d], [a, b, c, d]) ? creep
L = [a, b, c, d].


[trace]  ?- concatene(L1, L2, [a,b,c,d]).
   Call: (7) concatene(_G3565, _G3566, [a, b, c, d]) ? creep
   Call: (8) concatene(_G3664, _G3566, [b, c, d]) ? creep
   Call: (9) concatene(_G3667, _G3566, [c, d]) ? creep
   Call: (10) concatene(_G3670, _G3566, [d]) ? creep
   Call: (11) concatene(_G3673, _G3566, []) ? creep
   Exit: (11) concatene([], [], []) ? creep
   Exit: (10) concatene([d], [], [d]) ? creep
   Exit: (9) concatene([c, d], [], [c, d]) ? creep
   Exit: (8) concatene([b, c, d], [], [b, c, d]) ? creep
   Exit: (7) concatene([a, b, c, d], [], [a, b, c, d]) ? creep
L1 = [a, b, c, d],
L2 = [] ;
   Redo: (10) concatene(_G3670, _G3566, [d]) ? creep
   Exit: (10) concatene([], [d], [d]) ? creep
   Exit: (9) concatene([c], [d], [c, d]) ? creep
   Exit: (8) concatene([b, c], [d], [b, c, d]) ? creep
   Exit: (7) concatene([a, b, c], [d], [a, b, c, d]) ? creep
L1 = [a, b, c],
L2 = [d] ;
   Redo: (9) concatene(_G3667, _G3566, [c, d]) ? creep
   Exit: (9) concatene([], [c, d], [c, d]) ? creep
   Exit: (8) concatene([b], [c, d], [b, c, d]) ? creep
   Exit: (7) concatene([a, b], [c, d], [a, b, c, d]) ? creep
L1 = [a, b],
L2 = [c, d] ;
   Redo: (8) concatene(_G3664, _G3566, [b, c, d]) ? creep
   Exit: (8) concatene([], [b, c, d], [b, c, d]) ? creep
   Exit: (7) concatene([a], [b, c, d], [a, b, c, d]) ? creep
L1 = [a],
L2 = [b, c, d] ;
   Redo: (7) concatene(_G3565, _G3566, [a, b, c, d]) ? creep
   Exit: (7) concatene([], [a, b, c, d], [a, b, c, d]) ? creep
L1 = [],
L2 = [a, b, c, d].


puissant

**/

inverse([T | L], Lres) :- inverse(L, LI), concatene(LI,[T], Lres) .
inverse([], []).


supprime(X,a,L) :- concatene(
