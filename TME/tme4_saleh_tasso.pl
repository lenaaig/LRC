/* Sarah Saleh
Lenaïg Tasso */

/*Exercice 1*/

subs(chat, felin).
subs(lion, felin).
subs(chien, canide).
subs(canide, chien).
subs(souris, mam).
subs(felin, mam).
subs(canide, mam).
subs(mam, animal).
subs(canari, animal).
subs(animal, etreVivant).
subs(and(animal, plante), nothing).

subs(pet, all(aMaitre,animal)). /*Un animal qui a un maitre est un animal de compagnie*/
subs(pet, some(aMaitre)).
subs(some(aMaitre),humain).
subs(chihuahua, chien).
subs(chihuahua, pet).

subs(animal, some(mange)). /*Tout animal se nourrit*/
subs(and(some(mange), all(mange,nothing)),nothing).

subs(lion, carnivoreExc).
subs(carnivoreExc,predateur).


subs(A,B) :- equiv(A,B).
subs(B,A) :- equiv(A,B).


equiv(carnivoreExc,all(mange,animal)).
equiv(herbivoreExc,all(mange,plante)).

inst(felix, chat).
inst(pierre,humain).
inst(princesse,chihuahua).
inst(marie, humain).
inst(jerry, souris).
inst(titi, canari).

instR(felix, aMaitre, pierre).
instR(princesse, aMaitre, marie).
instR(felix, mange, titi).
instR(felix,mange,jerry).

/*Exercice 2*/

/*1. Ces règles traduisent la transitivité.*/

subsS1(C,C).
subsS1(C,D) :- subs(C,D), C\==D.
subsS1(C,D) :- subs(C,E), subsS1(E,D).

/*2.

subsS1(canari, animal).
true ;

subsS1(chat, etreVivant).
true .

3.

subsS1(chien, souris).
   Call: (7) subsS1(chien, souris) ? creep
   Call: (8) subs(chien, souris) ? creep
   Fail: (8) subs(chien, souris) ? creep
   Redo: (7) subsS1(chien, souris) ? creep
   Call: (8) subs(chien, _G1305) ? creep
   Exit: (8) subs(chien, canide) ? creep
   Call: (8) subsS1(canide, souris) ? creep
   Call: (9) subs(canide, souris) ? creep
   Fail: (9) subs(canide, souris) ? creep
   Redo: (8) subsS1(canide, souris) ? creep
   Call: (9) subs(canide, _G1305) ? creep
   Exit: (9) subs(canide, chien) ? creep
   Call: (9) subsS1(chien, souris) ? creep
   Call: (10) subs(chien, souris) ? creep
   Fail: (10) subs(chien, souris) ? creep
   Redo: (9) subsS1(chien, souris) ? creep
   Call: (10) subs(chien, _G1305) ? creep
   Exit: (10) subs(chien, canide) ? creep
   Call: (10) subsS1(canide, souris) ? creep
   Call: (11) subs(canide, souris) ? creep
   Fail: (11) subs(canide, souris) ? creep
   Redo: (10) subsS1(canide, souris) ? creep

Cette requete part en boucle infinie car chien subsume canide et canide subsume chien.*/

/*4.*/

subsS(C,D) :- subsS(C,D,[C]).
subsS(C,C,_).
subsS(C,D,_) :- subs(C,D), C\==D.
subsS(C,D,L) :- subs(C,E),not(member(E,L)), subsS(E,D,[E|L]), E\==D.

/*
subsS(canari, animal).
true 

subsS(chat, etreVivant).
true .

subsS(chien, canide).
true .

subsS(chien,chien).
true .

5.
subsS(souris, some(mange)).
true .

6.
subsS(chat,humain).
false.

subsS(chien, souris).
false.

7. La requete subsS(chat,X) devrait renvoyer X=chat, felin, animal, mam, etreVivant et some(mange).
La requete subsS(X,mam) devrait renvoyer X=felin,souris, canide,chien,chat ,lion, chihuahua.

subsS(chat,X).
X = chat ;
X = felin ;
X = mam ;
X = animal ;
X = etreVivant ;
X = some(mange) ;
false.


subsS(X,mam) :
X = mam ;
X = souris ;
X = felin ;
X = canide ;
X = chat ;
X = lion ;
X = chien ;
X = chihuahua ;
false.

8.

9.
Avant les règles :
subsS1(lion,all(mange,animal)).
false.

Après les règles :
subsS1(lion,all(mange,animal)).
true.

10.
On a plus interêt à dériver subs que subsS car les verifications faites par subsS sont plus lourdes, de plus subsS appelle subs.
Non, ça ne permet pas de répondre à toute requête atomique, elle ne prend pas en compte l'intersection par exemple. 


Exercice 3

*/
subsS(C,and(D1,D2),L) :- D1\=D2,subsS(C,D1,L),subsS(C,D2,L).
subsS(C,D,L) :- subs(and(D1,D2),D),E=and(D1,D2),not(member(E,L)),subsS(C,E,[E|L]),E\==C.
subsS(and(C,C), D, L) :- nonvar(C), subsS(C,D,[C|L]).
subsS(and(C1,C2), D, L) :- C1\=C2, subsS(C1, D, [C1 |L]).
subsS(and(C1,C2), D, L) :- C1\=C2, subsS(C2, D, [C2 |L]).
subsS(and(C1, C2),D,L) :- subs(C1, E1),E=and(E1,C2),not(member(E,L)),subsS(E,D,[E|L]),E\==D.
subsS(and(C1, C2),D,L) :- Cinv=and(C2,C1), not(member(Cinv, L)), subsS(Cinv,D,[Cinv|L]).

/* 
subsS(chihuahua, and(mam,some(aMaitre))).
true 

subsS(and(chien,some(aMaitre)),pet).
false.

subsS(chihuahua, and(pet,chien)).
true 


2.
subsS(C,and(D1,D2),L) :- D1\=D2,subsS(C,D1,L),subsS(C,D2,L).
Cette règle correspond au fait que si C est compris dans l'intersection de D1 et D2 alors C est compris dans D1 et C est compris dans D2.

subsS(C,D,L) :- subs(and(D1,D2),D),E=and(D1,D2),not(member(E,L)),subsS(C,E,[E|L]),E\==C.
Cette règle correspond au cas où C subsume D lorsque l'intersection de D1 et D2 subsume D et qu'elle n'est pas encore dans la liste des concepts utilisés dans la preuve de la subsomption.

subsS(and(C,C), D, L) :- nonvar(C), subsS(C,D,[C|L]).
Cette règle corespond au cas où on veut savoir si l'intersection de C avec lui même va etre subsumé par D, ce qui est vrai si C n'est pas une variable et que C est subsumé par D.

subsS(and(C1,C2), D, L) :- C1\=C2, subsS(C1, D, [C1 |L]).
Cette règle correspond au cas où on demande si une intersection de C1 et C2 est subsumé par un concept D, ce qui est vrai si C1 est différent de C2 et C1 est subsumé par D.

subsS(and(C1,C2), D, L) :- C1\=C2, subsS(C2, D, [C2 |L]).
Cette règle correspond au cas où on demande si une intersection de C1 et C2 est subsumé par un concept D, ce qui est vrai si C1 est différent de C2 et C2 est subsumé par D.
Ces deux dernières règles indiquent qu'une intersection est subsumée par un concept si un de ses éléments est subsumé par le concept en question.

subsS(and(C1, C2),D,L) :- subs(C1, E1),E=and(E1,C2),not(member(E,L)),subsS(E,D,[E|L]),E\==D.
Cette règle correspond au cas où on demande si une intersection de C1 et C2 est subsumée par un concept D, ce qui est vrai si C1 est subsumé par un concept E1, et que l'intersection de ce concept E1 avec le concept C2 est subsumée par D.

subsS(and(C1, C2),D,L) :- Cinv=and(C2,C1), not(member(Cinv, L)), subsS(Cinv,D,[Cinv|L]).
Cette règle correspond au cas où on demande si une intersection de C1 et C2 est subsumée par un concept D, c'est vrai si l'intersection de C2 et C1 est subsumée par D. On rend le and symétrique.

3.
Oui, ces règles suffisent pour gérer toute requête ne contenant que des concepts atomiques ou avec intersection.


Exercice 4

1.*/
subsS(all(R,C),all(R,D),L) :- subsS(C,D,L).

/*
2.
subsS(lion,all(mange,etreVivant)).
true .

subsS(all(mange,canari),carnivoreExc).
false.

3. 
subsS(and(carnivoreExc,herbivoreExc),all(mange,nothing)).
subsS(and(and(carnivoreExc,herbivoreExc),animal),nothing).*/

subsS(and(C1,C2),all(R,D),L) :- subsS(and(C1,C2),D,L).


/*
4.
