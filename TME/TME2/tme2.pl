/*
r(a,b).
q(X,X).
q(X,Z) :- r(X,Y),q(Y,Z).
*/

/*
reviser(X) :- serieux(X).
devoir(X) :- consciencieux(X).
reussir(X) :- reviser(X).
serieux(X) :- devoir(X).
consciencieux(zoe).
consciencieux(pascal).
*/

/*
pere(homer,bart).
pere(homer,lisa).
pere(homer,maggie).
pere(abraham,homer).
pere(clancy,marge).
mere(marge,bart).
mere(marge,lisa).
mere(marge,maggie).
parent(X,Y) :- pere(X,Y).
parent(X,Y) :- mere(X,Y).
parents(X,Y,Z) :- pere(X,Z), mere(Y,Z).
grandPere(X,Y) :- pere(X,Z) ,pere(Z,Y).
grandPere(X,Y) :- pere(X,Z) ,mere(Z,Y).
frereOuSoeur(X,Y) :- pere(Z,X), pere(Z,Y), mere(T,X), mere(T,Y).
ancetre(X,Y) :- pere(X,Y).
ancetre(X,Y) :- mere(X,Y).
ancetre(X,Y) :- grandPere(X,Y).		    
*/

et(0,0,0).
et(0,1,0).
et(1,0,0).
et(1,1,1).

ou(0,0,0).
ou(0,1,1).
ou(1,0,1).
ou(1,1,1).

non(0,1).
non(1,0).

nand(0,0,1).
nand(0,1,1).
nand(1,0,1).
nand(1,1,0).

xor(0,0,0).
xor(0,1,1).
xor(1,0,1).
xor(1,1,0).

circuit(0,0,1).
circuit(0,1,1).
circuit(1,0,0).
circuit(1,1,1).

circuit2(X,Y,Z) :- nand(X,Y,T1), non(X,T2), xor(T1,T2,T3), non(T3,Z).
