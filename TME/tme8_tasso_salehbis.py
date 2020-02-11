import LRC_TME8_definitions_Allen as lrc


def transposeSet(S) :
    result = set()

    for s in S :
        r = lrc.transpose[s]
        result.add(r)
    return result


# print(transposeSet(['e', "=", 'd']))

def symetrieSet(S) :
    result = set()
    for s in S :
        r = lrc.symetrie[s]
        result.add(r)
    return result

# print(symetrieSet(['e', "=", 'd']))

def compose(r1, r2):
    if r1 == '=' :
        return r2
    if r2 == '=' :
        return r1
    if  (r1,r2) in lrc.compositionBase.keys() :
        return lrc.compositionBase[(r1,r2)]
    if  (lrc.transpose[r2],lrc.transpose[r1]) in lrc.compositionBase.keys() :
        return transposeSet(lrc.compositionBase[lrc.transpose[r2],lrc.transpose[r1]])
    if  (lrc.symetrie[r1],lrc.symetrie[r2]) in lrc.compositionBase.keys() :
        return symetrieSet(lrc.compositionBase[lrc.symetrie[r1],lrc.symetrie[r2]])
    return symetrieSet(transposeSet(lrc.compositionBase[lrc.transpose[(lrc.symetrie[r2])],lrc.transpose[(lrc.symetrie[r1])]]))

# print((compose('=','d')))
# print((compose('m','d')))
# print((compose('ot','>')))
# print((compose('>','e')))
# print((compose('ot','m')))


def compositionSet(S1,S2) :
    result = set()
    if S1 == None or S2 == None :
        return set()
    for s1 in S1 :
        for s2 in S2 :
            result.add(compose(s1,s2))
    return result

#Exercice 2 :

class Graphe:
    def __init__(self,noeuds,relations) :
        self.noeuds = noeuds
        self.relations = relations

    def getRelations(self,i,j) :
        if (i,j) in self.relations.keys() :
            return self.relations[(i,j)]
        if (j,i) in self.relations.keys() :
            return transposeSet(self.relations[(j,i)])

    def setRelation(self,i,j,rel) :
        self.relations[(i,j)] = rel

    def copy(self) :
        return Graphe(self.noeuds, self.relations)

def propagation2(g,n1,n2) :
    graphe = g.copy()
    pile = dict()
    pile[(n1,n2)] = graphe.getRelations(n1,n2).copy()
    b1 = False
    b2 = False
    noeuds = graphe.noeuds
    while bool(pile):
        key = pile.keys()[0]
        element = pile.pop(key)
        for n in noeuds :
            if(n != n1 and n != n2):
                r1 = compositionSet(graphe.getRelations(n1,n2), graphe.getRelations(n2,n))
                r1 = r1 & graphe.getRelations(n1,n)
                b1 = True
                r2 = compositionSet(graphe.getRelations(n,n1), graphe.getRelations(n1,n2))
                r2 = r2 & graphe.getRelations(n,n2)
                b2 = True
                if (b2 and r2 == set()):
                    print('Contradiction temporelle')
                    return 0
                if (b1 and r1 == set()) :
                    print('Contradiction temporelle')
                    return 0
                if r1 != graphe.getRelations(n1,n):
                    graphe.setRelation(n1,n, r1)
                    pile[(n1,n)] = r1
                if r2 != graphe.getRelations(n,n2):
                    graphe.setRelation(n,n2,r2)
                    pile[(n,n2)] = r2
                b1 = False
                b2 = False
    return (1, graphe)

def propagation(g,n1,n2) :
    graphe = g.copy()
    pile = set()
    pile.add((n1,n2))
    noeuds = graphe.noeuds
    while len(pile)>0:
        i,j = pile.pop()
        for n in noeuds :
            if(n != i and n != j):
                r1 = compositionSet(graphe.getRelations(i,j), graphe.getRelations(j,n))
                r1 = r1 & graphe.getRelations(i,n)
                r2 = compositionSet(graphe.getRelations(n,i), graphe.getRelations(i,j))
                r2 = r2 & graphe.getRelations(n,j)
                if r1 == set() or r2 == set() :
                    print('Contradiction temporelle')
                    return 0
                if r1 != graphe.getRelations(i,n):
                    graphe.setRelation(i,n, r1)
                    pile.add(i,n)
                if r2 != graphe.getRelations(n,j):
                    graphe.setRelation(n,j,r2)
                    pile.add(n,j)
    return graphe


def ajouter2(graphe, n1, n2, rel) :
    if (n1 not in graphe.noeuds and n2 not in graphe.noeuds) :
        graphe.noeuds.add(n1)
        graphe.noeuds.add(n2)
        graphe.relations.update(rel)
    if (n1 not in graphe.noeuds):
        graphe.noeuds.add(n1)
        graphe.relations.update(rel)
    if (n2 not in graphe.noeuds) :
        graphe.noeuds.add(n2)
        graphe.relations.update(rel)
    if (n1 in graphe.noeuds and n2 in graphe.noeuds):
        res=rel & graphe.getRelations(n1,n2)
        if (res != set()):
            if ((n1, n2) in graphe.relations.keys()):
                graphe.setRelations(n1,n2,rel)
            elif ((n1, n2) in graphe.relations.keys()):
                graphe.setRelations(n1,n2,transposeSet(rel))
            else:
                graphe.setRelations(n1,n2,rel)
    propagation(graphe, n1, n2)


g1 = Graphe({'A','B','C'},{('A','B'): {'<'}, ('A','C'): {'>'}})
ajouter2(g1,'B','C',{'='})
print(g1.noeuds)
print(g1.relations)
print(propagation(g1,'B','C'))
print(g1.noeuds)
print(g1.relations)

 #Comme le resultat est zero, on en deduit que cela n est pas possible
#En effet, ('A','B'): {'<'} signfie que A se termine avant que B ne commence, et ('A','C'): {'>'} signifie que A commence une fois que C est termine.
#Or si B = C, cela est impossible car A ne peut pas se terminer avant que B et C ne commence et une fois qu ils sont termines -> CONTRADICTION

"""
g2 = Graphe({'A','B','C'},{})
g2.setRelation('A','B',{'<'})
g2.setRelation('A','C',{'<'})
ajouter(g2,'B','C',{'='})
print(g2.noeuds)
print(g2.relations)
propagation(g2,'B','C')
print(g2.noeuds)
print(g2.relations)
"""

#Question 5   :

"""g3 = Graphe({'S','L','R'},{})
g3.setRelation('L','S',{'ot', 'mt'})
g3.setRelation('S','R',{'<', '>', 'm', 'mt'})
r, g = propagation(g3,'S','R')
print(r)
print(g.noeuds)
print(g.relations)
"""
