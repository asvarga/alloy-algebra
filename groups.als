
open util/ternary

--------

-- TODO: stratify sets of elems better?
abstract sig Elem {}
sig BElem extends Elem {}
sig SElem extends Elem { E: set BElem }
fact { all disj x,y: SElem | x.E != y.E }
sig Group {
	E: set Elem,
	id: E,
	rel: E -> E -> one E
}{
	-- identity
	id.rel in iden and id.(flip12[rel]) in iden
	-- associativity
	all x,y,z: E | rel[rel[x][y]][z] = rel[x][rel[y][z]]
	-- inverse
	(rel.id).E = E and E.(rel.id) = E
}

--------

fun closure(g: Group, gen: set g.E): set g.E {
	(g.id).*(gen.(g.rel))
}
pred generator(g: Group, gen: set g.E) {
	closure[g, gen] = g.E
}
pred gen1(g: Group) {		-- aka cyclic
	some c: g.E | generator[g, c]
}
pred gen2(g: Group) {
	some disj c1,c2: g.E | generator[g, c1+c2]
}
pred gen3(g: Group) {
	some disj c1,c2,c3: g.E | generator[g, c1+c2+c3]
}

--------

pred subgroup(g: Group, n: set g.E) {
	some n
	g.rel[n][n] in n
}
pred normalSub(g: Group, n: set g.E) {
	subgroup[g, n]
	all x: g.E | g.rel[x][n] = g.rel[n][x]
}
pred homomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	all u,v: g.E | f[g.rel[u][v]] = h.rel[f[u]][f[v]]
}
pred homomorphic(g: Group, h: Group) {
	some f: g.E -> one h.E | homomorphism[g, h, f]
}
pred isomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	homomorphism[g, h, f]
	univ.f = h.E	-- onto
	//homomorphism[h, g, ~f]
}
pred isomorphic(g: Group, h: Group) {
	some f: g.E -> one h.E | isomorphism[g, h, f]
}

pred quotient(g: Group, n: set g.E, q: Group) {
	q.E = {s: SElem | some x: g.E | g.rel[x][n] = s.E}	-- q.E is cosets
	some f: g.E -> one q.E {
		//univ.f = q.E		-- onto
		all x: g.E | g.rel[x][n] = f[x].E
		//all j,k: g.E | f[g.rel[j][k]] = q.rel[f[j]][f[k]]
		homomorphism[g, q, f]
	}
}

--------

assert isoTheorem1 {
	all g: Group, h: Group, f: g.E -> one h.E | homomorphism[g, h, f] implies {
		-- 1. The kernel of f is a normal subgroup of G
		normalSub[g, f.(h.id)]
		-- 2. The image of f is a subgroup of H
		subgroup[h, f[g.E]]
		-- 3. The image of f is isomorphic to the quotient group G / ker(f)
	//	all q: Group | quotient[g, f.(h.id), q] implies isomorphic[f[g.E], q]
	}
}
check isoTheorem1

--------

fact useAll { Elem in Group.E }	-- all Elems used

-- make dealing with specific Groups neater
one sig Id extends BElem {}
one sig Gr extends Group {} { id = Id }

run Some { some Gr.E }
run Gen1 { gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen2 { gen2[Gr] and not gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen3 { gen3[Gr] and not gen2[Gr] } for exactly 8 Elem, 1 Group

run Sub { some n: set Gr.E | subgroup[Gr, n] } for exactly 4 Elem, 1 Group
run Norm { some n: set Gr.E | normalSub[Gr, n] } for exactly 4 Elem, 1 Group
run Hom { some g: Group-Gr | homomorphic[g, Gr] } for exactly 4 Elem, 2 Group
run Iso { some g: Group-Gr | isomorphic[g, Gr] } for exactly 4 Elem, 2 Group
run Quo {
	Gr.E = BElem
	some n: set Gr.E, q: Group-Gr {
		q.E = SElem
		normalSub[Gr, n]
		quotient[Gr, n, q]
	}
} for exactly 4 BElem, 2 SElem, 2 Group






