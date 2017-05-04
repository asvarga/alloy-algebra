
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

pred subgroup(s: Group, g: Group) {
	s.E in g.E
	s.rel in g.rel
}
pred normalSub(n: Group, g: Group) {
	subgroup[n, g]
	all x: g.E | g.rel[x][n.E] = g.rel[n.E][x]
}
pred homomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	all u,v: g.E | f[g.rel[u][v]] = h.rel[f[u]][f[v]]
}
pred homomorphic(g: Group, h: Group) {
	some f: g.E -> one h.E | homomorphism[g, h, f]
}
pred isomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	homomorphism[g, h, f]
	f in (g.E one->one h.E)			-- bijection
}
pred isomorphic(g: Group, h: Group) {
	some f: g.E -> one h.E | isomorphism[g, h, f]
}

--------

pred quotient(g: Group, n: Group, q: Group) {
	normalSub[n, g]
	-- q's elements are the cosets of n
	all x: g.E | some s: q.E | s.E = g.rel[x][n.E]
	//all s: q.E | some x: g.E | s.E = g.rel[x][n.E]	-- this is expressed below

	-- (xN)(yN) = (xy)N
	all s,t: q.E | some x,y: g.E {
		s.E = g.rel[x][n.E]
		t.E = g.rel[y][n.E]
		(q.rel[s][t]).E = g.rel[ g.rel[x][y] ][n.E]
	}
}

--------

assert isoTheorem1 {
	all g, h, ker, img, q: Group, f: g.E -> one h.E | {
		homomorphism[g, h, f]	-- f is an iso from g -> h
		ker.E = f.(h.id)		-- ker is the kernel of f
		img.E = f[g.E]			-- img is the image of f
		quotient[g, ker, q]		-- q = g/ker
	} implies {
		-- 1. The kernel of f is a normal subgroup of G
		normalSub[ker, g]
		-- 2. The image of f is a subgroup of H
		subgroup[img, h]
		-- 3. The image of f is isomorphic to the quotient group G / ker(f)
		isomorphic[img, q]
		-- In particular, if f is surjective then H is isomorphic to G / ker(f)
		//h.E in (g.E).f implies isomorphic[h, q]
	}
}
check isoTheorem1

--------

fact neat { 
	Elem in Group.E				-- all Elems used
	all g: Group | some g.E		-- no empty groups
}

-- make dealing with specific Groups neater
one sig Id extends BElem {}
one sig Gr extends Group {} { id = Id }

run Some { some Gr.E }
run Gen1 { gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen2 { gen2[Gr] and not gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen3 { gen3[Gr] and not gen2[Gr] } for exactly 8 Elem, 1 Group

run Sub { some s: Group-Gr | subgroup[s, Gr] } for exactly 4 BElem, 0 SElem, 2 Group
run Norm { some n: Group-Gr | normalSub[n, Gr] } for exactly 4 BElem, 0 SElem, 2 Group
run Hom { some h: Group-Gr | homomorphic[Gr, h] } for exactly 2 BElem, 0 SElem, 2 Group
run Iso { some g: Group-Gr | isomorphic[Gr, g] } for exactly 4 BElem, 0 SElem, 2 Group
run Quo {
	Gr.E = BElem
	some n,q: Group-Gr | quotient[Gr, n, q]
} for exactly 6 BElem, 2 SElem, 3 Group






