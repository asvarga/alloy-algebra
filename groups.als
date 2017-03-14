
open util/ternary

--------

sig Elem {}
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

pred subgroup(g: Group, h: Group) {
	g.E in h.E
	g.rel in h.rel
}
pred normalSub(g: Group, h: Group) {
	subgroup[g, h]
	all x: g.E | x.(h.rel) = x.(flip12[h.rel])
}
pred homomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	all u,v: g.E | f[g.rel[u][v]] = g.rel[f[u]][f[v]]
}
pred homomorphic(g: Group, h: Group) {
	some f: g.E -> one h.E | homomorphism[g, h, f]
}
pred isomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	-- TODO: optimize this?
	homomorphism[g, h, f]
	homomorphism[h, g, ~f]
}
pred isomorphic(g: Group, h: Group) {
	some f: g.E -> one h.E | isomorphism[g, h, f]
}

--------

fact useAll { Group.E = Elem }	-- all Elems used

-- make dealing with specific Groups neater
one sig Id extends Elem {}
one sig Gr extends Group {} { id = Id }

run Some { some Gr.E }
run Gen1 { gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen2 { gen2[Gr] and not gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen3 { gen3[Gr] and not gen2[Gr] } for exactly 8 Elem, 1 Group
run Sub { some g: Group-Gr | normalSub[g, Gr] } for exactly 4 Elem, 2 Group
run Hom { some g: Group-Gr | homomorphic[g, Gr] } for exactly 4 Elem, 2 Group









