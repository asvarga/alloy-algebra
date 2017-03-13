
open util/ternary

--------

sig Elem {}
sig Group {
	E: set Elem,
	id: one E,
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

fun closure(g: one Group, gen: set g.E): set g.E {
	(g.id).*(gen.(g.rel))
}
pred generator(g: one Group, gen: set g.E) {
	closure[g, gen] = g.E
}
pred gen1(g: one Group) {		-- aka cyclic
	some c: g.E | generator[g, c]
}
pred gen2(g: one Group) {
	some disj c1,c2: g.E | generator[g, c1+c2]
}
pred gen3(g: one Group) {
	some disj c1,c2,c3: g.E | generator[g, c1+c2+c3]
}

--------

fact useAll { Group.E = Elem }	-- all Elems used

-- make dealing with 1 Group neater
one sig Id extends Elem {}
one sig Gr extends Group {} { id = Id }

run Some { some Gr.E }
run Gen1 { gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen2 { gen2[Gr] and not gen1[Gr] } for exactly 6 Elem, 1 Group
run Gen3 { gen3[Gr] and not gen2[Gr] } for exactly 8 Elem, 1 Group











