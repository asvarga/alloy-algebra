
module groups

open sets[I] as S
open util/ternary

--------

abstract sig Elem { data: lone univ }	-- allows groups of anything w/o scope explosion
abstract sig Group {
	E: set Elem,
	id: Elem,							-- "E" doesn't work in Alloy*
	add: Elem -> Elem -> Elem,			-- "E -> E -> one E" doesn't work in Alloy*
} {
	-- fix for alloy*
	id in E
	add in E -> E -> one E
	-- identity
	id.add in iden and id.(flip12[add]) in iden
	-- associativity
	all x,y,z: E | add[add[x][y]][z] = add[x][add[y][z]]
	-- inverse
	(add.id).E = E and E.(add.id) = E
}

sig I extends Elem {} { no data }						-- Individuals
sig SI extends Elem {} { some data and data in S/Set }	-- Sets of Individuals
sig GI extends Group {} { E in I }						-- Groups of Individuals
sig GSI extends Group {} { E in SI }					-- Groups of Sets of Individuals

--------

pred eq(g1,g2: Group) { 
	g1.E = g2.E
	g1.id = g2.id
	g1.add = g2.add
}
pred unique { all disj x,y: Group | not eq[x, y] }

--------

fun closure(g: Group, gen: set g.E): set g.E {
	(g.id).*(gen.(g.add))
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
	s.add in g.add
}
pred normalSub(n: Group, g: Group) {
	subgroup[n, g]
	all x: g.E | g.add[x][n.E] = g.add[n.E][x]
}
pred homomorphism(g: Group, h: Group, f: g.E -> one h.E) {
	all u,v: g.E | f[g.add[u][v]] = h.add[f[u]][f[v]]
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

pred kernel(g, h, ker: Group, f: g.E -> one h.E) {
	ker.E = f.(h.id)
}
pred image(g, img: Group, f: g.E -> one Elem) {
	img.E = f[g.E]
	img.id = f[g.id]
}
pred quotient(g, n, q: Group) {
	normalSub[n, g]
	-- q's elements are the cosets of n
	all x: g.E | some s: q.E | s.data.e = g.add[x][n.E]

	-- (xN)(yN) = (xy)N
	all s,t: q.E | some x,y: g.E {
		s.data.e = g.add[x][n.E]
		t.data.e = g.add[y][n.E]
		(q.add[s][t]).data.e = g.add[ g.add[x][y] ][n.E]
	}
}

--------

run {}









