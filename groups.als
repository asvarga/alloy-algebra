
module groups

open util/ternary

--------

abstract sig Elem {}
sig Ind extends Elem {}
sig Group {
	E: set Elem,
	id: Elem,						-- "E" doesn't work in Alloy*
	add: Elem -> Elem -> Elem,		-- "E -> E -> one E" doesn't work in Alloy*
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

--------

pred allElemsUsed { Elem = Group.E }

pred groupEq(g1,g2: Group) { 
	g1.E = g2.E
	g1.id = g2.id
	g1.add = g2.add
}
pred disjGroups { all disj x,y: Group | not groupEq[x, y] }

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

/*pred subgroup(s, g: Group) {
	s.E in g.E
	s.add in g.add
}
pred normalSub(n, g: Group) {
	subgroup[n, g]
	all x: g.E | g.add[x][n.E] = g.add[n.E][x]
}*/

pred subgroup(g: Group, s: set g.E) {
	g.add[s][s] in s		-- s is closed in g
}
pred normalSub(g: Group, n: set g.E) {
	subgroup[g, n]
	// g.add[g.E][n] = g.add[n][g.E]		-- gn = ng
	all x: g.E | g.add[x][n] = g.add[n][x]
}

--------

pred homomorphism(g: Group, gs: set g.E, h: Group, hs: set h.E, f: gs -> one hs) {
	all u,v: gs | f[g.add[u][v]] = h.add[f[u]][f[v]]
}
pred homomorphic(g: Group, gs: set g.E, h: Group, hs: set h.E) {
	some f: gs -> one hs | homomorphism[g, gs, h, hs, f]
}
pred isomorphism(g: Group, gs: set g.E, h: Group, hs: set h.E, f: gs one->one hs) {
	homomorphism[g, gs, h, hs, f]
	// f in (gs one->one hs)			-- bijection
}
pred isomorphic(g: Group, gs: set g.E, h: Group, hs: set h.E) {
	some f: gs one->one hs | isomorphism[g, gs, h, hs, f]
}

--------

/*pred kernel(g, h, ker: Group, f: g.E -> one h.E) {
	ker.E = f.(h.id)
}
pred image(g, img: Group, f: g.E -> one Elem) {
	img.E = f[g.E]
	img.id = f[g.id]
}*/

fun kernel(g, h: Group, f: g.E -> one h.E): set g.E {
	f.(h.id)
}
fun image(g, h: Group, f: g.E -> one h.E): set h.E {
	f[g.E]
}

--------

pred product(g, s, t, st: Group) {
	s.E in g.E
	t.E in g.E
	st.E = g.add[s.E][t.E]
}
pred intersection(g, s, t, st: Group) {
	s.E in g.E
	t.E in g.E
	st.E = s.E & t.E
}

--------

run {}






