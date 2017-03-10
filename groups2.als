

sig Elem {
	rel: Elem -> one Elem
}{
	-- total
	rel.Elem = Elem
}
one sig Id extends Elem {}

fact {
	-- identity
	all x: Elem | rel[Id][x] = x and rel[x][Id] = x
	-- associativity
	all x,y,z: Elem | rel[rel[x][y]][z] = rel[x][rel[y][z]]
	-- inverse
	all x: Elem | some inv: Elem | rel[x][inv] = Id and rel[inv][x] = Id
}
run {} for exactly 6 Elem

--------

fun closure(gen: set Elem): set Elem {
	Id.*(gen.rel)
}
pred generator(gen: set Elem) {
	closure[gen] = Elem
}
pred cyclic {
	some c: Elem | generator[c]
}
run cyclic for exactly 6 Elem

run D6 {
	some disj s,r: Elem-Id {
		rel[s][s] = Id
		rel[r][rel[r][r]] = Id
	}
} for exactly 6 Elem


