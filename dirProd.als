
module dirProd

open groups as G

--------

sig PoG { A,B: Group }						-- pairs of groups
sig Pair extends Elem { a,b: Ind }			-- elems that are pairs
sig GoP extends Group {} { E in Pair }		-- groups of pairs

--------

pred test(pog: PoG, gop: GoP, a1,a2: pog.A.E, b1,b2: pog.B.E, p1,p2: gop.E) {
	p1.a = a1
	p1.b = b1
	p2.a = a2
	p2.b = b2
	gop.add[p1][p2].a = pog.A.add[a1][a2]
	gop.add[p1][p2].b = pog.B.add[b1][b2]
}

pred gprod(pog: PoG, gop: GoP) {
	all a1,a2: pog.A.E, b1,b2: pog.B.E {
		some p1,p2: gop.E | test[pog, gop, a1, a2, b1, b2, p1, p2]
	}
	all p1,p2: gop.E {
		some a1,a2: pog.A.E, b1,b2: pog.B.E | test[pog, gop, a1, a2, b1, b2, p1, p2]
	}	
}

--------

one sig ThePoG extends PoG {} {
	not A = B
	some A.E - A.id
	some B.E - B.id
}
one sig TheGoP extends GoP {}

run { gprod[ThePoG, TheGoP] } for 0 but exactly 1 ThePoG, exactly 3 Group, exactly 4 Pair, exactly 4 Ind
