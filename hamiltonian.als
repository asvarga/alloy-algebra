
open groups as G

--------

one sig G extends Group {}			-- a group
one sig g1,g2 extends Elem {}		-- generators of that group
fact { allElemsUsed }

--------

pred hamPath(G: Group, gs: set Elem, next: Elem one->one Elem) {
	-- so all but the id need a predecessor ("next.e" is e's predecessor)
	all e: Elem-G.id | some g: gs | G.add[next.e][g] = e
	G.id.*next = Elem
}
pred hasHamPath(G: Group, gs: set Elem) {
	some next: Elem one->one Elem | hamCycle[G, gs, next]
}

pred hamCycle(G: Group, gs: set Elem, next: Elem one->one Elem) {
	hamPath[G, gs, next]						-- same but also...
	some g: gs | G.add[next.(G.id)][g] = G.id	-- id has a predecessor
}
pred hasHamCycle(G: Group, gs: set Elem) {
	some next: Elem one->one Elem | hamCycle[G, gs, next]
}

--------

run {
	generator[G, g1+g2]
	not gen1[G]

	hasHamCycle[G, g1+g2]
	// some next: Elem one->one Elem | hamPath[G, g1+g2, next] and not hamCycle[G, g1+g2, next]

} for 0 but exactly 1 Group, exactly 6 Elem









