
module iso

open groups as G

--------

sig Set extends Elem { e: set Ind }

pred setEq(s1,s2: Set) { 
	s1.e = s2.e
}
pred disjSets { all disj x,y: Set | not setEq[x, y] }

--------

pred quotient(g: Group, n: set g.E, q: Group) {
	normalSub[g, n]
	-- q's elements are the cosets of n
	//all x: g.E | some s: q.E | s.e = g.add[x][n]

	all x,y: g.E {
		some s,t: q.E {
			s.e = g.add[x][n]
			t.e = g.add[y][n]
			(q.add[s][t]).e = g.add[ g.add[x][y] ][n]
		}
	}

	all s,t: q.E {
		some x,y: g.E {
			s.e = g.add[x][n]
			t.e = g.add[y][n]
			(q.add[s][t]).e = g.add[ g.add[x][y] ][n]
		}
	}

	-- (xN)(yN) = (xy)N
	/*all s,t: q.E | some x,y: g.E {
		s.e = g.add[x][n]
		t.e = g.add[y][n]
		(q.add[s][t]).e = g.add[ g.add[x][y] ][n]
	}*/
}

--------

assert isoTheorem1a {
	disjSets implies
	all g, h, q: Group, f: g.E -> one h.E | {
		homomorphism[g, g.E, h, h.E, f]			-- f is a hom from g -> h
		quotient[g, kernel[g, h, f], q]			-- g/ker = q
	} implies {
		-- The kernel of f is a normal subgroup of G
		normalSub[g, kernel[g, h, f]]
	}
}
check isoTheorem1a for 0 but exactly 3 Group, 6 Ind, 6 Set


assert isoTheorem1b {
	disjSets implies
	all g, h, q: Group, f: g.E -> one h.E | {
		homomorphism[g, g.E, h, h.E, f]			-- f is a hom from g -> h
		quotient[g, kernel[g, h, f], q]			-- g/ker = q
	} implies {
		-- The image of f is a subgroup of H
		subgroup[h, image[g, h, f]]
	}
}
check isoTheorem1b for 0 but exactly 3 Group, 4 Ind, 4 Set


assert isoTheorem1c {
	disjSets implies
	all g, h, q: Group, f: g.E -> one h.E | {
		homomorphism[g, g.E, h, h.E, f]			-- f is a hom from g -> h
		quotient[g, kernel[g, h, f], q]			-- g/ker = q
	} implies {
		-- The image of f is isomorphic to the quotient group G / ker(f)
		isomorphic[h, image[g, h, f], q, q.E]
	}
}
check isoTheorem1c for 0 but exactly 3 Group, 4 Ind, 4 Set




