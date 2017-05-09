
module quotient

open groups as G

--------

sig Set extends Elem { e: set Ind }

pred setEq(s1,s2: Set) { 
	s1.e = s2.e
}
pred disjSets { all disj x,y: Set | not setEq[x, y] }

--------

pred quotient(g, n, q: Group) {
	normalSub[n, g]
	-- q's elements are the cosets of n
	all x: g.E | some s: q.E | s.e = g.add[x][n.E]

	-- (xN)(yN) = (xy)N
	all s,t: q.E | some x,y: g.E {
		s.e = g.add[x][n.E]
		t.e = g.add[y][n.E]
		(q.add[s][t]).e = g.add[ g.add[x][y] ][n.E]
	}
}

run {}

--------

pred isoTheorem1 {
	disjSets implies
	all g, h, ker, img, q: Group, f: g.E -> one h.E | {
		homomorphism[g, h, f]	-- f is an iso from g -> h
		kernel[g, h, ker, f]	-- ker is the kernel of f
		image[g, h, img, f]		-- img is the image of f
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
// fact { isoTheorem1 }
assert isoTheorem1 { isoTheorem1 }
check isoTheorem1 for 0 but 5 Group, 4 Ind, 4 Set


-- NOT WORKING
-- evaluating "isomorphic[$isoTheorem2_q1, $isoTheorem2_q2]" gives:
-- 		Fatal error: Unknown exception occurred: java.lang.NullPointerException
pred isoTheorem2 {
	disjSets implies
	all g, s, n, sn, sin, q1, q2: Group | {
		subgroup[s, g]			
		normalSub[n, g]
		product[g, s, n, sn]	
		intersection[g, s, n, sin]	
		quotient[sn, n, q1]	
		quotient[s, sin, q2]
	} implies {
		-- 1. The product SN is a subgroup of G
		subgroup[sn, g]
		-- 2. The intersection S n N is a normal subgroup of S
		normalSub[sin, s]
		-- 3. The quotient groups (SN)/N and S/(SnN) are isomorphic
		isomorphic[q1, q2]
	}
}
// fact { isoTheorem2 }
assert isoTheorem2 { isoTheorem2 }
check isoTheorem2 for 6 but 7 Group













