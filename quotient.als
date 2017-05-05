
module quotient[T]

open groups[T] as GE				-- Groups of Elems
open sets[T] as SE					-- Sets of Elems
open groups[SE/Set] as GSE			-- Groups of Sets of Elems

--------

pred quotient(g: GE/Group, n: GE/Group, q: GSE/Group) {
	normalSub[n, g]
	-- q's elements are the cosets of n
	all x: g.E | some s: q.E | s.E = g.add[x][n.E]

	-- (xN)(yN) = (xy)N
	all s,t: q.E | some x,y: g.E {
		s.E = g.add[x][n.E]
		t.E = g.add[y][n.E]
		(q.add[s][t]).E = g.add[ g.add[x][y] ][n.E]
	}
}

run {}

-- maybe should assume f is surjective (img == h)
-- could get rid of h
/*assert isoTheorem1 {
	all g, h, ker, img: GE/Group, q: GSE/Group, f: g.E -> one h.E | {
		homomorphism[g, h, f]	-- f is an iso from g -> h
		kernel[g, h, ker, f]	-- ker is the kernel of f
		image[g, img, f]		-- img is the image of f
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
check isoTheorem1 for 4
*/