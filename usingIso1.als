
/*
This was an attempt to use first isomorphism theorem to speed up an assertion check,
instead of re-proving it with Alloy*. It doesn't seem to work :(
*/

--------

open groups as G
open quotient

--------

fact {
	//isoTheorem1						-- I hoped this assumption would help...
	allElemsUsed
	some g,h: Group {
		gen1[g] and #(g.E) = 4
		gen1[h] and	#(h.E) = 2
		some ker, img, q: Group, f: g.E -> one h.E | {
			homomorphism[g, h, f]	-- f is an iso from g -> h
			kernel[g, h, ker, f]	-- ker is the kernel of f
			image[g, img, f]		-- img is the image of f
			quotient[g, ker, q]		-- q = g/ker
		}
	}
}

check {
	some i,q: Group | isomorphic[i, q]		-- should work for (i,q)=(img,q) from above
} 		for 0 but exactly 5 Group, exactly 4 Ind, 2 Set, 4 Int
run {} 	for 0 but exactly 5 Group, exactly 4 Ind, 2 Set, 4 Int
