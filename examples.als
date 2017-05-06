
open groups	as G						-- Groups of Elems
// open quotient[Elem]

--------

fact neat { 
	Elem = Group.E						-- all Elems used
}

--------

run Some { some GSI.E } for 0 but exactly 1 GSI, exactly 3 SI, exactly 3 Set
run Gen1 { gen1[Group] } for 0 but exactly 1 GI, exactly 6 I
run Gen2 { gen2[Group] and not gen1[Group] } for 0 but exactly 1 GI, exactly 6 I
run Gen3 { gen3[Group] and not gen2[Group] } for 0 but exactly 1 GI, exactly 8 I

run Sub  { some disj g,h: GI | subgroup	  	[g, h] } for 0 but exactly 2 GI, exactly 6 I
run Norm { some disj g,h: GI | normalSub	[g, h] } for 0 but exactly 2 GI, exactly 6 I
run Hom  { some disj g,h: GI | homomorphic 	[g, h] } for 0 but exactly 2 GI, exactly 6 I
run Iso  { some disj g,h: GI | isomorphic  	[g, h] } for 0 but exactly 2 GI, exactly 6 I
run Quo {
	some disj g,n: GI, q: GSI {
		g.E = I
		quotient[g, n, q]
	}
} for 0 but exactly 3 Group, exactly 6 I, exactly 2 SI, 2 Set
