
open groups						-- Groups (of Any)
open sets						-- Sets (of Any)
open quotient

--------

sig Elem {}
sig SE extends Set {} { e in Elem }			-- Sets of Elems

sig GE extends Group {} { E in Elem }		-- Groups of Elems
sig GSE extends Group {} { E in SE }		-- Groups of Sets of Elems

fact neat { 
	Elem in Group.E				-- all Elems used
	SE in Group.E				-- all Sets used
	// SE/unique
}

--------

run Some { some GE.E } for 0 but exactly 4 Elem, 1 Group
run Gen1 { gen1[GE] } for 0 but exactly 6 Elem, 1 Group
run Gen2 { gen2[GE] and not gen1[GE] } for 0 but exactly 6 Elem, 1 Group
run Gen3 { gen3[GE] and not gen2[GE] } for 0 but exactly 8 Elem, 1 Group

run Sub { some disj g,h: GE | subgroup[g, h] } for 0 but exactly 4 Elem, 2 Group
run Norm { some disj g,h: GE | normalSub[g, h] } for 0 but exactly 4 Elem, 2 Group
run Hom { some disj g,h: GE | homomorphic[g, h] } for 0 but exactly 2 Elem, 2 Group
run Iso { some disj g,h: GE | isomorphic[g, h] } for 0 but exactly 4 Elem, 2 Group
run Quo {
	some disj g, n: GE, q: GSE {
		g.E = Elem					-- TODO: remove?
		quotient[g, n, q]
	}
} for exactly 6 Elem, 2 SE, 2 GE, 1 GSE
