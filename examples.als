
open groups as G					-- Groups (of Any)
open groupsOf[Elem] as GE			-- Groups of Elems
open sets[Elem] as SE				-- Sets of Elems
open groupsOf[SE/Set] as GSE		-- Groups of Sets of Elems
open quotient[Elem]

--------

abstract sig Elem {}

fact neat { 
	Elem in GE/Group.E				-- all Elems used
	Set in GSE/Group.E				-- all Sets used
	SE/unique
}

--------

run Some { some GE/Group.E } for 0 but exactly 4 Elem, 1 G/Group
run Gen1 { gen1[GE/Group] } for 0 but exactly 6 Elem, 1 G/Group
run Gen2 { gen2[GE/Group] and not gen1[GE/Group] } for 0 but exactly 6 Elem, 1 G/Group
run Gen3 { gen3[GE/Group] and not gen2[GE/Group] } for 0 but exactly 8 Elem, 1 G/Group

run Sub { some disj g,h: GE/Group | subgroup[g, h] } for 0 but exactly 4 Elem, 2 G/Group
run Norm { some disj g,h: GE/Group | normalSub[g, h] } for 0 but exactly 4 Elem, 2 G/Group
run Hom { some disj g,h: GE/Group | homomorphic[g, h] } for 0 but exactly 2 Elem, 2 G/Group
run Iso { some disj g,h: GE/Group | isomorphic[g, h] } for 0 but exactly 4 Elem, 2 G/Group
run Quo {
	some disj g,n: GE/Group, q:GSE/Group {
		g.E = Elem
		quotient[g, n, q]
	}
} for exactly 6 Elem, 2 Set, 2 GE/Group, 1 GSE/Group, 3 G/Group
