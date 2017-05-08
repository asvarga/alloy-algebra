
open groups as G
open rings as R
open quotient

--------

fact { allElemsUsed }

run Some { some Group.E } 	for 0 but exactly 4 Ind, 1 Group
run Gen1 { gen1[Group] } 	for 0 but exactly 6 Ind, 1 Group
run Gen2 { gen2[Group] and not gen1[Group] } for 0 but exactly 6 Ind, 1 Group
run Gen3 { gen3[Group] and not gen2[Group] } for 0 but exactly 8 Ind, 1 Group

run Sub { some disj g,h: Group | subgroup[g, h] } 		for 0 but exactly 4 Ind, exactly 2 Group, exactly 0 Ring
run Norm { some disj g,h: Group | normalSub[g, h] } 	for 0 but exactly 4 Ind, exactly 2 Group, exactly 0 Ring
run Hom { some disj g,h: Group | homomorphic[g, h] } 	for 0 but exactly 2 Ind, exactly 2 Group, exactly 0 Ring
run Iso { some disj g,h: Group | isomorphic[g, h] } 	for 0 but exactly 4 Ind, exactly 2 Group, exactly 0 Ring
run Prod { some disj g,s,t,st: Group | product[g, s, t, st] } for 0 but exactly 6 Ind, exactly 4 Group, exactly 0 Ring
run Inter { some disj g,s,t,st: Group | intersection[g, s, t, st] } for 0 but exactly 6 Ind, exactly 4 Group, exactly 0 Ring

--------

run Quo {
	some disj g,n,q: Group {
		g.E = Ind
		q.E = Set
		quotient[g, n, q]
	}
} for 0 but exactly 6 Ind, exactly 2 Set, exactly 3 Group, exactly 0 Ring

--------

run Some { some Ring.E } for 0 but exactly 5 Ind, exactly 1 Ring
