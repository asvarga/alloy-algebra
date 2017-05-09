
open groups as G
open iso

--------

fact { allElemsUsed }

run Some { some Group.E } 	for 0 but exactly 4 Ind, 1 Group
run Gen1 { gen1[Group] } 	for 0 but exactly 6 Ind, 1 Group
run Gen2 { gen2[Group] and not gen1[Group] } for 0 but exactly 6 Ind, 1 Group
run Gen3 { gen3[Group] and not gen2[Group] } for 0 but exactly 8 Ind, 1 Group

run Sub { some g: Group, h: set g.E | subgroup[g, h] } 			for 0 but exactly 4 Ind, exactly 1 Group
run Norm { some g: Group, h: set g.E | normalSub[g, h] } 		for 0 but exactly 4 Ind, exactly 1 Group
run Hom { some disj g,h: Group | homomorphic[g, g.E, h, h.E] } 	for 0 but exactly 2 Ind, exactly 2 Group
run Iso { some disj g,h: Group | isomorphic[g, g.E, h, h.E] } 	for 0 but exactly 4 Ind, exactly 2 Group
run Prod { some disj g,s,t,st: Group | product[g, s, t, st] } 	for 0 but exactly 6 Ind, exactly 4 Group
run Inter { some disj g,s,t,st: Group | intersection[g, s, t, st] } for 0 but exactly 6 Ind, exactly 4 Group

--------

run Quo {
	some disj g,q: Group, n: set g.E {
		g.E = Ind
		q.E = Set
		quotient[g, n, q]
	}
} for 0 but exactly 6 Ind, exactly 2 Set, exactly 2 Group



