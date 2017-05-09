
open rings as R
open groups as G

--------

fact { allElemsUsed }

run Some { some Ring.E } for 0 but exactly 5 Ind, exactly 1 Ring
run Sub { some disj g,h: Group | subring[g, h] } for 0 but exactly 4 Ind, exactly 2 Ring
run Ideal { some disj g,h: Group | ideal[g, h] } for 0 but exactly 4 Ind, exactly 2 Ring




