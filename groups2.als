

abstract sig Elem {}
sig BElem extends Elem {}
sig SElem extends Elem { E: set BElem }
fact { all disj x,y: SElem | x.E != y.E }

sig Group {
	E: set Elem,
	id: E,
	rel: E->E //-> one E
}



//one sig Id extends BElem {}

run {some BElem}

/*



{
	-- identity
	//id.rel in iden and id.(flip12[rel]) in iden
	-- associativity
	all x,y,z: E | rel[rel[x][y]][z] = rel[x][rel[y][z]]
	-- inverse
	(rel.id).E = E and E.(rel.id) = E
}





one sig Id extends BElem {}
one sig Gr extends Group {} { id = Id }

run Some { some Gr.E }
*/
