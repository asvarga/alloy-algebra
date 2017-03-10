
sig Elem {}

abstract sig Structure {
	G: set Elem,
	rel: G -> G -> one G
}{ rel.G = G->G }

sig Group extends Structure {
	id: one G
} {
	-- TODO: rewrite with relational logic
	//id.rel in iden and (univ->id)<:rel in iden

	-- identity
	all x: G | rel[id][x] = x and rel[x][id] = x
	-- associativity
	all x,y,z: G | rel[rel[x][y]][z] = rel[x][rel[y][z]]
	-- inverse
	all x: G | some inv: G | rel[x][inv] = id and rel[inv][x] = id
}

//pred 



fact neaten {
	Group.G = Elem		-- all Elems used
}
run {} for exactly 1 Group, 2 Elem
