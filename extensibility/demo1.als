
/*
Demo 1: This version is self-contained and uses ~10k clauses.

All elements of Groups are Dogs, but this isn't very extensible.
*/

--------

sig Dog {}
sig Group {
	E: set Dog,
	id: E,
	add: E -> E -> one E,
} {
	-- identity
	all x: E | add[x][id] = x and add[id][x] = x
	-- associativity
	all x,y,z: E | add[add[x][y]][z] = add[x][add[y][z]]
	-- inverse
	all x: E | some y: E | add[x][y] = id and add[y][x] = id
}

run {} for exactly 1 Group, exactly 4 Dog
