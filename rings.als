
module rings

open groups as G		

--------

sig Ring extends Group{
	uno: Elem,								-- "E" doesn't work in Alloy*
	mul: Elem -> Elem -> Elem				-- "E -> E -> one E" doesn't work in Alloy*
} {
	-- *abelian* group under addition
	all x,y: E | add[x][y] = add[y][x]		// TODO: use relations?
	-- fix for alloy*
	uno in E
	mul in E -> E -> one E
	-- identity
	uno.mul in iden and uno.(flip12[mul]) in iden
	-- associativity
	all x,y,z: E | mul[mul[x][y]][z] = mul[x][mul[y][z]]
	-- multiplication distributes over addition
	all x,y,z: E | mul[x][add[y][z]] = add[mul[x][y]][mul[x][z]]	// TODO: use relations?
	all x,y,z: E | mul[add[y][z]][x] = add[mul[y][x]][mul[z][x]]	// TODO: use relations?
}

pred ringEq(r1,r2: Ring) { 
	groupEq[r1, r2]
	r1.uno = r2.uno
	r1.mul = r2.mul
}
pred disjRings { all disj x,y: Ring | not ringEq[x, y] }

run {}
