
-- this module lets us parameterize over sets of things
module sets[T]

--------

sig Set { e: set T }

pred eq(s1,s2: Set) { s1.e = s2.e }
pred unique { all disj x,y: Set | not eq[x, y] }
