
-- this module lets us parameterize over sets of things
module sets[T]

--------

sig Set { E: set T }

pred eq(s1,s2: Set) { s1.E = s2.E }
pred unique { all disj x,y: Set | not eq[x, y] }
