
module sets

--------

abstract sig Set { e: set univ }

pred eq(s1,s2: Set) { s1.e = s2.e }
pred unique { all disj x,y: Set | not eq[x, y] }
