
open groups[Elem] as GE				-- Groups of Elems
open sets[Elem] as SE				-- Sets of Elems
open groups[SE/Set] as GSE			-- Groups of Sets of Elems
open rings[Elem] as RE				-- Rings of Elems

--------

abstract sig Elem {}

fact neat { 
	Elem in GE/Group.E				-- all Elems used
	Set in GSE/Group.E				-- all Sets used
}






//run {} for 2 but exactly 1 Ring
run {} for 2

