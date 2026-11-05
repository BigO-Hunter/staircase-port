import StaircasePort.NEBlocks
open StaircasePort.Stair
#check @stairNEBlocksX
#check @stairNE_cuts_cover
#check @stairNE_cuts_card
#check @stairNEBlocksX_map
#check @stairNESr
#print axioms stairNE_cuts_cover
#print axioms stairNE_cuts_card
#print axioms stairNEBlocksX_map
example : stairNEBlocksX.length = 689 := rfl
