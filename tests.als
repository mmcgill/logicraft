open block
open redstone

fact { block_bounds[0, 0, 0, 3, 3, 3] }

sig Dirt extends Block {}
fact { Dirt in Anchor }

run {} for 10 Block

run { some b1,b2:Block | above[b1,b2] } for 10 Block

run { some b1,b2:Block | adjacent[b1,ET, b2,1] } for 10 Block

run {} for 6 but exactly 5 RedstoneTorch

check {#RedstoneTorch=6 implies #Anchor>1} for 10 Block

run {} for 10 but exactly 4 Wire

run {some Wire} for 10 but exactly 1 Dirt, exactly 4 RedstoneTorch

