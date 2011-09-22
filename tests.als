open block
open redstone

fact { block_bounds[0, 0, 0, 3, 3, 3] }

sig Dirt extends Block {}
fact {
    Dirt in Anchor
    Dirt in OpaqueBlock
    no Dirt & Connectable
}

run {} for 10 Block

run { some b1,b2:Block | above[b1,b2] } for 10 Block

run { some b1,b2:Block | adjacent[b1,ET, b2,1] } for 10 Block

run {} for 6 but exactly 5 RedstoneTorch

check {#RedstoneTorch=6 implies #Anchor>1} for 10 Block

run {} for 10 but exactly 4 Wire

run {some Wire} for 10 but exactly 1 Dirt, exactly 4 RedstoneTorch

run {#connected > 4} for 10

run {some b:Block,w:Wire | aligned_with[w,b]} for 10

/* Find a model in which a wire connected to a torch
 * loops back around to lead into its anchor point.
 * 11 blocks appears to be the lower bound.
 */
run {
    some b:Block,w:Wire |
        b in univ.anchor and
        aligned_with[w,b] and
        anchor.b in w.(^connected)}
for 11 but 1 RedstoneTorch

