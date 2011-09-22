module logicraft/redstone

open logicraft/block

/* Blocks that can anchor Torches or Wire. */
sig Anchor in Block {}

/* Torches and Wires are not anchors. */
fact { no (RedstoneTorch + Wire) & Anchor }

/* A Torch block must have an anchor. It can anchor to
 * any face of an anchor block except the bottom face.
 */
sig RedstoneTorch extends Block {
    anchor: one Anchor
} {
    adjacent[this, anchor, 0] or below[this, anchor]
}


/* A Wire must rest on an anchor block (its base). */
sig Wire extends Block {
    base: one Anchor
} {
    below[this, base]
}

