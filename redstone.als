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


/* A Wire must rest on an anchor block (its base).
 */
sig Wire extends Block {
    base: one Anchor,
    connected: set Connectable
} {
    below[this, base]
    connected = { c:Connectable | connects_to[this, c] }
}

/*
 * A wire "connects to" (i.e. is rendered as if leading to)
 * adjacent blocks of certain types, under the right conditions.
 */
pred connects_to(w:Wire, c:Connectable) {
    (adjacent[w,c,-1] and no b:OpaqueBlock | above[c, b]) or
    adjacent[w,c,0] or
    (adjacent[w,c,1] and no b:OpaqueBlock | above[w, b])
}

/* A wire is 'aligned' with a block if that wire leads
 * directly into it. This is the case if the wire and the
 * block are adjacent at the same height and the wire
 * is connected on the opposite side.
 *
 * NOTE: In Minecraft 1.8.1, wire alignment appears to depend
 * on block updates. We model alignment under the assumption
 * that all possible block updates have been performed.
 */
pred aligned_with(w:Wire, b:Block) {
    some d:Dir |
        adjacent[b,d,w,0] and
        one w.connected and
        adjacent[w,d,w.connected]
}

/* Any block that a wire can connect to. */
sig Connectable in Block {}
fact { (RedstoneTorch + Wire) in Connectable }

/* Blocks that can 'pinch off' a connection between a
 * wire and an adjacent Connectable at a different height.
 */
sig OpaqueBlock in Block {}

/* Torches and wires are not opaque. */
fact { no (RedstoneTorch + Wire) & OpaqueBlock }

