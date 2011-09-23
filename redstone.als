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

sig Powered, Activated in Block {}

/* A wire is directly powered when adjacent to, above,
 * or below a powered non-wire block.
 */
pred directly_powered(w:Wire) {
    w.base in Powered or some b:Powered-Wire | adjacent[w,b,0] or above[w,b]
}

fact {
    Powered =
    /* A non-Wire, non-Torch block is powered exactly when a powered Torch
     * is under it. */
        { b:Block - Wire - RedstoneTorch |
            some t:Powered & RedstoneTorch | above[t,b] } +
    /* Wire is powered exactly when it is directly powered, or it is
     * transitively connected to directly powered wire.  */
        { w:Wire | some w2:w.*(connected:>Wire) | directly_powered[w2] } +
    /* A redstone torch is powered exactly when its anchor is not
     * activated.  */
        { t:RedstoneTorch | not t.anchor in Activated }
}

/* Activated blocks are non-Wire, non-Torch blocks that are
 * powered or aligned with/underneath powered wire.
 */
fact {
    Activated = {b:Block-(Wire+RedstoneTorch) |
        (b in Powered or
         some w:Powered & Wire |
            below[w,b] or aligned_with[w,b]) }
}


