module logicraft/block

/* In MineCraft, the world consists of blocks arranged
 * on a 3-dimensional grid. */
abstract sig Block {
    x: one Int,
    y: one Int,
    z: one Int,
} {
    // No two blocks may occupy the same location.
    no b:(Block-this) | b.@x = x and b.@y = y and b.@z = z
}

/* Use in a fact to constrain the world size. */
pred block_bounds(xmin,ymin,zmin,xmax,ymax,zmax:Int) {
    all b:Block |
        xmin <= b.x  and b.x <= xmax and
        ymin <= b.y  and b.y <= ymax and
        zmin <= b.z  and b.z <= zmax
}

