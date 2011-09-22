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

