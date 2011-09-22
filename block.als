module logicraft/block
open util/integer

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

/* For referring to blocks relative to a given block. */
abstract sig Dir {}
one sig ET, WT, NT, ST extends Dir {}
fact DirIsClosed { Dir = ET + WT + NT + ST }

/* True if b2 is an adjacent block in direction d from b1, subject to dy (delta-y). */
pred adjacent(b1:Block, d:Dir, b2:Block, dy:Int) {
    (d=ET and b1.x=b2.x and b1.y.add[dy]=b2.y and b1.z.sub[1]=b2.z) or
    (d=WT and b1.x=b2.x and b1.y.add[dy]=b2.y and b1.z.add[1]=b2.z) or
    (d=NT and b1.x.sub[1]=b2.x and b1.y.add[dy]=b2.y and b1.z=b2.z) or
    (d=ST and b1.x.add[1]=b2.x and b1.y.add[dy]=b2.y and b1.z=b2.z)
}

/* True if b2 is an adjacent block in direction d from b1,
 * within one y-unit up or down.
 */
pred adjacent(b1:Block, d:Dir, b2:Block) {
    adjacent[b1, d, b2, -1] or adjacent[b1, d, b2, 0] or adjacent[b1, d, b2, 1]
}

/* True if b2 is an adjacent block in some direction, subject to dy. */
pred adjacent(b1:Block, b2:Block, dy:Int) {
    some d:Dir | adjacent[b1, d, b2, dy]
}

/* True if b2 is an adjacent block in some direction from b1,
 * within one y-unit up or down.
 */
pred adjacent(b1:Block, b2:Block) {
    adjacent[b1, b2, -1] or adjacent[b1, b2, 0] or adjacent[b1, b2, 1]
}

/* True if b2 is above b1. */
pred above(b1,b2:Block) {
    b1.x = b2.x and b1.z = b2.z and b1.y.add[1] = b2.y
}

/* True if b2 is below b2. */
pred below(b1,b2:Block) {
    b1.x = b2.x and b1.z = b2.z and b1.y.sub[1] = b2.y
}

