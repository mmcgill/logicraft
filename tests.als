open logicraft/block

sig Dirt in Block {}

run {} for 10 Block

run { some b1,b2:Block | above[b1,b2] } for 10 Block

run { some b1,b2:Block | adjacent[b1,ET, b2,1] } for 10 Block

