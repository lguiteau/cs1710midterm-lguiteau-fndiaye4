#lang forge/froglet

-- Load the visualization script
option run_sterling "layout.cnd"



abstract sig StormBool {}
one sig StormFalse, StormTrue extends StormBool {}

sig Station {
-- fields
parent: lone Station,
passStormComing: lone Station

}


--Root Station
one sig AtlantaCentralStation extends Station {
centralStationStormInfo: one StormBool  -- StormFalse for false, StormTrue for true
}



one sig Georgetown, Philadelphia, NewYork, 
NewOrleans, Denver, LosAngeles, Dallas extends Station {}


pred validStations {
-- constraints

all s: Station | {

-- the root has no parent
(s = AtlantaCentralStation) implies (s.parent = none)

-- A station cannot be its own parent
s.parent != s

-- All stations except the root must be reachable from the central station
        (s != AtlantaCentralStation) implies reachable[AtlantaCentralStation, s, parent] implies 
        (s != AtlantaCentralStation) implies reachable[AtlantaCentralStation, s, parent]  


-- Each station (except the root) must have a path back to the root whether that be through a parent, ancestor, or direct
(s != AtlantaCentralStation) implies one s.parent

-- Atlanta can have at most 2 direct children
#{s: Station | s.parent = AtlantaCentralStation} <= 2

}
}

pred defineTree {
Georgetown.parent = AtlantaCentralStation
Philadelphia.parent = Georgetown
NewYork.parent = Philadelphia
NewOrleans.parent = AtlantaCentralStation
Denver.parent = Dallas
LosAngeles.parent = Denver
Dallas.parent = NewOrleans
}


pred defineStormEdges {
-- isStormComing mirrors parent for all non-root stations
all s: Station | s != AtlantaCentralStation implies s.passStormComing = s.parent

-- Root points to none
AtlantaCentralStation.passStormComing = none
}

run {
validStations
defineTree
defineStormEdges

} for 8 Station