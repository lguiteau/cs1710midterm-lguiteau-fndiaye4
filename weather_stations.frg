#lang forge/froglet

-- Load the visualization script
option run_sterling "layout.cnd"

// abstract sig Boolean {}
// one sig True, False extends Boolean {}

abstract sig StormBool {}
one sig StormFalse, StormTrue extends StormBool {}

sig Station {
    // fields
    parent: lone Station,
    // isStormComing: one Int  // 0 for false, 1 for true
    isStormComing: one StormBool


}


//Root Station
one sig AtlantaCentralStation extends Station {
  centralStationStormInfo: one Int  // 0 for false, 1 for true
}


one sig Georgetown, Philadelphia, NewYork, 
        NewOrleans, Denver, LosAngeles, Dallas extends Station {}

pred validStations {
    // constraints

    all s: Station | {

        // the root has no parent
        (s = AtlantaCentralStation) implies (s.parent = none)
        
        // A station cannot be its own parent
        s.parent != s

        // All stations except the root must be reachable from the central station
        (s != AtlantaCentralStation) implies reachable[AtlantaCentralStation, s, parent] 

            // No station can be connected to the central station through more than one path
        // s != AtlantaCentralStation implies not reachable[s, s, parent]

        // Each station (except the root) must have a path back to the root whether that be through a parent, ancestor, or direct
        (s != AtlantaCentralStation) implies one s.parent

        // Atlanta can have at most 2 direct children
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


pred stormPropagation {
    validStations

    // AtlantaCentralStation.centralStationStormInfo = 0 or AtlantaCentralStation.centralStationStormInfo= 1 
    // all s: Station | s != AtlantaCentralStation implies {
    //     s.isStormComing = s.parent.isStormComing  -- propagates down from root
    // }
     AtlantaCentralStation.centralStationStormInfo = 0 implies {
        all s: Station | s.isStormComing = StormFalse implies {
            all c: Station | c.parent = s implies c.isStormComing = StormFalse
        }
    }
    
    AtlantaCentralStation.centralStationStormInfo = 1 implies {
        all s: Station | s.isStormComing = StormTrue implies {
            all c: Station | c.parent = s implies c.isStormComing = StormTrue
        }
    }


}


run{
    validStations
    defineTree
    stormPropagation

} for 8 but 1 Station