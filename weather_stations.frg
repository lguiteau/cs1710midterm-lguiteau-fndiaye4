#lang forge/froglet

-- Load the visualization script
option run_sterling "layout.cnd"

abstract sig Boolean {}
one sig True, False extends Boolean {}


sig Station {
    // fields
    parent: lone Station,
    isStormComing: one Boolean  
}

//Root Station
one sig AtlantaCentralStation extends Station {
}

one sig Georgetown, Philadelphia, NewYork, 
        NewOrleans, Denver, LosAngeles, Dallas extends Station {}

pred validStations {
    // constraints

    all s: Station | {

        // the root has no parent
        (s = AtlantaCentralStation) implies (s.parent = none)
        
        // A station cannot be its own neighbor
        s not in s.parent

        // all noded stations must be connected to the central station through a path of its ancestors
        (s != AtlantaCentralStation) implies  reachable[AtlantaCentralStation, s, parent]

        // No cycles
        s != AtlantaCentralStation implies not reachable[s, s, parent]

        // all stations except the root must have one parent
        (s != AtlantaCentralStation) implies one s.parent

    }
}

pred stormPropagation {
    
 all s: Station | s != CentralStation implies {
      s.isStormComing = s.parent.isStormComing
    }
}