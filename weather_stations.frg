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
one sig CentralStation extends Station {
    // fields
    Atlanta: lone Station
}

sig CityStations extends Station {
    // fields
    Georgetown: one Station,
    Philadelphia: one Station,
    NewYork: one Station,
    NewOrleans: one Station,
    Denver: one Station,
    LosAngeles: one Station,
    Dallas: one Station
}

pred validStations {
    // constraints

    all s: Station | {

        // the root has no parent
        (s = CentralStation) implies (s.parent = none)
        
        // A station cannot be its own neighbor
        s not in s.Neighbors

        // all noded stations must be connected to the central station through a path of its ancestors
        reachable[CentralStation, s, parent]

        // all stations must have at least 1 parent
        // #s.parent >= 1

       // every station except the central station  must have exactly 1 ancestor station
        (s != CentralStation) implies (#s.parent = 1)
    
        // the central station must have 2 neighbors
        // (s = CentralStation) implies (#s.Neighbors = 2)

        // All station should eventually recieve the storm warning if the central station receives it
        (CentralStation.isStormComing = True) implies (s.isStormComing = True) // Think about this
    }
}