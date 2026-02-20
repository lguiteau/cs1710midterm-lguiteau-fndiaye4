#lang forge/froglet

-- Load the visualization script
option run_sterling "layout.cnd"

abstract sig Boolean {}
one sig True, False extends Boolean {}


sig Station {
    // fields
    Neighbors: set Station,
    isStormComing: one Boolean  
}

//Root Station
one sig CentralStation extends Station {
    // fields
    Atlanta: one Station
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
        // A station cannot be its own neighbor
        s not in s.Neighbors

        // Neighbors must be symmetric
        all n: s.Neighbors | s in n.Neighbors

        // A station cannot have more than 2 neighbors
        #s.Neighbors <= 2

        // all noded stations must be connected to the central station through a path of neighbors
        all n: Station | reachable[CentralStation, n, s.Neighbors]

        // all stations must have at least 1 neighbor
        #s.Neighbors >= 1

        //every station except the central station  must have exactly 1 ancestor station
        (s != CentralStation) implies (#(s.Neighbors) == 1)

        // the central station must have at least 2 neighbors
        (s = CentralStation) implies (#s.Neighbors >= 2)

        // All station should eventually recieve the storm warning if the central station receives it
        (CentralStation.isStormComing = True) implies (s.isStormComing = True)
    }
}