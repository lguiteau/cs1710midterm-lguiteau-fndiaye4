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

