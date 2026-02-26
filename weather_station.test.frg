#lang forge/froglet

open "weather_stations.frg"

--Testing Suite for our 3 predicates
-- Each predicate will have assertions + 1 bad example + 1 Good Example


test suite for validStations{

// AtlantaCentralStation (a.k.a root) should have not parent
 test expect centralStationNoParent {
    noParentForRoot: {
        validStations 
            all s: Station | {
                s != AtlantaCentralStation implies one s.parent
            }
    } for 8 Station is sat
 }

 test expect OwnParent{
    ownParents:{
        validStations 
            all station : Station | {
                station.parent = station
        }
    } for 8 Station is unsat
 }


}

test suite for defineTree{
    test expect defineTreeTest {
        defineTreeTest: {
            validStations
            defineTree
        } for 8 Station is sat
    }
    
    test expect defineTreeBad {
        defineTreeBad: {
            validStations
            defineTree
            Georgetown.parent = NewOrleans
        } for 8 Station is unsat 
    }

}

test suite for defineStormEdges{ -- storm propagation test suite
    test expect defineStormEdgesTest {
        defineStormEdgesTest: {
            validStations
            defineTree
            defineStormEdges
        } for 8 Station is sat
    }

    test expect defineStormEdgesBad {
        defineStormEdgesBad: {
            validStations
            defineTree
            defineStormEdges
            NewOrleans.passStormComing = none
        } for 8 Station is unsat 
    }

}
