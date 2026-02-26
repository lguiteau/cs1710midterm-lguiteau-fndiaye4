#lang forge/froglet

open "weather_stations.frg"

--Testing Suite for our 3 predicates
-- Each predicate will have assertions + 1 bad example + 1 Good Example

--TESTING GUIDELINES: 
--testing all predicates
--domain predicates (things that only have meaning in the domain we're modeling)
--over/under constraint
--inclusion vs. exclusion 


test suite for validStations{

// AtlantaCentralStation (a.k.a root) should have not parent
//  assert centralStationNoParent{ 
//     validStations
//     all s: Station | (
//         s != AtlantaCentralStation implies one s.parent
//     )

// } -- made no distinction between pre-condition and what we want to assert
// check centralStationNoParent -- using check is not something we learned/is not supported


rootNoParent: assert { --exclusion because it's similar to an "is unsat" --- "i bet you can't find an instance to satifies validStations but not this forall"
    all s: Station | (
        s != AtlantaCentralStation implies one s.parent
    )
} is necessary for validStations for 8 but 1 Station
-- validStations implies this forall



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
