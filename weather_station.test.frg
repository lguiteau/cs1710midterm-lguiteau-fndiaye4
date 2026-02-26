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
    validStations
    all s: Station | (
        s != AtlantaCentralStation implies one s.parent
    )
} is necessary for validStations for 8 but 1 Station
-- validStations implies this forall
rootNoParentBad: assert { --over constraint because it's a stronger version of the above assertion ... Inclusion 
    validStations
    AtlantaCentralStation.parent = Georgetown
} is unsat for 8 but 1 Station





//  test expect OwnParent{
//     ownParents:{
//         validStations 
//             all station : Station | {
//                 station.parent = station
//         }
//     } for 8 Station is unsat
//  }

ownParent: assert { -- exclusion: validStations should never allow a station to be its own parent
   validStations
    all station: Station | {
        station.parent != station
    }
} is necessary for validStations for 8 Station

}

test suite for defineTree{
    // test expect defineTreeTest {
    //     defineTreeTest: {
    //         validStations
    //         defineTree
    //     } for 8 Station is sat
    // }

    defineTreeGood: assert { -- inclusion: validStations + defineTree should be satisfiable together
        validStations and defineTree
    } is sufficient for defineTree for 8 Station

    
    // test expect defineTreeBad {
    //     defineTreeBad: {
    //         validStations
    //         defineTree
    //         Georgetown.parent = NewOrleans
    //     } for 8 Station is unsat 
    // }

    defineTreeBad: assert { -- exclusion: Georgetown should never have NewOrleans as parent in a valid tree
        validStations and defineTree
        Georgetown.parent = NewOrleans
    } is unsat for 8 Station


}

test suite for defineStormEdges{ -- storm propagation test suite
    // test expect defineStormEdgesTest {
    //     defineStormEdgesTest: {
    //         validStations
    //         defineTree
    //         defineStormEdges
    //     } for 8 Station is sat
    // }

    defineStormEdgesGood: assert { -- inclusion: all three predicates together should be satisfiable
        validStations and defineTree and defineStormEdges
    } is sufficient for defineStormEdges for 8 Station

    // test expect defineStormEdgesBad {
    //     defineStormEdgesBad: {
    //         validStations
    //         defineTree
    //         defineStormEdges
    //         NewOrleans.passStormComing = none
    //     } for 8 Station is unsat 
    // }

     defineStormEdgesBad: assert { -- exclusion: a station should never have no storm info once edges are defined
        validStations and defineTree and defineStormEdges
        NewOrleans.passStormComing = none
    } is unsat for 8 Station

}
