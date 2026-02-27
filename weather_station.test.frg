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

rootNoParent: assert { --exclusion because it's similar to an "is unsat" --- "i bet you can't find an instance to satifies validStations but not this forall"
    validStations
    AtlantaCentralStation.parent = none
} is necessary for validStations for 8 Station


rootNoParentBad: assert { --over constraint because it's a stronger version of the above assertion ... Inclusion 
    validStations
    AtlantaCentralStation.parent = Georgetown
} is unsat for 8  Station



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

    
    defineTreeBad: assert { -- exclusion: Georgetown should never have NewOrleans as parent in a valid tree
        validStations and defineTree
        Georgetown.parent = NewOrleans
    } is unsat for 8 Station

    -- Reachability Test: verifies parent chain for both branches of the tree
    -- avoids reachable[] due to known inconsistency with validStations
    test expect reachableViaDefineTree {
        reachableTest: {
            validStations
            defineTree
            NewYork.parent = Philadelphia
            Philadelphia.parent = Georgetown
            Georgetown.parent = AtlantaCentralStation
            LosAngeles.parent = Denver
            Denver.parent = Dallas
            Dallas.parent = NewOrleans
            NewOrleans.parent = AtlantaCentralStation
        } for 8 Station is sat
    }

}

test suite for defineStormEdges{ -- storm propagation test suite
 

    defineStormEdgesGood: assert { -- inclusion: all three predicates together should be satisfiable
        validStations and defineTree and defineStormEdges
    } is sufficient for defineStormEdges for 8 Station


     defineStormEdgesBad: assert { -- exclusion: a station should never have no storm info once edges are defined
        validStations and defineTree and defineStormEdges
        NewOrleans.passStormComing = none
    } is unsat for 8 Station

   
    -- All stations eventually receive storm info once tree and edges are defined
    test expect allStationsSameInfo {
        allStationsSameInfoTest: {
            validStations
            defineTree
            defineStormEdges
            some s: Station | s != AtlantaCentralStation and s.passStormComing = none
        } for 8 Station is unsat
    }


    
     -- Root is the only station that does not pass storm info (passStormComing = none)
    test expect onlyRootReceivesDirectly {
        onlyRootReceivesDirectlyTest: {
            validStations
            defineTree
            defineStormEdges
            some s: Station | s != AtlantaCentralStation and s.passStormComing = none
        } for 8 Station is unsat
    }
}
