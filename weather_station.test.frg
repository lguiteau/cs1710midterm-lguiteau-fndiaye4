#lang forge/temporal

open "weather_stations.frg"

--Testing Suite for our 3 predicates
-- Each predicate will have assertions + 1 bad example + 1 Good Example

--TESTING GUIDELINES: 
--testing all predicates
--domain predicates (things that only have meaning in the domain we're modeling)
--over/under constraint
--inclusion vs. exclusion 

test suite for validStations {

    rootNoParent: assert { -- exclusion: root must never have a parent
        validStations
        CentralStation.parent = none
    } is necessary for validStations for 8 Station


    rootNoParentBad: assert { -- over constraint: giving root a parent should break validStations
        validStations
        CentralStation.parent = Georgetown
    } is unsat for 8 Station


    test expect ownParent {
        ownParents: {
            validStations
            all s: Station | s.parent = s
        } for 8 Station is unsat
    }

    test expect atMostTwoChildren {
        tooManyChildren: {
            validStations
            #{s: Station | s.parent = CentralStation} > 2
        } for 8 Station is unsat
    }

}


test suite for defineTree {

    test expect defineTreeTest {
        defineTreeValid: {
            defineTree
            init
        } for 8 Station is sat
    }

    defineTreeBad: assert { -- exclusion: Georgetown should never have NewOrleans as parent
        validStations and defineTree
        Georgetown.parent = NewOrleans
    } is unsat for 8 Station

    -- Reachability: verifies parent chain for both branches of the tree
    test expect reachableViaDefineTree {
        reachableTest: {
            defineTree
            NewYork.parent = Philadelphia
            Philadelphia.parent = Georgetown
            Georgetown.parent = CentralStation
            LosAngeles.parent = Denver
            Denver.parent = Dallas
            Dallas.parent = NewOrleans
            NewOrleans.parent = CentralStation
        } for 8 Station is sat
    }

}



test suite for init {

    -- Only the central station should have storm info at time 0
    test expect onlyCentralHasInfo {
        onlyCentralHasInfoTest: {
            init
            some s: Station | s != CentralStation and one s.stormInfo
        } for 8 Station is unsat
    }

    -- Central station must have some storm info at time 0
    test expect centralHasInfo {
        centralHasInfoTest: {
            init
            no CentralStation.stormInfo
        } for 8 Station is unsat
    }

}



test suite for defineStormEdges {

    -- inclusion: all predicates together should be satisfiable
    defineStormEdgesGood: assert {
        validStations and defineTree and init and defineStormEdges
    } is sufficient for defineStormEdges for 8 Station


    -- Central station's storm info must not change between steps
    test expect centralInfoStable {
        centralInfoStableTest: {
            validStations
            defineTree
            init
            defineStormEdges
            CentralStation.stormInfo != CentralStation.stormInfo'
        } for 8 Station is unsat
    }

    -- A station with an informed parent must adopt that info next state
    test expect propagationOccurs {
        propagationOccursTest: {
            validStations
            defineTree
            init
            defineStormEdges
            -- Georgetown's parent (CentralStation) has info, so Georgetown must get it next
            one CentralStation.stormInfo
            no Georgetown.stormInfo'
        } for 8 Station is unsat
    }

    -- A station with no informed parent must keep its current info (no spontaneous change)
    test expect noSpontaneousChange {
        noSpontaneousChangeTest: {
            validStations
            defineTree
            init
            defineStormEdges
            no NewYork.parent.stormInfo
            NewYork.stormInfo' != NewYork.stormInfo
        } for 8 Station is unsat
    }

}



test suite for traces {

    -- The full traces pred should be satisfiable
    test expect tracessat {
        tracesSat: {
            traces
        } for 8 Station is sat
    }

    -- Eventually every station should be informed
    test expect allInformedEventually {
        allInformedTest: {
            traces
            not eventually { all s: Station | one s.stormInfo }
        } for 8 Station is unsat
    }

    -- No station should ever have info that contradicts the central station
    test expect signalConsistency {
        signalConsistencyTest: {
            traces
            eventually {
                some s: Station | 
                    one s.stormInfo and s.stormInfo != CentralStation.stormInfo
            }
        } for 8 Station is unsat
    }

    -- A non-root station should never be informed before its parent
    test expect noSkipping {
        noSkippingTest: {
            traces
            some s: Station | s != CentralStation and {
                one s.stormInfo
                no s.parent.stormInfo
            }
        } for 8 Station is unsat
    }

}