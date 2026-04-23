#lang forge/temporal

-- temporal constraints
option min_tracelength 2
option max_tracelength 10

-- Load the visualization script
// option run_sterling "layout.cnd"



abstract sig StormBool {}
one sig StormFalse, StormTrue extends StormBool {}

sig Station {
  -- fields
  parent: lone Station,
  passStormComing: lone Station,
  originatesInfo: lone StormBool,
  var stormInfo: lone StormBool 
}


--Root Station
// one sig CentralStation extends Station {
//   // centralStationStormInfo: one StormBool  -- StormFalse for false, StormTrue for true
// }



one sig Georgetown, Philadelphia, NewYork, 
NewOrleans, Denver, LosAngeles, Dallas extends Station {}


-- validStations predicate
pred validStations {
  all s: Station | {
    -- A station cannot be its own parent
    s.parent != s

    -- Originators act as roots and have no parent
    (some s.originatesInfo) implies (s.parent = none)

    -- Non-originators must have exactly one parent
    (no s.originatesInfo) implies one s.parent

    -- All non-originators must be reachable from SOME originator
    (no s.originatesInfo) implies {
      some orig: Station | {
        some orig.originatesInfo
        s in orig.^~parent
      }
    }
  }
}



// pred defineTree {
// Georgetown.parent = CentralStation
// Philadelphia.parent = Georgetown
// NewYork.parent = Philadelphia
// NewOrleans.parent = CentralStation
// Denver.parent = Dallas
// LosAngeles.parent = Denver
// Dallas.parent = NewOrleans
// }

pred init {
  -- Originators have their specific storm info at time 0
  all s: Station | (some s.originatesInfo) => {
    s.stormInfo = s.originatesInfo
  }

  -- All other stations start with no info yet
  all s: Station | (no s.originatesInfo) => {
    no s.stormInfo
  }
}


pred defineStormEdges {
  -- Originators' info never changes (they are the sources)
  all s: Station | (some s.originatesInfo) => {
    s.stormInfo' = s.stormInfo
  }
  all s: Station | (some s.originatesInfo) => {
    s.passStormComing = none
  }

  -- Non-originators point to their parent for passing info
  all s: Station | (no s.originatesInfo) => {
    s.passStormComing = s.parent
  }

  -- Each non-originator: if its parent has info, adopt it next state.
  -- If it already has info, keep it (sticky info)
  all s: Station | (no s.originatesInfo) => {
    (some s.parent.stormInfo) => {
      s.stormInfo' = s.parent.stormInfo
    }
    (no s.parent.stormInfo) => {
      s.stormInfo' = s.stormInfo
    }
  }
}

pred traces {
  // defineTree
  validStations
  init
  always defineStormEdges
}
option max_tracelength 10

run {
  traces
  some disj s1, s2: Station {
    some s1.originatesInfo
    some s2.originatesInfo
  }
} for 8 Station
