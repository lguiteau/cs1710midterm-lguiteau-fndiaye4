#lang forge/temporal

-- Load the visualization script
// option run_sterling "layout.cnd"



abstract sig StormBool {}
one sig StormFalse, StormTrue extends StormBool {}

sig Station {
-- fields
parent: lone Station,
passStormComing: lone Station,
var stormInfo: lone StormBool 

}


--Root Station
one sig CentralStation extends Station {
// centralStationStormInfo: one StormBool  -- StormFalse for false, StormTrue for true
}



one sig Georgetown, Philadelphia, NewYork, 
NewOrleans, Denver, LosAngeles, Dallas extends Station {}


pred validStations {
-- constraints

all s: Station | {

-- the root has no parent
(s = CentralStation) implies (s.parent = none)

-- A station cannot be its own parent
s.parent != s

-- All stations except the root must be reachable from the central station
  (s != CentralStation) implies s in CentralStation.^~parent


// -- Each station (except the root) must have a path back to the root whether that be through a parent, ancestor, or direct
(s != CentralStation) implies one s.parent


}
// -- Atlanta can have at most 2 direct children
#{s: Station | s.parent = CentralStation} <= 2
}


pred defineTree {
Georgetown.parent = CentralStation
Philadelphia.parent = Georgetown
NewYork.parent = Philadelphia
NewOrleans.parent = CentralStation
Denver.parent = Dallas
LosAngeles.parent = Denver
Dallas.parent = NewOrleans
}

pred init {
  -- Only the central station has storm info at time 0
  -- (it directly receives the boolean signal)
  one CentralStation.stormInfo

  -- All other stations start with no info yet
  all s: Station | s != CentralStation implies no s.stormInfo
}


pred defineStormEdges {
-- The central station's info never changes (it is the source)
  CentralStation.stormInfo = CentralStation.stormInfo'

  all s: Station | s != CentralStation implies s.passStormComing = s.parent
  CentralStation.passStormComing = none

  -- Each other station: if its parent has info, adopt it next state
  -- If it already has info, keep it (info is sticky once received)
  all s: Station | s != CentralStation implies {
    (some s.parent.stormInfo) implies s.stormInfo' = s.parent.stormInfo
    (no s.parent.stormInfo)   implies s.stormInfo' = s.stormInfo
  }
}

pred traces {
  defineTree
  validStations
  init
  always defineStormEdges
}
option max_tracelength 10

run {
  traces
} for 8 Station
