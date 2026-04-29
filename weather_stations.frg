#lang forge/temporal

-- temporal constraints
option min_tracelength 2
option max_tracelength 10

-- Load the visualization script
// option run_sterling "layout.cnd"

abstract sig StormBool {} -- abstract type for storm information (true/false)
one sig StormFalse, StormTrue extends StormBool {}

sig Station { 
  -- fields (static structure of the stations)
  parent: lone Station,
  backup: lone Station,  -- for potential backup paths 
  passStormComing: lone Station,
  originatesInfo: lone StormBool,

  -- dynamic structure
  var stormInfo: lone StormBool,
  var parentBeats: one Int, -- missed beats to receive info from parent
  var backupBeats: one Int, -- missed beats to receive info from backup
  var lostOriginator: lone StormBool -- whether the station has lost its original info

}

--Root Station
// one sig CentralStation extends Station {
//   // centralStationStormInfo: one StormBool  -- StormFalse for false, StormTrue for true
// }


one sig Georgetown, Philadelphia, NewYork, 
NewOrleans, Denver, LosAngeles, Dallas extends Station {} 

-----------------------------------------------------------------------------------
-- Define a constant for the timeout threshold
-- The timeout threshold for considering a station's parent or backup as "dead"
fun TIMEOUT: Int { 3 }

-- Parent is live if counter is under threshold
pred parentLive[s: Station] {
  some s.parent
  s.parentBeats < TIMEOUT
}

-- Backup is live if it exists and its counter is under threshold
pred backupLive[s: Station] {
  some s.backup
  s.backupBeats < TIMEOUT
}

-----------------------------------------------------------------------------------

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

    -- Backup must differ from parent
    some s.backup implies s.backup != s.parent
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

pred init { -- Initialize the storm info at time 0
  -- Originators have their specific storm info at time 0
  all s: Station | (some s.originatesInfo) => {
    s.stormInfo = s.originatesInfo
  }

  -- All other stations start with no info yet
  all s: Station | (no s.originatesInfo) => {
    no s.stormInfo
  }

  all s: Station | { -- Initialize beat counters and lost info status
    s.parentBeats = 0
    s.backupBeats = 0
    no s.lostOriginator
  }
}


-- Update the missed beat counters for each station based on whether their parent and backup are alive
pred updateMissedBeats {
  all s: Station | (no s.originatesInfo) implies {

    -- Parent beat: reset if parent has stormInfo, else increment
    (some s.parent and some s.parent.stormInfo) implies
      s.parentBeats' = 0
    (some s.parent and no s.parent.stormInfo) implies {
      (s.parentBeats < TIMEOUT)
        implies s.parentBeats' = add[s.parentBeats, 1]
      (s.parentBeats >= TIMEOUT)
        implies s.parentBeats' = TIMEOUT
    }
    (no s.parent) implies s.parentBeats' = s.parentBeats

    -- Backup beat: reset if backup has stormInfo, else increment
    (some s.backup and some s.backup.stormInfo) implies
      s.backupBeats' = 0
    (some s.backup and no s.backup.stormInfo) implies {
      (s.backupBeats < TIMEOUT)
        implies s.backupBeats' = add[s.backupBeats, 1]
      (s.backupBeats >= TIMEOUT)
        implies s.backupBeats' = TIMEOUT
    }
    (no s.backup) implies s.backupBeats' = s.backupBeats
  }

  -- Originators don't track anyone
  all s: Station | (some s.originatesInfo) implies {
    s.parentBeats' = s.parentBeats
    s.backupBeats' = s.backupBeats
  }
}

-- Route storm info based on the parent-child relationships and the liveness of parents/backups
-- This predicate defines how storm info is passed each time step
fun liveSource[s: Station]: lone Station {
  (parentLive[s])
    => s.parent
  else (not parentLive[s] and backupLive[s])
    => s.backup
  else
    none
}

-- ── Failsafe stub ─────────────────────────────────────────────────────────────
pred failsafe[s: Station] {
  -- TODO: implement later
}


-- Popagation of storm info based on live sources
pred defineStormEdges {
  -- Originators' info never changes (they are the sources)
  all s: Station | (some s.originatesInfo) => {
    s.stormInfo' = s.stormInfo
  }
  all s: Station | (some s.originatesInfo) => {
    s.passStormComing = none
  }

  updateMissedBeats -- Update the beat counters first

  all s: Station | (no s.originatesInfo) implies {
    s.passStormComing = liveSource[s]

    let src = liveSource[s] | {

      -- Normal: live source has info
      (some src and some src.stormInfo) implies {
        s.stormInfo'        = src.stormInfo
        no s.lostOriginator'
      }

      -- Waiting: live source exists but no info yet
      (some src and no src.stormInfo) implies {
        s.stormInfo'        = s.stormInfo
        no s.lostOriginator'
      }

      -- Isolated: no live source at all
      no src implies {
        s.stormInfo' = s.stormInfo

        -- Originator timed out → set flag and call failsafe
        (some s.parent and some s.parent.originatesInfo
         and s.parentBeats >= TIMEOUT) implies {
          one s.lostOriginator'
          -- failsafe[s] removed: undefined identifier
        }

        -- Regular node timed out → no escalation
        (some s.parent and no s.parent.originatesInfo) implies {
          no s.lostOriginator'
        }
      }
    }
  }
}


//   -- Non-originators point to their parent for passing info
//   all s: Station | (no s.originatesInfo) => {
//     s.passStormComing = s.parent
//   }

//   -- Each non-originator: if its parent has info, adopt it next state.
//   -- If it already has info, keep it (sticky info)
//   all s: Station | (no s.originatesInfo) => {
//     (some s.parent.stormInfo) => {
//       s.stormInfo' = s.parent.stormInfo
//     }
//     (no s.parent.stormInfo) => {
//       s.stormInfo' = s.stormInfo
//     }
//   }
// }

pred traces {
  // defineTree
  validStations
  init
  always defineStormEdges
}
option max_tracelength 10

run {
  traces
  some disj s1, s2: Station | {
    some s1.originatesInfo
    some s2.originatesInfo
  }
  some s: Station | eventually some s.lostOriginator
} for 8 Station, 5 Int
