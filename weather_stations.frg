#lang forge/temporal
// option run_sterling "layout.cnd"
option run_sterling "weather_stations.js"

option min_tracelength 5
option max_tracelength 15

abstract sig StormBool {}
one sig StormFalse, StormTrue extends StormBool {}

sig Station {
  parent:          set Station,                -- set of direct parents
  backup:          pfunc Station -> Station,   -- Partial function mapping a parent to its backup
  passStormInfo:   set Station,                -- set of stations passing info
  originatesInfo:  lone StormBool,

  var stormInfo:      lone StormBool,
  var parentBeats:    one Int,
  var backupBeats:    one Int,
  var lostOriginator: lone StormBool,
  var failed:         lone StormBool, -- station has gone silent
  isByzantine:        lone StormBool  -- station is Byzantine
}

// one sig Georgetown, Philadelphia, NewYork,
//         NewOrleans, Denver, LosAngeles, Dallas extends Station {}

fun TIMEOUT: Int { 3 }

-- Parent is live if counter is under threshold AND not failed
pred parentLive[s: Station] {
  some s.parent
  s.parentBeats < TIMEOUT
}

pred backupLive[s: Station] {
  some s.backup
  s.backupBeats < TIMEOUT
}

// -- What a station actually broadcasts this tick:
// -- none if it has failed, its stormInfo otherwise
// fun broadcasts[s: Station]: lone StormBool {
//   (some s.failed) => none else s.stormInfo
// }

-- what a station actually broadcasts this tick
fun broadcasts[s: Station]: lone StormBool {
  { b: StormBool | 
    -- Condition 1: Station must not be failed
    no s.failed and (
      -- Case A: Not Byzantine - b must match the actual info
      (no s.isByzantine and b = s.stormInfo) 
      or
      -- Case B: Byzantine and StormTrue - b must be StormFalse
      (some s.isByzantine and s.stormInfo = StormTrue and b = StormFalse)
      or
      -- Case C: Byzantine and StormFalse - b must be StormTrue
      (some s.isByzantine and s.stormInfo = StormFalse and b = StormTrue)
    )
  }
}

-- determines the majority consensus from a given set of stations
fun majorityVote[group: set Station]: lone StormBool {
  let tVotes = {p: group | broadcasts[p] = StormTrue},
      fVotes = {p: group | broadcasts[p] = StormFalse} |
    (add[#tVotes, #tVotes] > #group) => StormTrue else
    (add[#fVotes, #fVotes] > #group) => StormFalse else
    none
}

pred validStations {
  all s: Station | {
    s not in s.parent
    s not in Station.(s.backup) -- a node cannot be its own backup mapping output
    (some s.originatesInfo) implies no s.parent
    (no s.originatesInfo)   implies #(s.parent) >= 3
    -- always true majority (odd number)
    -- max parents is 6, so valid odds are 3 or 5
    (no s.originatesInfo)   implies (#(s.parent) = 3 or #(s.parent) = 5) 
    (no s.originatesInfo)   implies {
      some orig: Station | {
        some orig.originatesInfo
        s in orig.^~parent
      }
    }
    
    -- every child node has at least one backup assigned to one of its parents
    (some s.parent) implies {
      some p: s.parent | some s.backup[p]
    }
    
    -- constraints for the backup partial function
    all p: Station | some s.backup[p] implies p in s.parent
    all p: s.parent | some s.backup[p] implies {
      s.backup[p] != s
      s.backup[p] not in s.parent -- parent cannot be a backup for any parent of that child
    }
  }

  -- nodes cannot be parents/backups to each other
  all disj s1, s2: Station | {
    s1 in s2.parent implies s2 not in s1.parent
    s1 in Station.(s2.backup) implies s2 not in Station.(s1.backup)
    s1 in s2.parent implies s2 not in Station.(s1.backup)
  }
}

pred init {
  all s: Station | (some s.originatesInfo) implies s.stormInfo = s.originatesInfo
  all s: Station | (no s.originatesInfo)  implies no s.stormInfo
  all s: Station | {
    s.parentBeats = 0
    s.backupBeats = 0
    no s.lostOriginator
    no s.failed             -- nothing failed at t=0
  }
}

-- failures are sticky: once failed, always failed
pred failuresSticky {
  all s: Station | some s.failed implies some s.failed'
}

-- at most one originator can fail (keeps traces readable)
pred boundedFailures {
  lone s: Station | some s.originatesInfo and some s.failed
}

pred updateMissedBeats {
  all s: Station | (no s.originatesInfo) implies {

    -- parent beat: reset if parent is alive AND has stormInfo
    (some s.parent and some majorityVote[s.parent]) implies
      s.parentBeats' = 0
    (some s.parent and no majorityVote[s.parent]) implies {
      (s.parentBeats < TIMEOUT)
        implies s.parentBeats' = add[s.parentBeats, 1]
      (s.parentBeats >= TIMEOUT)
        implies s.parentBeats' = TIMEOUT
    }
    (no s.parent) implies s.parentBeats' = s.parentBeats

    -- backup beat: reset if backup is alive AND has stormInfo
    (some s.backup and some majorityVote[Station.(s.backup)]) implies
      s.backupBeats' = 0
    (some s.backup and no majorityVote[Station.(s.backup)]) implies {
      (s.backupBeats < TIMEOUT)
        implies s.backupBeats' = add[s.backupBeats, 1]
      (s.backupBeats >= TIMEOUT)
        implies s.backupBeats' = TIMEOUT
    }
    (no s.backup) implies s.backupBeats' = s.backupBeats
  }

  all s: Station | (some s.originatesInfo) implies {
    s.parentBeats' = s.parentBeats
    s.backupBeats' = s.backupBeats
  }
}

fun liveSource[s: Station]: set Station {
  { src: Station | 
    -- Case 1: Parent is live, so the source must be in the parent set
    (parentLive[s] => src in s.parent) 
    and
    -- Case 2: Parent is NOT live but backup IS live, so source is the backup mapping
    ((no s.parent or not parentLive[s]) and backupLive[s] => src in Station.(s.backup))
    and
    -- Case 3: If neither is live, no station should satisfy the conditions (returns none)
    ((not parentLive[s] and not backupLive[s]) => no src)
  }
}

-- ── Failsafe stub ─────────────────────────────────────────────────────────────
pred failsafe[s: Station] {
  -- Case 1: Backup is alive and has info → reroute to backup
  (backupLive[s] and some majorityVote[Station.(s.backup)]) implies { -- Parent went silent but backup is healthy, so the station reroutes. 
    s.stormInfo' = majorityVote[Station.(s.backup)]
    s.passStormInfo = Station.(s.backup)
    no s.lostOriginator'
  }

  -- Case 2: Backup exists but also has no info or is failed → freeze, stay lost
  (some s.backup and no majorityVote[Station.(s.backup)]) implies { -- backup exists but is also unreachable or uninformed
    s.stormInfo' = s.stormInfo
    one s.lostOriginator'
  }

  -- Case 3: No backup at all → freeze, stay lost
  (no s.backup) implies {
    s.stormInfo' = s.stormInfo
    one s.lostOriginator'
  }
}

pred defineStormEdges {
  // -- Originators: stormInfo unchanged, but failed ones broadcast nothing
  // all s: Station | (some s.originatesInfo) implies {
  //   s.stormInfo'      = s.stormInfo   -- internal value stays
  //   s.passStormInfo = none
  //   no s.lostOriginator'
  // }

  -- split originator block into healthy vs failed
  -- healthy originators leave failed' unconstrained (nondeterministic failure)
  all s: Station | (some s.originatesInfo and no s.failed) implies {
    s.stormInfo'      = s.stormInfo
    s.passStormInfo = none
    no s.lostOriginator'
    -- failed' intentionally unconstrained: allows failure mid-trace
  }

  -- failed originators stay failed and frozen
  all s: Station | (some s.originatesInfo and some s.failed) implies {
    s.stormInfo'      = s.stormInfo
    s.passStormInfo = none
    no s.lostOriginator'
    some s.failed'
  }

  failuresSticky
  updateMissedBeats

  all s: Station | (no s.originatesInfo) implies {
    s.passStormInfo = liveSource[s]

    -- failed non-originators freeze too
    some s.failed implies {
      s.stormInfo'      = s.stormInfo
      no s.lostOriginator'
    }

    no s.failed implies {
      let src = liveSource[s] | {

        -- Normal: live source is alive and has info
        (some src and some majorityVote[src]) implies {
          s.stormInfo'     = majorityVote[src]
          no s.lostOriginator'
        }

        -- Waiting: live source exists but failed or no info yet
        (some src and no majorityVote[src]) implies {
          s.stormInfo'     = s.stormInfo
          no s.lostOriginator'
        }

        -- Isolated: no live source
        no src implies {
          s.stormInfo' = s.stormInfo

          // -- Originator timed out → call failsafe
          // (some s.parent and some s.parent.originatesInfo
          //  and s.parentBeats >= TIMEOUT) implies {
          //   one s.lostOriginator'
          //   failsafe[s]
          // }

          // -- Regular node timed out → no escalation
          // (some s.parent and no s.parent.originatesInfo) implies {
          //   no s.lostOriginator'
          // }


           -- FIX 2: any timeout triggers lostOriginator + failsafe
          -- originator-specific distinction preserved in comment for later
          (s.parentBeats >= TIMEOUT) implies {
            one s.lostOriginator'
            failsafe[s]
            -- NOTE: to restore originator distinction later, check:
            -- some (s.parent & {p: Station | some p.originatesInfo})
          }

          (s.parentBeats < TIMEOUT) implies {
            no s.lostOriginator'
          }
        }
      }
    }
  }
}

pred traces {
  validStations
  init
  always defineStormEdges
  boundedFailures
  -- force failure to occur during the trace
  eventually (some s: Station | some s.originatesInfo and some s.failed)
}

run {
  traces
  some disj s1, s2: Station | {
    some s1.originatesInfo
    some s2.originatesInfo
  }
  some s: Station | some s.originatesInfo and eventually some s.failed
  
  -- at least one node is actively Byzantine
  some s: Station | some s.isByzantine 
  
  some s: Station | eventually s.parentBeats > 0
} for exactly 10 Station, 5 Int