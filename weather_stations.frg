#lang forge/temporal
option run_sterling "layout.cnd"

option min_tracelength 2
option max_tracelength 15

abstract sig StormBool {}
one sig StormFalse, StormTrue extends StormBool {}

sig Station {
  parent:          lone Station,
  backup:          lone Station,
  passStormComing: lone Station,
  originatesInfo:  lone StormBool,

  var stormInfo:      lone StormBool,
  var parentBeats:    one Int,
  var backupBeats:    one Int,
  var lostOriginator: lone StormBool,
  var failed:         lone StormBool   -- NEW: station has gone silent
}

one sig Georgetown, Philadelphia, NewYork,
        NewOrleans, Denver, LosAngeles, Dallas extends Station {}

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

pred validStations {
  all s: Station | {
    s.parent != s
    (some s.originatesInfo) implies s.parent = none
    (no s.originatesInfo)   implies one s.parent
    (no s.originatesInfo)   implies {
      some orig: Station | {
        some orig.originatesInfo
        s in orig.^~parent
      }
    }
    some s.backup implies s.backup != s.parent
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

-- Failures are sticky: once failed, always failed
pred failuresSticky {
  all s: Station | some s.failed implies some s.failed'
}

-- At most one originator can fail (keeps traces readable)
pred boundedFailures {
  lone s: Station | some s.originatesInfo and some s.failed
}

pred updateMissedBeats {
  all s: Station | (no s.originatesInfo) implies {

    -- Parent beat: reset if parent is alive AND has stormInfo
    (some s.parent and no s.parent.failed and some s.parent.stormInfo) implies
      s.parentBeats' = 0
    (some s.parent and (some s.parent.failed or no s.parent.stormInfo)) implies {
      (s.parentBeats < TIMEOUT)
        implies s.parentBeats' = add[s.parentBeats, 1]
      (s.parentBeats >= TIMEOUT)
        implies s.parentBeats' = TIMEOUT
    }
    (no s.parent) implies s.parentBeats' = s.parentBeats

    -- Backup beat: reset if backup is alive AND has stormInfo
    (some s.backup and no s.backup.failed and some s.backup.stormInfo) implies
      s.backupBeats' = 0
    (some s.backup and (some s.backup.failed or no s.backup.stormInfo)) implies {
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

fun liveSource[s: Station]: lone Station {
  (parentLive[s]) => s.parent
  else (not parentLive[s] and backupLive[s]) => s.backup
  else none
}

-- ── Failsafe stub ─────────────────────────────────────────────────────────────
pred failsafe[s: Station] {
  -- Case 1: Backup is alive and has info → reroute to backup
  (backupLive[s] and some s.backup.stormInfo and no s.backup.failed) implies { -- Parent went silent but backup is healthy, so the station reroutes. 
    s.stormInfo' = s.backup.stormInfo
    s.passStormComing = s.backup 
    no s.lostOriginator'
  }

  -- Case 2: Backup exists but also has no info or is failed → freeze, stay lost
  (some s.backup and (some s.backup.failed or no s.backup.stormInfo)) implies { -- backup exists but is also unreachable or uninformed
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
  -- Originators: stormInfo unchanged, but failed ones broadcast nothing
  all s: Station | (some s.originatesInfo) implies {
    s.stormInfo'      = s.stormInfo   -- internal value stays
    s.passStormComing = none
    no s.lostOriginator'
  }

  failuresSticky
  updateMissedBeats

  all s: Station | (no s.originatesInfo) implies {
    s.passStormComing = liveSource[s]

    -- failed non-originators freeze too
    some s.failed implies {
      s.stormInfo'      = s.stormInfo
      no s.lostOriginator'
    }

    no s.failed implies {
      let src = liveSource[s] | {

        -- Normal: live source is alive and has info
          (some src and no src.failed and some src.stormInfo) implies {
            s.stormInfo'     = src.stormInfo
            no s.lostOriginator'
          }

          -- Waiting: live source exists but failed or no info yet
          (some src and (some src.failed or no src.stormInfo)) implies {
            s.stormInfo'     = s.stormInfo
            no s.lostOriginator'
          }

        -- Isolated: no live source
        no src implies {
          s.stormInfo' = s.stormInfo

          -- Originator timed out → call failsafe
          (some s.parent and some s.parent.originatesInfo
           and s.parentBeats >= TIMEOUT) implies {
            one s.lostOriginator'
            failsafe[s]
          }

          -- Regular node timed out → no escalation
          (some s.parent and no s.parent.originatesInfo) implies {
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
}

run {
  traces
  some disj s1, s2: Station | {
    some s1.originatesInfo
    some s2.originatesInfo
  }
  some s: Station | some s.originatesInfo and eventually some s.failed
  -- Weaker: just check the counter gets above 0
  some s: Station | eventually s.parentBeats > 0
} for exactly 7 Station, 5 Int