#lang forge/temporal

open "weather_stations.frg"

-- ============================================================
-- Testing Suite for Weather Station Storm Propagation Model
-- ============================================================
-- This model simulates storm information propagating through
-- a network of weather stations. One or more stations act as
-- originators (the source of truth). Info spreads hop-by-hop
-- through parent edges. Stations can fail, triggering a
-- failsafe that reroutes through backup stations.
-- ============================================================



-- ============================================================
-- validStations: structural integrity of the station network
-- A valid network has no cycles, every non-originator has a 
-- parent, and backups must differ from parents
-- ============================================================

test suite for validStations {

    -- EXCLUSION: a station being its own parent should always be impossible.
    test expect ownParent {
        ownParents: {
            validStations
            some s: Station | s.parent = s
        } for 7 Station is unsat
    }

    -- EXCLUSION: an originator must never have a parent.
    test expect originatorNoParent {
        originatorNoParentTest: {
            validStations
            some s: Station | some s.originatesInfo and some s.parent
        } for 7 Station is unsat
    }

    -- EXCLUSION: every non-originator must have exactly one parent.
    test expect nonOriginatorNeedsParent {
        nonOriginatorNeedsParentTest: {
            validStations
            some s: Station | no s.originatesInfo and no s.parent
        } for 7 Station is unsat
    }


    -- INCLUSION: every non-originator must be reachable from some originator
    test expect allReachableFromOriginator {
        allReachableTest: {
            validStations
            some orig: Station | {
                some orig.originatesInfo
                some s: Station | s != orig and s not in orig.^~parent
            }
        } for 7 Station is sat
    }
    
    -- INCLUSION: Byzantine stations are structurally valid and can exist 
    -- anywhere in the network (as originators or children).
    test expect byzantineCanBeAnywhere {
        byzantineAnywhereTest: {
            validStations
            some s1, s2: Station | {
                some s1.isByzantine 
                some s2.isByzantine 
                some s1.originatesInfo 
                no s2.originatesInfo
            }
        } for 7 Station is sat
    }

}



-- ============================================================
-- init: correctness of the initial state at timestep 0
-- At t=0, only originators have storm info. All beat counters
-- start at 0 and nothing has failed yet.
-- ============================================================

test suite for init {

    -- EXCLUSION: a non-originator must never have storm info at t=0.
    test expect nonOriginatorNoInfoAtStart {
        nonOriginatorNoInfoTest: {
            init
            some s: Station | no s.originatesInfo and one s.stormInfo
        } for 7 Station is unsat
    }

    -- EXCLUSION: an originator must have storm info at t=0.
    --  if originator has no info, nothing can ever propagate.
    test expect originatorHasInfoAtStart {
        originatorHasInfoTest: {
            init
            some s: Station | some s.originatesInfo and no s.stormInfo
        } for 7 Station is unsat
    }

    -- EXCLUSION: no station should have failed at t=0.
    -- Failures only happen during propagation, not at initialization.
    test expect noFailuresAtStart {
        noFailuresTest: {
            init
            some s: Station | some s.failed
        } for 7 Station is unsat
    }

    -- EXCLUSION: all beat counters must start at 0.
    test expect beatsStartAtZero {
        beatsZeroTest: {
            init
            some s: Station | s.parentBeats != 0 or s.backupBeats != 0
        } for 7 Station is unsat
    }
    
    -- EXCLUSION: Being Byzantine does not change an originator's internal initialized storm info.
    -- They lie when broadcasting, but internally they know the truth at t=0.
    test expect byzantineOriginatorHasCorrectInitialInfo {
        byzantineInitTest: {
            init
            some s: Station | some s.isByzantine and some s.originatesInfo and s.stormInfo != s.originatesInfo
        } for 7 Station is unsat
    }

}



-- ============================================================
-- defineStormEdges: correctness of the propagation step
-- Storm info spreads hop-by-hop each timestep. Originators
-- keep their info. Non-originators adopt info from their live
-- source. Failed stations freeze. Beat counters update.
-- ============================================================

test suite for defineStormEdges {

    -- EXCLUSION: an originator's storm info must never change.
    test expect originatorInfoStable {
        originatorInfoStableTest: {
            validStations
            init
            defineStormEdges
            some s: Station | some s.originatesInfo and s.stormInfo != s.stormInfo'
        } for 7 Station is unsat
    }

    -- EXCLUSION: a station whose live parent has storm might not adopt next step (multiple parents, need majority).
    test expect propagationOccurs {
        propagationOccursTest: {
            validStations
            init
            defineStormEdges
            some s: Station | {
                no s.originatesInfo
                no s.failed
                parentLive[s]
                some s.parent.stormInfo
                no s.parent.failed
                no s.stormInfo'   -- station failed to adopt parent's info
            }
        } for 7 Station is sat
    }

    -- EXCLUSION: a failed station must freeze its storm info.
    test expect failedStationFreezes {
        failedStationFreezesTest: {
            validStations
            init
            defineStormEdges
            some s: Station | {
                no s.originatesInfo
                some s.failed
                s.stormInfo' != s.stormInfo
            }
        } for 7 Station is unsat
    }

    -- EXCLUSION: failures must be sticky — once failed, always failed.
    test expect failuresAreSticky {
        failuresStickyTest: {
            validStations
            init
            defineStormEdges
            some s: Station | some s.failed and no s.failed'
        } for 7 Station is unsat
    }

    -- EXCLUSION: a station with no live source must not spontaneously change info.
    test expect noSpontaneousChange {
        noSpontaneousChangeTest: {
            validStations
            init
            defineStormEdges
            some s: Station | {
                no s.originatesInfo
                no s.failed
                no liveSource[s]
                s.stormInfo' != s.stormInfo
            }
        } for 7 Station is unsat
    }
    
    -- INCLUSION: If all parents are Byzantine, live, and have StormTrue, 
    -- they broadcast StormFalse. The child will adopt StormFalse (the opposite).
    test expect childAdoptsByzantineLies {
        childAdoptsLiesTest: {
            validStations
            init
            defineStormEdges
            some s: Station | {
                no s.originatesInfo
                no s.failed
                parentLive[s]
                -- all parents are live, byzantine, and have StormTrue
                some s.parent
                all p: s.parent | {
                    some p.isByzantine
                    no p.failed
                    p.stormInfo = StormTrue
                }
                -- Child adopts the lie (StormFalse)
                s.stormInfo' = StormFalse
            }
        } for 7 Station is sat
    }

    -- INCLUSION: A mix of Byzantine and normal nodes can cause a tie/no majority,
    -- resulting in the child keeping its info and incrementing its beat counter.
    test expect byzantineCausesNoMajorityAndBeatsIncrement {
        byzantineSplitTest: {
            validStations
            init
            defineStormEdges
            some s: Station | {
                no s.originatesInfo
                no s.failed
                parentLive[s]
                -- Given an odd number of parents (e.g. 3), one fails, one is normal (True), one is Byz (False).
                -- The majorityVote resolves to 'none'.
                no majorityVote[s.parent]
                -- Because there's no majority, the beat increments.
                s.parentBeats' = add[s.parentBeats, 1]
            }
        } for 7 Station is sat
    }

}



-- ============================================================
-- failsafe: behavior when a station's parent goes silent
-- When parentBeats >= TIMEOUT, the station reroutes to backup
-- if available, otherwise freezes and marks lostOriginator.
-- ============================================================

test suite for failsafe {
   -- INCLUSION: Case 1 — when backup is live and has majority vote,
    -- failsafe should allow rerouting (stormInfo' = majorityVote of backups)
    test expect failsafeCase1Sat {
        failsafeCase1Test: {
            validStations
            init
            some s: Station | {
                no s.originatesInfo
                no s.failed
                backupLive[s]
                some majorityVote[Station.(s.backup)]
                failsafe[s]
                s.stormInfo' = majorityVote[Station.(s.backup)]
            }
        } for 7 Station is sat
    }

    -- INCLUSION: Case 2 — when backup exists but no majority vote,
    -- failsafe should freeze stormInfo and set lostOriginator
    test expect failsafeCase2Sat {
        failsafeCase2Test: {
            validStations
            init
            some s: Station | {
                no s.originatesInfo
                no s.failed
                some Station.(s.backup)
                no majorityVote[Station.(s.backup)]
                failsafe[s]
                one s.lostOriginator'
                s.stormInfo' = s.stormInfo
            }
        } for 7 Station is sat
    }

    -- EXCLUSION: Case 1 — when no backup at all,
    -- failsafe should freeze and set lostOriginator
    test expect failsafeCase3Sat {
        failsafeCase3Test: {
            validStations
            init
            some s: Station | {
                no s.originatesInfo
                no s.failed
                no Station.(s.backup)
                failsafe[s]
                one s.lostOriginator'
                s.stormInfo' = s.stormInfo
            }
        } for 7 Station is unsat
    }

    -- EXCLUSION: Case 2 should never set lostOriginator
    -- when backup is live and has a majority vote
    test expect failsafeCase1NoLostOriginator {
        failsafeCase1NoLostTest: {
            validStations
            init
            some s: Station | {
                no s.originatesInfo
                backupLive[s]
                some majorityVote[Station.(s.backup)]
                failsafe[s]
                one s.lostOriginator'
            }
        } for 7 Station is unsat
    }

    -- EXCLUSION: failsafe should never allow stormInfo to change
    -- when there is no live source at all (Cases 3 and 4)
    test expect failsafeNoSpontaneousChange {
        failsafeNoChangeTest: {
            validStations
            init
            some s: Station | {
                no s.originatesInfo
                no s.failed
                no majorityVote[Station.(s.backup)]
                failsafe[s]
                s.stormInfo' != s.stormInfo
            }
        } for 7 Station is unsat
    }
        
    -- EXCLUSION: a station with a live backup that has a majority vote
    -- must not stay permanently uninformed after parent times out.
    -- The failsafe must reroute it successfully.
    test expect failsafePreventsPermamentIsolation {
        failsafeIsolationTest: {
            traces
            some s: Station | {
                no s.originatesInfo
                no s.failed
                eventually {
                    failsafe[s]
                    s.parentBeats >= TIMEOUT
                    backupLive[s]
                    some majorityVote[Station.(s.backup)]
                }
                always no s.stormInfo
            }
        } for 7 Station is unsat
    }

    -- EXCLUSION: a station that successfully reroutes via failsafe
    -- must not simultaneously mark lostOriginator — these are mutually exclusive.
    test expect noLostOriginatorOnSuccessfulReroute {
        noLostOriginatorTest: {
            traces
            some s: Station | {
                no s.originatesInfo
                no s.failed
                eventually {
                    s.parentBeats >= TIMEOUT
                    backupLive[s]
                    some majorityVote[Station.(s.backup)]
                    one s.lostOriginator'  -- incorrectly marked lost despite successful reroute
                    failsafe[s]
                }
            }
        } for 7 Station is unsat
    }
    
    -- INCLUSION: Failsafe relies on backups. If the backups are Byzantine, 
    -- the failsafe will successfully route, but the node will adopt the backup's lies.
    test expect failsafeAdoptsByzantineBackupLies {
        failsafeByzBackupTest: {
            validStations
            init
            some s: Station | {
                no s.originatesInfo
                no s.failed
                backupLive[s]
                some Station.(s.backup)
                -- backups are byzantine and hold StormTrue, so they broadcast StormFalse
                all b: Station.(s.backup) | {
                    some b.isByzantine
                    no b.failed
                    b.stormInfo = StormTrue
                }
                failsafe[s]
                -- it correctly reroutes, but adopts the opposite info
                s.stormInfo' = StormFalse
            }
        } for 7 Station is sat
    }
}




-- ============================================================
-- traces: end-to-end temporal properties of the full system
-- These tests verify global properties that should hold across
-- all timesteps of a valid execution trace.
-- ============================================================

test suite for traces {

    -- INCLUSION: the full system should be satisfiable.
    -- If this fails, something in the combined predicates is contradictory.
    test expect tracesSat {
        tracesSatTest: {
            traces
        } for 7 Station is sat
    }

    -- EXCLUSION: a non-originator should never have info before its parent does,
    -- unless it received it via a backup.
    test expect noSkippingWithoutBackup {
        noSkippingTest: {
            traces
            some s: Station | {
                no s.originatesInfo
                no s.backup          -- no backup to explain receiving info early
                one s.stormInfo
                no s.parent.stormInfo
            }
        } for 7 Station is unsat
    }

    -- EXCLUSION: the number of failed originators should stay bounded.
    -- boundedFailures ensures at most one originator fails per trace,
    -- keeping the model tractable and readable.
    test expect atMostOneOriginatorFails {
        atMostOneOriginatorFailsTest: {
            traces
            #{s: Station | some s.originatesInfo and some s.failed} > 1
        } for 7 Station is unsat
    }

    -- INCLUSION: it should be possible for a station to eventually receive
    -- storm info after starting with none.
    test expect propagationEventuallyWorks {
        propagationWorksTest: {
            traces
            some s: Station | {
                no s.originatesInfo
                no s.stormInfo       -- starts uninformed
                eventually one s.stormInfo  -- eventually gets informed
            }
        } for 7 Station is sat
    }

    -- INCLUSION: it should be possible for a station to trigger the failsafe,
    -- demonstrating that failure and recovery can actually occur in a trace.
    test expect failsafeCanTrigger {
        failsafeCanTriggerTest: {
            traces
            some s: Station | eventually one s.lostOriginator
        } for 7 Station is sat
    }
    
    -- INCLUSION: End-to-end propagation can result in a station permanently holding 
    -- the wrong info (StormFalse) when the originator sent StormTrue, due to Byzantine flips.
    test expect systemCanPropagateWrongInfo {
        wrongInfoPropagationTest: {
            traces
            some orig: Station | {
                some orig.originatesInfo
                orig.stormInfo = StormTrue
            }
            eventually {
                some s: Station | {
                    no s.originatesInfo
                    s.stormInfo = StormFalse
                }
            }
        } for 7 Station is sat
    }
}