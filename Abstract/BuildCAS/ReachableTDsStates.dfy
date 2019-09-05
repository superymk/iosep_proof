include "ReachableTDsStates_Utils.dfy"

predicate FindReachableActiveTDsStatesFromActiveTDsState_KParams_PreConditions(k_params:ReachableTDsKParams)
{
    FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params) &&

    (true)
}

// Returns all reachable snapshots of active TDs starting from the current 
// state of active TDs
function AllReachableActiveTDsStates(k:State) : set<TDs_Vals>
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))

    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id 
        // Requirements: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)

    requires IsValidState_TDsToAllStates(k)

    ensures forall dev_id2 :: IsDevID_SlimState(KToKParams(k).subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(KToKParams(k).subjects, KToKParams(k).hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(KToKParams(k).subjects, dev_id2).td_ids <= KToKParams(k).objs_td_ids
        // Property needed by the following properties
    ensures forall tds_state :: tds_state in AllReachableActiveTDsStates(k)
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
    ensures forall tds_state :: tds_state in AllReachableActiveTDsStates(k)
                ==> (ActiveTDsState(k) == tds_state || IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k),
                            AllActiveDevs(k), ActiveTDsState(k), tds_state))
    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (ActiveTDsState(k) == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k),
                             AllActiveDevs(k), ActiveTDsState(k), tds_state2))
                                                // ActiveTDsState(k) -->* tds_state2
                ==> tds_state2 in AllReachableActiveTDsStates(k)
{
    var tds_to_all_states := k.tds_to_all_states;
    assert AllActiveTDs(k) in tds_to_all_states;
    assert forall tds_state :: tds_state in tds_to_all_states[AllActiveTDs(k)]
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k);

    Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev_SlimState(k, KToKParams(k));

    set tds_state | tds_state in tds_to_all_states[AllActiveTDs(k)] &&
                    (ActiveTDsState(k) == tds_state || 
                        IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k),
                            AllActiveDevs(k), ActiveTDsState(k), tds_state))
                  :: tds_state
}

// Return all states of active TDs reachable from <tds_state>.
// If in all reachable TDs' states, any active TDs read by any active devices 
// have no invalid references to I/O objects, then returns true
// In other words, (1) Forall tds_state2 in <explored_tds_states'>,
// tds_state -->* tds_state2 ("-->" is direct TD write by an active device in 
// <active_devs>), and (2) (status == true) ==> (Forall tds_state2, 
// tds_state -->* tds_state2 ==> tds_state2 in <explored_tds_states'>)
method FindReachableActiveTDsStatesFromActiveTDsState(
    k_params:ReachableTDsKParams, ghost k_active_tds_all_states:set<TDs_Vals>,
    active_devs:set<Dev_ID>, tds_state:TDs_Vals, explored_tds_states:seq<set<TDs_Vals>> 
) returns (explored_tds_states':seq<set<TDs_Vals>>, status:bool)
    requires FindReachableActiveTDsStatesFromActiveTDsState_KParams_PreConditions(k_params)

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement 1
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
        // Requirement 2: Forall tds_state2 in E[0..|E|], tds_state -->* tds_state2
    requires |explored_tds_states| >= 1 && explored_tds_states[0] == {tds_state}
        // Requirement 3: E0 == {tds_state}
    requires (|explored_tds_states| > 1)
              ==> (forall tds_state1, tds_state2 :: 
                        tds_state1 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) && 
                        TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                        (exists dev_id :: dev_id in active_devs && 
                            IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2))
                        ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0))
        // Requirement 4: Forall tds_state1 in E[0..|E|-1], and tds_state1 --> tds_state2 
        // ==> tds_state2 must be in E[0..|E|]
    requires (|explored_tds_states| > 1)
              ==>(forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0)
                        ==> (forall td_id2, dev_id :: 
                            dev_id in active_devs && 
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            td_id2 in k_params.objs_td_ids &&
                            ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                                // For all active TDs can be read by an active device
                            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)))
        // Requirement 5: Forall tds_state2 in E[0..|E|-1], any TDs can be read 
        // by an active device have no invalid references to I/O objects
    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
                ==> tds_state2 in k_active_tds_all_states
        // Requirement: k_active_tds_all_states includes all states of the active TDs
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Requirement 7: If hardcoded TDs are in E[0..|E|], their values are always from <k_params.hcoded_tds>

    ensures forall td_id2 :: td_id2 in k_params.all_active_tds
                ==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Property needed by property 6
    ensures |explored_tds_states'| >= 1 && explored_tds_states'[0] == {tds_state}
        // Property 1: After exploring TDs' states, the input TDs' state  
        // (<tds_state>) is always in <explored_tds_states'>
    ensures |explored_tds_states| <= |explored_tds_states'| &&
            explored_tds_states'[..|explored_tds_states|] == explored_tds_states
        // Property 2: The exploration only appends the new TDs' states at the  
        // end of <explored_tds_states>    
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Property 3: Forall tds_state2 in explored_tds_states', they include 
        // all active TDs in the I/O system
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
        // Property 4: Forall tds_state2 in explored_tds_states', tds_state -->* tds_state2
    ensures (status == true)
                ==> (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == 
                                          k_params.all_active_tds &&
                        (tds_state2 == tds_state || 
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
                                                    // tds_state -->* tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states', 0))
        // Property 5: Forall tds_state2, tds_state -->* tds_state2 ==> tds_state2 in explored_tds_states'
    ensures (status == true)
                <==> (forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                    ==> MapGetKeys<TD_ID, TD_Val>(tds_state2) == 
                            k_params.all_active_tds &&
                        (forall td_id2, dev_id :: 
                            dev_id in active_devs && 
                                // The device (<dev_id>) is active
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)))
    ensures status <==> AllReachableActiveTDsStatesAreSecure(k_params, active_devs, GetExploredTDsStates(explored_tds_states', 0))
        // Property 6: Any active TDs read by any active devices have no invalid
        // references to I/O objects
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Property 7: If hardcoded TDs are in E[0..|E|], their values are always from <k_params.hcoded_tds>
    
    decreases |k_active_tds_all_states - GetExploredTDsStates(explored_tds_states, 0)|
{
    explored_tds_states', status := FindReachableActiveTDsStatesFromActiveTDsState_Internal(k_params, k_active_tds_all_states,
        active_devs, tds_state, explored_tds_states);

    if(status == true)
    {
        Lemma_ProveAllReachableActiveTDsStates(k_params, active_devs, GetExploredTDsStates(explored_tds_states', 0));
    }
}

method FindReachableActiveTDsStatesFromActiveTDsState_Internal(
    k_params:ReachableTDsKParams, ghost k_active_tds_all_states:set<TDs_Vals>,
    active_devs:set<Dev_ID>, tds_state:TDs_Vals, explored_tds_states:seq<set<TDs_Vals>> 
) returns (explored_tds_states':seq<set<TDs_Vals>>, status:bool)
    requires FindReachableActiveTDsStatesFromActiveTDsState_KParams_PreConditions(k_params)

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement 1
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
        // Requirement 2: Forall tds_state2 in E[0..|E|], tds_state -->* tds_state2
    requires |explored_tds_states| >= 1 && explored_tds_states[0] == {tds_state}
        // Requirement 3: E0 == {tds_state}
    requires (|explored_tds_states| > 1)
              ==> (forall tds_state1, tds_state2 :: 
                        tds_state1 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) && 
                        TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                        (exists dev_id :: dev_id in active_devs && 
                            IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2))
                        ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0))
        // Requirement 4: Forall tds_state1 in E[0..|E|-1], and tds_state1 --> tds_state2 
        // ==> tds_state2 must be in E[0..|E|]
    requires (|explored_tds_states| > 1)
              ==>(forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0)
                        ==> (forall td_id2, dev_id :: 
                            dev_id in active_devs && 
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            td_id2 in k_params.objs_td_ids &&
                            ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                                // For all active TDs can be read by an active device
                            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)))
        // Requirement 5: Forall tds_state2 in E[0..|E|-1], any TDs can be read 
        // by an active device have no invalid references to I/O objects
    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
                ==> tds_state2 in k_active_tds_all_states
        // Requirement: k_active_tds_all_states includes all states of the active TDs
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Requirement 7: If hardcoded TDs are in E[0..|E|], their values are always from <k_params.hcoded_tds>

    ensures forall td_id2 :: td_id2 in k_params.all_active_tds
                ==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Property needed by property 6
    ensures |explored_tds_states'| >= 1 && explored_tds_states'[0] == {tds_state}
        // Property 1: After exploring TDs' states, the input TDs' state  
        // (<tds_state>) is always in <explored_tds_states'>
    ensures |explored_tds_states| <= |explored_tds_states'| &&
            explored_tds_states'[..|explored_tds_states|] == explored_tds_states
        // Property 2: The exploration only appends the new TDs' states at the  
        // end of <explored_tds_states>    
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Property 3: Forall tds_state2 in explored_tds_states', they include 
        // all active TDs in the I/O system
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
        // Property 4: Forall tds_state2 in explored_tds_states', tds_state -->* tds_state2
    ensures (status == true)
                ==> (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == 
                                          k_params.all_active_tds &&
                        (tds_state2 == tds_state || 
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
                                                    // tds_state -->* tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states', 0))
        // Property 5: Forall tds_state2, tds_state -->* tds_state2 ==> tds_state2 in explored_tds_states'
    ensures (status == true)
                <==> (forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                    ==> MapGetKeys<TD_ID, TD_Val>(tds_state2) == 
                            k_params.all_active_tds &&
                        (forall td_id2, dev_id :: 
                            dev_id in active_devs && 
                                // The device (<dev_id>) is active
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)))
        // Property 6: Any active TDs read by any active devices have no invalid
        // references to I/O objects
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Property 7: If hardcoded TDs are in E[0..|E|], their values are always from <k_params.hcoded_tds>
    
    decreases |k_active_tds_all_states - GetExploredTDsStates(explored_tds_states, 0)|
{
    var to_explore_states:set<TDs_Vals> := {};
    var exploring_states := explored_tds_states[|explored_tds_states| - 1];
    var devs := SetToSeq<Dev_ID>(active_devs);
    var s;

    to_explore_states, s := FindReachableTDsStatesFromTDsState_GetToExploreStates(
        k_params, active_devs, tds_state, explored_tds_states);
    if(!s)
    {return explored_tds_states, false; }

    if (to_explore_states == {})
    {
        assert forall tds_state1, tds_state2 :: tds_state1 in explored_tds_states[|explored_tds_states| - 1] &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0);
        assert forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) && 
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0);

        Lemma_FindReachableTDsStatesFromTDsState_ToExploreStatesIsEmptyThenReachableStatesAreExplored(
            k_params, devs, explored_tds_states);
        assert forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states, 0) &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0);

        assert tds_state in GetExploredTDsStates(explored_tds_states, 0);
        Lemma_ReachableTDsStatesAreExplored(k_params, active_devs, explored_tds_states, tds_state);

        Lemma_FindReachableTDsStatesFromTDsState_ReachableStatesHaveValidRefsOnly(
            k_params, devs, explored_tds_states);

        return explored_tds_states, true;
    }
    else
    {
        var t_explored_states := SeqAppend<set<TDs_Vals>>(explored_tds_states, to_explore_states);

        Lemma_ExploredTDsStatesAfterAppendingIncludeOldExploredTDsStatesAndAddedExploreTDsStates(
            t_explored_states, explored_tds_states, to_explore_states);
        assert GetExploredTDsStates(t_explored_states, 0) == GetExploredTDsStates(explored_tds_states, 0) + to_explore_states;
        assert t_explored_states[..|t_explored_states| - 1] == explored_tds_states;

        assert forall tds_state1, tds_state2 :: tds_state1 in exploring_states &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states;
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds;
                    
        Lemma_FindReachableTDsStatesFromTDsState_Req2(
            k_params, 
            active_devs, tds_state, t_explored_states, explored_tds_states, to_explore_states);
        Lemma_FindReachableTDsStatesFromTDsState_Req4(
            k_params, 
            active_devs, exploring_states, t_explored_states, explored_tds_states, to_explore_states);
        Lemma_FindReachableTDsStatesFromTDsState_Req7(
            k_params, 
            active_devs, tds_state, t_explored_states, explored_tds_states, to_explore_states);

        assert forall tds_state1, tds_state2 :: 
                tds_state1 in GetExploredTDsStates(explored_tds_states, 0) && 
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id :: dev_id in active_devs && 
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2))
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) + to_explore_states;

        Lemma_FindReachableTDsStatesFromTDsState_ReachableStatesHaveValidRefsOnly(
            k_params, devs, explored_tds_states);
        Lemma_FindReachableTDsStatesFromTDsState_ProveTermination(
            k_active_tds_all_states, t_explored_states, explored_tds_states, to_explore_states);
        explored_tds_states', status := FindReachableActiveTDsStatesFromActiveTDsState_Internal(k_params, k_active_tds_all_states,
                                            active_devs, tds_state, t_explored_states);
        Lemma_TransitiveSubSequence<set<TDs_Vals>>(explored_tds_states', t_explored_states, explored_tds_states);
        if(status == false)
        {    return explored_tds_states', false; }
    }
}

method FindReachableTDsStatesFromTDsState_GetToExploreStates(
    k_params:ReachableTDsKParams,  
    active_devs:set<Dev_ID>, tds_state:TDs_Vals, explored_tds_states:seq<set<TDs_Vals>>
) returns (to_explore_states':set<TDs_Vals>, status:bool)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
        // Requirement 2: Forall tds_state2 in E[0..|E|], tds_state -->* tds_state2
    requires |explored_tds_states| >= 1 && explored_tds_states[0] == {tds_state}
        // Requirement 3: E0 == {tds_state}
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Requirement 4: If hardcoded TDs are in E[0..|E|], their values are always from <k_params.hcoded_tds>

    ensures (status == true)
                ==> (forall tds_state2 :: tds_state2 in to_explore_states'
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds)
    ensures (status == true)
                ==> (forall tds_state2 :: tds_state2 in to_explore_states'
                    ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2)))
    ensures (status == true)
                ==> (forall tds_state1, tds_state2 :: tds_state1 in explored_tds_states[|explored_tds_states| - 1] &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in active_devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states') 
    ensures (status == true)
                ==> GetExploredTDsStates(explored_tds_states, 0) * to_explore_states' == {}

    ensures (status == true)
                <==> (forall tds_state2 :: tds_state2 in explored_tds_states[|explored_tds_states| - 1]
                    ==> MapGetKeys<TD_ID, TD_Val>(tds_state2) == 
                            k_params.all_active_tds &&
                        (forall td_id2, dev_id2 :: 
                        dev_id2 in active_devs && 
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id2, td_id2)
                            // For all active TDs can be read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)))
    ensures (status == true)
                ==> (forall tds_state2 :: tds_state2 in to_explore_states'
                        ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2))
{
    var to_explore_states:set<TDs_Vals> := {};
    var exploring_states := explored_tds_states[|explored_tds_states| - 1];
    var exploring_states_seq := SetToSeq<TDs_Vals>(exploring_states);
    var devs := SetToSeq<Dev_ID>(active_devs);
    var i := 0;
    var input_explored_states := GetExploredTDsStates(explored_tds_states, 0);

    assert forall dev_id2 :: dev_id2 in devs <==> dev_id2 in active_devs;
    while (i < |devs|)
        invariant i <= |devs|

        invariant forall tds_state2 :: tds_state2 in to_explore_states
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
                    // Invariant 2
        invariant forall tds_state2 :: tds_state2 in to_explore_states
                    ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
                    // Invariant 3
        
        invariant forall tds_state1, tds_state2 :: tds_state1 in exploring_states &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in devs[..i] &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states
                    // Invariant 4
        invariant input_explored_states * to_explore_states == {}
                    // Invariant 5
        invariant forall tds_state2 :: tds_state2 in exploring_states
                    ==> (forall td_id2, dev_id2 :: 
                        dev_id2 in devs[..i] && 
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id2, td_id2)
                            // For all active TDs can be read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
                    // Invariant 6
        invariant forall tds_state2 :: tds_state2 in to_explore_states
                    ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
                    // Invariant 7
    {
        var dev_id := devs[i];
        var tds_states_dev, s := FindAllActiveTDsStatesByDev(k_params, exploring_states_seq, dev_id);
        var old_to_explore_states;
        assert forall dev_id2 :: dev_id2 in devs[..i+1] ==> dev_id2 in active_devs;
        assert devs[..i+1] == devs[..i] + [dev_id];

        if(!s)
        {    return {}, false; }

        var unexplored_states := tds_states_dev - input_explored_states;
        Lemma_UnExploredStatesHasNoIntersectionWithInputExploredStates(
            tds_states_dev, unexplored_states, input_explored_states);

        assert (forall known_tds_state, td_id2 :: 
            known_tds_state in exploring_states_seq && 
            td_id2 in TDsStateGetTDIDs(known_tds_state) &&
            td_id2 in k_params.objs_td_ids &&
            ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
            CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, td_id2)
                // For all active TDs can be read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, known_tds_state, td_id2));

        assert forall tds_state2 :: tds_state2 in unexplored_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2);
        
        Lemma_FindReachableTDsStatesFromTDsState_LoopInv2(
            k_params,
            explored_tds_states, to_explore_states, unexplored_states);
        Lemma_FindReachableTDsStatesFromTDsState_LoopInv3(
            k_params, 
            dev_id, active_devs, tds_state, explored_tds_states, exploring_states, tds_states_dev, unexplored_states);
        Lemma_FindAllActiveTDsStatesByDev_TDsStatesReachedInOneStepAreReturned(
            k_params, 
            dev_id, exploring_states, tds_states_dev);
        Lemma_FindReachableTDsStatesFromTDsState_LoopInv4(
            k_params, 
            dev_id, active_devs, devs[..i+1], devs[..i],
            tds_state, explored_tds_states, 
            exploring_states, tds_states_dev, unexplored_states, to_explore_states);
        Lemma_FindReachableTDsStatesFromTDsState_LoopInv5(to_explore_states, unexplored_states, input_explored_states);
        
        Lemma_FindReachableTDsStatesFromTDsState_LoopInv6(
            k_params, 
            devs[..i+1], devs[..i], dev_id, exploring_states);
        Lemma_FindReachableTDsStatesFromTDsState_LoopInv7(
            k_params,
            explored_tds_states, to_explore_states, unexplored_states);
        
        old_to_explore_states := to_explore_states;
        to_explore_states := SetConcat<TDs_Vals>(old_to_explore_states, unexplored_states);
        
        i := i + 1;
    }

    return to_explore_states, true;
}

predicate IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(
    k_params:ReachableTDsKParams,
    active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
{
    (forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids) &&
    (forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids) &&
    (forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids) &&
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    (forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL) &&
        // Requirement: <k_params.all_active_tds> holds all active TDs
    (MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)) &&
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    (TDsStateGetTDIDs(from_tds_state) == k_params.all_active_tds) &&
    (TDsStateGetTDIDs(to_tds_state) == k_params.all_active_tds) &&
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs
    (forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL) &&
        // Requirement: The devices in <active_devs> must be active
    (forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids)
}

// Return if a set of active devices (<active_devs>) can read and produce  
// states of active TDs in chain, in order to modify <from_tds_state> to be 
// <to_tds_state>. This is noted as from_tds_state -->1+ to_tds_state.
// Consequently, from_tds_state -->* to_tds_state is defined as:
// (from_tds_state == to_tds_state) || (from_tds_state -->1+ to_tds_state)
function IsActiveTDsStateReachActiveTDsStateInChain(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
) : bool
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(
                    k_params,
                    active_devs, from_tds_state, to_tds_state)

    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state)
            <==>
            IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, active_devs, from_tds_state, to_tds_state) &&
            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state)

    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state) == true
                <==> (exists tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> ::
                        |tds_states| >= 2 && 
                        (forall tds_state2 :: tds_state2 in tds_states 
                            ==> TDsStateGetTDIDs(tds_state2) == 
                                k_params.all_active_tds) &&
                        |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                        tds_states[|tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
                        tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
                        (forall i :: 0<=i<|tds_states| - 1 
                            ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1])))
                                                            // tds_states[i] -->  tds_states[i+1]
{
    exists tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> ::
            |tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds) &&
            |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
            tds_states[|tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
            tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]))
                                                // tds_states[i] -->  tds_states[i+1]
}

predicate IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
{
    (forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids) &&
    (forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids) &&
    (forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids) &&
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    (forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL) &&
        // Requirement: <k_params.all_active_tds> holds all active TDs
    (MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)) &&
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    (TDsStateGetTDIDs(from_tds_state) == k_params.all_active_tds) &&
    (TDsStateGetTDIDs(to_tds_state) == k_params.all_active_tds) &&
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs
    (IsDevID_SlimState(k_params.subjects, dev_id)) &&
    (SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL) &&
        // Requirement: The device must be active
    (DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)) &&
    (IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids) &&

    (true)
}

// Return if the active device (<dev_id>) can issue TD writes and produce the 
// result state of active TDs <to_tds_state>, by reading the active TDs' state
// <from_tds_state>
// This is noted as from_tds_state --> to_tds_state
function IsActiveTDsStateReachActiveTDsStateInOneStep(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
) : bool
    requires IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(
                k_params, 
                dev_id, from_tds_state, to_tds_state)

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_tds_state, to_tds_state)
                <==> IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, from_tds_state, TDsStateDiff(to_tds_state, from_tds_state))
{
     IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, from_tds_state, TDsStateDiff(to_tds_state, from_tds_state))
}




//******** Utility Functions ********//
// Returns all states of active TDs recorded in <explored_tds_states> from the  
// index <lvl> to the end of the sequence
function method GetExploredTDsStates(explored_tds_states:seq<set<TDs_Vals>>, lvl:int) : set<TDs_Vals>
    requires 0 <= lvl <= |explored_tds_states|

    ensures forall i :: lvl <= i <|explored_tds_states|
                ==> explored_tds_states[i] <= GetExploredTDsStates(explored_tds_states, lvl)
    ensures forall td_id2 :: td_id2 in GetExploredTDsStates(explored_tds_states, lvl)
                <==> exists i :: lvl <= i <|explored_tds_states| && td_id2 in explored_tds_states[i]
    ensures explored_tds_states == [] 
                ==> GetExploredTDsStates(explored_tds_states, lvl) == {}

    decreases |explored_tds_states| - lvl
{
    if(lvl == |explored_tds_states|) then
        {}
    else
        explored_tds_states[lvl] + GetExploredTDsStates(explored_tds_states, lvl + 1)
}




//******** Utility Lemmas ********//
lemma Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(tds:TDs_Vals)
    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates([{tds}], 0)
                ==> (tds == tds_state2)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ProveAllReachableActiveTDsStates(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, reachable_tds_states:set<TDs_Vals>
)
    requires FindReachableActiveTDsStatesFromActiveTDsState_KParams_PreConditions(k_params)

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in reachable_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: Each known TDs' state includes all active TDs

    requires (forall tds_state2 :: tds_state2 in reachable_tds_states
        ==> MapGetKeys<TD_ID, TD_Val>(tds_state2) == 
                k_params.all_active_tds &&
            (forall td_id2, dev_id :: 
                dev_id in active_devs && 
                    // The device (<dev_id>) is active
                td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                    // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)))

    ensures AllReachableActiveTDsStatesAreSecure(k_params, active_devs, reachable_tds_states)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsActiveTDsStateReachActiveTDsStateInChain_PostConditions(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(
                    k_params,
                    active_devs, from_tds_state, to_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInChain(
                    k_params,
                    active_devs, from_tds_state, to_tds_state)

    ensures exists tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> ::
                    |tds_states| >= 2 && 
                    (forall tds_state2 :: tds_state2 in tds_states 
                        ==> TDsStateGetTDIDs(tds_state2) == 
                            k_params.all_active_tds) &&
                    |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                    tds_states[|tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
                    tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
                    (forall i :: 0<=i<|tds_states| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]))
    ensures exists tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> ::
                    |tds_states| >= 2 && 
                    (forall tds_state2 :: tds_state2 in tds_states 
                        ==> TDsStateGetTDIDs(tds_state2) == 
                            k_params.all_active_tds) &&
                    |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                    tds_states[|tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
                    tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
                    (forall i :: 0<=i<|tds_states| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, devs[i], tds_states[i], tds_states[i+1]) &&
                            IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsActiveTDsStateReachActiveTDsStateInChain_PostConditions_ReturnVals(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
) returns (result_tds_states:seq<TDs_Vals>, result_devs:seq<Dev_ID>)
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, active_devs, from_tds_state, to_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state)

    ensures  |result_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in result_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == 
                        k_params.all_active_tds) &&
                |result_devs| == |result_tds_states| - 1 && (forall dev_id2 :: dev_id2 in result_devs ==> dev_id2 in active_devs) &&
                result_tds_states[|result_tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
                result_tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
                (forall i :: 0<=i<|result_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, result_devs[i], result_tds_states[i], result_tds_states[i+1]))
{
    // Dafny can automatically prove this lemma
    var tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> :| // 191
            |tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds) &&
            |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
            tds_states[|tds_states| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
            tds_states[0] == from_tds_state && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]));
    
    result_tds_states := tds_states;
    result_devs := devs;
}

lemma Lemma_IsActiveTDsStateReachActiveTDsStateInChain_PreConditionsCanBeEliminated(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, active_devs, from_tds_state, to_tds_state)

    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state)
            <==>
            IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, active_devs, from_tds_state, to_tds_state) &&
            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_tds_state, to_tds_state)
{
    // Dafny can automatically prove this lemma
}

// Lemma: If <new_explored_states> is <old_explored_states> appended with 
// <add_explore_states>, then: GetExploredTDs(new_explored_tds, 0) == 
// GetExploredTDs(old_explored_states, 0) + add_explore_states
lemma Lemma_ExploredTDsStatesAfterAppendingIncludeOldExploredTDsStatesAndAddedExploreTDsStates(
    new_explored_states:seq<set<TDs_Vals>>, old_explored_states:seq<set<TDs_Vals>>, add_explore_states:set<TDs_Vals>
)
    requires new_explored_states == SeqAppend<set<TDs_Vals>>(old_explored_states, add_explore_states)
    ensures GetExploredTDsStates(new_explored_states, 0) == GetExploredTDsStates(old_explored_states, 0) + add_explore_states
{
    // Dafny can prove this lemma automatically
}

lemma Lemma_ExploredTDsStatesCanBeSeparated(explored_tds_states:seq<set<TDs_Vals>>)
    requires |explored_tds_states| > 0
    ensures GetExploredTDsStates(explored_tds_states, 0) == GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) + 
        explored_tds_states[|explored_tds_states| - 1]
{
    var all_seq := explored_tds_states;
    var sub_seq := explored_tds_states[..|explored_tds_states| - 1];
    var last_elem := explored_tds_states[|explored_tds_states| - 1];
    assert all_seq == SeqAppend<set<TDs_Vals>>(sub_seq, last_elem);

    // Dafny can automatically verify the following assertion
    assert GetExploredTDsStates(all_seq, 0) == GetExploredTDsStates(sub_seq, 0) + last_elem;
}

// Lemma: If tds_stateA -->* tds_stateB, tds_stateB --> tds_stateC, then
// tds_stateA -->* tds_stateC
lemma Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, active_devs:set<Dev_ID>,
    tds_stateA:TDs_Vals, tds_stateB:TDs_Vals, tds_stateC:TDs_Vals
)
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires dev_id in active_devs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires TDsStateGetTDIDs(tds_stateA) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_stateB) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_stateC) == k_params.all_active_tds

    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_stateA, tds_stateB)
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_stateB, tds_stateC)

    ensures  IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_stateA, tds_stateC)
{
    forall tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> | (|tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds) &&
            |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
            tds_states[|tds_states| - 1] == tds_stateB && // last TDs' state is the <to_tds_state>
            tds_states[0] == tds_stateA && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1])))
        ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_stateA, tds_stateC)
    {
        var tds_diff := TDsStateDiff(tds_stateC, tds_stateB);
        var tds_states_new := SeqAppend<TDs_Vals>(tds_states, tds_stateC);
        var devs_new := SeqAppend<Dev_ID>(devs, dev_id);
        Lemma_SequenceHighlightLastElemOfSubSeq(tds_states_new, tds_states);
        Lemma_SequenceHighlightLastElemOfSubSeq(devs_new, devs);

        assert |tds_states_new| >= 2 && 
                    (forall tds_state2 :: tds_state2 in tds_states_new 
                        ==> TDsStateGetTDIDs(tds_state2) == 
                            k_params.all_active_tds) &&
                    |devs_new| == |tds_states_new| - 1 && (forall dev_id2 :: dev_id2 in devs_new ==> dev_id2 in active_devs) &&
                    tds_states_new[|tds_states_new| - 1] == tds_stateC && // last TDs' state is the <to_tds_state>
                    tds_states_new[0] == tds_stateA; // first TDs' state is the <from_tds_state>

        // Prove for i in [0, |tds_states_new| - 1), IsActiveTDsStateReachActiveTDsStateInOneStep for successive TDs' states
        assert forall i :: 0<=i<|tds_states_new| - 2 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1]);
        
        assert tds_stateB == tds_states_new[|tds_states_new| - 2];
        assert tds_stateC == tds_states_new[|tds_states_new| - 1];
        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_stateB, tds_stateC);
        assert devs_new[|devs_new|-1] == dev_id;

        Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain_Private(
            k_params, dev_id, active_devs, tds_stateA, tds_stateB, tds_stateC,
            tds_states_new, devs_new);

        assert forall i :: 0<=i<|tds_states_new| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1]); 

        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_stateA, tds_stateC);
    }
}

// Lemma: For each TDs' state (tds_state2), if exists tds_state1 in <from_states>, 
// and IsActiveTDsStateReachActiveTDsStateInOneStep is true for the two states, then 
// tds_state2 must be in <to_states>
lemma Lemma_FindAllActiveTDsStatesByDev_TDsStatesReachedInOneStepAreReturned(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, from_states:set<TDs_Vals>, to_states:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in from_states + to_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: <from_states> and <to_states> must includes all active TDs 

    requires forall tds_state1, tds_diff:map<TD_ID, TD_Val> :: 
                    tds_state1 in from_states && 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(tds_state1) &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, tds_state1, tds_diff)
                    ==> (exists tds_state2 :: tds_state2 in to_states && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state1) && 
                        TDsStateDiff(tds_state2, tds_state1) == tds_diff)
        // Requirement: properties of FindAllActiveTDsStatesByDev

    ensures forall tds_state1, tds_state2 :: tds_state1 in from_states &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2)
                ==> tds_state2 in to_states
{
    Lemma_SameTDsStateIffSameDiffWithATDState();

    forall tds_state1, tds_state2 | tds_state1 in from_states &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2)
        ensures tds_state2 in to_states
    {
        var tds_diff:map<TD_ID, TD_Val> := TDsStateDiff(tds_state2, tds_state1);
        assert MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(tds_state1);
        assert IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, tds_state1, tds_diff);
        assert exists tds_state3 :: tds_state3 in to_states && 
                        TDsStateGetTDIDs(tds_state3) == TDsStateGetTDIDs(tds_state1) && 
                        TDsStateDiff(tds_state3, tds_state1) == tds_diff;
                        
        assert tds_state2 in to_states;
    }
}

// Lemma: For each TDs' state (tds_state2 in <to_states>) returned by 
// <FindAllActiveTDsStatesByDev>, there exists a TDs' state (tds_state1 in 
// <from_states>) input to the method, such that IsActiveTDsStateReachActiveTDsStateInOneStep 
// is true for the two states
lemma Lemma_FindAllActiveTDsStatesByDev_ReturnedTDsStatesCouldBeReachedInOneStep(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, from_states:set<TDs_Vals>, to_states:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in from_states + to_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: <from_states> and <to_states> must includes all active TDs 

    requires forall tds_state2 :: tds_state2 in to_states
                ==> (exists tds_state1, tds_diff :: tds_state1 in from_states && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state1) && 
                        tds_diff == TDsStateDiff(tds_state2, tds_state1) && 
                        IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, tds_state1, tds_diff)) 
        // Requirement: properties of FindAllActiveTDsStatesByDev

    ensures forall tds_state2 :: tds_state2 in to_states
                ==> (exists tds_state1 :: tds_state1 in from_states &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2))
{
    // Dafny can automatically prove this lemma
}

// Lemma: TDs' state reached by a TDs' state in one step also reached by the 
// state in chain 
lemma Lemma_TDsStateReachedInOneStepAlsoReachedInChain(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, active_devs:set<Dev_ID>, from_state:TDs_Vals, to_state:TDs_Vals
)
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires dev_id in active_devs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires TDsStateGetTDIDs(from_state) == k_params.all_active_tds
    requires TDsStateGetTDIDs(to_state) == k_params.all_active_tds
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_state, to_state)

    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, from_state, to_state)
{
    var tds_states:seq<TDs_Vals> := [from_state, to_state];
    var devs:seq<Dev_ID> := [dev_id];

    assert |tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
            |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
            tds_states[|tds_states| - 1] == to_state && // last TDs' state is the <to_tds_state>
            tds_states[0] == from_state && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]));
}

lemma Lemma_UnExploredStatesHasNoIntersectionWithInputExploredStates(
    tds_states_dev:set<TDs_Vals>, unexplored_states:set<TDs_Vals>, input_explored_states:set<TDs_Vals>
)
    requires unexplored_states == (tds_states_dev - input_explored_states)
    ensures unexplored_states * input_explored_states == {}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindReachableTDsStatesFromTDsState_LoopInv2(
    k_params:ReachableTDsKParams,
    explored_tds_states:seq<set<TDs_Vals>>, to_explore_states:set<TDs_Vals>, unexplored_states:set<TDs_Vals>
)
    requires forall tds_state2 :: tds_state2 in unexplored_states
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in to_explore_states
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds

    ensures forall tds_state2 :: tds_state2 in to_explore_states + unexplored_states
                ==> TDsStateGetTDIDs(tds_state2) == 
                    k_params.all_active_tds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindReachableTDsStatesFromTDsState_LoopInv3(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, active_devs:set<Dev_ID>, tds_state:TDs_Vals, explored_tds_states:seq<set<TDs_Vals>>,
    exploring_states:set<TDs_Vals>, tds_states_dev:set<TDs_Vals>, unexplored_states:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires dev_id in active_devs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in exploring_states + tds_states_dev
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: <exploring_states> and <tds_states_dev> must includes all active TDs 

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2))
        // Requirement: Forall tds_state2 in E[0..|E|], tds_state -->* tds_state2
    requires |explored_tds_states| >= 1 && explored_tds_states[0] == {tds_state}
        // Requirement: E0 == {tds_state}

    requires forall tds_state2 :: tds_state2 in tds_states_dev
                ==> (exists tds_state1, tds_diff :: tds_state1 in exploring_states && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state1) && 
                        tds_diff == TDsStateDiff(tds_state2, tds_state1) && 
                        IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, tds_state1, tds_diff)) 
    
    requires exploring_states == explored_tds_states[|explored_tds_states| - 1]
    requires unexplored_states == tds_states_dev - GetExploredTDsStates(explored_tds_states, 0)

    ensures forall tds_state2 :: tds_state2 in unexplored_states 
            ==> tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2)
{
    Lemma_FindAllActiveTDsStatesByDev_ReturnedTDsStatesCouldBeReachedInOneStep(k_params, dev_id, exploring_states, tds_states_dev);
    forall tds_state2 | tds_state2 in unexplored_states
        ensures tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2)
    {
        assert forall tds_state1 :: tds_state1 in exploring_states
                ==> tds_state == tds_state1 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state1);
                    // tds_state -->* exploring_states

        assert exists tds_state1 :: tds_state1 in exploring_states &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2);
            // exploring_states --> unexplored_states

        forall tds_state1 | tds_state1 in exploring_states &&
                    ( tds_state == tds_state1 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state1)) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state1, tds_state2)    
            ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2)
        {
            if(tds_state1 != tds_state)
            {
                assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state1);
                Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(
                    k_params, 
                    dev_id, active_devs, tds_state, tds_state1, tds_state2);
            }
            else
            {
                assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_state, tds_state2);
                Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, dev_id, active_devs, tds_state, tds_state2);
                assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2);
            }
        }
        assert tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_state, tds_state2);
    }
}

// Lemma: If tds_stateA --> tds_stateB, then forall tds_state2, 
// tds_stateB -->* tds_state2 ==> tds_stateA -->1+ tds_state2
lemma Lemma_TDsStateAReachTDsStateBInOneStep_ThenTDsStatesReachedByBInChainAlsoReachedByAInChain(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, active_devs:set<Dev_ID>,
    tds_stateA:TDs_Vals, tds_stateB:TDs_Vals
)
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires dev_id in active_devs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires TDsStateGetTDIDs(tds_stateA) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_stateB) == k_params.all_active_tds

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_stateA, tds_stateB)

    ensures forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (tds_stateB == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_stateB, tds_state2))
                                                // tds_stateB -->* tds_state2
                ==> IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_devs, tds_stateA, tds_state2)
                                                // tds_stateA -->1+ tds_state2
{
    forall tds_state2 | 
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (tds_stateB == tds_state2 || 
                    IsActiveTDsStateReachActiveTDsStateInChain(
                        k_params, 
                        active_devs, tds_stateB, tds_state2))
        ensures IsActiveTDsStateReachActiveTDsStateInChain(
                        k_params, 
                        active_devs, tds_stateA, tds_state2)
    {
        if(!IsActiveTDsStateReachActiveTDsStateInChain(
                k_params, 
                active_devs, tds_stateB, tds_state2))
        {
            assert tds_stateB == tds_state2;

            Lemma_TDsStateReachedInOneStepAlsoReachedInChain(
                k_params,
                dev_id, active_devs, tds_stateA, tds_stateB);

            assert IsActiveTDsStateReachActiveTDsStateInChain( 
                        k_params,
                        active_devs, tds_stateA, tds_state2);
        }
        else
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(
                        k_params,
                        active_devs, tds_stateB, tds_state2);
            forall tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> | (|tds_states| >= 2 && 
                    (forall tds_state3 :: tds_state3 in tds_states 
                        ==> TDsStateGetTDIDs(tds_state3) == k_params.all_active_tds) &&
                    |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
                    tds_states[|tds_states| - 1] == tds_state2 && // last TDs' state is the <to_tds_state>
                    tds_states[0] == tds_stateB && // first TDs' state is the <from_tds_state>
                    (forall i :: 0<=i<|tds_states| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(
                                k_params,
                                devs[i], tds_states[i], tds_states[i+1])))
                ensures IsActiveTDsStateReachActiveTDsStateInChain(
                                k_params,
                                active_devs, tds_stateA, tds_state2)
            {
                var tds_states_new := [tds_stateA] + tds_states;
                var devs_new := [dev_id] + devs;

                assert tds_state2 == tds_states[|tds_states| - 1];
                assert tds_state2 == tds_states_new[|tds_states_new| - 1];
                assert tds_stateA == tds_states_new[0];

                // Prove for i in [0, |tds_states_new| - 1), IsActiveTDsStateReachActiveTDsStateInOneStep 
                // for devs_new and tds_states_new holds
                assert forall i :: i == 0
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(
                                k_params,
                                devs_new[i], tds_states_new[i], tds_states_new[i+1]);

                forall i | 0<=i<|tds_states_new| - 1 
                    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(
                                k_params,
                                devs_new[i], tds_states_new[i], tds_states_new[i+1])
                {
                    if (i == 0)
                    {}
                    else
                    {
                        assert tds_states_new[i] == tds_states[i - 1];
                        assert devs_new[i] == devs[i - 1];

                        assert IsActiveTDsStateReachActiveTDsStateInOneStep(
                                k_params,
                                devs[i-1], tds_states[i-1], tds_states[i]);
                    }
                }

                assert forall i :: 0<=i<|tds_states_new| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(
                                k_params,
                                devs_new[i], tds_states_new[i], tds_states_new[i+1]);

                assert |tds_states_new| >= 2 && 
                    (forall tds_state3 :: tds_state3 in tds_states_new 
                        ==> TDsStateGetTDIDs(tds_state3) == k_params.all_active_tds) &&
                    |devs_new| == |tds_states_new| - 1 && (forall dev_id2 :: dev_id2 in devs_new ==> dev_id2 in active_devs);

                assert |tds_states_new| >= 2 && 
                    (forall tds_state2 :: tds_state2 in tds_states_new 
                        ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                    |devs_new| == |tds_states_new| - 1 && (forall dev_id2 :: dev_id2 in devs_new ==> dev_id2 in active_devs) &&
                    tds_states_new[|tds_states_new| - 1] == tds_state2 && // last TDs' state is the <to_tds_state>
                    tds_states_new[0] == tds_stateA && // first TDs' state is the <from_tds_state>
                    (forall i :: 0<=i<|tds_states_new| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1]));

                Lemma_TDsStateAReachTDsStateBInOneStep_ThenTDsStatesReachedByBInChainAlsoReachedByAInChain_ApplyIsTDsStateReachTDsStateInChainDef(
                    k_params,
                    tds_states_new, devs_new, active_devs, tds_stateA, tds_state2);                        
                assert IsActiveTDsStateReachActiveTDsStateInChain(
                            k_params,
                            active_devs, tds_stateA, tds_state2);
            }
        }
    }
}

// Private lemma: Used by 
// <Lemma_TDsStateAReachTDsStateBInOneStep_ThenTDsStatesReachedByBInChainAlsoReachedByAInChain>
lemma Lemma_TDsStateAReachTDsStateBInOneStep_ThenTDsStatesReachedByBInChainAlsoReachedByAInChain_ApplyIsTDsStateReachTDsStateInChainDef(
    k_params:ReachableTDsKParams,  
    tds_states_new:seq<TDs_Vals>, devs_new:seq<Dev_ID>, active_devs:set<Dev_ID>, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires |tds_states_new| >= 2 && 
            (forall tds_state2 :: tds_state2 in tds_states_new 
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
            |devs_new| == |tds_states_new| - 1 && (forall dev_id2 :: dev_id2 in devs_new ==> dev_id2 in active_devs) &&
            tds_states_new[|tds_states_new| - 1] == to_tds_state && // last TDs' state is the <to_tds_state>
            tds_states_new[0] == from_tds_state && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|tds_states_new| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1]));
    ensures  IsActiveTDsStateReachActiveTDsStateInChain(
                            k_params,
                            active_devs, from_tds_state, to_tds_state)
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_FindReachableTDsStatesFromTDsState_LoopInv4(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, active_devs:set<Dev_ID>, new_devs:seq<Dev_ID>, old_devs:seq<Dev_ID>,
    tds_state:TDs_Vals, explored_tds_states:seq<set<TDs_Vals>>,
    exploring_states:set<TDs_Vals>, tds_states_dev:set<TDs_Vals>, unexplored_states:set<TDs_Vals>, to_explore_states:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires dev_id in active_devs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in exploring_states + tds_states_dev
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: <exploring_states> and <tds_states_dev> must includes all active TDs
    requires forall dev_id2 :: dev_id2 in new_devs ==> dev_id2 in active_devs
    requires new_devs == old_devs + [dev_id]
        // Requirement: Relationships between <dev_id>, <active_devs> and <devs>

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(
                                                    k_params,
                                                    active_devs, tds_state, tds_state2))
        // Requirement: Forall tds_state2 in E[0..|E|], tds_state -->* tds_state2
    requires |explored_tds_states| >= 1 && explored_tds_states[0] == {tds_state}
        // Requirement: E0 == {tds_state}

    requires forall tds_state2 :: tds_state2 in tds_states_dev
                ==> (exists tds_state1, tds_diff :: tds_state1 in exploring_states && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state1) && 
                        tds_diff == TDsStateDiff(tds_state2, tds_state1) && 
                        IsTDsDiffReqInActiveTDsStateAndIssuedByDev(
                                                    k_params,
                                                    dev_id, tds_state1, tds_diff)) 
    
    requires exploring_states == explored_tds_states[|explored_tds_states| - 1]
    requires unexplored_states == tds_states_dev - GetExploredTDsStates(explored_tds_states, 0)

    requires forall tds_state1, tds_state2 :: tds_state1 in exploring_states &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                IsActiveTDsStateReachActiveTDsStateInOneStep(
                    k_params,
                    dev_id, tds_state1, tds_state2)
                ==> tds_state2 in tds_states_dev
        // Requirement: properties of FindAllActiveTDsStatesByDev

    requires forall tds_state1, tds_state2 :: tds_state1 in exploring_states &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in old_devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(
                            k_params,
                            dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states;

    ensures forall tds_state1, tds_state2 :: tds_state1 in exploring_states &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in new_devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states + unexplored_states
{
    assert forall dev_id2 :: dev_id2 in new_devs
            ==> dev_id2 in old_devs || dev_id2 == dev_id;
    forall tds_state1, tds_state2 | tds_state1 in exploring_states &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in new_devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))
        ensures tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states + unexplored_states
    {
        forall dev_id2 | dev_id2 in new_devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2)
            ensures tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states + unexplored_states
        {
            if (dev_id2 == dev_id)
            {
                assert tds_state1 in exploring_states &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id, tds_state1, tds_state2);
                assert tds_state2 in tds_states_dev;
                assert tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states + unexplored_states;
            }
            else
            {
                assert dev_id2 in old_devs;
                assert tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states + unexplored_states;
            }
        }
        
    }
}

lemma Lemma_FindReachableTDsStatesFromTDsState_LoopInv5(
    to_explore_states:set<TDs_Vals>, unexplored_states:set<TDs_Vals>, input_explored_states:set<TDs_Vals>
)
    requires unexplored_states * input_explored_states == {}
    requires input_explored_states * to_explore_states == {}
    ensures input_explored_states * (to_explore_states + unexplored_states) == {}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindReachableTDsStatesFromTDsState_LoopInv6(
    k_params:ReachableTDsKParams, 
    new_devs:seq<Dev_ID>, old_devs:seq<Dev_ID>, dev_id:Dev_ID,
    exploring_states:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires forall tds_state2 :: tds_state2 in exploring_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: The TDs' state includes all TDs
    requires forall dev_id2 :: dev_id2 in new_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in new_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires new_devs == old_devs + [dev_id]

    requires forall tds_state2 :: tds_state2 in exploring_states
                ==> (forall td_id2, dev_id2 :: 
                    dev_id2 in old_devs && 
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(
                        k_params,
                        tds_state2, dev_id2, td_id2)
                        // For all active TDs can be read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                            k_params,
                            tds_state2, td_id2))
    requires forall tds_state2 :: tds_state2 in exploring_states
                    ==> (forall td_id2 :: 
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(
                            k_params,
                            tds_state2, dev_id, td_id2)
                            // For all active TDs can be read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                                k_params,
                                tds_state2, td_id2))

    ensures forall tds_state2 :: tds_state2 in exploring_states
                ==> (forall td_id2, dev_id2 :: 
                    dev_id2 in new_devs && 
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(
                        k_params,
                        tds_state2, dev_id2, td_id2)
                        // For all active TDs can be read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                            k_params,
                            tds_state2, td_id2))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindReachableTDsStatesFromTDsState_LoopInv7(
    k_params:ReachableTDsKParams,
    explored_tds_states:seq<set<TDs_Vals>>, to_explore_states:set<TDs_Vals>, unexplored_states:set<TDs_Vals>
)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)

    requires forall tds_state2 :: tds_state2 in unexplored_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
    requires forall tds_state2 :: tds_state2 in to_explore_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)

    ensures forall tds_state2 :: tds_state2 in to_explore_states + unexplored_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
{
    // Dafny can automatically prove this lemma
}

// Lemma: If no new states is found (i.e., to_explore_states is empty in the 
// caller, then for any tds_state1 in <explored_tds_states> and 
// tds_state1 --> tds_state2, we have tds_state2 in <explored_tds_states>
lemma Lemma_FindReachableTDsStatesFromTDsState_ToExploreStatesIsEmptyThenReachableStatesAreExplored(
    k_params:ReachableTDsKParams, 
    devs:seq<Dev_ID>, explored_tds_states:seq<set<TDs_Vals>>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires forall dev_id2 :: dev_id2 in devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires |explored_tds_states| > 0

    requires forall tds_state1, tds_state2 :: tds_state1 in explored_tds_states[|explored_tds_states| - 1] &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
    requires forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) && 
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)

    ensures forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states, 0) &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(
                            k_params,
                            dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
{
    Lemma_ExploredTDsStatesCanBeSeparated(explored_tds_states);
}

lemma Lemma_FindReachableTDsStatesFromTDsState_ReachableStatesHaveValidRefsOnly(
    k_params:ReachableTDsKParams, 
    devs:seq<Dev_ID>, explored_tds_states:seq<set<TDs_Vals>>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires forall dev_id2 :: dev_id2 in devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires |explored_tds_states| > 0

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0)
                ==> (forall td_id2, dev_id :: 
                    dev_id in devs && 
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(
                        k_params,
                        tds_state2, dev_id, td_id2)
                        // For all active TDs can be read by an active device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                            k_params,
                            tds_state2, td_id2))
    requires forall tds_state2 :: tds_state2 in explored_tds_states[|explored_tds_states| - 1]
                ==> (forall td_id2, dev_id2 :: 
                    dev_id2 in devs && 
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(
                        k_params,
                        tds_state2, dev_id2, td_id2)
                        // For all active TDs can be read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                            k_params, 
                            tds_state2, td_id2))

    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (forall td_id2, dev_id :: 
                    dev_id in devs && 
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                        // For all active TDs can be read by an active device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
{
    Lemma_ExploredTDsStatesCanBeSeparated(explored_tds_states);
}

// Lemma: 
// If (1) tds_state is in explored_tds_states, and (2) For any tds_state1 
// in <explored_tds_states> and tds_state1 --> tds_state2, we have tds_state2 in 
// <explored_tds_states>
// Then any TDs' states reachable by tds_state (in chain) is in 
// <explored_tds_states>
lemma Lemma_ReachableTDsStatesAreExplored(
    k_params:ReachableTDsKParams,  
    active_devs:set<Dev_ID>, explored_tds_states:seq<set<TDs_Vals>>, tds_state:TDs_Vals
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires |explored_tds_states| > 0

    requires forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states, 0) &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in active_devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(
                            k_params,
                            dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
        // Requirement: Forall tds_state2 and explored state (<tds_state1>), if 
        // tds_state1 --> tds_state2, then tds_state2 is also explored
    requires tds_state in GetExploredTDsStates(explored_tds_states, 0)
        // Requirement: tds_state in GetExploredTDsStates(explored_tds_states, 0)

    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                        (tds_state2 == tds_state || 
                            IsActiveTDsStateReachActiveTDsStateInChain(
                                k_params,
                                active_devs, tds_state, tds_state2))
                                                    // tds_state -->* tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
        // Property: Forall tds_state2, tds_state -->* tds_state2, tds_state2 in explored
{
    forall tds_state2 | 
            TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
            (tds_state2 == tds_state || 
                IsActiveTDsStateReachActiveTDsStateInChain(
                    k_params,
                    active_devs, tds_state, tds_state2))
        ensures tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
    {
        if(tds_state2 == tds_state)
        {
            assert tds_state2 in GetExploredTDsStates(explored_tds_states, 0);
        }
        else
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(
                        k_params,
                        active_devs, tds_state, tds_state2);
            Lemma_ReachableTDsStatesAreExplored_TDsStatesReachedInChainAreExplored(
                k_params,
                active_devs, explored_tds_states, tds_state, tds_state2);
        }
    }
}

lemma Lemma_ReachableTDsStatesAreExplored_TDsStatesReachedInChainAreExplored(
    k_params:ReachableTDsKParams,  
    active_devs:set<Dev_ID>, explored_tds_states:seq<set<TDs_Vals>>, tds_state:TDs_Vals, tds_state2:TDs_Vals
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires |explored_tds_states| > 0

    requires forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states, 0) &&
                    TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (exists dev_id2 :: dev_id2 in active_devs &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(
                            k_params,
                            dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                    ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
        // Requirement: Forall tds_state2 and explored state (<tds_state1>), if 
        // tds_state1 --> tds_state2, then tds_state2 is also explored
    requires tds_state in GetExploredTDsStates(explored_tds_states, 0)
        // Requirement: tds_state in GetExploredTDsStates(explored_tds_states, 0)

    requires TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires IsActiveTDsStateReachActiveTDsStateInChain(
                k_params,
                active_devs, tds_state, tds_state2)

    ensures tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
{
    forall tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> |
            |tds_states| >= 2 && 
            (forall tds_state4 :: tds_state4 in tds_states 
                ==> TDsStateGetTDIDs(tds_state4) == k_params.all_active_tds) &&
            |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in active_devs) &&
            tds_states[|tds_states| - 1] == tds_state2 && // last TDs' state is the <to_tds_state>
            tds_states[0] == tds_state && // first TDs' state is the <from_tds_state>
            (forall i :: 0<=i<|tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        devs[i], tds_states[i], tds_states[i+1]))
        ensures tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
    {
        var i := 0;

        while(i < |tds_states|-1)
            invariant i <= |tds_states|-1
    
            invariant tds_states[i] in GetExploredTDsStates(explored_tds_states, 0)
            invariant forall p :: 0 <= p <= i
                    ==> tds_states[p] in GetExploredTDsStates(explored_tds_states, 0)
        {
            assert TDsStateGetTDIDs(tds_states[i+1]) == k_params.all_active_tds;
            assert IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        devs[i], tds_states[i], tds_states[i+1]);
                    
            assert tds_states[i+1] in GetExploredTDsStates(explored_tds_states, 0);
            i := i + 1;
        }

        assert forall tds_state3 :: tds_state3 in tds_states 
                ==> tds_state3 in GetExploredTDsStates(explored_tds_states, 0);
    }
}

// Lemma: If tds_states, status == FindReachableActiveTDsStatesFromActiveTDsState(k'.objects.tds), 
// and status == true, then IsValidState_ReachableTDsStates(k') is true
lemma Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateOfReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, tds_states:set<TDs_Vals>, k'_reachable_active_tds_states:set<TDs_Vals>, status:bool
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k'_params)
    // Requirements required by functions in this function method
    
    requires TDsStateGetTDIDs(ActiveTDsState(k')) == k'_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k'_params.all_active_tds
        // Requirement: <tds_states> must includes all active TDs
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k')
                ==> IsDevID_SlimState(k'_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k'_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k')
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> (ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params,
                                                        AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
        // Requirement: Forall tds_state2 in tds_states, ActiveTDsState(k') -->* tds_state2
    requires (status == true)
                ==> (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k') &&
                        (tds_state2 == ActiveTDsState(k') || 
                            IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
                                                    // ActiveTDsState(k') -->* tds_state2
                    ==> tds_state2 in tds_states)
        // Requirement: Forall tds_state2, ActiveTDsState(k') -->* tds_state2 ==> tds_state2 in tds_states
    requires status <==> AllReachableActiveTDsStatesAreSecure(k'_params, AllActiveDevs(k'), tds_states)
        // Requirement: Any active TDs read by any active devices have no invalid
        // references to I/O objects

    requires status == true
    requires k'_reachable_active_tds_states == tds_states

    ensures forall tds_state2 :: tds_state2 in k'_reachable_active_tds_states
                ==> (ActiveTDsState(k') == tds_state2 || 
                     IsActiveTDsStateReachActiveTDsStateInChain(k'_params,
                        AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
        // Property: k' fulfills Condition 5.2 of <IsValidState_ReachableTDsStates>
    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k') &&
                    (ActiveTDsState(k') == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k'_params,
                            AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
                                                // ActiveTDsState(k') -->* tds_state2
                ==> tds_state2 in k'_reachable_active_tds_states
        // Property: k' fulfills Condition 5.3 of <IsValidState_ReachableTDsStates>
    ensures forall tds_state2 :: tds_state2 in k'_reachable_active_tds_states
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k') && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k'_params,
                        tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params,
                            tds_state2, td_id2))
        // Property: k' fulfills Condition 5.5 of <IsValidState_ReachableTDsStates> 
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_FindReachableTDsStatesFromTDsState_Req2(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, tds_state:TDs_Vals,
    t_explored_states:seq<set<TDs_Vals>>, explored_tds_states:seq<set<TDs_Vals>>, to_explore_states:set<TDs_Vals>
)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    
    requires |explored_tds_states| > 0
    requires t_explored_states == SeqAppend<set<TDs_Vals>>(explored_tds_states, to_explore_states)

    requires GetExploredTDsStates(explored_tds_states, 0) * to_explore_states == {}
    requires to_explore_states != {}
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(t_explored_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds 

    requires forall tds_state2 :: tds_state2 in to_explore_states
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(
                                                    k_params,
                                                    active_devs, tds_state, tds_state2))
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(
                                                    k_params,
                                                    active_devs, tds_state, tds_state2))

    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(t_explored_states, 0)
                ==> (tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(
                                                    k_params,
                                                    active_devs, tds_state, tds_state2))
{
    Lemma_ExploredTDsStatesAfterAppendingIncludeOldExploredTDsStatesAndAddedExploreTDsStates(
        t_explored_states, explored_tds_states, to_explore_states);
}

lemma Lemma_FindReachableTDsStatesFromTDsState_Req4(
    k_params:ReachableTDsKParams,  
    active_devs:set<Dev_ID>, exploring_states:set<TDs_Vals>, 
    t_explored_states:seq<set<TDs_Vals>>, explored_tds_states:seq<set<TDs_Vals>>, to_explore_states:set<TDs_Vals>
)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires t_explored_states == SeqAppend<set<TDs_Vals>>(explored_tds_states, to_explore_states)
    requires |explored_tds_states| > 0
    requires exploring_states == explored_tds_states[|explored_tds_states| - 1]
    
    requires forall tds_state1, tds_state2 :: 
                tds_state1 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) && 
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id :: dev_id in active_devs && 
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id, tds_state1, tds_state2))
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
        // Requirement: Forall tds_state1 in E[0..|E|-1], and tds_state1 --> tds_state2 
        // ==> tds_state2 must be in E[0..|E|]
    requires forall tds_state1, tds_state2 :: tds_state1 in exploring_states &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in active_devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) || tds_state2 in to_explore_states;
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
            ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds;
                 
    ensures forall tds_state1, tds_state2 :: 
                tds_state1 in GetExploredTDsStates(explored_tds_states, 0) && 
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id :: dev_id in active_devs && 
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id, tds_state1, tds_state2))
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) + to_explore_states
{
    assert forall tds_state1, tds_state2 :: tds_state1 in explored_tds_states[|explored_tds_states| - 1] &&
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in active_devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0) + to_explore_states;

    Lemma_ExploredTDsStatesCanBeSeparated(explored_tds_states);
    assert GetExploredTDsStates(explored_tds_states, 0) == GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) + 
            explored_tds_states[|explored_tds_states| - 1];

    assert forall tds_state1, tds_state2 :: tds_state1 in GetExploredTDsStates(explored_tds_states[..|explored_tds_states| - 1], 0) && 
                TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                (exists dev_id2 :: dev_id2 in active_devs &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(
                        k_params,
                        dev_id2, tds_state1, tds_state2))  //tds_state1 --> tds_state2
                ==> tds_state2 in GetExploredTDsStates(explored_tds_states, 0);  
}

lemma Lemma_FindReachableTDsStatesFromTDsState_Req7(
    k_params:ReachableTDsKParams, 
    active_devs:set<Dev_ID>, tds_state:TDs_Vals,
    t_explored_states:seq<set<TDs_Vals>>, explored_tds_states:seq<set<TDs_Vals>>, to_explore_states:set<TDs_Vals>
)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    
    requires |explored_tds_states| > 0
    requires t_explored_states == SeqAppend<set<TDs_Vals>>(explored_tds_states, to_explore_states)

    requires GetExploredTDsStates(explored_tds_states, 0) * to_explore_states == {}
    requires to_explore_states != {}
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(t_explored_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds 

    requires forall tds_state2 :: tds_state2 in to_explore_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)

    ensures forall tds_state2 :: tds_state2 in GetExploredTDsStates(t_explored_states, 0)
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
{
    Lemma_ExploredTDsStatesAfterAppendingIncludeOldExploredTDsStatesAndAddedExploreTDsStates(
        t_explored_states, explored_tds_states, to_explore_states);
}

lemma Lemma_FindReachableTDsStatesFromTDsState_ProveTermination(
    k_active_tds_all_states:set<TDs_Vals>,
    t_explored_states:seq<set<TDs_Vals>>, explored_tds_states:seq<set<TDs_Vals>>, to_explore_states:set<TDs_Vals>
)
    requires GetExploredTDsStates(t_explored_states, 0) <= k_active_tds_all_states
    requires GetExploredTDsStates(explored_tds_states, 0) <= k_active_tds_all_states

    requires |explored_tds_states| > 0
    requires t_explored_states == SeqAppend<set<TDs_Vals>>(explored_tds_states, to_explore_states)

    requires GetExploredTDsStates(explored_tds_states, 0) * to_explore_states == {}
    requires to_explore_states != {}

    ensures |k_active_tds_all_states - GetExploredTDsStates(t_explored_states, 0)| < 
            |k_active_tds_all_states - GetExploredTDsStates(explored_tds_states, 0)|
{
    Lemma_ExploredTDsStatesAfterAppendingIncludeOldExploredTDsStatesAndAddedExploreTDsStates(
        t_explored_states, explored_tds_states, to_explore_states);
    assert GetExploredTDsStates(t_explored_states, 0) == GetExploredTDsStates(explored_tds_states, 0) + to_explore_states;
    Lemma_SetIncludeMoreElemsFormStrictSuperset(
        GetExploredTDsStates(t_explored_states, 0), GetExploredTDsStates(explored_tds_states, 0), to_explore_states);
    assert GetExploredTDsStates(t_explored_states, 0) > GetExploredTDsStates(explored_tds_states, 0);

    assert k_active_tds_all_states - GetExploredTDsStates(t_explored_states, 0) < k_active_tds_all_states - GetExploredTDsStates(explored_tds_states, 0);
    ProperSubsetCardinalityLemma<TDs_Vals>(
        k_active_tds_all_states - GetExploredTDsStates(explored_tds_states, 0), 
        k_active_tds_all_states - GetExploredTDsStates(t_explored_states, 0)
    );
}

lemma Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_Property(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(
                k_params, 
                dev_id, from_tds_state, to_tds_state)

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_tds_state, to_tds_state)
            <==> 
            IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, from_tds_state, TDsStateDiff(to_tds_state, from_tds_state))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
    k_params:ReachableTDsKParams, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k_params.subjects.drvs) && (Dev_ID(dev_sid) in k_params.subjects.devs)
                 ==> (drv_sid != dev_sid)

    requires TDsStateGetTDIDs(from_tds_state) == k_params.all_active_tds
    requires TDsStateGetTDIDs(to_tds_state) == k_params.all_active_tds
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_tds_state, to_tds_state)

    ensures forall td_id :: td_id in TDsStateDiff(to_tds_state, from_tds_state)
                ==> (exists tdx_id :: 
                            (dev_id in AllActiveDevs_SlimState(k_params.subjects) &&
                                tdx_id in k_params.all_active_tds &&
                                CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) &&
                                td_id in from_tds_state[tdx_id].trans_params_tds &&
                                W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                                    // The TD references the target TD (<td_id2>) with W
                                to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals))
                                // The TD specifies the new value to be written
{
    assert dev_id in k_params.subjects.devs;
    Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k_params.subjects, dev_id);
    assert SubjPID_SlimState(k_params.subjects, dev_id.sid) != NULL;
    assert dev_id in AllActiveDevs_SlimState(k_params.subjects);

    var tds_diff := TDsStateDiff(to_tds_state, from_tds_state);
    var tds_state := from_tds_state;
    assert forall td_id, td_new_cfg :: td_id in tds_diff &&
                td_new_cfg == tds_diff[td_id]
                    ==> (exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg));
                                    // the active TD refs the TD with W and the new TD cfg

    forall td_id | td_id in tds_diff
        ensures exists tdx_id :: 
                    (    tdx_id in k_params.all_active_tds &&
                        CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) &&
                        td_id in from_tds_state[tdx_id].trans_params_tds &&
                        W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                            // The TD references the target TD (<td_id2>) with W
                        to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals)
    {
        {
            var td_new_cfg := tds_diff[td_id];
            var tdx_id :|   tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg);

            assert tdx_id in k_params.all_active_tds &&
                    CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id);
        }
    }
}

// Returns if a device modifies the given TDs' state (<from_tds_state>) ONLY
// due to its hardcoded write transfers to TDs
predicate DevModifyTDsStateOnlyWithHCodedWToTDs(
    k_params:ReachableTDsKParams, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires TDsStateGetTDIDs(from_tds_state) == k_params.all_active_tds
        // Requirement: <from_tds_state> contains all IDs of active TDs

    requires dev_id in k_params.subjects.devs
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
    
    requires TDsStateGetTDIDs(from_tds_state) == TDsStateGetTDIDs(to_tds_state)
    
{
    // Device's (<dev_id>) modification to TDs' state is due to device's 
    // hardcoded write transfers to TDs
    (forall td_id, td_new_cfg :: td_id in TDsStateDiff(to_tds_state, from_tds_state) &&
            td_new_cfg == TDsStateDiff(to_tds_state, from_tds_state)[td_id]
        ==> TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id),
                    td_id, td_new_cfg)) &&
    // Device's (<dev_id>) modification to TDs' state is NOT due to write 
    // transfers in any TDs read by the device
    (forall td_id, td_new_cfg :: td_id in TDsStateDiff(to_tds_state, from_tds_state) &&
            td_new_cfg == TDsStateDiff(to_tds_state, from_tds_state)[td_id]
        ==> !(exists tdx_id :: 
                tdx_id in TDsStateGetTDIDs(from_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) && 
                        // exists an active TD readable by the device
                tdx_id !in k_params.hcoded_td_ids &&
                        // the active TD is not a hardcoded TD
                IsTDWriteInTD(from_tds_state, tdx_id, td_id, td_new_cfg))) &&

    (true)
}

lemma Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev_SlimState(k:State, k_params:ReachableTDsKParams)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))

    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id 
        // Requirements: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)
    
    requires k_params == KToKParams(k) 

    ensures forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain_Private(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, active_devs:set<Dev_ID>,
    tds_stateA:TDs_Vals, tds_stateB:TDs_Vals, tds_stateC:TDs_Vals,
    tds_states_new:seq<TDs_Vals>, devs_new:seq<Dev_ID>
)
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires dev_id in active_devs
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The device must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires TDsStateGetTDIDs(tds_stateA) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_stateB) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_stateC) == k_params.all_active_tds
    
    requires |tds_states_new| >= 2
    requires |devs_new| == |tds_states_new| - 1
    requires forall i :: 0<=i<|tds_states_new| - 2 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1]) &&
                            IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1])
    requires tds_stateB == tds_states_new[|tds_states_new| - 2]
    requires tds_stateC == tds_states_new[|tds_states_new| - 1]
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, tds_stateB, tds_stateC)
    requires devs_new[|devs_new|-1] == dev_id
    
    ensures forall i :: 0<=i<|tds_states_new| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs_new[i], tds_states_new[i], tds_states_new[i+1])
{
    // Dafny can automatically prove this lemma
}