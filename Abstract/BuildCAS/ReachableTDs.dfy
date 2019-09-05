include "../Syntax.dfy"
include "../Utils.dfy"
include "../Properties_Utils.dfy"
include "Utils_BuildCAS.dfy"

predicate FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params:ReachableTDsKParams)
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
    (forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k_params.subjects.drvs) && (Dev_ID(dev_sid) in k_params.subjects.devs)
                 ==> (drv_sid != dev_sid)) &&
        // Requirement: Subjects have different internal IDs

    (forall dev_id :: dev_id in k_params.subjects.devs
        ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.subjects.devs[dev_id].td_ids) &&
        // Hardcoded TDs are in devices
    (forall dev_id, td_id :: 
        dev_id in k_params.subjects.devs && td_id in k_params.subjects.devs[dev_id].td_ids
        ==> td_id in k_params.objs_td_ids) &&
        // TDs in devices are also in the state
    (forall s_id, o_id :: s_id in AllSubjsIDs(k_params.subjects) &&
                    DoOwnObj_SlimState(k_params.subjects, s_id, o_id)
                ==> o_id in k_params.objs_pids &&
                    k_params.objs_pids[o_id] == SubjPID_SlimState(k_params.subjects, s_id)) &&
        // Requirement: If a subject owns an object, then the subject and the 
        // object must be in the same partition
    (true)
}

// Find all TDs reachable from the hardcoded TD with R access mode.
// These TDs together are the set of TDs read by the device (<dev_id>)
//
// <tds_state> is the state of active TDs. In the graph of TDs and their
// references with read access mode, only active TDs are included. This is 
// because that (1) no active TD carries transfers to any inactive objects, and
// (2) active devices never have hardcoded transfers to inactive objects. Thus, 
// active TDs only refs active TDs.
method FindAllTDsReachableFromHCodedTDsWithR(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, dev_id:Dev_ID, hcoded_td_id:TD_ID
) returns (td_ids:set<TD_ID>, status:bool)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires hcoded_td_id == k_params.subjects.devs[dev_id].hcoded_td_id
        // Requirement: <hcoded_td_id> is the ID of the hardcoded TD in the 
        // device (<dev_id>)

    ensures forall td_id2 :: td_id2 in td_ids
                ==> td_id2 in TDsStateGetTDIDs(tds_state) && 
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        // Property: Each returned TD in <td_ids> is active, and can be read by
        // the device (<dev_id>)
    ensures status == true
                ==> (forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, hcoded_td_id, td_id2)
                    ==> td_id2 in td_ids)
        // Property: All active TDs refed by the hardcoded TD exist in <td_ids>
    ensures status == true
                ==> hcoded_td_id in td_ids
        // Property: Hardcoded TD is also in <td_ids>
    ensures status == true
                <==> (forall td_id2 :: td_id2 in td_ids
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2))
        // Property: Each returned TD in <td_ids> has no invalid references to
        // any I/O objects
{
    Lemma_DevsOwnHCodedTDs(k_params.subjects, dev_id, hcoded_td_id);

    Lemma_CanActiveDevReadActiveTD_DevCanAlwaysReadHCodedTD(k_params, tds_state, dev_id);
    assert hcoded_td_id in TDsStateGetTDIDs(tds_state);
    assert ObjPID_SlimState(k_params.objs_pids, hcoded_td_id.oid) != NULL;
    assert CanActiveDevReadActiveTD(k_params, tds_state, dev_id, hcoded_td_id);

    var explored_tds, s := FindAllTDsReachableFromTDWithR(k_params, dev_id, tds_state, hcoded_td_id, [{hcoded_td_id}]);
    var processed_tds := GetExploredTDs(explored_tds, 0);

    if (!s)
    { return processed_tds, false;}

    return processed_tds, true;
}

// Return all active TDs reachable from the TD (<td_id>) with R access mode
// If any reachable TDs ref inactive objects with non-empty access modes or any
// invalid objects, then return false and empty <read_td_ids>.
// Every TD in <processed_TDs> are processed and can be read by the device.
method FindAllTDsReachableFromTDWithR(
    k_params:ReachableTDsKParams,
    dev_id:Dev_ID, tds_state:TDs_Vals, td_id:TD_ID, explored_tds:seq<set<TD_ID>> 
) returns (explored_tds':seq<set<TD_ID>>, status:bool)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires td_id in k_params.objs_td_ids
    requires ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL
        // Requirement: The TD must be active
    requires td_id in TDsStateGetTDIDs(tds_state) 
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: The device can always read the TD (<td_id>) in the 
        // given TDs' state (<tds_state>)

    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        // Requirement 1: Each explored TD is active, and can be read by the
        // device (<dev_id>)
    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
        // Requirement 2: Forall td_id2 in E[0..|E|], td_id -->* td_id2
    requires |explored_tds| >= 1 && explored_tds[0] == {td_id}
        // Requirement 3: E0 == {td_id}
    requires forall td_id1, td_id2 :: 
                td_id1 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) && 
                td_id2 in TDsStateGetTDIDs(tds_state) &&
                ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)
                ==> td_id2 in GetExploredTDs(explored_tds, 0)
        // Requirement 4: Forall td_id1 in E[0..|E|-1], and td_id1 --> td_id2 
        // ==> td_id2 must be in E[0..|E|]
    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0)
            ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
        // Requirement 5: Forall td_id2 in E[0..|E|-1], the TD (<td_id2>) has 
        // no invalid references to any I/O objects

    ensures (status == true) 
                ==> |explored_tds'| >= 1 && explored_tds'[0] == {td_id}
        // Property: After exploring TDs, the TD (<td_id>) is always in 
        // <explored_tds'>
    ensures (status == true) 
                ==> |explored_tds| <= |explored_tds'| &&
                    explored_tds'[..|explored_tds|] == explored_tds
        // Property: The TD exploration only append the new TDs at the end of 
        // <explored_tds>                    
    ensures forall td_id2 :: td_id2 in GetExploredTDs(explored_tds', 0)
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        // Property: Each explored TD is active, and can be read by the
        // device (<dev_id>)
    ensures status == true 
                ==> (forall td_id2 :: td_id2 in GetExploredTDs(explored_tds', 0)
                    ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2)))
        // Property: Forall td_id2 in explored_tds', td_id -->* td_id2
    ensures status == true
                ==> (forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) &&
                            ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL && 
                            (td_id2 == td_id || 
                                IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
                                                        // td_id -->* td_id2
                        ==> td_id2 in GetExploredTDs(explored_tds', 0))
        // Property: Forall td_id2, td_id -->* td_id2 ==> td_id2 in explored_tds'
    ensures status == true
                <==> (forall td_id2 :: td_id2 in GetExploredTDs(explored_tds', 0)
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2))
        // Property: Forall td_id2 in explored_tds', the TD (<td_id2>) has no
        // invalid references to any I/O objects


    decreases |TDsStateGetTDIDs(tds_state) - GetExploredTDs(explored_tds, 0)|
{
    var to_explore_tds:set<TD_ID> := {};
    var exploring_tds_set := explored_tds[|explored_tds| - 1];
    var exploring_tds := SetToSeq<TD_ID>(exploring_tds_set);
    var s;

    to_explore_tds, s := FindAllTDsReachableFromTDWithR_GetToExploreTDs(
                            k_params, dev_id, tds_state, td_id, explored_tds);
    if(!s)
    {    return explored_tds, false;}    
    
    if (to_explore_tds == {})
    {
        assert forall td_id1, td_id2 :: td_id1 in explored_tds[|explored_tds| - 1] &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  //td_id1 --> td_id2
                    ==> td_id2 in GetExploredTDs(explored_tds, 0);
        assert forall td_id1, td_id2 :: td_id1 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) && 
                    td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)
                    ==> td_id2 in GetExploredTDs(explored_tds, 0);
        Lemma_ExploredTDsCanBeSeparated(explored_tds);
        assert forall td_id1, td_id2 :: td_id1 in GetExploredTDs(explored_tds, 0) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  //td_id1 --> td_id2
                    ==> td_id2 in GetExploredTDs(explored_tds, 0);
        assert td_id in GetExploredTDs(explored_tds, 0);
        Lemma_ReachableTDsAreExplored(k_params, tds_state, explored_tds, td_id);

        return explored_tds, true;
    }
    else
    {
        var t_explored_tds := SeqAppend<set<TD_ID>>(explored_tds, to_explore_tds);
        assert t_explored_tds[..|explored_tds|] == explored_tds;
        assert t_explored_tds[..|t_explored_tds| - 1] == explored_tds;

        assert forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);
        assert forall td_id2 :: td_id2 in to_explore_tds
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);

        Lemma_ExploredTDsAfterAppendingIncludeOldExploredTDsAndAddedExploreTDs(t_explored_tds, explored_tds, to_explore_tds);
        assert GetExploredTDs(t_explored_tds, 0) == GetExploredTDs(explored_tds, 0) + to_explore_tds; 
        
        assert forall td_id2 :: td_id2 in GetExploredTDs(t_explored_tds, 0)
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);      
        
        Lemma_FindAllTDsReachableFromTDWithR_Req2(k_params, dev_id, tds_state,
            t_explored_tds, explored_tds, to_explore_tds, td_id);
        Lemma_FindAllTDsReachableFromTDWithR_Req4(k_params, dev_id, tds_state,
            t_explored_tds, explored_tds, to_explore_tds);
        Lemma_FindAllTDsReachableFromTDWithR_Req5(k_params, dev_id, tds_state,
            t_explored_tds, explored_tds, to_explore_tds);
        Lemma_FindAllTDsReachableFromTDWithR_ProveTermination(k_params, dev_id, tds_state,
            t_explored_tds, explored_tds, to_explore_tds);

        explored_tds', status := FindAllTDsReachableFromTDWithR(k_params, dev_id, tds_state, td_id, t_explored_tds);
        if(status == false)
        {
            return explored_tds', false;
        }
        Lemma_TransitiveSubSequence<set<TD_ID>>(explored_tds', t_explored_tds, explored_tds);
    }
}

method FindAllTDsReachableFromTDWithR_GetToExploreTDs(
    k_params:ReachableTDsKParams,
    dev_id:Dev_ID, tds_state:TDs_Vals, td_id:TD_ID, explored_tds:seq<set<TD_ID>> 
) returns (to_explore_tds':set<TD_ID>, status:bool)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires td_id in k_params.objs_td_ids
    requires ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL
        // Requirement: The TD must be active
    requires td_id in TDsStateGetTDIDs(tds_state) 
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: The device can always read the TD (<td_id>) in the 
        // given TDs' state (<tds_state>)

    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        // Requirement 1: Each explored TD is active, and can be read by the
        // device (<dev_id>)
    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
        // Requirement 2: Forall td_id2 in E[0..|E|], td_id -->* td_id2
    requires |explored_tds| >= 1 && explored_tds[0] == {td_id}
        // Requirement 3: E0 == {td_id}

    ensures (status == true)
                ==> to_explore_tds' <= TDsStateGetTDIDs(tds_state)
    ensures forall td_id2 :: td_id2 in to_explore_tds'
                    ==> td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
    ensures (status == true)
                ==> (forall td_id2 :: td_id2 in to_explore_tds'
                    ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2)))
    ensures (status == true)
                ==> (forall td_id1, td_id2 :: td_id1 in explored_tds[|explored_tds| - 1] &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  //td_id1 --> td_id2
                    ==> td_id2 in GetExploredTDs(explored_tds, 0) || td_id2 in to_explore_tds')
    ensures (status == true)
                ==> GetExploredTDs(explored_tds, 0) * to_explore_tds' == {}
    ensures (status == true)
                <==> (forall td_id2 :: td_id2 in explored_tds[|explored_tds| - 1]
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2))
{
    var to_explore_tds:set<TD_ID> := {};
    var exploring_tds_set := explored_tds[|explored_tds| - 1];
    var exploring_tds := SetToSeq<TD_ID>(exploring_tds_set);
    var i := 0;
    var input_explored_tds := GetExploredTDs(explored_tds, 0);

    assert forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                    ==> td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);

    while (i < |exploring_tds|)
        invariant i <= |exploring_tds|

        invariant to_explore_tds <= TDsStateGetTDIDs(tds_state)
        invariant forall td_id2 :: td_id2 in to_explore_tds
                    ==> td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        invariant forall td_id2 :: td_id2 in to_explore_tds
                    ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
        invariant forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                    ==> td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        
        invariant forall td_id1, td_id2 :: td_id1 in exploring_tds[..i] &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  //td_id1 --> td_id2
                    ==> td_id2 in GetExploredTDs(explored_tds, 0) || td_id2 in to_explore_tds
        invariant input_explored_tds * to_explore_tds == {}

        invariant forall td_id2 :: td_id2 in exploring_tds[..i]
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
    {
        var explore_td_id := exploring_tds[i];
        var explore_td_cfg := tds_state[explore_td_id];
        var exists_invalid_ref := DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, explore_td_id);

        if (exists_invalid_ref)
        {    return {}, false; }

        assert forall td_id2 :: td_id2 == explore_td_id
            ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2);

        var read_tds_set := TDIDReadsInTDCfg(explore_td_cfg);
        var read_tds := SetToSeq<TD_ID>(read_tds_set);

        Lemma_ActiveDevCanReadTDsRefedByActiveTDWithR(k_params, tds_state, dev_id, explore_td_id);
        assert forall td_id2 :: td_id2 in read_tds
                    ==> CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);

        var unexplored_tds := read_tds_set - input_explored_tds;
        assert unexplored_tds <= TDsStateGetTDIDs(tds_state);
        assert forall td_id2 :: td_id2 in read_tds
                    ==> td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL;
        assert forall td_id2 :: td_id2 in unexplored_tds
                    ==> td_id2 in k_params.objs_td_ids &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);

        forall td_id2 | td_id2 in unexplored_tds
            ensures td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2)
        {
            assert (td_id == explore_td_id || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, explore_td_id)); 
            assert IsActiveTDRefActiveTDWithR(k_params, tds_state, explore_td_id, td_id2);
            Lemma_TD1RefsTD2InChainWithRAlsoRefsTDsReadByTheTD2Specific(k_params, tds_state, td_id, explore_td_id, td_id2);
        }
        assert forall td_id2 :: td_id2 in unexplored_tds
                    ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2));
        assert input_explored_tds * unexplored_tds == {};

        to_explore_tds := SetConcat<TD_ID>(to_explore_tds, unexplored_tds);
        i := i + 1;
    }

    return to_explore_tds, true;
}

// Return if the active TD (<from_td_id>) refs the target active TD 
// (<to_td_id>) in chain with R access mode
// The function return true, iff there exists a list of active TDs, which 
// starts from a TD (<from_td_id> to the target TD (<to_td_id>), and one refs  
// the next one in the list with R access mode
// Note: the length of the list must be >=2, in order to include both
// <from_td_id> and <to_td_id> in the list
function IsActiveTDRefActiveTDInChainWithR(
    k_params:ReachableTDsKParams, 
    tds:TDs_Vals, from_td_id:TD_ID, to_td_id:TD_ID
) : bool
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 

    ensures IsActiveTDRefActiveTDInChainWithR(k_params, tds, from_td_id, to_td_id)
                <==> (exists td_ids:seq<TD_ID> :: |td_ids| >= 2 && 
                     (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) && // A list of active TDs
                     td_ids[|td_ids| - 1] == to_td_id && // last TD is the target TD (<to_td_id>)
                     td_ids[0] == from_td_id && // first TD is the source TD (<from_td_id>)
                                                      // Each TD in the list is active
                     (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]])))
                                                      // previous TD always refs the current TD with R access mode
{
    exists td_ids:seq<TD_ID> :: |td_ids| >= 2 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) && // A list of active TDs
            td_ids[|td_ids| - 1] == to_td_id && // last TD is the target TD (<to_td_id>)
            td_ids[0] == from_td_id && // first TD is the source TD (<from_td_id>)
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]))
}

// Return if the active TD (<from_td_id>) refs the target active TD 
// (<to_td_id>) with R access mode
function IsActiveTDRefActiveTDWithR( 
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, from_td_id:TD_ID, to_td_id:TD_ID
) : bool
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 

    requires from_td_id in TDsStateGetTDIDs(tds)
    requires to_td_id in TDsStateGetTDIDs(tds)
    requires ObjPID_SlimState(k_params.objs_pids, from_td_id.oid) != NULL
    requires ObjPID_SlimState(k_params.objs_pids, to_td_id.oid) != NULL
        // Requirement: The source TD and the target TD are active

    ensures IsActiveTDRefActiveTDWithR(k_params, tds, from_td_id, to_td_id)
                <==> to_td_id in TDIDReadsInTDCfg(tds[from_td_id])
{
    to_td_id in TDIDReadsInTDCfg(tds[from_td_id])
}




//******** Utility Functions ********//
// Returns all TDs recorded in <explored_tds> from the index <lvl> to the end
// of the sequence
function method GetExploredTDs(explored_tds:seq<set<TD_ID>>, lvl:int) : set<TD_ID>
    requires 0 <= lvl <= |explored_tds|

    ensures forall i :: lvl <= i <|explored_tds|
                ==> explored_tds[i] <= GetExploredTDs(explored_tds, lvl)
    ensures forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, lvl)
                ==> exists i :: lvl <= i <|explored_tds| && td_id2 in explored_tds[i]

    decreases |explored_tds| - lvl
{
    if(lvl == |explored_tds|) then
        {}
    else
        explored_tds[lvl] + GetExploredTDs(explored_tds, lvl + 1)
}




/******** Lemmas for TDs *******/ 
// Lemma: All TDs the (active) device has hardcoded R access mode to are (1)
// active, and (2) can be read by the device
lemma Lemma_ActiveDevCanReadTheirHCodedTDs(
    k_params:ReachableTDsKParams, 
    tds_state:TDs_Vals, dev_id:Dev_ID
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
    // Requirements required by functions in this function method

    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k_params.subjects.drvs) && (Dev_ID(dev_sid) in k_params.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall dev_id, td_id :: dev_id in k_params.hcoded_tds && td_id in k_params.hcoded_tds[dev_id].trans_params_tds
                ==> td_id in IDToDev_SlimState(k_params.subjects, dev_id).td_ids
    requires forall dev_id, fd_id :: dev_id in k_params.hcoded_tds && fd_id in k_params.hcoded_tds[dev_id].trans_params_fds
                ==> fd_id in IDToDev_SlimState(k_params.subjects, dev_id).fd_ids
    requires forall dev_id, do_id :: dev_id in k_params.hcoded_tds && do_id in k_params.hcoded_tds[dev_id].trans_params_dos
                ==> do_id in IDToDev_SlimState(k_params.subjects, dev_id).do_ids

    requires forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices

    requires forall s_id, o_id :: s_id in AllSubjsIDs(k_params.subjects) &&
                    DoOwnObj_SlimState(k_params.subjects, s_id, o_id)
                ==> o_id in k_params.objs_pids &&
                    k_params.objs_pids[o_id] == SubjPID_SlimState(k_params.subjects, s_id)
        // Requirement: If a subject owns an object, then the subject and the 
        // object must be in the same partition
    
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires k_params.subjects.devs[dev_id].hcoded_td_id in tds_state
                ==> tds_state[k_params.subjects.devs[dev_id].hcoded_td_id] == k_params.hcoded_tds[dev_id]
        // Requirement: If hardcoded TDs are in <tds_state>, their values are always from <k_params.hcoded_tds>

    ensures forall td_id :: td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
                ==> td_id.oid in k_params.objs_pids
    ensures forall td_id :: td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
                ==> td_id in tds_state
        // Properties needed by the properties below
    ensures forall td_id :: td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
                ==> ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL
        // Property: All TDs the (active) device has hardcoded R access mode
        // to are active
    ensures forall td_id :: td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
                ==> CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id);
        // Property: All TDs the (active) device has hardcoded R access mode 
        // to can be read by the device
{
    var hcoded_td_id := k_params.subjects.devs[dev_id].hcoded_td_id;

    Lemma_DevsOwnHCodedTDs(k_params.subjects, dev_id, hcoded_td_id);
    assert DoOwnObj_SlimState(k_params.subjects, dev_id.sid, hcoded_td_id.oid);

    forall td_id | td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
        ensures td_id in tds_state
    {
        assert td_id in IDToDev_SlimState(k_params.subjects, dev_id).td_ids;

        assert DoOwnObj_SlimState(k_params.subjects, dev_id.sid, td_id.oid);
    }

    forall td_id | td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
        ensures CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
    {
        var td_ids:seq<TD_ID> := [hcoded_td_id, td_id];

        assert |td_ids| >= 1 && 
                (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state) &&
                td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
                                                // Each TD in the list is active
                (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]));
    }
}

lemma Lemma_ActiveDevCanReadTDsRefedByActiveTDWithR(
    k_params:ReachableTDsKParams,  
    tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires td_id in k_params.objs_td_ids
    requires ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL
        // Requirement: The TD must be active
    requires td_id in TDsStateGetTDIDs(tds_state) 
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: The device can always read the TD (<td_id>) in the 
        // given TDs' state (<tds_state>)
        
    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id)
     
    ensures forall td_id2 :: td_id2 in TDIDReadsInTDCfg(tds_state[td_id])
                    ==> CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
{
    var read_tds_from_td := TDIDReadsInTDCfg(tds_state[td_id]);

    forall td_ids:seq<TD_ID>| 
            (|td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in TDsStateGetTDIDs(tds_state)) &&
            td_ids[|td_ids| - 1] == td_id && // last element is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]])))
        ensures forall td_id2 :: td_id2 in read_tds_from_td
            ==> CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
    {
        forall td_id3:TD_ID | (td_id3 in read_tds_from_td) 
            ensures CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id3)
        {
            var td_ids_new:seq<TD_ID> := td_ids + [td_id3];

            assert  |td_ids_new| >= 1 &&
                    (forall td_id2 :: td_id2 in td_ids_new ==> td_id2 in TDsStateGetTDIDs(tds_state)) &&
                    td_ids_new[|td_ids_new| - 1] == td_id3 && // last element is the TD (<td_id3>)
                    td_ids_new[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                    (forall i :: 0<=i<|td_ids_new| ==> ObjPID_SlimState(k_params.objs_pids, td_ids_new[i].oid) != NULL) && 
                    (forall i :: 0<=i<|td_ids_new| - 1 ==> td_ids_new[i+1] in TDIDReadsInTDCfg(tds_state[td_ids_new[i]]));

            assert CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id3);
        }
    }
}

// Lemma: All root TDs read by the device (<dev_id>) are returned in 
// TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id) function
lemma Lemma_AllHCodedTDsReadByDevAreReturned(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID
)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires (forall td_id, fd_id :: TD_ID(td_id) in k_params.objs_td_ids && FD_ID(fd_id) in k_params.objs_fd_ids
                ==> td_id != fd_id) &&
            (forall td_id, do_id :: TD_ID(td_id) in k_params.objs_td_ids && DO_ID(do_id) in k_params.objs_do_ids
                ==> td_id != do_id) &&
            (forall fd_id, do_id :: FD_ID(fd_id) in k_params.objs_fd_ids && DO_ID(do_id) in k_params.objs_do_ids
                ==> fd_id != do_id)
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)

    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k_params.subjects.drvs) && (Dev_ID(dev_sid) in k_params.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall dev_id, fd_id :: 
                dev_id in k_params.subjects.devs && fd_id in k_params.subjects.devs[dev_id].fd_ids
                ==> fd_id in k_params.objs_fd_ids
    requires forall dev_id, do_id :: 
                dev_id in k_params.subjects.devs && do_id in k_params.subjects.devs[dev_id].do_ids
                ==> do_id in k_params.objs_do_ids

    ensures forall hcoded_td_id:TD_ID :: hcoded_td_id in k_params.objs_td_ids &&
                DoObjRefedInDevHCodedTD(k_params.hcoded_tds, dev_id, hcoded_td_id.oid) && 
                R in AModesToObjInDevHCodedTD(k_params.hcoded_tds, dev_id, hcoded_td_id.oid)
                <==> hcoded_td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
{
    assert forall hcoded_td_id:TD_ID :: hcoded_td_id in k_params.objs_td_ids &&
            DoObjRefedInDevHCodedTD(k_params.hcoded_tds, dev_id, hcoded_td_id.oid) && 
            R in AModesToObjInDevHCodedTD(k_params.hcoded_tds, dev_id, hcoded_td_id.oid)
            <==> hcoded_td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id);
}

lemma Lemma_RootTDsAndAllActiveTDsRefedByRootTDsAreAllTDsReadByDev(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, dev_id:Dev_ID, hcoded_td_id:TD_ID, t_td_ids:set<TD_ID>
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active

    requires hcoded_td_id == k_params.subjects.devs[dev_id].hcoded_td_id
        // Requirement: <hcoded_td_id> is the ID of the hardcoded TD in the 
        // device (<dev_id>)

    requires forall td_id2 :: td_id2 in k_params.objs_td_ids &&
                ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, hcoded_td_id, td_id2)
                ==> td_id2 in t_td_ids
        // Requirement: All TDs refed by a root TD in chain with R access mode 
        // are in <t_td_ids> 
    requires hcoded_td_id in t_td_ids
        // Requirement: Hardcoded TD of the device are also in <t_td_ids>

    ensures forall td_id2 :: td_id2 in k_params.objs_td_ids && 
                ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                    // For all active TDs can be read by the device
                ==> td_id2 in t_td_ids
        // Property: All active TDs can be read by the device is in <t_td_ids>
{
    assert TDsStateGetTDIDs(tds_state) == k_params.all_active_tds;

    forall td_ids:seq<TD_ID>, td_id2 | 
            |td_ids| >= 1 && 
            (forall td_id3 :: td_id3 in td_ids ==> td_id3 in TDsStateGetTDIDs(tds_state)) &&
            td_ids[|td_ids| - 1] == td_id2 && // last TD is the TD (<td_id2>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
                                            // Each TD in the list is active
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]])) && 
            (td_id2 != hcoded_td_id)
        ensures IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, hcoded_td_id, td_id2)
    {
        assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_ids[0], td_id2);
         
    }

    assert (forall td_id2 :: td_id2 in k_params.objs_td_ids && 
                ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                    // For all active TDs can be read by the device
                ==> td_id2 in t_td_ids);
}

// Lemma: TDs refed by a TD with R access mode is also refed by the TD in chain 
lemma Lemma_TDsRefedByTDAlsoRefedByTDInChain( 
    k_params:ReachableTDsKParams, 
    tds:TDs_Vals, from_td_id:TD_ID, to_td_id:TD_ID
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires from_td_id in TDsStateGetTDIDs(tds)
    requires to_td_id in TDsStateGetTDIDs(tds)
    requires ObjPID_SlimState(k_params.objs_pids, from_td_id.oid) != NULL
    requires ObjPID_SlimState(k_params.objs_pids, to_td_id.oid) != NULL
        // Requirement: The source TD and the target TD are active

    requires IsActiveTDRefActiveTDWithR(k_params, tds, from_td_id, to_td_id)

    ensures IsActiveTDRefActiveTDInChainWithR(k_params, tds, from_td_id, to_td_id)
{
    var td_ids:seq<TD_ID> := [from_td_id, to_td_id];

    assert forall i :: 0<=i<|td_ids| 
            ==> td_ids[i] in TDsStateGetTDIDs(tds);

    assert forall i :: 0<=i<|td_ids| 
            ==> td_ids[i] in k_params.objs_td_ids;

    assert |td_ids| >= 2 && 
        (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
        td_ids[|td_ids| - 1] == to_td_id && // last TD is the target TD (<to_td_id>)
        td_ids[0] == from_td_id && // first TD is the source TD (<from_td_id>)
        (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
                                        // Each TD in the list is active
        (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]));
}

// Lemma: If TD1 refs TD2 in chain with R access mode, then all TDs refed by 
// TD2 with R access mode are also refed by TD1 in chain with R access mode 
lemma Lemma_TD1RefsTD2InChainWithRAlsoRefsTDsReadByTheTD2(
    k_params:ReachableTDsKParams, 
    tds_state:TDs_Vals
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    ensures forall td_id1, td_id2, td_id3 ::
                td_id1 in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, td_id1.oid) != NULL &&
                td_id2 in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                td_id3 in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, td_id3.oid) != NULL &&
                (td_id1 == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2)) &&
                IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id2, td_id3)
                ==> (td_id1 == td_id3 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3))
        // Property: If td_id1 -->* td_id2, td_id2 --> td_id3, then td_id1 -->* td_id3
{
    forall td_id1, td_id2, td_id3 | td_id1 in k_params.objs_td_ids && ObjPID_SlimState(k_params.objs_pids, td_id1.oid) != NULL &&
                td_id2 in k_params.objs_td_ids && ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                td_id3 in k_params.objs_td_ids && ObjPID_SlimState(k_params.objs_pids, td_id3.oid) != NULL &&
                (td_id1 == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2)) &&
                IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id2, td_id3)
            ensures (td_id1 == td_id3 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3))
    {
        if (!IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2))
        {
            assert td_id1 == td_id2;
            assert IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id2, td_id3);
            Lemma_TDsRefedByTDAlsoRefedByTDInChain(k_params, tds_state, td_id2, td_id3);
            assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id2, td_id3);
        }
        else
        {
            assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2);
            forall td_ids:seq<TD_ID> |  |td_ids| >= 2 && 
                     (forall td_id4 :: td_id4 in td_ids ==> td_id4 in tds_state) &&
                     td_ids[|td_ids| - 1] == td_id2 && // last TD is the target TD (<to_td_id>)
                     td_ids[0] == td_id1 && // first TD is the source TD (<from_td_id>)
                     (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
                                                      // Each TD in the list is active
                     (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]))
                ensures IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3)
            {
                var new_td_ids := SeqAppend<TD_ID>(td_ids, td_id3);

                assert |new_td_ids| >= 2 && 
                     (forall td_id4 :: td_id4 in td_ids ==> td_id4 in tds_state) &&
                     new_td_ids[|new_td_ids| - 1] == td_id3 && // last TD is the target TD (<to_td_id>)
                     new_td_ids[0] == td_id1 && // first TD is the source TD (<from_td_id>)
                     (forall i :: 0<=i<|new_td_ids| ==> ObjPID_SlimState(k_params.objs_pids, new_td_ids[i].oid) != NULL) &&
                                                      // Each TD in the list is active
                     (forall i :: 0<=i<|new_td_ids| - 1 ==> new_td_ids[i+1] in TDIDReadsInTDCfg(tds_state[new_td_ids[i]]));

                assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3);
            }
        }
    }
}

// Lemma: If TD1 refs TD2 in chain with R access mode, then all TDs refed by 
// TD2 with R access mode are also refed by TD1 in chain with R access mode 
lemma Lemma_TD1RefsTD2InChainWithRAlsoRefsTDsReadByTheTD2Specific(
    k_params:ReachableTDsKParams, 
    tds_state:TDs_Vals, td_id1:TD_ID, td_id2:TD_ID, td_id3:TD_ID
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires td_id1 in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, td_id1.oid) != NULL
    requires td_id2 in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
    requires td_id3 in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, td_id3.oid) != NULL
    requires td_id1 == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2)
    requires IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id2, td_id3)

    ensures td_id1 == td_id3 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3)
        // Property: If td_id1 -->* td_id2, td_id2 --> td_id3, then td_id1 -->* td_id3
{
    if (!IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2))
    {
        assert td_id1 == td_id2;
        assert IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id2, td_id3);
        Lemma_TDsRefedByTDAlsoRefedByTDInChain(k_params, tds_state, td_id2, td_id3);
        assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id2, td_id3);
    }
    else
    {
        assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id2);

        forall td_ids:seq<TD_ID> |  |td_ids| >= 2 && 
                    (forall td_id4 :: td_id4 in td_ids ==> td_id4 in k_params.objs_td_ids) &&
                    td_ids[|td_ids| - 1] == td_id2 && // last TD is the target TD (<to_td_id>)
                    td_ids[0] == td_id1 && // first TD is the source TD (<from_td_id>)
                    (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
                                                    // Each TD in the list is active
                    (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]))
            ensures IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3)
        {
            var new_td_ids := SeqAppend<TD_ID>(td_ids, td_id3);

            assert |new_td_ids| >= 2 && 
                    (forall td_id4 :: td_id4 in td_ids ==> td_id4 in k_params.objs_td_ids) &&
                    new_td_ids[|new_td_ids| - 1] == td_id3 && // last TD is the target TD (<to_td_id>)
                    new_td_ids[0] == td_id1 && // first TD is the source TD (<from_td_id>)
                    (forall i :: 0<=i<|new_td_ids| ==> ObjPID_SlimState(k_params.objs_pids, new_td_ids[i].oid) != NULL) &&
                                                    // Each TD in the list is active
                    (forall i :: 0<=i<|new_td_ids| - 1 ==> new_td_ids[i+1] in TDIDReadsInTDCfg(tds_state[new_td_ids[i]]));

            assert IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id1, td_id3);
        }
    }
}




//******** Utility Lemmas ********//
// Lemma: If <new_explored_tds> is <old_explored_tds > appended with 
// <add_explore_tds>, then: GetExploredTDs(new_explored_tds, 0) == 
// GetExploredTDs(old_explored_tds, 0) + add_explore_tds
lemma Lemma_ExploredTDsAfterAppendingIncludeOldExploredTDsAndAddedExploreTDs(
    new_explored_tds:seq<set<TD_ID>>, old_explored_tds:seq<set<TD_ID>>, add_explore_tds:set<TD_ID>
)
        requires new_explored_tds == SeqAppend<set<TD_ID>>(old_explored_tds, add_explore_tds)

        ensures GetExploredTDs(new_explored_tds, 0) == GetExploredTDs(old_explored_tds, 0) + add_explore_tds
{
    // Dafny can prove this lemma automatically
}

// Lemma: If all TDs read by any explored TDs are explored, then forall TDs 
// reachable from an explored TD (<td_id>), the TDs are explored
lemma Lemma_ReachableTDsAreExplored(
    k_params:ReachableTDsKParams, 
    tds_state:TDs_Vals, explored_tds:seq<set<TD_ID>>, td_id:TD_ID
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
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires forall td_id2 :: (exists i :: 0 <= i < |explored_tds| && td_id2 in explored_tds[i])
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL 
        // Requirement: Each explored TD is active
    requires forall td_id1, td_id2 :: td_id1 in GetExploredTDs(explored_tds, 0) &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  // td_id1 --> td_id2
                ==> td_id2 in GetExploredTDs(explored_tds, 0)
        // Requirement: Forall td_id2 and explored TD (<td_id1>), if 
        // td_id1 --> td_id2, then td_id2 is also explored
    requires td_id in GetExploredTDs(explored_tds, 0)
        // Requirement: td_id in GetExploredTDs(explored_tds, 0)

    ensures forall td_id2 :: td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL && 
                    (td_id2 == td_id || 
                        IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
                                                // td_id -->* td_id2
                ==> td_id2 in GetExploredTDs(explored_tds, 0)
        // Property: Forall td_id2, td_id -->* td_id2, td_id2 in explored
{
    assert forall td_id2 :: td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL && 
                    td_id2 == td_id 
                ==> td_id2 in GetExploredTDs(explored_tds, 0);

    forall td_ids:seq<TD_ID>, td_id2| 
            td_id2 in k_params.objs_td_ids &&
            ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL && 
            (|td_ids| >= 1 && 
            (forall td_id3 :: td_id3 in td_ids ==> td_id3 in tds_state) &&
            td_ids[|td_ids| - 1] == td_id2 && // last TD is the target TD (<to_td_id>)
            td_ids[0] == td_id && // first TD is the source TD (<from_td_id>)
            (forall i :: 0<=i<|td_ids| ==> ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL) &&
                                            // Each TD in the list is active
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]])))
                                            // previous TD always refs the current TD with R access mode)
        ensures td_id2 in GetExploredTDs(explored_tds, 0)
    {
        var i := 0;
        assert forall i :: 0 <= i < |td_ids| - 1 
                ==> IsActiveTDRefActiveTDWithR(k_params, tds_state, td_ids[i], td_ids[i+1]);
        assert forall i :: 0 <= i < |td_ids|
                ==> td_ids[i] in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_ids[i].oid) != NULL;
        assert td_ids[0] in GetExploredTDs(explored_tds, 0);

        while(i < |td_ids|-1)
            invariant i <= |td_ids|-1
    
            invariant td_ids[i] in GetExploredTDs(explored_tds, 0)
            invariant forall p :: 0 <= p <= i
                    ==> td_ids[p] in GetExploredTDs(explored_tds, 0)
        {
            assert IsActiveTDRefActiveTDWithR(k_params, tds_state, td_ids[i], td_ids[i+1]);
            assert td_ids[i+1] in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_ids[i+1].oid) != NULL;

            assert td_ids[i+1] in GetExploredTDs(explored_tds, 0);
            i := i + 1;
        }
        assert forall td_id2 :: td_id2 in td_ids 
                ==> td_id2 in GetExploredTDs(explored_tds, 0);
    }
}

lemma Lemma_ExploredTDsCanBeSeparated(explored_tds:seq<set<TD_ID>>)
    requires |explored_tds| > 0
    ensures GetExploredTDs(explored_tds, 0) == GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) + explored_tds[|explored_tds| - 1]
{
    // Dafny can automatically prove the lemma
}

lemma Lemma_FindAllTDsReachableFromTDWithR_Req2(
    k_params:ReachableTDsKParams,
    dev_id:Dev_ID, tds_state:TDs_Vals, t_explored_tds:seq<set<TD_ID>>, explored_tds:seq<set<TD_ID>>, to_explore_tds:set<TD_ID>, td_id:TD_ID
)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires td_id in k_params.objs_td_ids
    requires ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL
        // Requirement: The TD must be active

    requires |explored_tds| > 0
    requires t_explored_tds == SeqAppend<set<TD_ID>>(explored_tds, to_explore_tds)

    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
    requires forall td_id2 :: td_id2 in to_explore_tds
                ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
    requires forall td_id2 :: td_id2 in GetExploredTDs(t_explored_tds, 0)
                ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL

    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
    requires forall td_id2 :: td_id2 in to_explore_tds
                ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))

    ensures forall td_id2 :: td_id2 in GetExploredTDs(t_explored_tds, 0)
                ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2))
{
    assert td_id in k_params.objs_td_ids;
    assert td_id in TDsStateGetTDIDs(tds_state);

    Lemma_ExploredTDsAfterAppendingIncludeOldExploredTDsAndAddedExploreTDs(t_explored_tds, explored_tds, to_explore_tds);
    assert GetExploredTDs(t_explored_tds, 0) == GetExploredTDs(explored_tds, 0) + to_explore_tds;
    assert forall td_id2 :: td_id2 in GetExploredTDs(t_explored_tds, 0)
                ==> (td_id == td_id2 || IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, td_id, td_id2));
}

lemma Lemma_FindAllTDsReachableFromTDWithR_Req4(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, tds_state:TDs_Vals, t_explored_tds:seq<set<TD_ID>>, explored_tds:seq<set<TD_ID>>, to_explore_tds:set<TD_ID>
)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active

    requires |explored_tds| > 0
    requires t_explored_tds == SeqAppend<set<TD_ID>>(explored_tds, to_explore_tds)
    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)

    
    requires forall td_id1, td_id2 :: 
                    td_id1 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) && 
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)
                    ==> td_id2 in GetExploredTDs(explored_tds, 0)
    requires forall td_id1, td_id2 :: td_id1 in explored_tds[|explored_tds| - 1] &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  //td_id1 --> td_id2
                    ==> td_id2 in GetExploredTDs(explored_tds, 0) || td_id2 in to_explore_tds
    
    ensures forall td_id1, td_id2 :: 
                    td_id1 in GetExploredTDs(explored_tds, 0) && 
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)
                    ==> td_id2 in GetExploredTDs(t_explored_tds, 0)
{
    Lemma_ExploredTDsCanBeSeparated(explored_tds);
    assert GetExploredTDs(explored_tds, 0) == 
        GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) + explored_tds[|explored_tds| - 1];

    forall td_id1, td_id2 | td_id1 in GetExploredTDs(explored_tds, 0) && 
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)
        ensures td_id2 in GetExploredTDs(t_explored_tds, 0)
    {
        if(td_id1 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0))
        {
            assert forall td_id1, td_id2 :: 
                    td_id1 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) && 
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)
                    ==> td_id2 in GetExploredTDs(t_explored_tds, 0);
        }
        else
        {
            assert td_id1 in explored_tds[|explored_tds| - 1];
            assert forall td_id1, td_id2 :: td_id1 in explored_tds[|explored_tds| - 1] &&
                    td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                    IsActiveTDRefActiveTDWithR(k_params, tds_state, td_id1, td_id2)  //td_id1 --> td_id2
                    ==> td_id2 in GetExploredTDs(t_explored_tds, 0);
        }
    }
}

lemma Lemma_FindAllTDsReachableFromTDWithR_Req5(
    k_params:ReachableTDsKParams,
    dev_id:Dev_ID, tds_state:TDs_Vals, t_explored_tds:seq<set<TD_ID>>, explored_tds:seq<set<TD_ID>>, to_explore_tds:set<TD_ID>
)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active

    requires |explored_tds| > 0
    requires t_explored_tds == SeqAppend<set<TD_ID>>(explored_tds, to_explore_tds)

    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds, 0)
                ==> td_id2 in TDsStateGetTDIDs(tds_state)
    requires forall td_id2 :: td_id2 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0)
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
    requires forall td_id2 :: td_id2 in explored_tds[|explored_tds| - 1]
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)

    
    ensures forall td_id2 :: td_id2 in GetExploredTDs(t_explored_tds[..|t_explored_tds| - 1], 0)
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
{
    Lemma_ExploredTDsCanBeSeparated(explored_tds);
    assert GetExploredTDs(explored_tds, 0) == 
        GetExploredTDs(explored_tds[..|explored_tds| - 1], 0) + explored_tds[|explored_tds| - 1];

    forall td_id2 | td_id2 in GetExploredTDs(explored_tds, 0)
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
    {
        if(td_id2 in GetExploredTDs(explored_tds[..|explored_tds| - 1], 0))
        {
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2);
        }
        else
        {
            assert td_id2 in explored_tds[|explored_tds| - 1];
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2);
        }
    }

    assert t_explored_tds[..|t_explored_tds| - 1] == explored_tds;
}

lemma Lemma_FindAllTDsReachableFromTDWithR_ProveTermination(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, tds_state:TDs_Vals, t_explored_tds:seq<set<TD_ID>>, explored_tds:seq<set<TD_ID>>, to_explore_tds:set<TD_ID>
)
    requires FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active

    requires |explored_tds| > 0
    requires t_explored_tds == SeqAppend<set<TD_ID>>(explored_tds, to_explore_tds)

    requires GetExploredTDs(explored_tds, 0) <= TDsStateGetTDIDs(tds_state)
    requires GetExploredTDs(t_explored_tds, 0) <= TDsStateGetTDIDs(tds_state) 
    requires GetExploredTDs(explored_tds, 0) * to_explore_tds == {}
    requires to_explore_tds != {}

    
    ensures |TDsStateGetTDIDs(tds_state) - GetExploredTDs(t_explored_tds, 0)| < |TDsStateGetTDIDs(tds_state) - GetExploredTDs(explored_tds, 0)|
{
    Lemma_ExploredTDsAfterAppendingIncludeOldExploredTDsAndAddedExploreTDs(t_explored_tds, explored_tds, to_explore_tds);
    assert GetExploredTDs(t_explored_tds, 0) == GetExploredTDs(explored_tds, 0) + to_explore_tds;
    assert GetExploredTDs(explored_tds, 0) < GetExploredTDs(t_explored_tds, 0);
    assert GetExploredTDs(explored_tds, 0) <= TDsStateGetTDIDs(tds_state);
    assert GetExploredTDs(t_explored_tds, 0) <= TDsStateGetTDIDs(tds_state);
    assert TDsStateGetTDIDs(tds_state) - GetExploredTDs(explored_tds, 0) > TDsStateGetTDIDs(tds_state) - GetExploredTDs(t_explored_tds, 0);
}