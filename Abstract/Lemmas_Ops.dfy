include "Syntax.dfy"
include "Properties.dfy"
include "Properties_Corollaries.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"

//******** Lemmas for All Operations  ********//
lemma Lemma_ValidK_HCodedTDsAreTDs(k:State)
    requires IsValidState(k)
    ensures forall dev_id :: dev_id in k.subjects.devs
        ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ValidState_FulfillCanActiveDevReadActiveTDPreConditions(k:State)
    requires IsValidState(k)
    ensures forall td_id2, dev_id, tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    dev_id in AllActiveDevs(k) && 
                    td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k:State, k_params:ReachableTDsKParams)
    requires IsValidState(k) && IsSecureState(k)
    
    requires k_params == KToKParams(k) 

    ensures forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k:State, k_params:ReachableTDsKParams)
    requires IsValidState(k) && IsSecureState(k)
    
    requires k_params == KToKParams(k)  

    ensures FindAllTDsReadByDev_KParams_PreConditions(k_params)
{
    var k_params := KToKParams(k);

    assert (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
        ==> SubjPID(k, s_id) == ObjPID(k, o_id));

    assert k.subjects == k_params.subjects;
    forall s_id, o_id | s_id in AllSubjsIDs(k_params.subjects) &&
                    DoOwnObj_SlimState(k_params.subjects, s_id, o_id)
        ensures o_id in k_params.objs_pids
        ensures k_params.objs_pids[o_id] == SubjPID_SlimState(k_params.subjects, s_id)
    {
        assert s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id);
        assert SubjPID(k, s_id) == ObjPID(k, o_id);
    }
}

// Lemma: Hardcoded TDs are unmodified between states
lemma Lemma_NewStateVars_HCodedTDsAreUnmodified(k:State, k'_subjects:Subjects, k'_objects:Objects)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids
        // Requirement: The IDs of TDs owned by a device is not changed

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val)

    ensures AllHCodedTDIDs(k'_subjects) == AllHCodedTDIDs(k.subjects)
    ensures BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)
    ensures MapGetKeys(BuildMap_ObjIDsToPIDs(k'_objects)) == MapGetKeys(BuildMap_ObjIDsToPIDs(k.objects))
{
    Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);
}

lemma Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(
    k:State, k'_objects_tds:map<TD_ID, TD_State>, k'_tds_to_all_states:map<set<TD_ID>, set<TDs_Vals>>
)
    requires forall td_ids :: td_ids in k'_tds_to_all_states
                <==> td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires MapGetKeys(k'_objects_tds) == MapGetKeys(k.objects.tds)

    ensures forall td_ids :: td_ids in k'_tds_to_all_states
                <==> td_ids <= MapGetKeys<TD_ID, TD_State>(k'_objects_tds)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(
    k'_objects_tds:map<TD_ID, TD_State>,
    k'_tds_to_all_states:map<set<TD_ID>, set<TDs_Vals>>, k'_active_tds:set<TD_ID>
)
    requires forall td_id :: td_id in k'_active_tds
                ==> td_id in k'_objects_tds
    requires k'_active_tds == AllActiveTDs_SlimState(k'_objects_tds)
    requires forall td_ids :: td_ids in k'_tds_to_all_states
                <==> td_ids <= MapGetKeys<TD_ID, TD_State>(k'_objects_tds)

    ensures k'_active_tds in k'_tds_to_all_states
{
    // Dafny can automatically prove this lemma
}


lemma Lemma_NewK_FulfillIsValidStateObjects(k:State, k':State)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos)
    requires forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)

    requires AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)
    requires BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)
    requires k'.tds_to_all_states == k.tds_to_all_states

    requires IsValidState_Objects(k)

    ensures IsValidState_Objects(k')
{
    assert forall dev_id :: dev_id in k'.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids);
    Lemma_SameObjsOwnershipInSuccessiveStates(k, k');

    Lemma_NewK_FulfillCondition24(k, k');
}

lemma Lemma_IsValidState_SubjectsObjects_Properties(k:State, k_params:ReachableTDsKParams)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires k_params == KToKParams(k)

    ensures TDsStateGetTDIDs(ActiveTDsState(k)) == AllActiveTDs(k)
    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    
    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys(k.objects.tds)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params:ReachableTDsKParams, k'_params:ReachableTDsKParams)
    //requires k'_params.subjects == k_params.subjects
    requires MapGetKeys<Drv_ID, Drv_State>(k'_params.subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k_params.subjects.drvs)
    requires MapGetKeys<Dev_ID, Dev_State>(k'_params.subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k_params.subjects.devs)
    requires forall drv_id :: drv_id in k_params.subjects.drvs
                ==> (k'_params.subjects.drvs[drv_id].td_ids == k_params.subjects.drvs[drv_id].td_ids) &&
                    (k'_params.subjects.drvs[drv_id].fd_ids == k_params.subjects.drvs[drv_id].fd_ids) &&
                    (k'_params.subjects.drvs[drv_id].do_ids == k_params.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k_params.subjects.devs
                ==> (k'_params.subjects.devs[dev_id].td_ids == k_params.subjects.devs[dev_id].td_ids) &&
                    (k'_params.subjects.devs[dev_id].fd_ids == k_params.subjects.devs[dev_id].fd_ids) &&
                    (k'_params.subjects.devs[dev_id].do_ids == k_params.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k_params.subjects.devs
                ==> k'_params.subjects.devs[dev_id].hcoded_td_id == k_params.subjects.devs[dev_id].hcoded_td_id

    requires k'_params.objs_td_ids == k_params.objs_td_ids
    requires k'_params.objs_fd_ids == k_params.objs_fd_ids
    requires k'_params.objs_do_ids == k_params.objs_do_ids
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    requires MapGetKeys(k'_params.objs_pids) == MapGetKeys(k_params.objs_pids)

    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    requires forall td_id2 :: td_id2 in k'_params.all_active_tds
                <==> td_id2 in k'_params.objs_td_ids &&
                    ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) != NULL
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids &&
                    k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)

    ensures FindAllTDsReadByDev_KParams_PreConditions(k'_params)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewKParams_SameSubjIDsOwnershipInSuccessiveStates(
    k:State, k'_subjects:Subjects, k_params:ReachableTDsKParams, k'_params:ReachableTDsKParams
)
    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires (forall drv_id :: drv_id in k'_subjects.drvs
            ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
            (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
            (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids))
    requires (forall dev_id :: dev_id in k'_subjects.devs
            ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
            (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
            (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
            (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids))

    requires k_params.subjects == k.subjects
    requires k'_params.subjects == k'_subjects

    ensures MapGetKeys<Drv_ID, Drv_State>(k'_params.subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k_params.subjects.drvs)
    ensures MapGetKeys<Dev_ID, Dev_State>(k'_params.subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k_params.subjects.devs)
    ensures forall drv_id :: drv_id in k_params.subjects.drvs
                ==> (k'_params.subjects.drvs[drv_id].td_ids == k_params.subjects.drvs[drv_id].td_ids) &&
                    (k'_params.subjects.drvs[drv_id].fd_ids == k_params.subjects.drvs[drv_id].fd_ids) &&
                    (k'_params.subjects.drvs[drv_id].do_ids == k_params.subjects.drvs[drv_id].do_ids)
    ensures forall dev_id :: dev_id in k_params.subjects.devs
                ==> (k'_params.subjects.devs[dev_id].td_ids == k_params.subjects.devs[dev_id].td_ids) &&
                    (k'_params.subjects.devs[dev_id].fd_ids == k_params.subjects.devs[dev_id].fd_ids) &&
                    (k'_params.subjects.devs[dev_id].do_ids == k_params.subjects.devs[dev_id].do_ids)
    ensures forall dev_id :: dev_id in k_params.subjects.devs
                ==> k'_params.subjects.devs[dev_id].hcoded_td_id == k_params.subjects.devs[dev_id].hcoded_td_id
{
    assert forall drv_id :: drv_id in k_params.subjects.drvs
                ==> (k'_params.subjects.drvs[drv_id].td_ids == k_params.subjects.drvs[drv_id].td_ids) &&
                    (k'_params.subjects.drvs[drv_id].fd_ids == k_params.subjects.drvs[drv_id].fd_ids) &&
                    (k'_params.subjects.drvs[drv_id].do_ids == k_params.subjects.drvs[drv_id].do_ids);
}

// Lemma:  In the current active TDs' state of k, any active TDs read by any 
// active devices have no invalid references to I/O objects
// (needs 50s to verify)
lemma Lemma_CurrentActiveTDsStateOnlyHasValidRefs(k:State, k_reachable_active_tds_states:set<TDs_Vals>)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id 
        // Requirement: Objects have different internal IDs
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Requirement: Subjects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
        // Requirement: k fulfills Condition 5.1 of <IsValidState_ReachableTDsStates>
    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2))
        // Requirement: k fulfills Condition 5.5 of <IsValidState_HelperStateVariables>
    requires ActiveTDsState(k) in k_reachable_active_tds_states
        // Requirement: k fulfills Condition 5.6 of <IsValidState_HelperStateVariables>

    ensures forall td_id2, dev_id :: 
            dev_id in AllActiveDevs(k) && 
                // The device (<dev_id>) is active
            td_id2 in AllActiveTDs(k) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), ActiveTDsState(k), td_id2)
        // Property: In the current active TDs' state of k, any active TDs read 
        // by any active devices have no invalid references to I/O objects
{
    // Dafny can automatically prove this lemma
}

// Lemma: If tds_states, status == FindReachableActiveTDsStatesFromActiveTDsState(k'.objects.tds), 
// and status == true, then AllReachableActiveTDsStates(k') == tds_states
lemma Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
    k:State, tds_states:set<TDs_Vals>
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
    requires forall tds_state2 :: tds_state2 in tds_states
                ==> (ActiveTDsState(k) == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k), tds_state2))
    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                        (tds_state2 == ActiveTDsState(k) || 
                            IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k), tds_state2))
                                                    // tds_state -->* tds_state2
                    ==> tds_state2 in tds_states

    ensures AllReachableActiveTDsStates(k) == tds_states
{
    // Dafny can automatically prove this lemma
}

// Lemma: If tds_states, status == FindReachableActiveTDsStatesFromActiveTDsState(k'.objects.tds), 
// and status == true, and if k' fulfills IsValidState_Objects and IsValidState_SubjsOwnObjsThenInSamePartition, then 
// IsValidState_ReachableTDsStates(k')
lemma Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, tds_states:set<TDs_Vals>, status:bool
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

    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k'.subjects.drvs) && (Dev_ID(dev_sid) in k'.subjects.devs)
                 ==> (drv_sid != dev_sid)
    requires IsValidState_Objects(k')
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k')
    requires k'_params == KToKParams(k')

    requires status == true
    requires AllReachableActiveTDsStates(k') == tds_states

    ensures IsValidState_ReachableTDsStates(k')
    ensures IsSecureState_SI1(k')
    ensures StatePropertiesCorollary1(k')
{
    var k'_reachable_active_tds_states := AllReachableActiveTDsStates(k');

    Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateOfReachableTDsStates(k', k'_params, tds_states, k'_reachable_active_tds_states, status);
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More(k');

    Lemma_IfFulfillCondition55AndIsValidState_SubjsOwnObjsThenInSamePartition_ThenFulfillCorollary1(k', k'_params, k'_reachable_active_tds_states);
}

lemma Lemma_AllActiveDevs_ReturnCorrectResult(k:State)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))

    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID_SlimState(KToKParams(k).subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(KToKParams(k).subjects, dev_id2) != NULL
{
    assert forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id;
    assert forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id;
    assert forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id;

    assert KToKParams(k).subjects == k.subjects;

    forall dev_id2 | dev_id2 in AllActiveDevs(k)
        ensures IsDevID_SlimState(KToKParams(k).subjects, dev_id2)
        ensures SubjPID_DevID_SlimState(KToKParams(k).subjects, dev_id2) != NULL
    {
        assert IsDevID_SlimState(k.subjects, dev_id2);
    }
}

lemma Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    ensures K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))
{
    // Dafny can automatically prove this lemma
}

// (needs 60s to verify)
lemma Lemma_AllReachableActiveTDsStates_ActiveTDsStateIsSecure_Property(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
     
    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2))

    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))

    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2))
{
    forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
        ensures (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))
        ensures (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2))
    {
        forall td_id2, dev_id | dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                            // The TD is read by the device
            ensures !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2)
            ensures !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2)
        {
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2);
        }
    }
}

lemma Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k:State)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    ensures P_ObjsInSubjsAreAlsoInState(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_AllReachableActiveTDsStates_PreConditions(k:State)
    requires IsValidState(k)

    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)
{
    // Dafny can automatically prove this lemma
}




//******** Lemmas for Specific Operations  ********//
// Lemma: In DevWrite, KToKParams(k) == KToKParams(k')
lemma Lemma_DrvDevWrite_NewKParams_SameWithKParams(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    
    requires k'_subjects == k.subjects
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)
    requires forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].pid == k.objects.tds[td_id].pid
    requires forall fd_id :: fd_id in k.objects.fds
                ==> k'_objects.fds[fd_id].pid == k.objects.fds[fd_id].pid
    requires forall do_id :: do_id in k.objects.dos
                ==> k'_objects.dos[do_id].pid == k.objects.dos[do_id].pid
        // Requirement: Unchanged IDs and PIDs between k and k'
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids
        // Requirement: The IDs of TDs owned by a device is not changed
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val)

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))
 
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    ensures KToKParams(k) == k'_params
{
    assert MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos);

    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids;
        // Requirement: The IDs of TDs owned by a device is not changed
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val);

    var k_params := KToKParams(k);

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'_subjects, k'_objects);
    assert k'_params.hcoded_td_ids == k_params.hcoded_td_ids;
    assert k'_params.hcoded_tds == k_params.hcoded_tds;

    assert k'_params.objs_pids == k_params.objs_pids;

    assert k'_params.all_active_tds == k_params.all_active_tds;
}

lemma Lemma_DevWrite_ReachableActiveTDsStatesFromNewKActiveTDsStatesMustBeSecure(
    k:State, k_params:ReachableTDsKParams, k'_active_tds_state:TDs_Vals
)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires k_params == KToKParams(k)

    requires TDsStateGetTDIDs(k'_active_tds_state) == k_params.all_active_tds

    requires (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
    requires forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
                                                // k'_active_tds_state -->* tds_state2
                ==> IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2)
                                                // ActiveTDsState(k) -->1+ tds_state2
        // Requirement: If k'_active_tds_state -->* tds_state2, then 
        // ActiveTDsState(k) -->1+ tds_state2

    ensures forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
{
    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
        ensures (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))
    {
        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2);
        assert tds_state2 in AllReachableActiveTDsStates(k);
    }
}

// (needs 180s to verify)
lemma Lemma_DevWrite_WrittenTDsFDsDOsExistInSystem(
    k:State, dev_id:Dev_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Requirement: Subjects have different internal IDs
    requires IsValidState_Objects(k)
    
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires forall td_id2 :: td_id2 in td_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each TD writes in <td_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                    W in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes && 
                        // The TD references the target FD (<fd_id2>) with W
                    fd_id_val_map[fd_id2] in GetTDVal(k, td_id).trans_params_fds[fd_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each FD writes in <fd_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)
    requires forall do_id2 :: do_id2 in do_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD in the system 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                    W in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes &&
                        // The TD references the target DO (<do_id2>) with W 
                    do_id_val_map[do_id2] in GetTDVal(k, td_id).trans_params_dos[do_id2].vals) 
                        // The TD specifies the new value to be written
        // Requirement: For each DO writes in <do_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)
    requires forall td_id2, dev_id2 :: 
            dev_id2 in AllActiveDevs(k) && 
                // The device (<dev_id2>) is active
            td_id2 in AllActiveTDs(k) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id2, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), ActiveTDsState(k), td_id2)
        // Requirement: In the current TDs' state of k, any active TDs read by any
        // active devices have no invalid references to I/O objects
    requires StatePropertiesCorollary2(k)

    ensures forall td_id :: td_id in td_id_val_map 
            ==> td_id in k.objects.tds &&
                td_id !in KToKParams(k).hcoded_td_ids &&
                ObjPID(k, td_id.oid) == SubjPID_DevID(k, dev_id)
    ensures forall fd_id :: fd_id in fd_id_val_map 
            ==> fd_id in k.objects.fds &&
                ObjPID(k, fd_id.oid) == SubjPID_DevID(k, dev_id)
    ensures forall do_id :: do_id in do_id_val_map 
            ==> do_id in k.objects.dos &&
                ObjPID(k, do_id.oid) == SubjPID_DevID(k, dev_id)
    ensures forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
            ==> {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, o_id)
{
    var k_params := KToKParams(k);

    forall td_id2 | td_id2 in td_id_val_map
        ensures td_id2 in k.objects.tds && ObjPID(k, td_id2.oid) == SubjPID_DevID(k, dev_id)
        ensures td_id2 !in k_params.hcoded_td_ids
        ensures {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, td_id2.oid)
    {
        assert exists td_id :: td_id in k.objects.tds &&
                ObjPID(k, td_id.oid) != NULL &&
                    // Exists an active TD in the system 
                CanActiveDevReadActiveTD(k_params, ActiveTDsState(k), dev_id, td_id) &&
                    // The device can read the active TD
                td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                    // The TD references the target TD (<td_id2>) with W
                td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals;
        assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, ActiveTDsState(k), dev_id, td_id2.oid);
        assert {W} <= DevAModesToObjFromTDs_SlimState(k_params, ActiveTDsState(k), dev_id, td_id2.oid);
        assert {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, td_id2.oid);

        assert td_id2.oid in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, td_id2.oid);
    }

    forall fd_id2 | fd_id2 in fd_id_val_map
        ensures fd_id2 in k.objects.fds && ObjPID(k, fd_id2.oid) == SubjPID_DevID(k, dev_id)
        ensures {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, fd_id2.oid)
    {
        assert exists td_id :: td_id in k.objects.tds &&
                ObjPID(k, td_id.oid) != NULL &&
                    // Exists an active TD in the system 
                CanActiveDevReadActiveTD(k_params, ActiveTDsState(k), dev_id, td_id) &&
                    // The device can read the active TD
                fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                W in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes && 
                    // The TD references the target FD (<fd_id2>) with W
                fd_id_val_map[fd_id2] in GetTDVal(k, td_id).trans_params_fds[fd_id2].vals;
        assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, ActiveTDsState(k), dev_id, fd_id2.oid);
        assert {W} <= DevAModesToObjFromTDs_SlimState(k_params, ActiveTDsState(k), dev_id, fd_id2.oid);
        assert {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, fd_id2.oid);

        assert fd_id2.oid in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, fd_id2.oid);
    }

    forall do_id2 | do_id2 in do_id_val_map
        ensures do_id2 in k.objects.dos && ObjPID(k, do_id2.oid) == SubjPID_DevID(k, dev_id)
        ensures {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, do_id2.oid)
    {
        assert exists td_id :: td_id in k.objects.tds &&
                ObjPID(k, td_id.oid) != NULL &&
                    // Exists an active TD in the system 
                CanActiveDevReadActiveTD(k_params, ActiveTDsState(k), dev_id, td_id) &&
                    // The device can read the active TD
                do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                W in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes &&
                    // The TD references the target DO (<do_id2>) with W 
                do_id_val_map[do_id2] in GetTDVal(k, td_id).trans_params_dos[do_id2].vals;
        assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, ActiveTDsState(k), dev_id, do_id2.oid);
        assert {W} <= DevAModesToObjFromTDs_SlimState(k_params, ActiveTDsState(k), dev_id, do_id2.oid);
        assert {W} <= DevAModesToObj(k, ActiveTDsState(k), dev_id, do_id2.oid);

        assert do_id2.oid in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, do_id2.oid);
    }
}

lemma Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed(
    k:State, dev_sid:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires IDToDev(k, Dev_ID(dev_sid)).pid != NULL
        // Requirement: The driver is in the I/O system and is active
    requires forall td_id2 :: td_id2 in td_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each TD writes in <td_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<Dev_ID(dev_sid)>)
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    fd_id2 in GetTDVal(k, td_id).trans_params_fds &&
                    W in GetTDVal(k, td_id).trans_params_fds[fd_id2].amodes && 
                        // The TD references the target FD (<fd_id2>) with W
                    fd_id_val_map[fd_id2] in GetTDVal(k, td_id).trans_params_fds[fd_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each FD writes in <fd_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<Dev_ID(dev_sid)>)
    requires forall do_id2 :: do_id2 in do_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    do_id2 in GetTDVal(k, td_id).trans_params_dos &&
                    W in GetTDVal(k, td_id).trans_params_dos[do_id2].amodes &&
                        // The TD references the target DO (<do_id2>) with W 
                    do_id_val_map[do_id2] in GetTDVal(k, td_id).trans_params_dos[do_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each DO writes in <do_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<Dev_ID(dev_sid)>)

    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)
        // Property 1: Written TDs, FDs and DOs are in the I/O system
    ensures forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) == SubjPID(k, dev_sid)
        // Property 2: All written objects are in the same partition with the device
    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Property 3: device does not write any hardcoded TDs
{
    var obj_id_list := TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map));
    Lemma_ActiveDevsHaveHcodedPtrsToOwnedObjs(k);
    
    // Prove StatePropertiesCorollary2(k)
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    assert StatePropertiesCorollary2(k);

    Lemma_CurrentActiveTDsStateOnlyHasValidRefs(k, AllReachableActiveTDsStates(k));
    Lemma_DevWrite_WrittenTDsFDsDOsExistInSystem(
        k, Dev_ID(dev_sid), td_id_val_map, fd_id_val_map, do_id_val_map);
    assert forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds;
    assert forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds;
    assert forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos;

    Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed_Property2(
        k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    assert forall dev_id :: dev_id in k.subjects.devs
            ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map;
}

lemma Lemma_DevWrite_HCodedTDsAreUnmodified(
    k:State, td_id_val_map:map<TD_ID, TD_Val>, k'_objects_tds:map<TD_ID, TD_State>
)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map

    requires forall td_id :: td_id in k.objects.tds <==> td_id in k'_objects_tds
    requires MapGetKeys(k'_objects_tds) == MapGetKeys(k.objects.tds)
    requires forall td_id :: td_id in k.objects.tds
                ==> (td_id in td_id_val_map ==> k'_objects_tds[td_id].val == td_id_val_map[td_id]) &&
                    (td_id !in td_id_val_map ==> k'_objects_tds[td_id] == k.objects.tds[td_id])
    requires forall td_id :: td_id in k.objects.tds
                ==> k.objects.tds[td_id].pid == k'_objects_tds[td_id].pid
        // Properties of WriteTDsVals(k.objects.tds, td_id_val_map)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
         
    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_objects_tds[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val)
{
    forall dev_id | dev_id in k.subjects.devs
        ensures k'_objects_tds[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val
    {
        assert k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map;

        assert k'_objects_tds[k.subjects.devs[dev_id].hcoded_td_id] == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id];
    }
}

lemma Lemma_DrvDevWrite_WrittenTDsMustBeActiveInK(k:State, td_id_val_map:map<TD_ID, TD_Val>)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires forall o_id :: o_id in TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map))
                        // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) != NULL
    requires forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds

    ensures forall td_id:: td_id in td_id_val_map ==> td_id in ActiveTDsState(k)
{
    forall td_id | td_id in td_id_val_map
        ensures td_id in ActiveTDsState(k)
    {
        assert td_id.oid in AllObjsIDs(k.objects);
        assert ObjPID(k, td_id.oid) != NULL;
    }
}

// (needs 50s to verify)
lemma Lemma_UnmodifiedSubjObjPIDs_NewKFulfillIsValidState_SubjsOwnObjsThenInSamePartition(k:State, k':State)
    requires IsValidState(k) && IsSecureState(k)

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos)
    requires forall drv_id :: drv_id in k'.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'.objects.tds[k'.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val)

    requires forall s_id :: s_id in AllSubjsIDs(k.subjects)
                ==> SubjPID(k, s_id) == SubjPID(k', s_id)
    requires forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> ObjPID(k, o_id) == ObjPID(k', o_id)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> o_id in AllObjsIDs(k'.objects) &&
                    SubjPID(k', s_id) == ObjPID(k', o_id)
{
    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);
}

lemma Lemma_DrvWrite_ProveProperty3(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val> // IDs of DOs, and values to be written
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)

    requires forall fd_id :: fd_id in fd_id_val_map ==>    
            SubjPID(k, drv_sid) == ObjPID(k, fd_id.oid)
    requires forall do_id :: do_id in do_id_val_map ==>        
            SubjPID(k, drv_sid) == ObjPID(k, do_id.oid)
    requires forall td_id :: td_id in td_id_val_map ==>        
            SubjPID(k, drv_sid) == ObjPID(k, td_id.oid)

    ensures (forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                        FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                        DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) == SubjPID(k, drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ExternalObjActivateDeactivate_NoSubjsOwnsExternalObjs_EquivilantRepresentation(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in td_ids || FD_ID(o_id) in fd_ids || DO_ID(o_id) in do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas  ********//
lemma Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed_Property2(
    k:State, dev_sid:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>,
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires IDToDev(k, Dev_ID(dev_sid)).pid != NULL
        // Requirement: The driver is in the I/O system and is active

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)
        // Requirement: Written TDs, FDs and DOs are in the I/O system
    requires forall td_id :: td_id in td_id_val_map 
            ==> td_id in k.objects.tds &&
                ObjPID(k, td_id.oid) == SubjPID_DevID(k, Dev_ID(dev_sid))
    requires forall fd_id :: fd_id in fd_id_val_map 
            ==> fd_id in k.objects.fds &&
                ObjPID(k, fd_id.oid) == SubjPID_DevID(k, Dev_ID(dev_sid))
    requires forall do_id :: do_id in do_id_val_map 
            ==> do_id in k.objects.dos &&
                ObjPID(k, do_id.oid) == SubjPID_DevID(k, Dev_ID(dev_sid))

    ensures forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                    FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                    DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
            ==> o_id in AllObjsIDs(k.objects) &&
                ObjPID(k, o_id) == SubjPID(k, dev_sid)
        // Property: All written objects are in the same partition with the device 
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevWrite_CurrentTDsStateReachNewTDsStateInOneStep(
    k:State, dev_id:Dev_ID, td_id_val_map:map<TD_ID, TD_Val>, new_tds_state:TDs_Vals
)
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
    
    requires TDsStateGetTDIDs(new_tds_state) == AllActiveTDs(k) 
        // Requirement: <new_tds_state> must includes all active TDs

    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires TDsStateGetTDIDs(ActiveTDsState(k)) == AllActiveTDs(k) 
    requires forall td_id2 :: td_id2 in TDsStateDiff(new_tds_state, ActiveTDsState(k))
                ==>  td_id2 in td_id_val_map &&
                     TDsStateDiff(new_tds_state, ActiveTDsState(k))[td_id2] == td_id_val_map[td_id2]
        // Requirement: The differences of active TDs' states (new_tds_state,  
        // ActiveTDsState(k)) must be included in td_id_val_map
    requires forall td_id2 :: td_id2 in td_id_val_map ==> td_id2 in k.objects.tds
    requires forall td_id2 :: td_id2 in td_id_val_map
            ==> (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), ActiveTDsState(k), dev_id, td_id) &&
                        // The device can read the active TD
                    td_id2 in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[td_id2].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    td_id_val_map[td_id2] in GetTDVal(k, td_id).trans_params_tds[td_id2].vals)
                        // The TD specifies the new value to be written
        // Requirement: For each TD writes in <td_id_val_map>, it must be from
        // an active TD (<td_id>) that can be read by the active device 
        // (<dev_id>)

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(KToKParams(k), dev_id, ActiveTDsState(k), new_tds_state)
        // Property: ActiveTDsState(k) can reach <new_tds_state> in one TDs write 
        // operation
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_DevWrite_NewReachableActiveTDsStatesIsSubsetOfTheOneInK(
    k:State, k_params:ReachableTDsKParams, dev_id:Dev_ID, k':State, k'_active_tds_state:TDs_Vals
)
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

    requires k_params == KToKParams(k)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params);
    requires forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
        // Requirements: Proved propertis of k_params

    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The device must be active

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos)

    requires k'.subjects == k.subjects
    requires AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)
    requires AllObjsIDs(k'.objects) == AllObjsIDs(k.objects)

    requires TDsStateGetTDIDs(k'_active_tds_state) == AllActiveTDs(k')
        // Requirement: <k'_active_tds_state> includes all active TDs in k' 

    requires forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2)

    requires IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, 
                dev_id, ActiveTDsState(k), k'_active_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, 
                dev_id, ActiveTDsState(k), k'_active_tds_state)

    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2)
    ensures forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            AllActiveDevs(k), ActiveTDsState(k), tds_state2)
        // Properties needed by the property below
    ensures AllActiveTDs(k') == AllActiveTDs(k)
    ensures forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k') &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), k'_active_tds_state, tds_state2))
                                                // k'_active_tds_state -->* tds_state2
                ==> IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2)
                                                // ActiveTDsState(k) -->1+ tds_state2
{
    assert AllActiveTDs(k') == AllActiveTDs(k);
    Lemma_TDsStateAReachTDsStateBInOneStep_ThenTDsStatesReachedByBInChainAlsoReachedByAInChain(k_params, 
        dev_id, AllActiveDevs(k), ActiveTDsState(k), k'_active_tds_state);
}

lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires IsValidState_ReachableTDsStates(k)
    requires IsSecureState_SI1(k)

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
{
    // Dafny can automatically prove this lemma
}

// (needs ~100s to verify)
lemma Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More(k:State)
    requires (forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                            dev_id in AllActiveDevs(k) &&
                            td_id2 in TDsStateGetTDIDs(tds_state2)
                        ==> CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)))
        // Property needed by the properties below
    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
             <==>
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))) &&
                        // The TD contains valid references only 
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))

    ensures (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs(k) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(tds_state2) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state2, td_id2)))
            <==> 
            (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2))
{
    // Dafny can automatically prove this lemma
}

// (need 100s to verify)
lemma Lemma_ActiveTDsUnchanged_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
    k:State, k_params:ReachableTDsKParams, from_tds_state:TDs_Vals, found_tds_states:set<TDs_Vals>, status:bool
)
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

    requires k_params == KToKParams(k)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params);
    requires forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
        // Requirements: Proved propertis of k_params

    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k)
    requires forall tds_state2 :: tds_state2 in found_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
        // Requirement: The TDs' state in k includes all active TDs. In other 
        // words, active TDs are unchanged
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID(k, dev_id2) &&
                    SubjPID_DevID(k, dev_id2) != NULL
        // Requirement: The devices in AllActiveDevs(k) must be active

    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            AllActiveDevs(k), from_tds_state, tds_state2)
    requires forall td_id2, dev_id, tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    dev_id in AllActiveDevs(k) && 
                    td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2)

    requires forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (from_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            AllActiveDevs(k), from_tds_state, tds_state2))
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs(k) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2))

    requires forall tds_state2 :: tds_state2 in found_tds_states
                ==> (from_tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                                        AllActiveDevs(k), from_tds_state, tds_state2))
        // Requirement: from_tds_state -->* found_tds_states

    requires status <==> AllReachableActiveTDsStatesAreSecure(k_params, AllActiveDevs(k), found_tds_states)
        // Requirement: Any active TDs read by any active devices have no invalid
        // references to I/O objects in each of <found_tds_states> 

    ensures status == true
{
    // Dafny can automatically prove this lemma.
}