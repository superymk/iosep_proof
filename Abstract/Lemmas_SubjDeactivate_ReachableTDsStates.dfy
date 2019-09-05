include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"

predicate SubjObjDeactivate_CommonPreConditionsOfKAndNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
{
    (SubjObjDeactivate_PreConditionsOfK(k)) &&
    (SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')) &&
    (SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)) &&
    (SubjObjDeactivate_SubjsObjsPIDsInNewK(k')) &&
    (SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)) &&
    (CanActiveDevReadActiveTD_KParams_PreConditions(k_params)) &&
    (SubjObjDeactivate_PreConditionsOfK(k')) &&
    (SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)) &&
    (SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToFDsAndDOsBeingDeactivated(
                k, k', todeactivate_fd_ids, todeactivate_do_ids)) &&

    (forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)) &&
        // Requirement: All objects active in k' have the same PID as in k
    (forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)) &&

    (true)
}

// (Needs 50s to verify)
lemma Lemma_SubjObjDeactivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    found_tds_states:set<TDs_Vals>, status:bool
)
    requires SubjObjDeactivate_CommonPreConditionsOfKAndNewK(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall tds_state2 :: tds_state2 in found_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
    requires forall tds_state2 :: tds_state2 in found_tds_states
                ==> (ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
        // Requirement: ActiveTDsState(k') -->* found_tds_states

    requires (status == true)
                <==> AllReachableActiveTDsStatesAreSecure(k'_params, AllActiveDevs(k'), found_tds_states)
        // Requirement: Any active TDs read by any active devices have no invalid
        // references to I/O objects in each of <found_tds_states> 
        
    ensures status == true
{
    var add_tds := TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids));

    forall tds_state2 | tds_state2 in found_tds_states
        ensures ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
    {
        assert ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                    AllActiveDevs(k'), ActiveTDsState(k'), tds_state2);

        if(ActiveTDsState(k') == tds_state2)
        {
            var k_active_tds_state := MapConcat<TD_ID, TD_Val>(ActiveTDsState(k'), add_tds);

            assert k_active_tds_state == ActiveTDsState(k);

            // Prove the properties of k_active_tds_state (ActiveTDsState(k))
            assert k_active_tds_state in AllReachableActiveTDsStates(k);

            // Prove TDs in ActiveTDsState(k') has no invalid refs
            Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIfValidBefore(k, k_params, k', k'_params,
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_active_tds_state, ActiveTDsState(k'));
        }
        else
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                        AllActiveDevs(k'), ActiveTDsState(k'), tds_state2);
            Lemma_IsActiveTDsStateReachActiveTDsStateInChain_PostConditions(k'_params, 
                        AllActiveDevs(k'), ActiveTDsState(k'), tds_state2);
            var k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID> :| 
                    |k'_tds_states| >= 2 && 
                    (forall tds_state2 :: tds_state2 in k'_tds_states 
                        ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
                    |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
                    k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
                    k'_tds_states[|k'_tds_states|-1] == tds_state2 &&
                    (forall i :: 0<=i<|k'_tds_states| - 1 
                        ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                                k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                            IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                                k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]));

            Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs(k, k_params, k', k'_params,
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                k'_tds_states, k'_devs, add_tds);
        }
    }
}




//******** Utility Functions  ********//
// Function: Forall tds_state, o_id, dev_id in reachable_active_tds_states, 
// active devices (dev_ids) and object ids (o_ids), 
// DevAModesToObj(k, tds_state, dev_id, o_id) == {}
function NoActiveDevHasTransferToObjsInReachableActiveTDsStates(
    k:State, reachable_active_tds_states:set<TDs_Vals>, dev_ids:set<Dev_ID>, o_ids:set<Object_ID>
) : bool
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id 
        // Requirements: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are TDs
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    // Requirements required by functions in this function method
    requires forall dev_id :: dev_id in dev_ids
                ==> IsDevID(k, dev_id) &&
                    SubjPID(k, dev_id.sid) != NULL
    // Requirement: The devices are active
    requires reachable_active_tds_states != {}

    requires forall tds_state :: tds_state in reachable_active_tds_states
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
{
    forall tds_state, o_id, dev_id :: 
                tds_state in reachable_active_tds_states &&
                        // Forall active TDs' state in reachable_active_tds_states
                o_id in o_ids &&
                dev_id in dev_ids
            ==> DevAModesToObj(k, tds_state, dev_id, o_id) == {}
                        // No active device has transfer to the object in the TDs' state
}

predicate SubjObjDeactivate_PreConditionsOfK(k:State)
{
    K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos)) &&

    P_ObjsInSubjsAreAlsoInState(k) &&

    (forall dev_id :: dev_id in k.subjects.devs
        ==> (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_tds) <= 
                IDToDev(k, dev_id).td_ids) &&
            (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_fds) <= 
                IDToDev(k, dev_id).fd_ids) &&
            (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_dos) <= 
                IDToDev(k, dev_id).do_ids)) &&

    (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
                ==> SubjPID(k, s_id) == ObjPID(k, o_id)) &&
        // Requirement: k fulfills IsValidState_SubjsOwnObjsThenInSamePartition

    IsValidState_TDsToAllStates(k)
}

predicate SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k:State, k'_subjects:Subjects, k'_objects:Objects)
{
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&
    (MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)) &&
    (MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)) &&
    (MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)) &&
    (forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)) &&

    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)) &&
    
    (true)
}

predicate SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k:State, k':State)
{
    (MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)) &&
    (MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)) &&
    (MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds)) &&
    (MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos)) &&
    (forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)) &&

    (AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)) &&
    (AllObjsIDs(k'.objects) == AllObjsIDs(k.objects)) &&

    (k'.tds_to_all_states == k.tds_to_all_states) &&
    (true)
}

predicate SubjObjDeactivate_SubjsObjsPIDsInNewK(k':State)
    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
{
    (forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> SubjPID(k', s_id) == ObjPID(k', o_id)) &&
        // Requirement: k' must fulfill IsValidState_SubjsOwnObjsThenInSamePartition

    (true)
}

predicate SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_ObjsInSubjsAreAlsoInState(k)
{
    (todeactivate_s_ids <= AllSubjsIDs(k.subjects)) &&
    (todeactivate_s_ids <= AllActiveSubjs(k)) &&

    (forall s_id :: s_id in todeactivate_s_ids 
                ==> (OwnedTDs(k, s_id) <= todeactivate_td_ids)) &&
        // Requirement: Subjects to be deactivated have their TDs in <todeactivate_td_ids>
    (todeactivate_td_ids <= MapGetKeys(k.objects.tds)) &&
        // Requirement: TDs in <todeactivate_td_ids> exist in the system
    (todeactivate_td_ids <= AllActiveTDs(k)) &&
    (AllActiveTDs(k') == AllActiveTDs(k) - todeactivate_td_ids) &&
    (AllActiveTDs(k') * todeactivate_td_ids == {}) &&
    (forall td_id :: td_id in k.objects.tds && td_id !in todeactivate_td_ids
                ==> ObjPID(k', td_id.oid) == ObjPID(k, td_id.oid)) &&
        // Requirement: All TDs except the TDs to be deactivated preserve their 
        // partition IDs between k and k'
    (forall dev_id2:Dev_ID :: IsDevID(k, dev_id2) && 
                    dev_id2.sid !in todeactivate_s_ids
                ==> k'.subjects.devs[dev_id2] == k.subjects.devs[dev_id2]) &&
    (forall drv_id2:Drv_ID :: IsDrvID(k, drv_id2) &&
                    drv_id2.sid !in todeactivate_s_ids
                ==> k'.subjects.drvs[drv_id2] == k.subjects.drvs[drv_id2]) &&
        // Requirement: Forall devices and drivers not being deactivated in the 
        // operation, their states are unchanged
    (forall s_id :: s_id in todeactivate_s_ids
                ==> SubjPID(k, s_id) != NULL && SubjPID(k', s_id) == NULL) &&
        // Requirement: If a subject is in <todeactivate_s_ids>, then the subject
        // is deactivating
    (forall td_id :: td_id in todeactivate_td_ids
                ==> ObjPID(k, td_id.oid) != NULL && ObjPID(k', td_id.oid) == NULL) &&
        // Requirement: If a TD is in <todeactivate_td_ids>, then the TD
        // is being deactivated
    (AllActiveDevs(k') <= AllActiveDevs(k))&&
    (forall td_id2 :: td_id2 in AllActiveTDs(k)
                ==> ObjPID(k, td_id2.oid) != NULL) &&

    (forall td_id :: td_id in k.objects.tds
                ==> k'.objects.tds[td_id].val == k.objects.tds[td_id].val) &&
    (forall fd_id :: fd_id in k.objects.fds
                ==> k'.objects.fds[fd_id].val == k.objects.fds[fd_id].val) &&
    (forall do_id :: do_id in k.objects.dos
                ==> k'.objects.dos[do_id].val == k.objects.dos[do_id].val) &&
        // Requirement: All objects preserve their values in 
        // Drv/Dev/ExternalObj deactivation
    
    (true)
}

predicate SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k:State)
    requires SubjObjDeactivate_PreConditionsOfK(k)
{
    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (ActiveTDsState(k) == tds_state2 ||
                    IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2))
                                                // ActiveTDsState(k) -->* tds_state2
                ==> tds_state2 in AllReachableActiveTDsStates(k)) &&
        // Requirement: k fulfills Condition 5.3 of <IsValidState_ReachableTDsStates>
    (ActiveTDsState(k) in AllReachableActiveTDsStates(k)) &&
        // Requirement: k fulfills Condition 5.6 of <IsValidState_ReachableTDsStates>
    (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
        ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)) &&
        // Requirement: k fulfills Condition 5.5 of <IsValidState_ReachableTDsStates>

    (true)
}

predicate SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(
    k:State, k':State, todeactivate_td_ids:set<TD_ID>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)

    requires AllActiveDevs(k') <= AllActiveDevs(k)
{
    (forall tds_state2, td_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to TDs 
        // being deactivated

    (true)
}

predicate SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToFDsAndDOsBeingDeactivated(
    k:State, k':State, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)

    requires AllActiveDevs(k') <= AllActiveDevs(k)
{
    (todeactivate_fd_ids <= MapGetKeys(k.objects.fds)) &&
    (forall fd_id :: fd_id in todeactivate_fd_ids
                ==> ObjPID(k, fd_id.oid) != NULL && ObjPID(k', fd_id.oid) == NULL) &&
    (forall fd_id :: fd_id in k.objects.fds && fd_id !in todeactivate_fd_ids
                ==> ObjPID(k', fd_id.oid) == ObjPID(k, fd_id.oid)) &&

    (todeactivate_do_ids <= MapGetKeys(k.objects.dos)) &&
    (forall do_id :: do_id in todeactivate_do_ids
                ==> ObjPID(k, do_id.oid) != NULL && ObjPID(k', do_id.oid) == NULL) &&
    (forall do_id :: do_id in k.objects.dos && do_id !in todeactivate_do_ids
                ==> ObjPID(k', do_id.oid) == ObjPID(k, do_id.oid)) &&

    (forall tds_state2, fd_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to FDs 
        // being deactivated

    (forall tds_state2, do_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to DOs 
        // being deactivated

    (true)
}

predicate P_SubjObjDeactivate_IfTDsInReachableTDsStatesInNewKIsSecure_ThenTDsInReachableTDsStatesInKIsSecure(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    k'_tds_states:seq<TDs_Vals>, add_tds:map<TD_ID, TD_Val>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
    requires forall tds_state2 :: tds_state2 in k'_tds_states
                ==> (forall k1, k2 :: k1 in tds_state2 && k2 in add_tds ==> k1 != k2)
{
    forall k'_tds_state, k_tds_state :: k'_tds_state in k'_tds_states &&
                    k_tds_state == MapConcat<TD_ID, TD_Val>(k'_tds_state, add_tds)
                ==> k_params.all_active_tds == TDsStateGetTDIDs(k_tds_state) &&
                    (ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_tds_state)
                        ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state))
}

// (needs 130s to verify)
lemma Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>,
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL && 
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in both k and k'
    requires |k'_tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))
    
    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Properties needed by the properties below
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
        // Property: ActiveTDsState(k) -->* k_last_to_tds_state (
        // k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1])
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')

    ensures P_SubjObjDeactivate_IfTDsInReachableTDsStatesInNewKIsSecure_ThenTDsInReachableTDsStatesInKIsSecure(
                k, k_params, k', k'_params, k'_tds_states, add_tds)
        // Property 6

    decreases |k'_tds_states| 
{
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    assert forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k');
    assert forall k1, k2 :: k1 in AllActiveTDs(k') && k2 in add_tds ==> k1 != k2;
    assert forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2);

    if(|k'_tds_states| == 2)
    {
        Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Base_ActiveTDsStatesInKCanReach(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_tds_states, k'_devs, add_tds);
    }
    else
    {
        var prev_k'_tds_states := k'_tds_states[..|k'_tds_states|-1];
        assert forall i :: 0<=i<|prev_k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                        k'_devs[i], prev_k'_tds_states[i], prev_k'_tds_states[i+1]);
        Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter(k, k_params, k', k'_params,
            todeactivate_s_ids, todeactivate_td_ids, prev_k'_tds_states, k'_devs[..|k'_devs|-1], add_tds);
        
        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(prev_k'_tds_states[|prev_k'_tds_states|-1], add_tds));

        // Prove k'_last_from_tds_state is the last element of k'_tds_states[..|k'_tds_states|-1]
        Lemma_SequenceHighlightLastElemOfSubSeq(k'_tds_states, prev_k'_tds_states);
        assert k'_tds_states[|k'_tds_states|-2] == prev_k'_tds_states[|prev_k'_tds_states|-1];

        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds));

        Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_Private(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_tds_states, k'_devs, add_tds);
    }
}

predicate P_ObjsToBeDeactivatedAreInactiveInNewK_AndNoActiveDevsInNewKHaveTransferToThem(
    k:State, k':State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires AllActiveDevs(k') <= AllActiveDevs(k)
{
    (todeactivate_fd_ids <= MapGetKeys(k.objects.fds)) &&
    (forall fd_id :: fd_id in todeactivate_fd_ids
                ==> ObjPID(k, fd_id.oid) != NULL && ObjPID(k', fd_id.oid) == NULL) &&
    (forall fd_id :: fd_id in k.objects.fds && fd_id !in todeactivate_fd_ids
                ==> ObjPID(k', fd_id.oid) == ObjPID(k, fd_id.oid)) &&
    (todeactivate_do_ids <= MapGetKeys(k.objects.dos)) &&
    (forall do_id :: do_id in todeactivate_do_ids
                ==> ObjPID(k, do_id.oid) != NULL && ObjPID(k', do_id.oid) == NULL) &&
    (forall do_id :: do_id in k.objects.dos && do_id !in todeactivate_do_ids
                ==> ObjPID(k', do_id.oid) == ObjPID(k, do_id.oid)) &&

    (forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, td_id.oid) == {}) &&
    (forall fd_id, dev_id :: fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, fd_id.oid) == {}) &&
    (forall do_id, dev_id :: do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, do_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to TDs/FDs/DOs 
        // being deactivated

    (true)
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIfValidBefore(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>, 
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k_tds_state> contains additional active TDs (if 
        // any) from <k'_tds_state>

    requires P_ObjsToBeDeactivatedAreInactiveInNewK_AndNoActiveDevsInNewKHaveTransferToThem(
                k, k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_tds_state)

    ensures ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), k_tds_state)
                ==> ActiveTDsStateIsSecure(KToKParams(k'), AllActiveDevs(k'), k'_tds_state)
{
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert MapGetKeys<Drv_ID, Drv_State>(k'.subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k.subjects.drvs);
    assert MapGetKeys<Dev_ID, Dev_State>(k'.subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k.subjects.devs);

    if(ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state))
    {
        forall k'_td_id, k'_dev_id |
                    k'_dev_id in AllActiveDevs(k') && 
                        // The device (<k'_dev_id>) is active
                    k'_td_id in TDsStateGetTDIDs(k'_tds_state) &&
                        // The TD (<k'_td_id>) is active
                    CanActiveDevReadActiveTD(k'_params, k'_tds_state, k'_dev_id, k'_td_id)
                        // The TD is read by the device
            ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id)
        {
            Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_ActiveDevsAndTDsInNewKHasSameResultWithTheOneForK(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k_tds_state, k'_tds_state);

            assert CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id);

            // Prove the postcondition of the forall statement
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);

            assert k'_tds_state[k'_td_id] == k_tds_state[k'_td_id];
            Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                k_tds_state, k'_tds_state, k'_dev_id, k'_td_id);
        }
    }
}

// Lemma: Any active TDs' state (active TDs of k') reachable from 
// ActiveTDsState(k') has no invalid refs
// (Need 70s to verify)
lemma Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>, 
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToFDsAndDOsBeingDeactivated(
                k, k', todeactivate_fd_ids, todeactivate_do_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in k'
    requires |k'_tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]
    
    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))
    
    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2 // Properties need to be fulfilled for MapConcat
    ensures forall tds_state2 :: tds_state2 in k'_tds_states
                ==> ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
        // Property: Any active TDs' state (active TDs of k') reachable from 
        // ActiveTDsState(k') and intermediate TDs' states have no invalid refs
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
        // Property: ActiveTDsState(k) -->* k_last_to_tds_state (
        // k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1])

    decreases |k'_tds_states|
{
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    if(|k'_tds_states| == 2)
    {
        var k'_from_tds_state := k'_tds_states[0];
        var k'_to_tds_state :=  k'_tds_states[1];
        var k'_dev := k'_devs[0];
        var k_from_tds_state := MapConcat<TD_ID, TD_Val>(k'_from_tds_state, add_tds);
        var k_to_tds_state := MapConcat<TD_ID, TD_Val>(k'_to_tds_state, add_tds);

        assert k'_from_tds_state == ActiveTDsState(k');
        assert k_from_tds_state == ActiveTDsState(k);

        // Prove TDs in k_from_tds_state has no invalid refs
        assert ActiveTDsState(k) in AllReachableActiveTDsStates(k);

        // Prove TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)
        assert TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state);
        assert TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k'_from_tds_state) + MapGetKeys<TD_ID, TD_Val>(add_tds);
        Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
            k'_from_tds_state, k'_to_tds_state, add_tds, k_from_tds_state, k_to_tds_state);

        // Prove k_from_tds_state --> k_to_tds_state
        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                    k'_dev, k'_from_tds_state, k'_to_tds_state);
        Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_dev,
            k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);
        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k'_dev, k_from_tds_state, k_to_tds_state);

        // Prove k_to_tds_state has no invalid refs
        Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, k'_dev, AllActiveDevs(k), k_from_tds_state, k_to_tds_state);
        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), k_to_tds_state); 
        assert k_to_tds_state in AllReachableActiveTDsStates(k);

        // Prove TDs in k'_from_tds_state has no invalid refs
        assert ActiveTDsState(k) in AllReachableActiveTDsStates(k);
        Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIfValidBefore(k, k_params, k', k'_params, 
            todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_from_tds_state, k'_from_tds_state);

        // Prove TDs in k'_to_tds_state has no invalid refs
        Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIfValidBefore(k, k_params, k', k'_params,
            todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_to_tds_state, k'_to_tds_state);
        assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_to_tds_state);
    }
    else
    {
        var prev_k'_tds_states := k'_tds_states[..|k'_tds_states|-1]; 
        Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs(k, k_params, k', k'_params,
            todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, 
            k'_tds_states[..|k'_tds_states|-1], k'_devs[..|k'_devs|-1], add_tds);

        Lemma_SequenceHighlightLastElemOfSubSeq(k'_tds_states, prev_k'_tds_states);
        assert k'_tds_states[|k'_tds_states|-2] == prev_k'_tds_states[|prev_k'_tds_states|-1];

        Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs_Induction_Private(k, k_params, k', k'_params,
            todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k'_tds_states, k'_devs, add_tds);
    }
}




//******** Private Lemmas ********//
lemma Lemma_SubjObjDeactivate_PropertyOfKToKParams(k:State)
    requires SubjObjDeactivate_PreConditionsOfK(k)

    ensures KToKParams(k).subjects == k.subjects
    ensures KToKParams(k).all_active_tds == AllActiveTDs(k)
{
    // Dafny can automatically prove this lemma
}

// (needs 100s to verify)
lemma Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_ActiveTDsStatesInKCanReach_Private(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, 
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
) returns (k_last_to_tds_state:TDs_Vals)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL && 
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in both k and k'
    requires |k'_tds_states| > 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params, 
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, 
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))

    requires forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-2] && k2 in add_tds ==> k1 != k2
    requires forall k'_tds_state :: k'_tds_state in k'_tds_states[..|k'_tds_states|-1]
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Requirements needed by the requirements below
    requires TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds)) == AllActiveTDs(k)
    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds))
    requires forall k'_tds_state :: k'_tds_state in k'_tds_states[..|k'_tds_states|-1]
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')

    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2
        // Property 1
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Property 2
        // Properties needed by the properties below
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')

    ensures k_last_to_tds_state == MapConcat<TD_ID, TD_Val> (k'_tds_states[|k'_tds_states|-1], add_tds)
    ensures k_last_to_tds_state in AllReachableActiveTDsStates(k)
    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_last_to_tds_state)
{
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k);
    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k');
    assert k_params.subjects == k.subjects;
    assert k'_params.subjects == k'.subjects;
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    var k'_last_from_tds_state := k'_tds_states[|k'_tds_states|-2];
    var k'_last_to_tds_state := k'_tds_states[|k'_tds_states|-1];
    var k'_last_dev := k'_devs[|k'_devs|-1];
    var k_last_from_tds_state := MapConcat<TD_ID, TD_Val>(k'_last_from_tds_state, add_tds);
    k_last_to_tds_state := MapConcat<TD_ID, TD_Val>(k'_last_to_tds_state, add_tds);

    assert TDsStateGetTDIDs(k'_last_to_tds_state) == AllActiveTDs(k');
    assert AllActiveTDs(k') * MapGetKeys(add_tds) == {};
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(TDsStateGetTDIDs(k'_last_to_tds_state), MapGetKeys(add_tds));

    // Prove k'_last_from_tds_state is the last element of k'_tds_states[..|k'_tds_states|-1]
    var prev_k'_tds_states := k'_tds_states[..|k'_tds_states|-1];
    Lemma_SequenceHighlightLastElemOfSubSeq(k'_tds_states, prev_k'_tds_states);
    assert k'_last_from_tds_state == prev_k'_tds_states[|prev_k'_tds_states|-1];

    // Prove TDsStateDiff(k'_last_to_tds_state, k'_last_from_tds_state) == TDsStateDiff(k_last_to_tds_state, k_last_from_tds_state)
    Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_PropertyOfAddTDs(
        k, k', todeactivate_td_ids, k'_tds_states, add_tds, 
        k'_last_from_tds_state, k_last_from_tds_state, k'_last_to_tds_state, k_last_to_tds_state);
    Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
        k'_last_from_tds_state, k'_last_to_tds_state, add_tds, k_last_from_tds_state, k_last_to_tds_state);

    // Properties due to ActiveTDsState(k) -->* k_last_from_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), k_last_from_tds_state);
    assert k_last_from_tds_state in AllReachableActiveTDsStates(k);
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_last_from_tds_state);

    // Prove k_last_from_tds_state --> k_last_to_tds_state
    Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_last_dev,
        k_last_from_tds_state, k_last_to_tds_state, k'_last_from_tds_state, k'_last_to_tds_state);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                k'_last_dev, k_last_from_tds_state, k_last_to_tds_state);

    // Prove ActiveTDsState(k) -->1+ k_last_to_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), k_last_from_tds_state);
    Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(k_params,
        k'_last_dev, AllActiveDevs(k), ActiveTDsState(k), k_last_from_tds_state, k_last_to_tds_state); 
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), k_last_to_tds_state);

    // Easy to prove TDs in k_last_to_tds_state has no invalid refs
    assert TDsStateGetTDIDs(k_last_to_tds_state) == AllActiveTDs(k);
    assert k_last_to_tds_state in AllReachableActiveTDsStates(k);
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_last_to_tds_state);

    // Summary for property 2
    forall k'_tds_state | k'_tds_state in k'_tds_states
        ensures (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
    {
        if(k'_tds_state in k'_tds_states[..|k'_tds_states|-1])
        {
            assert forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2;
        }
        else
        {
            assert k'_tds_state == k'_last_to_tds_state;
            assert forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2; 
        }
    }
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_PropertyOfAddTDs(
    k:State, k':State, todeactivate_td_ids:set<TD_ID>,
    k'_tds_states:seq<TDs_Vals>, add_tds:map<TD_ID, TD_Val>,
    k'_last_from_tds_state:TDs_Vals, k_last_from_tds_state:TDs_Vals, k'_last_to_tds_state:TDs_Vals, k_last_to_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires |k'_tds_states| >= 2
    requires forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)

    requires todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids)) 
    requires AllActiveTDs(k') * todeactivate_td_ids == {}
    
    requires forall k1, k2 :: k1 in AllActiveTDs(k') && k2 in add_tds ==> k1 != k2
    requires TDsStateGetTDIDs(k'_last_from_tds_state) == AllActiveTDs(k')
    requires TDsStateGetTDIDs(k'_last_to_tds_state) == AllActiveTDs(k')

    requires k'_last_from_tds_state == k'_tds_states[|k'_tds_states|-2]
    requires k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1]
    requires k_last_from_tds_state == MapConcat<TD_ID, TD_Val> (k'_last_from_tds_state, add_tds)
    requires k_last_to_tds_state == MapConcat<TD_ID, TD_Val> (k'_last_to_tds_state, add_tds)

    ensures MapGetKeys<TD_ID, TD_Val>(add_tds) * TDsStateGetTDIDs(k'_last_from_tds_state) == {}
    ensures add_tds ==  MapSubmap(k_last_from_tds_state, MapGetKeys(add_tds))
    ensures k'_last_from_tds_state == MapRemoveKeys<TD_ID, TD_Val>(k_last_from_tds_state, MapGetKeys(add_tds))
    ensures k'_last_to_tds_state == MapRemoveKeys<TD_ID, TD_Val>(k_last_to_tds_state, MapGetKeys(add_tds))
    ensures TDsStateGetTDIDs(k_last_from_tds_state) == TDsStateGetTDIDs(k'_last_from_tds_state) + MapGetKeys<TD_ID, TD_Val>(add_tds)
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(AllActiveTDs(k'), todeactivate_td_ids);

    assert MapGetKeys(MapSubmap(k.objects.tds, todeactivate_td_ids)) == todeactivate_td_ids;
    assert forall e1, e2 :: e1 in MapGetKeys(add_tds) && e2 in AllActiveTDs(k')
            ==> e1 != e2;
    Lemma_SetsWithoutSameElemHaveEmptyIntersection(MapGetKeys(add_tds), AllActiveTDs(k'));

    assert MapGetKeys(add_tds) * AllActiveTDs(k') == {};
}

// (need 260s to verify)
lemma Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_Private(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, 
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL && 
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in both k and k'
    requires |k'_tds_states| > 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params, 
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, 
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))

    requires forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-2] && k2 in add_tds ==> k1 != k2
    requires forall k'_tds_state :: k'_tds_state in k'_tds_states[..|k'_tds_states|-1]
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Requirements needed by the requirements below
    requires TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds)) == AllActiveTDs(k)
    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds))
    requires forall k'_tds_state :: k'_tds_state in k'_tds_states[..|k'_tds_states|-1]
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires P_SubjObjDeactivate_IfTDsInReachableTDsStatesInNewKIsSecure_ThenTDsInReachableTDsStatesInKIsSecure(
                k, k_params, k', k'_params, k'_tds_states[..|k'_tds_states|-1], add_tds)
        // Requirements from the induction hypothesis

    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Properties needed by the properties below
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
        // Property: ActiveTDsState(k) -->* k_last_to_tds_state (
        // k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1])
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    ensures P_SubjObjDeactivate_IfTDsInReachableTDsStatesInNewKIsSecure_ThenTDsInReachableTDsStatesInKIsSecure(
                k, k_params, k', k'_params, k'_tds_states, add_tds)
{
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    Lemma_AllActiveDevs_ReturnCorrectResult(k');
    assert forall dev_id2 :: dev_id2 in AllActiveDevs(k')
                ==> IsDevID_SlimState(k'_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k'_params.subjects, dev_id2) != NULL;

    var result_k_last_to_tds_state := 
                Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_ActiveTDsStatesInKCanReach_Private(
                    k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_tds_states, k'_devs, add_tds);

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);
    Lemma_SequenceHighlightLastElem(k'_tds_states);
    forall k'_tds_state, k_tds_state | k'_tds_state in k'_tds_states &&
                    k_tds_state == MapConcat<TD_ID, TD_Val>(k'_tds_state, add_tds) &&
                    ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_tds_state)
        ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)
    {
        assert k'_tds_state == k'_tds_states[|k'_tds_states|-1] || k'_tds_state in k'_tds_states[..|k'_tds_states|-1];
        if(k'_tds_state == k'_tds_states[|k'_tds_states|-1])
        {
            var k'_last_from_tds_state := k'_tds_states[|k'_tds_states|-2];
            var k'_last_to_tds_state := k'_tds_states[|k'_tds_states|-1];
            var k'_last_dev := k'_devs[|k'_devs|-1];
            var k_last_from_tds_state := MapConcat<TD_ID, TD_Val> (k'_last_from_tds_state, add_tds);
            var k_last_to_tds_state := MapConcat<TD_ID, TD_Val> (k'_last_to_tds_state, add_tds);

            assert k_last_to_tds_state == result_k_last_to_tds_state;

            assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_last_to_tds_state);
        }
        else
        {
            assert k'_tds_state in k'_tds_states[..|k'_tds_states|-1];

            assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state);
        }
    }
}

lemma Lemma_SubjObjDeactivate_ActiveTDsStateInNewKConcatWithAddTDs_EqualToActiveTDsStateInK(
    k:State, k':State, todeactivate_td_ids:set<TD_ID>, add_tds:map<TD_ID, TD_Val>,
    k'_from_tds_state:TDs_Vals, k_from_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)

    requires todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    requires todeactivate_td_ids <= AllActiveTDs(k)
    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids)) 
    requires AllActiveTDs(k') * todeactivate_td_ids == {}

    requires AllActiveTDs(k') == AllActiveTDs(k) - todeactivate_td_ids

    requires forall td_id :: td_id in k.objects.tds
                ==> k'.objects.tds[td_id].val == k.objects.tds[td_id].val

    requires k'_from_tds_state == ActiveTDsState(k')
    requires k_from_tds_state == MapConcat<TD_ID, TD_Val>(k'_from_tds_state, add_tds)

    ensures k_from_tds_state == ActiveTDsState(k)
{
    assert AllActiveTDs(k') <= AllActiveTDs(k);
    assert forall td_id :: td_id in add_tds
            ==> add_tds[td_id] == k.objects.tds[td_id].val;

    assert forall td_id :: td_id in k_from_tds_state
            <==> td_id in AllActiveTDs(k') || td_id in add_tds;
    Lemma_SetsWithoutSameElemHaveEmptyIntersection(MapGetKeys(add_tds), AllActiveTDs(k'));
    assert MapGetKeys(add_tds) * AllActiveTDs(k') == {};
    assert todeactivate_td_ids == MapGetKeys(add_tds);
    assert TDsStateGetTDIDs(k_from_tds_state) == todeactivate_td_ids + AllActiveTDs(k');

    Lemma_SetsAddProperty(AllActiveTDs(k), todeactivate_td_ids, AllActiveTDs(k'));
    assert TDsStateGetTDIDs(k_from_tds_state) == AllActiveTDs(k);

    assert TDsStateGetTDIDs(ActiveTDsState(k)) == AllActiveTDs(k);
    assert TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(ActiveTDsState(k));
}

lemma Lemma_SubjObjDeactivate_ActiveTDsStateInNewKConcatWithAddTDs_ResultContainsAllActiveTDsInK(
    k:State, k':State, todeactivate_td_ids:set<TD_ID>, add_tds:map<TD_ID, TD_Val>,
    k'_tds_state:TDs_Vals, k_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)

    requires todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    requires todeactivate_td_ids <= AllActiveTDs(k)
    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids)) 
    requires AllActiveTDs(k') * todeactivate_td_ids == {}

    requires AllActiveTDs(k') == AllActiveTDs(k) - todeactivate_td_ids

    requires forall td_id :: td_id in k.objects.tds
                ==> k'.objects.tds[td_id].val == k.objects.tds[td_id].val

    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires k_tds_state == MapConcat<TD_ID, TD_Val>(k'_tds_state, add_tds)

    ensures TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
{
    // Dafny can automatically prove this lemma
}

// (needs 150s to prove)
lemma Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Base_ActiveTDsStatesInKCanReach_Private(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, 
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
) returns (k_to_tds_state:TDs_Vals)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL && 
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in both k and k'
    requires |k'_tds_states| == 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))

    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Properties needed by the properties below
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
        // Property: ActiveTDsState(k) -->* k_last_to_tds_state (
        // k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1])
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')

    ensures k_to_tds_state == MapConcat<TD_ID, TD_Val>(k'_tds_states[1], add_tds)
    ensures k_to_tds_state in AllReachableActiveTDsStates(k)
    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_to_tds_state)
{
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k);
    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k');
    assert k_params.subjects == k.subjects;
    assert k'_params.subjects == k'.subjects;
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    assert forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k');
    assert forall k1, k2 :: k1 in AllActiveTDs(k') && k2 in add_tds ==> k1 != k2;
    assert forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2);

    var k'_from_tds_state := k'_tds_states[0];
    var k'_to_tds_state :=  k'_tds_states[1];
    var k'_dev := k'_devs[0];
    var k_from_tds_state := MapConcat<TD_ID, TD_Val>(k'_from_tds_state, add_tds);
    k_to_tds_state := MapConcat<TD_ID, TD_Val>(k'_to_tds_state, add_tds);

    assert k'_from_tds_state == ActiveTDsState(k');
    Lemma_SubjObjDeactivate_ActiveTDsStateInNewKConcatWithAddTDs_EqualToActiveTDsStateInK(
        k, k', todeactivate_td_ids, add_tds, k'_from_tds_state, k_from_tds_state);
    assert k_from_tds_state == ActiveTDsState(k);

    Lemma_SubjObjDeactivate_ActiveTDsStateInNewKConcatWithAddTDs_ResultContainsAllActiveTDsInK(
        k, k', todeactivate_td_ids, add_tds, k'_from_tds_state, k_from_tds_state);
    Lemma_SubjObjDeactivate_ActiveTDsStateInNewKConcatWithAddTDs_ResultContainsAllActiveTDsInK(
        k, k', todeactivate_td_ids, add_tds, k'_to_tds_state, k_to_tds_state);
    assert TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state);

    // Prove TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)
    Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Induction_PropertyOfAddTDs(
        k, k', todeactivate_td_ids, k'_tds_states, add_tds, 
        k'_from_tds_state, k_from_tds_state, k'_to_tds_state, k_to_tds_state);
    Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
        k'_from_tds_state, k'_to_tds_state, add_tds, k_from_tds_state, k_to_tds_state);
    assert TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state);

    // Prove k_from_tds_state --> k_to_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);
    Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_dev,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k'_dev, k_from_tds_state, k_to_tds_state);

    // Prove k_from_tds_state -->1+ k_to_tds_state
    Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, k'_dev, AllActiveDevs(k), k_from_tds_state, k_to_tds_state);
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), k_to_tds_state);

    assert TDsStateGetTDIDs(k_to_tds_state) == AllActiveTDs(k);
    assert k_to_tds_state in AllReachableActiveTDsStates(k);
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_to_tds_state);
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Base_ActiveTDsStatesInKCanReach(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, 
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
) 
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL && 
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in both k and k'
    requires |k'_tds_states| == 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))

    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> (forall k1, k2 :: k1 in k'_tds_state && k2 in add_tds ==> k1 != k2)
        // Properties needed by the properties below
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
        // Property: ActiveTDsState(k) -->* k_last_to_tds_state (
        // k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1])
    ensures forall k'_tds_state :: k'_tds_state in k'_tds_states
                ==> TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    ensures P_SubjObjDeactivate_IfTDsInReachableTDsStatesInNewKIsSecure_ThenTDsInReachableTDsStatesInKIsSecure(
                k, k_params, k', k'_params, k'_tds_states, add_tds)
{
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    var k'_from_tds_state := k'_tds_states[0];
    var k'_to_tds_state :=  k'_tds_states[1];
    var k'_dev := k'_devs[0];
    var k_from_tds_state := MapConcat<TD_ID, TD_Val>(k'_from_tds_state, add_tds);
    var k_to_tds_state := MapConcat<TD_ID, TD_Val>(k'_to_tds_state, add_tds);

    assert k'_from_tds_state == ActiveTDsState(k');
    Lemma_SubjObjDeactivate_ActiveTDsStateInNewKConcatWithAddTDs_EqualToActiveTDsStateInK(
        k, k', todeactivate_td_ids, add_tds, k'_from_tds_state, k_from_tds_state);
    assert k_from_tds_state == ActiveTDsState(k);

    var result_k_to_tds_state := 
            Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter_Base_ActiveTDsStatesInKCanReach_Private(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_tds_states, k'_devs, add_tds);

    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);
    assert forall k'_tds_state :: k'_tds_state in k'_tds_states
            ==> k'_tds_state == k'_tds_states[0] || k'_tds_state == k'_tds_states[1];

    forall k'_tds_state, k_tds_state | k'_tds_state in k'_tds_states &&
                    k_tds_state == MapConcat<TD_ID, TD_Val>(k'_tds_state, add_tds) &&
                    ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_tds_state)
        ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)
    {
        if(k'_tds_state == k'_tds_states[1])
        {
            assert k_tds_state == k_to_tds_state;
        }
        else
        {
            assert k'_tds_state == k'_tds_states[0];
            assert k_tds_state == k_from_tds_state;
            assert k_tds_state == ActiveTDsState(k);
        }
    }
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_NewKFulfillsKParamsPreConditions(k':State)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    ensures DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(KToKParams(k'))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_CertainVarsInKParamsAndNewKParamsAreSame(k:State, k':State)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    ensures KToKParams(k').objs_td_ids == KToKParams(k).objs_td_ids
    ensures KToKParams(k').objs_fd_ids == KToKParams(k).objs_fd_ids
    ensures KToKParams(k').objs_do_ids == KToKParams(k).objs_do_ids
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>, 
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k
    requires k'_td_id in k_tds_state
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') <= AllActiveTDs(k)

    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id)
        // Requirement: In <k_tds_state>, k'_td_id has no invalid transfers

    requires k'_td_id in AllActiveTDs(k)
    requires k'_td_id in AllActiveTDs(k')
    requires k'_tds_state[k'_td_id] == k_tds_state[k'_td_id]

    requires P_ObjsToBeDeactivatedAreInactiveInNewK_AndNoActiveDevsInNewKHaveTransferToThem(
                k, k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_tds_state)

    requires k'_dev_id in AllActiveDevs(k')
    requires CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id)
 
    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id)
        // Property: In <k'_tds_state>, k'_td_id has no invalid transfers
{
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_TDs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k_tds_state, k'_tds_state, k'_dev_id, k'_td_id);
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_FDs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, k_tds_state, k'_tds_state, k'_dev_id, k'_td_id);
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_DOs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_do_ids, k_tds_state, k'_tds_state, k'_dev_id, k'_td_id);

    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_NewKFulfillsKParamsPreConditions(k');
    Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Prove(
        k'_params, k'_tds_state, k'_td_id);
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_TDs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, 
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k
    requires k'_td_id in k_tds_state
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') <= AllActiveTDs(k)

    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id)
        // Requirement: In <k_tds_state>, k'_td_id has no invalid transfers

    requires k'_td_id in AllActiveTDs(k)
    requires k'_td_id in AllActiveTDs(k')
    requires k'_tds_state[k'_td_id] == k_tds_state[k'_td_id]

    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, td_id.oid) == {}
        // Requirement: All active devices in k' must have no access to TDs 
        // being deactivated

    requires k'_dev_id in AllActiveDevs(k')
    requires CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id)
 
    ensures forall td_id2 :: td_id2 in k'_tds_state[k'_td_id].trans_params_tds
            ==> td_id2 in k'_params.objs_td_ids &&
                td_id2 !in k'_params.hcoded_td_ids &&
                (ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, k'_td_id.oid) || 
                        // The TD (<k'_td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 k'_tds_state[k'_td_id].trans_params_tds[td_id2].amodes == {})
    ensures forall td_id :: td_id in k'_tds_state[k'_td_id].trans_params_tds
                ==> td_id in k'.objects.tds
{
    assert forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id);

    AllReqAModesPermsSubsetOfRW();
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_NewKFulfillsKParamsPreConditions(k');
    assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k'_params);

    Lemma_SubjObjDeactivate_CertainVarsInKParamsAndNewKParamsAreSame(k, k');

    if(exists td_id2 :: td_id2 in k'_tds_state[k'_td_id].trans_params_tds &&
                    (td_id2 !in k'_params.objs_td_ids ||
                     td_id2 in k'_params.hcoded_td_ids ||
                        (ObjPID(k', td_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                         k'_tds_state[k'_td_id].trans_params_tds[td_id2].amodes != {})))
    {
        var td_id2 :| td_id2 in k'_tds_state[k'_td_id].trans_params_tds &&
                    (td_id2 !in k'_params.objs_td_ids || 
                     td_id2 in k'_params.hcoded_td_ids ||
                        (ObjPID(k', td_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                         k'_tds_state[k'_td_id].trans_params_tds[td_id2].amodes != {}));

        assert k'_tds_state[k'_td_id] == k_tds_state[k'_td_id];
        if(td_id2 !in k'_params.objs_td_ids)
        {
            assert td_id2 !in k_params.objs_td_ids;
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
        }
        else if(td_id2 in k'_params.hcoded_td_ids)
        {
            assert td_id2 in k_params.hcoded_td_ids;
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
        }
        else
        {
            assert ObjPID(k', td_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                    k'_tds_state[k'_td_id].trans_params_tds[td_id2].amodes != {};
            if(td_id2 !in todeactivate_td_ids)
            {
                assert ObjPID(k', td_id2.oid) == ObjPID(k, td_id2.oid);
                assert ObjPID(k', k'_td_id.oid) == ObjPID(k, k'_td_id.oid);
                assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
            }
            else
            {
                assert k'_tds_state[k'_td_id].trans_params_tds[td_id2].amodes != {};

                // Prove DevAModesToObj(k, k_tds_state, k'_dev_id, td_id2.oid) != {}
                assert k'_td_id in k_tds_state;
                assert CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id);
                assert td_id2.oid in GetObjIDsRefedInTD(k_tds_state, k'_td_id);
                assert GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, td_id2.oid) != {};
                
                Lemma_DevAModesToObj_SubjObjDeactivate_IfDevCanReadTDAndTDIncludesTransferToObj_ThenDevHasTransferToObj(
                    k, k_params, k_tds_state, k'_dev_id, k'_td_id, td_id2.oid);
                assert DevAModesToObj(k, k_tds_state, k'_dev_id, td_id2.oid) != {};

                // Show conflicts
                assert td_id2 in todeactivate_td_ids;
                assert DevAModesToObj(k, k_tds_state, k'_dev_id, td_id2.oid) == {};
            }
        }
    }
    assert forall td_id :: td_id in k'_tds_state[k'_td_id].trans_params_tds
                ==> td_id in k'.objects.tds;
}

// (needs 100s to verify)
lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_FDs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>,
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires todeactivate_fd_ids <= MapGetKeys(k.objects.fds)
    requires forall fd_id :: fd_id in todeactivate_fd_ids
                ==> ObjPID(k, fd_id.oid) != NULL && ObjPID(k', fd_id.oid) == NULL
    requires forall fd_id :: fd_id in k.objects.fds && fd_id !in todeactivate_fd_ids
                ==> ObjPID(k', fd_id.oid) == ObjPID(k, fd_id.oid)

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k
    requires k'_td_id in k_tds_state
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') <= AllActiveTDs(k)

    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id)
        // Requirement: In <k_tds_state>, k'_td_id has no invalid transfers

    requires k'_td_id in AllActiveTDs(k)
    requires k'_td_id in AllActiveTDs(k')
    requires k'_tds_state[k'_td_id] == k_tds_state[k'_td_id]

    requires forall fd_id, dev_id :: fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, fd_id.oid) == {}
        // Requirement: All active devices in k' must have no access to FDs 
        // being deactivated

    requires k'_dev_id in AllActiveDevs(k')
    requires CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id)

    requires forall td_id :: td_id in k'_tds_state[k'_td_id].trans_params_tds
                ==> td_id in k'.objects.tds
 
    ensures forall fd_id2 :: fd_id2 in k'_tds_state[k'_td_id].trans_params_fds
            ==> fd_id2 in k'_params.objs_fd_ids &&
                ((ObjPID_SlimState(k'_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, k'_td_id.oid)) ||
                        // The TD (<k'_td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 k'_tds_state[k'_td_id].trans_params_fds[fd_id2].amodes == {})
    ensures forall fd_id :: fd_id in k'_tds_state[k'_td_id].trans_params_fds
                ==> fd_id in k'.objects.fds
{
    assert forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id);

    AllReqAModesPermsSubsetOfRW();
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_NewKFulfillsKParamsPreConditions(k');
    assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k'_params);

    Lemma_SubjObjDeactivate_CertainVarsInKParamsAndNewKParamsAreSame(k, k');

    if(exists fd_id2 :: fd_id2 in k'_tds_state[k'_td_id].trans_params_fds &&
                    (fd_id2 !in k'_params.objs_fd_ids ||
                        (ObjPID(k', fd_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                         k'_tds_state[k'_td_id].trans_params_fds[fd_id2].amodes != {})))
    {
        var fd_id2 :| fd_id2 in k'_tds_state[k'_td_id].trans_params_fds &&
                    (fd_id2 !in k'_params.objs_fd_ids || 
                        (ObjPID(k', fd_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                         k'_tds_state[k'_td_id].trans_params_fds[fd_id2].amodes != {}));

        assert k'_tds_state[k'_td_id] == k_tds_state[k'_td_id];
        if(fd_id2 !in k'_params.objs_fd_ids)
        {
            assert fd_id2 !in k_params.objs_fd_ids;
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
        }
        else
        {
            assert ObjPID(k', fd_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                    k'_tds_state[k'_td_id].trans_params_fds[fd_id2].amodes != {};
            if(fd_id2 !in todeactivate_fd_ids)
            {
                assert ObjPID(k', fd_id2.oid) == ObjPID(k, fd_id2.oid);
                assert ObjPID(k', k'_td_id.oid) == ObjPID(k, k'_td_id.oid);
                assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
            }
            else
            {
                assert k'_tds_state[k'_td_id].trans_params_fds[fd_id2].amodes != {};

                // Prove DevAModesToObj(k, k_tds_state, k'_dev_id, fd_id2.oid) != {}
                assert k'_td_id in k_tds_state;
                assert CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id);
                assert fd_id2.oid in GetObjIDsRefedInTD(k_tds_state, k'_td_id);
                Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_FDs_GetAModesOfObjRefedInTDNotEmpty(
                    k', k'_tds_state, k'_dev_id, k'_td_id, fd_id2);
                assert GetAModesOfObjRefedInTD(k'_tds_state, k'_td_id, fd_id2.oid) != {};
                assert GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, fd_id2.oid) != {};
                
                Lemma_DevAModesToObj_SubjObjDeactivate_IfDevCanReadTDAndTDIncludesTransferToObj_ThenDevHasTransferToObj(
                    k, k_params, k_tds_state, k'_dev_id, k'_td_id, fd_id2.oid);
                assert DevAModesToObj(k, k_tds_state, k'_dev_id, fd_id2.oid) != {};

                // Show conflicts
                assert fd_id2 in todeactivate_fd_ids;
                assert DevAModesToObj(k, k_tds_state, k'_dev_id, fd_id2.oid) == {};
            }
        }
    }
    assert forall fd_id :: fd_id in k'_tds_state[k'_td_id].trans_params_fds
                ==> fd_id in k'.objects.fds;
}

// (needs 100s to verify)
lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_DOs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires todeactivate_do_ids <= MapGetKeys(k.objects.dos)
    requires forall do_id :: do_id in todeactivate_do_ids
                ==> ObjPID(k, do_id.oid) != NULL && ObjPID(k', do_id.oid) == NULL
    requires forall do_id :: do_id in k.objects.dos && do_id !in todeactivate_do_ids
                ==> ObjPID(k', do_id.oid) == ObjPID(k, do_id.oid)

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k
    requires k'_td_id in k_tds_state
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') <= AllActiveTDs(k)

    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id)
        // Requirement: In <k_tds_state>, k'_td_id has no invalid transfers

    requires k'_td_id in AllActiveTDs(k)
    requires k'_td_id in AllActiveTDs(k')
    requires k'_tds_state[k'_td_id] == k_tds_state[k'_td_id]

    requires forall do_id, dev_id :: do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, do_id.oid) == {}
        // Requirement: All active devices in k' must have no access to DOs 
        // being deactivated

    requires k'_dev_id in AllActiveDevs(k')
    requires CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id)

    requires forall td_id :: td_id in k'_tds_state[k'_td_id].trans_params_tds
                ==> td_id in k'.objects.tds
    requires forall fd_id :: fd_id in k'_tds_state[k'_td_id].trans_params_fds
                ==> fd_id in k'.objects.fds
 
    ensures forall do_id2 :: do_id2 in k'_tds_state[k'_td_id].trans_params_dos
            ==> do_id2 in k'_params.objs_do_ids && 
                (ObjPID_SlimState(k'_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k'_params.objs_pids, k'_td_id.oid) ||
                        // The TD (<k'_td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes == {})
{
    assert forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id);

    AllReqAModesPermsSubsetOfRW();
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_NewKFulfillsKParamsPreConditions(k');
    assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k'_params);

    Lemma_SubjObjDeactivate_CertainVarsInKParamsAndNewKParamsAreSame(k, k');

    if(exists do_id2 :: do_id2 in k'_tds_state[k'_td_id].trans_params_dos &&
                    (do_id2 !in k'_params.objs_do_ids ||
                        (ObjPID(k', do_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                         k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes != {})))
    {
        var do_id2 :| do_id2 in k'_tds_state[k'_td_id].trans_params_dos &&
                    (do_id2 !in k'_params.objs_do_ids || 
                        (ObjPID(k', do_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                         k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes != {}));

        assert k'_tds_state[k'_td_id] == k_tds_state[k'_td_id];
        if(do_id2 !in k'_params.objs_do_ids)
        {
            assert do_id2 !in k_params.objs_do_ids;
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
        }
        else
        {
            assert ObjPID(k', do_id2.oid) != ObjPID(k', k'_td_id.oid) && 
                    k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes != {};
            if(do_id2 !in todeactivate_do_ids)
            {
                assert ObjPID(k', do_id2.oid) == ObjPID(k, do_id2.oid);
                assert ObjPID(k', k'_td_id.oid) == ObjPID(k, k'_td_id.oid);
                assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);
            }
            else
            {
                assert k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes != {};

                // Prove DevAModesToObj(k, k_tds_state, k'_dev_id, do_id2.oid) != {}
                assert k'_td_id in k_tds_state;
                assert CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id);
                assert do_id2.oid in GetObjIDsRefedInTD(k_tds_state, k'_td_id);
                Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_DOs_GetAModesOfObjRefedInTDNotEmpty(
                    k', k'_tds_state, k'_dev_id, k'_td_id, do_id2);
                assert GetAModesOfObjRefedInTD(k'_tds_state, k'_td_id, do_id2.oid) != {};
                assert GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, do_id2.oid) != {};
                
                Lemma_DevAModesToObj_SubjObjDeactivate_IfDevCanReadTDAndTDIncludesTransferToObj_ThenDevHasTransferToObj(
                    k, k_params, k_tds_state, k'_dev_id, k'_td_id, do_id2.oid);
                assert DevAModesToObj(k, k_tds_state, k'_dev_id, do_id2.oid) != {};

                // Show conflicts
                assert do_id2 in todeactivate_do_ids;
                assert DevAModesToObj(k, k_tds_state, k'_dev_id, do_id2.oid) == {};
            }
        }
    }
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_FDs_GetAModesOfObjRefedInTDNotEmpty(
    k':State, k'_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID, fd_id2:FD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires fd_id2 in k'.objects.fds
    requires k'_td_id in k'_tds_state
    requires fd_id2 in k'_tds_state[k'_td_id].trans_params_fds
    requires k'_tds_state[k'_td_id].trans_params_fds[fd_id2].amodes != {}

    requires forall td_id :: td_id in k'_tds_state[k'_td_id].trans_params_tds
                ==> td_id in k'.objects.tds

    ensures GetAModesOfObjRefedInTD(k'_tds_state, k'_td_id, fd_id2.oid) != {}
{
    assert TD_ID(fd_id2.oid) !in k'.objects.tds;
    assert DO_ID(fd_id2.oid) !in k'.objects.dos;
}

lemma Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates_DOs_GetAModesOfObjRefedInTDNotEmpty(
    k':State, k'_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID, do_id2:DO_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires do_id2 in k'.objects.dos
    requires k'_td_id in k'_tds_state
    requires do_id2 in k'_tds_state[k'_td_id].trans_params_dos
    requires k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes != {}

    requires forall td_id :: td_id in k'_tds_state[k'_td_id].trans_params_tds
                ==> td_id in k'.objects.tds
    requires forall fd_id :: fd_id in k'_tds_state[k'_td_id].trans_params_fds
                ==> fd_id in k'.objects.fds

    ensures GetAModesOfObjRefedInTD(k'_tds_state, k'_td_id, do_id2.oid) != {}
{
    assert TD_ID(do_id2.oid) !in k'.objects.tds;
    assert FD_ID(do_id2.oid) !in k'.objects.fds;

    assert do_id2 in k'_tds_state[k'_td_id].trans_params_dos;
    assert TD_ID(do_id2.oid) !in k'_tds_state[k'_td_id].trans_params_tds;
    assert FD_ID(do_id2.oid) !in k'_tds_state[k'_td_id].trans_params_fds;

    assert GetAModesOfObjRefedInTD(k'_tds_state, k'_td_id, do_id2.oid) == k'_tds_state[k'_td_id].trans_params_dos[do_id2].amodes;
}

lemma Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs_Induction_Private(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>, 
    k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>, add_tds:map<TD_ID, TD_Val>
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)
    requires SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToFDsAndDOsBeingDeactivated(
                k, k', todeactivate_fd_ids, todeactivate_do_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires forall o_id :: o_id in AllActiveObjs(k')
            ==> ObjPID(k, o_id) == ObjPID(k', o_id)
        // Requirement: All objects active in k' have the same PID as in k
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL && 
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in both k and k'
    requires |k'_tds_states| > 2 && 
            (forall tds_state2 :: tds_state2 in k'_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
            |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
            k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
            (forall i :: 0<=i<|k'_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) && 
                    IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                        k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]))
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))
    
    requires forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-2] && k2 in add_tds ==> k1 != k2
    requires forall tds_state2 :: tds_state2 in k'_tds_states[..|k'_tds_states|-1]
                ==> ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
    requires TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds)) == AllActiveTDs(k)
    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], add_tds))
        // Requirements got from the induction hypothesis

    ensures forall k1, k2 :: k1 in k'_tds_states[|k'_tds_states|-1] && k2 in add_tds ==> k1 != k2
        // Properties need to be fulfilled for MapConcat
    ensures forall tds_state2 :: tds_state2 in k'_tds_states
                ==> ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
        // Property 2: Any active TDs' state (active TDs of k') reachable from 
        // ActiveTDsState(k') and intermediate TDs' states have no invalid refs
    ensures TDsStateGetTDIDs(MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds)) == AllActiveTDs(k)
    ensures IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), MapConcat<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], add_tds))
        // Property: ActiveTDsState(k) -->* k_last_to_tds_state (
        // k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1])
{
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_devs);
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);

    var k'_last_from_tds_state := k'_tds_states[|k'_tds_states|-2];
    var k'_last_to_tds_state := k'_tds_states[|k'_tds_states|-1];
    var k'_last_dev := k'_devs[|k'_devs|-1];
    var k_last_from_tds_state := MapConcat<TD_ID, TD_Val>(k'_last_from_tds_state, add_tds);
    var k_last_to_tds_state := MapConcat<TD_ID, TD_Val>(k'_last_to_tds_state, add_tds);

    // Prove TDs in k_last_from_tds_state has no invalid refs
    Lemma_SubjObjDeactivate_TDsStateIsValidBeforeRemoveTDsIfValidAfter(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_tds_states, k'_devs, add_tds);

    // Prove TDsStateDiff(k'_last_to_tds_state, k'_last_from_tds_state) == TDsStateDiff(k_last_to_tds_state, k_last_from_tds_state)
    Lemma_AddTDs_Property(k'_last_from_tds_state, add_tds, k_last_from_tds_state);
    Lemma_AddTDs_Property(k'_last_to_tds_state, add_tds, k_last_to_tds_state);
    Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs_Induction_Private_AddTD(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, add_tds, 
        k'_last_from_tds_state, k_last_from_tds_state);
    Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
        k'_last_from_tds_state, k'_last_to_tds_state, add_tds, k_last_from_tds_state, k_last_to_tds_state);

    // Prove the properties of ActiveTDsState(k) -->1+ k_last_from_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                AllActiveDevs(k), ActiveTDsState(k), k_last_from_tds_state); 
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_last_from_tds_state);

    // Prove k_last_from_tds_state --> k_last_to_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);
    Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k'_last_dev,
        k_last_from_tds_state, k_last_to_tds_state, k'_last_from_tds_state, k'_last_to_tds_state);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                k'_last_dev, k_last_from_tds_state, k_last_to_tds_state);

    // Prove ActiveTDsState(k) -->1+ k_last_to_tds_state
    Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(k_params,
        k'_last_dev, AllActiveDevs(k),
        ActiveTDsState(k), k_last_from_tds_state, k_last_to_tds_state);

    // Prove TDs in k'_last_to_tds_state has no invalid refs
    assert k_last_to_tds_state in AllReachableActiveTDsStates(k);
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_last_to_tds_state);

    assert P_ObjsToBeDeactivatedAreInactiveInNewK_AndNoActiveDevsInNewKHaveTransferToThem(
                k, k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_last_to_tds_state);
    Lemma_SubjObjDeactivate_TDsStateIsValidAfterAddTDsIfValidBefore(k, k_params, k', k'_params, 
        todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_last_to_tds_state, k'_last_to_tds_state);
    assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_last_to_tds_state);

    // Prove Property 2
    Lemma_AllElemsIndexedInSeqAreInSeq(k'_tds_states);
    Lemma_SequenceHighlightLastElem(k'_tds_states);
    forall tds_state2 | tds_state2 in k'_tds_states
        ensures ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
    {
        if (tds_state2 == k'_tds_states[|k'_tds_states|-1])
        {
            assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2);
        }
        else
        {
            assert tds_state2 in k'_tds_states[..|k'_tds_states|-1];
            assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2);
        }
    }
}

lemma Lemma_SubjObjDeactivate_ReachableActiveTDsStateInNewKHasNoInvalidRefs_Induction_Private_AddTD(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>,
    add_tds:map<TD_ID, TD_Val>, 
    k'_last_from_tds_state:TDs_Vals, k_last_from_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)

    requires add_tds == TDsToTDsVals(MapSubmap(k.objects.tds, todeactivate_td_ids))

    requires forall k1, k2 :: k1 in k'_last_from_tds_state && k2 in add_tds ==> k1 != k2
    requires k_last_from_tds_state == MapConcat<TD_ID, TD_Val>(k'_last_from_tds_state, add_tds)

    ensures add_tds ==  MapSubmap(k_last_from_tds_state, MapGetKeys(add_tds))
{
    // Dafny can automatically prove this lemma
}




//******** Lemmas of ReachableTDs' States ********//
// (needs 100s to verify)
lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, dev_id) 
    requires SubjPID_DevID(k, dev_id) != NULL
    requires SubjPID_DevID(k', dev_id) != NULL
        // Requirement: The device (<dev_id>) is an existing active device 
        // (i.e., not activating between k and k')

    requires TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_from_tds_state) == TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k')
    requires TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)

    requires forall td_id :: td_id in TDsStateGetTDIDs(k_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k_from_tds_state> contains additional active TDs (if 
        // any) from <k'_from_tds_state>
    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_from_tds_state, dev_id, td_id.oid) == {}
        // Requirment: No active device in k' has transfer to the TDs to be
        // deactivated
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
    ensures IDToDev_SlimState(k'_params.subjects, dev_id).td_ids <= k'_params.objs_td_ids
    ensures (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)))
            <==>
            (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)))
    ensures IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k'_params,   
                dev_id, k'_from_tds_state, TDsStateDiff(k'_to_tds_state, k'_from_tds_state))
            <==> 
            IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, 
                dev_id, k_from_tds_state, TDsStateDiff(k_to_tds_state, k_from_tds_state))
{
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Left(
        k, k_params, k', k'_params,
        todeactivate_s_ids, todeactivate_td_ids, dev_id,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);
    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Right(
        k, k_params, k', k'_params,
        todeactivate_s_ids, todeactivate_td_ids, dev_id,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);
        
    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_DefApply(k'_params,   
        dev_id, k'_from_tds_state, TDsStateDiff(k'_to_tds_state, k'_from_tds_state));
    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_DefApply(k_params,   
        dev_id, k_from_tds_state, TDsStateDiff(k_to_tds_state, k_from_tds_state));
}

// Lemma: For the <IsActiveTDsStateReachActiveTDsStateInOneStep> function, 
// deactivating subjects and TDs does not change the current accesses of other
// active devices
// (needs 50s to verify)
lemma Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, dev_id) 
    requires SubjPID_DevID(k, dev_id) != NULL
    requires SubjPID_DevID(k', dev_id) != NULL
        // Requirement: The device (<dev_id>) is an existing active device 
        // (i.e., not activating between k and k')

    requires TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_from_tds_state) == TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k')
    requires TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)

    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_from_tds_state)
                ==>  k'_from_tds_state[td_id] == k_from_tds_state[td_id]
        // Requirement: <k_from_tds_state> contains additional active TDs (if 
        // any) from <k'_from_tds_state>
    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_from_tds_state, dev_id, td_id.oid) == {}
        // Requirment: No active device in k' has transfer to the TDs to be
        // deactivated
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, k'_from_tds_state, k'_to_tds_state)
            <==>
            IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, k_from_tds_state, k_to_tds_state)
{
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
        k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, dev_id,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);

    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, k_from_tds_state, k_to_tds_state)
                == IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, k_from_tds_state, TDsStateDiff(k_to_tds_state, k_from_tds_state));
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, k'_from_tds_state, k'_to_tds_state)
                == IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k'_params, dev_id, k'_from_tds_state, TDsStateDiff(k'_to_tds_state, k'_from_tds_state));
}




//******** Lemmas of CanActiveDevReadActiveTD and NoActiveDevHasTransferToObjsInReachableActiveTDsStates ********//
// Lemma: In <k'_tds_state>, if an device active in k' has read transfers
// to an active TD, then in <k_tds_state>, the same device also have read
// transfers to the same (active) TD.
lemma Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInNewK_ThenDevCanReadTDInK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k_tds_state> contains additional active TDs (if 
        // any) from <k'_tds_state>

    requires dev_id in AllActiveDevs(k')
    requires td_id in AllActiveTDs(k')

    requires CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id)

    ensures CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id)
{
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert forall drv_id :: drv_id in k'.subjects.drvs
            ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids);
    assert forall dev_id :: dev_id in k'.subjects.devs
            ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids);

    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k);
    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k');
    assert k_params.subjects == k.subjects;
    assert k'_params.subjects == k'.subjects;
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    assert forall td_id :: td_id in AllActiveTDs(k')
        ==> k'_tds_state[td_id] == k_tds_state[td_id];

    var k'_td_ids:seq<TD_ID> := Lemma_CanActiveDevReadActiveTD_Apply(k'_params, k'_tds_state, dev_id, td_id);

    assert P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(k'_tds_state, k'_td_ids);

    Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInNewK_ThenDevCanReadTDInK_Private(
    k, k', k_tds_state, k'_tds_state, k'_td_ids, dev_id, td_id);

    assert CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id);
}

// Lemma: In <k'_tds_state>, if an device active in k' has read transfers
// to an active TD, then in <k_tds_state>, the same device also have read
// transfers to the same (active) TD.
// (needs 40s to verify)
lemma Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInK_ThenDevCanReadTDInNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k_tds_state> contains additional active TDs (if 
        // any) from <k'_tds_state>

    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, td_id.oid) == {}
        // Requirment: No active device has transfer to the TDs to be 
        // deactivated

    requires dev_id in AllActiveDevs(k')
    requires td_id in AllActiveTDs(k')

    requires CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id)    

    ensures CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id)
{
    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k);
    Lemma_SubjObjDeactivate_PropertyOfKToKParams(k');
    assert k_params.subjects == k.subjects;
    assert k'_params.subjects == k'.subjects;
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    var k_td_ids:seq<TD_ID> := Lemma_CanActiveDevReadActiveTD_Apply(k_params, k_tds_state, dev_id, td_id);
    assert P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(k_tds_state, k_td_ids);

    // Prove forall td_id2 :: td_id2 in k_td_ids ==> td_id2 in k'_tds_state
    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(
        k_params, k_tds_state, dev_id, k_td_ids, td_id);
    if (exists td_id2 :: td_id2 in k_td_ids && td_id2 !in k'_tds_state)
    {
        var td_id2 :| td_id2 in k_td_ids && td_id2 !in k'_tds_state;
        assert td_id2 in todeactivate_td_ids;

        // Show conflicts
        //// In one hand
        assert CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2);
        Lemma_CanActiveDevReadActiveTD_ThenTDIsHCodedTDOrDevAModesToObjHasRTransfer(
            k, k_params, k_tds_state, dev_id, td_id2);
        assert td_id2 == k.subjects.devs[dev_id].hcoded_td_id || R in DevAModesToObj(k, k_tds_state, dev_id, td_id2.oid);
        //// In the other hand
        assert DevAModesToObj(k, k_tds_state, dev_id, td_id2.oid) == {};
        Lemma_EmptyAModesIsNoRAndNoW(DevAModesToObj(k, k_tds_state, dev_id, td_id2.oid));
        assert R !in DevAModesToObj(k, k_tds_state, dev_id, td_id2.oid);

        assert td_id2 == k.subjects.devs[dev_id].hcoded_td_id;
        assert DoOwnObj(k, dev_id.sid, td_id2.oid);

        assert DoOwnObj(k', dev_id.sid, td_id2.oid);
        assert ObjPID(k', td_id2.oid) != NULL;
        assert td_id2 in AllActiveTDs(k');
        assert td_id2 in k'_tds_state;
    }
    assert forall td_id2 :: td_id2 in k_td_ids ==> td_id2 in k'_tds_state;

    assert forall td_id2 :: td_id2 in AllActiveTDs(k')
            ==> k'_tds_state[td_id2] == k_tds_state[td_id2];

    Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInK_ThenDevCanReadTDInNewK_Private(
        k, k', k_tds_state, k'_tds_state, k_td_ids, dev_id, td_id);
    assert CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id);
}

// Lemma: For the <CanActiveDevReadActiveTD> function, For each active devices 
// (<dev_id2>) and TDs (<td_id2>) in k', 
// CanActiveDevReadActiveTD(k', k'_tds_state, dev_id2, td_id2) == 
// CanActiveDevReadActiveTD(k, k_tds_state, dev_id2, td_id2)
// (needs 60s to verify)
lemma Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_ActiveDevsAndTDsInNewKHasSameResultWithTheOneForK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k_tds_state> contains additional active TDs (if 
        // any) from <k'_tds_state>

    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_tds_state, dev_id, td_id.oid) == {}
        // Requirment: No active device has transfer to the TDs to be 
        // deactivated

    ensures forall td_id2, dev_id2 :: dev_id2 in AllActiveDevs(k') && td_id2 in AllActiveTDs(k')
                ==>(CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2)
                        <==> CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id2))
        // Property: For SubjObjDeactivate operations, forall active devices and TDs in k', 
        // the result of CanActiveDevReadActiveTD is unchanged
{
    forall td_id2, dev_id2 | dev_id2 in AllActiveDevs(k') && td_id2 in AllActiveTDs(k')
        ensures CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2)
                        <==> CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id2)
    {
        if(CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2))
        {
            Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInNewK_ThenDevCanReadTDInK(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k_tds_state, k'_tds_state, dev_id2, td_id2);
        }

        if(CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id2))
        {
            Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInK_ThenDevCanReadTDInNewK(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k_tds_state, k'_tds_state, dev_id2, td_id2);
        }
    }
}

lemma Lemma_DevAModesToObj_SubjObjDeactivate_IfDevCanReadTDAndTDIncludesTransferToObj_ThenDevHasTransferToObj(
    k:State, k_params:ReachableTDsKParams, k_tds_state:TDs_Vals, k'_dev_id:Dev_ID, k'_td_id:TD_ID, o_id2:Object_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, k_tds_state, k'_dev_id, k'_td_id)

    requires k_params == KToKParams(k)

    requires CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id)
    requires o_id2 in GetObjIDsRefedInTD(k_tds_state, k'_td_id)
    requires GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, o_id2) != {}

    requires TD_ID(o_id2) in k_params.objs_td_ids || FD_ID(o_id2) in k_params.objs_fd_ids || DO_ID(o_id2) in k_params.objs_do_ids

    ensures DevAModesToObj(k, k_tds_state, k'_dev_id, o_id2) != {}
{
    AllReqAModesPermsSubsetOfRW();
    if(DevAModesToObj(k, k_tds_state, k'_dev_id, o_id2) == {})
    {
        assert !DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, k'_dev_id, o_id2);
        assert !DevAModesToObjFromTDs_ExistW_SlimState(k_params, k_tds_state, k'_dev_id, o_id2);

        assert R !in GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, o_id2);
        assert W !in GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, o_id2);

        // Show conflict
        assert GetAModesOfObjRefedInTD(k_tds_state, k'_td_id, o_id2) == {};
        assert false;
    }
}




//******** Private Lemmas Used By Lemmas of ReachableTDs' States ********//
// (needs 70s to verify)
lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Right(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, dev_id) 
    requires SubjPID_DevID(k, dev_id) != NULL
    requires SubjPID_DevID(k', dev_id) != NULL
        // Requirement: The device (<dev_id>) is an existing active device 
        // (i.e., not activating between k and k')

    requires TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_from_tds_state) == TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k')
    requires TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)

    requires forall td_id :: td_id in TDsStateGetTDIDs(k_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k_from_tds_state> contains additional active TDs (if 
        // any) from <k'_from_tds_state>
    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_from_tds_state, dev_id, td_id.oid) == {}
        // Requirment: No active device in k' has transfer to the TDs to be
        // deactivated
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)))
            ==>
            (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)))
{
    if (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)))
    {
        forall td_id, td_new_cfg | td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                                    td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
            ensures (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                        ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg))
        {
            assert td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) && 
                    td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id];

            assert MapGetKeys<TD_ID, TD_Val>(k'_from_tds_state) ==  AllActiveTDs(k');
            var k'_tdx_id :| k'_tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, k'_tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, k'_tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, k'_tdx_id, td_id, td_new_cfg); 

            var k_tdx_id := k'_tdx_id;
            assert k_from_tds_state[k_tdx_id] == k'_from_tds_state[k_tdx_id];

            Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_ActiveDevsAndTDsInNewKHasSameResultWithTheOneForK(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k_from_tds_state, k'_from_tds_state);
            assert k_tdx_id in TDsStateGetTDIDs(k_from_tds_state);
            assert ObjPID_SlimState(k_params.objs_pids, k_tdx_id.oid) != NULL;
            assert IsTDWriteInTD(k_from_tds_state, k_tdx_id, td_id, td_new_cfg);
        }
    }
}

// (needs 30s to verify)
lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingDeactivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Left(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, dev_id) 
    requires SubjPID_DevID(k, dev_id) != NULL
    requires SubjPID_DevID(k', dev_id) != NULL
        // Requirement: The device (<dev_id>) is an existing active device 
        // (i.e., not activating between k and k')

    requires TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_from_tds_state) == TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k')
    requires TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)

    requires forall td_id :: td_id in TDsStateGetTDIDs(k_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k_from_tds_state> contains additional active TDs (if 
        // any) from <k'_from_tds_state>
    requires forall td_id, dev_id :: td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs(k')
            ==> DevAModesToObj(k, k_from_tds_state, dev_id, td_id.oid) == {}
        // Requirment: No active device in k' has transfer to the TDs to be
        // deactivated
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)))
            <==
            (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)))
{
    assert MapGetKeys(k'_params.objs_pids) == AllObjsIDs(k'.objects);
    assert dev_id in AllActiveDevs(k');

    if (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)))
    {
        forall td_id, td_new_cfg | td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                                    td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
            ensures (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                        ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg))
        {
            assert td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) && 
                    td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id];

            assert MapGetKeys<TD_ID, TD_Val>(k_from_tds_state) ==  AllActiveTDs(k);
            var k_tdx_id :| k_tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, k_tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, k_tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, k_tdx_id, td_id, td_new_cfg); 

            var k'_tdx_id := k_tdx_id;
            assert k'_tdx_id in k.objects.tds;
            assert k'_tdx_id.oid in AllObjsIDs(k'.objects);

            // Prove k'_tdx_id !in todeactivate_td_ids
            if(k'_tdx_id in todeactivate_td_ids)
            {
                assert CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, k'_tdx_id);
                Lemma_CanActiveDevReadActiveTD_ThenTDIsHCodedTDOrDevAModesToObjHasRTransfer(
                    k, k_params, k_from_tds_state, dev_id, k'_tdx_id);
                assert k'_tdx_id == k.subjects.devs[dev_id].hcoded_td_id || R in DevAModesToObj(k, k_from_tds_state, dev_id, k'_tdx_id.oid);

                // Show conflicts
                assert DevAModesToObj(k, k_from_tds_state, dev_id, k'_tdx_id.oid) == {};
                Lemma_EmptyAModesIsNoRAndNoW(DevAModesToObj(k, k_from_tds_state, dev_id, k'_tdx_id.oid));
                assert R !in DevAModesToObj(k, k_from_tds_state, dev_id, k'_tdx_id.oid);

                assert k'_tdx_id == k.subjects.devs[dev_id].hcoded_td_id;
                assert DoOwnObj(k, dev_id.sid, k'_tdx_id.oid);
                assert DoOwnObj(k', dev_id.sid, k'_tdx_id.oid);

                assert dev_id.sid !in todeactivate_s_ids;
                if(k'_tdx_id in todeactivate_td_ids)
                {
                    assert SubjPID(k', dev_id.sid) != ObjPID(k', k'_tdx_id.oid);
                    assert false;
                }
                assert k'_tdx_id !in todeactivate_td_ids;
            }
            assert k'_tdx_id !in todeactivate_td_ids;

            assert k'_from_tds_state[k'_tdx_id] == k_from_tds_state[k'_tdx_id];

            Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_ActiveDevsAndTDsInNewKHasSameResultWithTheOneForK(
                k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, k_from_tds_state, k'_from_tds_state);
            assert k_tdx_id in TDsStateGetTDIDs(k'_from_tds_state);
            assert ObjPID_SlimState(k'_params.objs_pids, k'_tdx_id.oid) != NULL;
            assert IsTDWriteInTD(k'_from_tds_state, k'_tdx_id, td_id, td_new_cfg);
        }
    }
}




//******** Private Lemmas Used By Lemmas of CanActiveDevReadActiveTD and NoActiveDevHasTransferToObjsInReachableActiveTDsStates ********//
lemma Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInNewK_ThenDevCanReadTDInK_Private(
    k:State, k':State, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k'_td_ids:seq<TD_ID>,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
    requires AllActiveTDs(k') <= AllActiveTDs(k)

    requires dev_id in k.subjects.devs
    requires SubjPID_DevID(k, dev_id) != NULL

    requires |k'_td_ids| >= 1
    requires forall td_id2 :: td_id2 in k'_td_ids ==> td_id2 in k'_tds_state
    requires k'_td_ids[|k'_td_ids| - 1] == td_id
    requires k'_td_ids[0] == KToKParams(k).subjects.devs[dev_id].hcoded_td_id
    requires P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(k'_tds_state, k'_td_ids)

    ensures CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, dev_id, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_CanActiveDevReadActiveTD_SubjObjDeactivate_IfActiveDevCanReadTDInK_ThenDevCanReadTDInNewK_Private(
    k:State, k':State, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k_td_ids:seq<TD_ID>,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_PreConditionsOfK(k')

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k'_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
    requires AllActiveTDs(k') <= AllActiveTDs(k)

    requires dev_id in k.subjects.devs
    requires dev_id in AllActiveDevs(k')

    requires |k_td_ids| >= 1
    requires forall td_id2 :: td_id2 in k_td_ids ==> td_id2 in k'_tds_state
    requires k_td_ids[|k_td_ids| - 1] == td_id
    requires k_td_ids[0] == KToKParams(k').subjects.devs[dev_id].hcoded_td_id
    requires P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(k_tds_state, k_td_ids)

    ensures CanActiveDevReadActiveTD(KToKParams(k'), k'_tds_state, dev_id, td_id)
{
    assert P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(k'_tds_state, k_td_ids);

    assert |k_td_ids| >= 1;
    assert forall td_id2 :: td_id2 in k_td_ids ==> td_id2 in k'_tds_state;
    assert k_td_ids[|k_td_ids| - 1] == td_id;
    assert k_td_ids[0] == KToKParams(k').subjects.devs[dev_id].hcoded_td_id;
    assert forall i :: 0<=i<|k_td_ids| - 1 ==> k_td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[k_td_ids[i]]);
}