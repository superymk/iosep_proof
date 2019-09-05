include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "Lemmas.dfy"
include "./BuildCAS/ReachableTDsStates.dfy"

predicate SubjObjActivate_CommonPreConditionsOfKAndNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>
)
{
    (SubjObjActivate_PreConditionsOfK(k)) &&
    (SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')) &&
    (SubjObjActivate_SubjsObjsPIDsInNewK(k')) &&
    (SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)) &&
    (SubjObjActivate_CertainTDsToActivateMustBeCleared(k, k', toactivate_s_ids)) &&
    (SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)) &&
    (CanActiveDevReadActiveTD_KParams_PreConditions(k_params)) &&
    (SubjObjActivate_PreConditionsOfK(k')) &&

    (forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2) &&
        // Requirement: In k, no two subjects own the same object
    (forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)) &&
    (forall dev_id2, td_id2 :: IsDevID(k, dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(KToKParams(k).hcoded_tds, dev_id2)
                ==> td_id2 != k.subjects.devs[dev_id2].hcoded_td_id) &&
        // Requirement: In k, the hardcoded TD of each device does not ref 
        // itself
    // Requirement: Additional preconditions of k for the proof
    (k_params == KToKParams(k)) &&
    (k'_params == KToKParams(k')) &&
    (k'_params.hcoded_td_ids == k_params.hcoded_td_ids) &&
    (k'_params.hcoded_tds == k_params.hcoded_tds) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds
                        ==> td_id !in k_params.hcoded_td_ids)) &&
        // Requirement: Devices' hardcoded TDs do not reference any hardcoded TDs

    (forall dev_id:Dev_ID :: dev_id.sid in toactivate_s_ids && dev_id in k.subjects.devs
                ==> (dev_id in k'.subjects.devs &&
                    (forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                        ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R,W}))) &&
        // Requirement: Devices to be activated do not have hardcoded R and W to the 
        // same object
    (forall td_id:TD_ID, dev_id:Dev_ID :: dev_id in k.subjects.devs &&
                dev_id.sid in toactivate_s_ids && 
                td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
            ==> td_id in k'.objects.tds &&
                k'.objects.tds[td_id].val == TD_Val(map[], map[], map[])) &&
        // Requirement: In k'.objects.tds, TDs refed by hardcoded TDs with R are empty

    (true)
}

// (Needs 100s to verify)
lemma Lemma_SubjObjActivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, found_tds_states:set<TDs_Vals>, status:bool
)
    requires SubjObjActivate_CommonPreConditionsOfKAndNewK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids)

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
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    assert forall tds_state2 :: tds_state2 in found_tds_states
                ==> MapGetKeys<TD_ID, TD_Val>(tds_state2) == AllActiveTDs(k');

    forall tds_state2 | tds_state2 in found_tds_states
        ensures ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
    {
        assert ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                    AllActiveDevs(k'), ActiveTDsState(k'), tds_state2);

        if(ActiveTDsState(k') == tds_state2)
        {
            var k'_tds_states:seq<TDs_Vals> := [ActiveTDsState(k')];
            var k'_devs:seq<Dev_ID> := [];

            Lemma_SubjObjActivate_ReachableActiveTDsStatesInNewKHaveNoInvalidRefs(
                    k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states, k'_devs); 
        }
        else
        {
            var k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID> :| 
                    (|k'_tds_states| >= 2 && 
                        (forall tds_state2 :: tds_state2 in k'_tds_states 
                            ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
                        |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
                        k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
                        k'_tds_states[|k'_tds_states|-1] == tds_state2 &&
                        (forall i :: 0<=i<|k'_tds_states| - 1 
                            ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                                    k'_devs[i], k'_tds_states[i], k'_tds_states[i+1])));

            Lemma_SubjObjActivate_ReachableActiveTDsStatesInNewKHaveNoInvalidRefs(
                    k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states, k'_devs);
        }
    }
}

lemma Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, k'_td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall o_id  :: TD_ID(o_id) in k.objects.tds
                ==> o_id in AllObjsIDs(k.objects)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires AllActiveDevs(k') >= AllActiveDevs(k)

    requires k'_td_id in k_tds_state
    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') >= AllActiveTDs(k)

    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id)
        // Requirement: In <k_tds_state>, k'_td_id has no invalid transfers

    requires k'_tds_state[k'_td_id] == k_tds_state[k'_td_id]
    requires k'_td_id in AllActiveTDs(k)
    requires k'_td_id in AllActiveTDs(k')
 
    ensures DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k'_params)
    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id)
        // Property: In <k'_tds_state>, k'_td_id has no invalid transfers
{
    forall td_id2 | td_id2 in k'_tds_state[k'_td_id].trans_params_tds
        ensures td_id2 in k'_params.objs_td_ids
        ensures td_id2 !in k'_params.hcoded_td_ids
        ensures (ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, k'_td_id.oid) || 
                        // The TD (<k'_td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 k'_tds_state[k'_td_id].trans_params_tds[td_id2].amodes == {})
                        // The TD does not contain a transfer to the target TD
    {
        assert td_id2 in k_tds_state[k'_td_id].trans_params_tds;
    }
}

// (needs 80s to verify)
lemma Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires SubjObjActivate_CertainTDsToActivateMustBeCleared(k, k', toactivate_s_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    
    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds
                        ==> td_id !in k_params.hcoded_td_ids)
        // Requirement: Devices' hardcoded TDs do not reference any hardcoded TDs

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> o_id in AllObjsIDs(k'.objects) &&
                    SubjPID(k', s_id) == ObjPID(k', o_id)
        // Requirement: k' must fulfill IsValidState_SubjsOwnObjsThenInSamePartition

    requires forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
                ==> (td_id in k'_tds_state && td_id in k'.objects.tds &&
                     k'_tds_state[td_id] == k'.objects.tds[td_id].val)
    requires forall dev_id, td_id :: dev_id in AllActiveDevs(k') &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
                ==> td_id in k'_tds_state &&
                    k'_tds_state[td_id] == k'.objects.tds[td_id].val
        // Requriement: <k'_tds_state> includes hardcoded TDs of active devices,
        // and their values in <k'.objects.tds>

    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)
                ==> ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_tds_state)
{
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs);
    assert MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs);
    assert forall s_id :: s_id in AllSubjsIDs(k'.subjects)
                <==> (Drv_ID(s_id) in k'.subjects.drvs) || (Dev_ID(s_id) in k'.subjects.devs);

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
            if (k'_dev_id in AllActiveDevs(k))
            {
                // Prove <k'_dev_id> can read <k'_td_id> in <k_tds_state>
                Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating(
                    k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_tds_state, k'_tds_state);
                assert k'_td_id in AllActiveTDs(k);
                
                Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK(
                    k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_tds_state, k'_tds_state);
                assert CanActiveDevReadActiveTD(k_params, k_tds_state, k'_dev_id, k'_td_id);

                // Prove the postcondition of the forall statement
                assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state);
                assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, k'_td_id);

                assert k'_tds_state[k'_td_id] == k_tds_state[k'_td_id];
                Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIffValidBefore_ActiveTDsInKAndNewKHaveNoInvalidTransfersInBothActiveTDsStates(
                    k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_tds_state, k'_tds_state, k'_td_id);
 
                assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id);
            }
            else
            {
                // <k'_dev_id> is being activated
                assert k'_dev_id !in AllActiveDevs(k);

                assert SubjPID_DevID(k, k'_dev_id) == NULL;
                assert SubjPID_DevID(k', k'_dev_id) != NULL;
                assert forall td_id :: td_id in k.objects.tds &&
                            td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, k'_dev_id)
                        ==> IsTDClearVal(k'.objects.tds, td_id);

                assert forall td_id :: td_id in k.objects.tds &&
                            td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, k'_dev_id)
                        ==> (k'_tds_state[td_id].trans_params_tds == map[] &&
                            k'_tds_state[td_id].trans_params_fds == map[] &&
                            k'_tds_state[td_id].trans_params_dos == map[]);
                             
                Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD_PreConditions(
                    k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids);
                Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD(k', k'_tds_state, k'_dev_id, k'_td_id);
                assert k'_td_id == k'.subjects.devs[k'_dev_id].hcoded_td_id ||
                        k'_tds_state[k'_td_id] == TD_Val(map[], map[], map[]);


                if(k'_td_id == k'.subjects.devs[k'_dev_id].hcoded_td_id)
                {
                    Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore_HCodedTDOfDevToBeActivatedHasNoInvalidRefs(
                        k, k_params, k', k'_params, k'_tds_state, k'_dev_id, k'_td_id);
                }
                else
                {
                    assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id);
                }
            }
        }
    }
}

// Lemma: In k', device being activated do not modify any hardcoded TDs, or TDs
// refed by these TDs with R
lemma Lemma_SubjObjActivate_DevBeingActivatedDoNotModifyHCodedTDs_OrTDsRefedByTheseTDsWithR(
    k':State, k'_params:ReachableTDsKParams, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k'.subjects) && s_id2 in AllSubjsIDs(k'.subjects) && 
                DoOwnObj(k', s_id1, o_id) && DoOwnObj(k', s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: In k', no two subjects own the same object
    requires forall dev_id2, td_id2 :: IsDevID(k', dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(KToKParams(k').hcoded_tds, dev_id2)
                ==> td_id2 != k'.subjects.devs[dev_id2].hcoded_td_id
        // Requirement: In k', the hardcoded TD of each device does not ref 
        // itself

    requires k'_params == KToKParams(k')

    requires TDsStateGetTDIDs(from_tds_state) == TDsStateGetTDIDs(to_tds_state) == AllActiveTDs(k')
    requires dev_id in k'.subjects.devs
    requires SubjPID_DevID_SlimState(k'_params.subjects, dev_id) != NULL

    requires DevModifyTDsStateOnlyWithHCodedWToTDs(k'_params, dev_id, from_tds_state, to_tds_state)
    requires forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                    ==> td_id in IDToDev_SlimState(k'.subjects, dev_id).td_ids
    requires forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                    ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R,W}
        // Requirement: Activating devices do not have hardcoded R and W to the 
        // same object

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, from_tds_state, to_tds_state)
        // Requirement: from_tds_state --> to_tds_state
    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k')

    ensures forall td_id2, dev_id2:Dev_ID :: IsDevID(k', dev_id2) &&
                    SubjPID_DevID(k', dev_id2) != NULL &&
                    td_id2 == k'.subjects.devs[dev_id2].hcoded_td_id
                        // Forall hardcoded TD (<td_id2>) in any active devices
                ==> td_id2 in from_tds_state && td_id2 in to_tds_state && 
                    from_tds_state[td_id2] == to_tds_state[td_id2]
    ensures forall td_id2, dev_id2:Dev_ID :: IsDevID(k', dev_id2) &&
                    SubjPID_DevID(k', dev_id2) != NULL &&
                    td_id2 in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id2)
                        // Forall TDs (<td_id2>) refed by hardcoded TDs of any active device
                ==> td_id2 in from_tds_state && td_id2 in to_tds_state &&
                    from_tds_state[td_id2] == to_tds_state[td_id2]
                        // Values of these TDs are not changed
{
    AllReqAModesPermsSubsetOfRW();
    assert k'_params.all_active_tds == AllActiveTDs(k');

    // Prove property 1
    forall td_id2, dev_id2:Dev_ID | IsDevID(k', dev_id2) &&
                    SubjPID_DevID(k', dev_id2) != NULL &&
                    td_id2 == k'.subjects.devs[dev_id2].hcoded_td_id
        ensures from_tds_state[td_id2] == to_tds_state[td_id2]
    {
        assert DoOwnObj(k', dev_id2.sid, td_id2.oid);
        if(from_tds_state[td_id2] != to_tds_state[td_id2])
        {
            var td_new_cfg := TDsStateDiff(to_tds_state, from_tds_state)[td_id2];

            assert TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id),
                        td_id2, td_new_cfg);
            // Prove dev_id == dev_id2
            assert DoOwnObj(k', dev_id.sid, td_id2.oid);
            assert dev_id == dev_id2;

            // Show conflict
            assert td_id2 in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id);
            assert td_id2 != k'.subjects.devs[dev_id].hcoded_td_id;
        }
    }

    // Prove property 2
    forall td_id2, dev_id2:Dev_ID | IsDevID(k', dev_id2) &&
                    SubjPID_DevID(k', dev_id2) != NULL &&
                    td_id2 in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id2)
                        // Forall TDs (<td_id2>) refed by hardcoded TDs of any active device
        ensures from_tds_state[td_id2] == to_tds_state[td_id2]
    {
        assert DoOwnObj(k', dev_id2.sid, td_id2.oid);
        assert R in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id2)[td_id2].amodes;

        if(from_tds_state[td_id2] != to_tds_state[td_id2])
        {
            var td_new_cfg := TDsStateDiff(to_tds_state, from_tds_state)[td_id2];

            assert TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id),
                        td_id2, td_new_cfg);

            // Prove dev_id == dev_id2
            assert DoOwnObj(k', dev_id.sid, td_id2.oid);
            assert dev_id == dev_id2;

            // Show conflict
            assert W in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id2].amodes;

            assert dev_id == dev_id2;
            assert R in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id2)[td_id2].amodes;
            assert GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id2].amodes == {R, W};

            // Show conflict
            assert forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R, W};
        }
    }
}

predicate SubjObjActivate_PreConditionsOfK(k:State)
{
    K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos)) &&

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

predicate SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k:State, k':State)
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

predicate SubjObjActivate_SubjsObjsPIDsInNewK(k':State)
    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
{
    (forall dev_id :: dev_id in k'.subjects.devs
        ==> (forall td_id :: td_id in IDToDev(k', dev_id).td_ids
                ==> ObjPID(k', td_id.oid) == SubjPID(k', dev_id.sid)) &&
            (forall fd_id :: fd_id in IDToDev(k', dev_id).fd_ids
                ==> ObjPID(k', fd_id.oid) == SubjPID(k', dev_id.sid)) &&
            (forall do_id :: do_id in IDToDev(k', dev_id).do_ids
                ==> ObjPID(k', do_id.oid) == SubjPID(k', dev_id.sid))) &&
        // Requirement: In k', a device must be in the same partition with its 
        // objects

    (forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> SubjPID(k', s_id) == ObjPID(k', o_id)) &&
        // Requirement: k' must fulfill IsValidState_SubjsOwnObjsThenInSamePartition

    (true)
}

predicate SubjObjActivate_PreConditionsOfSubjObjToActivate(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
{
    (toactivate_s_ids <= AllSubjsIDs(k.subjects)) &&
    (forall s_id :: s_id in toactivate_s_ids 
                ==> IsSubjID(k.subjects, s_id)) &&

    (forall s_id :: s_id in toactivate_s_ids 
                ==> OwnedTDs(k, s_id) <= toactivate_td_ids) &&
        // Requirement: Subjects to be activated have their TDs in <toactivate_td_ids>
    (toactivate_td_ids <= MapGetKeys(k.objects.tds)) &&
        // Requirement: TDs in <toactivate_td_ids> exist in the system
    (forall td_id :: td_id in toactivate_td_ids
                ==> td_id.oid in AllObjsIDs(k.objects)) &&
    (AllActiveTDs(k') == AllActiveTDs(k) + toactivate_td_ids) &&
    (AllActiveTDs(k) * toactivate_td_ids == {}) &&
    (forall td_id :: td_id in k.objects.tds && td_id !in toactivate_td_ids
                ==> k'.objects.tds[td_id] == k.objects.tds[td_id]) &&
        // Requirement: All TDs except the TDs to be activated preserve their 
        // states (i.e., pids and values) between k and k'
    (forall dev_id2:Dev_ID :: IsDevID(k, dev_id2) && 
                    dev_id2.sid !in toactivate_s_ids
                ==> k'.subjects.devs[dev_id2] == k.subjects.devs[dev_id2]) &&
    (forall drv_id2:Drv_ID :: IsDrvID(k, drv_id2) &&
                    drv_id2.sid !in toactivate_s_ids
                ==> k'.subjects.drvs[drv_id2] == k.subjects.drvs[drv_id2]) &&
        // Requirement: Forall devices and drivers not being activated in the 
        // operation, their states are unchanged
    (forall s_id :: s_id in toactivate_s_ids
                ==> SubjPID(k, s_id) == NULL && SubjPID(k', s_id) != NULL) &&
        // Requirement: If a subject is in <toactivate_s_ids>, then the subject
        // is being activated
    (forall td_id :: td_id in toactivate_td_ids
                ==> ObjPID(k, td_id.oid) == NULL && ObjPID(k', td_id.oid) != NULL) &&
        // Requirement: If a TD is in <toactivate_td_ids>, then the TD
        // is being activated
    (AllActiveDevs(k') >= AllActiveDevs(k))&&
    (forall td_id2 :: td_id2 in AllActiveTDs(k)
                ==> ObjPID(k, td_id2.oid) != NULL) &&

    (forall fd_id :: fd_id in AllActiveFDs(k)
                ==> k'.objects.fds[fd_id] == k.objects.fds[fd_id]) &&
    (forall do_id :: do_id in AllActiveDOs(k)
                ==> k'.objects.dos[do_id] == k.objects.dos[do_id]) &&
        // Requirement: Existing active FDs and DOs are unmodified

    (true)
}

predicate SubjObjActivate_CertainTDsToActivateMustBeCleared(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
{
    (forall dev_id2:Dev_ID, td_id2 :: IsDevID(k, dev_id2) && 
                    dev_id2.sid in toactivate_s_ids &&
                    td_id2 in TDsRefedByDevHCodedTDWithR(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id2)
                ==> td_id2 in k'.objects.tds &&
                    IsTDClearVal(k'.objects.tds, td_id2)) &&
        // Requirement: If a device is being activated, then all TDs refed by 
        // its hardcoded TD with R must be cleared
    
    (true)
}

predicate SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k:State)
    requires SubjObjActivate_PreConditionsOfK(k)
{
    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k) &&
                    (ActiveTDsState(k) == tds_state2 ||
                    IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k), 
                        AllActiveDevs(k), ActiveTDsState(k), tds_state2))
                                                // ActiveTDsState(k) -->* tds_state2
                ==> tds_state2 in AllReachableActiveTDsStates(k))&&
        // Requirement: k fulfills Condition 5.3 of <IsValidState_ReachableTDsStates>
    (ActiveTDsState(k) in AllReachableActiveTDsStates(k))&&
        // Requirement: k fulfills Condition 5.6 of <IsValidState_ReachableTDsStates>
    (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
        ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)) &&
        // Requirement: k fulfills Condition 5.5 of <IsValidState_ReachableTDsStates>

    (true)
}

predicate P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
    k':State, toactivate_s_ids:set<Subject_ID>, k'_tds_states:seq<TDs_Vals>
)
    requires SubjObjActivate_PreConditionsOfK(k')
{
    forall tds_state2 :: tds_state2 in k'_tds_states
        ==> P_HCodedTDsOfActiveDevsAreUnmodified(k', tds_state2)
}

predicate P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
    k':State, k'_params:ReachableTDsKParams, toactivate_s_ids:set<Subject_ID>, k'_tds_states:seq<TDs_Vals>
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires k'_params == KToKParams(k')
    requires |k'_tds_states| > 0
{
    forall tds_state2, td_id, dev_id:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    tds_state2 in k'_tds_states &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
                ==> (td_id in tds_state2 && td_id in k'.objects.tds &&
                     tds_state2[td_id] == k'.objects.tds[td_id].val)
        // For any tds_state2 in k'_tds_states, 
        // hardcoded TDs of devices to be activated, and TDs refed by these TDs 
        // with R have constant configurations
}

// Lemma: If ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1], then
// ActiveTDsState(k) -->* k_tds_states[|k_tds_states|-1]
// (needs 200s to verify)
lemma Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjActivate_PreConditionsOfK(k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: In k, no two subjects own the same object
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall dev_id2, td_id2 :: IsDevID(k, dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(KToKParams(k).hcoded_tds, dev_id2)
                ==> td_id2 != k.subjects.devs[dev_id2].hcoded_td_id
        // Requirement: In k, the hardcoded TD of each device does not ref 
        // itself
    // Requirement: Additional preconditions of k for the proof
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in k'
    requires forall dev_id:Dev_ID :: dev_id.sid in toactivate_s_ids && dev_id in k.subjects.devs
                ==> (dev_id in k'.subjects.devs &&
                    (forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                        ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R,W}))
        // Requirement: Activating devices do not have hardcoded R and W to the 
        // same object
    requires k'_tds_states[0] == ActiveTDsState(k')  
        // First TDs' state is the <ActiveTDsState(k')>
    requires (|k'_tds_states| == 1 && ActiveTDsState(k') == k'_tds_states[|k'_tds_states|-1]) ||
                    // k'_tds_states == [ActiveTDsState(k')], Or
             (|k'_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k'_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
                |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
                k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|k'_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                            k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                            k'_devs[i], k'_tds_states[i], k'_tds_states[i+1])))
                    // ActiveTDsState(k') -->1+ k'_tds_states[|k'_tds_states| - 1]
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]
    requires forall td_id:TD_ID, dev_id:Dev_ID :: dev_id in k.subjects.devs &&
                dev_id.sid in toactivate_s_ids && 
                td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
            ==> td_id in k'.objects.tds &&
                k'.objects.tds[td_id].val == TD_Val(map[], map[], map[])
        // Requirement: In k'.objects.tds, TDs refed by hardcoded TDs with R are empty

    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states)
    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states)
        // Property 2: For any tds_state2 in k'_tds_states, hardcoded TDs of 
        // devices to be activated, and TDs refed by these TDs with R have 
        // constant configurations
        // [NOTE] We prove this property here because otherwise there is circular dependency
        // between Lemma_SubjObjActivate_ActivatingRootTDsAreNotModifiedInAllReachableStatesInNewK 
        // and Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK
    ensures (ActiveTDsState(k) == MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], toactivate_td_ids)) ||
            (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), 
                    MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], toactivate_td_ids)) &&
             IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), 
                    MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], toactivate_td_ids)))
        // Property: ActiveTDsState(k) -->* k_tds_states[|k_tds_states|-1] (
        // k_tds_states[|k_tds_states|-1] == Remove activating TDs from k'_tds_states[|k'_tds_states|-1])

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

    if(|k'_tds_states| == 1)
    {
        var k'_from_tds_state := k'_tds_states[0];
        var k_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids);

        assert k'_from_tds_state == ActiveTDsState(k');
        assert k_from_tds_state == ActiveTDsState(k);

        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_OneStateSummary(
            k', k'_params, toactivate_s_ids, k'_tds_states);
    }
    else if(|k'_tds_states| == 2)
    {
        var k'_from_tds_state := k'_tds_states[0];
        var k'_to_tds_state :=  k'_tds_states[1];
        var k'_dev := k'_devs[0];
        var k_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids);
        var k_to_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_to_tds_state, toactivate_td_ids);

        assert k'_from_tds_state == ActiveTDsState(k');
        assert k_from_tds_state == ActiveTDsState(k);
        assert TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state);

        if(SubjPID_DevID(k, k'_dev) != NULL)
        {
            assert k_from_tds_state in AllReachableActiveTDsStates(k);
            Lemma_SubjObjActivate_ExistingActiveDevDoNotModify_TDsBeingActivated_IncludingTDsRefedByHCodedTDsWithROfDevsBeingActivated(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, 
                k'_from_tds_state, k'_to_tds_state, k'_dev);
            assert forall td_id :: td_id in toactivate_td_ids
                ==> k'_to_tds_state[td_id] == k'_from_tds_state[td_id];

            Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyHCodedTDsOfActiveDevsInNewK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, 
                k'_from_tds_state, k'_to_tds_state, k'_dev);

            // Prove TDsStateDiff(k'_to_tds_state, k'_from_tds_state) == TDsStateDiff(k_to_tds_state, k_from_tds_state)
            var add_tds := MapSubmap(k'_from_tds_state, toactivate_td_ids);
            Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
                k_from_tds_state, k_to_tds_state, add_tds, k'_from_tds_state, k'_to_tds_state);

            // Prove k_from_tds_state --> k_to_tds_state
            assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);
            Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_dev,
                k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);
            assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                    k'_dev, k_from_tds_state, k_to_tds_state);

            // Prove k_from_tds_state in AllReachableActiveTDsStates(k)
            Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params,
                    k'_dev, AllActiveDevs(k), k_from_tds_state, k_to_tds_state);

            // Prove property 2
            Lemma_SubjObjActivate_ExistingActiveDevDoNotModify_TDsBeingActivated_IncludingTDsRefedByHCodedTDsWithROfDevsBeingActivated(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_from_tds_state, k'_to_tds_state, k'_dev);

            Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_ExistingActiveDevSummary(
                k', k'_params, toactivate_s_ids, k'_tds_states,
                k'_from_tds_state, k'_to_tds_state);
        }
        else
        {
            assert SubjPID_DevID(k, k'_dev) == NULL;
            assert k'_dev.sid in toactivate_s_ids;

            // Prove property 2
            Lemma_SameObjsOwnershipInSuccessiveStates(k, k'); 
            Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_DevsToActivateOnlyModifyTDsWithHCodedW(
                    k', k'_dev, k'_from_tds_state, k'_to_tds_state);
            assert DevModifyTDsStateOnlyWithHCodedWToTDs(k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);

            Lemma_SubjObjActivate_DevBeingActivatedDoNotModifyHCodedTDs_OrTDsRefedByTheseTDsWithR(
                k', k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);

            // Prove k_from_tds_state == k_to_tds_state
            Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_DevsToActivateOnlyModifyTDsWithHCodedW(
                    k', k'_dev, k'_from_tds_state, k'_to_tds_state);
            assert DevModifyTDsStateOnlyWithHCodedWToTDs(k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);
            Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_UnOwnedTDsAreNotChanged(k', k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);
            assert forall td_id :: td_id in k'_from_tds_state &&
                        td_id !in toactivate_td_ids
                    ==> k'_to_tds_state[td_id] == k'_from_tds_state[td_id];
            Lemma_IfTDsStatesAreDifferentOnlyForAddedTDs_ThenReducedTDsStatesAreSame(
                toactivate_td_ids, k'_from_tds_state, k'_to_tds_state, k_from_tds_state, k_to_tds_state);
            assert k_from_tds_state == k_to_tds_state;

            Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_OneStateSummary(
                k', k'_params, toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1]);
            Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_DevToActivateSummary(
                k', k'_params, toactivate_s_ids, k'_tds_states,
                k'_from_tds_state, k'_to_tds_state);
        }
    }
    else
    {
        assert |k'_devs| >=2;
        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states[..|k'_tds_states|-1], k'_devs[..|k'_devs|-1]);

        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_Private(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states, k'_devs);
    }
}

// Lemma: Forall TDs states in <k'_tds_states>, no active TDs that can be read
// be an active device have no invalid refs
// (needs 240s to verify)
lemma Lemma_SubjObjActivate_ReachableActiveTDsStatesInNewKHaveNoInvalidRefs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>
)
    requires SubjObjActivate_CommonPreConditionsOfKAndNewK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids)

    requires |k'_devs| == |k'_tds_states| - 1
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in k'

    requires k'_tds_states[0] == ActiveTDsState(k')  
        // First TDs' state is the <ActiveTDsState(k')>
    requires (|k'_tds_states| == 1 && ActiveTDsState(k') == k'_tds_states[|k'_tds_states|-1]) ||
                    // k'_tds_states == [ActiveTDsState(k')], Or
             (|k'_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k'_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
                |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
                k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|k'_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, k'_devs[i], k'_tds_states[i], k'_tds_states[i+1])))
                    // ActiveTDsState(k') -->1+ k'_tds_states[|k'_tds_states| - 1]
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]

    ensures forall tds_state2 :: tds_state2 in k'_tds_states
                ==> ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
        // Property: Any active TDs' state (active TDs of k') reachable from 
        // ActiveTDsState(k') and intermediate TDs' states have no invalid refs
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

    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');
    if(|k'_tds_states| == 1)
    {
        var k'_from_tds_state := k'_tds_states[0];
        var k_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids);
        assert k'_from_tds_state == ActiveTDsState(k');
        assert k_from_tds_state == ActiveTDsState(k);

        // Prove TDs in k'_from_tds_state has no invalid refs
        assert ActiveTDsState(k) in AllReachableActiveTDsStates(k);
        Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
    }
    else if(|k'_tds_states| == 2)
    {
        var k'_from_tds_state := k'_tds_states[0];
        var k'_to_tds_state :=  k'_tds_states[1];
        var k'_dev := k'_devs[0];
        var k_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids);
        var k_to_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_to_tds_state, toactivate_td_ids);

        assert k'_from_tds_state == ActiveTDsState(k');
        assert k_from_tds_state == ActiveTDsState(k);

        // Prove the activating root TDs have constant configurations
        //Lemma_SubjObjActivate_ActivatingRootTDsAreNotModifiedInAllReachableStatesInNewK(
        //    k, k', toactivate_s_ids, toactivate_td_ids, k'_tds_states, k'_devs);

        // Prove k_from_tds_state -->* k_to_tds_state
        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states, k'_devs);

        // Prove TDs in k'_from_tds_state has no invalid refs
        assert ActiveTDsState(k) in AllReachableActiveTDsStates(k);
        Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);

        // Prove TDs in k'_to_tds_state has no invalid refs
        assert (ActiveTDsState(k) == k_to_tds_state) ||
                IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), k_to_tds_state);
        Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_to_tds_state, k'_to_tds_state);
        assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_to_tds_state);

        // Summarize
        Lemma_SequenceHighlightLastElem(k'_tds_states);
        forall tds_state2 | tds_state2 in k'_tds_states
            ensures ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
        {
            assert tds_state2 in k'_tds_states[..|k'_tds_states|-1] || tds_state2 == k'_to_tds_state;
            if(tds_state2 == k'_to_tds_state)
            {
                assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2);
            }
            else
            {
                assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2);
            }
        }
    }
    else
    {
        assert |k'_tds_states| > 2;
        Lemma_SubjObjActivate_ReachableActiveTDsStatesInNewKHaveNoInvalidRefs(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states[..|k'_tds_states|-1], k'_devs[..|k'_devs|-1]);

        var k'_last_from_tds_state := k'_tds_states[|k'_tds_states|-2];
        var k'_last_to_tds_state := k'_tds_states[|k'_tds_states|-1];
        var k'_last_dev := k'_devs[|k'_devs|-1];
        var k_last_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_last_from_tds_state, toactivate_td_ids);
        var k_last_to_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_last_to_tds_state, toactivate_td_ids);

        // Prove k_last_from_tds_state -->* k_last_to_tds_state
        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_tds_states, k'_devs);

        // Prove TDs in k'_last_from_tds_state has no invalid refs
        assert ActiveTDsState(k) in AllReachableActiveTDsStates(k);
        Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_last_from_tds_state, k'_last_from_tds_state);

        // Prove TDs in k'_last_to_tds_state has no invalid refs
        assert (ActiveTDsState(k) == k_last_to_tds_state) ||
                IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), k_last_to_tds_state);
        Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_last_to_tds_state, k'_last_to_tds_state);
        assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_last_to_tds_state);

        // Summarize
        Lemma_SequenceHighlightLastElem(k'_tds_states);
        forall tds_state2 | tds_state2 in k'_tds_states
            ensures ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2)
        {
            assert tds_state2 in k'_tds_states[..|k'_tds_states|-1] || tds_state2 == k'_last_to_tds_state;
            if(tds_state2 == k'_last_to_tds_state)
            {
                assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2);
            }
            else
            {
                assert ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), tds_state2);
            }
        }
    }
}




//******** Private Lemmas ********//
lemma Lemma_SubjObjActivate_RemoveActivatingTDsFromAnActiveTDsStateInNewKIsAnActiveTDsStateInK(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>,toactivate_td_ids:set<TD_ID>, k'_tds_state:TDs_Vals, k_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)

    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires k_tds_state == MapRemoveKeys<TD_ID, TD_Val>(k'_tds_state, toactivate_td_ids);

    ensures TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_IfNoWTransferInTD_ThenTDsValsCannotBeModifiedDueToDevReadTheTD(
    k:State, k_dev:Dev_ID, k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, tdx_id:TD_ID, dest_td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
        // Requirements required by functions in this function method
    requires MapGetKeys<TD_ID, TD_Val>(k_from_tds_state) == AllActiveTDs(k)
    requires MapGetKeys<TD_ID, TD_Val>(k_to_tds_state) == AllActiveTDs(k)

    requires tdx_id in k_from_tds_state
    requires IsDevID_SlimState(k.subjects, k_dev)
    requires SubjPID_DevID_SlimState(k.subjects, k_dev) != NULL
    requires ObjPID(k, tdx_id.oid) != NULL
        // Requirement: The device and the TD are active

    requires dest_td_id !in k_from_tds_state[tdx_id].trans_params_tds ||
            k_from_tds_state[tdx_id].trans_params_tds[dest_td_id].amodes == {}
        // Requirement: No transfers to <dest_td_id> in <tdx_id>

    ensures !(k_dev in AllActiveDevs(k) &&
                    tdx_id in AllActiveTDs(k) &&
                    CanActiveDevReadActiveTD(KToKParams(k), k_from_tds_state, k_dev, tdx_id) &&
                    dest_td_id in k_from_tds_state[tdx_id].trans_params_tds &&
                    W in k_from_tds_state[tdx_id].trans_params_tds[dest_td_id].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    k_to_tds_state[dest_td_id] in k_from_tds_state[tdx_id].trans_params_tds[dest_td_id].vals)
        // Property: k_from_tds_state --> k_to_tds_state due to k_dev and tdx_id
{
    // Dafny can automatically prove this lemma
}

predicate P_ForHCodedTDsOfDevsToBeActivated_TDsRefedByTheseTDsWithRAreUnmodified(
    k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, 
    k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires k'_params == KToKParams(k')
{
    forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
                ==> td_id in k'_to_tds_state && td_id in k'_from_tds_state &&
                    k'_to_tds_state[td_id] == k'_from_tds_state[td_id]
        // Property: Forall hardcoded TDs of devices being activated, any TDs 
        // refed by these TDs with R are unchanged between k'_from_tds_state 
        // and k'_to_tds_state
}

predicate P_ForDevsToBeActivated_TheirHCodedTDsAreUnmodified(
    k':State,
    toactivate_s_ids:set<Subject_ID>, 
    k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k')
{
     forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
                ==> (td_id in k'_to_tds_state && td_id in k'_from_tds_state &&
                     k'_to_tds_state[td_id] == k'_from_tds_state[td_id])
        // Property: Forall devices being activated, the values of their  
        // hardcoded TDs are not modified
}

// (needs 100s to verify)
lemma Lemma_SubjObjActivate_ExistingActiveDevDoNotModify_TDsBeingActivated_IncludingTDsRefedByHCodedTDsWithROfDevsBeingActivated(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, 
    k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals, k'_dev:Dev_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjActivate_PreConditionsOfK(k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
        // Requirement: Additional preconditions of k for the proof
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, k'_dev) 
    requires SubjPID_DevID(k, k'_dev) != NULL && SubjPID_DevID(k', k'_dev) != NULL;
        // Requirement: k'_dev is active in both k and k'
    requires TDsStateGetTDIDs(k'_from_tds_state) == AllActiveTDs(k');
    requires TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k');
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                k'_dev, k'_from_tds_state, k'_to_tds_state)

    requires MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids) in AllReachableActiveTDsStates(k)
        // Requirement: ActiveTDsState(k) -->* k_from_tds_state

    ensures forall dev_id2:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id2) && 
                    dev_id2.sid in toactivate_s_ids
                ==> IDToDev_SlimState(k'.subjects, dev_id2).td_ids <= AllActiveTDs(k')
        // Properties needed by the property below
    ensures forall td_id :: td_id in toactivate_td_ids
                ==> k'_to_tds_state[td_id] == k'_from_tds_state[td_id]
        // Property 2: Existing active devices do not modifiy any TDs being 
        // activated
    ensures forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
                ==> td_id in k'_to_tds_state &&
                    k'_to_tds_state[td_id] == k'_from_tds_state[td_id]
    ensures P_ForHCodedTDsOfDevsToBeActivated_TDsRefedByTheseTDsWithRAreUnmodified(
                k', k'_params, toactivate_s_ids, k'_from_tds_state, k'_to_tds_state)
        // Property 3: Forall hardcoded TDs of devices being activated, any TDs 
        // refed by these TDs with R are unchanged between k'_from_tds_state 
        // and k'_to_tds_state
{
    // Prove the property needed by other properties
    assert forall dev_id2:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id2) && 
                    dev_id2.sid in toactivate_s_ids
                ==> IDToDev_SlimState(k'.subjects, dev_id2).td_ids <= AllActiveTDs(k');

    // Prove property 2
    Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyAnyTDsBeingActivated(
        k, k_params, k', k'_params,
        toactivate_s_ids, toactivate_td_ids, 
        k'_from_tds_state, k'_to_tds_state, k'_dev);

    // Prove property 3
    assert forall s_id :: s_id in toactivate_s_ids 
                ==> OwnedTDs(k', s_id) == OwnedTDs(k, s_id);
    Lemma_SubjObjActivate_ForDevBeingActivated_TDsRefedByHCodedTDWithRMustAlsoBeingActivated(
        k', k'_params, toactivate_s_ids, toactivate_td_ids);
    assert forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
                ==> td_id in k'_to_tds_state &&
                    k'_to_tds_state[td_id] == k'_from_tds_state[td_id];
}

predicate P_ForDevsToBeActivated_HCodedTDsOfActiveDevsInNewKAreUnmodified(
    k':State,
    toactivate_s_ids:set<Subject_ID>, 
    k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k')
{
     forall td_id, dev_id:Dev_ID :: 
                    dev_id in AllActiveDevs(k') &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
                ==> (td_id in k'_to_tds_state && td_id in k'_from_tds_state &&
                     k'_to_tds_state[td_id] == k'_from_tds_state[td_id])
        // Property: Hardcoded TDs of all devices active in k' are not modified
}

lemma Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyHCodedTDsOfActiveDevsInNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, 
    k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals, k'_dev:Dev_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjActivate_PreConditionsOfK(k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
        // Requirement: Additional preconditions of k for the proof
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, k'_dev) 
    requires SubjPID_DevID(k, k'_dev) != NULL && SubjPID_DevID(k', k'_dev) != NULL;
        // Requirement: k'_dev is active in both k and k'
    requires TDsStateGetTDIDs(k'_from_tds_state) == AllActiveTDs(k');
    requires TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k');
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                k'_dev, k'_from_tds_state, k'_to_tds_state)

    requires MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids) in AllReachableActiveTDsStates(k)
        // Requirement: ActiveTDsState(k) -->* k_from_tds_state

    ensures P_ForDevsToBeActivated_HCodedTDsOfActiveDevsInNewKAreUnmodified(
                k', toactivate_s_ids, k'_from_tds_state, k'_to_tds_state)
        // Property: Hardcoded TDs of all devices active in k' are not modified
{
    var k_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids);

    assert k'_params.all_active_tds == AllActiveTDs(k');
    forall td_id, dev_id | dev_id in AllActiveDevs(k') &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
        ensures td_id in k'_to_tds_state
        ensures td_id in k'_from_tds_state
        ensures k'_to_tds_state[td_id] == k'_from_tds_state[td_id]
    {
        assert td_id in k'.subjects.devs[dev_id].td_ids;
        assert DoOwnObj(k', dev_id.sid, td_id.oid);

        assert td_id in AllActiveTDs(k');

        if(k'_to_tds_state[td_id] != k'_from_tds_state[td_id])
        {
            Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
                k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);
            var tdx_id :|
                (k'_dev in AllActiveDevs(k') &&
                    tdx_id in AllActiveTDs(k') &&
                    CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, k'_dev, tdx_id) &&
                    td_id in k'_from_tds_state[tdx_id].trans_params_tds &&
                    W in k'_from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    k'_to_tds_state[td_id] in k'_from_tds_state[tdx_id].trans_params_tds[td_id].vals);
                        // The TD specifies the new value to be written

            assert k_from_tds_state in AllReachableActiveTDsStates(k);
            assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state);

            // Prove CanActiveDevReadActiveTD(k, k'_dev, tdx_id)
            Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
            Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
            assert CanActiveDevReadActiveTD(k_params, k_from_tds_state, k'_dev, tdx_id);

            // Prove tdx_id does not contain transfers to td_id, in k_from_tds_state
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_from_tds_state, tdx_id);
            assert td_id !in k_from_tds_state[tdx_id].trans_params_tds ||
                    k_from_tds_state[tdx_id].trans_params_tds[td_id].amodes == {};
            assert td_id !in k'_from_tds_state[tdx_id].trans_params_tds ||
                    k'_from_tds_state[tdx_id].trans_params_tds[td_id].amodes == {};

            assert ObjPID(k', tdx_id.oid) != NULL;
            Lemma_SubjObjActivate_IfNoWTransferInTD_ThenTDsValsCannotBeModifiedDueToDevReadTheTD(
                k', k'_dev, k'_from_tds_state, k'_to_tds_state, tdx_id, td_id);

            assert false;
        }
    }
}

// (needs 160s to verify)
lemma Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_Private(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k'_tds_states:seq<TDs_Vals>, k'_devs:seq<Dev_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjActivate_PreConditionsOfK(k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: In k, no two subjects own the same object
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall dev_id2, td_id2 :: IsDevID(k, dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(KToKParams(k).hcoded_tds, dev_id2)
                ==> td_id2 != k.subjects.devs[dev_id2].hcoded_td_id
        // Requirement: In k, the hardcoded TD of each device does not ref 
        // itself
    // Requirement: Additional preconditions of k for the proof
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires |k'_devs| == |k'_tds_states| - 1 
    requires forall dev_id :: dev_id in k'_devs
                ==> (IsDevID_SlimState(k'.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k'.subjects, dev_id) != NULL)
        // Requirement: Devices in <k'_devs> are active in k'
    requires forall dev_id:Dev_ID :: dev_id.sid in toactivate_s_ids && dev_id in k.subjects.devs
                ==> (dev_id in k'.subjects.devs &&
                    (forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                        ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R,W}))
        // Requirement: Activating devices do not have hardcoded R and W to the 
        // same object
    requires k'_tds_states[0] == ActiveTDsState(k')  
        // First TDs' state is the <ActiveTDsState(k')>
    requires |k'_tds_states| > 2 && 
                (forall tds_state2 :: tds_state2 in k'_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
                |k'_devs| == |k'_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in AllActiveDevs(k')) &&
                k'_tds_states[0] == ActiveTDsState(k') && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|k'_tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                            k'_devs[i], k'_tds_states[i], k'_tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                            k'_devs[i], k'_tds_states[i], k'_tds_states[i+1])))
                    // ActiveTDsState(k') -->1+ k'_tds_states[|k'_tds_states| - 1]
        // Requirement: ActiveTDsState(k') -->* k'_tds_states[|k'_tds_states| - 1]
    requires forall td_id:TD_ID, dev_id:Dev_ID :: dev_id in k.subjects.devs &&
                dev_id.sid in toactivate_s_ids && 
                td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
            ==> td_id in k'.objects.tds &&
                k'.objects.tds[td_id].val == TD_Val(map[], map[], map[])
        // Property: In k'.objects.tds, TDs refed by hardcoded TDs with R are empty

    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])
    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])
        // Property 2: For any tds_state2 in k'_tds_states[..|k'_tds_states|-1], 
        // hardcoded TDs of devices to be activated, and TDs refed by these TDs 
        // with R have constant configurations
        // [NOTE] We prove this property here because otherwise there is circular dependency
        // between Lemma_SubjObjActivate_ActivatingRootTDsAreNotModifiedInAllReachableStatesInNewK 
        // and Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK
    requires (ActiveTDsState(k) == MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], toactivate_td_ids)) ||
            (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), 
                    MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], toactivate_td_ids)) && 
             IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), 
                    MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-2], toactivate_td_ids)))
        // Property: ActiveTDsState(k) -->* k_tds_states[|k_tds_states|-1] (
        // k_tds_states[|k_tds_states|-1] == Remove activating TDs from k'_tds_states[|k'_tds_states|-2])
        // Properties of Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK(
        // k, k', toactivate_s_ids, toactivate_td_ids, k'_tds_states[..|k'_tds_states|-2], k'_devs[..|k'_devs|-2]);

    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states)
    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states)
        // Property 2: For any tds_state2 in k'_tds_states, hardcoded TDs of 
        // devices to be activated, and TDs refed by these TDs with R have 
        // constant configurations
        // [NOTE] We prove this property here because otherwise there is circular dependency
        // between Lemma_SubjObjActivate_ActivatingRootTDsAreNotModifiedInAllReachableStatesInNewK 
        // and Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK
    ensures (ActiveTDsState(k) == MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], toactivate_td_ids)) ||
            (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), 
                    MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], toactivate_td_ids)) &&
             IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    AllActiveDevs(k), ActiveTDsState(k), 
                    MapRemoveKeys<TD_ID, TD_Val>(k'_tds_states[|k'_tds_states|-1], toactivate_td_ids)))
        // Property: ActiveTDsState(k) -->* k_tds_states[|k_tds_states|-1] (
        // k_tds_states[|k_tds_states|-1] == Remove activating TDs from k'_tds_states[|k'_tds_states|-1])

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

    var k'_last_from_tds_state := k'_tds_states[|k'_tds_states|-2];
    var k'_last_to_tds_state := k'_tds_states[|k'_tds_states|-1];
    var k'_last_dev := k'_devs[|k'_devs|-1];
    var k_last_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_last_from_tds_state, toactivate_td_ids);
    var k_last_to_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_last_to_tds_state, toactivate_td_ids);
    assert TDsStateGetTDIDs(k_last_from_tds_state) == TDsStateGetTDIDs(k_last_to_tds_state);

    Lemma_SubjObjActivate_RemoveActivatingTDsFromAnActiveTDsStateInNewKIsAnActiveTDsStateInK(
        k, k', toactivate_s_ids, toactivate_td_ids, k'_last_from_tds_state, k_last_from_tds_state);
    assert TDsStateGetTDIDs(k_last_from_tds_state) == AllActiveTDs(k);
    assert IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                AllActiveDevs(k), ActiveTDsState(k), k_last_from_tds_state);
    if(SubjPID_DevID(k, k'_last_dev) != NULL)
    {
        assert SubjPID_DevID(k, k'_last_dev) != NULL && SubjPID_DevID(k', k'_last_dev) != NULL;

        assert k_last_from_tds_state in AllReachableActiveTDsStates(k);
        Lemma_SubjObjActivate_ExistingActiveDevDoNotModify_TDsBeingActivated_IncludingTDsRefedByHCodedTDsWithROfDevsBeingActivated(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, 
            k'_last_from_tds_state, k'_last_to_tds_state, k'_last_dev);
        assert forall td_id :: td_id in toactivate_td_ids
            ==> k'_last_to_tds_state[td_id] == k'_last_from_tds_state[td_id];

        Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyHCodedTDsOfActiveDevsInNewK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, 
            k'_last_from_tds_state, k'_last_to_tds_state, k'_last_dev);

        // Prove TDsStateDiff(k'_last_to_tds_state, k'_last_from_tds_state) == TDsStateDiff(k_last_to_tds_state, k_last_from_tds_state)
        var add_tds := MapSubmap(k'_last_from_tds_state, toactivate_td_ids);
        Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
            k_last_from_tds_state, k_last_to_tds_state, add_tds, k'_last_from_tds_state, k'_last_to_tds_state);

        // Prove k_last_from_tds_state --> k_last_to_tds_state
        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                    k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);
        Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_last_dev,
            k_last_from_tds_state, k_last_to_tds_state, k'_last_from_tds_state, k'_last_to_tds_state);
        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                k'_last_dev, k_last_from_tds_state, k_last_to_tds_state);

        // Prove (ActiveTDsState(k) == k_tds_states[|k_tds_states|-1]) ||
        //        IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), k_tds_states[|k_tds_states|-1])
        if(ActiveTDsState(k) == k_last_from_tds_state)
        {
            Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params,
                k'_last_dev, AllActiveDevs(k), k_last_from_tds_state, k_last_to_tds_state);
        }
        else
        {
            Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(k_params,
                k'_last_dev, AllActiveDevs(k),
                ActiveTDsState(k), k_last_from_tds_state, k_last_to_tds_state);
        }

        // Prove property 2
        Lemma_SubjObjActivate_ExistingActiveDevDoNotModify_TDsBeingActivated_IncludingTDsRefedByHCodedTDsWithROfDevsBeingActivated(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k'_last_from_tds_state, k'_last_to_tds_state, k'_last_dev);

        assert P_ForHCodedTDsOfDevsToBeActivated_TDsRefedByTheseTDsWithRAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_last_from_tds_state, k'_last_to_tds_state);
        assert P_ForDevsToBeActivated_TheirHCodedTDsAreUnmodified(
                    k', toactivate_s_ids, k'_last_from_tds_state, k'_last_to_tds_state);

        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_ExistingActiveDevSummary(
            k', k'_params, toactivate_s_ids, k'_tds_states,
            k'_last_from_tds_state, k'_last_to_tds_state);
    }
    else
    {
        assert SubjPID_DevID(k, k'_last_dev) == NULL;
        assert k'_last_dev.sid in toactivate_s_ids;

        // Prove property 2
        Lemma_SubjObjActivate_TDsRefedByHCodedTDWithROfDevBeingActivatedAreEmpty(
            k', k'_params, toactivate_s_ids, k'_tds_states, k'_last_from_tds_state, k'_last_dev);
        assert forall td_id:TD_ID :: td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, k'_last_dev)
            ==> (k'_last_from_tds_state[td_id].trans_params_tds == map[] &&
                k'_last_from_tds_state[td_id].trans_params_fds == map[] &&
                k'_last_from_tds_state[td_id].trans_params_dos == map[]);

        Lemma_SameObjsOwnershipInSuccessiveStates(k, k');
        Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_DevsToActivateOnlyModifyTDsWithHCodedW(
                k', k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);
        assert DevModifyTDsStateOnlyWithHCodedWToTDs(k'_params, k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);

        Lemma_SubjObjActivate_DevBeingActivatedDoNotModifyHCodedTDs_OrTDsRefedByTheseTDsWithR(
            k', k'_params, k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);

        // Prove k_last_from_tds_state == k_last_to_tds_state
        Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_DevsToActivateOnlyModifyTDsWithHCodedW(
                k', k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);
        assert DevModifyTDsStateOnlyWithHCodedWToTDs(k'_params, k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);
        Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_UnOwnedTDsAreNotChanged(k', k'_params, k'_last_dev, k'_last_from_tds_state, k'_last_to_tds_state);
        assert forall td_id :: td_id in k'_last_from_tds_state &&
                    td_id !in toactivate_td_ids
                ==> k'_last_to_tds_state[td_id] == k'_last_from_tds_state[td_id];
        Lemma_IfTDsStatesAreDifferentOnlyForAddedTDs_ThenReducedTDsStatesAreSame(
            toactivate_td_ids, k'_last_from_tds_state, k'_last_to_tds_state, k_last_from_tds_state, k_last_to_tds_state);
        assert k_last_from_tds_state == k_last_to_tds_state;

        Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_DevToActivateSummary(
            k', k'_params, toactivate_s_ids, k'_tds_states,
            k'_last_from_tds_state, k'_last_to_tds_state);
    }
}

lemma Lemma_SubjObjActivate_TDsStateIsValidAfterAddTDsIfValidBefore_HCodedTDOfDevToBeActivatedHasNoInvalidRefs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    k'_tds_state:TDs_Vals,
    k'_dev_id:Dev_ID, k'_td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds
                        ==> td_id !in k_params.hcoded_td_ids)
        // Requirement: Devices' hardcoded TDs do not reference any hardcoded TDs

    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')

    requires k'_dev_id in AllActiveDevs(k')
    requires k'_td_id in TDsStateGetTDIDs(k'_tds_state)
        // Requirement: The TD (<k'_td_id>) is active
    requires k'_td_id == k'.subjects.devs[k'_dev_id].hcoded_td_id
        // Requirement: k'_td_id is the hardcoded TD of the device to be 
        // activated

    requires forall dev_id, td_id :: dev_id in AllActiveDevs(k') &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
                ==> td_id in k'_tds_state &&
                    k'_tds_state[td_id] == k'.objects.tds[td_id].val
        // Requriement: <k'_tds_state> includes hardcoded TDs of active devices,
        // and their values in <k'.objects.tds>

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id)
{
    assert k'.subjects.devs[k'_dev_id].hcoded_td_id == k.subjects.devs[k'_dev_id].hcoded_td_id;

    assert k'.objects.tds[k'.subjects.devs[k'_dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[k'_dev_id].hcoded_td_id].val;
    assert k'.objects.tds[k'_td_id].val == k.objects.tds[k'_td_id].val;

    assert k.objects.tds[k.subjects.devs[k'_dev_id].hcoded_td_id].val == HCodedTDValOfDev(KToKParams(k).hcoded_tds, k'_dev_id);
    assert k.objects.tds[k.subjects.devs[k'_dev_id].hcoded_td_id].val == HCodedTDValOfDev(KToKParams(k').hcoded_tds, k'_dev_id);

    var hcoded_td := HCodedTDValOfDev(KToKParams(k').hcoded_tds, k'_dev_id);
    assert MapGetKeys(hcoded_td.trans_params_tds) <= IDToDev(k', k'_dev_id).td_ids;
    assert MapGetKeys(hcoded_td.trans_params_fds) <= IDToDev(k', k'_dev_id).fd_ids;
    assert MapGetKeys(hcoded_td.trans_params_dos) <= IDToDev(k', k'_dev_id).do_ids;

    assert forall td_id :: td_id in hcoded_td.trans_params_tds
                ==> td_id !in KToKParams(k).hcoded_td_ids;

    assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k'_tds_state, k'_td_id);
}

lemma Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_Prove(
    k:State,
    dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: No two subjects own the same object

    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k)
        // Requirement: <from_tds_state> contains all IDs of active TDs

    requires dev_id in k.subjects.devs
    requires SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL
    
    requires TDsStateGetTDIDs(from_tds_state) == TDsStateGetTDIDs(to_tds_state)

    requires forall td_id:TD_ID :: td_id in TDsRefedByDevHCodedTDWithR(KToKParams(k).hcoded_tds, dev_id)
                ==> td_id in from_tds_state &&
                    from_tds_state[td_id].trans_params_tds == map[] &&
                    from_tds_state[td_id].trans_params_fds == map[] &&
                    from_tds_state[td_id].trans_params_dos == map[]
        // Requirement: TDs that refed in the device's hardcoded TD with R
        // must be cleared in device activation
    requires P_HCodedTDsOfActiveDevsAreUnmodified(k, from_tds_state)
        // Requriement: <from_tds_state> includes hardcoded TDs of active devices,
        // and their values in <k.objects.tds>

    requires forall td_id, td_new_cfg :: td_id in TDsStateDiff(to_tds_state, from_tds_state) && 
                    td_new_cfg == TDsStateDiff(to_tds_state, from_tds_state)[td_id]
                ==> (exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(from_tds_state) && ObjPID_SlimState(KToKParams(k).objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(KToKParams(k), from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(from_tds_state, tdx_id, td_id, td_new_cfg))

    requires forall td_id, td_new_cfg :: td_id in TDsStateDiff(to_tds_state, from_tds_state) && 
                    td_new_cfg == TDsStateDiff(to_tds_state, from_tds_state)[td_id]
                ==> !(exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(from_tds_state) && ObjPID_SlimState(KToKParams(k).objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(KToKParams(k), from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device
                            tdx_id !in KToKParams(k).hcoded_td_ids &&
                                // the active TD is not a hardcoded TD
                            IsTDWriteInTD(from_tds_state, tdx_id, td_id, td_new_cfg))

    ensures DevModifyTDsStateOnlyWithHCodedWToTDs(KToKParams(k), dev_id, from_tds_state, to_tds_state)
{
    var tds_diff := TDsStateDiff(to_tds_state, from_tds_state);
    var k_params := KToKParams(k);
    var hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;

    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k_params.hcoded_tds[dev_id] == 
                    k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val;

    assert dev_id in AllActiveDevs(k);
    assert forall dev_id2, td_id2 :: dev_id2 in AllActiveDevs(k) &&
                    td_id2 == k.subjects.devs[dev_id2].hcoded_td_id
                ==> td_id2 in from_tds_state &&
                    from_tds_state[td_id2] == k.objects.tds[td_id2].val;
    assert GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id) == from_tds_state[k.subjects.devs[dev_id].hcoded_td_id].trans_params_tds;

    assert (forall dev_id :: dev_id in k.subjects.devs
        ==> (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_tds) <= 
                IDToDev(k, dev_id).td_ids) &&
            (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_fds) <= 
                IDToDev(k, dev_id).fd_ids) &&
            (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_dos) <= 
                IDToDev(k, dev_id).do_ids));

    forall td_id, td_new_cfg | td_id in tds_diff &&
                               td_new_cfg == tds_diff[td_id]
        ensures TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id),
                    td_id, td_new_cfg)
    {
        var tdx_id :| tdx_id in TDsStateGetTDIDs(from_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(from_tds_state, tdx_id, td_id, td_new_cfg);
        assert tdx_id in k_params.hcoded_td_ids;

        // Prove tdx_id in k.subjects.devs[dev_id].td_ids
        Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_Prove_TDXMustInDev(
            k, from_tds_state, dev_id, tdx_id);

        // Prove tdx_id == k.subjects.devs[dev_id].hcoded_td_id 
        Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_Prove_TDXIDIsHCodedTDID(k, dev_id, tdx_id);
        assert tdx_id == k.subjects.devs[dev_id].hcoded_td_id;

        if(!TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id),
                    td_id, td_new_cfg))
        {
            assert !TDWriteTransferInTD(from_tds_state[k.subjects.devs[dev_id].hcoded_td_id].trans_params_tds,
                    td_id, td_new_cfg);

            assert !TDWriteTransferInTD(from_tds_state[tdx_id].trans_params_tds, td_id, td_new_cfg);

            // Show conflict
            assert IsTDWriteInTD(from_tds_state, tdx_id, td_id, td_new_cfg);
            assert false;
        }
    }
}

lemma Lemma_SubjObjActivate_ForDevBeingActivated_TDsRefedByHCodedTDWithRMustAlsoBeingActivated(
    k:State, k_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in toactivate_s_ids 
                ==> IsSubjID(k.subjects, s_id)

    requires forall s_id :: s_id in toactivate_s_ids 
                ==> OwnedTDs(k, s_id) <= toactivate_td_ids
        // Requirement: Activating subjects have their TDs in <toactivate_td_ids>
    requires toactivate_td_ids <= MapGetKeys(k.objects.tds)
        // Requirement: TDs in <toactivate_td_ids> exist in the system

    ensures forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id in TDsRefedByDevHCodedTDWithR(KToKParams(k).hcoded_tds, dev_id)
                ==> td_id in toactivate_td_ids
        // Property: TDs refed by hardcoded TDs are also being activated
{
    var k_params := KToKParams(k);

    assert forall td_id, dev_id:Dev_ID :: IsDevID_SlimState(k.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, dev_id)
                ==> td_id in k.subjects.devs[dev_id].td_ids;
}

lemma Lemma_IfTDsStatesAreDifferentOnlyForAddedTDs_ThenReducedTDsStatesAreSame(
    add_tds:set<TD_ID>,
    from_tds_state':TDs_Vals, to_tds_state':TDs_Vals, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires from_tds_state == MapRemoveKeys<TD_ID, TD_Val>(from_tds_state', add_tds)
    requires to_tds_state == MapRemoveKeys<TD_ID, TD_Val>(to_tds_state', add_tds)

    requires TDsStateGetTDIDs(to_tds_state) == TDsStateGetTDIDs(from_tds_state)
    requires TDsStateGetTDIDs(to_tds_state') == TDsStateGetTDIDs(from_tds_state')
    requires TDsStateGetTDIDs(from_tds_state) * add_tds == {}
    requires TDsStateGetTDIDs(from_tds_state') == TDsStateGetTDIDs(from_tds_state) + add_tds

    requires forall td_id :: td_id in from_tds_state' &&
                    td_id !in add_tds
                ==> to_tds_state'[td_id] == from_tds_state'[td_id]

    ensures from_tds_state == to_tds_state
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_DevToActivateSummary(
    k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, k'_tds_states:seq<TDs_Vals>,
    k'_last_from_tds_state:TDs_Vals, k'_last_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires k'_params == KToKParams(k')

    requires forall s_id :: s_id in AllSubjsIDs(k'.subjects) &&
                    s_id in toactivate_s_ids 
                ==> SubjPID(k', s_id) != NULL

    requires |k'_tds_states| >= 2
    requires k'_last_from_tds_state == k'_tds_states[|k'_tds_states|-2]
    requires k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1]

    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])
    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])
                    
    requires forall td_id2, dev_id2:Dev_ID :: IsDevID(k', dev_id2) &&
                    SubjPID_DevID(k', dev_id2) != NULL &&
                    td_id2 == k'.subjects.devs[dev_id2].hcoded_td_id
                        // Forall hardcoded TD (<td_id2>) in any active devices
                ==> td_id2 in k'_last_from_tds_state && td_id2 in k'_last_to_tds_state && 
                    k'_last_from_tds_state[td_id2] == k'_last_to_tds_state[td_id2]
    requires forall td_id2, dev_id2:Dev_ID :: IsDevID(k', dev_id2) &&
                    SubjPID_DevID(k', dev_id2) != NULL &&
                    td_id2 in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id2)
                        // Forall TDs (<td_id2>) refed by hardcoded TDs of any active device
                ==> td_id2 in k'_last_from_tds_state && td_id2 in k'_last_to_tds_state &&
                    k'_last_from_tds_state[td_id2] == k'_last_to_tds_state[td_id2]

    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states)
    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states)
{
    assert forall tds_state2 :: tds_state2 in k'_tds_states
                ==> tds_state2 == k'_last_to_tds_state || tds_state2 in k'_tds_states[..|k'_tds_states|-1];
    assert k'_last_from_tds_state in k'_tds_states[..|k'_tds_states|-1];

    // Prove property 1
    forall tds_state2 | tds_state2 in k'_tds_states
        ensures P_HCodedTDsOfActiveDevsAreUnmodified(k', tds_state2)
    {
        if(tds_state2 == k'_last_to_tds_state)
        {
            forall dev_id, td_id | dev_id in AllActiveDevs(k') &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
                ensures td_id in tds_state2
                ensures tds_state2[td_id] == k'.objects.tds[td_id].val
            {
                assert IsDevID(k', dev_id);
                assert SubjPID_DevID(k', dev_id) != NULL;
                assert tds_state2[td_id] == k'_last_from_tds_state[td_id];
            }
        }
    }

    // Prove property 2
    forall tds_state2, td_id, dev_id:Dev_ID | IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    tds_state2 in k'_tds_states &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
        ensures (td_id in tds_state2 && td_id in k'.objects.tds &&
                     tds_state2[td_id] == k'.objects.tds[td_id].val)
    {
        if(tds_state2 == k'_last_to_tds_state)
        {
            assert SubjPID_DevID(k', dev_id) != NULL;

            assert td_id in k'_last_from_tds_state;
            assert td_id in tds_state2;
            assert tds_state2[td_id] == k'.objects.tds[td_id].val;
        }
    }
}

lemma Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_ExistingActiveDevSummary(
    k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, k'_tds_states:seq<TDs_Vals>,
    k'_last_from_tds_state:TDs_Vals, k'_last_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires k'_params == KToKParams(k')

    requires forall s_id :: s_id in AllSubjsIDs(k'.subjects) &&
                    s_id in toactivate_s_ids 
                ==> SubjPID(k', s_id) != NULL

    requires |k'_tds_states| >= 2
    requires k'_last_from_tds_state == k'_tds_states[|k'_tds_states|-2]
    requires k'_last_to_tds_state == k'_tds_states[|k'_tds_states|-1]

    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])
    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])
        
    requires P_ForDevsToBeActivated_HCodedTDsOfActiveDevsInNewKAreUnmodified(
                    k', toactivate_s_ids, k'_last_from_tds_state, k'_last_to_tds_state)            
    requires P_ForHCodedTDsOfDevsToBeActivated_TDsRefedByTheseTDsWithRAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_last_from_tds_state, k'_last_to_tds_state)
    
    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_HCodedTDsOfDevsToBeActivatedAreUnmodified(
                    k', toactivate_s_ids, k'_tds_states)
    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states)
{
    assert forall tds_state2 :: tds_state2 in k'_tds_states
                ==> tds_state2 == k'_last_to_tds_state || tds_state2 in k'_tds_states[..|k'_tds_states|-1];
    assert k'_last_from_tds_state in k'_tds_states[..|k'_tds_states|-1];

    // Prove property 1
    forall tds_state2 | tds_state2 in k'_tds_states
        ensures P_HCodedTDsOfActiveDevsAreUnmodified(k', tds_state2)
    {
        if(tds_state2 == k'_last_to_tds_state)
        {
            forall dev_id, td_id | dev_id in AllActiveDevs(k') &&
                    td_id == k'.subjects.devs[dev_id].hcoded_td_id
                ensures td_id in tds_state2
                ensures tds_state2[td_id] == k'.objects.tds[td_id].val
            {
                assert IsDevID(k', dev_id);
                assert SubjPID_DevID(k', dev_id) != NULL;

                assert td_id in tds_state2;
                assert tds_state2[td_id] == k'_last_from_tds_state[td_id];
            }
        }
    }

    // Prove property 2
    forall tds_state2, td_id, dev_id:Dev_ID | IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    tds_state2 in k'_tds_states &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
        ensures (td_id in tds_state2 && td_id in k'.objects.tds &&
                     tds_state2[td_id] == k'.objects.tds[td_id].val)
    {
        if(tds_state2 == k'_last_to_tds_state)
        {
            assert SubjPID_DevID(k', dev_id) != NULL;

            assert td_id in k'_last_from_tds_state;
            assert td_id in tds_state2;
            assert tds_state2[td_id] == k'.objects.tds[td_id].val;
        }
    }
}

lemma Lemma_SubjObjActivate_IfTDsStatesCanBeReachedFromActiveTDsStatesInNewK_ThenReducedTDsStatesCanBeReachedInK_OneStateSummary(
    k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, k'_tds_states:seq<TDs_Vals>
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires k'_params == KToKParams(k')

    requires forall s_id :: s_id in AllSubjsIDs(k'.subjects) &&
                    s_id in toactivate_s_ids 
                ==> SubjPID(k', s_id) != NULL

    requires |k'_tds_states| == 1
    requires k'_tds_states[0] == ActiveTDsState(k')

    ensures P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states)
{
    forall tds_state2, td_id, dev_id:Dev_ID | IsDevID_SlimState(k'.subjects, dev_id) &&
                    dev_id.sid in toactivate_s_ids &&
                    tds_state2 in k'_tds_states &&
                    td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
        ensures (td_id in tds_state2 && td_id in k'.objects.tds &&
                     tds_state2[td_id] == k'.objects.tds[td_id].val)
    {
        assert tds_state2 == ActiveTDsState(k');
        assert DoOwnObj(k', dev_id.sid, td_id.oid);

        assert td_id in tds_state2;
        assert td_id in k'.objects.tds;
    }
}

lemma Lemma_SubjObjActivate_TDsRefedByHCodedTDWithROfDevBeingActivatedAreEmpty(
    k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, k'_tds_states:seq<TDs_Vals>,
    k'_last_from_tds_state:TDs_Vals, k'_last_dev:Dev_ID
)
    requires SubjObjActivate_PreConditionsOfK(k')
    requires k'_params == KToKParams(k')

    requires |k'_tds_states| > 2
    requires k'_last_from_tds_state == k'_tds_states[|k'_tds_states|-2]

    requires IsDevID_SlimState(k'.subjects, k'_last_dev)
    requires k'_last_dev.sid in toactivate_s_ids

    requires forall td_id:TD_ID, dev_id:Dev_ID :: dev_id in k'.subjects.devs &&
                dev_id.sid in toactivate_s_ids && 
                td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
            ==> td_id in k'.objects.tds &&
                k'.objects.tds[td_id].val == TD_Val(map[], map[], map[])
        // Property: In k'.objects.tds, TDs refed by hardcoded TDs with R are empty
    requires P_ReachableTDsStatesFromActiveTDsStatesOfNewK_TDsRefedByHCodedTDsWithROfDevToBeActivatedAreUnmodified(
                    k', k'_params, toactivate_s_ids, k'_tds_states[..|k'_tds_states|-1])

    ensures forall td_id:TD_ID :: td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, k'_last_dev)
            ==> (k'_last_from_tds_state[td_id].trans_params_tds == map[] &&
                k'_last_from_tds_state[td_id].trans_params_fds == map[] &&
                k'_last_from_tds_state[td_id].trans_params_dos == map[]);
{
    // Dafny can automatically prove this lemma
}




//******** Lemmas of ReachableTDs' States ********//
predicate P_HCodedTDsOfActiveDevsAreUnmodified(k:State, tds_state:TDs_Vals)
    requires SubjObjActivate_PreConditionsOfK(k)
{
    forall dev_id, td_id :: dev_id in AllActiveDevs(k) &&
                    td_id == k.subjects.devs[dev_id].hcoded_td_id
                ==> td_id in tds_state &&
                    tds_state[td_id] == k.objects.tds[td_id].val
        // <tds_state> includes hardcoded TDs of active devices,
        // and their values in <k.objects.tds>
}

lemma Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_DevsToActivateOnlyModifyTDsWithHCodedW(
    k:State, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: No two subjects own the same object

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(to_tds_state) == AllActiveTDs(k)
        // Requirement: <from_tds_state> and <to_tds_state> must includes all active TDs
    requires IsDevID_SlimState(k.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires forall td_id:TD_ID :: td_id in TDsRefedByDevHCodedTDWithR(KToKParams(k).hcoded_tds, dev_id)
                ==> td_id in from_tds_state &&
                    from_tds_state[td_id].trans_params_tds == map[] &&
                    from_tds_state[td_id].trans_params_fds == map[] &&
                    from_tds_state[td_id].trans_params_dos == map[]
        // Requirement: TDs that refed in the device's hardcoded TD with R
        // must be cleared in device activation
    requires P_HCodedTDsOfActiveDevsAreUnmodified(k, from_tds_state)
        // Requriement: <from_tds_state> includes hardcoded TDs of active devices,
        // and their values in <k.objects.tds>
   
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(KToKParams(k), dev_id, from_tds_state, to_tds_state)

    ensures DevModifyTDsStateOnlyWithHCodedWToTDs(KToKParams(k), dev_id, from_tds_state, to_tds_state)
        // Property: An activating device modifies the given TDs' state 
        // (<from_tds_state>) ONLY due to its hardcoded write transfers to TDs
{
    var tds_diff := TDsStateDiff(to_tds_state, from_tds_state);
    var tds_state := from_tds_state;
    var k_params := KToKParams(k);

    Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
            k_params, dev_id, from_tds_state, to_tds_state);
    assert forall td_id, td_new_cfg :: td_id in tds_diff &&
                td_new_cfg == tds_diff[td_id]
                    ==> (exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg));
                                // the active TD refs the TD with W and the new TD cfg
    
    forall td_id, td_new_cfg | td_id in tds_diff &&
                               td_new_cfg == tds_diff[td_id]
        ensures !(exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device
                            tdx_id !in k_params.hcoded_td_ids &&
                                // the active TD is not a hardcoded TD
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg))
    {
        if (exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            tdx_id !in k_params.hcoded_td_ids &&
                                    // the active TD is not a hardcoded TD
                            IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg))
        {
            var tdx_id :|   tdx_id in AllActiveTDs(k) &&
                            CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) &&
                            tdx_id !in k_params.hcoded_td_ids &&
                            td_id in from_tds_state[tdx_id].trans_params_tds &&
                            W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                                // The TD references the target TD (<td_id2>) with W
                            to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals;

            assert CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id);

            Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD(
                k, from_tds_state, dev_id, tdx_id);
            assert tdx_id in k_params.hcoded_td_ids || from_tds_state[tdx_id].trans_params_tds == map[];
            assert false;
        }
    }

    Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_Prove(k, dev_id, from_tds_state, to_tds_state);
}

lemma Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyAnyTDsBeingActivated(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, 
    k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals, k'_dev:Dev_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires SubjObjActivate_PreConditionsOfK(k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
        // Requirement: Additional preconditions of k for the proof
    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, k'_dev) 
    requires SubjPID_DevID(k, k'_dev) != NULL && SubjPID_DevID(k', k'_dev) != NULL;
        // Requirement: k'_dev is active in both k and k'
    requires TDsStateGetTDIDs(k'_from_tds_state) == AllActiveTDs(k')
    requires TDsStateGetTDIDs(k'_to_tds_state) == AllActiveTDs(k')
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                k'_dev, k'_from_tds_state, k'_to_tds_state)

    requires MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids) in AllReachableActiveTDsStates(k)
        // Requirement: ActiveTDsState(k) -->* k_from_tds_state

    ensures forall td_id :: td_id in toactivate_td_ids
                ==> k'_to_tds_state[td_id] == k'_from_tds_state[td_id]
{
    var k_from_tds_state := MapRemoveKeys<TD_ID, TD_Val>(k'_from_tds_state, toactivate_td_ids);

    assert k'_dev in k'.subjects.devs;

    Lemma_CanActiveDevReadActiveTD_NewKParamsFulfillPreConditions(k, k_params, k', k'_params);
    assert CanActiveDevReadActiveTD_KParams_PreConditions(k'_params);

    if(exists td_id :: td_id in toactivate_td_ids &&
                k'_to_tds_state[td_id] != k'_from_tds_state[td_id])
    {
        var td_id :| td_id in toactivate_td_ids &&
                k'_to_tds_state[td_id] != k'_from_tds_state[td_id];

        // Prove the TD modifications are stored in TDs
        Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyAnyTDsBeingActivated_RequiredPreConditionsOfNewK(
            k, k_params, k', k'_params, k'_dev);
        Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
            k'_params, k'_dev, k'_from_tds_state, k'_to_tds_state);
        var tdx_id :|
                (k'_dev in AllActiveDevs(k') &&
                    tdx_id in AllActiveTDs(k') &&
                    CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, k'_dev, tdx_id) &&
                    td_id in k'_from_tds_state[tdx_id].trans_params_tds &&
                    W in k'_from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                        // The TD references the target TD (<td_id2>) with W
                    k'_to_tds_state[td_id] in k'_from_tds_state[tdx_id].trans_params_tds[td_id].vals);
                        // The TD specifies the new value to be written

        assert k_from_tds_state in AllReachableActiveTDsStates(k);
        assert ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), k_from_tds_state);
                
        // Prove CanActiveDevReadActiveTD(k, k'_dev, tdx_id)
        Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
        Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
        assert CanActiveDevReadActiveTD(k_params, k_from_tds_state, k'_dev, tdx_id);

        // Prove tdx_id does not contain transfers to td_id, in k_from_tds_state
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_from_tds_state, tdx_id);
        assert td_id !in k_from_tds_state[tdx_id].trans_params_tds ||
                k_from_tds_state[tdx_id].trans_params_tds[td_id].amodes == {};
        assert td_id !in k'_from_tds_state[tdx_id].trans_params_tds ||
                k'_from_tds_state[tdx_id].trans_params_tds[td_id].amodes == {};

        assert ObjPID(k', tdx_id.oid) != NULL;
        Lemma_SubjObjActivate_IfNoWTransferInTD_ThenTDsValsCannotBeModifiedDueToDevReadTheTD(
            k', k'_dev, k'_from_tds_state, k'_to_tds_state, tdx_id, td_id);

        assert false;
    }
}

// Lemma: Prove the required preconditions for the property 2 of  
// Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyActivatingTDs
lemma Lemma_SubjObjActivate_ExistingActiveDevDoNotModifyAnyTDsBeingActivated_RequiredPreConditionsOfNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, k'_dev:Dev_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires IsDevID(k, k'_dev)
    requires SubjPID_DevID(k', k'_dev) != NULL

    ensures forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k'_params.subjects.drvs) && (Dev_ID(dev_sid) in k'_params.subjects.devs)
                 ==> (drv_sid != dev_sid)
    ensures AllActiveTDs(k') == k'_params.all_active_tds

    ensures IsDevID_SlimState(k'_params.subjects, k'_dev)
    ensures SubjPID_DevID_SlimState(k'_params.subjects, k'_dev) != NULL
    ensures DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, k'_dev)
    ensures IDToDev_SlimState(k'_params.subjects, k'_dev).td_ids <= k'_params.objs_td_ids
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

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
        // Requirement: Modifications to existing active TDs only

    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k'_from_tds_state> contains additional active TDs (if 
        // any) from <k_from_tds_state>
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
        // Property needed by the property below
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

    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Left(
        k, k_params, k', k'_params,
        toactivate_s_ids, toactivate_td_ids, dev_id,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);
    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Right(
        k, k_params, k', k'_params,
        toactivate_s_ids, toactivate_td_ids, dev_id,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);

    assert IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k'_params,   
                dev_id, k'_from_tds_state, TDsStateDiff(k'_to_tds_state, k'_from_tds_state))
           ==
            (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)));

    assert IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params,   
                dev_id, k_from_tds_state, TDsStateDiff(k_to_tds_state, k_from_tds_state))
           == 
           (forall td_id, td_new_cfg :: td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)));
}

// Lemma: For the <IsActiveTDsStateReachActiveTDsStateInOneStep> function, 
// activating subjects and TDs does not change the current accesses of other
// active devices
// (needs 30s to verify)
lemma Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

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
        // Requirement: Modifications to existing active TDs only   

    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k'_from_tds_state> contains additional active TDs (if 
        // any) from <k_from_tds_state>
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, k'_from_tds_state, k'_to_tds_state)
            <==>
            IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, k_from_tds_state, k_to_tds_state)
{
    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs(
        k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, dev_id,
        k_from_tds_state, k_to_tds_state, k'_from_tds_state, k'_to_tds_state);

    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, k_from_tds_state, k_to_tds_state)
                == IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, k_from_tds_state, TDsStateDiff(k_to_tds_state, k_from_tds_state));
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, k'_from_tds_state, k'_to_tds_state)
                == IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k'_params, dev_id, k'_from_tds_state, TDsStateDiff(k'_to_tds_state, k'_from_tds_state));
}

lemma Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_UnOwnedTDsAreNotChanged(
    k:State, k_params:ReachableTDsKParams, dev_id:Dev_ID, from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires k_params == KToKParams(k)

    requires dev_id in k.subjects.devs
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
    requires forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id)
                ==> td_id in k.subjects.devs[dev_id].td_ids

    requires TDsStateGetTDIDs(from_tds_state) == TDsStateGetTDIDs(to_tds_state) == AllActiveTDs(k)
    requires forall td_id :: td_id in TDsStateGetTDIDs(from_tds_state) &&
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, from_tds_state, dev_id, td_id)
    
    requires DevModifyTDsStateOnlyWithHCodedWToTDs(k_params, dev_id, from_tds_state, to_tds_state)

    ensures forall td_id :: td_id in from_tds_state &&
                        td_id !in OwnedTDs(k, dev_id.sid)
                    ==> to_tds_state[td_id] == from_tds_state[td_id]
        // Property: TDs not owned by the device <dev_id> are unchanged 
        // between from_tds_state and to_tds_state
{
    assert forall td_id, td_new_cfg :: td_id in TDsStateDiff(to_tds_state, from_tds_state) &&
                td_new_cfg == TDsStateDiff(to_tds_state, from_tds_state)[td_id]
            ==> TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id),
                        td_id, td_new_cfg);

    // Prove forall td_id :: td_id in TDsStateDiff(to_tds_state, from_tds_state)
    //       ==> td_id in IDToDev_SlimState(k.subjects, dev_id).td_ids;
    if(exists td_id :: td_id in TDsStateDiff(to_tds_state, from_tds_state) &&
                       td_id !in IDToDev_SlimState(k.subjects, dev_id).td_ids)
    {
        var td_id :| td_id in TDsStateDiff(to_tds_state, from_tds_state) &&
                     td_id !in IDToDev_SlimState(k.subjects, dev_id).td_ids;
        var td_new_cfg := TDsStateDiff(to_tds_state, from_tds_state)[td_id];

        assert td_id !in GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id);

        // Show conflict
        assert !TDWriteTransferInTD(GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id),
                        td_id, td_new_cfg);
    }

    assert forall td_id :: td_id in TDsStateDiff(to_tds_state, from_tds_state)
            ==> td_id in IDToDev_SlimState(k.subjects, dev_id).td_ids;
    forall td_id | td_id in from_tds_state &&
                   td_id !in OwnedTDs(k, dev_id.sid)
        ensures to_tds_state[td_id] == from_tds_state[td_id]
    {
        if(to_tds_state[td_id] != from_tds_state[td_id])
        {
            assert false;
        }
    }
}




//******** Lemmas of CanActiveDevReadActiveTD ********//
lemma Lemma_CanActiveDevReadActiveTD_NewKParamsFulfillPreConditions(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
{
    // Dafny can automatically prove this lemma
}

// Lemma: For the <CanActiveDevReadActiveTD> function, when a subject is 
// activating, if the device (<dev_id>) is active in both k and k', and the 
// device can read the active TD (<tdx_id>) under the active TDs' state 
// (<k'_tds_state>), then the TD cannot be in <activating_td_ids>
// (needs 120s to verify)
lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall o_id  :: TD_ID(o_id) in k.objects.tds
                ==> o_id in AllObjsIDs(k.objects)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)
        // Requirement: In <k_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures forall td_id2, dev_id2 :: 
                        dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                        td_id2 in AllActiveTDs(k') &&
                        CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2)
                        // Forall active TDs that can be read by active devices
                ==> td_id2 in AllActiveTDs(k)
        // Property: In <k'_tds_state>, if an device active in k and k' has read 
        // transfers to an active TD, then the TD cannot be in <toactivate_td_ids>
    ensures forall activating_td_id, dev_id2 :: 
                dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                activating_td_id in toactivate_td_ids
            ==> DoOwnObj(k', dev_id2.sid, activating_td_id.oid) == false
        // Property: Device active in both k and k' do not own any TDs being activated
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

    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    assert CanActiveDevReadActiveTD_KParams_PreConditions(k'_params);
    if (exists td_id2, dev_id2 :: dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                        td_id2 in AllActiveTDs(k') &&
                        CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2) &&
                        td_id2 in toactivate_td_ids)
    {
        var k_dev_id, k'_td_id :| k_dev_id in AllActiveDevs(k) && k_dev_id in AllActiveDevs(k') &&
                        k'_td_id in AllActiveTDs(k') &&
                        CanActiveDevReadActiveTD(k'_params, k'_tds_state, k_dev_id, k'_td_id) &&
                        k'_td_id in toactivate_td_ids;

        assert DoOwnObj(k, k_dev_id.sid, k'_td_id.oid) == false;
        assert ObjPID(k, k'_td_id.oid) == NULL && ObjPID(k', k'_td_id.oid) != NULL;

        assert toactivate_td_ids != {};

        assert CanActiveDevReadActiveTD(k'_params, k'_tds_state, k_dev_id, k'_td_id);

        var tdx_id, out_td_id := Lemma_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotBeingActivated_ToActiveTDIDsAreNotEmpty(
            k, k', k_dev_id, k'_td_id, k_tds_state, k'_tds_state);
        assert CanActiveDevReadActiveTD(k_params, k_tds_state, k_dev_id, tdx_id);
        assert k_dev_id in AllActiveDevs(k);
        assert tdx_id in TDsStateGetTDIDs(k_tds_state);

        // tdx_id should not contain transfers to <out_td_id>
        assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state);
        Lemma_ActiveTDsStateIsSecure_TDReadByActiveDevMustHaveValidRefsOnly(
            k, k_tds_state, k_dev_id, tdx_id, out_td_id);
        assert out_td_id !in TDIDReadsInTDCfg(k_tds_state[tdx_id]);

        // Show the conflict
        assert TDIDReadsInTDCfg(k_tds_state[tdx_id]) == TDIDReadsInTDCfg(k'_tds_state[tdx_id]);

        assert false;
    }

    Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating_Property2(
        k, k', toactivate_td_ids);
}


// Lemma: In <k'_tds_state>, if an device active in k and k' has read transfers
// to an active TD, then in <k_tds_state>, the same device also have read
// transfers to the same (active) TD.
// (needs 100s to verify)
lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,  
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall o_id  :: TD_ID(o_id) in k.objects.tds
                ==> o_id in AllObjsIDs(k.objects)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires forall td_id2, dev_id2 :: 
                        dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                        td_id2 in AllActiveTDs(k') &&
                        CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2)
                        // Forall active TDs that can be read by active devices
                ==> td_id2 in AllActiveTDs(k)
        // Requirement: In <k'_tds_state>, if an device active in k and k' has read 
        // transfers to an active TD, then the TD cannot be in <toactivate_td_ids>
     
    ensures forall td_id2, dev_id2 :: 
                        dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                        td_id2 in AllActiveTDs(k') &&
                        CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id2, td_id2)
                ==> CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id2)
        // Property: In <k'_tds_state>, if an device active in k and k' has read 
        // transfers to an active TD, then in <k_tds_state>, the same device also
        // have read transfers to the same (active) TD.
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

    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    assert CanActiveDevReadActiveTD_KParams_PreConditions(k'_params);
    forall td_id, dev_id | dev_id in AllActiveDevs(k) && dev_id in AllActiveDevs(k') &&
                        td_id in AllActiveTDs(k') &&
                        CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id)
        ensures CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id)
    {
        var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k'_tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k'_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[td_ids[i]]));

        Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k'_params, k'_tds_state, dev_id, td_ids, td_id);
        assert forall td_id2 :: td_id2 in td_ids
                ==> CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id2);

        assert forall td_id2 :: td_id2 in td_ids 
                ==> td_id2 in k_tds_state;

        Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK_Private(
            k, k_tds_state, k'_tds_state, td_ids, dev_id, td_id);
    }
}

// (needs 120s to verify)
lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfActiveDevCanReadTDInK_ThenDevCanReadTDInNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,  
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall o_id  :: TD_ID(o_id) in k.objects.tds
                ==> o_id in AllObjsIDs(k.objects)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires dev_id in AllActiveDevs(k)
    requires td_id in TDsStateGetTDIDs(k_tds_state)
    requires ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL

    requires CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id)

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
    ensures CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id)
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

    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');

    assert CanActiveDevReadActiveTD_KParams_PreConditions(k'_params);
}

lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD_PreConditions(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    ensures SubjObjActivate_PreConditionsOfK(k')
    ensures forall dev_id2 :: dev_id2 in k'.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k', dev_id2) &&
                    IDToDev(k', dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k'.objects.tds)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD(
    k:State, k_tds_state:TDs_Vals, k_dev_id:Dev_ID, k_td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    requires forall o_id  :: TD_ID(o_id) in k.objects.tds
                ==> o_id in AllObjsIDs(k.objects)

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires k_td_id in k_tds_state
    requires IsDevID_SlimState(k.subjects, k_dev_id)
    requires SubjPID_DevID_SlimState(k.subjects, k_dev_id) != NULL

    requires CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, k_dev_id, k_td_id)

    requires forall td_id :: td_id in k.objects.tds &&
                    td_id in TDsRefedByDevHCodedTDWithR(KToKParams(k).hcoded_tds, k_dev_id)
                ==> td_id in k_tds_state &&
                    k_tds_state[td_id].trans_params_tds == map[] &&
                    k_tds_state[td_id].trans_params_fds == map[] &&
                    k_tds_state[td_id].trans_params_dos == map[]
    requires forall dev_id, td_id :: dev_id in AllActiveDevs(k) &&
                    td_id == k.subjects.devs[dev_id].hcoded_td_id
                ==> td_id in k_tds_state &&
                    k_tds_state[td_id] == k.objects.tds[td_id].val
        // Requirement: <k_tds_state> includes hardcoded TDs of active devices,
        // and their values in <k.objects.tds>

    ensures DoOwnObj(k, k_dev_id.sid, k_td_id.oid)
    ensures k_td_id == k.subjects.devs[k_dev_id].hcoded_td_id ||
            k_tds_state[k_td_id] == TD_Val(map[], map[], map[])
{
    var k_params := KToKParams(k);
    Lemma_TDsDevHCodedRead_ReturnsAllTDsReadRefedInHCodedTD(k.subjects, k.objects, k_params.hcoded_tds, k_dev_id);

    forall td_ids:seq<TD_ID> | 
                |td_ids| >= 1 && 
                (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k_tds_state) &&
                                                // A list of active TDs
                td_ids[|td_ids| - 1] == k_td_id && // last TD is the TD (<k_td_id>)
                td_ids[0] == k_params.subjects.devs[k_dev_id].hcoded_td_id &&
                                                // first TD must be the hardcoded TD
                (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[i]]))
        ensures |td_ids| <= 2
        ensures DoOwnObj(k, k_dev_id.sid, k_td_id.oid)
        ensures k_td_id == k.subjects.devs[k_dev_id].hcoded_td_id || 
                k_tds_state[k_td_id] == TD_Val(map[], map[], map[])
    {
        if(|td_ids| > 2)
        {
            assert td_ids[2] in TDIDReadsInTDCfg(k_tds_state[td_ids[1]]);
            assert td_ids[1] in TDIDReadsInTDCfg(k_tds_state[td_ids[0]]);

            assert k_params.hcoded_tds[k_dev_id] == k.objects.tds[k.subjects.devs[k_dev_id].hcoded_td_id].val;
            assert td_ids[1] in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, k_dev_id);

            // Show conflict    
            assert k_tds_state[td_ids[1]].trans_params_tds == map[];
            assert td_ids[2] !in TDIDReadsInTDCfg(k_tds_state[td_ids[1]]);
        }
        else if (|td_ids| == 2)
        {
            assert td_ids[1] in TDIDReadsInTDCfg(k_tds_state[td_ids[0]]);

            assert td_ids[1] in IDToDev(k, k_dev_id).td_ids;
            assert DoOwnObj(k, k_dev_id.sid, k_td_id.oid);

            assert k_td_id in TDsRefedByDevHCodedTDWithR(k_params.hcoded_tds, k_dev_id);
            assert k_tds_state[k_td_id] == TD_Val(map[], map[], map[]);
        }
        else
        {
            assert k_td_id == k.subjects.devs[k_dev_id].hcoded_td_id;
        }
    }
}




//******** Private Lemmas Used By Lemmas of ReachableTDs' States ********//
// (needs 80s to verify)
lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Left(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

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
        // Requirement: Modifications to existing active TDs only

    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k'_from_tds_state> contains additional active TDs (if 
        // any) from <k_from_tds_state>
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
        // Property needed by the property below
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

    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');
    
    Lemma_CanActiveDevReadActiveTD_NewKParamsFulfillPreConditions(k, k_params, k', k'_params);
    assert CanActiveDevReadActiveTD_KParams_PreConditions(k'_params);

    if(forall td_id, td_new_cfg :: td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)))
    {
        assert TDsStateGetTDIDs(k_from_tds_state) == AllActiveTDs(k);
        forall td_id, td_new_cfg | td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
            ensures exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                        ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)
        {
            var k_tdx_id :| k_tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, k_tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, k_tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, k_tdx_id, td_id, td_new_cfg);
            var k'_tdx_id := k_tdx_id;
                    
            assert k'_tdx_id in TDsStateGetTDIDs(k'_from_tds_state);
            assert ObjPID_SlimState(k'_params.objs_pids, k'_tdx_id.oid) != NULL; 
            Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfActiveDevCanReadTDInK_ThenDevCanReadTDInNewK(
                k, k_params, k', k'_params,  
                toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state,
                dev_id, k'_tdx_id);
            assert CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, k'_tdx_id);
            assert IsTDWriteInTD(k'_from_tds_state, k'_tdx_id, td_id, td_new_cfg);
        }
    }
}

// (needs 90s to verify)
lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_SubjsBeingActivatedDoNotModifyCurrentAccessesOfOtherActiveDevs_Right(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, dev_id:Dev_ID,
    k_from_tds_state:TDs_Vals, k_to_tds_state:TDs_Vals, k'_from_tds_state:TDs_Vals, k'_to_tds_state:TDs_Vals
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

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
        // Requirement: Modifications to existing active TDs only

    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_from_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_from_tds_state) ==> k'_from_tds_state[td_id] == k_from_tds_state[td_id])
        // Requirement: <k'_from_tds_state> contains additional active TDs (if 
        // any) from <k_from_tds_state>
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_from_tds_state)
        // Requirement: In <k_from_tds_state>, any active TDs read by any 
        // active devices have no invalid references to I/O objects

    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k'_params)
        // Property needed by the property below
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

    assert k_params.all_active_tds == AllActiveTDs(k);
    assert k'_params.all_active_tds == AllActiveTDs(k');
    
    Lemma_CanActiveDevReadActiveTD_NewKParamsFulfillPreConditions(k, k_params, k', k'_params);
    assert CanActiveDevReadActiveTD_KParams_PreConditions(k'_params);

    if(forall td_id, td_new_cfg :: td_id in TDsStateDiff(k'_to_tds_state, k'_from_tds_state) &&
                td_new_cfg == TDsStateDiff(k'_to_tds_state, k'_from_tds_state)[td_id]
                    ==> (exists tdx_id :: tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, tdx_id, td_id, td_new_cfg)))
    {
        assert TDsStateGetTDIDs(k'_from_tds_state) == AllActiveTDs(k');
        forall td_id, td_new_cfg | td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
                                    td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id]
            ensures exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && 
                        ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)
        {
            var k'_tdx_id :| k'_tdx_id in TDsStateGetTDIDs(k'_from_tds_state) && 
                            ObjPID_SlimState(k'_params.objs_pids, k'_tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k'_params, k'_from_tds_state, dev_id, k'_tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k'_from_tds_state, k'_tdx_id, td_id, td_new_cfg);

            var k_tdx_id := k'_tdx_id;
            Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
            assert k_tdx_id in TDsStateGetTDIDs(k_from_tds_state);
            assert ObjPID_SlimState(k_params.objs_pids, k_tdx_id.oid) != NULL;
            Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, k_from_tds_state, k'_from_tds_state);
            assert CanActiveDevReadActiveTD(k_params, k_from_tds_state, dev_id, k_tdx_id);
            assert IsTDWriteInTD(k_from_tds_state, k_tdx_id, td_id, td_new_cfg);
        }
    }
}

lemma Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_Prove_TDXIDIsHCodedTDID(k:State, dev_id:Dev_ID, tdx_id:TD_ID)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: No two subjects own the same object

    requires dev_id in k.subjects.devs

    requires tdx_id in KToKParams(k).hcoded_td_ids
    requires tdx_id in k.subjects.devs[dev_id].td_ids

    ensures tdx_id == k.subjects.devs[dev_id].hcoded_td_id
{
    assert forall td_id :: td_id in KToKParams(k).hcoded_td_ids
                <==> (exists dev_id :: dev_id in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id].hcoded_td_id);

    if(tdx_id != k.subjects.devs[dev_id].hcoded_td_id)
    {
        assert exists dev_id2 :: dev_id2 in k.subjects.devs &&
                dev_id2 != dev_id &&
                tdx_id == k.subjects.devs[dev_id2].hcoded_td_id;

        var dev_id2 :| dev_id2 in k.subjects.devs &&
                dev_id2 != dev_id &&
                tdx_id == k.subjects.devs[dev_id2].hcoded_td_id;

        assert DoOwnObj(k, dev_id2.sid, tdx_id.oid);

        // Show conflict
        assert DoOwnObj(k, dev_id.sid, tdx_id.oid);
        assert dev_id2 == dev_id;
    }
}

lemma Lemma_DevModifyTDsStateOnlyWithHCodedWToTDs_Prove_TDXMustInDev(
    k:State, from_tds_state:TDs_Vals,
    dev_id:Dev_ID, tdx_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires dev_id in k.subjects.devs
    requires SubjPID_DevID_SlimState(k.subjects, dev_id) != NULL
    
    requires MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= IDToDev(k, dev_id).td_ids

    requires tdx_id in KToKParams(k).hcoded_td_ids

    requires tdx_id in TDsStateGetTDIDs(from_tds_state)
    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k)
        // Requirement: <from_tds_state> contains all IDs of active TDs

    requires CanActiveDevReadActiveTD(KToKParams(k), from_tds_state, dev_id, tdx_id)

    requires forall td_id:TD_ID :: td_id in TDsRefedByDevHCodedTDWithR(KToKParams(k).hcoded_tds, dev_id)
                ==> td_id in from_tds_state &&
                    from_tds_state[td_id].trans_params_tds == map[] &&
                    from_tds_state[td_id].trans_params_fds == map[] &&
                    from_tds_state[td_id].trans_params_dos == map[]
        // Requirement: TDs that refed in the device's hardcoded TD with R
        // must be cleared in device activation
    requires P_HCodedTDsOfActiveDevsAreUnmodified(k, from_tds_state)
        // Requriement: <from_tds_state> includes hardcoded TDs of active devices,
        // and their values in <k.objects.tds>

    ensures tdx_id in k.subjects.devs[dev_id].td_ids
{
    var k_params := KToKParams(k);
    assert k_params.hcoded_td_ids == AllHCodedTDIDs(k.subjects);

    if(tdx_id !in k.subjects.devs[dev_id].td_ids)
    {
        assert k_params.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids;
        assert tdx_id != k_params.subjects.devs[dev_id].hcoded_td_id;

        var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
                (forall td_id2 :: td_id2 in td_ids ==> td_id2 in from_tds_state) &&
                                                // A list of active TDs
                td_ids[|td_ids| - 1] == tdx_id && // last TD is the TD (<td_id>)
                td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                                // first TD must be the hardcoded TD
                (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(from_tds_state[td_ids[i]]));
                                                // previous TD always refs the current TD with R access mode

        // Prove |td_ids| > 2
        assert MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_tds) <= IDToDev(k, dev_id).td_ids;
        if(|td_ids| == 2)
        { 
            assert tdx_id in HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_tds;
        }
        assert |td_ids| > 2;

        // Show conflicts
        assert td_ids[1] in TDsRefedByDevHCodedTDWithR(KToKParams(k).hcoded_tds, dev_id);
        assert td_ids[2] in TDIDReadsInTDCfg(from_tds_state[td_ids[1]]);

        assert td_ids[2] !in TDIDReadsInTDCfg(from_tds_state[td_ids[1]]);
        assert false;
    }
}




//******** Private Lemmas Used By Lemmas of CanActiveDevReadActiveTD ********//
predicate CanActiveDevReadActiveTD_TDRefTDWithRInChain(tds_state:TDs_Vals, td_ids:seq<TD_ID>)
    requires forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state
{
    forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]])
}

lemma Lemma_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotBeingActivated_ToActiveTDIDsAreNotEmpty(
    k:State, k':State,
    k_dev_id:Dev_ID, k'_td_id:TD_ID, 
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
) returns (tdx_id:TD_ID, out_td_id:TD_ID)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') > AllActiveTDs(k)
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires k_dev_id in AllActiveDevs(k) && k_dev_id in AllActiveDevs(k')

    requires k'_td_id !in AllActiveTDs(k) && k'_td_id in AllActiveTDs(k')
    requires CanActiveDevReadActiveTD(KToKParams(k'), k'_tds_state, k_dev_id, k'_td_id)

    ensures tdx_id in TDsStateGetTDIDs(k_tds_state)
    ensures tdx_id in AllActiveTDs(k)
    ensures out_td_id in TDIDReadsInTDCfg(k'_tds_state[tdx_id])
    ensures out_td_id !in AllActiveTDs(k) && out_td_id in AllActiveTDs(k')
    ensures ObjPID(k, tdx_id.oid) != ObjPID(k, out_td_id.oid)
    ensures CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, k_dev_id, tdx_id)
{
    var td_ids, tdx_id_i, t_tdx_id, t_out_td_id := 
        Lemma_SubjObjActivate_IfActiveDevReadsNewlyActivatedTDInNewK_ThenExistActiveTDInRefsInactiveTDInK(
              k, k', k_dev_id, k'_td_id, k'_tds_state);

    Lemma_SubjObjActivate_IfActiveDevReadsNewlyActivatedTDInNewK_ThenDevCanReadTDXInK(
        k, k', k_dev_id, k'_td_id, 
        k_tds_state, k'_tds_state,
        td_ids, tdx_id_i, t_tdx_id, t_out_td_id);

    tdx_id := t_tdx_id;
    out_td_id := t_out_td_id;
}

lemma Lemma_SubjObjActivate_IfActiveDevReadsNewlyActivatedTDInNewK_ThenExistActiveTDInRefsInactiveTDInK(
    k:State, k':State,
    k_dev_id:Dev_ID, k'_td_id:TD_ID, 
    k'_tds_state:TDs_Vals
) returns (td_ids:seq<TD_ID>, tdx_id_i:int, tdx_id:TD_ID, out_td_id:TD_ID)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') > AllActiveTDs(k)

    requires k_dev_id in AllActiveDevs(k) && k_dev_id in AllActiveDevs(k')

    requires k'_td_id !in AllActiveTDs(k) && k'_td_id in AllActiveTDs(k')
    requires CanActiveDevReadActiveTD(KToKParams(k'), k'_tds_state, k_dev_id, k'_td_id)

    ensures 0 <= tdx_id_i < |td_ids| - 1 &&
            (forall j :: 0 <= j <= tdx_id_i ==> td_ids[j] in AllActiveTDs(k)) &&
            td_ids[tdx_id_i + 1] !in AllActiveTDs(k) && td_ids[tdx_id_i + 1] in AllActiveTDs(k')
    ensures tdx_id == td_ids[tdx_id_i]
    ensures out_td_id == td_ids[tdx_id_i+1]
    ensures tdx_id in AllActiveTDs(k)
    ensures out_td_id in TDIDReadsInTDCfg(k'_tds_state[tdx_id])
    ensures out_td_id !in AllActiveTDs(k) && out_td_id in AllActiveTDs(k')
    ensures |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k'_tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == k'_td_id && // last TD is the TD (<td_id>)
            td_ids[0] == KToKParams(k').subjects.devs[k_dev_id].hcoded_td_id &&
                                // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[td_ids[i]]))
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');

    td_ids := Lemma_CanActiveDevReadActiveTD_Apply(k'_params, k'_tds_state, k_dev_id, k'_td_id);

    assert |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k'_tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == k'_td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k'_params.subjects.devs[k_dev_id].hcoded_td_id &&
                                // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[td_ids[i]]));

    assert DoOwnObj(k, k_dev_id.sid, k'_params.subjects.devs[k_dev_id].hcoded_td_id.oid);
    assert k'_params.subjects.devs[k_dev_id].hcoded_td_id in AllActiveTDs(k);

    assert td_ids[|td_ids| - 1] != td_ids[0];
    assert |td_ids| > 1;

    Lemma_AChainOfElemsAcrossFromSmallSetToSuperSet_MustHaveOneElemInSmallSetAsLastElem<TD_ID>(
        td_ids, AllActiveTDs(k), AllActiveTDs(k'));
    tdx_id_i :| 0 <= tdx_id_i < |td_ids| - 1 &&
                    (forall j :: 0 <= j <= tdx_id_i ==> td_ids[j] in AllActiveTDs(k)) &&
                    td_ids[tdx_id_i + 1] !in AllActiveTDs(k) && td_ids[tdx_id_i + 1] in AllActiveTDs(k');
    tdx_id := td_ids[tdx_id_i];
    out_td_id := td_ids[tdx_id_i+1]; // The closet TD outside of AllActiveTDs(k)
}

// (needs 100s to verify)
lemma Lemma_SubjObjActivate_IfActiveDevReadsNewlyActivatedTDInNewK_ThenDevCanReadTDXInK(
    k:State, k':State,
    k_dev_id:Dev_ID, k'_td_id:TD_ID, 
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals,
    td_ids:seq<TD_ID>, tdx_id_i:int, tdx_id:TD_ID, out_td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires TDsStateGetTDIDs(k_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(k'_tds_state) == AllActiveTDs(k')
    requires AllActiveTDs(k') >= AllActiveTDs(k)
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires k_dev_id in AllActiveDevs(k) && k_dev_id in AllActiveDevs(k')

    requires k'_td_id !in AllActiveTDs(k) && k'_td_id in AllActiveTDs(k')
    requires CanActiveDevReadActiveTD(KToKParams(k'), k'_tds_state, k_dev_id, k'_td_id)

    requires AllActiveTDs(k') > AllActiveTDs(k)

    requires 0 <= tdx_id_i < |td_ids| - 1 &&
            (forall j :: 0 <= j <= tdx_id_i ==> td_ids[j] in AllActiveTDs(k)) &&
            td_ids[tdx_id_i + 1] !in AllActiveTDs(k) && td_ids[tdx_id_i + 1] in AllActiveTDs(k')
    requires tdx_id == td_ids[tdx_id_i]
    requires out_td_id == td_ids[tdx_id_i+1]
    requires tdx_id in AllActiveTDs(k)
    requires out_td_id in TDIDReadsInTDCfg(k'_tds_state[tdx_id])
    requires out_td_id !in AllActiveTDs(k) && out_td_id in AllActiveTDs(k')
    requires |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k'_tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == k'_td_id && // last TD is the TD (<td_id>)
            td_ids[0] == KToKParams(k').subjects.devs[k_dev_id].hcoded_td_id &&
                                // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[td_ids[i]]))

    ensures CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, k_dev_id, tdx_id)
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');

    // 2.1 CanActiveDevReadActiveTD(k_tds_state, k_dev_id, tdx_id) is true
    var k_td_ids := td_ids[..tdx_id_i+1];
    Lemma_Sequence_LastElemOfSubSequenceIsFromOriginalSequence(td_ids, k_td_ids, tdx_id_i+1);
    assert k_td_ids[|k_td_ids| - 1] == td_ids[tdx_id_i];
    assert k_td_ids[|k_td_ids| - 1] == tdx_id;
    assert forall td_id :: td_id in k_td_ids
           ==> td_id in k_tds_state && td_id in k'_tds_state;

    Lemma_SubjObjActivate_IfActiveDevReadsNewlyActivatedTDInNewK_ThenExistActiveTDInRefsInactiveTDInK_Private(
        k_td_ids, td_ids, tdx_id_i, k_tds_state, k'_tds_state);
    assert CanActiveDevReadActiveTD_TDRefTDWithRInChain(k_tds_state, k_td_ids);  
    assert |k_td_ids| >= 1 && 
        (forall td_id2 :: td_id2 in k_td_ids ==> td_id2 in k_tds_state) &&
                                        // A list of active TDs
        k_td_ids[|k_td_ids| - 1] == tdx_id && // last TD is the TD (<tdx_id>)
        k_td_ids[0] == k'_params.subjects.devs[k_dev_id].hcoded_td_id &&
                                       // first TD must be the hardcoded TD
        (forall i :: 0<=i<|k_td_ids| - 1 ==> k_td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[k_td_ids[i]]));
    assert k_td_ids[0] == k_params.subjects.devs[k_dev_id].hcoded_td_id;
    assert CanActiveDevReadActiveTD(k_params, k_tds_state, k_dev_id, tdx_id);
}

lemma Lemma_SubjObjActivate_IfActiveDevReadsNewlyActivatedTDInNewK_ThenExistActiveTDInRefsInactiveTDInK_Private(
    k_td_ids:seq<TD_ID>, td_ids:seq<TD_ID>, tdx_id_i:int,
    k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals
)
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
    requires forall td_id :: td_id in k_td_ids
                ==> td_id in k_tds_state && td_id in k'_tds_state

    requires |td_ids| > 1
    requires forall td_id2 :: td_id2 in td_ids ==> td_id2 in k'_tds_state
    requires forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[td_ids[i]])

    requires 0 <= tdx_id_i < |td_ids| - 1
    requires k_td_ids == td_ids[..tdx_id_i+1]

    ensures forall i :: 0<=i<|k_td_ids| - 1 ==> k_td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[k_td_ids[i]])
    ensures CanActiveDevReadActiveTD_TDRefTDWithRInChain(k_tds_state, k_td_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTD_ThenTDIsNotActivating_Property2(
    k:State, k':State, toactivate_td_ids:set<TD_ID>
)
    requires SubjObjActivate_PreConditionsOfK(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2

    requires forall td_id :: td_id in toactivate_td_ids
                ==> td_id.oid in AllObjsIDs(k.objects)
    requires forall td_id :: td_id in toactivate_td_ids
                ==> ObjPID(k, td_id.oid) == NULL

    ensures forall activating_td_id, dev_id2 :: 
                dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                activating_td_id in toactivate_td_ids
            ==> DoOwnObj(k', dev_id2.sid, activating_td_id.oid) == false
{
    Lemma_SameObjsOwnershipInSuccessiveStates(k, k');

    if (exists activating_td_id, dev_id2 :: 
                dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
                activating_td_id in toactivate_td_ids &&
               DoOwnObj(k', dev_id2.sid, activating_td_id.oid))
    {
        var activating_td_id, dev_id2 :| dev_id2 in AllActiveDevs(k) && dev_id2 in AllActiveDevs(k') &&
               activating_td_id in toactivate_td_ids &&
               DoOwnObj(k', dev_id2.sid, activating_td_id.oid);

        assert DoOwnObj(k, dev_id2.sid, activating_td_id.oid);

        //Show conflict
        assert ObjPID(k, activating_td_id.oid) != SubjPID(k, dev_id2.sid);

        assert false;
    }
}

lemma Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfDevActiveInKAndNewKCanReadTDInNewK_ThenDevCanReadTDInK_Private(
    k:State, k_tds_state:TDs_Vals, k'_tds_state:TDs_Vals, 
    td_ids:seq<TD_ID>, dev_id:Dev_ID, td_id:TD_ID
)
    requires SubjObjActivate_PreConditionsOfK(k)

    requires TDsStateGetTDIDs(k_tds_state) == KToKParams(k).all_active_tds
    requires forall td_id :: td_id in TDsStateGetTDIDs(k'_tds_state)
                ==> (td_id in TDsStateGetTDIDs(k_tds_state) ==> k'_tds_state[td_id] == k_tds_state[td_id])
        // Requirement: <k'_tds_state> contains additional active TDs (if 
        // any) from <k_tds_state>

    requires td_id in AllActiveTDs(k)
    requires dev_id in AllActiveDevs(k)

    requires |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k'_tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k'_tds_state[td_ids[i]]))

    requires forall td_id2 :: td_id2 in td_ids 
                ==> td_id2 in k_tds_state

    ensures forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[i]])
    ensures CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, dev_id, td_id)
{
    // Dafny can automatically prove this lemma
}

