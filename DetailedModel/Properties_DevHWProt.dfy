include "Syntax.dfy"
include "Utils.dfy"
include "Properties_ValidDMState.dfy"
include "./utils/Collections.dfy"
include "K_AdditionalPropertiesLemmas.dfy"
include "Util_Lemmas.dfy"
include "Lemmas_Ops_Common.dfy"

//******** Underlying Functions provided by HW protection mechanisms ********//                                 
// HW protection mechanisms modify the red TDs, such 
// that the reachable states of red TDs fulfill following property:
// If a device in red partition has read transfer to a red TD, then the TD only  
// has transfers to red objects at any time
// Note: We do not use the property "Devices in red partition only have 
// transfers to red objects", because it is more abstract for HW protection
// mechanisms
// Note: In some I/O architectures, we expect the I/O hardware security 
// mechansims provide this function, e.g., via IOMMU (including interrupt 
// remapping) and ACS. In other I/O architectures, WK code needs to implement 
// additional checks to provide this function
function method {:axiom} DevHWProt(ws:DM_State) : DM_State
    requires DM_IsValidState_SubjsObjsPIDs(ws)
        
    requires DM_IsValidState_DevsActivateCond(ws)
        // Requirement: Devices can be active or inactive, as long as they
        // fulfill DM_IsValidState_DevsActivateCond

    ensures P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(ws, DevHWProt(ws))
    ensures P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(ws, DevHWProt(ws))
        // Property: <dev_hwprot> only modifies values of red TDs (excluding 
        // hardcoded TDs)

    ensures DevHWProt_ReturnGoodSnapshotOfRedTDs(ws, DevHWProt(ws))


predicate DevHWProt_ReturnGoodSnapshotOfRedTDs(in_ws:DM_State, out_ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(in_ws)

    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(in_ws, out_ws)
    requires P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(in_ws, out_ws)

    ensures DevHWProt_ReturnGoodSnapshotOfRedTDs(in_ws, out_ws)
                ==> P_DMAndNewDM_SameObjectID(in_ws, out_ws)

    ensures DM_IsValidState_SubjsObjsPIDs(out_ws)
    ensures DevHWProt_ReturnGoodSnapshotOfRedTDs(in_ws, out_ws)
                ==> P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(out_ws)
{
    // Prove DM_IsValidState_SubjsObjsPIDs(out_ws)
    Lemma_NewDM_AlwaysFulfillMostValidityProperties(in_ws, out_ws);

    Lemma_NewDM_SameSubjObjIDs(in_ws, out_ws);
    Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(in_ws, out_ws);

    // Prove DM_IsValidState_SubjsObjsPIDs(out_ws)
    Lemma_NewDM_FulFillIsValidState_SubjsOwnObjsThenInSamePartition_IfPIDsAreUnchanged(in_ws, out_ws);
    assert DM_IsValidState_SubjsObjsPIDs(out_ws);

    P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(out_ws)
        // Property: The closure from the snapshot enforces: If a red device
        // has read transfer to a TD, then the TD only has transfers to red
        // objects at any time
}




//******** Major properties of DevDevHWProt ********//
predicate P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(good_ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
{
    var good_k := DMStateToState(good_ws);
    var good_k_params := KToKParams(good_k);
    var good_k_tds_state := ActiveTDsState_SlimState(good_k.objects.tds);

    Lemma_ValidK_FulFills_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(good_k);
    Lemma_ValidDMStateToState_DMDevsInRedAreActiveInK(good_ws, good_k);

    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(good_k.objects.tds) &&
                    (good_k_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2)))
                                    // Forall tds_state2, good_k_tds_state -->* tds_state2
                ==> (forall td_id2, dev_id ::
                            dev_id in DM_DevsInRed(good_ws) && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(good_k_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(good_k_params, tds_state2, td_id2, good_ws.red_pid)))
                                // The TD only refs objects in red
}

predicate P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
{
    var good_k := DMStateToState(good_ws);
    var good_k_params := KToKParams(good_k);
    var good_k_tds_state := ActiveTDsState_SlimState(good_k.objects.tds);

    Lemma_ValidK_FulFills_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(good_k);
    Lemma_ValidDMStateToState_DMDevsInRedAreActiveInK(good_ws, good_k);
    Lemma_P_DevHWProt_TDsReadByRedOnlyDevsHaveTransfersToRedObjsAtAnyTime_FulfillPreConditions(good_k);

    P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Value(good_ws)
}



//******** Relationship between DM_State and DM_State as the key and value of the map <dev_hwprot> ********//
predicate P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(in_ws:DM_State, out_ws:DM_State)
{
    // Same subjects
    (in_ws.subjects == out_ws.subjects) &&

    // Same <pids>
    (in_ws.pids == out_ws.pids) &&

    // Same <red_pid>
    (in_ws.red_pid == out_ws.red_pid) &&

    // Same <devs_activatecond>
    (in_ws.devs_activatecond == out_ws.devs_activatecond) &&

    // Same <tds_to_all_states>
    (in_ws.tds_to_all_states == out_ws.tds_to_all_states) &&

    (true)
}

predicate P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_Objs(in_ws:DM_State, out_ws:DM_State)
    requires P_AllHCodedTDsAreObjs(in_ws)
{
    // Same object IDs with DM state
    (MapGetKeys(out_ws.objects.tds) == MapGetKeys(in_ws.objects.tds) &&
     MapGetKeys(out_ws.objects.fds) == MapGetKeys(in_ws.objects.fds) &&
     MapGetKeys(out_ws.objects.dos) == MapGetKeys(in_ws.objects.dos)) &&

    // FDs and DOs are unchanged
    ((forall id :: id in in_ws.objects.fds ==> in_ws.objects.fds[id] == out_ws.objects.fds[id]) &&
             (forall id :: id in in_ws.objects.dos ==> in_ws.objects.dos[id] == out_ws.objects.dos[id])) &&

    // Hardcoded TDs are unchanged
    (forall id :: id in DM_AllHCodedTDIDs(in_ws.subjects) ==> in_ws.objects.tds[id] == out_ws.objects.tds[id]) &&

    // PIDs of all TDs are unchanged
    (forall id :: id in in_ws.objects.tds ==> in_ws.objects.tds[id].pid == out_ws.objects.tds[id].pid) &&

    // TDs not in red preserve their states
    (forall id :: id in in_ws.objects.tds && in_ws.objects.tds[id].pid != in_ws.red_pid ==> in_ws.objects.tds[id] == out_ws.objects.tds[id]) &&

    (true)
}



//******** Utility Predicates ********//
predicate P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition1(ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
{
    var k := DMStateToState(ws);

    forall dev_id :: dev_id in DM_DevsInRed(ws) ==> dev_id in k.subjects.devs && SubjPID_DevID(k, dev_id) != NULL
}

predicate P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition2(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && 
            IsValidState_Partitions(k)
{
    forall tds_state2, td_id2, dev_id :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects.tds) &&
                dev_id in k.subjects.devs && SubjPID_DevID(k, dev_id) != NULL && 
                td_id2 in TDsStateGetTDIDs(tds_state2) 
            ==> td_id2 in k.objects.tds &&
                CanActiveDevReadActiveTD_PreConditions(KToKParams(k), tds_state2, dev_id, td_id2)
}

predicate P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Value(good_ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition1(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition2(DMStateToState(good_ws))
{
    var good_k := DMStateToState(good_ws);
    var good_k_params := KToKParams(good_k);
    var good_k_tds_state := ActiveTDsState_SlimState(good_k.objects.tds);

    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(good_k.objects.tds) &&
                    (good_k_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2)))
                                    // Forall tds_state2, good_k_tds_state -->* tds_state2
                ==> (forall td_id2, dev_id ::
                            dev_id in DM_DevsInRed(good_ws) && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(good_k_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(good_k_params, tds_state2, td_id2)))
                                // The TD only includes valid and secure transfers to objects
}




//******** Utility Functions ********//
function method DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID, red_pid:Partition_ID
) : bool
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active
{
    if (forall td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
            ==> td_id2 in k_params.objs_td_ids &&
                td_id2 !in k_params.hcoded_td_ids &&
                (ObjPID_SlimState(k_params.objs_pids, td_id2.oid) == red_pid || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_tds[td_id2].amodes == {})) &&
                        // The TD does not contain a transfer to the target TD
        (forall fd_id2 :: fd_id2 in tds_state[td_id].trans_params_fds
            ==> fd_id2 in k_params.objs_fd_ids &&
                (ObjPID_SlimState(k_params.objs_pids, fd_id2.oid) == red_pid ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_fds[fd_id2].amodes == {})) &&
                        // The TD does not contain a transfer to the target FD
        (forall do_id2 :: do_id2 in tds_state[td_id].trans_params_dos
            ==> do_id2 in k_params.objs_do_ids && 
                (ObjPID_SlimState(k_params.objs_pids, do_id2.oid) == red_pid ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_dos[do_id2].amodes == {}))
                        // The TD does not contain a transfer to the target DO
    then true
    else false
}




//******** Utility Lemmas ********//
lemma Lemma_P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Apply(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(ws)

    requires (tds_state == ActiveTDsState(k)) ||
            (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state) &&
             IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state))

    ensures forall dev_id2 :: dev_id2 in DM_DevsInRed(ws)
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
    ensures ActiveTDsStateIsSecure(k_params, DM_DevsInRed(ws), tds_state)
{
    Lemma_ValidK_FulFills_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k);
    Lemma_ValidDMStateToState_DMDevsInRedAreActiveInK(ws, k);
    Lemma_P_DevHWProt_TDsReadByRedOnlyDevsHaveTransfersToRedObjsAtAnyTime_FulfillPreConditions(k);

    assert P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Value(ws);
}

lemma Lemma_P_DevHWProt_TDsReadByRedOnlyDevsHaveTransfersToRedObjsAtAnyTime_FulfillPreConditions(k:State)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && 
            IsValidState_Partitions(k)

    ensures P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition2(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Prove(
    good_ws:DM_State, good_k:State, good_k_params:ReachableTDsKParams, good_k_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)

    requires good_k == DMStateToState(good_ws)
    requires good_k_params == KToKParams(good_k)
    requires good_k_tds_state == ActiveTDsState_SlimState(good_k.objects.tds)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition1(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_PreCondition2(DMStateToState(good_ws))
    requires forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(good_k.objects.tds) &&
                    (good_k_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2)))
                                    // Forall tds_state2, good_k_tds_state -->* tds_state2
                ==> ActiveTDsStateIsSecure(good_k_params, DM_DevsInRed(good_ws), tds_state2)
    
    ensures P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)
{
    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(good_k.objects.tds) &&
                    (good_k_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2)))
                                    // Forall tds_state2, good_k_tds_state -->* tds_state2
        ensures (forall td_id2, dev_id ::
                            dev_id in DM_DevsInRed(good_ws) && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(good_k_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(good_k_params, tds_state2, td_id2))
    {
        assert ActiveTDsStateIsSecure(good_k_params, DM_DevsInRed(good_ws), tds_state2);
    }

    assert P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Value(good_ws);
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed_ThenDoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartitionIsFalse(
    k_params:ReachableTDsKParams, tds_state:TDs_Vals, td_id:TD_ID, red_pid:Partition_ID
)
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    requires ObjPID_SlimState(k_params.objs_pids, td_id.oid) == red_pid

    requires DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_id, red_pid)

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id)
{
    // Dafny can automatically prove this lemma
}