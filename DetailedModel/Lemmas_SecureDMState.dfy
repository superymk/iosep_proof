include "../Abstract/Properties.dfy"
include "Properties_SecureDMState.dfy"
include "Util_Lemmas.dfy"

lemma Lemma_SecureDMState_GreenDevsDoNotModifyAnyTDs(
    ws:DM_State, k:State,
    from_tds_state:TDs_Vals, to_tds_state:TDs_Vals, dev_id:Dev_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    
    requires k == DMStateToState(ws)
    requires DM_IsSecureState_SI2(ws)
        // Property: Secure DM State

    requires dev_id in DM_DevsInGreen(ws)
    requires dev_id in AllActiveDevs(k)

    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
    requires forall td_id :: td_id in ActiveTDsState(k) <==> td_id in AllActiveTDs(k)
    requires TDsStateGetTDIDs(from_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(to_tds_state) == AllActiveTDs(k)
    requires forall td_id :: td_id in from_tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> from_tds_state[td_id] == ActiveTDsState(k)[td_id])

    requires IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(KToKParams(k), dev_id, from_tds_state, to_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(KToKParams(k), dev_id, from_tds_state, to_tds_state)

    ensures from_tds_state == to_tds_state
{
    var k_params := KToKParams(k);

    if(from_tds_state != to_tds_state)
    {
        Lemma_K_DifferentTDsState_MustIncludeOneTDWithDifferentVals(from_tds_state, to_tds_state);
        var td_id :| td_id in from_tds_state &&
                    from_tds_state[td_id] != to_tds_state[td_id];
        var tds_diff := TDsStateDiff(to_tds_state, from_tds_state);

        Lemma_K_FindAllActiveTDsStatesByDev_KParams_PreConditions_Prove(k);
        assert FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params);
        Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_Apply(k_params, dev_id, td_id, from_tds_state, tds_diff);
        var tdx_id :| tdx_id in TDsStateGetTDIDs(from_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(from_tds_state, tdx_id, td_id, tds_diff[td_id]);
        assert CanActiveDevReadActiveTD(k_params, from_tds_state, dev_id, tdx_id);

        Lemma_DMState_GreenDevsOnlyRedGreenTDs(ws, k, from_tds_state, dev_id, tdx_id);
    }
}

lemma Lemma_DMState_GreenDevsOnlyRedGreenTDs(
    ws:DM_State, k:State, tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    
    requires k == DMStateToState(ws)
 
    requires DM_IsSecureState_SI2(ws)

    requires dev_id in DM_DevsInGreen(ws)
    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
    requires td_id in TDsStateGetTDIDs(tds_state)
    requires forall td_id :: td_id in tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> tds_state[td_id] == ActiveTDsState(k)[td_id])
    requires CanActiveDevReadActiveTD(KToKParams(k), tds_state, dev_id, td_id)

    ensures DM_SubjPID(ws.subjects, dev_id.sid) == DM_ObjPID(ws.objects, td_id.oid)
    ensures td_id in DM_TDIDsInGreen(ws)
{
    var k_params := KToKParams(k);

    var td_ids := Lemma_CanActiveDevReadActiveTD_Apply(k_params, tds_state, dev_id, td_id);
    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, tds_state, dev_id, td_ids, td_id);

    var i := 0;

    // Prove td_ids[0] in DM_TDIDsInGreen(ws)
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
    assert DoOwnObj(k, dev_id.sid, td_ids[0].oid);
    assert ObjPID(k, td_ids[0].oid) != NULL;
    assert ObjPID(k, td_ids[0].oid) != ws.red_pid;
    Lemma_DM_TDIDsInGreen_Prove(ws, td_ids[0]);
    assert td_ids[0] in DM_TDIDsInGreen(ws);

    while (i < |td_ids| - 1)
        invariant i <= |td_ids| - 1

        invariant ObjPID(k, td_ids[0].oid) == ObjPID(k, td_ids[i].oid)

        invariant td_ids[i] in DM_TDIDsInGreen(ws)
    {
        if(ObjPID(k, td_ids[i].oid) != ObjPID(k, td_ids[i+1].oid))
        {
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_ids[i]);

            assert CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_ids[i]);
            assert !DM_IsSecureState_SI2(ws);
        }
        assert ObjPID(k, td_ids[i].oid) == ObjPID(k, td_ids[i+1].oid);
        i := i + 1; 
    }
}

lemma Lemma_SecureDMState_ActiveTDsReadByWimpDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(
    ws:DM_State, k:State, tds_state:TDs_Vals
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    
    requires k == DMStateToState(ws)
    requires DM_IsSecureState_SI2(ws)

    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
    requires forall td_id :: td_id in ActiveTDsState(k) <==> td_id in AllActiveTDs(k)
    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
    requires forall td_id :: td_id in tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> tds_state[td_id] == ActiveTDsState(k)[td_id])

    ensures DM_DevsInGreen(ws) <= AllActiveDevs(k)
    ensures forall dev_id2 :: dev_id2 in DM_DevsInGreen(ws)
                ==> IsDevID_SlimState(KToKParams(k).subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(KToKParams(k).subjects, dev_id2) != NULL
        // Property needed by the following property

    ensures ActiveTDsStateIsSecure(KToKParams(k), DM_DevsInGreen(ws), tds_state)
{
    var k_params := KToKParams(k);
    var active_devs := DM_DevsInGreen(ws);

    forall td_id2, dev_id | dev_id in active_devs && 
                    // The device (<dev_id>) is active
                td_id2 in TDsStateGetTDIDs(tds_state) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                    // The TD is read by the device
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
    {
        Lemma_DMState_GreenDevsOnlyRedGreenTDs(ws, k, tds_state, dev_id, td_id2);

        assert td_id2 in DM_TDIDsInGreen(ws);
        assert DM_IsSecureState_SI2(ws);

        Lemma_SecureDMState_ActiveTDsReadByWimpDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Private(ws, k, tds_state, td_id2);
    }
}

lemma Lemma_SecureDMState_ActiveTDsReadByWimpDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Private(
    ws:DM_State, k:State, tds_state:TDs_Vals, td_id2:TD_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires k == DMStateToState(ws)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
    requires forall td_id :: td_id in tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> tds_state[td_id] == ActiveTDsState(k)[td_id])
    requires td_id2 in TDsStateGetTDIDs(tds_state)
    requires td_id2 in DM_TDIDsInGreen(ws)

    requires DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id2);

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state, td_id2)
{
    var k_params := KToKParams(k);
    assert tds_state[td_id2] == ActiveTDsState(k)[td_id2];
    forall td_id3 | td_id3 in tds_state[td_id2].trans_params_tds
        ensures td_id3 in k_params.objs_td_ids &&
                td_id3 !in k_params.hcoded_td_ids &&
                (ObjPID_SlimState(k_params.objs_pids, td_id3.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) || 
                        // The TD (<td_id2>) contains a transfer, the target TD 
                        // (<td_id3>) must be in the same partition with the TD
                 tds_state[td_id2].trans_params_tds[td_id3].amodes == {})
    {
        // Dafny can automatically prove this statement
    }
}