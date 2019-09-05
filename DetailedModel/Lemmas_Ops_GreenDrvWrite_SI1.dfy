include "Lemmas_ClosuresCombination.dfy"
include "Properties_DevHWProt.dfy"
include "Properties_SecureDMState.dfy"





//******** Main Lemmas ********//
// (needs 30s to verify)
lemma Lemma_DM_SI1HoldsIfRedTDsAreUnchanged(
    ws:DM_State, k:State, ws':DM_State, k':State
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)
        // Requirement: IDs and ownerships are not changed
    requires MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds)
    requires MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds)
    requires MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos)

    requires ws'.red_pid == ws.red_pid
    requires ws.red_pid != NULL

    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)
        // Requirement: Objects' PIDs are not changed
    requires forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_SubjPID(ws'.subjects, s_id) == DM_SubjPID(ws.subjects, s_id)
        // Requirement: Subjects' PIDs are not changed
    requires DM_DevsInRed(ws') == DM_DevsInRed(ws)

    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')
    requires KToKParams(k) == KToKParams(k')

    requires forall td_id :: td_id in DM_TDIDsInRed(ws')
                ==> DM_IsSameTD(ws'.objects, ws.objects, td_id)
        // Requirement: TDs in red are unmodified
    requires DM_IsSecureState_SI2(ws')
        // Requirement: Green TDs are good
                
    requires DM_IsSecureState_SI1(ws)
    requires DM_IsSecureState_SI2(ws)
    requires ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), ActiveTDsState_SlimState(k.objects.tds))

    requires DM_IsSecureState_SI2(ws')

    ensures DM_IsSecureState_SI1(ws')
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');
    assert k'_params == k_params;

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k); 
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws', k'); 
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws', k');
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    var k_tds_state := ActiveTDsState_SlimState(k.objects.tds);
    var k'_tds_state := ActiveTDsState_SlimState(k'.objects.tds);

    // Prove ReachableTDsStates_PreConditionsOfK
    Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_ProveReachableTDsStates_PreConditionsOfK(ws', k', k'_params);
    assert ReachableTDsStates_PreConditionsOfK(k'_params, AllObjsIDs(k'.objects));

    // Prove equal DM_TDIDsInGreen and DM_TDIDsInRed
    Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_ProveEqualDMTDIDsInGreenRed(ws, ws');
    assert DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws);
    assert DM_TDIDsInRed(ws') == DM_TDIDsInRed(ws);

    // Prove WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs
    var k'_os_tds_state0 := MaskTDsState(k'_tds_state, DM_TDIDsInGreen(ws'));
    var k'_wimps_tds_state0 := MaskTDsState(k'_tds_state, DM_TDIDsInRed(ws'));
    assert WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k'_params,
                DM_TDIDsInRed(ws'), DM_TDIDsInGreen(ws'),
                ActiveTDsState(k'), k'_os_tds_state0, k'_wimps_tds_state0);

    // Prove k_os_tds_state0 == k'_os_tds_state0
    assert forall td_id :: td_id in DM_TDIDsInGreen(ws) ==> td_id in k_tds_state;
    var k_os_tds_state0 := MaskTDsState(k_tds_state, DM_TDIDsInGreen(ws));
    Lemma_RedTDsStateIsSame_IfRedTDsAreUnmodified(ws, k, ws', k', k_os_tds_state0, k'_os_tds_state0);
    assert k_os_tds_state0 == k'_os_tds_state0;

    // Prove WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
    //            k'_params, AllObjsIDs(k'.objects), DM_DevsInRed(ws'), k'_os_tds_state0)
    Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState(ws, k, k_params, k_os_tds_state0);
    assert WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInRed(ws), k_os_tds_state0);
    assert WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k'_params, AllObjsIDs(k'.objects), DM_DevsInRed(ws'), k'_os_tds_state0);

    // Prove WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
    //            k'_params, AllObjsIDs(k'.objects), DM_DevsInGreen(ws'), k'_wimps_tds_state0)
    Lemma_GreenDrvWrite_TDsInGreenPartitionHasNoInvalidRefs_IfDMIsSecureState(ws', k', k'_params, k'_wimps_tds_state0);
    assert WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k'_params, AllObjsIDs(k'.objects), DM_DevsInGreen(ws'), k'_wimps_tds_state0);

    // Prove main property
    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k'.objects.tds) &&
                    (k'_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, 
                                DM_DevsInRed(ws'), k'_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                DM_DevsInRed(ws'), k'_tds_state, tds_state2)))
                                    // Forall tds_state2, k'_tds_state -->* tds_state2
        ensures (forall td_id2, dev_id ::
                            dev_id in DM_DevsInRed(ws') && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k'_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k'_params, tds_state2, td_id2, ws'.red_pid))
                                // The TD only refs objects in red
    {
        if(k'_tds_state == tds_state2)
        {
            assert ActiveTDsState(k') == tds_state2;
        }
        else
        {
            Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_IfTDsStateCanBeReachedWithRedDevs_ThenTDsStateCanBeReachedWithActiveDevs(ws', k', k'_params,
                k'_tds_state, tds_state2);
        }
        assert ActiveTDsState(k') == tds_state2 ||
                (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, AllActiveDevs(k'), ActiveTDsState(k'), tds_state2) &&
                 IsActiveTDsStateReachActiveTDsStateInChain(k'_params, AllActiveDevs(k'), ActiveTDsState(k'), tds_state2));

        Lemma_WKStateToState_AllReachableStatesAreSecure(ws', k', k'_params,
            tds_state2, k'_os_tds_state0, k'_wimps_tds_state0);

        Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_ProveDevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(
            ws', k', k'_params, k'_tds_state, tds_state2);
    }
}




//******** Private Lemmas of Main Lemmas ********//
lemma Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_ProveReachableTDsStates_PreConditionsOfK(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires IsValidState_Subjects(k') && IsValidState_Objects(k') && IsValidState_Partitions(k') && IsValidState_SubjsOwnObjsThenInSamePartition(k')
    requires k'_params == KToKParams(k')

    ensures forall dev_id2 :: dev_id2 in k'_params.subjects.devs
                ==> dev_id2 in k'_params.hcoded_tds
    ensures ReachableTDsStates_PreConditionsOfK(k'_params, AllObjsIDs(k'.objects))
{
    Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions1(ws', k', k'_params);
}

lemma Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_ProveEqualDMTDIDsInGreenRed(
    ws:DM_State, ws':DM_State
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires ws'.red_pid == ws.red_pid

    //requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)

    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)
        // Requirement: Objects' PIDs are not changed
     
    ensures DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
    ensures DM_TDIDsInRed(ws') == DM_TDIDsInRed(ws)
{
    Lemma_DM_SameIDsIffSameInternalIDs();

    var ws_green_td_ids := DM_TDIDsInGreen(ws);
    var ws'_green_td_ids := DM_TDIDsInGreen(ws');
    forall td_id | td_id in ws_green_td_ids
        ensures td_id in ws'_green_td_ids
    {
        assert td_id in DM_AllTDIDs(ws'.objects) &&
               DM_ObjPID(ws'.objects, td_id.oid) != NULL &&
               DM_ObjPID(ws'.objects, td_id.oid) != ws'.red_pid;
        Lemma_DM_TDIDsInGreen_Prove(ws', td_id);
        assert td_id in ws'_green_td_ids;
    }
    
    forall td_id | td_id in ws'_green_td_ids
        ensures td_id in ws_green_td_ids
    {
        assert td_id in DM_AllTDIDs(ws.objects) &&
               DM_ObjPID(ws.objects, td_id.oid) != NULL &&
               DM_ObjPID(ws.objects, td_id.oid) != ws.red_pid;
        Lemma_DM_TDIDsInGreen_Prove(ws, td_id);
        assert td_id in ws_green_td_ids;
    }
    
    Lemma_Set_Equality(ws'_green_td_ids, ws_green_td_ids);
    
    var ws_red_td_ids := DM_TDIDsInRed(ws);
    var ws'_red_td_ids := DM_TDIDsInRed(ws');
    forall td_id | td_id in ws_red_td_ids
        ensures td_id in ws'_red_td_ids
    {
        assert td_id in DM_AllTDIDs(ws'.objects) &&
               DM_ObjPID(ws'.objects, td_id.oid) == ws'.red_pid;
        Lemma_DM_TDIDsInRed_Prove(ws', td_id);
        assert td_id in ws'_red_td_ids;
    }
    
    forall td_id | td_id in ws'_red_td_ids
        ensures td_id in ws_red_td_ids
    {
        assert td_id in DM_AllTDIDs(ws.objects) &&
               DM_ObjPID(ws.objects, td_id.oid) == ws.red_pid;
        Lemma_DM_TDIDsInRed_Prove(ws, td_id);
        assert td_id in ws_red_td_ids;
    }
    
    Lemma_Set_Equality(ws'_red_td_ids, ws_red_td_ids);
}

lemma Lemma_RedTDsStateIsSame_IfRedTDsAreUnmodified(ws:DM_State, k:State, ws':DM_State, k':State, k_os_tds_state0:TDs_Vals, k'_os_tds_state0:TDs_Vals)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)
        // Requirement: IDs and ownerships are not changed
    requires MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds)
    requires MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds)
    requires MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos)

    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
    requires DM_TDIDsInRed(ws') == DM_TDIDsInRed(ws)

    requires k_os_tds_state0 == MaskTDsState(ActiveTDsState_SlimState(k.objects.tds), DM_TDIDsInGreen(ws))
    requires k'_os_tds_state0 == MaskTDsState(ActiveTDsState_SlimState(k'.objects.tds), DM_TDIDsInGreen(ws'))

    requires forall td_id :: td_id in DM_TDIDsInRed(ws')
                ==> DM_IsSameTD(ws'.objects, ws.objects, td_id)

    ensures k_os_tds_state0 == k'_os_tds_state0
{
    if (k_os_tds_state0 != k'_os_tds_state0)
    {
        var td_id :| td_id in k_os_tds_state0 && k'_os_tds_state0[td_id] != k_os_tds_state0[td_id];

        assert td_id in DM_TDIDsInRed(ws);
    }
}

lemma Lemma_DM_AllTDsHaveSecureTransfersInMaskedTDsState(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    tds_state2:TDs_Vals, expanded_tds_state2:TDs_Vals, red_td_ids:set<TD_ID>, 
    red_devs:set<Dev_ID>, dev_id:Dev_ID, td_ids:seq<TD_ID>, target_td_id:TD_ID
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires red_td_ids == DM_TDIDsInRed(ws)
    requires red_devs == DM_DevsInRed(ws)

    requires red_td_ids <= TDsStateGetTDIDs(tds_state2)
    requires TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(expanded_tds_state2)
    requires forall td_id :: td_id in red_td_ids
                ==> tds_state2[td_id] == expanded_tds_state2[td_id]
    requires forall td_id :: td_id in tds_state2 && td_id !in red_td_ids
                ==> tds_state2[td_id] == TD_Val(map[], map[], map[])
        // Requirement: Relationships between tds_state2, expanded_tds_state2, and red_td_ids

    requires red_devs <= AllActiveDevs(k)
    requires dev_id in red_devs
        // Requirement: The device (<dev_id>) is a device in the red partition

    requires P_CanActiveDevReadActiveTD_Def(k_params, tds_state2, dev_id, td_ids, target_td_id)
        // Requirement: From Lemma_CanActiveDevReadActiveTD_Apply

    requires (forall td_id2, dev_id :: dev_id in red_devs && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(expanded_tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, expanded_tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, expanded_tds_state2, td_id2, ws.red_pid))
        // Requirement: From DM_IsSecureState_SI1

    ensures P_CanActiveDevReadActiveTD_Def(k_params, expanded_tds_state2, dev_id, td_ids, target_td_id)
    ensures CanActiveDevReadActiveTD(k_params, expanded_tds_state2, dev_id, target_td_id)
        // Property: Device have read transfers to the TD under expanded_tds_state2
    ensures forall td_id :: td_id in td_ids
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id)
    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, target_td_id)
        // Property: All TDs in <td_ids> have secure transfers only
    ensures forall td_id :: td_id in td_ids
                ==> td_id in red_td_ids
{
    if(|td_ids| == 1)
    {
        assert target_td_id == td_ids[0];
        assert target_td_id == k_params.subjects.devs[dev_id].hcoded_td_id;

        Lemma_DM_IsValidState_SubjsOwnObjsThenInSamePartition_Property(ws);
        assert DM_DoOwnObj(ws.subjects, dev_id.sid, target_td_id.oid);
        assert target_td_id in red_td_ids;

        // Prove CanActiveDevReadActiveTD(k_params, expanded_tds_state2, dev_id, target_td_id)
        assert CanActiveDevReadActiveTD(k_params, expanded_tds_state2, dev_id, target_td_id);
        
        // Prove !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, target_td_id)
        assert tds_state2[target_td_id] == expanded_tds_state2[target_td_id];

        assert DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, expanded_tds_state2, target_td_id, ws.red_pid);
        Lemma_DM_ActiveTDOnlyHasValidTransfers_IfDevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(ws, k, k_params,
            tds_state2, expanded_tds_state2, target_td_id);
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, target_td_id);
    }
    else
    {
        assert |td_ids| > 1;

        var new_td_ids := td_ids[..|td_ids|-1];
        var new_target_td_id := new_td_ids[|new_td_ids|-1];

        Lemma_DM_AllTDsHaveSecureTransfersInMaskedTDsState(ws, k, k_params, tds_state2, expanded_tds_state2, red_td_ids, 
            red_devs, dev_id, new_td_ids, new_target_td_id);

        // Prove CanActiveDevReadActiveTD(k_params, expanded_tds_state2, dev_id, target_td_id)
        assert CanActiveDevReadActiveTD(k_params, expanded_tds_state2, dev_id, target_td_id);

        // Prove target_td_id in red_td_ids
        assert target_td_id in TDIDReadsInTDCfg(expanded_tds_state2[new_target_td_id]);
        assert target_td_id in red_td_ids;

        // Prove !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, target_td_id)
        assert tds_state2[target_td_id] == expanded_tds_state2[target_td_id];

        assert DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, expanded_tds_state2, target_td_id, ws.red_pid);
        Lemma_DM_ActiveTDOnlyHasValidTransfers_IfDevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(ws, k, k_params,
            tds_state2, expanded_tds_state2, target_td_id);
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, target_td_id);

        Lemma_SequenceHighlightLastElem(td_ids);
        forall td_id | td_id in td_ids
            ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id)
        {
            if(td_id in new_td_ids)
            {
                assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id);
            }
            else
            {
                assert td_id == target_td_id;
                assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id);
            }
        }
    }
}

predicate P_Lemma_AllTDsStatesInKOSTDsStatesAreSecure_Properties(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    k_os_tds_states:seq<TDs_Vals>, k_tds_state:TDs_Vals, k_wimps_tds_state0:TDs_Vals, 
    red_devs:set<Dev_ID>
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)
    requires k_wimps_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInRed(ws))
    requires red_devs == DM_DevsInRed(ws)

    requires forall tds_state2 :: tds_state2 in k_os_tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
{
    (forall tds_state2, expanded_tds_state2 :: tds_state2 in k_os_tds_states &&
                    expanded_tds_state2 == MergeTDsState(tds_state2, k_wimps_tds_state0, DM_TDIDsInGreen(ws))
                ==> expanded_tds_state2 == k_tds_state ||
                    (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        red_devs, k_tds_state, expanded_tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                        red_devs, k_tds_state, expanded_tds_state2))) &&
        // Property 1: k_tds_state -->* expanded_tds_state2
    (forall tds_state, td_id :: tds_state in k_os_tds_states &&
                    td_id in tds_state && td_id !in DM_TDIDsInRed(ws)
                ==> tds_state[td_id] == TD_Val(map[], map[], map[])) &&
        // Property 2: In <k_os_tds_states>, green TDs have empty content
    (forall tds_state2 :: tds_state2 in k_os_tds_states
                ==> ActiveTDsStateIsSecure(k_params, red_devs, tds_state2)) &&
        // Property 3: All TDs' states in <k_os_tds_states> is secure

    (true)
}

lemma Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    k_os_tds_states:seq<TDs_Vals>, k_os_tds_state0:TDs_Vals, k_tds_state:TDs_Vals,
    red_devs:set<Dev_ID>, k_devs:seq<Dev_ID>, last_k_os_tds_state:TDs_Vals, k_wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)
    requires k_os_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInGreen(ws))
    requires k_wimps_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInRed(ws))
    requires red_devs == DM_DevsInRed(ws)
    
    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)

    requires (|k_os_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k_os_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)) &&
                |k_devs| == |k_os_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in red_devs) &&
                k_os_tds_states[0] == k_os_tds_state0 && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|k_os_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            k_devs[i], k_os_tds_states[i], k_os_tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            k_devs[i], k_os_tds_states[i], k_os_tds_states[i+1])))
                    // k_os_tds_state0 -->1+ k_os_tds_states[|k_os_tds_states| - 1]
        // Requirement: k_os_tds_state0 -->* k_os_tds_states[|k_os_tds_states| - 1]

    requires k_os_tds_states[0] == k_os_tds_state0  
        // First TDs' state is the <k_os_tds_state0>
    requires k_os_tds_states[|k_os_tds_states|-1] == last_k_os_tds_state
        // Requirement: Last TDs' state is <last_k_os_tds_state>

    requires DM_AllActiveDevs(ws.subjects) == DM_DevsInRed(ws) + DM_DevsInGreen(ws)
    requires DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k)
        // Requirement: Properties better to be proved in the caller

    requires forall td_id, td_id2 :: td_id in k_wimps_tds_state0 && td_id2 in k_wimps_tds_state0[td_id].trans_params_tds
                ==> W !in k_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirement: From DM_IsSecureState_SI1

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)

    ensures P_Lemma_AllTDsStatesInKOSTDsStatesAreSecure_Properties(ws, k, k_params,
                k_os_tds_states, k_tds_state, k_wimps_tds_state0, red_devs)        
{
    if(|k_os_tds_states| == 2)
    {
        Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoElems(ws, k, k_params, 
            k_os_tds_states, k_os_tds_state0, k_tds_state, 
            red_devs, k_devs, last_k_os_tds_state, k_wimps_tds_state0);
    }
    else
    {
        var last_k_os_tds_states := k_os_tds_states[..|k_os_tds_states|-1];
        var last_k_devs := k_devs[..|k_devs|-1];
        Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems(ws, k, k_params, 
            last_k_os_tds_states, k_os_tds_state0, k_tds_state, 
            red_devs, last_k_devs, last_k_os_tds_states[|last_k_os_tds_states|-1], k_wimps_tds_state0);

        Lemma_AllTDsStatesInKOSTDsStatesAreSecure_MultiElems(ws, k, k_params, 
            k_os_tds_states, k_os_tds_state0, k_tds_state, 
            red_devs, k_devs, last_k_os_tds_state, k_wimps_tds_state0);
    }
}

// (needs 40s to verify)
lemma Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, k_os_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_os_tds_state0 == MaskTDsState(ActiveTDsState_SlimState(k.objects.tds), DM_TDIDsInGreen(ws))

    requires DM_IsSecureState_SI1(ws)
    requires DM_IsSecureState_SI2(ws)
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), ActiveTDsState_SlimState(k.objects.tds))

    ensures WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInRed(ws), k_os_tds_state0)
{
    var red_devs := DM_DevsInRed(ws);
    var k_tds_state := ActiveTDsState_SlimState(k.objects.tds);
    var k_wimps_tds_state0 := MaskTDsState(ActiveTDsState_SlimState(k.objects.tds), DM_TDIDsInRed(ws));

    assert (forall td_id, td_id2 :: td_id in DM_TDIDsInGreen(ws) && td_id2 in k_wimps_tds_state0[td_id].trans_params_tds
        ==> W !in k_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes);

    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds &&
                    (k_os_tds_state0 == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                red_devs, k_os_tds_state0, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                                red_devs, k_os_tds_state0, tds_state2)))
                                    // k_os_tds_state0 -->* tds_state2
        ensures forall td_id2, dev_id :: 
                        dev_id in red_devs && 
                            // The device (<dev_id>) is an active OS device
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2) &&
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)
    {
        Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveCanActiveDevReadActiveTD_PreConditions(
            ws, k, k_params, tds_state2);
        assert forall td_id2, dev_id :: dev_id in red_devs && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2);
    
        var expanded_tds_state2 := MergeTDsState(tds_state2, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
        if(tds_state2 != k_os_tds_state0)
        {
            var k_os_tds_states, k_devs := Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Apply(
                                        k_params, red_devs, k_os_tds_state0, tds_state2);
            Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems(ws, k, k_params,
                k_os_tds_states, k_os_tds_state0, k_tds_state,
                red_devs, k_devs, tds_state2, k_wimps_tds_state0);
        }
        else
        {
            assert k_os_tds_state0 == tds_state2;
            Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveExpandedTDsState2EqualsKTDsState(
                ws, k, k_params, k_tds_state, k_wimps_tds_state0, tds_state2, expanded_tds_state2);
            assert expanded_tds_state2 == k_tds_state;

            Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveKOSTDSState0IsSecure(
                ws, k, k_params, k_tds_state, tds_state2);
            assert ActiveTDsStateIsSecure(k_params, red_devs, tds_state2);
        }

        Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_Private(
            ws, k, k_params, red_devs, tds_state2);
    }
}

lemma Lemma_AllTDsStatesInNewKGreenTDsStatesAreSecure_TwoOrMoreElems(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams,
    k'_wimps_tds_states:seq<TDs_Vals>, k'_tds_state:TDs_Vals,
    green_devs:set<Dev_ID>, k'_devs:seq<Dev_ID>, k'_wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires k'_params == KToKParams(k')
    requires k'_tds_state == ActiveTDsState_SlimState(k'.objects.tds)
    requires k'_wimps_tds_state0 == MaskTDsState(k'_tds_state, DM_TDIDsInRed(ws'))
    requires green_devs == DM_DevsInGreen(ws')
    
    requires DM_TDIDsInGreen(ws') <= AllActiveTDs(k')

    requires (|k'_wimps_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k'_wimps_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')) &&
                |k'_devs| == |k'_wimps_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k'_devs ==> dev_id2 in green_devs) &&
                k'_wimps_tds_states[0] == k'_wimps_tds_state0 && // first TDs' state is the <ActiveTDsState(k'')>
                (forall i :: 0<=i<|k'_wimps_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k'_params,
                            k'_devs[i], k'_wimps_tds_states[i], k'_wimps_tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params,
                            k'_devs[i], k'_wimps_tds_states[i], k'_wimps_tds_states[i+1])))
                    // k'_wimps_tds_state0 -->1+ k'_wimps_tds_states[|k'_wimps_tds_states| - 1]
        // Requirement: k'_wimps_tds_state0 -->* k'_wimps_tds_states[|k'_wimps_tds_states| - 1]

    requires k'_wimps_tds_states[0] == k'_wimps_tds_state0
        // First TDs' state is the <k'_wimps_tds_state0>

    requires DM_AllActiveDevs(ws'.subjects) == DM_DevsInRed(ws') + DM_DevsInGreen(ws')
    requires DM_AllActiveDevs(ws'.subjects) == AllActiveDevs(k')
        // Requirement: Properties better to be proved in the caller

    requires forall td_id, td_id2 :: td_id in k'_wimps_tds_state0 && td_id2 in k'_wimps_tds_state0[td_id].trans_params_tds
                ==> W !in k'_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes

    ensures forall tds_state2 :: tds_state2 in k'_wimps_tds_states
                ==> tds_state2 == k'_wimps_tds_state0
{
    if(|k'_wimps_tds_states| == 2)
    {
        var dev_id := k'_devs[0];
        var from_wimps_tds_state := k'_wimps_tds_states[0];
        var to_wimps_tds_state := k'_wimps_tds_states[1];

        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, from_wimps_tds_state, to_wimps_tds_state);
        Lemma_AllTDsStatesInNewKGreenTDsStatesAreSecure_TwoOrMoreElems_ProveTDsStateIsUnchanged(ws', k', k'_params, dev_id, from_wimps_tds_state, to_wimps_tds_state);
        assert from_wimps_tds_state == to_wimps_tds_state;
    }
    else
    {
        assert |k'_wimps_tds_states| > 2;

        var last_k'_wimps_tds_states := k'_wimps_tds_states[..|k'_wimps_tds_states|-1];
        var last_k'_devs := k'_devs[..|k'_devs|-1];
        Lemma_AllTDsStatesInNewKGreenTDsStatesAreSecure_TwoOrMoreElems(ws', k', k'_params, 
            last_k'_wimps_tds_states, k'_tds_state, 
            green_devs, last_k'_devs, k'_wimps_tds_state0);

        var dev_id := k'_devs[|k'_devs|-1];
        var from_wimps_tds_state := k'_wimps_tds_states[|k'_wimps_tds_states|-2];
        var to_wimps_tds_state := k'_wimps_tds_states[|k'_wimps_tds_states|-1];

        Lemma_SequenceHighlightLastElemOfSubSeq(k'_wimps_tds_states, last_k'_wimps_tds_states);
        assert from_wimps_tds_state == last_k'_wimps_tds_states[|last_k'_wimps_tds_states|-1];

        // Prove no write in TDs in <from_wimps_tds_state>
        assert from_wimps_tds_state in last_k'_wimps_tds_states;
        assert from_wimps_tds_state == k'_wimps_tds_state0;
        assert forall td_id, td_id2 :: td_id in k'_wimps_tds_state0 && td_id2 in k'_wimps_tds_state0[td_id].trans_params_tds
                ==> W !in k'_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes;
        assert forall td_id, td_id2 :: td_id in from_wimps_tds_state && td_id2 in from_wimps_tds_state[td_id].trans_params_tds
                ==> W !in from_wimps_tds_state[td_id].trans_params_tds[td_id2].amodes;

        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, from_wimps_tds_state, to_wimps_tds_state);
        Lemma_AllTDsStatesInNewKGreenTDsStatesAreSecure_TwoOrMoreElems_ProveTDsStateIsUnchanged(ws', k', k'_params, dev_id, from_wimps_tds_state, to_wimps_tds_state);
        assert from_wimps_tds_state == to_wimps_tds_state;

        Lemma_SequenceHighlightLastElem(k'_wimps_tds_states);
        forall tds_state2 | tds_state2 in k'_wimps_tds_states
            ensures tds_state2 == k'_wimps_tds_state0
        {
            if(tds_state2 == to_wimps_tds_state)
            { assert tds_state2 == k'_wimps_tds_state0;}
            else
            { assert tds_state2 == k'_wimps_tds_state0;}
        }
    }
}

// (needs 100s to verify)
lemma Lemma_GreenDrvWrite_TDsInGreenPartitionHasNoInvalidRefs_IfDMIsSecureState(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams, k'_wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires k'_params == KToKParams(k')
    requires k'_wimps_tds_state0 == MaskTDsState(ActiveTDsState_SlimState(k'.objects.tds), DM_TDIDsInRed(ws'))

    requires DM_IsSecureState_SI2(ws') 

    ensures WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k'_params, AllObjsIDs(k'.objects), DM_DevsInGreen(ws'), k'_wimps_tds_state0)
{
    var green_devs := DM_DevsInGreen(ws');

    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == k'_params.all_active_tds &&
                    (k'_wimps_tds_state0 == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, 
                                green_devs, k'_wimps_tds_state0, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k'_params,  
                                green_devs, k'_wimps_tds_state0, tds_state2)))
                                    // k_os_tds_state0 -->* tds_state2
        ensures tds_state2 == k'_wimps_tds_state0
    {
        assert forall td_id, td_id2 :: td_id in k'_wimps_tds_state0 && td_id2 in k'_wimps_tds_state0[td_id].trans_params_tds
                        ==> W !in k'_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes;

        if(k'_wimps_tds_state0 != tds_state2)
        {
            var k'_wimps_tds_states, k'_devs := Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Apply(
                                                k'_params, green_devs, k'_wimps_tds_state0, tds_state2);

            Lemma_AllTDsStatesInNewKGreenTDsStatesAreSecure_TwoOrMoreElems(ws', k', k'_params,
                k'_wimps_tds_states, ActiveTDsState_SlimState(k'.objects.tds),
                green_devs, k'_devs, k'_wimps_tds_state0);

            assert tds_state2 in k'_wimps_tds_states;
            assert tds_state2 == k'_wimps_tds_state0;
            assert false;
        }
    }
}




//******** Additional Private Lemmas ********//
lemma Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveCanActiveDevReadActiveTD_PreConditions(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, tds_state2:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds

    ensures forall td_id2, dev_id :: dev_id in DM_DevsInRed(ws) && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ActiveTDOnlyHasValidTransfers_IfDevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    tds_state2:TDs_Vals, expanded_tds_state2:TDs_Vals,
    target_td_id:TD_ID
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires ws.red_pid != NULL

    requires TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(expanded_tds_state2)
    requires forall td_id :: td_id in DM_TDIDsInRed(ws)
                ==> tds_state2[td_id] == expanded_tds_state2[td_id]
    requires forall td_id :: td_id in tds_state2 && td_id !in DM_TDIDsInRed(ws)
                ==> tds_state2[td_id] == TD_Val(map[], map[], map[])
        // Requirement: Relationships between tds_state2, expanded_tds_state2, and DM_TDIDsInRed(ws)
    requires target_td_id in tds_state2

    requires DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, expanded_tds_state2, target_td_id, ws.red_pid)

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, target_td_id)
{
    // Dafny can automatically prove this lemma
}

// (needs 190s to verify)
lemma Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems_Private(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, k_wimps_tds_state0:TDs_Vals, 
    from_os_tds_state:TDs_Vals, to_os_tds_state:TDs_Vals, 
    expanded_from_os_tds_state:TDs_Vals, expanded_to_os_tds_state:TDs_Vals,
    dev_id:Dev_ID
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_wimps_tds_state0 == MaskTDsState(ActiveTDsState_SlimState(k.objects.tds), DM_TDIDsInRed(ws))

    requires TDsStateGetTDIDs(from_os_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(to_os_tds_state) == AllActiveTDs(k)

    requires forall id :: id in DM_TDIDsInGreen(ws)
                ==> from_os_tds_state[id] == to_os_tds_state[id] == TD_Val(map[], map[], map[])

    requires expanded_from_os_tds_state == MergeTDsState(from_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
    requires expanded_to_os_tds_state == MergeTDsState(to_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
    requires dev_id in DM_DevsInRed(ws)

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state)
    requires forall td_id, td_id2 :: td_id in k_wimps_tds_state0 && td_id2 in k_wimps_tds_state0[td_id].trans_params_tds
                        ==> W !in k_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes
    
    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, expanded_from_os_tds_state, expanded_to_os_tds_state)
{
    var k_tds_state := ActiveTDsState_SlimState(k.objects.tds);
    var tds_diff := TDsStateDiff(to_os_tds_state, from_os_tds_state);

    // Prove tds_diff == TDsStateDiff(expanded_to_os_tds_state, expanded_from_os_tds_state)
    Lemma_MergeTDsState_SameTDsDiff(from_os_tds_state, to_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws), expanded_from_os_tds_state, expanded_to_os_tds_state);
    assert tds_diff == TDsStateDiff(expanded_to_os_tds_state, expanded_from_os_tds_state);

    forall td_id, td_new_cfg | td_id in tds_diff &&
                td_new_cfg == tds_diff[td_id]
        ensures exists tdx_id :: 
                        tdx_id in TDsStateGetTDIDs(expanded_from_os_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, expanded_from_os_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(expanded_from_os_tds_state, tdx_id, td_id, td_new_cfg)
    {
        // Apply IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state)
        assert exists tdx_id ::
                        tdx_id in TDsStateGetTDIDs(from_os_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, from_os_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(from_os_tds_state, tdx_id, td_id, td_new_cfg);

        var tdx_id :| tdx_id in TDsStateGetTDIDs(from_os_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, from_os_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(from_os_tds_state, tdx_id, td_id, td_new_cfg);

        assert tdx_id in TDsStateGetTDIDs(expanded_from_os_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, expanded_from_os_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(expanded_from_os_tds_state, tdx_id, td_id, td_new_cfg);
    }
}

// (needs 70s to verify)
lemma Lemma_AllTDsStatesInKOSTDsStatesAreSecure_UnmodifiedGreenTDs(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, red_devs:set<Dev_ID>,
    from_os_tds_state:TDs_Vals, to_os_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires red_devs == DM_DevsInRed(ws)

    requires dev_id in red_devs

    requires TDsStateGetTDIDs(from_os_tds_state) == AllActiveTDs(k)
    requires TDsStateGetTDIDs(to_os_tds_state) == AllActiveTDs(k)

    requires ActiveTDsStateIsSecure(k_params, red_devs, from_os_tds_state)
    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> from_os_tds_state[td_id] == TD_Val(map[], map[], map[])

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state)

    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> to_os_tds_state[td_id] == TD_Val(map[], map[], map[])
{
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
    forall td_id | td_id in DM_TDIDsInGreen(ws)
        ensures to_os_tds_state[td_id] == TD_Val(map[], map[], map[])
    {
        if(to_os_tds_state[td_id] != TD_Val(map[], map[], map[]))
        {
            assert to_os_tds_state[td_id] != from_os_tds_state[td_id];

            // Apply IsTDsDiffReqInActiveTDsStateAndIssuedByDev
            var tds_diff := TDsStateDiff(to_os_tds_state, from_os_tds_state);
            var td_new_cfg := tds_diff[td_id];
            var tdx_id :| tdx_id in TDsStateGetTDIDs(from_os_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, from_os_tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(from_os_tds_state, tdx_id, td_id, td_new_cfg);
                                // the active TD refs the TD with W and the new TD cfg

            // Prove tdx_id is in red partition
            Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(
                k, k_params, red_devs, from_os_tds_state, dev_id, tdx_id);
            assert SubjPID(k, dev_id.sid) == ObjPID(k, tdx_id.oid);
            assert ObjPID(k, tdx_id.oid) == ws.red_pid;

            // Show conflict
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, from_os_tds_state, tdx_id);
            assert false;
        }
    }
}

lemma Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems_ProveToOSTDsStateIsSecure(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    k_tds_state:TDs_Vals, k_wimps_tds_state0:TDs_Vals, red_devs:set<Dev_ID>,
    to_os_tds_state:TDs_Vals, expanded_to_os_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)
    requires k_wimps_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInRed(ws))
    requires red_devs == DM_DevsInRed(ws)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirement: From DM_IsSecureState_SI1

    requires TDsStateGetTDIDs(to_os_tds_state) == k_params.all_active_tds
    requires forall id :: id in DM_TDIDsInGreen(ws)
                ==> to_os_tds_state[id] == TD_Val(map[], map[], map[])
        // Requirement: Properties of <to_os_tds_state>

    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
    requires expanded_to_os_tds_state == MergeTDsState(to_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws))
    requires expanded_to_os_tds_state == k_tds_state ||
                (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        red_devs, k_tds_state, expanded_to_os_tds_state) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                        red_devs, k_tds_state, expanded_to_os_tds_state))
        // Requirements: Properties of <expanded_to_os_tds_state>

    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires forall dev_id2 :: dev_id2 in red_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: Requirements of CanActiveDevReadActiveTD

    ensures ActiveTDsStateIsSecure(k_params, red_devs, to_os_tds_state)
{
    forall td_id2, dev_id | dev_id in red_devs && 
                        // The device (<dev_id>) is an active OS device
                    td_id2 in TDsStateGetTDIDs(to_os_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, to_os_tds_state, dev_id, td_id2)
                        // The TD is read by the device
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, to_os_tds_state, td_id2)
    {
        var td_ids := Lemma_DM_CanActiveDevReadActiveTD_Apply(k_params, to_os_tds_state, dev_id, td_id2);
        assert P_CanActiveDevReadActiveTD_Def(k_params, to_os_tds_state, dev_id, td_ids, td_id2);

        Lemma_DM_AllTDsHaveSecureTransfersInMaskedTDsState(ws, k, k_params, 
            to_os_tds_state, expanded_to_os_tds_state, DM_TDIDsInRed(ws), 
            red_devs, dev_id, td_ids, td_id2);
    }
}

// (needs 120s to verify)
lemma Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoElems(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    k_os_tds_states:seq<TDs_Vals>, k_os_tds_state0:TDs_Vals, k_tds_state:TDs_Vals,
    red_devs:set<Dev_ID>, k_devs:seq<Dev_ID>, last_k_os_tds_state:TDs_Vals, k_wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)
    requires k_os_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInGreen(ws))
    requires k_wimps_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInRed(ws))
    requires red_devs == DM_DevsInRed(ws)
    
    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)

    requires (|k_os_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k_os_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)) &&
                |k_devs| == |k_os_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in red_devs) &&
                k_os_tds_states[0] == k_os_tds_state0 && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|k_os_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            k_devs[i], k_os_tds_states[i], k_os_tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            k_devs[i], k_os_tds_states[i], k_os_tds_states[i+1])))
                    // k_os_tds_state0 -->1+ k_os_tds_states[|k_os_tds_states| - 1]
        // Requirement: k_os_tds_state0 -->* k_os_tds_states[|k_os_tds_states| - 1]

    requires |k_os_tds_states| == 2
    requires k_os_tds_states[0] == k_os_tds_state0  
        // First TDs' state is the <k_os_tds_state0>
    requires k_os_tds_states[|k_os_tds_states|-1] == last_k_os_tds_state
        // Requirement: Last TDs' state is <last_k_os_tds_state>

    requires DM_AllActiveDevs(ws.subjects) == DM_DevsInRed(ws) + DM_DevsInGreen(ws)
    requires DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k)
        // Requirement: Properties better to be proved in the caller

    requires forall td_id, td_id2 :: td_id in k_wimps_tds_state0 && td_id2 in k_wimps_tds_state0[td_id].trans_params_tds
                ==> W !in k_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirement: From DM_IsSecureState_SI1

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), k_tds_state)

    ensures P_Lemma_AllTDsStatesInKOSTDsStatesAreSecure_Properties(ws, k, k_params,
                k_os_tds_states, k_tds_state, k_wimps_tds_state0, red_devs)          
{
    var dev_id := k_devs[0];
    var from_os_tds_state := k_os_tds_states[0];
    var to_os_tds_state := k_os_tds_states[1];

    var expanded_from_os_tds_state := MergeTDsState(from_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
    var expanded_to_os_tds_state := MergeTDsState(to_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
    assert expanded_from_os_tds_state == k_tds_state;

    // Prove ActiveTDsStateIsSecure(k_params, red_devs, from_os_tds_state)
    Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveKOSTDSState0IsSecure(
        ws, k, k_params, k_tds_state, from_os_tds_state);
    assert ActiveTDsStateIsSecure(k_params, red_devs, from_os_tds_state);

    // Prove property 2
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state);
    Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, dev_id, red_devs, from_os_tds_state, to_os_tds_state); 
    assert forall id :: id in DM_TDIDsInGreen(ws)
            ==> from_os_tds_state[id] == TD_Val(map[], map[], map[]);
    Lemma_AllTDsStatesInKOSTDsStatesAreSecure_UnmodifiedGreenTDs(ws, k, k_params, dev_id, red_devs, from_os_tds_state, to_os_tds_state);
    assert forall id :: id in DM_TDIDsInGreen(ws)
            ==> to_os_tds_state[id] == TD_Val(map[], map[], map[]);

    // Prove property 1
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state);
    Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems_Private(ws, k, k_params, k_wimps_tds_state0,
        from_os_tds_state, to_os_tds_state, expanded_from_os_tds_state, expanded_to_os_tds_state, dev_id);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, expanded_from_os_tds_state, expanded_to_os_tds_state);
    Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, dev_id, red_devs, expanded_from_os_tds_state, expanded_to_os_tds_state);

    // Summary of property 1
    Lemma_SeqWithTwoElem_HighlightEachOne(k_os_tds_states);
    forall tds_state2, expanded_tds_state2 | tds_state2 in k_os_tds_states &&
                expanded_tds_state2 == MergeTDsState(tds_state2, k_wimps_tds_state0, DM_TDIDsInGreen(ws))
        ensures expanded_tds_state2 == k_tds_state ||
                (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        red_devs, k_tds_state, expanded_tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                        red_devs, k_tds_state, expanded_tds_state2))
    {
        assert tds_state2 == from_os_tds_state || tds_state2 == to_os_tds_state;
        assert expanded_tds_state2 == expanded_from_os_tds_state || expanded_tds_state2 == expanded_to_os_tds_state;
    }

    // Prove ActiveTDsStateIsSecure(k_params, red_devs, to_os_tds_state)
    Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems_ProveToOSTDsStateIsSecure(
        ws, k, k_params, k_tds_state, k_wimps_tds_state0, red_devs,
        to_os_tds_state, expanded_to_os_tds_state);
}

// (needs 240s to verify)
lemma Lemma_AllTDsStatesInKOSTDsStatesAreSecure_MultiElems(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    k_os_tds_states:seq<TDs_Vals>, k_os_tds_state0:TDs_Vals, k_tds_state:TDs_Vals,
    red_devs:set<Dev_ID>, k_devs:seq<Dev_ID>, last_k_os_tds_state:TDs_Vals, k_wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)
    requires k_os_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInGreen(ws))
    requires k_wimps_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInRed(ws))
    requires red_devs == DM_DevsInRed(ws)
    
    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)

    requires (|k_os_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k_os_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)) &&
                |k_devs| == |k_os_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in red_devs) &&
                k_os_tds_states[0] == k_os_tds_state0 && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|k_os_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            k_devs[i], k_os_tds_states[i], k_os_tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            k_devs[i], k_os_tds_states[i], k_os_tds_states[i+1])))
                    // k_os_tds_state0 -->1+ k_os_tds_states[|k_os_tds_states| - 1]
        // Requirement: k_os_tds_state0 -->* k_os_tds_states[|k_os_tds_states| - 1]

    requires |k_os_tds_states| > 2
    requires k_os_tds_states[0] == k_os_tds_state0  
        // First TDs' state is the <k_os_tds_state0>
    requires k_os_tds_states[|k_os_tds_states|-1] == last_k_os_tds_state
        // Requirement: Last TDs' state is <last_k_os_tds_state>

    requires DM_AllActiveDevs(ws.subjects) == DM_DevsInRed(ws) + DM_DevsInGreen(ws)
    requires DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k)
        // Requirement: Properties better to be proved in the caller

    requires forall td_id, td_id2 :: td_id in k_wimps_tds_state0 && td_id2 in k_wimps_tds_state0[td_id].trans_params_tds
                ==> W !in k_wimps_tds_state0[td_id].trans_params_tds[td_id2].amodes


    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirement: From DM_IsSecureState_SI1

    requires P_Lemma_AllTDsStatesInKOSTDsStatesAreSecure_Properties(ws, k, k_params,
                k_os_tds_states[..|k_os_tds_states|-1], k_tds_state, k_wimps_tds_state0, red_devs)
        // Requirement: For recursion

    ensures P_Lemma_AllTDsStatesInKOSTDsStatesAreSecure_Properties(ws, k, k_params,
                k_os_tds_states, k_tds_state, k_wimps_tds_state0, red_devs)
{
    var dev_id := k_devs[|k_devs|-1];
    var from_os_tds_state := k_os_tds_states[|k_os_tds_states|-2];
    var to_os_tds_state := k_os_tds_states[|k_os_tds_states|-1];
    var last_k_os_tds_states := k_os_tds_states[..|k_os_tds_states|-1];

    Lemma_SequenceHighlightLastElemOfSubSeq(k_os_tds_states, last_k_os_tds_states);
    assert from_os_tds_state == last_k_os_tds_states[|last_k_os_tds_states|-1];

    var expanded_from_os_tds_state := MergeTDsState(from_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
    var expanded_to_os_tds_state := MergeTDsState(to_os_tds_state, k_wimps_tds_state0, DM_TDIDsInGreen(ws));
    //assert expanded_from_os_tds_state == k_tds_state;

    // Prove ActiveTDsStateIsSecure(k_params, red_devs, from_os_tds_state)
    assert ActiveTDsStateIsSecure(k_params, red_devs, from_os_tds_state);

    // Prove property 2
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state);
    Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, dev_id, red_devs, from_os_tds_state, to_os_tds_state); 
    assert forall id :: id in DM_TDIDsInGreen(ws)
            ==> from_os_tds_state[id] == TD_Val(map[], map[], map[]);
    Lemma_AllTDsStatesInKOSTDsStatesAreSecure_UnmodifiedGreenTDs(ws, k, k_params, dev_id, red_devs, from_os_tds_state, to_os_tds_state);
    assert forall id :: id in DM_TDIDsInGreen(ws)
            ==> to_os_tds_state[id] == TD_Val(map[], map[], map[]);

    // Prove property 1
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, from_os_tds_state, to_os_tds_state);
    Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems_Private(ws, k, k_params, k_wimps_tds_state0,
        from_os_tds_state, to_os_tds_state, expanded_from_os_tds_state, expanded_to_os_tds_state, dev_id);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, dev_id, expanded_from_os_tds_state, expanded_to_os_tds_state);

    //// Prove k_tds_state -->1+ expanded_to_os_tds_state
    if(expanded_from_os_tds_state == k_tds_state)
    {
        Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, dev_id, red_devs, 
            expanded_from_os_tds_state, expanded_to_os_tds_state);
    }
    else
    {
        Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(k_params, dev_id, red_devs, 
            k_tds_state, expanded_from_os_tds_state, expanded_to_os_tds_state);
    }

    // Summary of property 1
    Lemma_SequenceHighlightLastElem(k_os_tds_states);
    forall tds_state2, expanded_tds_state2 | tds_state2 in k_os_tds_states &&
                expanded_tds_state2 == MergeTDsState(tds_state2, k_wimps_tds_state0, DM_TDIDsInGreen(ws))
        ensures expanded_tds_state2 == k_tds_state ||
                (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        red_devs, k_tds_state, expanded_tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                        red_devs, k_tds_state, expanded_tds_state2))
    {
        assert tds_state2 in last_k_os_tds_states || tds_state2 == to_os_tds_state;
        if(tds_state2 == to_os_tds_state)
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                        red_devs, k_tds_state, expanded_tds_state2);
        }
        else
        {
            assert tds_state2 in last_k_os_tds_states;
            assert P_Lemma_AllTDsStatesInKOSTDsStatesAreSecure_Properties(ws, k, k_params,
                        last_k_os_tds_states, k_tds_state, k_wimps_tds_state0, red_devs);
            assert expanded_tds_state2 == k_tds_state ||
                (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        red_devs, k_tds_state, expanded_tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                        red_devs, k_tds_state, expanded_tds_state2));
        }
    }

    // Prove ActiveTDsStateIsSecure(k_params, red_devs, to_os_tds_state)
    Lemma_AllTDsStatesInKOSTDsStatesAreSecure_TwoOrMoreElems_ProveToOSTDsStateIsSecure(
        ws, k, k_params, k_tds_state, k_wimps_tds_state0, red_devs,
        to_os_tds_state, expanded_to_os_tds_state);
}

lemma Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_Private(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    red_devs:set<Dev_ID>, tds_state2:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires red_devs == DM_DevsInRed(ws)

    requires TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires ActiveTDsStateIsSecure(k_params, red_devs, tds_state2)
    requires forall td_id2, dev_id :: dev_id in red_devs && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2)

    ensures forall td_id2, dev_id :: dev_id in red_devs && 
                            // The device (<dev_id>) is an active OS device
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2) &&
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveExpandedTDsState2EqualsKTDsState(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    k_tds_state:TDs_Vals, k_wimps_tds_state0:TDs_Vals, k_os_tds_state0:TDs_Vals, expanded_tds_state2:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)
    
    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
    requires k_wimps_tds_state0 == MaskTDsState(k_tds_state, DM_TDIDsInRed(ws))
    requires k_os_tds_state0 == MaskTDsState(ActiveTDsState_SlimState(k.objects.tds), DM_TDIDsInGreen(ws))
    requires expanded_tds_state2 == MergeTDsState(k_os_tds_state0, k_wimps_tds_state0, DM_TDIDsInGreen(ws))
    
    ensures expanded_tds_state2 == k_tds_state
{
    assert MapGetKeys(expanded_tds_state2) == MapGetKeys(k_tds_state);
    forall id | id in expanded_tds_state2
        ensures expanded_tds_state2[id] == k_tds_state[id]
    {
        // Dafny can automatically prove this statement
    }
}

lemma Lemma_AllTDsStatesInNewKGreenTDsStatesAreSecure_TwoOrMoreElems_ProveTDsStateIsUnchanged(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams,
    dev_id:Dev_ID, from_wimps_tds_state:TDs_Vals, to_wimps_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires k'_params == KToKParams(k')

    requires dev_id in DM_DevsInGreen(ws')

    requires TDsStateGetTDIDs(from_wimps_tds_state) == AllActiveTDs(k')
    requires TDsStateGetTDIDs(to_wimps_tds_state) == AllActiveTDs(k')

    requires forall td_id, td_id2 :: td_id in from_wimps_tds_state && td_id2 in from_wimps_tds_state[td_id].trans_params_tds
                ==> W !in from_wimps_tds_state[td_id].trans_params_tds[td_id2].amodes

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k'_params, dev_id, from_wimps_tds_state, to_wimps_tds_state)
    ensures from_wimps_tds_state == to_wimps_tds_state
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_IfTDsStateCanBeReachedWithRedDevs_ThenTDsStateCanBeReachedWithActiveDevs(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams,
    k'_tds_state:TDs_Vals, tds_state2:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires k'_params == KToKParams(k')
    requires k'_tds_state == ActiveTDsState_SlimState(k'.objects.tds)

    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, 
                DM_DevsInRed(ws'), k'_tds_state, tds_state2) &&
            IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                DM_DevsInRed(ws'), k'_tds_state, tds_state2)

    ensures (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, AllActiveDevs(k'), ActiveTDsState(k'), tds_state2) &&
                 IsActiveTDsStateReachActiveTDsStateInChain(k'_params, AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_SI1HoldsIfRedTDsAreUnchanged_ProveDevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams,
    k'_tds_state:TDs_Vals, tds_state2:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires k'_params == KToKParams(k')
    requires k'_tds_state == ActiveTDsState_SlimState(k'.objects.tds)

    requires TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k'.objects.tds)
    requires ActiveTDsStateIsSecure(k'_params, AllActiveDevs_SlimState(k'_params.subjects), tds_state2)

    ensures (forall td_id2, dev_id ::
                            dev_id in DM_DevsInRed(ws') && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k'_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k'_params, tds_state2, td_id2, ws'.red_pid))
{
    forall td_id2, dev_id | dev_id in DM_DevsInRed(ws') && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k'_params, tds_state2, dev_id, td_id2)
        ensures DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k'_params, tds_state2, td_id2, ws'.red_pid)
    {
        Lemma_K_SecureState_IfDevHasTransferToTD_ThenTheyAreInSamePartition(
            k', k'_params, DM_DevsInRed(ws'), tds_state2, dev_id, td_id2);
        assert ObjPID(k', td_id2.oid) == ws'.red_pid;

        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, tds_state2, td_id2);
    }
}

// (needs 60s to verify)
lemma Lemma_GreenDrvWrite_TDsInRedPartitionHasNoInvalidRefs_IfDMIsSecureState_ProveKOSTDSState0IsSecure(
    ws':DM_State, k':State, k'_params:ReachableTDsKParams,
    k'_tds_state:TDs_Vals, k_os_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws')
    requires k' == DMStateToState(ws')
    requires k'_params == KToKParams(k')
    requires k'_tds_state == ActiveTDsState_SlimState(k'.objects.tds)
    requires k_os_tds_state0 == MaskTDsState(k'_tds_state, DM_TDIDsInGreen(ws'))
    
    requires ActiveTDsStateIsSecure(k'_params, AllActiveDevs(k'), k'_tds_state)

    ensures ActiveTDsStateIsSecure(k'_params, DM_DevsInRed(ws'), k_os_tds_state0)
{
    forall td_id2, dev_id | dev_id in DM_DevsInRed(ws') && 
                    // The device (<dev_id>) is active
                td_id2 in TDsStateGetTDIDs(k_os_tds_state0) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k'_params, k_os_tds_state0, dev_id, td_id2)
                    // The TD is read by the device
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k_os_tds_state0, td_id2)
    {
        assert dev_id in AllActiveDevs(k');
        assert CanActiveDevReadActiveTD(k'_params, k'_tds_state, dev_id, td_id2);

        // Prove ObjPID(k', td_id2.oid) == ws'.red_pid
        Lemma_K_SecureState_IfDevHasTransferToTD_ThenTheyAreInSamePartition(
            k', k'_params, AllActiveDevs(k'), k'_tds_state, dev_id, td_id2);
        assert ObjPID(k', td_id2.oid) == ws'.red_pid;

        assert k_os_tds_state0[td_id2] == k'_tds_state[td_id2];
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k'_params, k_os_tds_state0, td_id2);
    }
}