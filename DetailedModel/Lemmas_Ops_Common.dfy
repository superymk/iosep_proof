include "../Abstract/Properties.dfy"
include "../Abstract/Lemmas_Ops.dfy"
include "Utils.dfy"
include "./utils/Collections.dfy"
include "Properties_ValidDMState.dfy"
include "K_AdditionalPropertiesLemmas.dfy"

predicate P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws:DM_State, ws':DM_State)
{
    // Same subject IDs
    MapGetKeys(ws'.subjects.drvs) == MapGetKeys(ws.subjects.drvs) &&
    MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs) &&

    // Same object ownership
    (forall id :: id in ws'.subjects.drvs 
        ==> (ws'.subjects.drvs[id].td_ids == ws.subjects.drvs[id].td_ids) &&
            (ws'.subjects.drvs[id].fd_ids == ws.subjects.drvs[id].fd_ids) &&
            (ws'.subjects.drvs[id].do_ids == ws.subjects.drvs[id].do_ids)) &&
    (forall id :: id in ws'.subjects.devs 
        ==> (ws'.subjects.devs[id].hcoded_td_id == ws.subjects.devs[id].hcoded_td_id) &&
            (ws'.subjects.devs[id].td_ids == ws.subjects.devs[id].td_ids) &&
            (ws'.subjects.devs[id].fd_ids == ws.subjects.devs[id].fd_ids) &&
            (ws'.subjects.devs[id].do_ids == ws.subjects.devs[id].do_ids)) &&

    (true)
}

predicate P_AllHCodedTDsAreObjs(ws:DM_State)
{
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id in ws.subjects.devs[dev_id].td_ids) &&
        // Requirement: Hardcoded TDs are in devices
    (forall dev_id, td_id :: 
                dev_id in ws.subjects.devs && td_id in ws.subjects.devs[dev_id].td_ids
                ==> td_id in ws.objects.tds)
}

predicate P_DMAndNewDM_SameObjectID(ws:DM_State, ws':DM_State)
    requires P_AllHCodedTDsAreObjs(ws)
{
    // Same object IDs
    (MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds) &&
     MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds) &&
     MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos)) &&

    // Same hardcoded TD Values
    (forall id :: id in DM_AllHCodedTDIDs(ws.subjects) ==> ws.objects.tds[id].val == ws'.objects.tds[id].val) &&

    // Same <tds_to_all_states>
    (ws'.tds_to_all_states == ws.tds_to_all_states) &&

    (true)
}
predicate P_DMAndNewDM_SameSubjObjPID(ws:DM_State, ws':DM_State)
    requires P_AllHCodedTDsAreObjs(ws)
    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
{
    // Same Subjects' PIDs
    (forall id :: id in ws'.subjects.drvs
        ==> ws'.subjects.drvs[id].pid == ws.subjects.drvs[id].pid) &&
    (forall id :: id in ws'.subjects.devs
        ==> ws'.subjects.devs[id].pid == ws.subjects.devs[id].pid) &&

    // Same Objects' PIDs
    (forall id :: id in ws'.objects.tds
        ==> ws'.objects.tds[id].pid == ws.objects.tds[id].pid) &&
    (forall id :: id in ws'.objects.fds
        ==> ws'.objects.fds[id].pid == ws.objects.fds[id].pid) &&
    (forall id :: id in ws'.objects.dos
        ==> ws'.objects.dos[id].pid == ws.objects.dos[id].pid) &&

    (true)
}

lemma Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    ensures DM_IsValidState_Subjects(ws')
    ensures DM_IsValidState_Objects(ws')

    ensures DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    ensures DM_AllHCodedTDIDs(ws'.subjects) == DM_AllHCodedTDIDs(ws.subjects)

    ensures DM_AllTDIDs(ws'.objects) == DM_AllTDIDs(ws.objects)
    ensures DM_AllFDIDs(ws'.objects) == DM_AllFDIDs(ws.objects)
    ensures DM_AllDOIDs(ws'.objects) == DM_AllDOIDs(ws.objects)
{
    var k := DMStateToState(ws);
    var k' := DMStateToState(ws');
    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);
    
    assert forall dev_id :: dev_id in k'.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids);
    Lemma_SameObjsOwnershipInSuccessiveStates(k, k');

    Lemma_NewK_FulfillCondition24(k, k');
}

lemma Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_ObjIDs(ws)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_AllHCodedTDsAreObjs(ws)

    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjObjPID(ws, ws')

    ensures forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_SubjPID(ws'.subjects, s_id) == DM_SubjPID(ws.subjects, s_id)
    ensures forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id)

    ensures DM_AllActiveSubjs(ws'.subjects) == DM_AllActiveSubjs(ws.subjects)
    ensures DM_AllActiveDevs(ws'.subjects) == DM_AllActiveDevs(ws.subjects)
{
    assert DM_BuildMap_ObjIDsToPIDs(ws'.objects) == DM_BuildMap_ObjIDsToPIDs(ws.objects);
}




//******** From NewK ********//
lemma Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws':DM_State, k':State)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_ObjIDs(ws')

    requires IsValidState_Subjects(k') && IsValidState_Objects(k') && 
            IsValidState_Partitions(k') && IsValidState_SubjsOwnObjsThenInSamePartition(k')
    requires k' == DMStateToState(ws')

    ensures DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
{
    Lemma_K_ProveIsValidState_SubjsOwnObjsThenInSamePartition(k');
    assert forall s_id, o_id :: s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
                ==> o_id in AllObjsIDs(k'.objects) &&
                    SubjPID(k', s_id) == ObjPID(k', o_id);
    
    // Prove the property
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws', k');
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws', k');

    Lemma_DM_ObjsInSubjsAreAlsoInState(ws');

    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws'.subjects) && DM_DoOwnObj(ws'.subjects, s_id, o_id)
        ensures DM_SubjPID(ws'.subjects, s_id) == DM_ObjPID(ws'.objects, o_id)
    {
        assert s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id);
    }
}




//******** Important Sub-Lemmas ********//
lemma Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(
    ws:DM_State, ws':DM_State
)
    requires DM_IsValidState_DevsActivateCond(ws)

    requires ws'.devs_activatecond == ws.devs_activatecond
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires forall id :: id in ws.subjects.devs
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)

    ensures DM_IsValidState_DevsActivateCond(ws')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_FulFillIsValidState_SubjsOwnObjsThenInSamePartition_IfPIDsAreUnchanged(
    ws:DM_State, ws':DM_State
)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_AllHCodedTDsAreObjs(ws)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires P_DMSubjectsHasUniqueIDs(ws'.subjects)

    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)

    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    requires DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_DoOwnObj(ws'.subjects, s_id, o_id) == DM_DoOwnObj(ws.subjects, s_id, o_id)
    requires forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_SubjPID(ws'.subjects, s_id) == DM_SubjPID(ws.subjects, s_id)
    requires forall o_id :: o_id in DM_AllObjsIDs(ws.objects)
                ==> DM_ObjPID(ws'.objects, o_id) == DM_ObjPID(ws.objects, o_id) 

    ensures P_ObjsInSubjsAreInSetOfAllObjs(ws'.subjects, ws'.objects)
    ensures DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
{
    var k := DMStateToState(ws);

    Lemma_DM_ObjsInSubjsAreAlsoInState(ws);

    // Prove property 2
    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws'.subjects) && DM_DoOwnObj(ws'.subjects, s_id, o_id)
        ensures DM_SubjPID(ws'.subjects, s_id) == DM_ObjPID(ws'.objects, o_id)
    {
        assert s_id in DM_AllSubjsIDs(ws.subjects);
        assert DM_DoOwnObj(ws.subjects, s_id, o_id);

        assert DoOwnObj(k, s_id, o_id);
        assert SubjPID(k, s_id) == ObjPID(k, o_id);

        assert DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, o_id);
    }
}

// (needs 80s to verify)
lemma Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(
    ws:DM_State, k:State, ws':DM_State, k':State
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id)

    requires ws'.red_pid == ws.red_pid
    requires DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)

    requires forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> ws'.objects.tds[td_id] == ws.objects.tds[td_id]
    requires forall fd_id :: fd_id in DM_FDIDsInGreen(ws)
                ==> ws'.objects.fds[fd_id].pid == ws.objects.fds[fd_id].pid
    requires forall do_id :: do_id in DM_DOIDsInGreen(ws)
                ==> ws'.objects.dos[do_id].pid == ws.objects.dos[do_id].pid
                     
    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id)
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);
    assert k'_params.hcoded_td_ids == k_params.hcoded_td_ids;
    assert k'_params.objs_td_ids == k_params.objs_td_ids;
    assert k'_params.objs_fd_ids == k_params.objs_fd_ids;
    assert k'_params.objs_do_ids == k_params.objs_do_ids;

    forall td_id | td_id in DM_TDIDsInGreen(ws')
        ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id)
    {
        assert ws'.objects.tds[td_id] == ws.objects.tds[td_id];
        assert ActiveTDsState(k')[td_id] == ActiveTDsState(k)[td_id];

        assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, ActiveTDsState(k), td_id);

        // Prove DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id)
        var k'_tds_state := ActiveTDsState(k');
        forall td_id2 | td_id2 in k'_tds_state[td_id].trans_params_tds
            ensures td_id2 in k'_params.objs_td_ids &&
                td_id2 !in k'_params.hcoded_td_ids &&
                (ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid) || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_tds[td_id2].amodes == {})
        {
            // Dafny can automatically prove this statement
        }

        forall fd_id2 | fd_id2 in k'_tds_state[td_id].trans_params_fds
            ensures fd_id2 in k'_params.objs_fd_ids &&
                ((ObjPID_SlimState(k'_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid)) ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {})
        {
            // Dafny can automatically prove this statement
        }

        forall do_id2 | do_id2 in k'_tds_state[td_id].trans_params_dos
            ensures do_id2 in k'_params.objs_do_ids && 
                (ObjPID_SlimState(k'_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid) ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {})
        {
            // Dafny can automatically prove this statement
        }
    }
}

lemma Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws:DM_State, ws':DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)

    requires ws'.red_pid == ws.red_pid
        // Requirement: PID of red partition is unchanged

    requires MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds)
    requires forall id :: id in ws.objects.tds
                ==> ws'.objects.tds[id].pid == ws.objects.tds[id].pid

    ensures DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws)
{
    // Dafny can automatically prove this lemma
}




//******** Important Util Lemmas ********//
lemma Lemma_NewDM_SameSubjObjIDs(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_ObjIDs(ws)
    requires P_AllHCodedTDsAreObjs(ws)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    ensures DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures DM_AllObjsIDs(ws'.objects) == DM_AllObjsIDs(ws.objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_IsValidState_DevsActivateCond(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_DevsActivateCond(ws)

    requires ws'.devs_activatecond == ws.devs_activatecond
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires (forall dev_id :: dev_id in ws'.devs_activatecond
                ==> DM_SubjPID(ws'.subjects, dev_id.sid) == NULL ||  DM_SubjPID(ws'.subjects, dev_id.sid) == ws'.red_pid)
        // Condition 5.2
    requires (forall dev_id, dev_id2 :: dev_id in ws'.devs_activatecond &&
                    dev_id2 in ws'.devs_activatecond[dev_id]
                ==> DM_SubjPID(ws'.subjects, dev_id2.sid) != ws'.red_pid)
        // Condition 5.3
    requires (forall dev_id :: dev_id in ws'.devs_activatecond &&
                    DM_SubjPID(ws'.subjects, dev_id.sid) != NULL
                ==> (forall dev_id2 :: dev_id2 in ws'.devs_activatecond[dev_id]
                        ==> DM_SubjPID(ws'.subjects, dev_id2.sid) == NULL))
        // Condition 5.6

    ensures DM_IsValidState_DevsActivateCond(ws')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_SameSubjObjOwnership(ws:DM_State, ws':DM_State)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_ObjIDs(ws)
    requires P_AllHCodedTDsAreObjs(ws)

    requires P_DMAndNewDM_SameObjectID(ws, ws')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')
    

    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_ObjIDs(ws')

    ensures DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects)
                ==> DM_DoOwnObj(ws'.subjects, s_id, o_id) == DM_DoOwnObj(ws.subjects, s_id, o_id)
{
    Lemma_NewDM_SameSubjObjIDs(ws, ws');

    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws.subjects)
        ensures DM_DoOwnObj(ws'.subjects, s_id, o_id) == DM_DoOwnObj(ws.subjects, s_id, o_id)
    {
        // Dafny can automatically prove this statement
    }
}

lemma Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws:DM_State, k:State)
    requires DM_IsValidState_Subjects(ws)
    requires k == DMStateToState(ws)

    ensures (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
        // Property: Unique subject IDs
    ensures AllSubjsIDs(k.subjects) == DM_AllSubjsIDs(ws.subjects)
    ensures forall s_id :: DM_IsDevID(ws.subjects, Dev_ID(s_id))
                <==> IsDevID(k, Dev_ID(s_id))
    ensures forall s_id :: DM_IsDrvID(ws.subjects, Drv_ID(s_id))
                <==> IsDrvID(k, Drv_ID(s_id))

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
                ==> DM_SubjPID(ws.subjects, s_id) == SubjPID(k, s_id)
{
    // Dafny can automatically prove this lemma
}

// Lemma: After mapping a valid WK state <ws> to the abstract state <k>,
// DM_ObjPID returns same PID of objects to objects as ObjPID.
lemma Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws:DM_State, k:State)
    requires DM_IsValidState_ObjIDs(ws)
    requires k == DMStateToState(ws)

    ensures forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    ensures forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    ensures forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id
        // Properties needed by the ObjPID

    ensures AllObjsIDs(k.objects) == DM_AllObjsIDs(ws.objects)
    ensures forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> o_id in DM_AllObjsIDs(ws.objects)
    ensures forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> DM_ObjPID(ws.objects, o_id) == ObjPID(k, o_id)
{
    // Dafny can automatically prove this lemma
}




//******** For EmptyPartitionDestroy ********//
lemma Lemma_DM_EmptyPartitionDestroy_ProveCheckOfDevActivateInK(
    ws:DM_State, k:State, pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires k == DMStateToState(ws)

    requires (pid != NULL) &&
        (pid in ws.pids) &&
        (forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects) ==> DM_SubjPID(ws.subjects, s_id) != pid) &&
        (forall o_id :: o_id in DM_AllObjsIDs(ws.objects) ==> DM_ObjPID(ws.objects, o_id) != pid)
    
    ensures forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    ensures forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    ensures forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id
    ensures (pid != NULL) &&
                (pid in k.pids) &&
                (forall s_id :: s_id in AllSubjsIDs(k.subjects) ==> SubjPID(k, s_id) != pid) &&
                (forall o_id :: o_id in AllObjsIDs(k.objects) ==> ObjPID(k, o_id) != pid)
{
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
}

lemma Lemma_EmptyPartitionDestroy_ProveRedPIDStillExists(
    ws:DM_State, ws':DM_State, pid:Partition_ID
)
    requires pid != ws.red_pid
    requires ws'.red_pid == ws.red_pid
    requires ws'.pids == ws.pids - {pid}
    
    requires ws.red_pid in ws.pids
    
    ensures ws'.red_pid in ws'.pids
{
    // Dafny can automatically prove this lemma
}

//******** For ExternalObjsActivate/Deactivate ********//
lemma Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(
    ws:DM_State, k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    requires k == DMStateToState(ws)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
{
    forall s_id, o_id | s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
        ensures !DoOwnObj(k, s_id, o_id)
    {
        assert !DM_DoOwnObj(ws.subjects, s_id, o_id);
    }
}

lemma Lemma_NewDMFromNewK_FulfillSI1_Private(k':State, tds_state2:TDs_Vals)
    requires IsValidState_Subjects(k') && IsValidState_Objects(k')

    requires forall td_id2 :: td_id2 in AllActiveTDs_SlimState(k'.objects.tds)
                ==> td_id2.oid in AllObjsIDs(k'.objects) &&
                    ObjPID(k', td_id2.oid) != NULL
    requires TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k'.objects.tds)

    ensures forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> td_id2.oid in AllObjsIDs(k'.objects) &&
                    ObjPID(k', td_id2.oid) != NULL
{
    // Dafny can automatically prove this lemma
}