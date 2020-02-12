include "SecurityProperties_Ops.dfy"

//******** Prove Security Properties ********//
// Proof of the Security Property 1: Forall traces starting from a secure state,
// no I/O access (as operations) crosses partition
lemma Lemma_DM_ProveSP1(t:DM_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties
    requires DM_IsValidTrace(t)
            
    ensures forall i, states:seq<DM_State> :: 0 <= i < |t.ops| && states == DM_CalcNewStates(t)
                ==> (t.ops[i].DM_RedDrvReadOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_GreenDrvReadOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid,
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_RedDrvWriteOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_GreenDrvWriteOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DM_DevReadOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid,
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].DM_RedDevWriteOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].DM_GreenDevWriteOp? && DM_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the device
                    )
{
    // Dafny can automatically prove this lemma
}

// Proof of the Security Property 2: Only hardcoded TDs can be reused in a 
// new partition
lemma Lemma_DM_ProveSP2(t:DM_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties
    requires DM_IsValidTrace(t)
    
    ensures forall i, states:seq<DM_State> :: 0 <= i < |t.ops| && states == DM_CalcNewStates(t)
                ==> MapGetKeys(states[i+1].objects.tds) == MapGetKeys(states[i].objects.tds) &&
                    MapGetKeys(states[i+1].objects.fds) == MapGetKeys(states[i].objects.fds) &&
                    MapGetKeys(states[i+1].objects.dos) == MapGetKeys(states[i].objects.dos)
        // Property needed by the following property
    ensures forall i, states:seq<DM_State> :: 0 <= i < |t.ops| && states == DM_CalcNewStates(t)
                ==> (forall td_id :: P_DM_IsNonHCodedTDBeingMovedToAnActivePartition(states[i], states[i+1], td_id)
                        ==> DM_IsTDClearVal(states[i+1].objects, td_id)
                    ) && 
                    (forall fd_id :: P_DM_IsFDBeingMovedToAnActivePartition(states[i], states[i+1], fd_id)
                        ==> DM_IsFDClearVal(states[i+1].objects, fd_id)
                    ) &&
                    (forall do_id :: P_DM_IsDOBeingMovedToAnActivePartition(states[i], states[i+1], do_id)
                        ==> DM_IsDOClearVal(states[i+1].objects, do_id))
        // Main property: Only hardcoded TDs can be reused in a new partition
{
    var states := DM_CalcNewStates(t);
    
    forall i | 0 <= i < |t.ops|
        ensures MapGetKeys(states[i+1].objects.tds) == MapGetKeys(states[i].objects.tds)
        ensures MapGetKeys(states[i+1].objects.fds) == MapGetKeys(states[i].objects.fds)
        ensures MapGetKeys(states[i+1].objects.dos) == MapGetKeys(states[i].objects.dos)
    {
        var ws := states[i];
        var ws' := DM_CalcNewState(states[i], t.ops[i]).0;
        assert ws' == states[i+1];
        assert DM_IsSecureOps(ws, ws');   
    }

    forall i | 0 <= i < |t.ops|
        ensures forall td_id :: P_DM_IsNonHCodedTDBeingMovedToAnActivePartition(states[i], states[i+1], td_id)
                        ==> DM_IsTDClearVal(states[i+1].objects, td_id)
        ensures forall fd_id :: P_DM_IsFDBeingMovedToAnActivePartition(states[i], states[i+1], fd_id)
                        ==> DM_IsFDClearVal(states[i+1].objects, fd_id)
        ensures forall do_id :: P_DM_IsDOBeingMovedToAnActivePartition(states[i], states[i+1], do_id)
                        ==> DM_IsDOClearVal(states[i+1].objects, do_id)
    {
        var ws := states[i];
        var ws' := DM_CalcNewState(states[i], t.ops[i]).0;
        assert ws' == states[i+1];
        assert DM_IsSecureOps(ws, ws');

        Lemma_DM_ProveSP2_Private(ws, ws');
    }
}

// Return if the TD is moved to an active partition, and the TD is not a 
// hardcoded TD
predicate P_DM_IsNonHCodedTDBeingMovedToAnActivePartition(ws:DM_State, ws':DM_State, td_id:TD_ID)
    requires MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds)
{
    td_id in ws'.objects.tds &&
    ws'.objects.tds[td_id].pid != ws.objects.tds[td_id].pid &&
    ws'.objects.tds[td_id].pid != NULL &&
        // For a transition from ws to ws', if a TD is activated (or moved) into an
        // active partition
    td_id !in DM_AllHCodedTDIDs(ws'.subjects)
        // TD is not a hardcoded TD
}

predicate P_DM_IsFDBeingMovedToAnActivePartition(ws:DM_State, ws':DM_State, fd_id:FD_ID)
    requires MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds)
{
    fd_id in ws'.objects.fds &&
    ws'.objects.fds[fd_id].pid != ws.objects.fds[fd_id].pid &&
    ws'.objects.fds[fd_id].pid != NULL
    // For a transition from ws to ws', if a FD is activated (or moved) into an 
    // active partition
}

predicate P_DM_IsDOBeingMovedToAnActivePartition(ws:DM_State, ws':DM_State, do_id:DO_ID)
    requires MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos)
{
    do_id in ws'.objects.dos &&
    ws'.objects.dos[do_id].pid != ws.objects.dos[do_id].pid &&
    ws'.objects.dos[do_id].pid != NULL
    // For a transition from ws to ws', if a DO is activated (or moved) into an 
    // active partition
}




//******** Prove Initial State Is Secure, Theorem 1 and 2 ********//
lemma Lemma_DM_ProveInitialStateIsSecure(ws0:DM_State)
    requires DM_IsValidState_Subjects(ws0) && DM_IsValidState_Objects(ws0)

    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws0)
        // Initial State Setup: If a subject owns an object, then the subject 
        // and the object must be in the same partition
    requires DM_IsValidState_TDsToAllStates(ws0)
        // Initial State Setup: Any combination of values of any set of TDs is 
        // a finite set
    requires DM_IsValidState_DevsActivateCond(ws0)
        // Initial State Setup: A correct data structure for a subset of 
        // devices, describing when a device can be activated
    
    requires NULL !in ws0.pids
    requires ws0.pids == {ws0.red_pid}
        // Initial State Setup: Only the red partition exists

    requires forall s_id :: s_id in DM_AllSubjsIDs(ws0.subjects)
                ==> DM_SubjPID(ws0.subjects, s_id) == NULL || DM_SubjPID(ws0.subjects, s_id) == ws0.red_pid
    requires forall o_id :: o_id in DM_AllObjsIDs(ws0.objects)
                ==> DM_ObjPID(ws0.objects, o_id) == NULL || DM_ObjPID(ws0.objects, o_id) == ws0.red_pid
        // Initial State Setup: All subjects and objects are either inactive 
        // or in the red partition

    requires DM_IsSecureState_SI1(ws0)
        // Initial State Setup: The snapshot of red TDs must be from the  
        // abstraction of hardware protection mechanisms

    ensures DM_IsValidState(ws0) && DM_IsSecureState(ws0)
{
    var k := DMStateToState(ws0);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws0, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws0, k);
    forall s_id | s_id in AllSubjsIDs(k.subjects) && SubjPID(k, s_id) != NULL
        ensures SubjPID(k, s_id) in k.pids
    {
        assert SubjPID(k, s_id) == ws0.red_pid;
    }

    forall o_id | o_id in AllObjsIDs(k.objects) && ObjPID(k, o_id) != NULL
        ensures ObjPID(k, o_id) in k.pids
    {
        assert ObjPID(k, o_id) == ws0.red_pid;
    }
}

// Theorem 1: If state wsn is reached after the application of trace t, and the
// beginning state t.ws0 is secure, then wsn is secure
lemma Lemma_DM_ProveTheorem1(t:DM_Trace, wsn:DM_State)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties
    requires DM_IsValidTrace(t)

    requires wsn == DM_CalcNewStates(t)[|DM_CalcNewStates(t)|-1]

    ensures DM_IsValidState(wsn) && DM_IsSecureState(wsn)
{
    // Dafny can automatically prove this lemma
}

// Theorem 2: For all traces from secure state ws0 to secure state wsn, the
// state transitions of the trace fulfill all transition contraints
lemma Lemma_DM_ProveTheorem2(ws0:DM_State, wsn:DM_State)
    requires DM_IsValidState(ws0) && DM_IsSecureState(ws0)
    requires DM_IsValidState(wsn) && DM_IsSecureState(wsn)
    
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties
    
    ensures forall t:DM_Trace :: |t.ops| > 0 &&
                    t.ws0 == ws0 &&
                    DM_IsValidTrace(t) &&
                    wsn == DM_CalcNewStates(t)[|DM_CalcNewStates(t)|-1]
                        // Trace t transits ws0 to wsn
                ==> (forall i :: 0 <= i < |t.ops| 
                        ==> (forall dev_id :: dev_id in DM_CalcNewStates(t)[i].subjects.devs
                                ==> DM_CalcNewStates(t)[i].subjects.devs[dev_id].hcoded_td_id in DM_CalcNewStates(t)[i].objects.tds) && // Needed by DM_IsSecureOps
                            DM_IsSecureOps(DM_CalcNewStates(t)[i], DM_CalcNewStates(t)[i+1]))
                        // Each transition in trace satisfies all TCs
{
    forall t:DM_Trace | |t.ops| > 0 &&
                    t.ws0 == ws0 &&
                    DM_IsValidTrace(t) &&
                    wsn == DM_CalcNewStates(t)[|DM_CalcNewStates(t)|-1]
        ensures forall i :: 0 <= i < |t.ops| 
                    ==> (forall dev_id :: dev_id in DM_CalcNewStates(t)[i].subjects.devs
                                ==> DM_CalcNewStates(t)[i].subjects.devs[dev_id].hcoded_td_id in DM_CalcNewStates(t)[i].objects.tds) &&
                        DM_IsSecureOps(DM_CalcNewStates(t)[i], DM_CalcNewStates(t)[i+1])
    {
        var states_seq := DM_CalcNewStates(t);
        forall i | 0 <= i < |t.ops|
            ensures forall dev_id :: dev_id in states_seq[i].subjects.devs
                                ==> states_seq[i].subjects.devs[dev_id].hcoded_td_id in states_seq[i].objects.tds
            ensures DM_IsSecureOps(states_seq[i], states_seq[i+1])
        {
            assert DM_IsValidState(states_seq[i]);
            Lemma_ValidDM_HCodedTDsAreTDs(states_seq[i]);
        }
    }
}




//******** Utility Predicates And Functions for High Level Theorems And Security Properties ********//
// If the operation (<op>) is one of the defined operations, then the requirements
// of the operation always implies the properties of the operation
// Note: All operations in Model.dfy are proved to satisfy P_WS_OpsProperties
predicate P_DM_OpsProperties(ws:DM_State, op:DM_Op)
{
    (op.DM_RedDrvReadOp? ==> P_DM_OpsProperties_RedDrvReadOp(ws, op)) &&
    (op.DM_GreenDrvReadOp? ==> P_DM_OpsProperties_GreenDrvReadOp(ws, op)) &&
    (op.DM_DevReadOp? ==> P_DM_OpsProperties_DevReadOp(ws, op)) &&
    (op.DM_RedDrvWriteOp? ==> P_DM_OpsProperties_RedDrvWriteOp(ws, op)) &&
    (op.DM_GreenDrvWriteOp? ==> P_DM_OpsProperties_GreenDrvWriteOp(ws, op)) &&
    (op.DM_RedDevWriteOp? ==> P_DM_OpsProperties_RedDevWriteOp(ws, op)) &&
    (op.DM_GreenDevWriteOp? ==> P_DM_OpsProperties_GreenDevWriteOp(ws, op)) &&

    (op.DM_EmptyPartitionCreateOp? ==> P_DM_OpsProperties_EmptyPartitionCreateOp(ws, op)) &&
    (op.DM_EmptyPartitionDestroyOp? ==> P_DM_OpsProperties_EmptyPartitionDestroyOp(ws, op)) &&
    (op.DM_DrvActivateToGreenPartitionOp? ==> P_DM_OpsProperties_DrvActivateToGreenPartitionOp(ws, op)) &&
    (op.DM_GreenDrvDeactivateOp? ==> P_DM_OpsProperties_GreenDrvDeactivateOp(ws, op)) &&
    (op.DM_DevActivateOp? ==> P_DM_OpsProperties_DevActivateOp(ws, op)) &&
    (op.DM_DevDeactivateOp? ==> P_DM_OpsProperties_DevDeactivateOp(ws, op)) &&
    (op.DM_ExternalObjsActivateToGreenPartitionOp? ==> P_DM_OpsProperties_ExternalObjsActivateToGreenPartitionOp(ws, op)) &&
    (op.DM_GreenExternalObjsDeactivateOp? ==> P_DM_OpsProperties_GreenExternalObjsDeactivateOp(ws, op))
}

// If the operation (<op>) fulfill its preconditions
predicate P_DM_OpsFulfillPreConditions(ws:DM_State, op:DM_Op)
{
    (op.DM_RedDrvReadOp? ==> DM_RedDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.DM_GreenDrvReadOp? ==> DM_GreenDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.DM_DevReadOp? ==> DM_DevRead_PreConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.DM_RedDrvWriteOp? ==> DM_RedDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.DM_GreenDrvWriteOp? ==> DM_GreenDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.DM_RedDevWriteOp? ==> DM_RedDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.DM_GreenDevWriteOp? ==> DM_GreenDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&

    (op.DM_EmptyPartitionCreateOp? ==> DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (op.DM_EmptyPartitionDestroyOp? ==> DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (op.DM_DrvActivateToGreenPartitionOp? ==> (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                        Drv_ID(op.drv_sid) in ws.subjects.drvs &&
                        op.green_pid != NULL &&
                        op.green_pid != ws.red_pid)) &&
    (op.DM_GreenDrvDeactivateOp? ==> (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                        Drv_ID(op.drv_sid) in ws.subjects.drvs &&
                        DM_SubjPID(ws.subjects, op.drv_sid) != NULL &&
                        DM_SubjPID(ws.subjects, op.drv_sid) != ws.red_pid)) &&
    (op.DM_DevActivateOp? ==> (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
                        Dev_ID(op.dev_sid) in ws.subjects.devs &&
                        op.pid != NULL)) &&
    (op.DM_DevDeactivateOp? ==> DM_DevDeactivate_PreConditions(ws, op.dev_sid)) &&
    (op.DM_ExternalObjsActivateToGreenPartitionOp? ==> DM_ExternalObjsActivateToGreenPartition_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid)) &&
    (op.DM_GreenExternalObjsDeactivateOp? ==> DM_GreenExternalObjsDeactivate_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid))
}

// Valid trace: all intermediate ws and op fulfill all preconditions of the 
// corresponding operation
predicate DM_IsValidTrace(t:DM_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        true
    else
        var b1 := P_DM_OpsFulfillPreConditions(t.ws0, t.ops[0]);
        if(!b1) then 
            false
        else
            var k1 := DM_CalcNewState(t.ws0, t.ops[0]).0; // Eval t.ops[0]
            b1 && DM_IsValidTrace(DM_Trace(k1, t.ops[1..]))
}

// Given a secure state and a transition, calculate the result state
function DM_CalcNewState(ws:DM_State, op:DM_Op) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires P_DM_OpsProperties(ws, op)
    requires P_DM_OpsFulfillPreConditions(ws, op)

    ensures DM_IsValidState(result.0) && DM_IsSecureState(result.0) // result.0 is the new State
    ensures DM_IsSecureOps(ws, result.0)
{
    if(op.DM_RedDrvReadOp?) then
        var ws', ws_d :| DM_RedDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, ws', ws_d) &&
                            (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src); (ws', ws_d)
    else if(op.DM_GreenDrvReadOp?) then
        var ws', ws_d :| DM_GreenDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, ws', ws_d) &&
                            (ws', ws_d) == DM_GreenDrvReadRead_InnerFunc(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src); (ws', ws_d)
    else if (op.DM_DevReadOp?) then
        var ws', ws_d :| DM_DevRead_PostConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, ws', ws_d) &&
                            (ws', ws_d) == DM_DevRead_InnerFunc(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src); (ws', ws_d)
    else if (op.DM_RedDrvWriteOp?) then
        var ws', ws_d :| DM_RedDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                            ws' == DM_RedDrvWrite_InnerFunc(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map).1 &&
                            ws_d == DM_RedDrvWrite_InnerFunc(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map).2; (ws', ws_d)
    else if (op.DM_GreenDrvWriteOp?) then
        var ws', ws_d :| DM_GreenDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                            (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map); (ws', ws_d)
    else if (op.DM_RedDevWriteOp?) then
        var ws', ws_d :| DM_RedDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                            (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map); (ws', ws_d)
    else if (op.DM_GreenDevWriteOp?) then
        var ws', ws_d :| DM_GreenDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                            (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map); (ws', ws_d)

    else if (op.DM_EmptyPartitionCreateOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, op.new_pid); (ws', ws_d)
    else if (op.DM_EmptyPartitionDestroyOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, op.pid); (ws', ws_d)
    else if (op.DM_DrvActivateToGreenPartitionOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, op.drv_sid, op.green_pid); (ws', ws_d) 
    else if (op.DM_GreenDrvDeactivateOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, op.drv_sid); (ws', ws_d)
    else if (op.DM_DevActivateOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_DevActivate_InnerFunc(ws, op.dev_sid, op.pid); (ws', ws_d)
    else if (op.DM_DevDeactivateOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, op.dev_sid); (ws', ws_d)
    else if (op.DM_ExternalObjsActivateToGreenPartitionOp?) then
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) && 
                         (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid); (ws', ws_d)
    else
        var ws', ws_d :| DM_Common_PostConditions(ws, ws', ws_d) &&
                        (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid); (ws', ws_d)
}

// Given a trace, calculate all the reached states
// (needs 70s to verify)
function DM_CalcNewStates(t:DM_Trace) : (states:seq<DM_State>)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any ws satisfies 
        // P_DM_OpsProperties

    requires DM_IsValidTrace(t)

    ensures |states| == |t.ops| + 1
    ensures forall i :: 0 <= i <= |states| - 1
                ==> DM_IsValidState(states[i]) && DM_IsSecureState(states[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> DM_IsSecureOps(states[i], states[i+1])
        // Properties from DM_CalcNewState
    ensures forall i :: 0 <= i < |states| - 1
                ==> P_DM_OpsFulfillPreConditions(states[i], t.ops[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> states[i+1] == DM_CalcNewState(states[i], t.ops[i]).0
        // Property: <states> form a chain
    ensures states[0] == t.ws0

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        [t.ws0]
    else
        var ws1 := DM_CalcNewState(t.ws0, t.ops[0]).0; // Eval t.ops[0]
        var step_states := DM_CalcNewStates(DM_Trace(ws1, t.ops[1..]));
        var result_states := [t.ws0] + step_states;
        assert DM_IsValidState(ws1) && DM_IsSecureState(ws1);
        assert P_DM_OpsFulfillPreConditions(t.ws0, t.ops[0]);

        Lemma_DM_CalcNewStates_Private1(t.ws0, step_states, result_states);
        assert t.ops == [t.ops[0]] + t.ops[1..];
        Lemma_DM_CalcNewStates_Private2(t.ws0, step_states, result_states, t.ops[0], DM_Trace(ws1, t.ops[1..]), t);
        result_states
}




//******** Private Lemmas  ********//

lemma Lemma_DM_CalcNewStates_Private1(state:DM_State, step_states:seq<DM_State>, result_states:seq<DM_State>)
    requires forall i :: 0 <= i <= |step_states| - 1
                ==> DM_IsValidState(step_states[i]) && DM_IsSecureState(step_states[i])
    requires DM_IsValidState(state) && DM_IsSecureState(state)

    requires result_states == [state] + step_states

    ensures forall i :: 0 <= i <= |result_states| - 1
                ==> DM_IsValidState(result_states[i]) && DM_IsSecureState(result_states[i])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_CalcNewStates_Private2(state:DM_State, step_states:seq<DM_State>, result_states:seq<DM_State>, op:DM_Op, step_t:DM_Trace, t:DM_Trace)
    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_DM_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires P_DM_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops

    ensures forall i :: 0 <= i < |result_states| - 1
                ==> P_DM_OpsFulfillPreConditions(result_states[i], t.ops[i])
{
    forall i | 0 <= i < |result_states| - 1
        ensures P_DM_OpsFulfillPreConditions(result_states[i], t.ops[i])
    {
        if (i == 0)
        {
            assert result_states[i] == state;
            assert t.ops[i] == op;
        }
        else
        {
            assert result_states[i] == step_states[i-1];
            assert t.ops[i] == step_t.ops[i-1];
        }
    }
}

lemma Lemma_ValidDM_HCodedTDsAreTDs(ws:DM_State)
    requires DM_IsValidState(ws)
    ensures forall dev_id :: dev_id in ws.subjects.devs
        ==> ws.subjects.devs[dev_id].hcoded_td_id in ws.objects.tds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ProveSP2_Private(ws:DM_State, ws':DM_State)
    requires DM_IsValidState(ws) 
    requires DM_IsSecureOps(ws, ws')

    ensures forall td_id :: P_DM_IsNonHCodedTDBeingMovedToAnActivePartition(ws, ws', td_id)
                    ==> DM_IsTDClearVal(ws'.objects, td_id)
    ensures forall fd_id :: P_DM_IsFDBeingMovedToAnActivePartition(ws, ws', fd_id)
                    ==> DM_IsFDClearVal(ws'.objects, fd_id)
    ensures forall do_id :: P_DM_IsDOBeingMovedToAnActivePartition(ws, ws', do_id)
                    ==> DM_IsDOClearVal(ws'.objects, do_id) 
{
    // Dafny can automatically prove this lemma
}