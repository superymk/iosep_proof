include "SecurityProperties_Ops.dfy"

// Proof of the Security Property 1: Forall traces starting from a secure state,
// no I/O access (as operations) crosses partition
lemma Lemma_WS_ProveSP1(t:WS_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_WS_OpsProperties
    requires WS_IsValidTrace(t)
            
    ensures forall i, states:seq<DM_State> :: 0 <= i < |t.ops| && states == WS_CalcNewStates(t)
                ==> (t.ops[i].WS_OSDrvReadOp? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].WS_WimpDrvReadOp? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid,
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].WS_OSDrvWrite_Op? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].WS_WimpDrvWrite_Op? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].WS_DevRead_Op? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid,
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].WS_OSDevWrite_Op? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].WS_WimpDevWrite_Op? && WS_CalcNewState(states[i], t.ops[i]).2 == true // allow access
                        ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the device
                    )
{
    // Dafny can automatically prove this lemma
}

// Proof of the Security Property 2: Only hardcoded TDs can be reused in a 
// new partition
lemma Lemma_WS_ProveSP2(t:WS_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_WS_OpsProperties
    requires WS_IsValidTrace(t)
    
    ensures forall i, states:seq<DM_State> :: 0 <= i < |t.ops| && states == WS_CalcNewStates(t)
                ==> MapGetKeys(states[i+1].objects.tds) == MapGetKeys(states[i].objects.tds) &&
                    MapGetKeys(states[i+1].objects.fds) == MapGetKeys(states[i].objects.fds) &&
                    MapGetKeys(states[i+1].objects.dos) == MapGetKeys(states[i].objects.dos)
        // Property needed by the following property
    ensures forall i, states:seq<DM_State> :: 0 <= i < |t.ops| && states == WS_CalcNewStates(t)
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
    var states := WS_CalcNewStates(t);
    
    forall i | 0 <= i < |t.ops|
        ensures MapGetKeys(states[i+1].objects.tds) == MapGetKeys(states[i].objects.tds)
        ensures MapGetKeys(states[i+1].objects.fds) == MapGetKeys(states[i].objects.fds)
        ensures MapGetKeys(states[i+1].objects.dos) == MapGetKeys(states[i].objects.dos)
    {
        var ws := states[i];
        var ws' := WS_CalcNewState(states[i], t.ops[i]).1;
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
        var ws' := WS_CalcNewState(states[i], t.ops[i]).1;
        assert ws' == states[i+1];
        assert DM_IsSecureOps(ws, ws');

        Lemma_WS_ProveSP2_Private(ws, ws');
    }
}




//******** Prove Initial State Is Secure, Theorem 1 and 2 ********//
// [Note] Same initial state as the one in the detailed model
lemma Lemma_WS_ProveInitialStateIsSecure(ws0:DM_State)
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
    // Same initial state as the one in the detailed model
    Lemma_DM_ProveInitialStateIsSecure(ws0); 
}

// Theorem 1: If state wsn is reached after the application of trace t, and the
// beginning state t.ws0 is secure, then wsn is secure
lemma Lemma_WS_ProveTheorem1(t:WS_Trace, wsn:DM_State)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_WS_OpsProperties
    requires WS_IsValidTrace(t)

    requires wsn == WS_CalcNewStates(t)[|WS_CalcNewStates(t)|-1]

    ensures DM_IsValidState(wsn) && DM_IsSecureState(wsn)
{
    // Dafny can automatically prove this lemma
}

// Theorem 2: For all traces from secure state ws0 to secure state wsn, the
// state transitions of the trace fulfill all transition contraints (TCs)
// Note: The TCs are same as ones in the detailed model
lemma Lemma_WS_ProveTheorem2(ws0:DM_State, wsn:DM_State)
    requires DM_IsValidState(ws0) && DM_IsSecureState(ws0)
    requires DM_IsValidState(wsn) && DM_IsSecureState(wsn)
    
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_WS_OpsProperties
    
    ensures forall t:WS_Trace :: |t.ops| > 0 &&
                    t.ws0 == ws0 &&
                    WS_IsValidTrace(t) &&
                    wsn == WS_CalcNewStates(t)[|WS_CalcNewStates(t)|-1]
                        // Trace t transits ws0 to wsn
                ==> (forall i :: 0 <= i < |t.ops| 
                        ==> (forall dev_id :: dev_id in WS_CalcNewStates(t)[i].subjects.devs
                                ==> WS_CalcNewStates(t)[i].subjects.devs[dev_id].hcoded_td_id in WS_CalcNewStates(t)[i].objects.tds) && // Needed by DM_IsSecureOps
                            DM_IsSecureOps(WS_CalcNewStates(t)[i], WS_CalcNewStates(t)[i+1]))
                        // Each transition in trace satisfies all TCs
{
    forall t:WS_Trace | |t.ops| > 0 &&
                    t.ws0 == ws0 &&
                    WS_IsValidTrace(t) &&
                    wsn == WS_CalcNewStates(t)[|WS_CalcNewStates(t)|-1]
        ensures forall i :: 0 <= i < |t.ops| 
                    ==> (forall dev_id :: dev_id in WS_CalcNewStates(t)[i].subjects.devs
                                ==> WS_CalcNewStates(t)[i].subjects.devs[dev_id].hcoded_td_id in WS_CalcNewStates(t)[i].objects.tds) &&
                        DM_IsSecureOps(WS_CalcNewStates(t)[i], WS_CalcNewStates(t)[i+1])
    {
        var states_seq := WS_CalcNewStates(t);
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
predicate P_WS_OpsProperties(ws:DM_State, op:WS_Op)
{
    (op.WS_OSDrvReadOp? ==> P_WS_OSDrvRead_Op(ws, op)) &&
    (op.WS_WimpDrvReadOp? ==> P_WS_WimpDrvRead_Op(ws, op)) &&
    (op.WS_DevRead_Op? ==> P_WS_DevRead_Op(ws, op)) &&
    (op.WS_OSDrvWrite_Op? ==> P_WS_OSDrvWrite_Op(ws, op)) &&
    (op.WS_WimpDrvWrite_Op? ==> P_WS_WimpDrvWrite_Op(ws, op)) &&
    (op.WS_OSDevWrite_Op? ==> P_WS_OSDevWrite_Op(ws, op)) &&
    (op.WS_WimpDevWrite_Op? ==> P_WS_WimpDevWrite_Op(ws, op)) && 

    (op.WK_WimpDrvsDevs_Registration_CreatePartition_Op? ==> P_WK_WimpDrvsDevs_Registration_CreatePartition_Op(ws, op)) &&
    (op.WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op? ==> P_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(ws, op)) &&
    (op.WK_WimpDrvsDevs_Unregistration_Op? ==> P_WK_WimpDrvsDevs_Unregistration_Op(ws, op)) &&

    (true)
}

// Return if the operation (<op>) fulfill its preconditions
predicate P_WS_OpsFulfillPreConditions(ws:DM_State, op:WS_Op)
{
    (op.WS_OSDrvReadOp? ==> WS_OSDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.WS_WimpDrvReadOp? ==> WS_WimpDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.WS_DevRead_Op? ==> WS_DevRead_PreConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.WS_OSDrvWrite_Op? ==> WS_OSDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.WS_WimpDrvWrite_Op? ==> WS_WimpDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.WS_OSDevWrite_Op? ==> WS_OSDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.WS_WimpDevWrite_Op? ==> WS_WimpDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&

    (op.WK_WimpDrvsDevs_Registration_CreatePartition_Op? ==> WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)) &&
    (op.WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op? ==> WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
                ws, op.to_deactivate_dev_id, op.to_assign_drv_ids, op.to_assign_dev_ids,
                op.to_assign_external_td_ids, op.to_assign_external_fd_ids, op.to_assign_external_do_ids, op.green_pid)) &&
    (op.WK_WimpDrvsDevs_Unregistration_Op? ==> WK_WimpDrvsDevs_Unregistration_PreConditions(
                ws, op.to_deactivate_drv_ids, op.to_deactivate_dev_ids, op.devs_to_activate_in_red,
                op.to_deactivate_external_td_ids, op.to_deactivate_external_fd_ids, op.to_deactivate_external_do_ids, op.green_pid)) &&

    (true)
}

// Valid trace: all intermediate ws and op fulfill all preconditions of the 
// corresponding operation
predicate WS_IsValidTrace(t:WS_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    decreases |t.ops|
{
    if(|t.ops| == 0) then
        true
    else
        var b1 := P_WS_OpsFulfillPreConditions(t.ws0, t.ops[0]);
        if(!b1) then 
            false
        else
            var k1 := WS_CalcNewState(t.ws0, t.ops[0]).1; // Eval t.ops[0]
            b1 && WS_IsValidTrace(WS_Trace(k1, t.ops[1..]))
}

// Given a secure state and a transition, calculate the result state
function WS_CalcNewState(ws:DM_State, op:WS_Op) : (result:(DM_Trace, DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires P_WS_OpsProperties(ws, op)
    requires P_WS_OpsFulfillPreConditions(ws, op)

    ensures DM_IsValidState(result.1) && DM_IsSecureState(result.1) // result.1 is the new State
    ensures DM_IsSecureOps(ws, result.1)
    ensures DM_IsValidState(result.0.ws0) && DM_IsSecureState(result.0.ws0)
    ensures DM_IsValidTrace(result.0)
        // Property: Returned DM_Trace must be valid
    ensures result.1 == SeqLastElem(DM_CalcNewStates(result.0))
        // Property: Corresponding result state in detailed model is the expected one
{
    if(op.WS_OSDrvReadOp?) then
        var t, ws', ws_d :| WS_OSDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WS_WimpDrvReadOp?) then
        var t, ws', ws_d :| WS_WimpDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WS_DevRead_Op?) then
        var t, ws', ws_d :| WS_DevRead_PostConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WS_OSDrvWrite_Op?) then
        var t, ws', ws_d :| WS_OSDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WS_WimpDrvWrite_Op?) then
        var t, ws', ws_d :| WS_WimpDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WS_OSDevWrite_Op?) then
        var t, ws', ws_d :| WS_OSDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WS_WimpDevWrite_Op?) then
        var t, ws', ws_d :| WS_WimpDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WK_WimpDrvsDevs_Registration_CreatePartition_Op?) then
        var t, ws', ws_d :| WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(ws, t, ws', ws_d); (t, ws', ws_d)
    else if(op.WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op?) then
        var t, ws', ws_d :| WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(ws, 
                op.to_deactivate_dev_id, op.to_assign_drv_ids, op.to_assign_dev_ids,
                op.to_assign_external_td_ids, op.to_assign_external_fd_ids, op.to_assign_external_do_ids, op.green_pid, t, ws', ws_d); (t, ws', ws_d)
    else
        var t, ws', ws_d :| WK_WimpDrvsDevs_Unregistration_PostConditions(ws, 
                op.to_deactivate_drv_ids, op.to_deactivate_dev_ids, op.devs_to_activate_in_red,
                op.to_deactivate_external_td_ids, op.to_deactivate_external_fd_ids, op.to_deactivate_external_do_ids, op.green_pid, t, ws', ws_d); (t, ws', ws_d)
}

// Given a trace, calculate the corresponding trace in the detailed model
function WS_CalcDMTrace(t:WS_Trace) : (dmt:DM_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    requires WS_IsValidTrace(t)

    ensures dmt.ws0 == t.ws0
    ensures DM_IsValidTrace(dmt)

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        DM_Trace(t.ws0, [])
    else
        var dmt := WS_CalcNewState(t.ws0, t.ops[0]).0; // Eval t.ops[0]
        var ws1 := WS_CalcNewState(t.ws0, t.ops[0]).1;
        var step_dmt := WS_CalcDMTrace(WS_Trace(ws1, t.ops[1..]));

        assert DM_IsValidTrace(dmt);
        assert DM_IsValidTrace(step_dmt);
        assert step_dmt.ws0 == ws1;
        var result_dmt := ValidDMTrace_Concat(dmt, step_dmt);

        result_dmt
}

// Given a trace, calculate all the reached states
// (needs 40s to verify)
function WS_CalcNewStates(t:WS_Trace) : (states:seq<DM_State>)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties

    requires WS_IsValidTrace(t)

    ensures |states| == |t.ops| + 1
    ensures forall i :: 0 <= i <= |states| - 1
                ==> DM_IsValidState(states[i]) && DM_IsSecureState(states[i])
        // Properties from DM_CalcNewState
    ensures forall i :: 0 <= i < |states| - 1
                ==> P_WS_OpsFulfillPreConditions(states[i], t.ops[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> states[i+1] == WS_CalcNewState(states[i], t.ops[i]).1
        // Property: <states> form a chain
    ensures states[0] == t.ws0

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        [t.ws0]
    else
        var ws1 := WS_CalcNewState(t.ws0, t.ops[0]).1; // Eval t.ops[0]
        var step_states := WS_CalcNewStates(WS_Trace(ws1, t.ops[1..]));
        var result_states := [t.ws0] + step_states;
        assert DM_IsValidState(ws1) && DM_IsSecureState(ws1);
        assert P_WS_OpsFulfillPreConditions(t.ws0, t.ops[0]);

        Lemma_DM_CalcNewStates_Private1(t.ws0, step_states, result_states);
        assert t.ops == [t.ops[0]] + t.ops[1..];
        Lemma_WS_CalcNewStates_Private2(t.ws0, step_states, result_states, t.ops[0], WS_Trace(ws1, t.ops[1..]), t);
        result_states
}




//******** Private Lemmas ********//
lemma Lemma_WS_CalcNewStates_Private2(state:DM_State, step_states:seq<DM_State>, result_states:seq<DM_State>, op:WS_Op, step_t:WS_Trace, t:WS_Trace)
    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_WS_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires P_WS_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops

    ensures forall i :: 0 <= i < |result_states| - 1
                ==> P_WS_OpsFulfillPreConditions(result_states[i], t.ops[i])
{
    Lemma_Seq_JumpFirstElem(result_states, step_states, state);
    Lemma_Seq_JumpFirstElem(t.ops, step_t.ops, op);

    forall i | 0 <= i < |result_states| - 1
        ensures P_WS_OpsFulfillPreConditions(result_states[i], t.ops[i])
    {
        if (i == 0)
        {
            assert result_states[i] == state;
            assert t.ops[i] == op;
        }
        else
        {
            assert result_states == [state] + step_states;
            assert t.ops == [op] + step_t.ops;

            assert result_states[i] == step_states[i-1];
            assert t.ops[i] == step_t.ops[i-1];
        }
    }
}

lemma Lemma_WS_ProveSP2_Private(ws:DM_State, ws':DM_State)
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




//******** Lemma Unneeded for Now ********//
lemma Lemma_IfWSTraceIsValid_ThenDMTraceIsValid(t:WS_Trace)
    requires DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
        // Requirement: The trace <t> starts from a secure state
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires forall ws:DM_State, op:WS_Op :: P_WS_OpsProperties(ws, op)
        // [Note] For any operations defined in this model, any state satisfies 
        // P_DM_OpsProperties
    requires WS_IsValidTrace(t)

    ensures DM_IsValidTrace(WS_CalcDMTrace(t))
{
    // Dafny can automatically prove this lemma
}