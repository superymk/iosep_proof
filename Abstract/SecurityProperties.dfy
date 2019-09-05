include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"
include "Lemmas_SubjActivate_Ops.dfy"
include "Lemmas_SubjActivate_ReachableTDsStates.dfy"
include "Lemmas_SubjDeactivate_Ops.dfy"
include "./BuildCAS/BuildCAS.dfy"
include "SecurityProperties_Ops.dfy"





//******** Prove Security Properties ********//
// Proof of the Security Property 1: Forall traces starting from a secure state,
// no I/O access (as operations) crosses partition
lemma Lemma_ProveSP1(t:Trace)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties
    requires IsValidTrace(t)
            
    ensures forall i, states:seq<State> :: 0 <= i < |t.ops| && states == K_CalcNewStates(t)
                ==> (t.ops[i].DrvReadOp? && K_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DrvWriteOp? && K_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    ) &&
                    (t.ops[i].DevReadOp? && K_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                                                // Objects are in the same partition with the device
                    ) &&
                    (t.ops[i].DevWriteOp? && K_CalcNewState(states[i], t.ops[i]).1 == true // allow access
                        ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                                                // Objects are in the same partition with the driver
                    )
{
    Lemma_ProveSP1_Reads(t);
    Lemma_ProveSP1_Writes(t);
}

// Proof of the Security Property 2: Only hardcoded TDs can be reused in a 
// new partition
lemma Lemma_ProveSP2(t:Trace)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties
    requires IsValidTrace(t)
    
    ensures forall i, states:seq<State> :: 0 <= i < |t.ops| && states == K_CalcNewStates(t)
                ==> MapGetKeys(states[i+1].objects.tds) == MapGetKeys(states[i].objects.tds) &&
                    MapGetKeys(states[i+1].objects.fds) == MapGetKeys(states[i].objects.fds) &&
                    MapGetKeys(states[i+1].objects.dos) == MapGetKeys(states[i].objects.dos)
        // Property needed by the following property
    ensures forall i, states:seq<State> :: 0 <= i < |t.ops| && states == K_CalcNewStates(t)
                ==> (forall td_id :: P_IsNonHCodedTDBeingMovedToAnActivePartition(states[i], states[i+1], td_id)
                        ==> IsTDClearVal(states[i+1].objects.tds, td_id)
                    ) && 
                    (forall fd_id :: P_IsFDBeingMovedToAnActivePartition(states[i], states[i+1], fd_id)
                        ==> IsFDClearVal(states[i+1].objects.fds, fd_id) 
                    ) &&
                    (forall do_id :: P_IsDOBeingMovedToAnActivePartition(states[i], states[i+1], do_id)
                        ==> IsDOClearVal(states[i+1].objects.dos, do_id))
        // Main property: Only hardcoded TDs can be reused in a new partition
{
    var states := K_CalcNewStates(t);
    
    forall i | 0 <= i < |t.ops|
        ensures MapGetKeys(states[i+1].objects.tds) == MapGetKeys(states[i].objects.tds)
        ensures MapGetKeys(states[i+1].objects.fds) == MapGetKeys(states[i].objects.fds)
        ensures MapGetKeys(states[i+1].objects.dos) == MapGetKeys(states[i].objects.dos)
    {
        var k := states[i];
        var k' := K_CalcNewState(states[i], t.ops[i]).0;
        assert IsSecureOps(k, k');
    }
}

// Return if the TD is moved to an active partition, and the TD is not a 
// hardcoded TD
predicate P_IsNonHCodedTDBeingMovedToAnActivePartition(k:State, k':State, td_id:TD_ID)
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)
{
    td_id in k'.objects.tds &&
    k'.objects.tds[td_id].pid != k.objects.tds[td_id].pid &&
    k'.objects.tds[td_id].pid != NULL &&
        // For a transition from k to k', if a TD is activated (or moved) into an
        // active partition
    td_id !in AllHCodedTDIDs(k'.subjects)
        // TD is not a hardcoded TD
}

predicate P_IsFDBeingMovedToAnActivePartition(k:State, k':State, fd_id:FD_ID)
    requires MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds)
{
    fd_id in k'.objects.fds &&
    k'.objects.fds[fd_id].pid != k.objects.fds[fd_id].pid &&
    k'.objects.fds[fd_id].pid != NULL
    // For a transition from k to k', if a FD is activated (or moved) into an 
    // active partition
}

predicate P_IsDOBeingMovedToAnActivePartition(k:State, k':State, do_id:DO_ID)
    requires MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos)
{
    do_id in k'.objects.dos &&
    k'.objects.dos[do_id].pid != k.objects.dos[do_id].pid &&
    k'.objects.dos[do_id].pid != NULL
    // For a transition from k to k', if a DO is activated (or moved) into an 
    // active partition
}




//******** Prove Initial State Is Secure, Theorem 1 and 2 ********//
lemma Lemma_ProveInitialStateIsSecure(k0:State)
    requires IsValidState_Subjects(k0) && IsValidState_Objects(k0)
        // Requirement: IDs are unique, No two subjects own the same object, 
        // etc. We still need these properties for <k0>
    requires forall s_id :: s_id in AllSubjsIDs(k0.subjects)
                ==> SubjPID(k0, s_id) == NULL
    requires forall o_id :: o_id in AllObjsIDs(k0.objects)
                ==> ObjPID(k0, o_id) == NULL 
        // Requirement: All subjects and objects are inactive
    requires k0.pids == {}
        // Requirement: PIDs is empty

    ensures IsValidState(k0) && IsSecureState(k0)
{
    // Dafny can automatically prove this lemma
}

// Theorem 1: If state kn is reached after the application of trace t, and the
// beginning state t.k0 is secure, then kn is secure
lemma Lemma_ProveTheorem1(t:Trace, kn:State)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties
    requires IsValidTrace(t)

    requires kn == K_CalcNewStates(t)[|K_CalcNewStates(t)|-1]

    ensures IsValidState(kn) && IsSecureState(kn)
{
    // Dafny can automatically prove this lemma
}

// Theorem 2: For all traces from secure state k0 to secure state kn, the
// state transitions of the trace fulfill all transition contraints
lemma Lemma_ProveTheorem2(k0:State, kn:State)
    requires IsValidState(k0) && IsSecureState(k0)
    requires IsValidState(kn) && IsSecureState(kn)
    
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties
    
    ensures forall t:Trace :: |t.ops| > 0 &&
                    t.k0 == k0 &&
                    IsValidTrace(t) &&
                    kn == K_CalcNewStates(t)[|K_CalcNewStates(t)|-1]
                        // Trace t transits k0 to kn
                ==> (forall i :: 0 <= i < |t.ops| 
                        ==> (forall dev_id :: dev_id in K_CalcNewStates(t)[i].subjects.devs
                                ==> K_CalcNewStates(t)[i].subjects.devs[dev_id].hcoded_td_id in K_CalcNewStates(t)[i].objects.tds) && // Needed by IsSecureOps
                            IsSecureOps(K_CalcNewStates(t)[i], K_CalcNewStates(t)[i+1]))
                        // Each transition in trace satisfies all TCs
{
    forall t:Trace | |t.ops| > 0 &&
                    t.k0 == k0 &&
                    IsValidTrace(t) &&
                    kn == K_CalcNewStates(t)[|K_CalcNewStates(t)|-1]
        ensures forall i :: 0 <= i < |t.ops| 
                    ==> (forall dev_id :: dev_id in K_CalcNewStates(t)[i].subjects.devs
                                ==> K_CalcNewStates(t)[i].subjects.devs[dev_id].hcoded_td_id in K_CalcNewStates(t)[i].objects.tds) &&
                        IsSecureOps(K_CalcNewStates(t)[i], K_CalcNewStates(t)[i+1])
    {
        var states_seq := K_CalcNewStates(t);
        forall i | 0 <= i < |t.ops|
            ensures forall dev_id :: dev_id in states_seq[i].subjects.devs
                                ==> states_seq[i].subjects.devs[dev_id].hcoded_td_id in states_seq[i].objects.tds
            ensures IsSecureOps(states_seq[i], states_seq[i+1])
        {
            assert IsValidState(states_seq[i]);
            Lemma_ValidK_HCodedTDsAreTDs(states_seq[i]);
        }
    }
}




//******** Utility Predicates And Functions for High Level Theorems And Security Properties ********//
// If the operation (<op>) is one of the operations, then the requirements
// of the operation always implies the properties of the operation
// Note: the requirements and properties of operations must be same with the 
// ones in Model.dfy
predicate P_OpsProperties(k:State, op:Op)
{
    (op.DrvReadOp? ==> P_OpsProperties_DrvReadOp(k, op)) &&
    (op.DevReadOp? ==> P_OpsProperties_DevReadOp(k, op)) &&
    (op.DevWriteOp? ==> P_OpsProperties_DevWriteOp(k, op)) &&
    (op.EmptyPartitionCreateOp? ==> P_OpsProperties_EmptyPartitionCreateOp(k, op)) &&
    (op.EmptyPartitionDestroyOp? ==> P_OpsProperties_EmptyPartitionDestroyOp(k, op)) &&
    (op.DrvActivateOp? ==> P_OpsProperties_DrvActivateOp(k, op)) &&
    (op.DrvDeactivateOp? ==> P_OpsProperties_DrvDeactivateOp(k, op)) &&
    (op.DevActivateOp? ==> P_OpsProperties_DevActivateOp(k, op)) &&
    (op.DevDeactivateOp? ==> P_OpsProperties_DevDeactivateOp(k, op)) &&
    (op.ExternalObjsActivateOp? ==> P_OpsProperties_ExternalObjsActivateOp(k, op)) &&
    (op.ExternalObjsDeactivateOp? ==> P_OpsProperties_ExternalObjsDeactivateOp(k, op)) &&
    (op.DrvWriteOp? ==> P_OpsProperties_DrvWriteOp(k, op))
}

// Return if the operation (<op>) fulfill its preconditions
predicate P_OpsFulfillPreConditions(k:State, op:Op)
{
    (op.DrvReadOp? ==> DrvRead_PreConditions(k, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.DevReadOp? ==> DevRead_PreConditions(k, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)) &&
    (op.DevWriteOp? ==> DevWrite_PreConditions(k, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)) &&
    (op.EmptyPartitionCreateOp? ==> IsValidState(k) && IsSecureState(k)) &&
    (op.EmptyPartitionDestroyOp? ==> IsValidState(k) && IsSecureState(k)) &&
    (op.DrvActivateOp? ==> (IsValidState(k) && IsSecureState(k) &&
                        Drv_ID(op.drv_sid) in k.subjects.drvs &&
                        op.pid != NULL)) &&
    (op.DrvDeactivateOp? ==> (IsValidState(k) && IsSecureState(k) &&
                        Drv_ID(op.drv_sid) in k.subjects.drvs)) &&
    (op.DevActivateOp? ==> (IsValidState(k) && IsSecureState(k) &&
                        Dev_ID(op.dev_sid) in k.subjects.devs &&
                        op.pid != NULL)) &&
    (op.DevDeactivateOp? ==> (IsValidState(k) && IsSecureState(k) &&
                        Dev_ID(op.dev_sid) in k.subjects.devs)) &&
    (op.ExternalObjsActivateOp? ==> ExternalObjsActivate_PreConditions(k, op.td_ids, op.fd_ids, op.do_ids, op.pid)) &&
    (op.ExternalObjsDeactivateOp? ==> ExternalObjsDeactivate_PreConditions(k, op.td_ids, op.fd_ids, op.do_ids, op.obj_pid)) &&
    (op.DrvWriteOp? ==> DrvWrite_PreConditions(k, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map))
}

// Valid trace: all intermediate k and op fulfill all preconditions of the 
// corresponding operation
predicate IsValidTrace(t:Trace)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        true
    else
        var b1 := P_OpsFulfillPreConditions(t.k0, t.ops[0]);
        if(!b1) then 
            false
        else
            var k1 := K_CalcNewState(t.k0, t.ops[0]).0; // Eval t.ops[0]
            b1 && IsValidTrace(Trace(k1, t.ops[1..]))
}

// Given a secure state and a transition, calculate the result state
function K_CalcNewState(k:State, op:Op) : (result:(State, bool))
    requires IsValidState(k) && IsSecureState(k)
    requires P_OpsProperties(k, op)
    requires P_OpsFulfillPreConditions(k, op)

    ensures IsValidState(result.0) && IsSecureState(result.0) // result.0 is the new State
    ensures IsSecureOps(k, result.0)
{
    if(op.DrvReadOp?) then
        var k', d :| DrvRead_PostConditions(k, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, k', d); (k', d)
    else if (op.DevReadOp?) then
        var k', d :| DevRead_PostConditions(k, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, k', d); (k', d)
    else if (op.DevWriteOp?) then
        var k', d :| DevWrite_PostConditions(k, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, k', d); (k', d)
    else if (op.EmptyPartitionCreateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.EmptyPartitionDestroyOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.DrvActivateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.DrvDeactivateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.DevActivateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.DevDeactivateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.ExternalObjsActivateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else if (op.ExternalObjsDeactivateOp?) then
        var k', d :| Common_PostConditions(k, k', d); (k', d)
    else
        var k', d :| DrvWrite_PostConditions(k, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, k', d); (k', d)
}

// Given a trace, calculate all the reached states
// (needs 40s to verify)
function K_CalcNewStates(t:Trace) : (states:seq<State>)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties

    requires IsValidTrace(t)

    ensures |states| == |t.ops| + 1
    ensures forall i :: 0 <= i <= |states| - 1
                ==> IsValidState(states[i]) && IsSecureState(states[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> IsSecureOps(states[i], states[i+1])
        // Properties from K_CalcNewState
    ensures forall i :: 0 <= i < |states| - 1
                ==> P_OpsFulfillPreConditions(states[i], t.ops[i])
    ensures forall i :: 0 <= i < |states| - 1
                ==> states[i+1] == K_CalcNewState(states[i], t.ops[i]).0
        // Property: <states> form a chain

    decreases |t.ops| 
{
    if(|t.ops| == 0) then
        [t.k0]
    else
        var k1 := K_CalcNewState(t.k0, t.ops[0]).0; // Eval t.ops[0]
        var step_states := K_CalcNewStates(Trace(k1, t.ops[1..]));
        var result_states := [t.k0] + step_states;
        assert IsValidState(k1) && IsSecureState(k1);
        assert P_OpsFulfillPreConditions(t.k0, t.ops[0]);

        Lemma_K_CalcNewStates_Private1(t.k0, step_states, result_states);
        Lemma_K_CalcNewStates_Private2(t.k0, step_states, result_states, t.ops[0], Trace(k1, t.ops[1..]), t);
        result_states
}




//******** Private Lemmas  ********//
lemma Lemma_K_CalcNewStates_Private1(state:State, step_states:seq<State>, result_states:seq<State>)
    requires forall i :: 0 <= i <= |step_states| - 1
                ==> IsValidState(step_states[i]) && IsSecureState(step_states[i])
    requires IsValidState(state) && IsSecureState(state)

    requires result_states == [state] + step_states

    ensures forall i :: 0 <= i <= |result_states| - 1
                ==> IsValidState(result_states[i]) && IsSecureState(result_states[i])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_K_CalcNewStates_Private2(state:State, step_states:seq<State>, result_states:seq<State>, op:Op, step_t:Trace, t:Trace)
    requires |t.ops| > 0
    requires |step_states| == |step_t.ops| + 1
    requires forall i :: 0 <= i < |step_states| - 1
                ==> P_OpsFulfillPreConditions(step_states[i], step_t.ops[i])
    requires P_OpsFulfillPreConditions(state, op);

    requires result_states == [state] + step_states
    requires t.ops == [op] + step_t.ops

    ensures forall i :: 0 <= i < |result_states| - 1
                ==> P_OpsFulfillPreConditions(result_states[i], t.ops[i])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ProveSP1_Reads(t:Trace)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties
    requires IsValidTrace(t)
            
    ensures forall i, states:seq<State> :: 0 <= i < |t.ops| && states == K_CalcNewStates(t)
                ==> (t.ops[i].DrvReadOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                    ) &&
                    (t.ops[i].DevReadOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
                    )
{
    var states := K_CalcNewStates(t);
    forall i | 0 <= i < |t.ops|
        ensures t.ops[i].DrvReadOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
        ensures t.ops[i].DevReadOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src)
    {
        var temp := K_CalcNewState(states[i], t.ops[i]);
        var k', d := temp.0, temp.1;

        if(t.ops[i].DrvReadOp? && d == true)
        {
            assert DrvRead_PreConditions(states[i], t.ops[i].drv_sid, t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src);
            assert DrvRead_PostConditions(states[i], t.ops[i].drv_sid, t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src, k', d);
            assert P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src);
        }
        else if (t.ops[i].DevReadOp? && d == true)
        {
            assert DevRead_PreConditions(states[i], t.ops[i].dev_sid, t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src);
            assert DevRead_PostConditions(states[i], t.ops[i].dev_sid, t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src, k', d);
            assert P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].read_objs, t.ops[i].tds_dst_src, t.ops[i].fds_dst_src, t.ops[i].dos_dst_src);
        }
    }
}

lemma Lemma_ProveSP1_Writes(t:Trace)
    requires IsValidState(t.k0) && IsSecureState(t.k0)
        // Requirement: The trace <t> starts from a secure state
    requires forall k:State, op:Op :: P_OpsProperties(k, op)
        // [Note] For any operations defined in this model, any k satisfies 
        // P_OpsProperties
    requires IsValidTrace(t)
            
    ensures forall i, states:seq<State> :: 0 <= i < |t.ops| && states == K_CalcNewStates(t)
                ==> (t.ops[i].DrvWriteOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                    ) &&
                    (t.ops[i].DevWriteOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
                    )
{
    var states := K_CalcNewStates(t);
    forall i | 0 <= i < |t.ops|
        ensures t.ops[i].DrvWriteOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
        ensures t.ops[i].DevWriteOp? && K_CalcNewState(states[i], t.ops[i]).1 == true
                        ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map)
    {
        var temp := K_CalcNewState(states[i], t.ops[i]);
        var k', d := temp.0, temp.1;

        if(t.ops[i].DrvWriteOp? && d == true)
        {
            assert DrvWrite_PreConditions(states[i], t.ops[i].drv_sid, t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map);
            assert DrvWrite_PostConditions(states[i], t.ops[i].drv_sid, t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map, k', d);
            assert P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].drv_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map);
        }
        else if (t.ops[i].DevWriteOp? && d == true)
        {
            assert DevWrite_PreConditions(states[i], t.ops[i].dev_sid, t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map);
            assert DevWrite_PostConditions(states[i], t.ops[i].dev_sid, t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map, k', d);
            assert P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(states[i], t.ops[i].dev_sid, 
                                t.ops[i].td_id_val_map, t.ops[i].fd_id_val_map, t.ops[i].do_id_val_map);
        }
    }
}