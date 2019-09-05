include "Properties_DevHWProt.dfy"
include "Properties_SecureDMState.dfy"

// Lemma: P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(good_ws) ==> 
// P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)
lemma Lemma_DevHWProt_GoodDM_TDsReadByRedDevs_ThenDoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartitionIsFalse(
    good_ws:DM_State
)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(good_ws)

    ensures P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)
{
    var good_k := DMStateToState(good_ws);
    var good_k_params := KToKParams(good_k);
    var good_k_tds_state := ActiveTDsState_SlimState(good_k.objects.tds);

    Lemma_ValidK_FulFills_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(good_k);
    Lemma_ValidDMStateToState_DMDevsInRedAreActiveInK(good_ws, good_k);
    Lemma_P_DevHWProt_TDsReadByRedOnlyDevsHaveTransfersToRedObjsAtAnyTime_FulfillPreConditions(good_k);

    Lemma_K_ProveIsValidState_SubjsOwnObjsThenInSamePartition(good_k);

    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(good_k.objects.tds) &&
                    (good_k_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, tds_state2)))
                                    // Forall tds_state2, good_k_tds_state -->* tds_state2
        ensures ActiveTDsStateIsSecure(good_k_params, DM_DevsInRed(good_ws), tds_state2)
    {
        forall td_id2, dev_id | dev_id in DM_DevsInRed(good_ws) && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(good_k_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
            ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(good_k_params, tds_state2, td_id2)
        {
            Lemma_K_TDsInAllActiveTDsAreInState(good_k, tds_state2, td_id2);
            assert td_id2 in good_k.objects.tds;
            assert td_id2.oid in AllObjsIDs(good_k.objects);
            
            assert DM_SubjPID_DevID(good_ws.subjects, dev_id) == good_ws.red_pid;
            Lemma_DM_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(good_ws.subjects, dev_id);
            assert DM_SubjPID(good_ws.subjects, dev_id.sid) == good_ws.red_pid;
            assert SubjPID_DevID(good_k, dev_id) == good_ws.red_pid;

            // Prove <td_id2> is in red partition
            Lemma_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime_TDsReadByActiveDevAreInSamePartitionWithDev(
                good_k, good_k_params, DM_DevsInRed(good_ws), tds_state2, dev_id, td_id2, good_ws.red_pid);
            assert DM_ObjPID(good_ws.objects, td_id2.oid) == good_ws.red_pid;

            // Prove ObjPID_SlimState(k_params.objs_pids, td_id2.oid) == good_ws.red_pid
            assert ObjPID(good_k, td_id2.oid) == good_ws.red_pid;
            assert ObjPID_SlimState(good_k_params.objs_pids, td_id2.oid) == good_ws.red_pid;
            
            assert DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(good_k_params, tds_state2, td_id2, good_ws.red_pid);

            Lemma_DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed_ThenDoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartitionIsFalse(
                good_k_params, tds_state2, td_id2, good_ws.red_pid);
        }

        Lemma_K_ActiveTDsStateIsSecure_Prove(good_k_params, DM_DevsInRed(good_ws), tds_state2);
    }

    Lemma_P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Prove(good_ws, good_k, good_k_params, good_k_tds_state);
}

// Lemma: Green TDs are unmodified by red devices at any time
lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs(
    good_ws:DM_State, good_k:State, good_k_params:ReachableTDsKParams, good_k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>, devs:seq<Dev_ID>
)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)

    requires good_k == DMStateToState(good_ws)
    //requires P_DMStateToState_ValidDMState_Property(good_ws)
    requires good_k_params == KToKParams(good_k)
    requires good_k_tds_state == ActiveTDsState_SlimState(good_k.objects.tds)

    requires |devs| == |tds_states| - 1 
    requires forall dev_id :: dev_id in devs
                ==> dev_id in DM_DevsInRed(good_ws)
        // Requirement: Devices <devs> are red devices
    requires |tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(good_k)) &&
                |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in AllActiveDevs(good_k)) &&
                tds_states[0] == good_k_tds_state && // first TDs' state is the <good_k_tds_state>
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1])))
                    // good_k_tds_state -->1+ tds_states[|tds_states| - 1]
        // Requirement: good_k_tds_state -->* tds_states[|tds_states| - 1]

    ensures P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(good_k, tds_states, good_ws.red_pid)

    decreases |tds_states|
{
    var red_pid := good_ws.red_pid;

    if(|tds_states| == 2)
    {
        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_TwoElems(
            good_ws, good_k, good_k_params, good_k_tds_state,
            tds_states, devs);
    }
    else
    {
        assert |tds_states| > 2;

        var tds_states' := tds_states[..|tds_states|-1];
        var devs' := devs[..|devs|-1];

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_Recursion_ProvePreConditions(
            DM_DevsInRed(good_ws), AllActiveTDs(good_k), AllActiveDevs(good_k),
            good_k_params, good_k_tds_state, tds_states, devs, tds_states', devs');

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs(
            good_ws, good_k, good_k_params, good_k_tds_state,
            tds_states', devs');
        assert P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(good_k, tds_states', good_ws.red_pid);

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_MultiElems(
            good_ws, good_k, good_k_params, good_k_tds_state,
            tds_states, devs);

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_MultiElemsSummary(good_k, tds_states, red_pid);
        Lemma_DevHWProt_GreenTDsAreUnmodifiedByRedDevs_Prove(good_k, tds_states, red_pid);
    }
}

predicate P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(
    k:State, tds_states:seq<TDs_Vals>, red_pid:Partition_ID
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires |tds_states| > 0
    requires forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires red_pid != NULL
{
    assert forall tds_state2 :: tds_state2 in tds_states
        ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_states[0]);

    forall td_id, tds_state2 :: tds_state2 in tds_states &&
            td_id in TDsStateGetTDIDs(tds_state2) &&
            ObjPID(k, td_id.oid) != red_pid
                // For all green TDs
        ==> tds_state2[td_id] == tds_states[0][td_id]
                // Their values are unmodified
}




//******** Other Private Lemmas ********//
lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_SameTDsStateGetTDIDs_TwoElems(
    tds_states:seq<TDs_Vals>, s:set<TD_ID>
)
    requires |tds_states| == 2
    requires forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == s

    ensures TDsStateGetTDIDs(tds_states[0]) == TDsStateGetTDIDs(tds_states[1])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_TwoElemsSummary(
    k:State, tds_states:seq<TDs_Vals>, red_pid:Partition_ID
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires |tds_states| == 2
    requires forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires red_pid != NULL

    requires forall td_id :: td_id in tds_states[0] <==> td_id in tds_states[1]
    requires !(exists td_id :: td_id in TDsStateGetTDIDs(tds_states[0]) &&
                            ObjPID(k, td_id.oid) != red_pid &&
                            tds_states[1][td_id] != tds_states[0][td_id])

    ensures forall td_id, tds_state2 :: tds_state2 in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state2) &&
                    ObjPID(k, td_id.oid) != red_pid
                        // For all green TDs
                ==> tds_state2[td_id] == tds_states[0][td_id]
                        // Their values are unmodified
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_MultiElemsSummary(
    k:State, tds_states:seq<TDs_Vals>, red_pid:Partition_ID
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires |tds_states| > 2
    requires forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires red_pid != NULL

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_states[0])

    requires P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(k, tds_states[..|tds_states|-1], red_pid)
    requires forall td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2])
                ==> td_id in tds_states[|tds_states|-2] && td_id in tds_states[|tds_states|-1]
    requires !(exists td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2]) &&
                            ObjPID(k, td_id.oid) != red_pid &&
                            tds_states[|tds_states|-1][td_id] != tds_states[|tds_states|-2][td_id])

    ensures forall td_id, tds_state2 :: tds_state2 in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state2)
                ==> td_id.oid in AllObjsIDs(k.objects)
    ensures forall td_id, tds_state2 :: tds_state2 in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state2)
                ==> td_id in tds_states[0]
        // Properties needed by the following property
    ensures forall td_id, tds_state2 :: tds_state2 in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state2) &&
                    ObjPID(k, td_id.oid) != red_pid
                        // For all green TDs
                ==> tds_state2[td_id] == tds_states[0][td_id]
                        // Their values are unmodified
{
    Lemma_SequenceHighlightLastElem(tds_states);
    forall td_id, tds_state2 | tds_state2 in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state2) &&
                    ObjPID(k, td_id.oid) != red_pid
        ensures tds_state2[td_id] == tds_states[0][td_id]
    {
        if(tds_state2 in tds_states[..|tds_states|-1])
        {
            assert tds_state2[td_id] == tds_states[0][td_id];
        }
        else
        {
            assert tds_state2 == tds_states[|tds_states|-1];
            assert tds_state2[td_id] == tds_states[0][td_id];
        }
    }
}

lemma Lemma_DevHWProt_GreenTDsAreUnmodifiedByRedDevs_Prove(
    k:State, tds_states:seq<TDs_Vals>, red_pid:Partition_ID
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires |tds_states| > 0
    requires forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires red_pid != NULL

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_states[0])
    requires forall td_id, tds_state2 :: tds_state2 in tds_states &&
                    td_id in TDsStateGetTDIDs(tds_state2) &&
                    ObjPID(k, td_id.oid) != red_pid
                        // For all green TDs
                ==> tds_state2[td_id] == tds_states[0][td_id]
                        // Their values are unmodified

    ensures P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(k, tds_states, red_pid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_Conflict(
    k:State, tds_state:TDs_Vals, tdx_id:TD_ID, td_id:TD_ID, red_pid:Partition_ID
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
    requires tdx_id in AllActiveTDs(k)
    requires td_id in TDsStateGetTDIDs(tds_state)

    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(KToKParams(k), tds_state, tdx_id)
    requires ObjPID(k, tdx_id.oid) == red_pid

    requires ObjPID(k, td_id.oid) != red_pid
    requires td_id in tds_state[tdx_id].trans_params_tds &&
             W in tds_state[tdx_id].trans_params_tds[td_id].amodes

    ensures false
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_TwoElems_ActiveTDs(
    good_ws:DM_State, good_k:State, good_k_params:ReachableTDsKParams, good_k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>,
    from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)

    requires good_k == DMStateToState(good_ws)
    requires good_k_params == KToKParams(good_k)
    requires good_k_tds_state == ActiveTDsState_SlimState(good_k.objects.tds)

    requires |tds_states| == 2 &&  
             (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(good_k))

    requires from_tds_state == tds_states[0]
    requires to_tds_state == tds_states[1]

    ensures TDsStateGetTDIDs(from_tds_state) == good_k_params.all_active_tds
    ensures TDsStateGetTDIDs(to_tds_state) == good_k_params.all_active_tds 
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_TwoElems(
    good_ws:DM_State, good_k:State, good_k_params:ReachableTDsKParams, good_k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>, devs:seq<Dev_ID>
)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)

    requires good_k == DMStateToState(good_ws)
    requires good_k_params == KToKParams(good_k)
    requires good_k_tds_state == ActiveTDsState_SlimState(good_k.objects.tds)

    requires |devs| == |tds_states| - 1 
    requires forall dev_id :: dev_id in devs
                ==> dev_id in DM_DevsInRed(good_ws)
        // Requirement: Devices <devs> are red devices
    requires |tds_states| == 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(good_k)) &&
                |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in AllActiveDevs(good_k)) &&
                tds_states[0] == good_k_tds_state && // first TDs' state is the <good_k_tds_state>
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1])))
                    // good_k_tds_state -->1+ tds_states[|tds_states| - 1]
        // Requirement: good_k_tds_state -->* tds_states[|tds_states| - 1]

    ensures P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(good_k, tds_states, good_ws.red_pid)

    decreases |tds_states|
{
    var red_pid := good_ws.red_pid;

    var from_tds_state := tds_states[0];
    var to_tds_state := tds_states[1];
    var dev_id := devs[0];

    Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_TwoElems_ActiveTDs(
        good_ws, good_k, good_k_params, good_k_tds_state, tds_states, from_tds_state, to_tds_state);

    assert forall dev_id :: dev_id in DM_DevsInRed(good_ws)
            ==> SubjPID_DevID(good_k, dev_id) == red_pid;
    assert DM_DevsInRed(good_ws) <= AllActiveDevs(good_k);

    Lemma_K_TDsStateGetTDIDs_SameInSeq_LastTwoElems(tds_states, AllActiveTDs(good_k));

    if(exists td_id :: td_id in TDsStateGetTDIDs(from_tds_state) &&
                        ObjPID(good_k, td_id.oid) != red_pid &&
                        to_tds_state[td_id] != from_tds_state[td_id])
    {
        var td_id :| td_id in TDsStateGetTDIDs(from_tds_state) &&
                        ObjPID(good_k, td_id.oid) != red_pid &&
                        to_tds_state[td_id] != from_tds_state[td_id];

        Lemma_K_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(good_k);
        Lemma_K_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
            good_k_params, dev_id, from_tds_state, to_tds_state);
        assert P_ExistsTDXDevHasReadTransferToAndIncludeWriteTransferToTD(good_k_params, dev_id, from_tds_state, to_tds_state, td_id);
        var tdx_id :|
            (dev_id in AllActiveDevs(good_k) &&
                tdx_id in AllActiveTDs(good_k) &&
                CanActiveDevReadActiveTD_PreConditions(good_k_params, from_tds_state, dev_id, tdx_id) &&
                CanActiveDevReadActiveTD(good_k_params, from_tds_state, dev_id, tdx_id) &&
                td_id in from_tds_state[tdx_id].trans_params_tds &&
                W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                    // The TD references the target TD (<td_id2>) with W
                to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals);
                    // The TD specifies the new value to be written

        assert CanActiveDevReadActiveTD(good_k_params, from_tds_state, dev_id, tdx_id);

        // Prove tdx_id does not contain transfers to td_id, in from_tds_state
        Lemma_K_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(good_k);
        Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_IfExistsASequence_ThenReturnsTrue(
            good_k_params, DM_DevsInRed(good_ws), tds_states, devs);
        assert (good_k_tds_state == from_tds_state || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, from_tds_state) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, from_tds_state)));
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(good_k_params, from_tds_state, tdx_id);
        
        Lemma_K_SecureState_IfDevHasTransferToTD_ThenTheyAreInSamePartition(
            good_k, good_k_params, DM_DevsInRed(good_ws), from_tds_state, dev_id, tdx_id);
        assert ObjPID(good_k, tdx_id.oid) == red_pid;

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_Conflict(
            good_k, from_tds_state, tdx_id, td_id, red_pid);

        assert false;
    }

    Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_TwoElemsSummary(good_k, tds_states, red_pid);
    Lemma_DevHWProt_GreenTDsAreUnmodifiedByRedDevs_Prove(good_k, tds_states, red_pid);
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_MultiElems(
    good_ws:DM_State, good_k:State, good_k_params:ReachableTDsKParams, good_k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>, devs:seq<Dev_ID>
)
    requires DM_IsValidState_SubjsObjsPIDs(good_ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(good_ws)

    requires good_k == DMStateToState(good_ws)
    requires good_k_params == KToKParams(good_k)
    requires good_k_tds_state == ActiveTDsState_SlimState(good_k.objects.tds)

    requires |devs| == |tds_states| - 1 
    requires forall dev_id :: dev_id in devs
                ==> dev_id in DM_DevsInRed(good_ws)
        // Requirement: Devices <devs> are red devices
    requires |tds_states| > 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(good_k)) &&
                |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in AllActiveDevs(good_k)) &&
                tds_states[0] == good_k_tds_state && // first TDs' state is the <good_k_tds_state>
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1])))
                    // good_k_tds_state -->1+ tds_states[|tds_states| - 1]
        // Requirement: good_k_tds_state -->* tds_states[|tds_states| - 1]

    ensures forall td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2])
                ==> td_id.oid in AllObjsIDs(good_k.objects)
    ensures forall td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2])
                ==> td_id in tds_states[|tds_states|-1]
        // Properties needed by the following property
    ensures !(exists td_id :: td_id in TDsStateGetTDIDs(tds_states[|tds_states|-2]) &&
                        ObjPID(good_k, td_id.oid) != good_ws.red_pid &&
                        tds_states[|tds_states|-1][td_id] != tds_states[|tds_states|-2][td_id])

    decreases |tds_states|
{
    var red_pid := good_ws.red_pid;

    var from_tds_state := tds_states[|tds_states|-2];
    var to_tds_state := tds_states[|tds_states|-1];
    var dev_id := devs[|devs|-1];

    assert forall dev_id :: dev_id in DM_DevsInRed(good_ws)
            ==> SubjPID_DevID(good_k, dev_id) == red_pid;
    assert DM_DevsInRed(good_ws) <= AllActiveDevs(good_k);

    Lemma_K_TDsStateGetTDIDs_TDsAreInAllObjs(good_k, tds_states);
    assert forall td_id :: td_id in TDsStateGetTDIDs(from_tds_state)
                ==> td_id.oid in AllObjsIDs(good_k.objects);
    Lemma_K_TDsStateGetTDIDs_SameInSeq_LastTwoElems(tds_states, AllActiveTDs(good_k));

    assert AllActiveDevs(good_k) == AllActiveDevs_SlimState(good_k_params.subjects);
    assert AllActiveTDs(good_k) == good_k_params.all_active_tds;
    if(exists td_id :: td_id in TDsStateGetTDIDs(from_tds_state) &&
                        ObjPID(good_k, td_id.oid) != red_pid &&
                        to_tds_state[td_id] != from_tds_state[td_id])
    {
        var td_id :| td_id in TDsStateGetTDIDs(from_tds_state) &&
                        ObjPID(good_k, td_id.oid) != red_pid &&
                        to_tds_state[td_id] != from_tds_state[td_id];

        Lemma_K_IsActiveTDsStateReachActiveTDsStateInOneStep_TDModificationsAreFromTDs(
            good_k_params, dev_id, from_tds_state, to_tds_state);
        assert P_ExistsTDXDevHasReadTransferToAndIncludeWriteTransferToTD(good_k_params, dev_id, from_tds_state, to_tds_state, td_id);
        var tdx_id :|
            (dev_id in AllActiveDevs(good_k) &&
                tdx_id in AllActiveTDs(good_k) &&
                CanActiveDevReadActiveTD_PreConditions(good_k_params, from_tds_state, dev_id, tdx_id) &&
                CanActiveDevReadActiveTD(good_k_params, from_tds_state, dev_id, tdx_id) &&
                td_id in from_tds_state[tdx_id].trans_params_tds &&
                W in from_tds_state[tdx_id].trans_params_tds[td_id].amodes &&
                    // The TD references the target TD (<td_id2>) with W
                to_tds_state[td_id] in from_tds_state[tdx_id].trans_params_tds[td_id].vals);
                    // The TD specifies the new value to be written

        assert CanActiveDevReadActiveTD(good_k_params, from_tds_state, dev_id, tdx_id);

        // Prove tdx_id does not contain transfers to td_id, in from_tds_state
        Lemma_K_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(good_k);
        Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_IfExistsASequence_ThenReturnsTrue(
            good_k_params, DM_DevsInRed(good_ws), tds_states, devs);
        assert (good_k_tds_state == from_tds_state || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, from_tds_state) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(good_k_params, 
                                DM_DevsInRed(good_ws), good_k_tds_state, from_tds_state)));
        assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(good_k_params, from_tds_state, tdx_id);
        
        Lemma_K_SecureState_IfDevHasTransferToTD_ThenTheyAreInSamePartition(
            good_k, good_k_params, DM_DevsInRed(good_ws), from_tds_state, dev_id, tdx_id);
        assert ObjPID(good_k, tdx_id.oid) == red_pid;

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_Conflict(
            good_k, from_tds_state, tdx_id, td_id, red_pid);

        assert false;
    }
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_Recursion_ProvePreConditions(
    ws_reddevs:set<Dev_ID>, k_active_tds:set<TD_ID>, k_active_devs:set<Dev_ID>, 
    good_k_params:ReachableTDsKParams, good_k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>, devs:seq<Dev_ID>, tds_states':seq<TDs_Vals>, devs':seq<Dev_ID>
)
    requires |devs| == |tds_states| - 1 
    requires forall dev_id :: dev_id in devs
                ==> dev_id in ws_reddevs
        // Requirement: Devices <devs> are red devices
    requires |tds_states| > 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_active_tds) &&
                |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in k_active_devs) &&
                tds_states[0] == good_k_tds_state && // first TDs' state is the <good_k_tds_state>
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(good_k_params,
                            devs[i], tds_states[i], tds_states[i+1])))
                    // good_k_tds_state -->1+ tds_states[|tds_states| - 1]
        // Requirement: good_k_tds_state -->* tds_states[|tds_states| - 1]

    requires tds_states' == tds_states[..|tds_states|-1];
    requires devs' == devs[..|devs|-1];

    ensures |devs'| == |tds_states'| - 1 
    ensures forall dev_id :: dev_id in devs'
                ==> dev_id in ws_reddevs
        // Requirement: Devices <devs'> are red devices
    ensures |tds_states'| >= 2 && 
                (forall tds_state2 :: tds_state2 in tds_states' 
                    ==> TDsStateGetTDIDs(tds_state2) == k_active_tds) &&
                |devs'| == |tds_states'| - 1 && (forall dev_id2 :: dev_id2 in devs' ==> dev_id2 in k_active_devs) &&
                tds_states'[0] == good_k_tds_state && // first TDs' state is the <good_k_tds_state>
                (forall i :: 0<=i<|tds_states'| - 1 
                    ==> (IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(good_k_params,
                            devs'[i], tds_states'[i], tds_states'[i+1]) &&
                         IsActiveTDsStateReachActiveTDsStateInOneStep(good_k_params,
                            devs'[i], tds_states'[i], tds_states'[i+1])))
                    // good_k_tds_state -->1+ tds_states'[|tds_states'| - 1]
        // Requirement: good_k_tds_state -->* tds_states'[|tds_states'| - 1]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime_TDsReadByActiveDevAreInSamePartitionWithDev_Private(
    k:State, k_params:ReachableTDsKParams, active_devs:set<Dev_ID>,
    tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID, red_pid:Partition_ID
)
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
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds_state, dev_id, td_id)
    requires k_params == KToKParams(k)

    requires active_devs <= AllActiveDevs(k)

    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    requires (forall td_id2, dev_id ::
                            dev_id in active_devs && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_id2, red_pid))

    requires dev_id in active_devs
    requires td_id in TDsStateGetTDIDs(tds_state)
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)

    ensures DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_id, red_pid)
{
    // Dafny can automatically prove this lemma
}

// Lemma: In a state, if active TDs only ref objects in red partition, then red
// devices can only read TDs in red partition
// (needs 40s to verify)
lemma Lemma_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime_TDsReadByActiveDevAreInSamePartitionWithDev(
    k:State, k_params:ReachableTDsKParams, active_devs:set<Dev_ID>,
    tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID, red_pid:Partition_ID
)
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
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds_state, dev_id, td_id)
    requires k_params == KToKParams(k)

    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
                ==> o_id in AllObjsIDs(k.objects) &&
                    SubjPID(k, s_id) == ObjPID(k, o_id)
        // Requirement: k fulfills IsValidState_SubjsOwnObjsThenInSamePartition
    requires active_devs <= AllActiveDevs(k)
    requires dev_id in active_devs
    requires SubjPID_DevID(k, dev_id) == red_pid
    requires (forall td_id2, dev_id ::
                            dev_id in active_devs && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_id2, red_pid))
        // Requirement: <tds_state> is secure
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: Device (<dev_id>) can read the TD (<td_id>)

    ensures SubjPID_DevID(k, dev_id) == ObjPID(k, td_id.oid)
{
    var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]));
    
    assert DoOwnObj(k, dev_id.sid, td_ids[0].oid);
    assert SubjPID_DevID(k, dev_id) == ObjPID(k, td_ids[0].oid);

    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, tds_state, dev_id, td_ids, td_id);

    assert (forall td_id2, dev_id ::
                            dev_id in active_devs && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_id, red_pid));
    
    var i := 0;
    while (i < |td_ids| - 1)
        invariant i <= |td_ids| - 1

        invariant dev_id in active_devs
        invariant td_ids[i] in TDsStateGetTDIDs(tds_state)
        invariant CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_ids[i])

        invariant ObjPID(k, td_ids[i].oid) == red_pid
        invariant ObjPID(k, td_ids[0].oid) == ObjPID(k, td_ids[i].oid)
    {
        Lemma_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime_TDsReadByActiveDevAreInSamePartitionWithDev_Private(
            k, k_params, active_devs, tds_state, dev_id, td_ids[i], red_pid);
        assert DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_ids[i], red_pid);

        if(ObjPID(k, td_ids[i].oid) != ObjPID(k, td_ids[i+1].oid))
        {
            assert ObjPID(k, td_ids[i+1].oid) != red_pid;
            assert !DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k_params, tds_state, td_ids[i], red_pid);
        }
        assert ObjPID(k, td_ids[i].oid) == ObjPID(k, td_ids[i+1].oid);
        i := i + 1; 
    }
}