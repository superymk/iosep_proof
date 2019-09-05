include "Lemmas_DevHWProt.dfy" 

lemma Lemma_NewDMFromNewK_FulfillSI1(ws':DM_State, k':State)
    requires DM_IsValidState(ws')
    requires k' == DMStateToState(ws')
    requires IsValidState_Subjects(k') && IsValidState_Objects(k')
    requires IsValidState_ReachableTDsStates(k')

    requires IsSecureState_SI1(k')
    
    ensures DM_IsSecureState_SI1(ws')
{
    var k'_params := KToKParams(k');
    var k'_tds_state := ActiveTDsState_SlimState(k'.objects.tds);

    forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k'.objects.tds) &&
                    (k'_tds_state == tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, 
                                DM_DevsInRed(ws'), k'_tds_state, tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                DM_DevsInRed(ws'), k'_tds_state, tds_state2)))
        ensures (forall td_id2, dev_id ::
                            dev_id in DM_DevsInRed(ws') && 
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k'_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
                        ==> DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k'_params, tds_state2, td_id2, ws'.red_pid))
    {
        Lemma_K_AllReachableActiveTDsStates_Prove(k', tds_state2, DM_DevsInRed(ws'));
        assert tds_state2 in AllReachableActiveTDsStates(k');
        
        Lemma_K_AllActiveTDs_SlimState_Property(k');
        assert forall td_id2 :: td_id2 in AllActiveTDs_SlimState(k'.objects.tds)
                ==> td_id2.oid in AllObjsIDs(k'.objects) &&
                    ObjPID(k', td_id2.oid) != NULL;
        assert TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k'.objects.tds);
        Lemma_NewDMFromNewK_FulfillSI1_Private(k', tds_state2);
        assert forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> td_id2.oid in AllObjsIDs(k'.objects) &&
                    ObjPID(k', td_id2.oid) != NULL;
        forall td_id2, dev_id | dev_id in DM_DevsInRed(ws') &&
                                // The device (<dev_id>) is in red
                            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k'_params, tds_state2, dev_id, td_id2)
                                // The TD is read by the device
            ensures DevHWProt_DoActiveTDOnlyIncludeTransfersToObjInRed(k'_params, tds_state2, td_id2, ws'.red_pid)
        {
            assert !DoActiveTDIncludeTransfersToObjOutsidePartition(k'_params, tds_state2, td_id2);

            assert SubjPID(k', dev_id.sid) == ws'.red_pid;

            Lemma_K_ProveIsValidState_SubjsOwnObjsThenInSamePartition(k');
            assert ActiveTDsStateIsSecure(k'_params, DM_DevsInRed(ws'), tds_state2);
            Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(k', k'_params, 
                DM_DevsInRed(ws'), tds_state2, dev_id, td_id2);
            assert ObjPID(k', td_id2.oid) == ws'.red_pid;
        }
    }
}

lemma Lemma_NewDMFromNewK_FulfillSI3(ws':DM_State, k':State)
    requires k' == DMStateToState(ws')
    requires IsValidState(k') && IsSecureState_SI2(k')
    
    ensures (forall s_id :: s_id in DM_AllSubjsIDs(ws'.subjects) && DM_SubjPID(ws'.subjects, s_id) != NULL
                ==> DM_SubjPID(ws'.subjects, s_id) in ws'.pids) &&
            (forall o_id :: o_id in DM_AllObjsIDs(ws'.objects) && DM_ObjPID(ws'.objects, o_id) != NULL
                ==> DM_ObjPID(ws'.objects, o_id) in ws'.pids)
    ensures DM_IsSecureState_SI3(ws')
{
    // Dafny can automatically prove this lemma
}