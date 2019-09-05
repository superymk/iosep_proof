include "../Abstract/Model.dfy"
include "Lemmas_Ops_Common.dfy"
include "Lemmas_Ops_SI1_Common.dfy"
include "Util_Lemmas.dfy"
include "Utils_DevsActivateCond.dfy"
include "Model_Ops_Predicates.dfy"

function method DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(
    ws:DM_State, k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
) : bool
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)
    
    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)
    
    requires tds_states_set == {ActiveTDsState(k)}
    
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas) 
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);
    
    (forall o_id, dev_id2 :: 
            (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) &&
            (dev_id2 in AllActiveDevs(k)) &&
            SubjPID(k, dev_id2.sid) == ObjPID(k, o_id)
        ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
}

function method DM_DevDeactivate_ChkNoOtherDevHasTransferToDevToBeDeactivated_IfTheDevIsInGreen(
    ws:DM_State, k:State, dev_sid:Subject_ID, k_cas:CAS, tds_states_set:set<TDs_Vals>
) : bool
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)
    
    requires Dev_ID(dev_sid) in DM_AllDevIDs(ws.subjects)
    
    requires tds_states_set == {ActiveTDsState(k)}
    
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas) 
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);
    
    (forall o_id, dev_id2 :: 
            (o_id in OwnObjIDs(k, dev_sid)) && 
            (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}) &&
            SubjPID(k, dev_id2.sid) == SubjPID(k, dev_sid)
        ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
}

lemma Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(
    k:State, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k) && IsSecureState(k)
    requires tds_states_set == {ActiveTDsState(k)}
    
    ensures forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' states includes all TDs
    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    ensures forall tds_state2 :: tds_state2 in tds_states_set
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)
                
    ensures TDsStateToCASForDev_PreConditions(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewDM_SubjObjDeactivate_FulfillSI2(
    ws:DM_State, k:State, ws':DM_State, k':State,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'.subjects)
                ==> dev_id in AllActiveDevs(k) 

    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires pid != NULL

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)
    requires pid != ws.red_pid ==> 
                DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                        todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)

    requires forall id :: id in todeactivate_td_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == pid
    requires forall id :: id in todeactivate_fd_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == pid
    requires forall id :: id in todeactivate_do_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == pid

    requires (forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))

    ensures (forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id))
{
    if(pid == ws.red_pid)
    {
        assert DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws);
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
    }
    else
    {
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2_DeactivateFromGreenPartition(ws, k, ws', k',
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
    }
}

lemma Lemma_NewDM_DevDeactivate_OtherDevsHaveUnchangedPIDs(
    ws:DM_State, ws':DM_State, wimpdev_id:Dev_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires wimpdev_id in ws.subjects.devs

    requires ws.subjects.devs[wimpdev_id].hcoded_td_id in ws.objects.tds
    requires forall id :: id in ws.subjects.devs[wimpdev_id].fd_ids ==> id in ws.objects.fds
    requires forall id :: id in ws.subjects.devs[wimpdev_id].do_ids ==> id in ws.objects.dos

    requires P_DMAndNewDM_SameObjectID(ws, ws')

    requires P_DevDeactivate_ModificationToState(DMStateToState(ws), wimpdev_id.sid, DMStateToState(ws'))

    ensures forall id :: id in ws.subjects.devs &&
                    id != wimpdev_id
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
{
    forall id | id in ws.subjects.devs && id != wimpdev_id
        ensures DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
    {
        assert ws'.subjects.devs[id] == ws.subjects.devs[id];
    }
}




//******** Common Lemmas ********//
lemma Lemma_DM_GreenDrvDeactivate_ObjectsToBeDeactivatedAreInSamePartitionWithDrv(
    ws:DM_State, drv_id:Drv_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires DM_IsValidState_Subjects(ws)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)

    requires drv_id in ws.subjects.drvs

    requires todeactivate_td_ids == ws.subjects.drvs[drv_id].td_ids
    requires todeactivate_fd_ids == ws.subjects.drvs[drv_id].fd_ids
    requires todeactivate_do_ids == ws.subjects.drvs[drv_id].do_ids

    ensures forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, drv_id.sid)
    ensures forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, drv_id.sid)
    ensures forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, drv_id.sid)
{
    var k := DMStateToState(ws);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    forall id | id in todeactivate_td_ids 
            ensures DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, drv_id.sid)
    {
        assert DM_DoOwnObj(ws.subjects, drv_id.sid, id.oid);
    }

    forall id | id in todeactivate_fd_ids 
            ensures DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, drv_id.sid)
    {
        assert DM_DoOwnObj(ws.subjects, drv_id.sid, id.oid);
    }

    forall id | id in todeactivate_do_ids 
            ensures DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, drv_id.sid)
    {
        assert DM_DoOwnObj(ws.subjects, drv_id.sid, id.oid);
    }
}

lemma Lemma_DM_ObjsDeactivate_ProveCheckOfObjDeactivateInK(
    ws:DM_State, k:State, green_pid:Partition_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
                
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: Objects to be deactivated are in a green partition
        
    requires tds_states_set == {ActiveTDsState(k)}
        
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas) 
    requires DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set)
        // Requirement: No active device in the same partition with the objects 
        // has transfers to these objects
        
    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)

    ensures forall id :: id in todeactivate_td_ids 
                ==> id in k.objects.tds
    ensures forall id :: id in todeactivate_fd_ids 
                ==> id in k.objects.fds
    ensures forall id :: id in todeactivate_do_ids 
                ==> id in k.objects.dos
    ensures todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    ensures todeactivate_fd_ids <= MapGetKeys(k.objects.fds)
    ensures todeactivate_do_ids <= MapGetKeys(k.objects.dos)
    ensures P_ObjsDeactivate_ReturnTrue_Def(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
{
    // Prove IsValidState(k)
    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove main property
    var k_params := KToKParams(k);

    assert k == DMStateToState(ws);
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);
    
    assert DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k);
            
    forall o_id, dev_id2 | o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                dev_id2 in AllActiveDevs(k)
        ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                    ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
    {
        assert ObjPID(k, o_id) == green_pid;
        
        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateCanAlwaysBeReachedWithDevsInRedOnly(
            ws, k, k_params);
            
        forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
            ensures DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            var k_tds_state := ActiveTDsState(k);
            
            if(SubjPID(k, dev_id2.sid) == green_pid)
            {
                assert forall td_id2 :: td_id2 in tds_state2 &&
                            td_id2 in DM_TDIDsInGreen(ws)
                        ==> tds_state2[td_id2] == k_tds_state[td_id2];
                        
                if(DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
                {
                    Lemma_InActiveTDsState_Dev2InGreenHasTransfersToObjInGreen_IfSoInReachableTDsState(
                        k, k_tds_state, tds_state2, dev_id2, o_id, green_pid);

                    // Show conflicts
                    assert DevAModesToObj(k, k_tds_state, dev_id2, o_id) != {};
                    Lemma_CASEntryIsNotEmpty_IfDevHasTransferToObjInActiveTDsState(
                        ws, k, dev_id2, o_id, k_cas, tds_states_set);
                    IfAModesContainROrWThenNotEmpty();
                    assert CASGetAModes(k_cas, dev_id2, o_id) != {};

                    assert DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k, 
                            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set);
                    assert CASGetAModes(k_cas, dev_id2, o_id) == {};

                    assert false;
                }
                        
                assert DevAModesToObj(k, tds_state2, dev_id2, o_id) == {};
            }
            else
            {
                assert SubjPID(k, dev_id2.sid) != green_pid;
                
                Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
                assert StatePropertiesCorollary1(k);
                
                if (DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
                {
                    // Show conflicts
                    assert SubjPID_DevID(k, dev_id2) == ObjPID(k, o_id);
                    assert ObjPID(k, o_id) != green_pid;
                    
                    assert false;
                }
                assert DevAModesToObj(k, tds_state2, dev_id2, o_id) == {};
            }
        }
    }
}

lemma Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_IfDevIsInRed(
    ws:DM_State, k:State, dev_sid:Subject_ID
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)

    requires Dev_ID(dev_sid) in DM_AllDevIDs(ws.subjects)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires dev_sid in DM_AllSubjsIDs(ws.subjects)

    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid
        // Requirement: The device is in red
    requires P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, Dev_ID(dev_sid))
        // Requirement: No other red device has transfers to any objects of the 
        // device to be deactivated

    ensures IsValidState(k)
    ensures P_DevDeactivate_ReturnTrue_Def(k, dev_sid)
{
    // Prove IsValidState(k)
    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove main property
    var dev_id := Dev_ID(dev_sid);
    var k_params := KToKParams(k);

    assert k == DMStateToState(ws);
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    forall o_id, dev_id2 | o_id in OwnObjIDs(k, dev_sid) && 
                dev_id2 in AllActiveDevs(k) - {dev_id}
        ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                    ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
    {
        Lemma_OwnObjIDs_Property(k, dev_sid);
        assert DoOwnObj(k, dev_sid, o_id);
        Lemma_ObjsInSubjsAreAlsoInState(k);
        assert o_id in AllObjsIDs(k.objects);
        
        Lemma_K_SubjAndItsObjHasSamePID(k, dev_sid, o_id, ws.red_pid);
        assert ObjPID(k, o_id) == ws.red_pid;
        
        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateCanAlwaysBeReachedWithDevsInRedOnly(
            ws, k, k_params);
                
        forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
            ensures DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            var k_tds_state := ActiveTDsState(k);

            Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_TDsStateCanBeReachedWithDevsInRed(
                ws, k, k_params, tds_state2, k_tds_state);
            assert (k_tds_state == tds_state2 ||
                    (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2)));

            assert DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid;
            
            assert DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k);
            if(dev_id2 in DM_DevsInRed(ws))
            {
                assert dev_id2 in DM_DevsInRed(ws) - {dev_id};
                assert P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, dev_id);
                assert DevAModesToObj(k, tds_state2, dev_id2, o_id) == {};
            }
            else
            {
                assert dev_id2 in DM_DevsInGreen(ws);
                
                Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
                assert StatePropertiesCorollary1(k);
                
                if (DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
                {
                    // Show conflicts
                    assert SubjPID_DevID(k, dev_id2) == ObjPID(k, o_id);
                    assert ObjPID(k, o_id) != ws.red_pid;
                    
                    assert false;
                }
                assert DevAModesToObj(k, tds_state2, dev_id2, o_id) == {};
            }
        }
    }
}

lemma Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_IfDevIsInGreen(
    ws:DM_State, k:State, dev_sid:Subject_ID, k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)

    requires Dev_ID(dev_sid) in DM_AllDevIDs(ws.subjects)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires dev_sid in DM_AllSubjsIDs(ws.subjects)

    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
    requires DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
        // Requirement: The device is in green
        
    requires tds_states_set == {ActiveTDsState(k)}
        
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas) 
    requires DM_DevDeactivate_ChkNoOtherDevHasTransferToDevToBeDeactivated_IfTheDevIsInGreen(ws, k, dev_sid, k_cas, tds_states_set)
        // Requirement: No other active device has transfers to any objects of the 
        // device to be deactivated
        
    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)

    ensures P_DevDeactivate_ReturnTrue_Def(k, dev_sid)
{
    // Prove IsValidState(k)
    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    // Prove main property
    var dev_id := Dev_ID(dev_sid);
    var k_params := KToKParams(k);

    assert k == DMStateToState(ws);
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);
    
    assert DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k);
            
    forall o_id, dev_id2 | o_id in OwnObjIDs(k, dev_sid) && 
                dev_id2 in AllActiveDevs(k) - {dev_id}
        ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                    ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
    {
        var pid := SubjPID(k, dev_id.sid);
        
        Lemma_OwnObjIDs_Property(k, dev_sid);
        assert DoOwnObj(k, dev_sid, o_id);
        Lemma_ObjsInSubjsAreAlsoInState(k);
        assert o_id in AllObjsIDs(k.objects);
        
        Lemma_K_SubjAndItsObjHasSamePID(k, dev_sid, o_id, pid);
        assert ObjPID(k, o_id) == pid;
        
        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateCanAlwaysBeReachedWithDevsInRedOnly(
            ws, k, k_params);
            
        forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
            ensures DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            var k_tds_state := ActiveTDsState(k);
            
            if(SubjPID(k, dev_id2.sid) == pid)
            {
                assert forall td_id2 :: td_id2 in tds_state2 &&
                            td_id2 in DM_TDIDsInGreen(ws)
                        ==> tds_state2[td_id2] == k_tds_state[td_id2];
                        
                if(DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
                {
                    Lemma_InActiveTDsState_Dev2InGreenHasTransfersToObjInGreen_IfSoInReachableTDsState(
                        k, k_tds_state, tds_state2, dev_id2, o_id, pid);

                    // Show conflicts
                    assert DevAModesToObj(k, k_tds_state, dev_id2, o_id) != {};
                    Lemma_CASEntryIsNotEmpty_IfDevHasTransferToObjInActiveTDsState(
                        ws, k, dev_id2, o_id, k_cas, tds_states_set);
                    IfAModesContainROrWThenNotEmpty();
                    assert CASGetAModes(k_cas, dev_id2, o_id) != {};

                    assert DM_DevDeactivate_ChkNoOtherDevHasTransferToDevToBeDeactivated_IfTheDevIsInGreen(ws, k, dev_sid, k_cas, tds_states_set);
                    assert CASGetAModes(k_cas, dev_id2, o_id) == {};

                    assert false;
                }
                        
                assert DevAModesToObj(k, tds_state2, dev_id2, o_id) == {};
            }
            else
            {
                assert SubjPID(k, dev_id2.sid) != pid;
                
                Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
                assert StatePropertiesCorollary1(k);
                
                if (DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
                {
                    // Show conflicts
                    assert SubjPID_DevID(k, dev_id2) == ObjPID(k, o_id);
                    assert ObjPID(k, o_id) != pid;
                    
                    assert false;
                }
                assert DevAModesToObj(k, tds_state2, dev_id2, o_id) == {};
            }
        }
    }
}

lemma Lemma_K_SubjObjDeactivate_ActiveDevsInNewKIsSubsetOfOnesInK(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Subjects(k')

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)

    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k'.subjects)
                ==> dev_id in AllActiveDevs(k) 
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ActiveDevsInNewKIsSubsetOfOnesInK(
    k:State, k':State, dev_id:Dev_ID, dev_state:Dev_State
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Subjects(k')

    requires dev_id in k.subjects.devs
    requires dev_state == k.subjects.devs[dev_id]
    requires k'.subjects.devs == k.subjects.devs[dev_id := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids)]

    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k'.subjects)
                ==> dev_id in AllActiveDevs(k) 
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs(
    ws:DM_State, k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, green_pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)
    
    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)
    
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in {ActiveTDsState(k)}
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, {ActiveTDsState(k)}, k_cas) 

    requires green_pid != NULL
    requires green_pid != ws.red_pid

    requires forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid

    requires forall dev_id :: dev_id in AllActiveDevs(k)
                ==> k.subjects.devs[dev_id].hcoded_td_id !in todeactivate_td_ids
    requires ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k)) 

    requires DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid)

    ensures DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k,
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, {ActiveTDsState(k)})
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    var k_tds_state := ActiveTDsState(k);
    var k_params := KToKParams(k);
    forall o_id, dev_id2 | 
            (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) &&
            (dev_id2 in AllActiveDevs(k)) &&
            SubjPID(k, dev_id2.sid) == ObjPID(k, o_id)
        ensures IsInCAS(k_cas, dev_id2, o_id) 
        ensures CASGetAModes(k_cas, dev_id2, o_id) == {}
    {
        assert IsInCAS(k_cas, dev_id2, o_id);
        var amodes := CASGetAModes(k_cas, dev_id2, o_id);

        // Prove SubjPID(k, dev_id2.sid) == green_pid
        Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs_OIDInGreenPartition(
            ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid, o_id);
        assert SubjPID(k, dev_id2.sid) == green_pid;

        AllReqNonEmptyAModesMustContainROrW();
        if(R in amodes)
        {
            assert R in DevAModesToObj(k, k_tds_state, dev_id2, o_id);
            assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id2, o_id);
            var td_id :| td_id in k_tds_state &&        // Exist an active TD (<td_id>)
                        CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id) &&
                                            // The device (<dev_id2>) can read the (active) TD
                        o_id in GetObjIDsRefedInTD(k_tds_state, td_id) &&
                        R in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
                                            // The TD refs the object (<o_id>) with R access mode

            var td_ids := Lemma_DM_CanActiveDevReadActiveTD_Apply(k_params, k_tds_state, dev_id2, td_id);
            Lemma_K_SecureActiveTDsState_IfDevHasReadTransferToTD_ThenAllIntermediateTDsAreInSamePartitionWithDev(k, k_params, k_tds_state, dev_id2, td_ids, td_id);

            // Prove GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) != {}
            assert R in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
            IfAModesContainROrWThenNotEmpty();

            Lemma_DM_ObjDeactivate_IfDevHasReadTransfersToTD_ThenTDHasNoTransfersToObjsToBeDeactivated(ws, k, k_tds_state, dev_id2,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                green_pid, td_ids, td_id, o_id);
        }

        if(W in amodes)
        {
            assert W in DevAModesToObj(k, k_tds_state, dev_id2, o_id);
            assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, k_tds_state, dev_id2, o_id);
            var td_id :| td_id in k_tds_state &&        // Exist an active TD (<td_id>)
                        CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id) &&
                                            // The device (<dev_id2>) can read the (active) TD
                        o_id in GetObjIDsRefedInTD(k_tds_state, td_id) &&
                        W in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
                                            // The TD refs the object (<o_id>) with R access mode

            var td_ids := Lemma_DM_CanActiveDevReadActiveTD_Apply(k_params, k_tds_state, dev_id2, td_id);
            Lemma_K_SecureActiveTDsState_IfDevHasReadTransferToTD_ThenAllIntermediateTDsAreInSamePartitionWithDev(k, k_params, k_tds_state, dev_id2, td_ids, td_id);

            // Prove GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) != {}
            assert W in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
            IfAModesContainROrWThenNotEmpty();

            Lemma_DM_ObjDeactivate_IfDevHasReadTransfersToTD_ThenTDHasNoTransfersToObjsToBeDeactivated(ws, k, k_tds_state, dev_id2,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                green_pid, td_ids, td_id, o_id);
        }
        assert amodes == {};
    }
}




//******** Lemma of GreenDrvDeactivate ********//
lemma Lemma_GreenDrvDeactivate_HCodedTDsAreNotBeingDeactivated(k:State, drv_id:Drv_ID)
    requires IsValidState(k)
    requires drv_id in k.subjects.drvs

    ensures forall dev_id :: dev_id in AllActiveDevs(k)
                ==> k.subjects.devs[dev_id].hcoded_td_id !in k.subjects.drvs[drv_id].td_ids
{
    Lemma_DM_SameIDsIffSameInternalIDs();
    forall dev_id | dev_id in AllActiveDevs(k)
        ensures k.subjects.devs[dev_id].hcoded_td_id !in k.subjects.drvs[drv_id].td_ids
    {
        if(k.subjects.devs[dev_id].hcoded_td_id in k.subjects.drvs[drv_id].td_ids)
        {
            var td_id := k.subjects.devs[dev_id].hcoded_td_id;
            assert DoOwnObj(k, dev_id.sid, td_id.oid);
            assert DoOwnObj(k, drv_id.sid, td_id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2);
        }
    }
}




//******** Lemmas Of DevDeactivate ********//
lemma Lemma_NewDM_IsValidState_DevDeactivate_DevsActivateCond(
    ws:DM_State, ws':DM_State, toactivate_wimpdev_id:Dev_ID
)
    requires DM_IsValidState_DevsActivateCond(ws)

    requires ws'.devs_activatecond == ws.devs_activatecond
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires ws.red_pid != NULL
    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)

    requires toactivate_wimpdev_id in ws.subjects.devs
        // Requirement: <ws.subjects.devs> in <devs>

    requires forall id :: id in ws.subjects.devs &&
                    id != toactivate_wimpdev_id
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
    requires DM_SubjPID(ws'.subjects, toactivate_wimpdev_id.sid) == NULL

    ensures DM_IsValidState_DevsActivateCond(ws')
{
    forall wimpdev_id | wimpdev_id in ws'.devs_activatecond
        ensures DM_SubjPID(ws'.subjects, wimpdev_id.sid) == NULL ||  DM_SubjPID(ws'.subjects, wimpdev_id.sid) == ws'.red_pid
    {
        if(wimpdev_id != toactivate_wimpdev_id)
        {
            assert DM_SubjPID(ws'.subjects, wimpdev_id.sid) == DM_SubjPID(ws.subjects, wimpdev_id.sid);
            assert DM_SubjPID(ws'.subjects, wimpdev_id.sid) == NULL ||  DM_SubjPID(ws'.subjects, wimpdev_id.sid) == ws'.red_pid;
        }
        else
        {
            assert wimpdev_id == toactivate_wimpdev_id;

            assert DM_SubjPID(ws'.subjects, wimpdev_id.sid) == NULL;
        }
    }

    forall wimpdev_id, wimpdev_id2 | wimpdev_id in ws'.devs_activatecond &&
                    wimpdev_id2 in ws'.devs_activatecond[wimpdev_id]
        ensures DM_SubjPID(ws'.subjects, wimpdev_id2.sid) != ws'.red_pid
    {
        if(wimpdev_id2 != toactivate_wimpdev_id)
        {
            assert DM_SubjPID(ws'.subjects, wimpdev_id2.sid) == DM_SubjPID(ws.subjects, wimpdev_id2.sid);
            assert DM_SubjPID(ws'.subjects, wimpdev_id2.sid) != ws'.red_pid;
        }
        else
        {
            assert wimpdev_id2 == toactivate_wimpdev_id;

            assert DM_SubjPID(ws'.subjects, wimpdev_id2.sid) == NULL;
        }
    }

    forall wimpdev_id | wimpdev_id in ws'.devs_activatecond &&
                    DM_SubjPID(ws'.subjects, wimpdev_id.sid) != NULL
        ensures (forall wimpdev_id2 :: wimpdev_id2 in ws'.devs_activatecond[wimpdev_id]
                        ==> DM_SubjPID(ws'.subjects, wimpdev_id2.sid) == NULL)
    {
        // Dafny can automatically prove this lemma
    }

    Lemma_NewDM_IsValidState_DevsActivateCond(ws, ws');
}

lemma Lemma_DM_DevDeactivate_PropertiesOfObjsToBeDeactivated(
    ws:DM_State, dev_id:Dev_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires DM_IsValidState_Subjects(ws)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)

    requires dev_id in ws.subjects.devs

    requires todeactivate_td_ids == ws.subjects.devs[dev_id].td_ids
    requires todeactivate_fd_ids == ws.subjects.devs[dev_id].fd_ids
    requires todeactivate_do_ids == ws.subjects.devs[dev_id].do_ids

    ensures forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    ensures forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    ensures forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)
    ensures forall id :: id in todeactivate_td_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, dev_id.sid)
    ensures forall id :: id in todeactivate_fd_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, dev_id.sid)
    ensures forall id :: id in todeactivate_do_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, dev_id.sid)
{
    var k := DMStateToState(ws);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    forall id | id in todeactivate_td_ids
            ensures id.oid in DM_AllObjsIDs(ws.objects)
            ensures DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, dev_id.sid)
    {
        assert DM_DoOwnObj(ws.subjects, dev_id.sid, id.oid);
    }

    forall id | id in todeactivate_fd_ids
            ensures id.oid in DM_AllObjsIDs(ws.objects)
            ensures DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, dev_id.sid)
    {
        assert DM_DoOwnObj(ws.subjects, dev_id.sid, id.oid);
    }

    forall id | id in todeactivate_do_ids
            ensures id.oid in DM_AllObjsIDs(ws.objects)
            ensures DM_ObjPID(ws.objects, id.oid) == DM_SubjPID(ws.subjects, dev_id.sid)
    {
        assert DM_DoOwnObj(ws.subjects, dev_id.sid, id.oid);
    }
}

lemma Lemma_DM_DevDeactivate_ObjsToBeDeactivatedAreInDev(
    ws:DM_State, k:State, deactivate_dev_id:Dev_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)

    requires deactivate_dev_id in DM_AllDevIDs(ws.subjects)
    requires SubjPID(k, deactivate_dev_id.sid) == green_pid

    requires todeactivate_td_ids == ws.subjects.devs[deactivate_dev_id].td_ids
    requires todeactivate_fd_ids == ws.subjects.devs[deactivate_dev_id].fd_ids
    requires todeactivate_do_ids == ws.subjects.devs[deactivate_dev_id].do_ids

    ensures forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    ensures forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    ensures forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    ensures forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    ensures forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    ensures forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid

    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures OwnObjIDs(k, deactivate_dev_id.sid) == TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)
{
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
    forall id | id in todeactivate_td_ids
        ensures DM_ObjPID(ws.objects, id.oid) == green_pid
    {
        assert DoOwnObj(k, deactivate_dev_id.sid, id.oid);
    }
    
    forall id | id in todeactivate_fd_ids
        ensures DM_ObjPID(ws.objects, id.oid) == green_pid
    {
        assert DoOwnObj(k, deactivate_dev_id.sid, id.oid);
    }
    
    forall id | id in todeactivate_do_ids
        ensures DM_ObjPID(ws.objects, id.oid) == green_pid
    {
        assert DoOwnObj(k, deactivate_dev_id.sid, id.oid);
    }
}

// (needs 40s to verify)
lemma Lemma_DM_DevDeactivate_NoOtherGreenTDsRefObjsOfDevToBeDeactivated_ThenNoOtherDevHasTransferToDev(
    ws:DM_State, k:State, deactivate_dev_id:Dev_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, green_pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)
    
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in {ActiveTDsState(k)}
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, {ActiveTDsState(k)}, k_cas) 

    requires green_pid != NULL
    requires green_pid != ws.red_pid

    requires deactivate_dev_id in DM_AllDevIDs(ws.subjects)
    requires SubjPID(k, deactivate_dev_id.sid) == green_pid

    requires todeactivate_td_ids == ws.subjects.devs[deactivate_dev_id].td_ids
    requires todeactivate_fd_ids == ws.subjects.devs[deactivate_dev_id].fd_ids
    requires todeactivate_do_ids == ws.subjects.devs[deactivate_dev_id].do_ids

    requires forall dev_id :: dev_id in AllActiveDevs(k) - {deactivate_dev_id}
                ==> k.subjects.devs[dev_id].hcoded_td_id !in todeactivate_td_ids
    requires ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), ActiveTDsState(k)) 

    requires DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid)

    ensures DM_DevDeactivate_ChkNoOtherDevHasTransferToDevToBeDeactivated_IfTheDevIsInGreen(ws, k,
                deactivate_dev_id.sid, k_cas, {ActiveTDsState(k)})
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    var k_tds_state := ActiveTDsState(k);
    var k_params := KToKParams(k);

    Lemma_DM_DevDeactivate_ObjsToBeDeactivatedAreInDev(ws, k, deactivate_dev_id,
        todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid);
    forall o_id, dev_id2 | 
            (o_id in OwnObjIDs(k, deactivate_dev_id.sid)) && 
            (dev_id2 in AllActiveDevs(k) - {deactivate_dev_id}) &&
            SubjPID(k, dev_id2.sid) == SubjPID(k, deactivate_dev_id.sid)
        ensures IsInCAS(k_cas, dev_id2, o_id) 
        ensures CASGetAModes(k_cas, dev_id2, o_id) == {}
    {
        assert o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids);
        assert IsInCAS(k_cas, dev_id2, o_id);
        var amodes := CASGetAModes(k_cas, dev_id2, o_id);

        // Prove SubjPID(k, dev_id2.sid) == green_pid
        assert SubjPID(k, dev_id2.sid) == green_pid;

        AllReqNonEmptyAModesMustContainROrW();
        if(R in amodes)
        {
            assert R in DevAModesToObj(k, k_tds_state, dev_id2, o_id);
            assert DevAModesToObjFromTDs_ExistR_SlimState(k_params, k_tds_state, dev_id2, o_id);
            var td_id :| td_id in k_tds_state &&        // Exist an active TD (<td_id>)
                        CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id) &&
                                            // The device (<dev_id2>) can read the (active) TD
                        o_id in GetObjIDsRefedInTD(k_tds_state, td_id) &&
                        R in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
                                            // The TD refs the object (<o_id>) with R access mode

            var td_ids := Lemma_DM_CanActiveDevReadActiveTD_Apply(k_params, k_tds_state, dev_id2, td_id);
            Lemma_K_SecureActiveTDsState_IfDevHasReadTransferToTD_ThenAllIntermediateTDsAreInSamePartitionWithDev(k, k_params, k_tds_state, dev_id2, td_ids, td_id);

            // Prove GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) != {}
            assert R in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
            IfAModesContainROrWThenNotEmpty();

            Lemma_DM_ObjDeactivate_IfDevHasReadTransfersToTD_ThenTDHasNoTransfersToObjsToBeDeactivated(ws, k, k_tds_state, dev_id2,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                green_pid, td_ids, td_id, o_id);
        }

        if(W in amodes)
        {
            assert W in DevAModesToObj(k, k_tds_state, dev_id2, o_id);
            assert DevAModesToObjFromTDs_ExistW_SlimState(k_params, k_tds_state, dev_id2, o_id);
            var td_id :| td_id in k_tds_state &&        // Exist an active TD (<td_id>)
                        CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id) &&
                                            // The device (<dev_id2>) can read the (active) TD
                        o_id in GetObjIDsRefedInTD(k_tds_state, td_id) &&
                        W in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
                                            // The TD refs the object (<o_id>) with R access mode

            var td_ids := Lemma_DM_CanActiveDevReadActiveTD_Apply(k_params, k_tds_state, dev_id2, td_id);
            Lemma_K_SecureActiveTDsState_IfDevHasReadTransferToTD_ThenAllIntermediateTDsAreInSamePartitionWithDev(k, k_params, k_tds_state, dev_id2, td_ids, td_id);

            // Prove GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) != {}
            assert W in GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id);
            IfAModesContainROrWThenNotEmpty();

            Lemma_DM_ObjDeactivate_IfDevHasReadTransfersToTD_ThenTDHasNoTransfersToObjsToBeDeactivated(ws, k, k_tds_state, dev_id2,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                green_pid, td_ids, td_id, o_id);
        }
        assert amodes == {};
    }
}

lemma Lemma_DevDeactivate_HCodedTDsOfOtherDevsAreNotBeingDeactivated(k:State, deactivate_dev_id:Dev_ID)
    requires IsValidState(k)
    requires deactivate_dev_id in k.subjects.devs

    ensures forall dev_id :: dev_id in AllActiveDevs(k) - {deactivate_dev_id}
                ==> k.subjects.devs[dev_id].hcoded_td_id !in k.subjects.devs[deactivate_dev_id].td_ids
{
    Lemma_DM_SameIDsIffSameInternalIDs();
    forall dev_id | dev_id in AllActiveDevs(k) - {deactivate_dev_id}
        ensures k.subjects.devs[dev_id].hcoded_td_id !in k.subjects.devs[deactivate_dev_id].td_ids
    {
        if(k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[deactivate_dev_id].td_ids)
        {
            var td_id := k.subjects.devs[dev_id].hcoded_td_id;
            assert DoOwnObj(k, dev_id.sid, td_id.oid);
            assert DoOwnObj(k, deactivate_dev_id.sid, td_id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2);
        }
    }
}




//******** Lemma of ExternalWimpObjsDeactivate ********//
lemma Lemma_DM_ExternalWimpObjsDeactivate_ProveCheckOfObjDeactivateInK(
    ws:DM_State, k:State, green_pid:Partition_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
                
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: Objects to be deactivated are in a green partition
        
    requires tds_states_set == {ActiveTDsState(k)}
        
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas) 
    requires DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set)
        // Requirement: No active device in the same partition with the objects 
        // has transfers to these objects
        
    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)

    ensures todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    ensures todeactivate_fd_ids <= MapGetKeys(k.objects.fds)
    ensures todeactivate_do_ids <= MapGetKeys(k.objects.dos)
        // Properties needed by the following property
    ensures P_ExternalObjsDeactivate_ReturnTrue_Def(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid)
{
    Lemma_DM_ObjsDeactivate_ProveCheckOfObjDeactivateInK(ws, k, green_pid,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set);

    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    
    assert forall id :: id in todeactivate_td_ids ==> id in MapGetKeys(k.objects.tds);
    assert forall id :: id in todeactivate_fd_ids ==> id in MapGetKeys(k.objects.fds);
    assert forall id :: id in todeactivate_do_ids ==> id in MapGetKeys(k.objects.dos);
    
    Lemma_SetInclusion_Prove(todeactivate_td_ids, MapGetKeys(k.objects.tds));
    Lemma_SetInclusion_Prove(todeactivate_fd_ids, MapGetKeys(k.objects.fds));
    Lemma_SetInclusion_Prove(todeactivate_do_ids, MapGetKeys(k.objects.dos));
    
    // Prove the main property
    forall id | id in todeactivate_fd_ids
        ensures ObjPID(k, id.oid) == green_pid
    {
        assert ObjPID(k, id.oid) == DM_ObjPID(ws.objects, id.oid);
    }
    
    forall id | id in todeactivate_do_ids
        ensures ObjPID(k, id.oid) == green_pid
    {
        assert ObjPID(k, id.oid) == DM_ObjPID(ws.objects, id.oid);
    }
}

lemma Lemma_ExternalObjsDeactivate_HCodedTDsAreNotBeingDeactivated(
    ws:DM_State, k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    requires k == DMStateToState(ws)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)

    ensures forall dev_id :: dev_id in AllActiveDevs(k)
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_ids
{
    Lemma_DM_SameIDsIffSameInternalIDs();
    Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
    forall dev_id | dev_id in AllActiveDevs(k)
        ensures k.subjects.devs[dev_id].hcoded_td_id !in td_ids
    {
        if(k.subjects.devs[dev_id].hcoded_td_id in td_ids)
        {
            var td_id := k.subjects.devs[dev_id].hcoded_td_id;
            assert DoOwnObj(k, dev_id.sid, td_id.oid);
        }
    }
}




//******** Private Lemmas ********//
lemma Lemma_CASEntryIsNotEmpty_IfDevHasTransferToObjInActiveTDsState(
    ws:DM_State, k:State, dev_id2:Dev_ID, o_id:Object_ID, k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)
        
    requires tds_states_set == {ActiveTDsState(k)}
        
    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas) 
    
    requires dev_id2 in k.subjects.devs
    requires SubjPID(k, dev_id2.sid) != NULL
    
    requires o_id in AllObjsIDs(k.objects)
    requires ObjPID(k, o_id) != NULL
    
    requires DevAModesToObj(k, ActiveTDsState(k), dev_id2, o_id) != {}
    
    requires IsInCAS(k_cas, dev_id2, o_id)
    
    ensures CASGetAModes(k_cas, dev_id2, o_id) != {}
{
    AllReqNonEmptyAModesMustContainROrW();
    
    assert dev_id2 in AllActiveDevs(k);
    
    Lemma_K_AllActiveObjs_Prove(k, o_id);
    assert o_id in AllActiveObjs(k);
        
    if(R in DevAModesToObj(k, ActiveTDsState(k), dev_id2, o_id))
    {
        assert P_BuildCAS_Properties(k, tds_states_set, k_cas);
        
        assert R in CASGetAModes(k_cas, dev_id2, o_id);
    }
    else
    {
        assert W in DevAModesToObj(k, ActiveTDsState(k), dev_id2, o_id);
        assert P_BuildCAS_Properties(k, tds_states_set, k_cas);
        assert W in CASGetAModes(k_cas, dev_id2, o_id);
    }
    
    assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in CASGetAModes(k_cas, dev_id2, o_id);
    IfAModesContainROrWThenNotEmpty();
}

lemma Lemma_CanActiveDevReadActiveTD_IfRelatedTDsValsAreUnmodified(
    k_params:ReachableTDsKParams, tds_state1:TDs_Vals, tds_state2:TDs_Vals, td_ids:seq<TD_ID>,
    dev_id:Dev_ID, td_id:TD_ID
)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds_state1, dev_id, td_id)
    
    requires |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state1) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                    // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state1[td_ids[i]]))
    requires TDsStateGetTDIDs(tds_state1) == TDsStateGetTDIDs(tds_state2)
    requires forall td_id2 :: td_id2 in td_ids
            ==> tds_state1[td_id2] == tds_state2[td_id2]
            
            
    ensures CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_InActiveTDsState_Dev2InGreenHasTransfersToObjInGreen_IfSoInReachableTDsState(
    k:State, k_tds_state:TDs_Vals, tds_state2:TDs_Vals, dev_id2:Dev_ID, o_id:Object_ID, green_pid:Partition_ID
)
    requires IsValidState(k)
    
    requires green_pid != NULL
    
    requires dev_id2 in k.subjects.devs
    requires SubjPID(k, dev_id2.sid) == green_pid
    
    requires o_id in AllObjsIDs(k.objects)
    requires ObjPID(k, o_id) == green_pid
    
    requires tds_state2 in AllReachableActiveTDsStates(k)
    requires k_tds_state == ActiveTDsState(k)
    requires forall td_id2 :: td_id2 in tds_state2 &&
                    ObjPID(k, td_id2.oid) == green_pid
                ==> tds_state2[td_id2] == k_tds_state[td_id2]
        // Requirement: TDs in green are not changed
    requires DevAModesToObj(k, tds_state2, dev_id2, o_id) != {}
    
    requires ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)
    
    ensures DevAModesToObj(k, k_tds_state, dev_id2, o_id) != {}
{
    var k_params := KToKParams(k);
    
    AllReqNonEmptyAModesMustContainROrW();
    Lemma_K_DevAModesToObj_Property(k, tds_state2, dev_id2, o_id);
    var td_id :| td_id in tds_state2 && 
            CanActiveDevReadActiveTD(k_params, tds_state2, dev_id2, td_id) &&
            o_id in GetObjIDsRefedInTD(tds_state2, td_id) &&
            GetAModesOfObjRefedInTD(tds_state2, td_id, o_id) != {};
            
    var td_ids:seq<TD_ID> := Lemma_CanActiveDevReadActiveTD_Apply(k_params, tds_state2, dev_id2, td_id);
    
    // Prove all intermediate TDs are unchanged
    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, tds_state2, dev_id2, td_ids, td_id);
    
    Lemma_ObjsInSubjsAreAlsoInState(k);
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
    forall td_id2 | td_id2 in td_ids
        ensures ObjPID(k, td_id2.oid) == green_pid
    {
        assert CanActiveDevReadActiveTD(k_params, tds_state2, dev_id2, td_id2);
        Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(
            k, k_params, AllActiveDevs(k), tds_state2, dev_id2, td_id2);
    }
    
    assert forall td_id2 :: td_id2 in td_ids
            ==> tds_state2[td_id2] == k_tds_state[td_id2];
            
    // Prove CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id)
    Lemma_CanActiveDevReadActiveTD_IfRelatedTDsValsAreUnmodified(k_params, tds_state2, k_tds_state, td_ids,
        dev_id2, td_id);

    assert CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id2, td_id);
    
    // Prove DevAModesToObj(k, k_tds_state, dev_id2, o_id) != {}
    assert td_id in k_tds_state;
    Lemma_K_GetObjIDsRefedInTD_Equal(tds_state2, k_tds_state, td_id);
    assert o_id in GetObjIDsRefedInTD(k_tds_state, td_id);
    Lemma_K_GetAModesOfObjRefedInTD_Equal(tds_state2, k_tds_state, td_id, o_id);
    assert GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) != {};

    Lemma_K_DevAModesToObj_NonEmpty_Prove(k, k_tds_state, dev_id2, o_id, td_id);
}

lemma Lemma_NewDM_SubjObjDeactivate_FulfillSI2_DeactivateFromGreenPartition(
    ws:DM_State, k:State, ws':DM_State, k':State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'.subjects)
                ==> dev_id in AllActiveDevs(k) 

    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires pid != ws.red_pid
    requires pid != NULL

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)
    requires DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)

    requires forall id :: id in todeactivate_td_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == pid
    requires forall id :: id in todeactivate_fd_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == pid
    requires forall id :: id in todeactivate_do_ids
                ==> id.oid in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, id.oid) == pid

    requires (forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))

    ensures (forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id))
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
        assert td_id in DM_TDIDsInGreen(ws);
        if(td_id in DM_TDIDsInGreen(ws))
        {
            assert ws'.objects.tds[td_id] == ws.objects.tds[td_id];
            assert ActiveTDsState(k')[td_id] == ActiveTDsState(k)[td_id];

            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, ActiveTDsState(k), td_id);

            var k_tds_state := ActiveTDsState(k);
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
                assert td_id2 in k_tds_state[td_id].trans_params_tds;
                assert td_id2 in k'_params.objs_td_ids;
                assert td_id2 !in k'_params.hcoded_td_ids;

                if(k_tds_state[td_id].trans_params_tds[td_id2].amodes != {})
                {
                    assert ObjPID_SlimState(k_params.objs_pids, td_id2.oid) == ObjPID_SlimState(k_params.objs_pids, td_id.oid);
                    assert td_id2 in DM_TDIDsInGreen(ws') || td_id2 in todeactivate_td_ids;

                    if(td_id2 in todeactivate_td_ids)
                    {
                        if(DM_ObjPID(ws.objects, td_id.oid) == pid)
                        {
                            // Apply DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition
                            assert DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                                        todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
                            assert td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids);
                        
                            assert td_id2 !in k_tds_state[td_id].trans_params_tds || k_tds_state[td_id].trans_params_tds[td_id2].amodes == {};
                            assert k'_tds_state[td_id].trans_params_tds[td_id2].amodes == {};
                        }
                        else
                        {
                            // <td_id> is in a different green partition from <td_id2>
                            assert ObjPID_SlimState(k'_params.objs_pids, td_id.oid) == ObjPID_SlimState(k_params.objs_pids, td_id.oid);
                            assert k'_tds_state[td_id].trans_params_tds[td_id2].amodes == {};
                        }
                    }
                    else
                    {
                        // Apply SubjObjDeactivate_PropertiesOfTDs
                        assert td_id2 in DM_TDIDsInGreen(ws');
                        assert ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) == ObjPID_SlimState(k'_params.objs_pids, td_id.oid);
                    }
                }
                else
                {
                    assert k'_tds_state[td_id].trans_params_tds[td_id2].amodes == {};
                }
            }

            forall fd_id2 | fd_id2 in k'_tds_state[td_id].trans_params_fds
                ensures fd_id2 in k'_params.objs_fd_ids &&
                    ((ObjPID_SlimState(k'_params.objs_pids, fd_id2.oid) == 
                        ObjPID_SlimState(k'_params.objs_pids, td_id.oid)) ||
                            // The TD (<td_id>) contains a transfer, the target FD 
                            // (<fd_id2>) must be in the same partition with the TD
                     k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {})
            {
                assert fd_id2 in k_tds_state[td_id].trans_params_fds;
                assert fd_id2 in k'_params.objs_fd_ids;

                if(k_tds_state[td_id].trans_params_fds[fd_id2].amodes != {})
                {
                    assert ObjPID_SlimState(k_params.objs_pids, fd_id2.oid) == ObjPID_SlimState(k_params.objs_pids, td_id.oid);
                    assert fd_id2 in DM_FDIDsInGreen(ws') || fd_id2 in todeactivate_fd_ids;

                    if(fd_id2 in todeactivate_fd_ids)
                    {
                        if(DM_ObjPID(ws.objects, td_id.oid) == pid)
                        {
                            // Apply DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition
                            assert DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                                        todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
                            assert td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids);
                        
                            assert fd_id2 !in k_tds_state[td_id].trans_params_fds || k_tds_state[td_id].trans_params_fds[fd_id2].amodes == {};
                            assert k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {};
                        }
                        else
                        {
                            // <td_id> is in a different green partition from <fd_id2>
                            assert ObjPID_SlimState(k'_params.objs_pids, td_id.oid) == ObjPID_SlimState(k_params.objs_pids, td_id.oid);
                            assert k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {};
                        }
                    }
                    else
                    {
                        // Apply SubjObjDeactivate_PropertiesOfTDs
                        assert fd_id2 in DM_FDIDsInGreen(ws');
                        assert ObjPID_SlimState(k'_params.objs_pids, fd_id2.oid) == ObjPID_SlimState(k'_params.objs_pids, td_id.oid);
                    }
                }
                else
                {
                    assert k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {};
                }
            }

            forall do_id2 | do_id2 in k'_tds_state[td_id].trans_params_dos
                ensures do_id2 in k'_params.objs_do_ids && 
                    (ObjPID_SlimState(k'_params.objs_pids, do_id2.oid) ==
                        ObjPID_SlimState(k'_params.objs_pids, td_id.oid) ||
                            // The TD (<td_id>) contains a transfer, the target DO
                            // (<do_id2>) must be in the same partition with the TD
                     k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {})
            {
                assert do_id2 in k_tds_state[td_id].trans_params_dos;
                assert do_id2 in k'_params.objs_do_ids;

                if(k_tds_state[td_id].trans_params_dos[do_id2].amodes != {})
                {
                    assert ObjPID_SlimState(k_params.objs_pids, do_id2.oid) == ObjPID_SlimState(k_params.objs_pids, td_id.oid);
                    assert do_id2 in DM_DOIDsInGreen(ws') || do_id2 in todeactivate_do_ids;

                    if(do_id2 in todeactivate_do_ids)
                    {
                        if(DM_ObjPID(ws.objects, td_id.oid) == pid)
                        {
                            // Apply DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition
                            assert DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                                        todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
                            assert td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids);
                        
                            assert do_id2 !in k_tds_state[td_id].trans_params_dos || k_tds_state[td_id].trans_params_dos[do_id2].amodes == {};
                            assert k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {};
                        }
                        else
                        {
                            // <td_id> is in a different green partition from <do_id2>
                            assert ObjPID_SlimState(k'_params.objs_pids, td_id.oid) == ObjPID_SlimState(k_params.objs_pids, td_id.oid);
                            assert k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {};
                        }
                    }
                    else
                    {
                        // Apply SubjObjDeactivate_PropertiesOfTDs
                        assert do_id2 in DM_DOIDsInGreen(ws');
                        assert ObjPID_SlimState(k'_params.objs_pids, do_id2.oid) == ObjPID_SlimState(k'_params.objs_pids, td_id.oid);
                    }
                }
                else
                {
                    assert k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {};
                }
            }

            Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Prove(k'_params, k'_tds_state, td_id);
            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, k'_tds_state, td_id);
        }
    }
}

lemma Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_TDsStateCanBeReachedWithDevsInRed(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, tds_state2:TDs_Vals, k_tds_state:TDs_Vals
)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires IsValidState(k)

    requires forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ((tds_state2 == ActiveTDsState(k)) ||
                        (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state2) &&
                         IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state2)))

    requires tds_state2 in AllReachableActiveTDsStates(k)
    requires k_tds_state == ActiveTDsState(k)

    ensures (k_tds_state == tds_state2 ||
                    (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2)))
{
    // Dafny can automatically prove this lemma
}

// (needs 50s to verify)
lemma Lemma_DM_ObjDeactivate_IfDevHasReadTransfersToTD_ThenTDHasNoTransfersToObjsToBeDeactivated(
    ws:DM_State, k:State, k_tds_state:TDs_Vals, dev_id:Dev_ID,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    green_pid:Partition_ID, td_ids:seq<TD_ID>, last_td_id:TD_ID, o_id:Object_ID
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k)

    requires k_tds_state == ActiveTDsState(k)
    
    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    requires TDsStateToCASForDev_PreConditions(k)
    requires forall tds_state :: tds_state in {k_tds_state}
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Needed for P_BuildCAS_Properties
    //requires P_BuildCAS_Properties(k, {k_tds_state}, k_cas) 

    requires green_pid != NULL
    requires green_pid != ws.red_pid

    requires forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid

    requires dev_id in AllActiveDevs(k)
    requires P_CanActiveDevReadActiveTD_Def(KToKParams(k), k_tds_state, dev_id, td_ids, last_td_id)
        // Requirement: Exists a path of TDs
    requires forall td_id :: td_id in td_ids
                ==> ObjPID(k, td_id.oid) == green_pid
        // Requirement: All TDs in the path are in the green partition
    requires k.subjects.devs[dev_id].hcoded_td_id !in todeactivate_td_ids
        // Requirement: Hardcoded TD of the device is not going to be deactivated
    requires o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)
    requires o_id in GetObjIDsRefedInTD(k_tds_state, last_td_id)
    requires GetAModesOfObjRefedInTD(k_tds_state, last_td_id, o_id) != {}
        // Requirement: The last TD has transfer to the object (<o_id>)

    requires DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid)

    ensures false

    decreases |td_ids|
{
    assert forall td_id :: td_id in td_ids
            ==> td_id in DM_TDIDsInGreen(ws);

    if(|td_ids| == 1)
    {
        var hcoded_td_id := td_ids[0];
        assert hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id;
        assert hcoded_td_id == last_td_id;

        // Apply DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition
        assert hcoded_td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids);
        Lemma_DM_ObjDeactivate_ApplyDM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(k, k_tds_state, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
            dev_id, hcoded_td_id, o_id);
        assert GetAModesOfObjRefedInTD(k_tds_state, last_td_id, o_id) == {};
        assert false;
    }
    else
    {
        assert |td_ids| > 1;

        if(last_td_id !in todeactivate_td_ids)
        {
            assert last_td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids);
            Lemma_DM_ObjDeactivate_ApplyDM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(k, k_tds_state, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                dev_id, last_td_id, o_id);
            assert GetAModesOfObjRefedInTD(k_tds_state, last_td_id, o_id) == {};
            assert false;
        }
        else
        {
            assert last_td_id in todeactivate_td_ids;
            var new_td_ids:seq<TD_ID> := td_ids[..|td_ids|-1];
            var new_last_td_id := new_td_ids[|new_td_ids|-1];

            // Prove preconditions
            forall i | 0<=i<|new_td_ids| - 1 
                ensures new_td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[new_td_ids[i]])
            {
                assert new_td_ids[i] == td_ids[i];
                assert new_td_ids[i+1] == td_ids[i+1];
            }

            Lemma_DM_ObjDeactivate_IfDevHasReadTransfersToTD_ThenTDHasNoTransfersToObjsToBeDeactivated(ws, k, k_tds_state, dev_id,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids,
                green_pid, new_td_ids, new_last_td_id, last_td_id.oid);
        }
    }
}

lemma Lemma_DM_ObjDeactivate_ApplyDM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(
    k:State, k_tds_state:TDs_Vals, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    dev_id:Dev_ID, td_id:TD_ID, o_id:Object_ID
)
    requires IsValidState(k) 
    requires forall id :: id in todeactivate_td_ids 
                ==> id in k.objects.tds
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in k.objects.fds
    requires forall id :: id in todeactivate_do_ids 
                ==> id in k.objects.dos

    requires dev_id in AllActiveDevs(k)
    requires td_id in k_tds_state
    requires k_tds_state == ActiveTDsState(k)
    requires CanActiveDevReadActiveTD(KToKParams(k), k_tds_state, dev_id, td_id)

    requires (forall id :: id in todeactivate_td_ids 
                    ==> (id !in k_tds_state[td_id].trans_params_tds || k_tds_state[td_id].trans_params_tds[id].amodes == {}))
    requires (forall id :: id in todeactivate_fd_ids 
                    ==> (id !in k_tds_state[td_id].trans_params_fds || k_tds_state[td_id].trans_params_fds[id].amodes == {}))
    requires (forall id :: id in todeactivate_do_ids 
                    ==> (id !in k_tds_state[td_id].trans_params_dos || k_tds_state[td_id].trans_params_dos[id].amodes == {}))
        // Requirement: Statement from DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition
    requires o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)

    ensures o_id !in GetObjIDsRefedInTD(k_tds_state, td_id) || GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {}
{
    var k_params := KToKParams(k);

    Lemma_DM_SameIDsIffSameInternalIDs();
    if(o_id in TDIDsToObjIDs(todeactivate_td_ids))
    {
        assert TD_ID(o_id) in todeactivate_td_ids;
        if(TD_ID(o_id) in k_tds_state[td_id].trans_params_tds)
        {
            Lemma_K_IsValidState_ReachableTDsStates_Apply(k, k_tds_state, dev_id, td_id);
            assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, k_tds_state, td_id);
            assert FD_ID(o_id) !in k_tds_state[td_id].trans_params_fds;
            assert DO_ID(o_id) !in k_tds_state[td_id].trans_params_dos;
            assert GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {};
        }
        else
        {
            assert TD_ID(o_id) !in k_tds_state[td_id].trans_params_tds;
            
            Lemma_K_IsValidState_ReachableTDsStates_Apply(k, k_tds_state, dev_id, td_id);
            assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, k_tds_state, td_id);
            assert FD_ID(o_id) !in k_tds_state[td_id].trans_params_fds;
            assert DO_ID(o_id) !in k_tds_state[td_id].trans_params_dos;

            Lemma_K_GetObjIDsRefedInTD_NotIn(k_tds_state, td_id, o_id);
            assert o_id !in GetObjIDsRefedInTD(k_tds_state, td_id);
        }
        assert o_id !in GetObjIDsRefedInTD(k_tds_state, td_id) || GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {};
    }

    if(o_id in FDIDsToObjIDs(todeactivate_fd_ids))
    {
        assert FD_ID(o_id) in todeactivate_fd_ids;
        if(FD_ID(o_id) in k_tds_state[td_id].trans_params_fds)
        {
            Lemma_K_IsValidState_ReachableTDsStates_Apply(k, k_tds_state, dev_id, td_id);
            assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, k_tds_state, td_id);
            assert TD_ID(o_id) !in k_tds_state[td_id].trans_params_tds;
            assert DO_ID(o_id) !in k_tds_state[td_id].trans_params_dos;
            assert GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {};
        }
        else
        {
            assert FD_ID(o_id) !in k_tds_state[td_id].trans_params_fds;
            
            Lemma_K_IsValidState_ReachableTDsStates_Apply(k, k_tds_state, dev_id, td_id);
            assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, k_tds_state, td_id);
            assert TD_ID(o_id) !in k_tds_state[td_id].trans_params_tds;
            assert DO_ID(o_id) !in k_tds_state[td_id].trans_params_dos;

            Lemma_K_GetObjIDsRefedInTD_NotIn(k_tds_state, td_id, o_id);
            assert o_id !in GetObjIDsRefedInTD(k_tds_state, td_id);
        }
        assert o_id !in GetObjIDsRefedInTD(k_tds_state, td_id) || GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {};
    }

    if(o_id in DOIDsToObjIDs(todeactivate_do_ids))
    {
        assert DO_ID(o_id) in todeactivate_do_ids;
        if(DO_ID(o_id) in k_tds_state[td_id].trans_params_dos)
        {
            Lemma_K_IsValidState_ReachableTDsStates_Apply(k, k_tds_state, dev_id, td_id);
            assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, k_tds_state, td_id);
            assert FD_ID(o_id) !in k_tds_state[td_id].trans_params_fds;
            assert TD_ID(o_id) !in k_tds_state[td_id].trans_params_tds;
            assert GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {};
        }
        else
        {
            assert DO_ID(o_id) !in k_tds_state[td_id].trans_params_dos;
            
            Lemma_K_IsValidState_ReachableTDsStates_Apply(k, k_tds_state, dev_id, td_id);
            assert !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, k_tds_state, td_id);
            assert FD_ID(o_id) !in k_tds_state[td_id].trans_params_fds;
            assert TD_ID(o_id) !in k_tds_state[td_id].trans_params_tds;

            Lemma_K_GetObjIDsRefedInTD_NotIn(k_tds_state, td_id, o_id);
            assert o_id !in GetObjIDsRefedInTD(k_tds_state, td_id);
        }
        assert o_id !in GetObjIDsRefedInTD(k_tds_state, td_id) || GetAModesOfObjRefedInTD(k_tds_state, td_id, o_id) == {};
    }
}

lemma Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs_OIDInGreenPartition(
    ws:DM_State, k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    green_pid:Partition_ID, o_id:Object_ID
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in DM_AllDOIDs(ws.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_fd_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in todeactivate_do_ids 
                ==> DM_ObjPID(ws.objects, id.oid) == green_pid

    requires o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)

    ensures ObjPID(k, o_id) == green_pid
{
    // Dafny can automatically prove this lemma
}