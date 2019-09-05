include "../Abstract/Model.dfy"
include "Mappings_ValidState_SecureState.dfy"

//******** SubjRead ********//
// Property: If a subject read objects (and/or copy to destination objects),  
// then the subject and all accessed objects must be in the same partition 
predicate P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(
    ws:DM_State, s_id:Subject_ID,
    read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    requires s_id in DM_AllSubjsIDs(ws.subjects)

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (forall o_id :: o_id in read_objs
                    ==> o_id in DM_AllObjsIDs(ws.objects) &&
                        DM_ObjPID(ws.objects, o_id) == DM_SubjPID(ws.subjects, s_id)) &&
        // Objects in parameters must be in the same partition with the driver
    (forall td_id :: td_id in tds_dst_src
                    ==> DM_ObjPID(ws.objects, td_id.oid) == DM_SubjPID(ws.subjects, s_id)) &&
    (forall fd_id :: fd_id in fds_dst_src
                    ==> DM_ObjPID(ws.objects, fd_id.oid) == DM_SubjPID(ws.subjects, s_id)) &&
    (forall do_id :: do_id in dos_dst_src
                    ==> DM_ObjPID(ws.objects, do_id.oid) == DM_SubjPID(ws.subjects, s_id)) &&
        // All objects that store read results must be in the same partition
        // with the subject

    (true)
}

predicate DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(
    ws:DM_State, 
    
    tds_dst_src:map<TD_ID, TD_ID>,
    fds_dst_src:map<FD_ID, FD_ID>,
    dos_dst_src:map<DO_ID, DO_ID> 
)
{
    (forall td_id :: td_id in tds_dst_src
                ==> td_id in ws.objects.tds && tds_dst_src[td_id] in ws.objects.tds) &&
    (forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in ws.objects.fds && fds_dst_src[fd_id] in ws.objects.fds) &&
    (forall do_id :: do_id in dos_dst_src
                ==> do_id in ws.objects.dos && dos_dst_src[do_id] in ws.objects.dos) &&
        // Requirement: Destination and source objects must be in the DM state
        
    (true)
}

predicate DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(
    ws:DM_State,
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    (forall td_id2 :: td_id2 in tds_dst_src
                ==> DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, td_id2, ws.objects.tds[tds_dst_src[td_id2]].val))&&
    (forall fd_id2 :: fd_id2 in fds_dst_src
                ==> DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, fd_id2, ws.objects.fds[fds_dst_src[fd_id2]].val))&&
    (forall do_id2 :: do_id2 in dos_dst_src
                ==> DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, do_id2, ws.objects.dos[dos_dst_src[do_id2]].val))&&
        // Requirement: Writing destination TDs/FDs/DOs with values of source 
        // objects must be in tranfers

    (true)
}

predicate DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    
    (forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)) &&
        // Requirement: The device (<Dev_ID(dev_sid)>) must have transfers to
        // the objects (<read_objs>)
        
    (true)
}



//******** DrvWrite ********//
function method DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
) : bool
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
        // Requirement: Driver only write existing objects
{
    (forall id :: id in td_id_val_map
        ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, id.oid)) &&
    (forall id :: id in fd_id_val_map
        ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, id.oid)) &&
    (forall id :: id in do_id_val_map
        ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, id.oid))
}

function method DM_GreenDrvWrite_ChkNewValsOfTDs(
    ws:DM_State, 
    td_id_val_map:map<TD_ID, TD_Val>
) : bool
    requires DM_IsValidState_Subjects(ws) && DM_IsValidState_Objects(ws)
    
    requires forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds
        // Requirement: Driver only write existing objects
    requires forall id :: id in td_id_val_map
                ==> DM_ObjPID(ws.objects, id.oid) != NULL
        // Requirement: TDs in <td_id_val_map> are active
{
    var k := DMStateToState(ws);
    var tds' := WriteTDsVals(ws.objects.tds, td_id_val_map);

    forall id :: id in td_id_val_map
        ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState_SlimState(tds'), id)
}




//******** DevWrite ********//
predicate DM_DevWrite_WriteTDWithValMustBeInATransfer(
    ws:DM_State, dev_sid:Subject_ID, target_td_id:TD_ID, write_val:TD_Val
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, target_td_id, write_val)
}

predicate DM_DevWrite_WriteFDWithValMustBeInATransfer(
    ws:DM_State, dev_sid:Subject_ID, target_fd_id:FD_ID, write_val:FD_Val
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, target_fd_id, write_val)
}

predicate DM_DevWrite_WriteDOWithValMustBeInATransfer(
    ws:DM_State, dev_sid:Subject_ID, target_do_id:DO_ID, write_val:DO_Val
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, target_do_id, write_val)
}

// Property: If a subject write objects, then the subject and the objects must 
// be in the same partition 
predicate P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(
    ws:DM_State, 
    s_id:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires DM_IsValidState_ObjIDs(ws) 
    requires s_id in DM_AllSubjsIDs(ws.subjects)

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
        // Requirement: Device only write existing objects
{
    forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                    // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
        ==> o_id in DM_AllObjsIDs(ws.objects) &&
            DM_ObjPID(ws.objects, o_id) == DM_SubjPID(ws.subjects, s_id) &&

    (true)
}




//******** Deactivate ********//
function method DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(
    ws:DM_State, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>, green_pid:Partition_ID
) : bool
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in DM_AllTDIDs(ws.objects)
    requires forall id :: id in todeactivate_fd_ids
                ==> id in DM_AllFDIDs(ws.objects)
    requires forall id :: id in todeactivate_do_ids
                ==> id in DM_AllDOIDs(ws.objects)
                
    requires green_pid != NULL
    requires green_pid != ws.red_pid
{
    var k := DMStateToState(ws);
    var k_tds_state := ActiveTDsState(k);

    forall td_id :: td_id in (DM_TDIDsInGreen(ws) - todeactivate_td_ids) &&
                    DM_ObjPID(ws.objects, td_id.oid) == green_pid
                        // For all other green TDs in the partition <green_pid>
                ==> (forall id :: id in todeactivate_td_ids 
                            ==> (id !in k_tds_state[td_id].trans_params_tds || k_tds_state[td_id].trans_params_tds[id].amodes == {})) &&
                    (forall id :: id in todeactivate_fd_ids 
                            ==> (id !in k_tds_state[td_id].trans_params_fds || k_tds_state[td_id].trans_params_fds[id].amodes == {})) &&
                    (forall id :: id in todeactivate_do_ids 
                            ==> (id !in k_tds_state[td_id].trans_params_dos || k_tds_state[td_id].trans_params_dos[id].amodes == {}))
                        // They do not ref any objects to be deactivated
}




//******** DevDeactivate ********//
predicate P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_SubjsObjsPIDs(ws)

    requires dev_id in DM_AllDevIDs(ws.subjects)
    requires DM_SubjPID(ws.subjects, dev_id.sid) == ws.red_pid
{
    var objs := DM_OwnedObjs(ws.subjects, dev_id.sid);

    var k := DMStateToState(ws);
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState_SlimState(k.objects.tds);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);

    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects.tds) &&
            (k_tds_state == tds_state2 || 
                (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                    IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        DM_DevsInRed(ws), k_tds_state, tds_state2)))
                            // Forall tds_state2, k_tds_state -->* tds_state2
        ==> (forall o_id, dev_id2 :: 
                    o_id in objs &&
                    dev_id2 in DM_DevsInRed(ws) - {dev_id}
                            // For each device (<dev_id2>) in red different from the device (<dev_id>)
                ==> DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {}))
                            // The device has no transfer to any objects of the device <dev_id>
}

// (needs 30s to verify)
method DM_Chk_DevDeactivate_OtherDevsInRedPartitonHaveNoTransferToGivenRedDevAtAnyTime(
    ws:DM_State, k:State, dev_id:Dev_ID
) returns (d:bool)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k) && IsSecureState(k)

    requires dev_id in DM_DevsInRed(ws)

    ensures d ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, dev_id)
{
    // Calculate reachable snapshots of active TDs in K
    var k_tds_states := ValidSecureState_ReachableStatesOfActiveTDs(k);

    // Build CAS for K
    var k_cas := BuildCAS(k, KToKParams(k), k_tds_states);

    Lemma_K_P_ObjsInSubjsAreAlsoInState_Prove(k);

    d := (forall o_id, dev_id2 :: 
            (o_id in OwnObjIDs(k, dev_id.sid)) && 
            (dev_id2 in DM_DevsInRed(ws) - {dev_id})
            ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {});

    // Prove P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime
    if(d)
    {
        var objs := DM_OwnedObjs(ws.subjects, dev_id.sid);
        var k_params := KToKParams(k);
        var k_tds_state := ActiveTDsState_SlimState(k.objects.tds);

        forall tds_state2 | TDsStateGetTDIDs(tds_state2) == AllActiveTDs_SlimState(k.objects.tds) &&
                (k_tds_state == tds_state2 || 
                    (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2) &&
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                            DM_DevsInRed(ws), k_tds_state, tds_state2)))
            ensures (forall o_id, dev_id2 :: 
                    o_id in objs &&
                    dev_id2 in DM_DevsInRed(ws) - {dev_id}
                            // For each device (<dev_id2>) in red different from the device (<dev_id>)
                ==> DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {})
        {
            // Prove tds_state2 in AllReachableActiveTDsStates(k);
            if(k_tds_state == tds_state2)
            {
                assert tds_state2 in AllReachableActiveTDsStates(k);
            }
            else
            {
                Lemma_DM_DevsInRed_IsSubsetOfAllActiveDevs(ws, k);
                Lemma_K_IfTDsStateCanBeReachedViaSmallSetOfActiveDevs_ThenCanBeReachedViaLargeSetToo(
                    k_params, DM_DevsInRed(ws), AllActiveDevs(k), k_tds_state, tds_state2);
                assert tds_state2 in AllReachableActiveTDsStates(k);
            }
            assert tds_state2 in AllReachableActiveTDsStates(k);

            Lemma_DMOwnedObjsEqualsOwnObjIDs(ws, k);
            forall o_id, dev_id2 | o_id in objs &&
                        dev_id2 in DM_DevsInRed(ws) - {dev_id}
                            // For each device (<dev_id2>) in red different from the device (<dev_id>)
                ensures DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id) == {}
            {
                Lemma_DM_ObjsOwnedByActiveSubjs_AreActive(ws, k, dev_id.sid, o_id);
                assert dev_id2 in AllActiveDevs(k);
                assert o_id in AllActiveObjs(k);

                assert IsInCAS(k_cas, dev_id2, o_id);
                var amodes := CASGetAModes(k_cas, dev_id2, o_id);
                assert amodes == {};
                Lemma_EmptyAModesIsNoRAndNoW(amodes);

                var amodes2 := DevAModesToObj_SlimState(k_params, tds_state2, dev_id2, o_id);
                if(R in amodes2)
                {
                    assert tds_state2 in k_tds_states;
                    assert R in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                    assert R in amodes;
                    assert false;
                }
                if(W in amodes2)
                {
                    assert tds_state2 in k_tds_states;
                    assert W in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                    assert W in amodes;
                    assert false;
                }

                Lemma_EmptyAModesIsNoRAndNoW(amodes2);
                assert amodes2 == {};
            }
        }
    }
}




//******** For Proof of Commutative Diagrams ********//
function DrvDevWrite_Func(
    k:State,
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (k':State)
    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> td_id2 in k.objects.tds
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> fd_id2 in k.objects.fds
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> do_id2 in k.objects.dos
{
    // Construct k'.objects
    var tds' := WriteTDsVals(k.objects.tds, td_id_val_map);
    var fds' := WriteFDsVals(k.objects.fds, fd_id_val_map);
    var dos' := WriteDOsVals(k.objects.dos, do_id_val_map);
    var new_objects := Objects(tds', fds', dos');

    State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}

function EmptyPartitionCreate_Func(k:State, new_pid:Partition_ID) : (k':State)
{
    var pids' := k.pids + {new_pid};

    State(k.subjects, k.objects, pids', k.tds_to_all_states)
}

function EmptyPartitionDestroy_Func(k:State, pid:Partition_ID) : (k':State)
{
    var pids' := k.pids - {pid};

    State(k.subjects, k.objects, pids', k.tds_to_all_states)
}

function DrvActivate_Func(k:State, drv_sid:Subject_ID, pid:Partition_ID) : (k':State)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires pid != NULL

    requires k.subjects.drvs[Drv_ID(drv_sid)].td_ids <= MapGetKeys(k.objects.tds)
    requires k.subjects.drvs[Drv_ID(drv_sid)].fd_ids <= MapGetKeys(k.objects.fds)
    requires k.subjects.drvs[Drv_ID(drv_sid)].do_ids <= MapGetKeys(k.objects.dos)
{
    var drv_id := Drv_ID(drv_sid);
    var drv_state := IDToDrv(k, drv_id);
    var new_drv_state := Drv_State(pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
    var new_drvs := k.subjects.drvs[drv_id := new_drv_state];
    var new_subjects := Subjects(new_drvs, k.subjects.devs);

    // Construct k'.objects
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
    //// Clear the objects being activated
    var temp_tds := ClearTDs(k.objects.tds, tds_owned_by_drv);
    var temp_fds := ClearFDs(k.objects.fds, fds_owned_by_drv);
    var temp_dos := ClearDOs(k.objects.dos, dos_owned_by_drv);
    //// Modify the PID of these objects
    var tds' := SetTDsPIDs(temp_tds, tds_owned_by_drv, pid);
    var fds' := SetFDsPIDs(temp_fds, fds_owned_by_drv, pid);
    var dos' := SetDOsPIDs(temp_dos, dos_owned_by_drv, pid);
    var new_objects := Objects(tds', fds', dos');

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function DevActivate_Func(k:State, dev_sid:Subject_ID, pid:Partition_ID) : (k':State)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires pid != NULL

    requires k.subjects.devs[Dev_ID(dev_sid)].td_ids <= MapGetKeys(k.objects.tds)
    requires k.subjects.devs[Dev_ID(dev_sid)].fd_ids <= MapGetKeys(k.objects.fds)
    requires k.subjects.devs[Dev_ID(dev_sid)].do_ids <= MapGetKeys(k.objects.dos)
{
    var dev_id := Dev_ID(dev_sid);
    var dev_state := IDToDev(k, dev_id);
    var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
    var new_devs := k.subjects.devs[dev_id := new_dev_state];
    var new_subjects := Subjects(k.subjects.drvs, new_devs);

    // Construct k'.objects
    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    //// Clear the objects being activated
    var toactive_hcoded_td_id := dev_state.hcoded_td_id;
    var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
    var temp_tds := ClearTDs(k.objects.tds, toclear_td_ids);
    var temp_fds := ClearFDs(k.objects.fds, fds_owned_by_dev);
    var temp_dos := ClearDOs(k.objects.dos, dos_owned_by_dev);
    //// Modify the PID of these objects
    var tds' := SetTDsPIDs(temp_tds, tds_owned_by_dev, pid);
    var fds' := SetFDsPIDs(temp_fds, fds_owned_by_dev, pid);
    var dos' := SetDOsPIDs(temp_dos, dos_owned_by_dev, pid);
    var new_objects := Objects(tds', fds', dos');

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function ExternalObjsActivate_Func(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID
) : (k':State)
    requires IsValidState(k)

    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    requires pid != NULL

    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> MapGetKeys(k'.objects.fds) == MapGetKeys(k.objects.fds)
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> MapGetKeys(k'.objects.dos) == MapGetKeys(k.objects.dos)

    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> (forall td_id :: td_id in k.objects.tds
                            ==> (td_id in td_ids ==> k'.objects.tds[td_id] == TD_State(pid, TD_Val(map[], map[], map[]))) &&
                                (td_id !in td_ids ==> k'.objects.tds[td_id] == k.objects.tds[td_id]))
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> (forall fd_id :: fd_id in k.objects.fds
                            ==> (fd_id in fd_ids ==> k'.objects.fds[fd_id] == FD_State(pid, FD_Val(""))) &&
                                (fd_id !in fd_ids ==> k'.objects.fds[fd_id] == k.objects.fds[fd_id]))
    ensures P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
                ==> (forall do_id :: do_id in k.objects.dos
                            ==> (do_id in do_ids ==> k'.objects.dos[do_id] == DO_State(pid, DO_Val(""))) &&
                                (do_id !in do_ids ==> k'.objects.dos[do_id] == k.objects.dos[do_id]))
{
    // Clear the objects being activated
    var temp_tds := ClearTDs(k.objects.tds, td_ids);
    var temp_fds := ClearFDs(k.objects.fds, fd_ids);
    var temp_dos := ClearDOs(k.objects.dos, do_ids);

    // Modify the PID of these objects
    var tds' := SetTDsPIDs(temp_tds, td_ids, pid);
    var fds' := SetFDsPIDs(temp_fds, fd_ids, pid);
    var dos' := SetDOsPIDs(temp_dos, do_ids, pid);

    var new_objects := Objects(tds', fds', dos');

    State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}

function DrvDeactivate_Func(k:State, drv_sid:Subject_ID) : (k':State)
    requires Drv_ID(drv_sid) in k.subjects.drvs

    requires k.subjects.drvs[Drv_ID(drv_sid)].td_ids <= MapGetKeys(k.objects.tds)
    requires k.subjects.drvs[Drv_ID(drv_sid)].fd_ids <= MapGetKeys(k.objects.fds)
    requires k.subjects.drvs[Drv_ID(drv_sid)].do_ids <= MapGetKeys(k.objects.dos)
{
    var drv_id := Drv_ID(drv_sid);
    var drv_state := IDToDrv(k, drv_id);
    var new_drv_state := Drv_State(NULL, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
    var new_drvs := k.subjects.drvs[drv_id := new_drv_state];

    // Construct k'.subjects
    var new_subjects := Subjects(new_drvs, k.subjects.devs);

    // Construct k'.objects
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
    //// Modify the PID of these objects
    var tds' := SetTDsPIDs(k.objects.tds, tds_owned_by_drv, NULL);
    var fds' := SetFDsPIDs(k.objects.fds, fds_owned_by_drv, NULL);
    var dos' := SetDOsPIDs(k.objects.dos, dos_owned_by_drv, NULL);
    var new_objects := Objects(tds', fds', dos');

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function DevDeactivate_Func(k:State, dev_sid:Subject_ID) : (k':State)
    requires Dev_ID(dev_sid) in k.subjects.devs

    requires k.subjects.devs[Dev_ID(dev_sid)].td_ids <= MapGetKeys(k.objects.tds)
    requires k.subjects.devs[Dev_ID(dev_sid)].fd_ids <= MapGetKeys(k.objects.fds)
    requires k.subjects.devs[Dev_ID(dev_sid)].do_ids <= MapGetKeys(k.objects.dos)
{
    var dev_id := Dev_ID(dev_sid);
    var dev_state := IDToDev(k, dev_id);
    var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
    var new_devs := k.subjects.devs[dev_id := new_dev_state];
    var new_subjects := Subjects(k.subjects.drvs, new_devs);

    // Construct k'.objects
    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    //// Modify the PID of these objects
    var tds' := SetTDsPIDs(k.objects.tds, tds_owned_by_dev, NULL);
    var fds' := SetFDsPIDs(k.objects.fds, fds_owned_by_dev, NULL);
    var dos' := SetDOsPIDs(k.objects.dos, dos_owned_by_dev, NULL);
    var new_objects := Objects(tds', fds', dos');

    State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

function ExternalObjsDeactivate_Func(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
) : (k':State)
    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
{
    // Construct k'.objects
    //// Modify the PID of these objects
    var tds' := SetTDsPIDs(k.objects.tds, td_ids, NULL);
    var fds' := SetFDsPIDs(k.objects.fds, fd_ids, NULL);
    var dos' := SetDOsPIDs(k.objects.dos, do_ids, NULL);
    var new_objects := Objects(tds', fds', dos');

    State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}