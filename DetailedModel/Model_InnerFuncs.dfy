include "../Abstract/Model.dfy"
include "Mappings_ValidState_SecureState.dfy"
include "Utils_DevsActivateCond.dfy"
include "Model_Ops_Predicates.dfy"
include "Lemmas_Ops_SubjRead.dfy"

//******** DrvRead/DevRead ********//
function method DM_RedDrvRead_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: the driver is in a green partition

    requires read_objs <= DM_AllObjsIDs(ws.objects)
    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src
        // Requirement: The driver does not write any hardcoded TDs

    ensures result.1 ==> result.0 == DM_RedDrvWrite_InnerFunc(ws, drv_sid, 
                                            DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)).1
    ensures !result.1 ==> result.0 == ws
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id)) then
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

        var ws2' := DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1;
        var d := DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2;
        (ws2',d)
    else
        (ws, false)
}

function method DM_GreenDrvReadRead_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: the driver is in a green partition

    requires read_objs <= DM_AllObjsIDs(ws.objects)
    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src
        // Requirement: The driver does not write any hardcoded TDs

    ensures result.1 ==> result.0 == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, 
                                            DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                            DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)).0
    ensures !result.1 ==> result.0 == ws
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id)) then
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

        DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    else
        (ws, false)
}

function method DM_DevRead_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    // Construct ws'
    var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
    var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
    var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

    if(DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid) then
        // If the device is in the red partition
        DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    else
        // If the device is in a green partition
        DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}




//******** DrvWrite/DevWrite ********//
function method DM_RedDrvWrite_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid
        // Requirement: the driver is in the red partition

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures result.2 ==> DM_IsValidState(result.0)
{
    if( DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) then
        // Construct ws'.objects
        var tds' := WriteTDsVals(ws.objects.tds, td_id_val_map);
        var fds' := WriteFDsVals(ws.objects.fds, fd_id_val_map);
        var dos' := WriteDOsVals(ws.objects.dos, do_id_val_map);
        var new_objects := Objects(tds', fds', dos');

        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDM_FulFillIsValidState_SubjsOwnObjsThenInSamePartition_IfPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Apply DevHWProt
        var ws2' := DevHWProt(ws');
        var ws_d := true;

        (ws', ws2', ws_d)
    else
        (ws, ws, false)
}

function method DM_GreenDrvWrite_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: the driver is in the green partition

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs
{
    if( DM_DrvWrite_ChkDrvAndObjsAreInSamePartition(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
        DM_GreenDrvWrite_ChkNewValsOfTDs(ws, td_id_val_map)
    ) then
        // Construct ws'.objects
        var tds' := WriteTDsVals(ws.objects.tds, td_id_val_map);
        var fds' := WriteFDsVals(ws.objects.fds, fd_id_val_map);
        var dos' := WriteDOsVals(ws.objects.dos, do_id_val_map);
        var new_objects := Objects(tds', fds', dos');

        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_RedDevWrite_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid
        // Requirement: the device is in the red partition

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
{
    // Construct ws'.objects
    var tds' := WriteTDsVals(ws.objects.tds, td_id_val_map);
    var fds' := WriteFDsVals(ws.objects.fds, fd_id_val_map);
    var dos' := WriteDOsVals(ws.objects.dos, do_id_val_map);
    var new_objects := Objects(tds', fds', dos');

    var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
    var ws_d := true;

    (ws', ws_d)
}

function method DM_GreenDevWrite_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
    requires DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
        // Requirement: the device must be in a green partition

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
{
    // Construct ws'.objects
    var tds' := WriteTDsVals(ws.objects.tds, td_id_val_map);
    var fds' := WriteFDsVals(ws.objects.fds, fd_id_val_map);
    var dos' := WriteDOsVals(ws.objects.dos, do_id_val_map);
    var new_objects := Objects(tds', fds', dos');

    var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
    var ws_d := true;

    (ws', ws_d)
}




//******** Create/Destroy Partition ********//
function method DM_EmptyPartitionCreate_InnerFunc(
    ws:DM_State, 
    new_pid:Partition_ID // The ID of the new partition
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    if (new_pid != NULL) &&
        (new_pid !in ws.pids) 
    then
        // Add the ID of the creating partition into the new state
        var pids' := ws.pids + {new_pid};

        var ws'_subjects := ws.subjects;
        var ws'_objects := ws.objects;

        var ws' := DM_State(ws'_subjects, ws'_objects, pids', ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}

function method DM_EmptyPartitionDestroy_InnerFunc(
    ws:DM_State, 
    pid:Partition_ID // The ID of the partition to be destroyed
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    if ((pid != NULL) &&
        (pid in ws.pids) &&
        (forall s_id :: s_id in DM_AllSubjsIDs(ws.subjects) ==> DM_SubjPID(ws.subjects, s_id) != pid) &&
        (forall o_id :: o_id in DM_AllObjsIDs(ws.objects) ==> DM_ObjPID(ws.objects, o_id) != pid) &&
        pid != ws.red_pid)
            // OS partition cannot be destroyed
    then
        // Add the ID of the creating partition into the new state
        var pids' := ws.pids - {pid};

        var ws'_subjects := ws.subjects;
        var ws'_objects := ws.objects;

        var ws' := DM_State(ws'_subjects, ws'_objects, pids', ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}




//******** DrvActivate ********//
function method DM_DrvActivateToGreenPartition_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver to be activated
    green_pid:Partition_ID // ID of the partition to activate the driver into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: the destination partition must be a green partition
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    if((DM_SubjPID(ws.subjects, drv_sid) == NULL) && (green_pid in ws.pids)) then
        // Set the driver's partition ID to be <green_pid>
        var drv_state := ws.subjects.drvs[drv_id];
        var new_drv_state := Drv_State(green_pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
        var new_drvs := ws.subjects.drvs[drv_id := new_drv_state];
        
        // Construct k'.subjects
        var new_subjects := Subjects(new_drvs, ws.subjects.devs);

        // Construct k'.objects
        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;
        //// Clear the objects being activated
        var temp_tds := ClearTDs(ws.objects.tds, tds_owned_by_drv);
        var temp_fds := ClearFDs(ws.objects.fds, fds_owned_by_drv);
        var temp_dos := ClearDOs(ws.objects.dos, dos_owned_by_drv);
        //// Modify the PID of these objects
        var tds' := SetTDsPIDs(temp_tds, tds_owned_by_drv, green_pid);
        var fds' := SetFDsPIDs(temp_fds, fds_owned_by_drv, green_pid);
        var dos' := SetDOsPIDs(temp_dos, dos_owned_by_drv, green_pid);
        var new_objects := Objects(tds', fds', dos');
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}




//******** DevActivate ********//
function method DM_DevActivate_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device to be activated
    pid:Partition_ID // ID of the partition to activate the device into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires pid != NULL
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    if( (DM_SubjPID(ws.subjects, dev_sid) == NULL) && (pid in ws.pids) &&
            (pid == ws.red_pid ==> TryActivateDevInRed(ws, dev_id)) &&
            (pid != ws.red_pid ==> TryActivateDevInGreen(ws, dev_id)) &&
                // If the device is an ephemeral device, the two checks decide 
                // if we can activate the device into the destination partition
            (forall hcoded_td_id, td_id :: hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
                        td_id in k.objects.tds[hcoded_td_id].val.trans_params_tds
                    ==> W !in k.objects.tds[hcoded_td_id].val.trans_params_tds[td_id].amodes)
    ) then
        // Set the device's partition ID to be <pid>
        var dev_state := ws.subjects.devs[dev_id];
        var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
        var new_drvs := ws.subjects.devs[dev_id := new_dev_state];
        
        // Construct k'.subjects
        var new_subjects := Subjects(ws.subjects.drvs, new_drvs);

        // Construct k'.objects
        var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;
        //// Clear the objects being activated (except the hardcoded TD)
        var toactive_hcoded_td_id := dev_state.hcoded_td_id;
        var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
        var temp_tds := ClearTDs(ws.objects.tds, toclear_td_ids);
        var temp_fds := ClearFDs(ws.objects.fds, fds_owned_by_dev);
        var temp_dos := ClearDOs(ws.objects.dos, dos_owned_by_dev);
        //// Modify the PID of these objects
        var tds' := SetTDsPIDs(temp_tds, tds_owned_by_dev, pid);
        var fds' := SetFDsPIDs(temp_fds, fds_owned_by_dev, pid);
        var dos' := SetDOsPIDs(temp_dos, dos_owned_by_dev, pid);
        var new_objects := Objects(tds', fds', dos');

        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);

        var ws_d := true;

        // Call underlying functions to activate ephemeral devices
        if(Edev_Activate(DMStateToState(ws), dev_id)) then
            (ws', ws_d)
        else
            (ws, false)
    else
       (ws, false)
}




//******** ExternalObjsActivate ********//
function method DM_ExternalObjsActivateToGreenPartition_InnerFunc(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be activated
    green_pid:Partition_ID // ID of the partition to activate the objects into
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires td_ids <= MapGetKeys(ws.objects.tds)
    requires fd_ids <= MapGetKeys(ws.objects.fds)
    requires do_ids <= MapGetKeys(ws.objects.dos)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects 

    requires green_pid != NULL
    requires green_pid != ws.red_pid
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    if((forall td_id :: td_id in td_ids ==> DM_ObjPID(ws.objects, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> DM_ObjPID(ws.objects, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> DM_ObjPID(ws.objects, do_id.oid) == NULL) &&
           green_pid in ws.pids
    ) then
            // Construct ws'.objects
            // Clear the objects being activated
            var temp_tds := ClearTDs(ws.objects.tds, td_ids);
            var temp_fds := ClearFDs(ws.objects.fds, fd_ids);
            var temp_dos := ClearDOs(ws.objects.dos, do_ids);

            // Modify the PID of these objects
            var tds' := SetTDsPIDs(temp_tds, td_ids, green_pid);
            var fds' := SetFDsPIDs(temp_fds, fd_ids, green_pid);
            var dos' := SetDOsPIDs(temp_dos, do_ids, green_pid);
            var new_objects := Objects(tds', fds', dos');

            var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
            var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}




//******** DrvDeactivate ********//
function method DM_GreenDrvDeactivate_InnerFunc(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    var todeactivate_td_ids := ws.subjects.drvs[drv_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.drvs[drv_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.drvs[drv_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, drv_sid);

    if( DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid)
            // Ensure no other green TD in the same partition with the driver 
            // has transfers to any objects of the driver
      ) then
        // Set the driver's partition ID to be NULL
        var drv_state := ws.subjects.drvs[drv_id];
        var new_drv_state := Drv_State(NULL, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
        var new_drvs := ws.subjects.drvs[drv_id := new_drv_state];
        
        // Construct ws'.subjects
        var new_subjects := Subjects(new_drvs, ws.subjects.devs);

        // Construct ws'.objects
        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;
        //// Modify the PID of these objects
        var tds' := SetTDsPIDs(ws.objects.tds, tds_owned_by_drv, NULL);
        var fds' := SetFDsPIDs(ws.objects.fds, fds_owned_by_drv, NULL);
        var dos' := SetDOsPIDs(ws.objects.dos, dos_owned_by_drv, NULL);
        var new_objects := Objects(tds', fds', dos');
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}




//******** DevDeactivate ********//
function method DM_DevDeactivate_InnerFunc(
    ws:DM_State, 
    dev_sid:Subject_ID // ID of the device to be deactivated
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active
    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid 
                ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, Dev_ID(dev_sid))
        // Requirement: If the device is in red, then no other red device has 
        // transfers to any objects of the device to be deactivated
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    
    var todeactivate_td_ids := ws.subjects.devs[dev_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.devs[dev_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.devs[dev_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, dev_sid);
    
    if( (DM_SubjPID(ws.subjects, dev_sid) != NULL && DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid
            ==> DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
                    todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid))
                    // Ensure no other green TD in the same partition with the driver 
                    // has transfers to any objects of the driver
    ) then
        // Set the device's partition ID to be <pid>
        var dev_state := ws.subjects.devs[dev_id];
        var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
        var new_devs := ws.subjects.devs[dev_id := new_dev_state];
        
        // Construct ws'.subjects
        var new_subjects := Subjects(ws.subjects.drvs, new_devs);

        // Construct ws'.objects
        var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;
        //// Modify the PID of these objects
        var tds' := SetTDsPIDs(ws.objects.tds, tds_owned_by_dev, NULL);
        var fds' := SetFDsPIDs(ws.objects.fds, fds_owned_by_dev, NULL);
        var dos' := SetDOsPIDs(ws.objects.dos, dos_owned_by_drv, NULL);
        var new_objects := Objects(tds', fds', dos');
        
        var ws' := DM_State(new_subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        // Call underlying functions to deactivate ephemeral devices
        if(Edev_Deactivate(DMStateToState(ws), dev_id)) then
            (ws', ws_d)
        else
            (ws, false)
    else
       (ws, false)
}




//******** ExternalObjsDeactivate ********//
function method DM_GreenExternalObjsDeactivate_InnerFunc(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    green_pid:Partition_ID // The green partition that holds these objects
) : (result:(DM_State, bool))
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires td_ids <= MapGetKeys(ws.objects.tds)
    requires fd_ids <= MapGetKeys(ws.objects.fds)
    requires do_ids <= MapGetKeys(ws.objects.dos)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: no subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires forall id :: id in td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
        // Requirement: The objects must be in the same green partition
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var todeactivate_td_ids := td_ids;
    var todeactivate_fd_ids := fd_ids;
    var todeactivate_do_ids := do_ids;

    if( DM_Chk_SubjObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivatedInSamePartition(ws, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid)
            // Ensure no other green TD in the same partition with the driver 
            // has transfers to any objects of the driver
      ) then
        // Construct ws'.objects
        //// Modify the PID of these objects
        var tds' := SetTDsPIDs(ws.objects.tds, td_ids, NULL);
        var fds' := SetFDsPIDs(ws.objects.fds, fd_ids, NULL);
        var dos' := SetDOsPIDs(ws.objects.dos, do_ids, NULL);
        var new_objects := Objects(tds', fds', dos');
        
        var ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        var ws_d := true;

        (ws', ws_d)
    else
        (ws, false)
}