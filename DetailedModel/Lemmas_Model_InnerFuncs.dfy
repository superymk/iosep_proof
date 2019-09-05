include "SecurityProperties.dfy"


lemma Lemma_DM_RedDrvRead_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    ws':DM_State, ws_d:bool
)
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
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs
        // Requirement: Read objects must not be any hardcoded TDs

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    requires (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures P_DM_OpsProperties_RedDrvReadOp(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    assert DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    assert DM_RedDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
    assert (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    assert P_DM_OpsProperties_RedDrvReadOp(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
}

lemma Lemma_DM_RedDrvRead_ProveDM_CalcNewState(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    ws':DM_State, ws_d:bool
)
    requires DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    
    requires (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_RedDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d)

    ensures DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_GreenDrvRead_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>,  // Map from destination DO to source DO
    ws':DM_State, ws_d:bool
)
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
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs
        // Requirement: Read objects must not be any hardcoded TDs

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    requires (ws', ws_d) == DM_GreenDrvReadRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures P_DM_OpsProperties_GreenDrvReadOp(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    assert DM_GreenDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    assert DM_GreenDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
    assert (ws', ws_d) == DM_GreenDrvReadRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    assert P_DM_OpsProperties_GreenDrvReadOp(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
}

lemma Lemma_DM_GreenDrvRead_ProveDM_CalcNewState(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    ws':DM_State, ws_d:bool
)
    requires DM_GreenDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    
    requires (ws', ws_d) == DM_GreenDrvReadRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_GreenDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d)

    ensures DM_CalcNewState(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevRead_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>,  // Map from destination DO to source DO
    ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: Objects in parameters must be in the same partition with 
        // the device

    requires (ws', ws_d) == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures P_DM_OpsProperties_DevReadOp(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    assert DM_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    assert DM_DevRead_PostConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
    assert (ws', ws_d) == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    assert P_DM_OpsProperties_DevReadOp(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
}

lemma Lemma_DM_RedDrvWrite_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>,  // IDs of DOs, and values to be written
    ws':DM_State, ws_d:bool
)
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

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    requires ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1
    requires ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2

    ensures P_DM_OpsProperties_RedDrvWriteOp(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    assert DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_RedDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
    assert ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1;
    assert ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2;
    assert P_DM_OpsProperties_RedDrvWriteOp(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
}

lemma Lemma_DM_GreenDrvWrite_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>,  // IDs of DOs, and values to be written
    ws':DM_State, ws_d:bool
)
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

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    requires (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)

    ensures P_DM_OpsProperties_GreenDrvWriteOp(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    assert DM_GreenDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_GreenDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
    assert (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert P_DM_OpsProperties_GreenDrvWriteOp(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
}

lemma Lemma_DM_RedDevWrite_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>,  // IDs of DOs, and values to be written
    ws':DM_State, ws_d:bool
)
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

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
        // Properties needed by the following property
    requires P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device

    requires (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)

    ensures P_DM_OpsProperties_RedDevWriteOp(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    assert DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_RedDevWrite_PostConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
    assert (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert P_DM_OpsProperties_RedDevWriteOp(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
}

lemma Lemma_DM_GreenDevWrite_ProvePreConditionsOfDM_CalcNewState(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>,  // IDs of DOs, and values to be written
    ws':DM_State, ws_d:bool
)
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

    requires ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    requires DM_IsValidState(ws') && DM_IsSecureState(ws')
    requires DM_IsSecureOps(ws, ws')
                    
    requires IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
        // Properties needed by the following property
    requires P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device

    requires (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)

    ensures P_DM_OpsProperties_GreenDevWriteOp(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    assert DM_GreenDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert DM_GreenDevWrite_PostConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
    assert (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert P_DM_OpsProperties_GreenDevWriteOp(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
}