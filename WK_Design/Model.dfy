include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"
include "Utils.dfy"
include "SecurityProperties.dfy"

//******** Wimpy Kernel Operations ********//
// Corresponding to DM_RedDrvRead in the detailed model
method WS_OSDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_OSDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    t := DM_Trace(ws, [op]);
    ws', ws_d, real_td_id_val_map := DM_RedDrvRead(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_OSDrvRead_ProvePWSOpsProperties(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
}

// Corresponding to DM_GreenDrvRead in the detailed model
method WS_WimpDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_WimpDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDrvRead(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_WimpDrvRead_ProvePWSOpsProperties(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
}

// Corresponding to DM_DevRead in the detailed model
method WS_DevRead(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_DevRead_Op(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_DevRead(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_DevRead_ProvePWSOpsProperties(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d);
}

// Corresponding to DM_RedDrvWrite in the detailed model
method WS_OSDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_OSDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d, real_td_id_val_map := DM_RedDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_OSDrvWrite_ProvePWSOpsProperties(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Corresponding to DM_GreenDrvWrite in the detailed model
method WS_WimpDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_WimpDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_WimpDrvWrite_ProvePWSOpsProperties(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Corresponding to DM_RedDevWrite in the detailed model
method WS_OSDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
        // Properties needed by the following properties
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_OSDrvWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_RedDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_OSDevWrite_ProvePWSOpsProperties(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Corresponding to DM_GreenDevWrite in the detailed model
method WS_WimpDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

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

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)
        // Properties needed by the following property
    ensures P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the device

    ensures t.ws0 == ws
    ensures DM_IsValidTrace(t)
    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WS_WimpDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var op := DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    t := DM_Trace(ws, [op]);
    ws', ws_d := DM_GreenDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

    if(ws_d)
    {
        Lemma_DM_CalcNewStates_OneDMOp_Property(ws, op, ws');
    }
    else
    {
        assert DM_CalcNewStates(t) == [ws, ws];
    }

    Lemma_WimpDevWrite_ProvePWSOpsProperties(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d);
}

// Create an empty wimp partition 
method WK_WimpDrvsDevs_Registration_CreatePartition(
    ws:DM_State
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool, green_pid:Partition_ID)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_EmptyPartitionCreateOp(green_pid)]
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws_d == true ==> green_pid != NULL
    ensures ws_d == true ==> green_pid != ws.red_pid
    ensures ws_d == true ==> green_pid !in ws.pids 
    ensures ws_d == true ==> green_pid in ws'.pids
        // Property: If returns true, then create a new wimp (green) partition

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WK_WimpDrvsDevs_Registration_CreatePartition_Op())
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var last_ws:DM_State, new_last_ws:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;
    var new_pid := GetNewPartitionID(ws);

    // Create partition
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_EmptyPartitionCreateOp(new_pid)]);
    new_last_ws, d := DM_EmptyPartitionCreate(ws, new_pid);
    if(!d)
    { return DM_Trace(ws, []), ws, false, ws.red_pid;}
    assert DM_IsValidTrace(t1);
    assert new_last_ws == SeqLastElem(DM_CalcNewStates(t1));
    assert P_DMState_UnchangedStateVarsAndFields(ws, new_last_ws);
    last_ws := new_last_ws;

    ws' := last_ws;
    t := t1;
    ws_d := true;
    green_pid := new_pid;

    Lemma_WimpDrvsDevs_Registration_CreatePartition_ProvePWSOpsProperties(ws, t, ws', ws_d);
}

// Move devices, and activate drivers and external objects into the given 
// wimp partition 
method WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires to_deactivate_dev_id in ws.subjects.devs
    requires DM_SubjPID(ws.subjects, to_deactivate_dev_id.sid) == ws.red_pid
    requires P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, to_deactivate_dev_id)
        // Requirement: For the device to be deactivated

    requires forall i, j :: 0 <= i < |to_assign_drv_ids| && 0 <= j < |to_assign_drv_ids|
                ==> (i == j <==> to_assign_drv_ids[i] == to_assign_drv_ids[j])
        // Requirement: No duplicate device ID in <to_assign_drv_ids>
    requires forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    requires forall id :: id in to_assign_drv_ids ==> id in ws.subjects.drvs
    requires |to_assign_drv_ids| >= 0
    requires forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs
    requires |to_assign_dev_ids| >= 0

    requires to_assign_external_td_ids <= MapGetKeys(ws.objects.tds)
    requires to_assign_external_fd_ids <= MapGetKeys(ws.objects.fds)
    requires to_assign_external_do_ids <= MapGetKeys(ws.objects.dos)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: We have already create a green partition

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_DevDeactivateOp(to_deactivate_dev_id.sid)] + DevActivateMulti_ToTraceOps(to_assign_dev_ids, green_pid) +
                                    WimpDrvActivateMulti_ToTraceOps(to_assign_drv_ids, green_pid) + 
                                    [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)]
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Deactivate device
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_DevDeactivateOp(to_deactivate_dev_id.sid)]);
    ws2, d := DM_DevDeactivate(ws, to_deactivate_dev_id.sid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert ws2 == SeqLastElem(DM_CalcNewStates(t1));
    assert P_DMState_UnchangedStateVarsAndFields(ws, ws2);

    // Activate devices
    ghost var t2:DM_Trace;
    ghost var t2_detailed:DM_Trace_Detailed;
    t2, t2_detailed, ws3, d := WS_DevActivate_Multi(ws2, to_assign_dev_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    ghost var t1_t2 := ValidDMTrace_Concat(t1, t2);
    Lemma_WS_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t2_detailed.states, ws2, ws3);
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws2, ws3);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws2, ws3, t1, t2);
    assert ws3 == SeqLastElem(DM_CalcNewStates(t1_t2));

    // Activate drivers
    ghost var t3:DM_Trace;
    ghost var t3_detailed:DM_Trace_Detailed;
    t3, t3_detailed, ws4, d := WS_WimpDrvActivate_Multi(ws3, to_assign_drv_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    Lemma_WS_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t3_detailed.states, ws3, ws4);
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws3, ws4);
    
    // Activate external objects
    assert DM_IsValidState(ws4) && DM_IsSecureState(ws4);
    assert P_DMState_UnchangedStateVarsAndFields(ws, ws4);
    Lemma_ExternalObjsActivateDeactivate_ProvePreConditions(ws, ws4, to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids);

    var op4 := DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);
    ghost var t4:DM_Trace := DM_Trace(ws4, [op4]);
    ws5, d := DM_ExternalObjsActivateToGreenPartition(ws4, to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
            to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    Lemma_WK_WimpDrvsDevs_Registration_ProveValidTrace_AfterActivateExternalObjsToGreenPartition(
        ws4, t4, to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);
    assert DM_IsValidTrace(t4);
    ghost var t3_t4 := ValidDMTrace_Concat(t3, t4);
    Lemma_DM_CalcNewStates_OneDMOp_Property(ws4, op4, ws5);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws3, ws4, ws5, t3, t4);
    assert ws5 == SeqLastElem(DM_CalcNewStates(t3_t4));

    ws' := ws5;
    t := ValidDMTrace_Concat(t1_t2, t3_t4);
    ws_d := true;

    // Prove property 2
    var seq1 := [DM_DevDeactivateOp(to_deactivate_dev_id.sid)];
    var seq2 := DevActivateMulti_ToTraceOps(to_assign_dev_ids, green_pid);
    var seq3 := WimpDrvActivateMulti_ToTraceOps(to_assign_drv_ids, green_pid);
    var seq4 := [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)];

    Lemma_DMTraceConcat_IsConcatOfDMOps(t1_t2, t1, t2, seq1, seq2);
    Lemma_DMTraceConcat_IsConcatOfDMOps(t3_t4, t3, t4, seq3, seq4);
    assert t1_t2.ops == seq1 + seq2;
    assert t3_t4.ops == seq3 + seq4;

    Lemma_ConcatFourOpSeq(t1_t2, t3_t4, t, seq1, seq2, seq3, seq4); 
    assert t.ops == seq1 + seq2 + seq3 + seq4;

    // Prove ws' == SeqLastElem(DM_CalcNewStates(t))
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws3, ws', t1_t2, t3_t4);
    assert ws' == SeqLastElem(DM_CalcNewStates(t));
    
    // Prove DM_IsSecureOps(ws, ws')
    Lemma_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
        ws, ws2, ws3, ws4, ws5,
        to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
        to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid);

    Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
        to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, t, ws', ws_d);
}

// Move devices, and deactivate wimp drivers and external objects out of the 
// given wimp partition, and then destroy the partition
// (needs 60s to verify)
method WK_WimpDrvsDevs_Unregistration(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |to_deactivate_drv_ids| && 0 <= j < |to_deactivate_drv_ids|
                ==> (i == j <==> to_deactivate_drv_ids[i] == to_deactivate_drv_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_drv_ids>
    requires forall i, j :: 0 <= i < |to_deactivate_dev_ids| && 0 <= j < |to_deactivate_dev_ids|
                ==> (i == j <==> to_deactivate_dev_ids[i] == to_deactivate_dev_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_dev_ids>
    requires forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs
    requires |to_deactivate_drv_ids| >= 0
    requires forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs
    requires |to_deactivate_dev_ids| >= 0

    requires forall id :: id in to_deactivate_drv_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
    requires forall id :: id in to_deactivate_dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
        // Requirement: Drivers and devices to be deactivated must be from the 
        // green partition

    requires forall i, j :: 0 <= i < |devs_to_activate_in_red| && 0 <= j < |devs_to_activate_in_red|
                ==> (i == j <==> devs_to_activate_in_red[i] == devs_to_activate_in_red[j])
        // Requirement: No duplicate device ID in <devs_to_activate_in_red>
    requires forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs
    requires |devs_to_activate_in_red| >= 0
        // Requirement: Devices to be activated in the red partition must be 
        // existing devices

    requires to_deactivate_external_td_ids <= MapGetKeys(ws.objects.tds)
    requires to_deactivate_external_fd_ids <= MapGetKeys(ws.objects.fds)
    requires to_deactivate_external_do_ids <= MapGetKeys(ws.objects.dos)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
    requires forall id :: id in to_deactivate_external_td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
        // Requirement: External objects to be deactivated must be from the 
        // green partition

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: A green partition to be destroyed

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws') 

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)] +
                                WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids) +
                                GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids) +
                                DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid) +
                                [DM_EmptyPartitionDestroyOp(green_pid)]
                                
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures P_WS_OpsProperties(ws, WK_WimpDrvsDevs_Unregistration_Op(to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid))
        // Property: The implemetation of this operation fulfills the specification of P_WS_OpsProperties
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Call WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs
    ghost var t1:DM_Trace;
    t1, ws2, d := WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                    to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
            to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
            green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert ws2 == SeqLastElem(DM_CalcNewStates(t1));

    // Call WK_WimpDrvsDevs_UnRegistration_DestroyPartition
    ghost var t2:DM_Trace;
    t2, ws3, d := WK_WimpDrvsDevs_UnRegistration_DestroyPartition(ws2, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
            to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
            green_pid, t, ws', ws_d);
        return t, ws', ws_d;
    }
    ghost var t1_t2 := ValidDMTrace_Concat(t1, t2);
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws2, ws3);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws2, ws3, t1, t2);
    assert ws3 == SeqLastElem(DM_CalcNewStates(t1_t2));

    ws' := ws3;
    t := t1_t2;
    ws_d := true;
    
    Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
        to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
        green_pid, t, ws', ws_d);
}




//******** Utility functions ********//
// Get the partition ID to be associated with the newly created partition
method {:axiom} GetNewPartitionID(ws:DM_State) returns (new_pid:Partition_ID)
    ensures new_pid != NULL
    ensures new_pid != ws.red_pid
    ensures new_pid !in ws.pids




//******** Utility Operations ********//
// (needs 70s to verify)
method WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |to_deactivate_drv_ids| && 0 <= j < |to_deactivate_drv_ids|
                ==> (i == j <==> to_deactivate_drv_ids[i] == to_deactivate_drv_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_drv_ids>
    requires forall i, j :: 0 <= i < |to_deactivate_dev_ids| && 0 <= j < |to_deactivate_dev_ids|
                ==> (i == j <==> to_deactivate_dev_ids[i] == to_deactivate_dev_ids[j])
        // Requirement: No duplicate device ID in <to_deactivate_dev_ids>
    requires forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs
    requires |to_deactivate_drv_ids| >= 0
    requires forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs
    requires |to_deactivate_dev_ids| >= 0

    requires forall id :: id in to_deactivate_drv_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
    requires forall id :: id in to_deactivate_dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid
        // Requirement: Drivers and devices to be deactivated must be from the 
        // green partition

    requires forall i, j :: 0 <= i < |devs_to_activate_in_red| && 0 <= j < |devs_to_activate_in_red|
                ==> (i == j <==> devs_to_activate_in_red[i] == devs_to_activate_in_red[j])
        // Requirement: No duplicate device ID in <devs_to_activate_in_red>
    requires forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs
    requires |devs_to_activate_in_red| >= 0
        // Requirement: Devices to be activated in the red partition must be 
        // existing devices

    requires to_deactivate_external_td_ids <= MapGetKeys(ws.objects.tds)
    requires to_deactivate_external_fd_ids <= MapGetKeys(ws.objects.fds)
    requires to_deactivate_external_do_ids <= MapGetKeys(ws.objects.dos)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
    requires forall id :: id in to_deactivate_external_td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
    requires forall id :: id in to_deactivate_external_do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid
        // Requirement: External objects to be deactivated must be from the 
        // green partition

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: A green partition to be destroyed

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws') 

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)] +
                                WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids) +
                                GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids) +
                                DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid)
        // Property 2: <t> is the desired trace
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures ws'.pids == ws.pids
        // Utility properties needed by <WK_WimpDrvsDevs_Unregistration>
{
    var ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Deactivate external objects
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)]);
    ws2, d := DM_GreenExternalObjsDeactivate(ws, to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert ws2 == SeqLastElem(DM_CalcNewStates(t1));
    assert ws2.pids == ws.pids;

    // Deactivate drivers
    ghost var t2:DM_Trace;
    ghost var t2_detailed:DM_Trace_Detailed;
    t2, t2_detailed, ws3, d := WS_WimpDrvDeactivate_Multi(ws2, to_deactivate_drv_ids);
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    ghost var t1_t2 := ValidDMTrace_Concat(t1, t2);
    Lemma_WS_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t2_detailed.states, ws2, ws3);
    assert ws3.pids == ws2.pids; 
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws2, ws3);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws2, ws3, t1, t2);
    assert ws3 == SeqLastElem(DM_CalcNewStates(t1_t2));

    // Deactivate devices
    ghost var t3:DM_Trace;
    ghost var t3_detailed:DM_Trace_Detailed;
    t3, t3_detailed, ws4, d := WS_DevDeactivate_FromGreen_Multi(ws3, to_deactivate_dev_ids); 
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    assert SeqLastElem(t3_detailed.states) == ws4;
    assert t3_detailed.states[|t3_detailed.states|-1] == ws4;
    Lemma_WS_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t3_detailed.states, ws3, ws4);
    assert ws4.pids == ws3.pids;
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws3, ws4);

    // Activate devices
    ghost var t4:DM_Trace;
    ghost var t4_detailed:DM_Trace_Detailed;
    t4, t4_detailed, ws5, d := WS_DevActivate_Multi(ws4, devs_to_activate_in_red, ws.red_pid); 
    if(!d)
    {
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        Lemma_DM_CalcNewStates_NoDMOp_Property(ws);
        
        return t, ws', ws_d;
    }
    ghost var t3_t4 := ValidDMTrace_Concat(t3, t4);
    assert SeqLastElem(t4_detailed.states) == ws5;
    assert t4_detailed.states[|t4_detailed.states|-1] == ws5;
    Lemma_WS_UnchangedStateVars_ProveSameSubjObjIDsAndRedPID(t4_detailed.states, ws4, ws5);
    assert ws5.pids == ws4.pids;
    Lemma_P_DMState_UnchangedStateVarsAndFields_Transitivity(ws, ws4, ws5);
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws3, ws4, ws5, t3, t4);
    assert ws5 == SeqLastElem(DM_CalcNewStates(t3_t4));

    ws' := ws5;
    t := ValidDMTrace_Concat(t1_t2, t3_t4);
    ws_d := true;

    // Prove property 2
    var seq1 := [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)];
    var seq2 := WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids);
    var seq3 := GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids);
    var seq4 := DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid);

    Lemma_DMTraceConcat_IsConcatOfDMOps(t1_t2, t1, t2, seq1, seq2);
    Lemma_DMTraceConcat_IsConcatOfDMOps(t3_t4, t3, t4, seq3, seq4);
    assert t1_t2.ops == seq1 + seq2;
    assert t3_t4.ops == seq3 + seq4;
    Lemma_ConcatFourOpSeq(t1_t2, t3_t4, t, seq1, seq2, seq3, seq4); 
    assert t.ops == seq1 + seq2 + seq3 + seq4;

    // Prove ws' == SeqLastElem(DM_CalcNewStates(t))
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(ws, ws3, ws', t1_t2, t3_t4);
    assert ws' == SeqLastElem(DM_CalcNewStates(t));

    // Prove DM_IsSecureOps(ws, ws')
    Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
        ws, ws2, ws3, ws4, ws5,
        to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red, 
        to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
        green_pid);
        
    // Prove ws'.pids == ws.pids
    assert ws2.pids == ws.pids;
    assert ws3.pids == ws2.pids;
    assert ws4.pids == ws3.pids;
    assert ws5.pids == ws4.pids;
    assert ws' == ws5;
    Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProvePIDsAreUnchanged(
        ws, ws2, ws3, ws4, ws5, ws');
    assert ws'.pids == ws.pids;
}

method WK_WimpDrvsDevs_UnRegistration_DestroyPartition(
    ws:DM_State, green_pid:Partition_ID
) returns (ghost t:DM_Trace, ws':DM_State, ws_d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: A green partition to be destroyed

    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws_d == true ==> t.ws0 == ws
    ensures ws_d == true ==> t.ops == [DM_EmptyPartitionDestroyOp(green_pid)]
    ensures ws_d == true ==> DM_IsValidTrace(t)

    ensures !ws_d ==> t == DM_Trace(ws, [])
    ensures !ws_d ==> ws' == ws
    ensures !ws_d ==> DM_IsValidTrace(t)
        // Property: If returns false, then stays at the same state

    ensures ws_d == true ==> green_pid !in ws'.pids
        // Property: If returns true, then destroy the green partition

    ensures ws' == SeqLastElem(DM_CalcNewStates(t))
        // Property: The corresponding DM_Trace from ws to ws' is valid
    ensures ws'.subjects == ws.subjects
    ensures ws'.objects == ws.objects
        // Utility properties needed by <WK_WimpDrvsDevs_Unregistration>
{
    var last_ws:DM_State, new_last_ws:DM_State;
    var ws_seq:seq<DM_State>;
    var d:bool;

    // Destroy partition
    ghost var t1:DM_Trace := DM_Trace(ws, [DM_EmptyPartitionDestroyOp(green_pid)]);
    new_last_ws, d := DM_EmptyPartitionDestroy(ws, green_pid);
    if(!d)
    { 
        t, ws', ws_d := DM_Trace(ws, []), ws, false;
        return t, ws', ws_d;
    }
    assert DM_IsValidTrace(t1);
    assert new_last_ws == SeqLastElem(DM_CalcNewStates(t1));
    assert P_DMState_UnchangedStateVarsAndFields(ws, new_last_ws);
    last_ws := new_last_ws;

    ws' := last_ws;
    t := t1;
    ws_d := true;
}




//******** Utility Lemmas ********//
lemma Lemma_OSDrvRead_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_OSDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires WS_OSDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_OSDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvRead_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_WimpDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires WS_WimpDrvRead_PostConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_WimpDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevRead_ProvePWSOpsProperties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>, // Map from destination DO to source DO
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires WS_DevRead_PostConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_DevRead_Op(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OSDrvWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_OSDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WS_OSDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_OSDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_WimpDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WS_WimpDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_WimpDrvWrite_Op(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OSDevWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_OSDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WS_OSDevWrite_PostConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_OSDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDevWrite_ProvePWSOpsProperties(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>, // IDs of DOs, and values to be written
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_WimpDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires WS_WimpDevWrite_PostConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WS_WimpDevWrite_Op(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvsDevs_Registration_CreatePartition_ProvePWSOpsProperties(
    ws:DM_State,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)
    requires WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(ws, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WK_WimpDrvsDevs_Registration_CreatePartition_Op())
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProvePWSOpsProperties(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids,
                green_pid)
    requires WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids,
                green_pid, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WimpDrvsDevs_Unregistration_ProvePWSOpsProperties(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Unregistration_PreConditions(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
                green_pid)
    requires WK_WimpDrvsDevs_Unregistration_PostConditions(ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
                green_pid, t, ws', ws_d)
    
    ensures P_WS_OpsProperties(ws, WK_WimpDrvsDevs_Unregistration_Op(to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProvePIDsAreUnchanged(
    ws:DM_State, ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State, ws':DM_State
)
    requires ws2.pids == ws.pids
    requires ws3.pids == ws2.pids
    requires ws4.pids == ws3.pids
    requires ws5.pids == ws4.pids
    requires ws' == ws5
    
    ensures ws'.pids == ws.pids
{
    // Dafny can automatically prove this lemma
}