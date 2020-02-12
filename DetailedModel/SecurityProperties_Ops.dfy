include "Syntax.dfy"
include "Properties_SecureDMState.dfy"
include "Utils.dfy"
include "Model_Ops_Predicates.dfy"
include "Model_InnerFuncs.dfy"

datatype DM_Op   =  DM_RedDrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) | 
                    DM_GreenDrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) | 
                    DM_DevReadOp(dev_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) |
                    DM_RedDrvWriteOp(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    DM_GreenDrvWriteOp(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    DM_RedDevWriteOp(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    DM_GreenDevWriteOp(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |

                    DM_EmptyPartitionCreateOp(new_pid:Partition_ID) | 
                    DM_EmptyPartitionDestroyOp(pid:Partition_ID) |
                    DM_DrvActivateToGreenPartitionOp(drv_sid:Subject_ID, green_pid:Partition_ID) |
                    DM_GreenDrvDeactivateOp(drv_sid:Subject_ID) | 
                    DM_DevActivateOp(dev_sid:Subject_ID, pid:Partition_ID) |
                    DM_DevDeactivateOp(dev_sid:Subject_ID) |
                    DM_ExternalObjsActivateToGreenPartitionOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID) | 
                    DM_GreenExternalObjsDeactivateOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID)

datatype DM_Trace = DM_Trace(ws0:DM_State, ops:seq<DM_Op>)




//******** Property of Each Operation ********//
predicate P_DM_OpsProperties_RedDrvReadOp(ws:DM_State, op:DM_Op)
    requires op.DM_RedDrvReadOp?
{
    DM_RedDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists ws':DM_State, ws_d:bool :: DM_RedDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, ws', ws_d) &&
                                (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src))
}

predicate P_DM_OpsProperties_GreenDrvReadOp(ws:DM_State, op:DM_Op)
    requires op.DM_GreenDrvReadOp?
{
    DM_GreenDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists ws':DM_State, ws_d:bool :: DM_GreenDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, ws', ws_d) &&
                                (ws', ws_d) == DM_GreenDrvReadRead_InnerFunc(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src))
}

predicate P_DM_OpsProperties_DevReadOp(ws:DM_State, op:DM_Op)
    requires op.DM_DevReadOp?
{
    DM_DevRead_PreConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists ws':DM_State, ws_d:bool :: DM_DevRead_PostConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, ws', ws_d) &&
                                (ws', ws_d) == DM_DevRead_InnerFunc(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src))
}

predicate P_DM_OpsProperties_RedDrvWriteOp(ws:DM_State, op:DM_Op)
    requires op.DM_RedDrvWriteOp?
{
    DM_RedDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists ws':DM_State, ws_d:bool :: DM_RedDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                                ws' == DM_RedDrvWrite_InnerFunc(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map).1 &&
                                ws_d == DM_RedDrvWrite_InnerFunc(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map).2)
}

predicate P_DM_OpsProperties_GreenDrvWriteOp(ws:DM_State, op:DM_Op)
    requires op.DM_GreenDrvWriteOp?
{
    DM_GreenDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists ws':DM_State, ws_d:bool :: DM_GreenDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                                (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map))
}

predicate P_DM_OpsProperties_RedDevWriteOp(ws:DM_State, op:DM_Op)
    requires op.DM_RedDevWriteOp?
{
    DM_RedDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists ws':DM_State, ws_d:bool :: DM_RedDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                                (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map))
}

predicate P_DM_OpsProperties_GreenDevWriteOp(ws:DM_State, op:DM_Op)
    requires op.DM_GreenDevWriteOp?
{
    DM_GreenDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists ws':DM_State, ws_d:bool :: DM_GreenDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, ws', ws_d) &&
                                (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map))
}



predicate P_DM_OpsProperties_EmptyPartitionCreateOp(ws:DM_State, op:DM_Op)
    requires op.DM_EmptyPartitionCreateOp?
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws))
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, op.new_pid))
}

predicate P_DM_OpsProperties_EmptyPartitionDestroyOp(ws:DM_State, op:DM_Op)
    requires op.DM_EmptyPartitionDestroyOp?
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws))
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, op.pid))
}

predicate P_DM_OpsProperties_DrvActivateToGreenPartitionOp(ws:DM_State, op:DM_Op)
    requires op.DM_DrvActivateToGreenPartitionOp?
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Drv_ID(op.drv_sid) in ws.subjects.drvs &&
            op.green_pid != NULL &&
            op.green_pid != ws.red_pid)
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, op.drv_sid, op.green_pid))
}

predicate P_DM_OpsProperties_GreenDrvDeactivateOp(ws:DM_State, op:DM_Op)
    requires op.DM_GreenDrvDeactivateOp?
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Drv_ID(op.drv_sid) in ws.subjects.drvs &&
            DM_SubjPID(ws.subjects, op.drv_sid) != NULL &&
            DM_SubjPID(ws.subjects, op.drv_sid) != ws.red_pid)
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, op.drv_sid))
}

predicate P_DM_OpsProperties_DevActivateOp(ws:DM_State, op:DM_Op)
    requires op.DM_DevActivateOp?
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws) &&
            Dev_ID(op.dev_sid) in ws.subjects.devs &&
            op.pid != NULL)
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_DevActivate_InnerFunc(ws, op.dev_sid, op.pid))
}

predicate P_DM_OpsProperties_DevDeactivateOp(ws:DM_State, op:DM_Op)
    requires op.DM_DevDeactivateOp?
{
    DM_DevDeactivate_PreConditions(ws, op.dev_sid)
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, op.dev_sid))
}

predicate P_DM_OpsProperties_ExternalObjsActivateToGreenPartitionOp(ws:DM_State, op:DM_Op)
    requires op.DM_ExternalObjsActivateToGreenPartitionOp?
{
    DM_ExternalObjsActivateToGreenPartition_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid)
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) && 
                            (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid))
}

predicate P_DM_OpsProperties_GreenExternalObjsDeactivateOp(ws:DM_State, op:DM_Op)
    requires op.DM_GreenExternalObjsDeactivateOp?
{
    DM_GreenExternalObjsDeactivate_PreConditions(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid)
    ==> (exists ws':DM_State, ws_d:bool :: DM_Common_PostConditions(ws, ws', ws_d) &&
                            (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, op.td_ids, op.fd_ids, op.do_ids, op.green_pid))
}




//******** PreConditions and PostConditions of Operations ********//
predicate DM_RedDrvRead_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>  
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))) &&
    (DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid) &&
        // Requirement: the driver is in a green partition

    (read_objs <= DM_AllObjsIDs(ws.objects)) &&
    (DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src) &&
        // Requirement: The driver does not write any hardcoded TDs
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs) &&
        // Requirement: Read objects must not be any hardcoded TDs

    (true)
}

predicate DM_RedDrvRead_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    ws':DM_State, ws_d:bool
)
    requires DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&

    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    (true)
}

predicate DM_GreenDrvRead_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>  
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))) &&
    (DM_SubjPID(ws.subjects, drv_sid) != NULL) &&
    (DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid) &&
        // Requirement: the driver is in a green partition

    (read_objs <= DM_AllObjsIDs(ws.objects)) &&
    (DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src) &&
        // Requirement: The driver does not write any hardcoded TDs
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs) &&
        // Requirement: Read objects must not be any hardcoded TDs

    (true)
}

predicate DM_GreenDrvRead_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    ws':DM_State, ws_d:bool
)
    requires DM_GreenDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    
    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    (true)
}

predicate DM_DevRead_PreConditions(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>  
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDevID(ws.subjects, Dev_ID(dev_sid))) &&
    (DM_SubjPID(ws.subjects, dev_sid) != NULL) &&
        // Requirement: the device is active

    (DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)) &&
    (DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&

    (true)
}

predicate DM_DevRead_PostConditions(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    ws':DM_State, ws_d:bool
)
    requires DM_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    
    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device

    (true)
}

predicate DM_RedDrvWrite_PreConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))) &&
    (DM_SubjPID(ws.subjects, drv_sid) == ws.red_pid) &&
        // Requirement: the driver is in the red partition

    ((forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)) &&
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map) &&
        // Requirement: The driver does not write any hardcoded TDs

    (true)
}

predicate DM_RedDrvWrite_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    ws':DM_State, ws_d:bool
)
    requires DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    
    (ws_d == true
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    (true)
}

predicate DM_GreenDrvWrite_PreConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDrvID(ws.subjects, Drv_ID(drv_sid))) &&
    (DM_SubjPID(ws.subjects, drv_sid) != NULL) &&
    (DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid) &&
        // Requirement: the driver is in the green partition

    ((forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)) &&
    (forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map) &&
        // Requirement: The driver does not write any hardcoded TDs

    (true)
}

predicate DM_GreenDrvWrite_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    ws':DM_State, ws_d:bool
)
    requires DM_GreenDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    
    (ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    (true)
}

predicate DM_RedDevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDevID(ws.subjects, Dev_ID(dev_sid))) &&
    (DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid) &&
        // Requirement: the device is in the red partition

    (forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])) &&
    (forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])) &&
    (forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])) &&

    (true)
}

predicate DM_RedDevWrite_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    ws':DM_State, ws_d:bool
)
    requires DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
                    
    (IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))) &&
    ((forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)) &&
        // Properties needed by the following properties
    (P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property: Objects in parameters must be in the same partition with 
        // the device

    (true)
}

predicate DM_GreenDevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (DM_IsDevID(ws.subjects, Dev_ID(dev_sid))) &&
    (DM_SubjPID(ws.subjects, dev_sid) != NULL) &&
    (DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid) &&
        // Requirement: the device must be in a green partition

    (forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(ws, dev_sid, td_id2, td_id_val_map[td_id2])) &&
    (forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(ws, dev_sid, fd_id2, fd_id_val_map[fd_id2])) &&
    (forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(ws, dev_sid, do_id2, do_id_val_map[do_id2])) &&

    (true)
}

predicate DM_GreenDevWrite_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    ws':DM_State, ws_d:bool
)
    requires DM_GreenDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
                    
    (IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))) &&
    ((forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)) &&
        // Properties needed by the following property
    (P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property: Objects in parameters must be in the same partition with 
        // the device

    (true)
}

predicate DM_Common_PostConditions(
    ws:DM_State, ws':DM_State, ws_d:bool
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&

    (true)
}

predicate DM_DevDeactivate_PreConditions(
    ws:DM_State, dev_sid:Subject_ID
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&
    (Dev_ID(dev_sid) in ws.subjects.devs) &&
    (DM_SubjPID(ws.subjects, dev_sid) != NULL) &&
        // Requirement: the device must be active
    (DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid 
                ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, Dev_ID(dev_sid))) &&
        // Requirement: If the device is in red, then no other red device has 
        // transfers to any objects of the device to be deactivated

    (true)
}

predicate DM_ExternalObjsActivateToGreenPartition_PreConditions(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (td_ids <= MapGetKeys(ws.objects.tds)) &&
    (fd_ids <= MapGetKeys(ws.objects.fds)) &&
    (do_ids <= MapGetKeys(ws.objects.dos)) &&

    (forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)) &&
        // Requirement: No subject owns these external objects 

    (green_pid != NULL) &&
    (green_pid != ws.red_pid) &&

    (true)
}

predicate DM_GreenExternalObjsDeactivate_PreConditions(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, green_pid:Partition_ID
)
{
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (td_ids <= MapGetKeys(ws.objects.tds)) &&
    (fd_ids <= MapGetKeys(ws.objects.fds)) &&
    (do_ids <= MapGetKeys(ws.objects.dos)) &&

    (forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)) &&
        // Requirement: no subject owns these external objects

    (green_pid != NULL) &&
    (green_pid != ws.red_pid) &&
    (forall id :: id in td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
    (forall id :: id in fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
    (forall id :: id in do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
        // Requirement: The objects must be in the same green partition

    (true)
}