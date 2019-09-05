include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"
include "Utils.dfy"

datatype WS_Op   =  WS_OSDrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) | 
                    WS_WimpDrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) |
                    WS_DevRead_Op(dev_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) |
                    WS_OSDrvWrite_Op(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WS_WimpDrvWrite_Op(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WS_OSDevWrite_Op(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    WS_WimpDevWrite_Op(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) | 

                    WK_WimpDrvsDevs_Registration_CreatePartition_Op() | 
                    WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
                        to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
                        green_pid:Partition_ID) |
                    WK_WimpDrvsDevs_Unregistration_Op(to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
                        to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
                        green_pid:Partition_ID)

datatype WS_Trace = WS_Trace(ws0:DM_State, ops:seq<WS_Op>)




//******** Property of Each Operation ********//
predicate P_WS_OSDrvRead_Op(ws:DM_State, op:WS_Op)
    requires op.WS_OSDrvReadOp?
{
    WS_OSDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_OSDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d))
}

predicate P_WS_WimpDrvRead_Op(ws:DM_State, op:WS_Op)
    requires op.WS_WimpDrvReadOp?
{
    WS_WimpDrvRead_PreConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_WimpDrvRead_PostConditions(ws, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d))
}

predicate P_WS_DevRead_Op(ws:DM_State, op:WS_Op)
    requires op.WS_DevRead_Op?
{
    WS_DevRead_PreConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_DevRead_PostConditions(ws, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, t, ws', ws_d))
}

predicate P_WS_OSDrvWrite_Op(ws:DM_State, op:WS_Op)
    requires op.WS_OSDrvWrite_Op?
{
    WS_OSDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_OSDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WS_WimpDrvWrite_Op(ws:DM_State, op:WS_Op)
    requires op.WS_WimpDrvWrite_Op?
{
    WS_WimpDrvWrite_PreConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_WimpDrvWrite_PostConditions(ws, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WS_OSDevWrite_Op(ws:DM_State, op:WS_Op)
    requires op.WS_OSDevWrite_Op?
{
    WS_OSDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_OSDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WS_WimpDevWrite_Op(ws:DM_State, op:WS_Op)
    requires op.WS_WimpDevWrite_Op?
{
    WS_WimpDevWrite_PreConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WS_WimpDevWrite_PostConditions(ws, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, t, ws', ws_d))
}

predicate P_WK_WimpDrvsDevs_Registration_CreatePartition_Op(ws:DM_State, op:WS_Op)
    requires op.WK_WimpDrvsDevs_Registration_CreatePartition_Op?
{
    WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(ws, t, ws', ws_d))
}

predicate P_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op(ws:DM_State, op:WS_Op)
    requires op.WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_Op?
{
    WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
                ws, op.to_deactivate_dev_id, op.to_assign_drv_ids, op.to_assign_dev_ids,
                op.to_assign_external_td_ids, op.to_assign_external_fd_ids, op.to_assign_external_do_ids, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(ws, 
                op.to_deactivate_dev_id, op.to_assign_drv_ids, op.to_assign_dev_ids,
                op.to_assign_external_td_ids, op.to_assign_external_fd_ids, op.to_assign_external_do_ids, op.green_pid, t, ws', ws_d))
}

predicate P_WK_WimpDrvsDevs_Unregistration_Op(ws:DM_State, op:WS_Op)
    requires op.WK_WimpDrvsDevs_Unregistration_Op?
{
    WK_WimpDrvsDevs_Unregistration_PreConditions(
                ws, op.to_deactivate_drv_ids, op.to_deactivate_dev_ids, op.devs_to_activate_in_red,
                op.to_deactivate_external_td_ids, op.to_deactivate_external_fd_ids, op.to_deactivate_external_do_ids, op.green_pid)
    ==> (exists t:DM_Trace, ws':DM_State, ws_d:bool :: WK_WimpDrvsDevs_Unregistration_PostConditions(ws, 
                op.to_deactivate_drv_ids, op.to_deactivate_dev_ids, op.devs_to_activate_in_red,
                op.to_deactivate_external_td_ids, op.to_deactivate_external_fd_ids, op.to_deactivate_external_do_ids, op.green_pid, t, ws', ws_d))
}




//******** PreConditions and PostConditions of Operations ********//
predicate WS_OSDrvRead_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_RedDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
}

predicate WS_OSDrvRead_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_OSDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WS_WimpDrvRead_PreConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_GreenDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
}

predicate WS_WimpDrvRead_PostConditions(
    ws:DM_State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_WimpDrvRead_PreConditions(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WS_DevRead_PreConditions(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
}

predicate WS_DevRead_PostConditions(
    ws:DM_State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_DevRead_PreConditions(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
        
    (true)
}

predicate WS_OSDrvWrite_PreConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WS_OSDrvWrite_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_OSDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WS_WimpDrvWrite_PreConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_GreenDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WS_WimpDrvWrite_PostConditions(
    ws:DM_State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_WimpDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    (ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    (true)
}

predicate WS_OSDevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_RedDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WS_OSDevWrite_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_OSDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    ((forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)) &&
        // Properties needed by the following property
    (P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
        
    (true)
}

predicate WS_WimpDevWrite_PreConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    DM_GreenDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate WS_WimpDevWrite_PostConditions(
    ws:DM_State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WS_WimpDevWrite_PreConditions(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    WK_Access_Common_PostConditions(ws, t, ws', ws_d) &&

    ((forall td_id :: td_id in td_id_val_map ==> td_id in ws.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in ws.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in ws.objects.dos)) &&
        // Properties needed by the following property
    (P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device
        
    (true)
}

predicate WK_Access_Common_PostConditions(
    ws:DM_State, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&

    (t.ws0 == ws) &&
    (DM_IsValidTrace(t)) &&
    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

predicate WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(
    ws:DM_State
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&
    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (true)
}

predicate WK_WimpDrvsDevs_Registration_CreatePartition_PostConditions(
    ws:DM_State, 
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_CreatePartition_PreConditions(ws)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

predicate WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&

    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (to_deactivate_dev_id in ws.subjects.devs) &&
    (DM_SubjPID(ws.subjects, to_deactivate_dev_id.sid) == ws.red_pid) &&
    (P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, to_deactivate_dev_id)) &&
        // Requirement: For the device to be deactivated

    (forall i, j :: 0 <= i < |to_assign_drv_ids| && 0 <= j < |to_assign_drv_ids|
                ==> (i == j <==> to_assign_drv_ids[i] == to_assign_drv_ids[j])) &&
        // Requirement: No duplicate device ID in <to_assign_drv_ids>
    (forall i, j :: 0 <= i < |to_assign_dev_ids| && 0 <= j < |to_assign_dev_ids|
                ==> (i == j <==> to_assign_dev_ids[i] == to_assign_dev_ids[j])) &&
        // Requirement: No duplicate device ID in <to_assign_dev_ids>
    (forall id :: id in to_assign_drv_ids ==> id in ws.subjects.drvs) &&
    (|to_assign_drv_ids| >= 0) &&
    (forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs) &&
    (|to_assign_dev_ids| >= 0) &&

    (to_assign_external_td_ids <= MapGetKeys(ws.objects.tds)) &&
    (to_assign_external_fd_ids <= MapGetKeys(ws.objects.fds)) &&
    (to_assign_external_do_ids <= MapGetKeys(ws.objects.dos)) &&

    (forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)) &&
        // Requirement: No subject owns these external objects

    (green_pid != NULL) &&
    (green_pid != ws.red_pid) &&
    (green_pid in ws.pids) &&
        // Requirement: We have already create a green partition

    (true)
}

predicate WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PostConditions(
    ws:DM_State, to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_PreConditions(
                ws, to_deactivate_dev_id, to_assign_drv_ids, to_assign_dev_ids,
                to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids,
                green_pid)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> t.ops == [DM_DevDeactivateOp(to_deactivate_dev_id.sid)] + DevActivateMulti_ToTraceOps(to_assign_dev_ids, green_pid) +
                                    WimpDrvActivateMulti_ToTraceOps(to_assign_drv_ids, green_pid) + 
                                    [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)]) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}

predicate WK_WimpDrvsDevs_Unregistration_PreConditions(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
{
    (forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)) &&

    (DM_IsValidState(ws) && DM_IsSecureState(ws)) &&

    (forall i, j :: 0 <= i < |to_deactivate_drv_ids| && 0 <= j < |to_deactivate_drv_ids|
                ==> (i == j <==> to_deactivate_drv_ids[i] == to_deactivate_drv_ids[j])) &&
        // Requirement: No duplicate device ID in <to_deactivate_drv_ids>
    (forall i, j :: 0 <= i < |to_deactivate_dev_ids| && 0 <= j < |to_deactivate_dev_ids|
                ==> (i == j <==> to_deactivate_dev_ids[i] == to_deactivate_dev_ids[j])) &&
        // Requirement: No duplicate device ID in <to_deactivate_dev_ids>
    (forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs) &&
    (|to_deactivate_drv_ids| >= 0) &&
    (forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs) &&
    (|to_deactivate_dev_ids| >= 0) &&

    (forall id :: id in to_deactivate_drv_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid) &&
    (forall id :: id in to_deactivate_dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) == green_pid) &&
        // Requirement: Drivers and devices to be deactivated must be from the 
        // green partition

    (forall i, j :: 0 <= i < |devs_to_activate_in_red| && 0 <= j < |devs_to_activate_in_red|
                ==> (i == j <==> devs_to_activate_in_red[i] == devs_to_activate_in_red[j])) &&
        // Requirement: No duplicate device ID in <devs_to_activate_in_red>
    (forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs) &&
    (|devs_to_activate_in_red| >= 0) &&
        // Requirement: Devices to be activated in the red partition must be 
        // existing devices

    (to_deactivate_external_td_ids <= MapGetKeys(ws.objects.tds)) &&
    (to_deactivate_external_fd_ids <= MapGetKeys(ws.objects.fds)) &&
    (to_deactivate_external_do_ids <= MapGetKeys(ws.objects.dos)) &&
    (forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)) &&
    (forall id :: id in to_deactivate_external_td_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
    (forall id :: id in to_deactivate_external_fd_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
    (forall id :: id in to_deactivate_external_do_ids
            ==> DM_ObjPID(ws.objects, id.oid) == green_pid) &&
        // Requirement: External objects to be deactivated must be from the 
        // green partition

    (green_pid != NULL) &&
    (green_pid != ws.red_pid) &&
    (green_pid in ws.pids) &&
        // Requirement: A green partition to be destroyed

    (true)
}

predicate WK_WimpDrvsDevs_Unregistration_PostConditions(
    ws:DM_State, to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID,
    t:DM_Trace, ws':DM_State, ws_d:bool
)
    requires WK_WimpDrvsDevs_Unregistration_PreConditions(
                ws, to_deactivate_drv_ids, to_deactivate_dev_ids, devs_to_activate_in_red,
                to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids,
                green_pid)
{
    (DM_IsValidState(ws') && DM_IsSecureState(ws')) &&
    (DM_IsSecureOps(ws, ws')) &&
    (ws_d == true ==> t.ws0 == ws) &&
    (ws_d == true ==> t.ops == [DM_GreenExternalObjsDeactivateOp(to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids, green_pid)] +
                                WimpDrvDeactivateMulti_ToTraceOps(to_deactivate_drv_ids) +
                                GreenDevDeactivateMulti_ToTraceOps(to_deactivate_dev_ids) +
                                DevActivateMulti_ToTraceOps(devs_to_activate_in_red, ws.red_pid) +
                                [DM_EmptyPartitionDestroyOp(green_pid)]) &&
    (ws_d == true ==> DM_IsValidTrace(t)) &&

    (!ws_d ==> t == DM_Trace(ws, [])) &&
    (!ws_d ==> ws' == ws) &&
    (!ws_d ==> DM_IsValidTrace(t)) &&
        // Property: If returns false, then stays at the same state

    (ws' == SeqLastElem(DM_CalcNewStates(t))) &&

    (true)
}