include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"

datatype Op      =  DrvReadOp(drv_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) | 
                    DevReadOp(dev_sid:Subject_ID, read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>) |
                    DevWriteOp(dev_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>) |
                    EmptyPartitionCreateOp(new_pid:Partition_ID) | 
                    EmptyPartitionDestroyOp(pid:Partition_ID) |
                    DrvActivateOp(drv_sid:Subject_ID, pid:Partition_ID) |
                    DrvDeactivateOp(drv_sid:Subject_ID) | 
                    DevActivateOp(dev_sid:Subject_ID, pid:Partition_ID) |
                    DevDeactivateOp(dev_sid:Subject_ID) |
                    ExternalObjsActivateOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID) | 
                    ExternalObjsDeactivateOp(td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, obj_pid:Partition_ID) | 
                    DrvWriteOp(drv_sid:Subject_ID, td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>)

datatype Trace   =  Trace(k0:State, ops:seq<Op>)




//******** Property of Each Operation ********//
predicate P_OpsProperties_DrvReadOp(k:State, op:Op)
    requires op.DrvReadOp?
{
    DrvRead_PreConditions(k, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists k':State, d:bool :: DrvRead_PostConditions(k, op.drv_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, k', d))
}

predicate P_OpsProperties_DevReadOp(k:State, op:Op)
    requires op.DevReadOp?
{
    DevRead_PreConditions(k, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src)
    ==> (exists k':State, d:bool :: DevRead_PostConditions(k, op.dev_sid, op.read_objs, op.tds_dst_src, op.fds_dst_src, op.dos_dst_src, k', d))
}

predicate P_OpsProperties_DevWriteOp(k:State, op:Op)
    requires op.DevWriteOp?
{
    DevWrite_PreConditions(k, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists k':State, d:bool :: DevWrite_PostConditions(k, op.dev_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, k', d))
}

predicate P_OpsProperties_EmptyPartitionCreateOp(k:State, op:Op)
    requires op.EmptyPartitionCreateOp?
{
    (IsValidState(k) && IsSecureState(k))
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_EmptyPartitionDestroyOp(k:State, op:Op)
    requires op.EmptyPartitionDestroyOp?
{
    (IsValidState(k) && IsSecureState(k))
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_DrvActivateOp(k:State, op:Op)
    requires op.DrvActivateOp?
{
    (IsValidState(k) && IsSecureState(k) &&
            Drv_ID(op.drv_sid) in k.subjects.drvs &&
            op.pid != NULL)
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_DrvDeactivateOp(k:State, op:Op)
    requires op.DrvDeactivateOp?
{
    (IsValidState(k) && IsSecureState(k) &&
            Drv_ID(op.drv_sid) in k.subjects.drvs)
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_DevActivateOp(k:State, op:Op)
    requires op.DevActivateOp?
{
    (IsValidState(k) && IsSecureState(k) &&
            Dev_ID(op.dev_sid) in k.subjects.devs &&
            op.pid != NULL)
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_DevDeactivateOp(k:State, op:Op)
    requires op.DevDeactivateOp?
{
    (IsValidState(k) && IsSecureState(k) &&
            Dev_ID(op.dev_sid) in k.subjects.devs)
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_ExternalObjsActivateOp(k:State, op:Op)
    requires op.ExternalObjsActivateOp?
{
    ExternalObjsActivate_PreConditions(k, op.td_ids, op.fd_ids, op.do_ids, op.pid)
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_ExternalObjsDeactivateOp(k:State, op:Op)
    requires op.ExternalObjsDeactivateOp?
{
    ExternalObjsDeactivate_PreConditions(k, op.td_ids, op.fd_ids, op.do_ids, op.obj_pid)
    ==> (exists k':State, d:bool :: Common_PostConditions(k, k', d))
}

predicate P_OpsProperties_DrvWriteOp(k:State, op:Op)
    requires op.DrvWriteOp?
{
    DrvWrite_PreConditions(k, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map)
    ==> (exists k':State, d:bool :: DrvWrite_PostConditions(k, op.drv_sid, op.td_id_val_map, op.fd_id_val_map, op.do_id_val_map, k', d))
}




//******** PreConditions and PostConditions of Operations ********//
predicate DrvRead_PreConditions(
    k:State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>  
)
{
    (IsValidState(k) && IsSecureState(k)) &&
    (Drv_ID(drv_sid) in k.subjects.drvs) &&
    (SubjPID(k, drv_sid) != NULL) &&
        // Requirement: The driver is in the state and is active
    (read_objs <= AllObjsIDs(k.objects)) &&

    (DrvRead_ReadSrcObjsToDestObjs_PreConditions(k, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&

    (true)
}

predicate DrvRead_PostConditions(
    k:State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    k':State, d:bool
)
    requires DrvRead_PreConditions(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (forall dev_id :: dev_id in k'.subjects.devs
                ==> k'.subjects.devs[dev_id].hcoded_td_id in k'.objects.tds) &&
        // Property needed by "(IsSecureOps(k, k')"
    (IsValidState(k') && IsSecureState(k')) &&
    (IsSecureOps(k, k')) &&

    (d == true ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(k, drv_sid, 
        read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
        // Property 4: All read objects and objects to store read results must be 
        // in the same partition with the driver

    (true)
}

predicate DevRead_PreConditions(
    k:State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>  
)
{
    (IsValidState(k) && IsSecureState(k)) &&
    (Dev_ID(dev_sid) in k.subjects.devs) &&
    (SubjPID(k, dev_sid) != NULL) &&
        // Requirement: The device is in the state and is active
    (forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)) &&
        // Requirement: The device (<Dev_ID(dev_sid)>) must have transfers to
        // the objects (<read_objs>)

    (DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)) &&
    (DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) &&

    (true)
}

predicate DevRead_PostConditions(
    k:State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    k':State, d:bool
)
    requires DevRead_PreConditions(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (forall dev_id :: dev_id in k'.subjects.devs
                ==> k'.subjects.devs[dev_id].hcoded_td_id in k'.objects.tds) &&
        // Property needed by "(IsSecureOps(k, k')"
    (IsValidState(k') && IsSecureState(k')) &&
    (IsSecureOps(k, k')) &&

    P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(k, dev_sid, 
        read_objs, tds_dst_src, fds_dst_src, dos_dst_src) &&
        // Property 4: All read objects and objects to store read results must be 
        // in the same partition with the driver

    (true)
}

predicate P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(
    k:State, 
    s_id:Subject_ID, 
    td_id_val_map:map<TD_ID, TD_Val>,
    fd_id_val_map:map<FD_ID, FD_Val>, 
    do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) 
    requires s_id in AllSubjsIDs(k.subjects)

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)
        // Requirement: Device only write existing objects
{
    (forall o_id :: o_id in (TDIDsToObjIDs(MapGetKeys<TD_ID, TD_Val>(td_id_val_map)) + 
                                FDIDsToObjIDs(MapGetKeys<FD_ID, FD_Val>(fd_id_val_map)) + 
                                DOIDsToObjIDs(MapGetKeys<DO_ID, DO_Val>(do_id_val_map)))
                    // Forall o_id that is an internal ID of any TD/FD/DO in *_id_val_map
        ==> o_id in AllObjsIDs(k.objects) &&
            ObjPID(k, o_id) == SubjPID(k, s_id)) &&

    (true)
}

predicate DevWrite_PreConditions(
    k:State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (IsValidState(k) && IsSecureState(k)) &&
    (Dev_ID(dev_sid) in k.subjects.devs) &&
    (SubjPID(k, dev_sid) != NULL) &&
        // Requirement: The device is in the state and is active

    (forall td_id2 :: td_id2 in td_id_val_map
                ==> DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, td_id2, td_id_val_map[td_id2])) &&
    (forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, fd_id2, fd_id_val_map[fd_id2])) &&
    (forall do_id2 :: do_id2 in do_id_val_map
                ==> DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, do_id2, do_id_val_map[do_id2])) &&

    (true)
}

predicate DevWrite_PostConditions(
    k:State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    k':State, d:bool
)
    requires DevWrite_PreConditions(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    (IsValidState(k') && IsSecureState(k')) &&
    (IsSecureOps(k, k')) &&
    ((forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)) &&
        // Property 3: Written TDs, FDs and DOs are in the I/O state. 
        // Note: If not proving this property, then it is possible the o_id is 
        // in AllObjsIDs(k), but the TD_ID(o_id) in td_id_val_map is not in 
        // k.objects.tds. Same issue for FDs and DOs.
    P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map) &&
        // Property 4: All written objects are in the same partition with the device

    (true)
}

predicate Common_PostConditions(
    k:State, k':State, d:bool
)
    requires IsValidState(k) && IsSecureState(k)
{
    (IsValidState(k') && IsSecureState(k')) &&
    (IsSecureOps(k, k')) &&

    (true)
}

predicate ExternalObjsActivate_PreConditions(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID
)
{
    (IsValidState(k) && IsSecureState(k)) &&
    (td_ids <= MapGetKeys(k.objects.tds)) &&
    (fd_ids <= MapGetKeys(k.objects.fds)) &&
    (do_ids <= MapGetKeys(k.objects.dos)) &&
    (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)) &&
        // Requirement: no subject owns these external objects 
    (pid != NULL) &&

    (true)
}

predicate ExternalObjsDeactivate_PreConditions(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, obj_pid:Partition_ID
)
{
    (IsValidState(k) && IsSecureState(k)) &&
    (td_ids <= MapGetKeys(k.objects.tds)) &&
    (fd_ids <= MapGetKeys(k.objects.fds)) &&
    (do_ids <= MapGetKeys(k.objects.dos)) &&
    (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)) &&
        // Requirement: no subject owns these external objects 

    (true)
}

predicate DrvWrite_PreConditions(
    k:State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
{
    (IsValidState(k) && IsSecureState(k)) &&
    (Drv_ID(drv_sid) in k.subjects.drvs) &&
    (IDToDrv(k, Drv_ID(drv_sid)).pid != NULL) &&
        // Requirement: The driver is in the state and is active
    ((forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map) &&
        // Requirement: The driver does not write any hardcoded TDs

    (true)
}

predicate DrvWrite_PostConditions(
    k:State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    k':State, d:bool
)
    requires DrvWrite_PreConditions(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    (IsValidState(k') && IsSecureState(k')) &&
    (IsSecureOps(k, k')) &&
    (d == true ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) &&
        // Property 3: All written objects are in the same partition with the driver

    (true)
}




//******** Internal Predicates of PreConditions and PostConditions ********//
predicate P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(
    k:State, s_id:Subject_ID,
    read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires s_id in AllSubjsIDs(k.subjects)

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires K_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(k, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (forall o_id :: o_id in read_objs
                    ==> o_id in AllObjsIDs(k.objects) &&
                        ObjPID(k, o_id) == SubjPID(k, s_id)) &&
        // Objects in parameters must be in the same partition with the driver
    (forall td_id :: td_id in tds_dst_src
                    ==> ObjPID(k, td_id.oid) == SubjPID(k, s_id)) &&
    (forall fd_id :: fd_id in fds_dst_src
                    ==> ObjPID(k, fd_id.oid) == SubjPID(k, s_id)) &&
    (forall do_id :: do_id in dos_dst_src
                    ==> ObjPID(k, do_id.oid) == SubjPID(k, s_id)) &&
        // All objects that store read results must be in the same partition
        // with the subject

    (true)
}

predicate K_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(
    k:State, 
    
    tds_dst_src:map<TD_ID, TD_ID>,
    fds_dst_src:map<FD_ID, FD_ID>,
    dos_dst_src:map<DO_ID, DO_ID> 
)
{
    (forall td_id :: td_id in tds_dst_src
                ==> td_id in k.objects.tds && tds_dst_src[td_id] in k.objects.tds) &&
    (forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in k.objects.fds && fds_dst_src[fd_id] in k.objects.fds) &&
    (forall do_id :: do_id in dos_dst_src
                ==> do_id in k.objects.dos && dos_dst_src[do_id] in k.objects.dos) &&
        // Requirement: Destination and source objects must be in the DM state
        
    (true)
}

predicate DrvRead_ReadSrcObjsToDestObjs_PreConditions(
    k:State, 
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
{
    (forall td_id :: td_id in tds_dst_src
                ==> tds_dst_src[td_id].oid in read_objs) &&
    (forall fd_id :: fd_id in fds_dst_src
                ==> fds_dst_src[fd_id].oid in read_objs) &&
    (forall do_id :: do_id in dos_dst_src
                ==> dos_dst_src[do_id].oid in read_objs) &&
        // Requirement: Source objects in <tds/fds/dos_dst_src> must also be 
        // in <read_objs>
    K_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(k, tds_dst_src, fds_dst_src, dos_dst_src) &&
        // Requirement: Destination and source objects must be in the state
    (forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in tds_dst_src) &&
        // Requirement: Destination TDs cannot be any hardcoded TDs
    (forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id.oid !in read_objs) &&
        // Requirement: Read objects must not be any hardcoded TDs

    (true)
}

predicate DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
{
    (forall td_id :: td_id in tds_dst_src
                ==> tds_dst_src[td_id].oid in read_objs)&&
    (forall fd_id :: fd_id in fds_dst_src
                ==> fds_dst_src[fd_id].oid in read_objs)&&
    (forall do_id :: do_id in dos_dst_src
                ==> dos_dst_src[do_id].oid in read_objs)&&
        // Requirement: Source objects in <tds/fds/dos_dst_src> must also be 
        // in <read_objs>

    (true)
}

predicate DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(
    k:State,
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
{
    K_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(k, tds_dst_src, fds_dst_src, dos_dst_src) &&
        // Requirement: Destination and source objects must be in the state

    (true)
}

predicate DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(
    k:State,
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active

    requires DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)
{
    (forall td_id2 :: td_id2 in tds_dst_src
                ==> DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, td_id2, k.objects.tds[tds_dst_src[td_id2]].val))&&
    (forall fd_id2 :: fd_id2 in fds_dst_src
                ==> DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, fd_id2, k.objects.fds[fds_dst_src[fd_id2]].val))&&
    (forall do_id2 :: do_id2 in dos_dst_src
                ==> DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, do_id2, k.objects.dos[dos_dst_src[do_id2]].val))&&
        // Requirement: Writing destination TDs/FDs/DOs with values of source 
        // objects must be in tranfers

    (true)
}

predicate DevWrite_WriteTDWithValMustBeInATransfer(
    k:State, dev_sid:Subject_ID, target_td_id:TD_ID, write_val:TD_Val
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_td_id in GetTDVal(k, td_id).trans_params_tds &&
                    W in GetTDVal(k, td_id).trans_params_tds[target_td_id].amodes &&
                        // The TD references the target TD (<target_td_id>) with W
                    write_val in GetTDVal(k, td_id).trans_params_tds[target_td_id].vals)
                        // The TD specifies the new value to be written
        // For the write to the TD (<target_td_id>) with the new value 
        // (<write_val>), it must be from an active TD (<td_id>) that can be 
        // read by the active device (<Dev_ID(dev_sid)>)
}

predicate DevWrite_WriteFDWithValMustBeInATransfer(
    k:State, dev_sid:Subject_ID, target_fd_id:FD_ID, write_val:FD_Val
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_fd_id in GetTDVal(k, td_id).trans_params_fds &&
                    W in GetTDVal(k, td_id).trans_params_fds[target_fd_id].amodes && 
                        // The TD references the target FD (<target_fd_id>) with W
                    write_val in GetTDVal(k, td_id).trans_params_fds[target_fd_id].vals)
                        // The TD specifies the new value to be written
        // For the write to the FD (<target_fd_id>) with the new value 
        // (<write_val>), it must be from an active TD (<td_id>) that can be 
        // read by the active device (<Dev_ID(dev_sid)>)
}

predicate DevWrite_WriteDOWithValMustBeInATransfer(
    k:State, dev_sid:Subject_ID, target_do_id:DO_ID, write_val:DO_Val
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    (exists td_id :: td_id in k.objects.tds &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_do_id in GetTDVal(k, td_id).trans_params_dos &&
                    W in GetTDVal(k, td_id).trans_params_dos[target_do_id].amodes &&
                        // The TD references the target DO (<target_do_id>) with W 
                    write_val in GetTDVal(k, td_id).trans_params_dos[target_do_id].vals)
                        // The TD specifies the new value to be written
        // For the write to the DO (<target_do_id>) with the new value 
        // (<write_val>), it must be from an active TD (<td_id>) that can be 
        // read by the active device (<Dev_ID(dev_sid)>)
}