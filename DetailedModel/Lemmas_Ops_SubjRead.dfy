include "Model_Ops_Predicates.dfy"

lemma Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(
    ws:DM_State, k:State, dev_sid:Subject_ID, read_objs:set<Object_ID>
)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)
    requires IsValidState(k) && IsSecureState(k)
    requires IsSubjID(k.subjects, dev_sid)

    requires forall o_id :: o_id in read_objs
                ==> o_id in AllObjsIDs(k.objects) &&
                    ObjPID(k, o_id) == SubjPID(k, dev_sid) 
        // Property 4: All read objects must be in the same partition with 
        // the driver

    ensures forall o_id :: o_id in read_objs
                ==> o_id in DM_AllObjsIDs(ws.objects) &&
                    DM_ObjPID(ws.objects, o_id) == DM_SubjPID(ws.subjects, dev_sid)
{
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
}

lemma Lemma_K_P_DrvRead_ReturnTrue_Def_Prove(
    k:State, drv_sid:Subject_ID,
    read_objs:set<Object_ID>, tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>  
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs

    requires read_objs <= AllObjsIDs(k.objects)
    requires DrvRead_ReadSrcObjsToDestObjs_PreConditions(k, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    requires td_id_val_map == DrvDevRead_ReplaceSrcTDWithVal(k, tds_dst_src)
    requires fd_id_val_map == DrvDevRead_ReplaceSrcFDWithVal(k, fds_dst_src)
    requires do_id_val_map == DrvDevRead_ReplaceSrcDOWithVal(k, dos_dst_src)

    requires (forall o_id :: o_id in read_objs
        ==> SubjPID(k, drv_sid) == ObjPID(k, o_id))
    requires P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)

    ensures P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    // Dafny can automatically prove this lemma
}