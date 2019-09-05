include "Model_Ops_Predicates.dfy"
include "Model_InnerFuncs.dfy"
include "Lemmas_Ops_SubjRead.dfy"
include "Lemmas_Ops_SubjWrite.dfy"
include "Lemmas_Ops_SubjObjActivate.dfy"
include "Lemmas_Ops_SubjObjDeactivate.dfy"
include "Lemmas_Ops_GreenDrvWrite_SI1.dfy"
include "Lemmas_Model_InnerFuncs.dfy"

//******** DrvRead/DevRead ********//
// Operation: Driver in the red partition reads a set of objects, and copies 
// the values if needed
// (needs 360s to verify)
method DM_RedDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
    
    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver
        
    ensures (ws', ws_d) == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures P_DM_OpsProperties(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures ws_d == true ==> (forall td_id2 :: td_id2 in real_td_id_val_map ==> td_id2 in DMStateToState(ws).objects.tds)
        // Property needed by the properties below
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), 
                                real_td_id_val_map, 
                                DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src),
                                DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), 
                                    real_td_id_val_map, 
                                    DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)
                                ) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id))
    {
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);
        ws', ws_d, real_td_id_val_map := DM_RedDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        
        if(ws_d)
        {
            // Prove DM_CalcNewState() == (ws', ws_d)
            Lemma_DM_RedDrvRead_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
            ghost var result1 := DM_CalcNewState(ws, DM_RedDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
            assert result1 == DM_RedDrvRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
            assert result1 == (ws', ws_d);
        }
        else
        {
            assert ws_d == false;
            assert ws' == ws;
            
            Lemma_DM_RedDrvRead_ProveDM_CalcNewState(
                ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
        }
    }
    else
    {
        ws' := ws;
        ws_d := false;
    }
}

// Operation: Driver in a green partition reads a set of objects, and copies 
// the values if needed
// (needs 190s to verify)
method DM_GreenDrvRead(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
    
    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, drv_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the driver

    ensures (ws', ws_d) == DM_GreenDrvReadRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures P_DM_OpsProperties(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures DM_CalcNewState(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures IsValidState(DMStateToState(ws)) 
    ensures ws_d == true ==> P_DrvRead_ReturnTrue_Def(DMStateToState(ws), drv_sid, 
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: DrvRead in the abstract model returns true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), 
                                DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src),
                                DMStateToState(ws'))
    
    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), 
                                    DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)
                                ) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvRead in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);
    if( forall o_id :: o_id in read_objs ==> DM_SubjPID(ws.subjects, drv_sid) == DM_ObjPID(ws.objects, o_id))
    {
        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, drv_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);
        ws', ws_d := DM_GreenDrvWrite(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

        if(ws_d)
        {
            assert P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

            Lemma_K_P_DrvRead_ReturnTrue_Def_Prove(k, drv_sid, read_objs, 
                tds_dst_src, fds_dst_src, dos_dst_src,
                td_id_val_map, fd_id_val_map, do_id_val_map);
            assert P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);

            // Prove DM_CalcNewState() == (ws', ws_d)
            Lemma_DM_GreenDrvRead_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
            ghost var result1 := DM_CalcNewState(ws, DM_GreenDrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
            assert result1 == DM_GreenDrvReadRead_InnerFunc(ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
            assert result1 == (ws', ws_d);
        }
        else
        {
            assert ws_d == false;
            assert ws' == ws;
            
            Lemma_DM_GreenDrvRead_ProveDM_CalcNewState(
                ws, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
        }
    }
    else
    {
        ws' := ws;
        ws_d := false;
    }
}

// Operation: Device reads a set of objects, and copies the values if needed.
// The device could be in the red partition, or a green partition.
// (needs 130s to verify)
method DM_DevRead(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires DM_IsDevID(ws.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device is active

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_SubjRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInDMState(ws, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(ws, dev_sid, read_objs)
    requires DM_DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
    
    ensures ws_d == true ==> P_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(ws, dev_sid,
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 2: All accessed objects in parameters must be in the same 
        // partition with the device

    ensures (ws', ws_d) == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures P_DM_OpsProperties(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
    ensures DM_CalcNewState(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures ws_d == true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), 
                                DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src),
                                DMStateToState(ws'))
        
    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), 
                                    DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src), 
                                    DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src)
                              ) == DMStateToState(ws'))
        // Property: Commutative diagram to DevRead in the abstract model
        // [NOTE] This is because DevRead in the abstract model (always) returns
        // true, and DevRead modifies state as specified in DrvDevWrite_Func
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Dev_ID(dev_sid) in k.subjects.devs;

    var dev_id := Dev_ID(dev_sid);
    {
        var k', d := DevRead(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
        assert d == true;

        Lemma_DrvDevRead_InterpretedPropertyOf_AllReadObjsMustBeinSamePartitionWithDev(ws, k, dev_sid, read_objs);

        // Construct ws'
        var td_id_val_map := DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src);
        var fd_id_val_map := DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src);
        var do_id_val_map := DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src);

        if(DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid)
        {
            // If the device is in the red partition
            ws', ws_d := DM_RedDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);       
        }
        else
        {
            // If the device is in a green partition
            ws', ws_d := DM_GreenDevWrite(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        }
        assert ws_d == true;
        
        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_DevRead_ProvePreConditionsOfDM_CalcNewState(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src));
        assert result1 == DM_DevRead_InnerFunc(ws, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
        assert result1 == (ws', ws_d);
    }
}




//******** DrvWrite/DevWrite ********//
// Operation: Driver in the red partition writes a set of objects with values
method DM_RedDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool, ghost real_td_id_val_map:map<TD_ID, TD_Val>)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1
    ensures ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2
    ensures P_DM_OpsProperties(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures ws_d == true
                ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver

    ensures forall td_id2 :: td_id2 in real_td_id_val_map ==> td_id2 in DMStateToState(ws).objects.tds
        // Property needed by the properties below
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), real_td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), real_td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Drv_ID(drv_sid) in k.subjects.drvs;

    var drv_id := Drv_ID(drv_sid);

    var result := DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    var in_ws' := result.0;
    ws' := result.1;
    ws_d := result.2;
    if(ws_d)
    {
        // Prove DM_IsValidState(ws')
        assert DevHWProt_ReturnGoodSnapshotOfRedTDs(in_ws', ws');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        assert P_DevHWProt_ResultDMIStateModifiesValsOfRedTDsOnly_SubjsPIDsRedPID(in_ws', ws');
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(in_ws', ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState_SI2(ws')
        Lemma_NewDM_RedDrvWrite_SameDMAllActiveGreenUSBTDs(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_RedDrvWrite_CommonValidityPropertiesOfNewDM_AndUnchangedPIDsOfGreenFDsDOs(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', DMStateToState(ws'));
        assert DM_IsSecureState_SI2(ws');

        // Prove DM_IsSecureState_SI3(ws')
        Lemma_NewDM_RedDrvWrite_SameDMAllObjsIDsAndObjPIDs(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DrvWrite_NewDM_FulfillSI3(ws, ws');

        // Prove DM_IsSecureState(ws')
        assert DM_IsSecureState_SI1(ws');        
        assert DM_IsSecureState(ws');

        // Prove k' == DMStateToState(ws')
        var ws_k' := DMStateToState(ws');
        Lemma_DMStateToState_SecureK(ws', ws_k');
        assert IsValidState(ws_k') && IsSecureState(ws_k');
        //// Calculate actual <td_id_val_map>, <fd_id_val_map>, <do_id_val_map> written
        var td_id_val_map2 := TDsStateDiff(TDStateToTDVal(ws'.objects.tds), TDStateToTDVal(ws.objects.tds));
        Lemma_NewDM_RedDrvWrite_MappedStateOfNewDMIsProposedWriteResultOfMappedStateOfDM(ws, in_ws', ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map2, fd_id_val_map, do_id_val_map);
        //// Prove k' == DMStateToState(ws')
        Lemma_RedDrvWrite_PIDsOfAllTDsInTDDValMap2AreUnmodified(ws, k, in_ws', ws', drv_sid, td_id_val_map, td_id_val_map2, fd_id_val_map, do_id_val_map);
        Lemma_RedDrvWrite_ProveP_DrvWrite_ReturnTrue_Def(k, ws_k', drv_sid, td_id_val_map2, fd_id_val_map, do_id_val_map);
        var k', d := DrvWrite(k, drv_sid, td_id_val_map2, fd_id_val_map, do_id_val_map);
        assert d == true;
        assert k' == DMStateToState(ws');

        real_td_id_val_map := td_id_val_map2;
        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map2, fd_id_val_map, do_id_val_map);

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_RedDrvWrite_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_RedDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == (DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1, 
                           DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
        real_td_id_val_map := td_id_val_map;

        assert DM_RedDrvWrite_PreConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert DM_RedDrvWrite_PostConditions(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        assert ws' == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).1;
        assert ws_d == DM_RedDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).2;
    }
}

// Operation: Driver in a green partition writes a set of objects with values
// (needs 50s to verify)
method DM_GreenDrvWrite(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures P_DM_OpsProperties(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures ws_d == true ==> P_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: Objects in parameters must be in the same partition with 
        // the driver
    ensures IsValidState(DMStateToState(ws))
    ensures ws_d == true ==> P_DrvWrite_ReturnTrue_Def(DMStateToState(ws), drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property: DrvWrite in the abstract model returns true

    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Drv_ID(drv_sid) in k.subjects.drvs;

    var drv_id := Drv_ID(drv_sid);

    var result := DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        // Construct ws'.objects
        var tds' := WriteTDsVals(ws.objects.tds, td_id_val_map);
        var fds' := WriteFDsVals(ws.objects.fds, fd_id_val_map);
        var dos' := WriteDOsVals(ws.objects.dos, do_id_val_map);
        var new_objects := Objects(tds', fds', dos');
        ws' := DM_State(ws.subjects, new_objects, ws.pids, ws.red_pid, ws.devs_activatecond, ws.tds_to_all_states);
        ws_d := true;

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
        
        // Prove DM_IsSecureState_SI2(ws')
        var ws_k' := DMStateToState(ws');
        Lemma_DM_GreenDrvWrite_FulfillSI2(ws, k, ws', ws_k', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert DM_IsSecureState_SI2(ws');

        // Prove DM_IsSecureState_SI3(ws')
        Lemma_NewDM_GreenDrvWrite_SameDMAllObjsIDsAndObjPIDs(ws, ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DrvWrite_NewDM_FulfillSI3(ws, ws');

        // Prove DM_IsSecureState(ws')
        Lemma_NewDM_GreenDrvWrite_SameDMRedTDs(ws, ws', drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DM_SI1HoldsIfRedTDsAreUnchanged(ws, k, ws', ws_k');
        assert DM_IsSecureState_SI1(ws');
        assert DM_IsSecureState(ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DMStateToState_SecureK(ws', ws_k');
        assert IsValidState(ws_k') && IsSecureState(ws_k');
        assert ws_k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map);
        var k', d := DrvWrite(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert d == true;
        assert k' == DMStateToState(ws');

        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map, fd_id_val_map, do_id_val_map);

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_GreenDrvWrite_ProvePreConditionsOfDM_CalcNewState(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_GreenDrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == DM_GreenDrvWrite_InnerFunc(ws, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}

// Operation: Device in the red partition writes a set of objects with values
method DM_RedDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
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
        
    ensures (ws', ws_d) == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures P_DM_OpsProperties(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
        
    ensures ws_d == true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DevWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Dev_ID(dev_sid) in k.subjects.devs;

    var dev_id := Dev_ID(dev_sid);
    {
        var k', d := DevWrite(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert d == true;

        var result := DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        ws' := result.0;
        ws_d := result.1;

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        assert k' == DMStateToState(ws');
        Lemma_DM_DevWrite_AllWrittenObjsMustBeInSamePartitionWithDev(ws, k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map, fd_id_val_map, do_id_val_map);
        
        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_RedDevWrite_ProvePreConditionsOfDM_CalcNewState(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_RedDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == DM_RedDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert result1 == (ws', ws_d);
    }
}

// Operation: Device in a green partition writes a set of objects with values
method DM_GreenDevWrite(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
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

    ensures (ws', ws_d) == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures P_DM_OpsProperties(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    ensures DM_CalcNewState(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures ws_d == true
    ensures ws_d == true ==> P_DrvDevWrite_ModificationToState(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map, DMStateToState(ws'))

    ensures (ws_d == true ==> DrvDevWrite_Func(DMStateToState(ws), td_id_val_map, fd_id_val_map, do_id_val_map) == DMStateToState(ws'))
        // Property: Commutative diagram to DevWrite in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
    assert Dev_ID(dev_sid) in k.subjects.devs;

    var dev_id := Dev_ID(dev_sid);

    {
        var k', d := DevWrite(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert d == true;

        var result := DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        ws' := result.0;
        ws_d := result.1;

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        assert k' == DMStateToState(ws');
        Lemma_DM_DevWrite_AllWrittenObjsMustBeInSamePartitionWithDev(ws, k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        
        // Prove TDs are not modified
        Lemma_DM_DevsInGreen_Prove(ws, dev_id);
        Lemma_GreenDevWrite_TDsAreUnmodified(ws, k, dev_id, td_id_val_map);
        Lemma_GreenDevWrite_TDsInDMObjectsAreSame(ws, ws', td_id_val_map, fd_id_val_map, do_id_val_map);
        
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        Lemma_DrvDevWrite_Func_Prove(k, k', td_id_val_map, fd_id_val_map, do_id_val_map);

        // Prove DM_CalcNewState() == (ws', ws_d)
        Lemma_DM_GreenDevWrite_ProvePreConditionsOfDM_CalcNewState(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, ws', ws_d);
        ghost var result1 := DM_CalcNewState(ws, DM_GreenDevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map));
        assert result1 == DM_GreenDevWrite_InnerFunc(ws, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        assert result1 == (ws', ws_d);
    }
}




//******** Create/Destroy Partition ********//
// Operation: Create an empty I/O partition
method DM_EmptyPartitionCreate(
    ws:DM_State, 
    new_pid:Partition_ID // The ID of the new partition
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_EmptyPartitionCreate_InnerFunc(ws, new_pid)
    ensures P_DM_OpsProperties(ws, DM_EmptyPartitionCreateOp(new_pid))
    ensures DM_CalcNewState(ws, DM_EmptyPartitionCreateOp(new_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state
    
    ensures ws_d ==> EmptyPartitionCreate_Prop(DMStateToState(ws), new_pid, DMStateToState(ws'), true)

    ensures (ws_d == true ==> EmptyPartitionCreate_Func(DMStateToState(ws), new_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to EmptyPartitionCreate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var result := DM_EmptyPartitionCreate_InnerFunc(ws, new_pid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        assert (new_pid != NULL) && (new_pid !in k.pids);
        var k', d := EmptyPartitionCreate(k, new_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        ghost var result1 := DM_CalcNewState(ws, DM_EmptyPartitionCreateOp(new_pid));
        assert result1 == DM_EmptyPartitionCreate_InnerFunc(ws, new_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}

// Operation: Destroy an I/O partition
method DM_EmptyPartitionDestroy(
    ws:DM_State, 
    pid:Partition_ID // The ID of the partition to be destroyed
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_EmptyPartitionDestroy_InnerFunc(ws, pid)
    ensures P_DM_OpsProperties(ws, DM_EmptyPartitionDestroyOp(pid))
    ensures DM_CalcNewState(ws, DM_EmptyPartitionDestroyOp(pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures ws_d ==> EmptyPartitionDestroy_Prop(DMStateToState(ws), pid, DMStateToState(ws'), true)

    ensures (ws_d == true ==> EmptyPartitionDestroy_Func(DMStateToState(ws), pid) == DMStateToState(ws'))
        // Property: Commutative diagram to EmptyPartitionDestroy in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var result := DM_EmptyPartitionDestroy_InnerFunc(ws, pid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');
        Lemma_NewDM_SameSubjObjPIDsIfPIDsAreUnchanged(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_EmptyPartitionDestroy_ProveCheckOfDevActivateInK(ws, k, pid);
        var k', d := EmptyPartitionDestroy(k, pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_EmptyPartitionDestroy_ProveRedPIDStillExists(ws, ws', pid);
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SameTDsInGreen_IfTDsPIDsAreUnchanged(ws, ws');
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        ghost var result1 := DM_CalcNewState(ws, DM_EmptyPartitionDestroyOp(pid));
        assert result1 == DM_EmptyPartitionDestroy_InnerFunc(ws, pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}




//******** DrvActivate ********//
// Operation: Activate a driver into a green partition
// [NOTE] Red drivers do not need to be deactivated/activated, because they do
// not need to be moved to green partitions
method DM_DrvActivateToGreenPartition(
    ws:DM_State, 
    drv_sid:Subject_ID, // ID of the driver to be activated
    green_pid:Partition_ID // ID of the partition to activate the driver into
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires green_pid != NULL
    requires green_pid != ws.red_pid
        // Requirement: the destination partition must be a green partition

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid)
    ensures P_DM_OpsProperties(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid))
    ensures DM_CalcNewState(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)
        // Property needed by the following property
    ensures (ws_d == true ==> P_DrvActivate_ModificationToState(DMStateToState(ws), drv_sid, green_pid, DMStateToState(ws')))

    ensures (ws_d == true ==> DrvActivate_Func(DMStateToState(ws), drv_sid, green_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Drv_Property(k, Drv_ID(drv_sid));

    var drv_id := Drv_ID(drv_sid);
    
    var result := DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        var tds_owned_by_drv:set<TD_ID> := ws.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := ws.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := ws.subjects.drvs[drv_id].do_ids;

        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        var tds' := new_objects.tds;
        assert ws'.red_pid == ws.red_pid;

        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {drv_sid};
        var toactivate_td_ids := tds_owned_by_drv;
        var toactivate_fd_ids := fds_owned_by_drv;
        var toactivate_do_ids := dos_owned_by_drv;

        Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, drv_id, toactivate_td_ids);
        assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, green_pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, new_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid);

        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, new_subjects.devs, new_objects, toactivate_td_ids, green_pid);

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        Lemma_DM_DevActivate_ProveCheckOfDevActivateInK(ws, k, drv_sid, green_pid);
        assert (SubjPID(k, drv_sid) == NULL) && (green_pid in k.pids);
        var k', d := DrvActivate(k, drv_sid, green_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');
        
        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        ghost var result1 := DM_CalcNewState(ws, DM_DrvActivateToGreenPartitionOp(drv_sid, green_pid));
        assert result1 == DM_DrvActivateToGreenPartition_InnerFunc(ws, drv_sid, green_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}




//******** DevActivate ********//
// Operation: Activate a device into a partition. The partition could be green
// or red partition. For example, devices are moved between red and green.
// (need 50s to verify)
method DM_DevActivate(
    ws:DM_State, 
    dev_sid:Subject_ID, // ID of the device to be activated
    pid:Partition_ID // ID of the partition to activate the device into
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires pid != NULL

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_DevActivate_InnerFunc(ws, dev_sid, pid)
    ensures P_DM_OpsProperties(ws, DM_DevActivateOp(dev_sid, pid))
    ensures DM_CalcNewState(ws, DM_DevActivateOp(dev_sid, pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)
        // Property needed by the following property
    ensures (ws_d == true ==> P_DevActivate_ModificationToState(DMStateToState(ws), dev_sid, pid, DMStateToState(ws')))

    ensures (ws_d == true ==> DevActivate_Func(DMStateToState(ws), dev_sid, pid) == DMStateToState(ws'))
        // Property: Commutative diagram to DevActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    {
        var result := DM_DevActivate_InnerFunc(ws, dev_sid, pid);
        ws' := result.0;
        ws_d := result.1; 
        if(ws_d)
        {
            var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;

            var new_objects := ws'.objects;
            var new_subjects := ws'.subjects;
            var tds' := new_objects.tds;
            assert ws'.red_pid == ws.red_pid;

            // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
            var toactivate_s_ids:set<Subject_ID> := {dev_sid};
            var toactivate_td_ids := tds_owned_by_dev;
            var toactivate_fd_ids := fds_owned_by_dev;
            var toactivate_do_ids := dos_owned_by_dev;

            Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
            Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
            Lemma_DevActivate_HCodedTDsToBeActivatedHaveUnmodifiedVals(k, tds', dev_id, toactivate_td_ids);
            assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, pid);
            assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, pid);
            assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, pid);
            assert SubjObjActivate_PropertiesOfNewSubjs(k, new_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

            Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, new_subjects.devs, new_objects, toactivate_td_ids, pid);

            assert P_DMAndNewDM_SameObjectID(ws, ws');
            assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

            // Prove common validity properties
            Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

            Lemma_NewDM_SameSubjObjIDs(ws, ws');
            Lemma_NewDM_SameSubjObjOwnership(ws, ws');

            // Prove k' == DMStateToState(ws')
            Lemma_DM_DevActivate_ProveCheckOfDevActivateInK(ws, k, dev_sid, pid);
            assert (SubjPID(k, dev_sid) == NULL) && (pid in k.pids);
            var k', d := DevActivate(k, dev_sid, pid);
            assert d == true;
            assert k' == DMStateToState(ws');
            
            // Prove DM_IsValidState_SubjsObjsPIDs(ws')
            Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
            assert DM_IsValidState_SubjsObjsPIDs(ws');

            // Prove DM_IsValidState(ws')
            Lemma_NewDM_DevActivate_OtherDevsHaveUnchangedPIDs(ws, ws', dev_id, pid);
            Lemma_NewDM_IsValidState_DevActivate_DevsActivateCond(ws, ws', dev_id, pid);
            assert DM_IsValidState(ws');

            // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
            Lemma_DevActivate_HCodedTDsBeingActivatedHaveNoWriteTransfersToTDs(k, dev_id);
            Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
            Lemma_NewDMFromNewK_FulfillSI3(ws', k');
            assert DM_IsSecureState_SI3(ws');
            Lemma_NewDMFromNewK_FulfillSI1(ws', k');
            assert DM_IsSecureState(ws');

            // Prove DM_CalcNewState() == (ws', ws_d)
            ghost var result1 := DM_CalcNewState(ws, DM_DevActivateOp(dev_sid, pid));
            assert result1 == DM_DevActivate_InnerFunc(ws, dev_sid, pid);
            assert result1 == (ws', ws_d);
        }
        else
        {
            assert ws' == ws;
            assert ws_d == false;
        }
    }
}




//******** ExternalObjsActivate ********//
// Operation: Activate external objects into a green partition
// [NOTE] External objects in red do not need to be deactivated/activated,
// because these objects do not need to be moved to green partitions
method DM_ExternalObjsActivateToGreenPartition(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be activated
    green_pid:Partition_ID // ID of the partition to activate the objects into
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
    ensures P_DM_OpsProperties(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid))
    ensures DM_CalcNewState(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    ensures fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    ensures do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)
    ensures (ws_d == true 
                ==> (forall s_id, o_id :: s_id in AllSubjsIDs(DMStateToState(ws).subjects) &&
                            o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                        ==> !DoOwnObj(DMStateToState(ws), s_id, o_id)))
        // Property needed by the following property
    ensures (ws_d == true 
                ==> P_ExternalObjsActivate_ModificationToState(DMStateToState(ws), 
                        td_ids, fd_ids, do_ids, green_pid, DMStateToState(ws')))

    ensures (ws_d == true ==> ExternalObjsActivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids, green_pid) == DMStateToState(ws'))
        // Property: Commutative diagram to ExternalObjsActivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    {
        var result := DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
        ws' := result.0;
        ws_d := result.1;
        if(ws_d)
        {
            var new_objects := ws'.objects;
            var new_subjects := ws'.subjects;
            var tds' := new_objects.tds;
            assert ws'.red_pid == ws.red_pid;

            Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, td_ids, fd_ids, do_ids);
            // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
            var toactivate_s_ids:set<Subject_ID> := {};
            var toactivate_td_ids := td_ids;
            var toactivate_fd_ids := fd_ids;
            var toactivate_do_ids := do_ids;

            Lemma_ExternalObjsActivate_AllObjsToBeActivatedAreExternalObjs(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
            Lemma_ExternalObjsActivate_HCodedTDsAreUnchanged(k, k.subjects.devs, tds', td_ids);
            assert SubjObjActivate_PropertiesOfNewTDs(k, new_objects, toactivate_td_ids, green_pid);
            assert SubjObjActivate_PropertiesOfNewFDs(k, new_objects, toactivate_fd_ids, green_pid);
            assert SubjObjActivate_PropertiesOfNewDOs(k, new_objects, toactivate_do_ids, green_pid);
            assert SubjObjActivate_PropertiesOfNewSubjs(k, k.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid); 

            Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, k.subjects.devs, new_objects, toactivate_td_ids, green_pid);

            assert P_DMAndNewDM_SameObjectID(ws, ws');
            assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

            // Prove common validity properties
            Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

            Lemma_NewDM_SameSubjObjIDs(ws, ws');
            Lemma_NewDM_SameSubjObjOwnership(ws, ws');

            // Prove k' == DMStateToState(ws')
            Lemma_DM_ExternalObjActivate_ProveCheckOfDevActivateInK(ws, k, td_ids, fd_ids, do_ids, green_pid);
            
            var k', d := ExternalObjsActivate(k, td_ids, fd_ids, do_ids, green_pid);
            assert d == true;
            assert k' == DMStateToState(ws');

            // Prove DM_IsValidState_SubjsObjsPIDs(ws')
            Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
            assert DM_IsValidState_SubjsObjsPIDs(ws');

            // Prove DM_IsValidState(ws')
            Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
            assert DM_IsValidState(ws');

            // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
            Lemma_NewDM_SubjObjActivate_FulfillSI2(ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, green_pid);
            Lemma_NewDMFromNewK_FulfillSI3(ws', k');
            assert DM_IsSecureState_SI3(ws');
            Lemma_NewDMFromNewK_FulfillSI1(ws', k');
            assert DM_IsSecureState(ws');

            // Prove DM_CalcNewState() == (ws', ws_d)
            ghost var result1 := DM_CalcNewState(ws, DM_ExternalObjsActivateToGreenPartitionOp(td_ids, fd_ids, do_ids, green_pid));
            assert result1 == DM_ExternalObjsActivateToGreenPartition_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
            assert result1 == (ws', ws_d);
        }
        else
        {
            assert ws' == ws;
            assert ws_d == false;
        }
    }
}




//******** DrvDeactivate ********//
// Operation: Deactivate a driver from a green partition
// [NOTE] Red drivers do not need to be deactivated/activated, because they do
// not need to be moved to green partitions
method DM_GreenDrvDeactivate(
    ws:DM_State, 
    drv_sid:Subject_ID // ID of the driver to be activated
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Drv_ID(drv_sid) in ws.subjects.drvs
    requires DM_SubjPID(ws.subjects, drv_sid) != NULL
    requires DM_SubjPID(ws.subjects, drv_sid) != ws.red_pid
        // Requirement: The driver must be in a green partition

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid)
    ensures P_DM_OpsProperties(ws, DM_GreenDrvDeactivateOp(drv_sid))
    ensures DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    ensures DMStateToState(ws).subjects.drvs[Drv_ID(drv_sid)].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)
        // Property needed by the following property
    ensures (ws_d == true ==> P_DrvDeactivate_ModificationToState(DMStateToState(ws), drv_sid, DMStateToState(ws')))

    ensures (ws_d == true ==> DrvDeactivate_Func(DMStateToState(ws), drv_sid) == DMStateToState(ws'))
        // Property: Commutative diagram to DrvDeactivate in the abstract model
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

    var result := DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        {
            assert pid != NULL;
            assert pid != ws.red_pid;
                
            assert DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws);
            Lemma_DM_GreenDrvDeactivate_ObjectsToBeDeactivatedAreInSamePartitionWithDrv(ws, drv_id,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

            // Prove the condition saves us from checking CAS
            //// Build CAS for K
            Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(k, {ActiveTDsState(k)});
            var k_cas_for_dev_in_green := BuildCAS(k, KToKParams(k), {ActiveTDsState(k)});
            Lemma_GreenDrvDeactivate_HCodedTDsAreNotBeingDeactivated(k, drv_id);
            Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs(ws, k, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, pid); 
            assert DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
                // Property: Ensure no active device in the same partition with the driver 
                // has transfers to any objects of the driver

            Lemma_DM_ObjsDeactivate_ProveCheckOfObjDeactivateInK(ws, k, pid,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
        }
        var k', d := DrvDeactivate(k, drv_sid);
        assert d == true;
        assert k' == DMStateToState(ws');
        
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        ghost var result1 := DM_CalcNewState(ws, DM_GreenDrvDeactivateOp(drv_sid));
        assert result1 == DM_GreenDrvDeactivate_InnerFunc(ws, drv_sid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}




//******** DevDeactivate ********//
// Operation: Deactivate a device from red or green partitions
method DM_DevDeactivate(
    ws:DM_State, 
    dev_sid:Subject_ID // ID of the device to be deactivated
) returns (ws':DM_State, ws_d:bool)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires Dev_ID(dev_sid) in ws.subjects.devs
    requires DM_SubjPID(ws.subjects, dev_sid) != NULL
        // Requirement: the device must be active
    requires DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid 
                ==> P_OtherRedDevsHaveNoTransferToGivenRedDevAtAnyTime(ws, Dev_ID(dev_sid))
        // Requirement: If the device is in red, then no other red device has 
        // transfers to any objects of the device to be deactivated
        // [Note] This is not a protection constraint, because we can check it 
        // in this operation. Thus, this statement is not assumption, it is
        // just a check move into precondition.

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')
    
    ensures (ws', ws_d) == DM_DevDeactivate_InnerFunc(ws, dev_sid)
    ensures P_DM_OpsProperties(ws, DM_DevDeactivateOp(dev_sid))
    ensures DM_CalcNewState(ws, DM_DevDeactivateOp(dev_sid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    ensures DMStateToState(ws).subjects.devs[Dev_ID(dev_sid)].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)
        // Property needed by the following property
    ensures (ws_d == true ==> P_DevDeactivate_ModificationToState(DMStateToState(ws), dev_sid, DMStateToState(ws')))

    ensures (ws_d == true ==> DevDeactivate_Func(DMStateToState(ws), dev_sid) == DMStateToState(ws'))
        // Property: Commutative diagram to DevDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_K_ValidState_Dev_Property(k, Dev_ID(dev_sid));

    var dev_id := Dev_ID(dev_sid);
    var dev_state := ws.subjects.devs[dev_id];

    var todeactivate_td_ids := ws.subjects.devs[dev_id].td_ids;
    var todeactivate_fd_ids := ws.subjects.devs[dev_id].fd_ids;
    var todeactivate_do_ids := ws.subjects.devs[dev_id].do_ids;
    var pid := DM_SubjPID(ws.subjects, dev_sid);
    
    var result := DM_DevDeactivate_InnerFunc(ws, dev_sid);
    ws' := result.0;
    ws_d := result.1; 
    if(ws_d)
    {
        var tds_owned_by_dev:set<TD_ID> := ws.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := ws.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_dev:set<DO_ID> := ws.subjects.devs[dev_id].do_ids;

        var new_objects := ws'.objects;
        var new_subjects := ws'.subjects;
        var tds' := new_objects.tds;
        assert ws'.red_pid == ws.red_pid;

        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        if(DM_SubjPID(ws.subjects, dev_sid) == ws.red_pid)
        {
            Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_IfDevIsInRed(ws, k, dev_sid);
        }
        else
        {
            assert DM_SubjPID(ws.subjects, dev_sid) != NULL;
            assert DM_SubjPID(ws.subjects, dev_sid) != ws.red_pid;

            // Prove the condition saves us from checking CAS
            //// Build CAS for K
            Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(k, {ActiveTDsState(k)});
            var k_cas_for_dev_in_green := BuildCAS(k, KToKParams(k), {ActiveTDsState(k)});
            Lemma_DevDeactivate_HCodedTDsOfOtherDevsAreNotBeingDeactivated(k, dev_id);
            Lemma_DM_DevDeactivate_NoOtherGreenTDsRefObjsOfDevToBeDeactivated_ThenNoOtherDevHasTransferToDev(ws, k, dev_id, 
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, pid); 
            assert DM_DevDeactivate_ChkNoOtherDevHasTransferToDevToBeDeactivated_IfTheDevIsInGreen(ws, k, dev_sid, k_cas_for_dev_in_green, {ActiveTDsState(k)});
                // Check the CAS only when the device to be deactivated is in green
                // Ensure no active device in the same partition with the device 
                // has transfers to any objects of the device

            Lemma_DM_DevDeactivate_ProveCheckOfDevDeactivateInK_IfDevIsInGreen(ws, k, dev_sid, k_cas_for_dev_in_green, {ActiveTDsState(k)});
        }
        var k', d := DevDeactivate(k, dev_sid);
        assert d == true;
        assert k' == DMStateToState(ws');
            
        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_DevDeactivate_OtherDevsHaveUnchangedPIDs(ws, ws', dev_id);
        Lemma_NewDM_IsValidState_DevDeactivate_DevsActivateCond(ws, ws', dev_id);
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_DevDeactivate_ActiveDevsInNewKIsSubsetOfOnesInK(k, k', dev_id, dev_state);
        Lemma_DM_DevDeactivate_PropertiesOfObjsToBeDeactivated(ws, dev_id,
                todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');
        
        // Prove DM_CalcNewState() == (ws', ws_d)
        ghost var result1 := DM_CalcNewState(ws, DM_DevDeactivateOp(dev_sid));
        assert result1 == DM_DevDeactivate_InnerFunc(ws, dev_sid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}




//******** ExternalObjsDeactivate ********//
// Operation: Deactivate wimp USB TDs, external wimp FDs and external wimp DOs
// from the given green partition
// [NOTE] External objects in red do not need to be deactivated/activated,
// because these objects do not need to be moved to green partitions
method DM_GreenExternalObjsDeactivate(
    ws:DM_State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, //  IDs of the objects to be deactivated
    green_pid:Partition_ID // The green partition that holds these objects
) returns (ws':DM_State, ws_d:bool)
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

    ensures ws'.red_pid == ws.red_pid
        // Property needed for wimpy kernel operations
    ensures DM_IsValidState(ws') && DM_IsSecureState(ws')
    ensures DM_IsSecureOps(ws, ws')

    ensures (ws', ws_d) == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid)
    ensures P_DM_OpsProperties(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid))
    ensures DM_CalcNewState(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid)) == (ws', ws_d)
        // Prove DM_CalcNewState end up at the result state

    ensures IsValidState(DMStateToState(ws)) && IsSecureState(DMStateToState(ws))
    ensures td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    ensures fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    ensures do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)
        // Property needed by the following property
    ensures (ws_d == true 
                ==> P_ExternalObjsDeactivate_ModificationToState(DMStateToState(ws), DMStateToState(ws'),
                        td_ids, fd_ids, do_ids))

    ensures (ws_d == true ==> ExternalObjsDeactivate_Func(DMStateToState(ws), td_ids, fd_ids, do_ids) == DMStateToState(ws'))
        // Property: Commutative diagram to ExternalObjsDeactivate in the abstract model
{
    var k := DMStateToState(ws);

    Lemma_DMStateToState_SecureK(ws, k);
    assert IsValidState(k) && IsSecureState(k);

    var todeactivate_td_ids := td_ids;
    var todeactivate_fd_ids := fd_ids;
    var todeactivate_do_ids := do_ids;

    var result := DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
    ws' := result.0;
    ws_d := result.1;
    if(ws_d)
    {
        assert P_DMAndNewDM_SameObjectID(ws, ws');
        assert P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws');

        // Prove common validity properties
        Lemma_NewDM_AlwaysFulfillMostValidityProperties(ws, ws');

        Lemma_NewDM_SameSubjObjIDs(ws, ws');
        Lemma_NewDM_SameSubjObjOwnership(ws, ws');

        // Prove k' == DMStateToState(ws')
        // Prove the condition saves us from checking CAS
        //// Build CAS for K
        Lemma_SubjObjDeactivate_ProvePreConditionsOfBuildCAS(k, {ActiveTDsState(k)});
        var k_cas_for_dev_in_green := BuildCAS(k, KToKParams(k), {ActiveTDsState(k)});
        Lemma_ExternalObjsDeactivate_HCodedTDsAreNotBeingDeactivated(ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_DM_ObjDeactivate_NoOtherGreenTDsRefObjsToBeDeactivated_ThenNoOtherDevHasTransferToTheseObjs(ws, k, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, green_pid); 
        assert DM_ObjDeactivate_ChkNoOtherDevHasTransferToObjToBeDeactivated_IfTheObjIsInGreen(ws, k,
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
            // Property: Ensure no active device in the same partition with the objects 
            // has transfers to any of these objects 

        Lemma_DM_ExternalWimpObjsDeactivate_ProveCheckOfObjDeactivateInK(ws, k, green_pid,
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas_for_dev_in_green, {ActiveTDsState(k)});
        Lemma_ExternalObjsActivateDeactivate_NoSubjOwnExternalObj_Interpretation(ws, k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        var k', d := ExternalObjsDeactivate(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid);
        assert d == true;
        assert k' == DMStateToState(ws');

        // Prove DM_IsValidState_SubjsObjsPIDs(ws')
        Lemma_NewDMFromNewK_SubjsOwnObjsThenInSamePartition_Prove(ws', k');
        assert DM_IsValidState_SubjsObjsPIDs(ws');

        // Prove DM_IsValidState(ws')
        Lemma_NewDM_IsValidState_DevsActivateCond_IfDevPIDsAreUnchanged(ws, ws');
        assert DM_IsValidState(ws');

        // Prove DM_IsSecureState(ws') and DM_IsSecureOps(ws, ws')
        Lemma_NewDM_SubjObjDeactivate_FulfillSI2(ws, k, ws', k', todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, green_pid);
        Lemma_NewDMFromNewK_FulfillSI3(ws', k');
        assert DM_IsSecureState_SI3(ws');
        Lemma_NewDMFromNewK_FulfillSI1(ws', k');
        assert DM_IsSecureState(ws');

        // Prove DM_CalcNewState() == (ws', ws_d)
        ghost var result1 := DM_CalcNewState(ws, DM_GreenExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, green_pid));
        assert result1 == DM_GreenExternalObjsDeactivate_InnerFunc(ws, td_ids, fd_ids, do_ids, green_pid);
        assert result1 == (ws', ws_d);
    }
    else
    {
        assert ws' == ws;
        assert ws_d == false;
    }
}