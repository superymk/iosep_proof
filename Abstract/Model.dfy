include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"
include "Lemmas_SubjActivate_Ops.dfy"
include "Lemmas_SubjActivate_ReachableTDsStates.dfy"
include "Lemmas_SubjDeactivate_Ops.dfy"
include "./BuildCAS/BuildCAS.dfy"
include "SecurityProperties_Ops.dfy"

//******** 10 Operations of the Model ********//
// Operation: Driver reads a set of objects, and copies the values if needed
// [Note] If the read results are copied to other objects, the source and 
// destination objects also need to be specified in <tds/fds/dos_dst_src>
method DrvRead(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires SubjPID(k, drv_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires read_objs <= AllObjsIDs(k.objects)

    requires DrvRead_ReadSrcObjsToDestObjs_PreConditions(k, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    
    ensures forall dev_id :: dev_id in k'.subjects.devs
        ==> k'.subjects.devs[dev_id].hcoded_td_id in k'.objects.tds
        // Property needed by "ensures IsSecureOps(k, k')"
    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')

    ensures d == true ==> P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(k, drv_sid, 
                                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property: All read objects and objects to store read results must be 
        // in the same partition with the driver
    ensures P_OpsProperties_DrvReadOp(k, DrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        
    ensures d == true <==> P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    ensures (d == true ==> P_DrvDevWrite_ModificationToState(k, 
                                DrvDevRead_ReplaceSrcTDWithVal(k, tds_dst_src), 
                                DrvDevRead_ReplaceSrcFDWithVal(k, fds_dst_src), 
                                DrvDevRead_ReplaceSrcDOWithVal(k, dos_dst_src), k'))
    ensures d == false ==> k' == k
{
    if (forall o_id :: o_id in read_objs  
            ==> SubjPID(k, drv_sid) == ObjPID(k, o_id))
                // The driver and the objects must be in the same partition
    {
        var td_id_val_map := DrvDevRead_ReplaceSrcTDWithVal(k, tds_dst_src);
        var fd_id_val_map := DrvDevRead_ReplaceSrcFDWithVal(k, fds_dst_src);
        var do_id_val_map := DrvDevRead_ReplaceSrcDOWithVal(k, dos_dst_src);

        k', d := DrvWrite(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        if(d)
        {
            assert P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
            assert P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src); 
        }
        else
        {
            assert k' == k;
            assert d == false;
            assert !P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
        }
    }
    else
    {
        k' := k;
        d := false;
        assert !P_DrvRead_ReturnTrue_Def(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    }
    
    Lemma_P_OpsProperties_DrvReadOp_Prove(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, k' ,d);
}

// Operation: Device reads a set of objects, and copies the values if needed
// [Note] If the read results are copied to other objects, the source and 
// destination objects also need to be specified in <tds/fds/dos_dst_src>
method DevRead(
    k:State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active
    requires forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)
        // Requirement: The read transfers must be defined in TDs that can be
        // read by the device

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    
    ensures forall dev_id :: dev_id in k'.subjects.devs
                ==> k'.subjects.devs[dev_id].hcoded_td_id in k'.objects.tds
        // Property needed by "ensures IsSecureOps(k, k')"
    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')

    ensures P_K_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(k, dev_sid, 
                read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
        // Property 4: All read objects and objects to store read results must be 
        // in the same partition with the driver
    ensures P_OpsProperties_DevReadOp(k, DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
        
    ensures d == true
    ensures (d == true ==> P_DrvDevWrite_ModificationToState(k, 
                                DrvDevRead_ReplaceSrcTDWithVal(k, tds_dst_src), 
                                DrvDevRead_ReplaceSrcFDWithVal(k, fds_dst_src), 
                                DrvDevRead_ReplaceSrcDOWithVal(k, dos_dst_src), k'))
    ensures d == false ==> k' == k
{
    var td_id_val_map := DrvDevRead_ReplaceSrcTDWithVal(k, tds_dst_src);
    var fd_id_val_map := DrvDevRead_ReplaceSrcFDWithVal(k, fds_dst_src);
    var do_id_val_map := DrvDevRead_ReplaceSrcDOWithVal(k, dos_dst_src);

    k', d := DevWrite(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    
    Lemma_SecureState_FulfillsStatePropertyCorollary1(k);
    Lemma_StatePropertyCorollary1_ImpliesCorollary2(k);
    
    forall o_id | o_id in read_objs
        ensures o_id in AllObjsIDs(k.objects)
        ensures ObjPID(k, o_id) == SubjPID(k, dev_sid)
    {
        assert DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id) != {};
    }
    
    Lemma_P_OpsProperties_DevReadOp_Prove(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, k' ,d);
}

// Operation: Device writes a set of objects with values
// [NOTE] Differences from the DevWrite operation in the paper/slides:
//    (1) This method takes <td_id_val_map>, <fd_id_val_map> and <do_id_val_map>
//        instead of <obj_id_val_map> in the paper/slides.
// (needs 200s to verify)
method DevWrite(
    k:State, 
    dev_sid:Subject_ID, // ID of the device issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>  // IDs of DOs, and values to be written
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active

    requires forall td_id2 :: td_id2 in td_id_val_map
                ==> DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, td_id2, td_id_val_map[td_id2])
    requires forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, fd_id2, fd_id_val_map[fd_id2])
    requires forall do_id2 :: do_id2 in do_id_val_map
                ==> DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, do_id2, do_id_val_map[do_id2])
        // Requirement: The write transfers must be defined in TDs that can be
        // read by the device

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)
        // Property 3: Written TDs, FDs and DOs are in the I/O state. 
        // Note: If not proving this property, then it is possible the o_id is 
        // in AllObjsIDs(k), but the TD_ID(o_id) in td_id_val_map is not in 
        // k.objects.tds. Same issue for FDs and DOs.
    ensures P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property 4: All written objects are in the same partition with the device
    ensures P_OpsProperties_DevWriteOp(k, DevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
    
    ensures forall td_id :: td_id in td_id_val_map
            ==> td_id !in AllHCodedTDIDs(k.subjects)
        // (For Model Interpretation) Property 5: Hardcoded TDs are not modified
    ensures AllActiveTDs(k') == AllActiveTDs(k)
        // (For Model Interpretation) Property 6: Same set of active TDs
    ensures IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(KToKParams(k), Dev_ID(dev_sid), ActiveTDsState(k), ActiveTDsState(k'))
    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(KToKParams(k), Dev_ID(dev_sid), ActiveTDsState(k), ActiveTDsState(k'))
        // (For Model Interpretation) Property 7: ActiveTDsState(k) --> ActiveTDsState(k')
    ensures d == true ==> DevWrite_ClosureRelationship(k, k')
        // (For Model Interpretation) Property 8: Correct relationship between closures in k and k'
        
    ensures d == true
    ensures (d == true ==> P_DrvDevWrite_ModificationToState(k, td_id_val_map, fd_id_val_map, do_id_val_map, k'))
    ensures d == false ==> k' == k
{
    // Prove property 3 and 4
    Lemma_DevWrite_DevAccessObjsInSystemAndAccessIsAllowed(
        k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map;

    var k'_subjects := k.subjects;
    var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(k.objects.tds);
    var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(k.objects.fds);
    var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(k.objects.dos);
    ghost var k'_tds_to_all_states := k.tds_to_all_states;
    var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

    var tds' := WriteTDsVals(k.objects.tds, td_id_val_map);
    var fds' := WriteFDsVals(k.objects.fds, fd_id_val_map);
    var dos' := WriteDOsVals(k.objects.dos, do_id_val_map);

    assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
    assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
    assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

    var k'_active_tds := AllActiveTDs_SlimState(tds');
    var k'_active_tds_state := ActiveTDsState_SlimState(tds');
    var k'_objects := Objects(tds', fds', dos');

    // Build k'
    k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
    d := true;

    var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

    // Prove common properties hold for k'_params and state variables of k' in all operations
    var k_params := KToKParams(k);
    Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
    Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

    Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
    Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

    // Prove all preconditions for buliding <reachable_active_tds_states> for k'
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id);
    Lemma_DevWrite_HCodedTDsAreUnmodified(k, td_id_val_map, k'_objects.tds);
    Lemma_DrvDevWrite_NewKParams_SameWithKParams(k, k'_subjects, k'_objects, k'_params);
    assert k'_params == k_params;
    assert FindAllTDsReadByDev_KParams_PreConditions(k'_params);

    Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
    assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                ==> (k'_active_tds_state == tds_state2);
    assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

    Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);
    
    // Build <reachable_active_tds_states> for k'
    var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
            k'_params, k'_tds_to_all_states[k'_active_tds],
            k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
    var tds_states := GetExploredTDsStates(explored_tds_states, 0);

    Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
    Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
    assert KToKParams(k') == KToKParams(k);

    assert AllActiveTDs(k') == AllActiveTDs(k);
    Lemma_SameTDIDsInTDsStateIfTDIDsSetIsSame(ActiveTDsState(k), k'_active_tds_state);
    assert TDsStateGetTDIDs(k'_active_tds_state) == TDsStateGetTDIDs(ActiveTDsState(k));
    assert AllActiveDevs(k) == k'_active_devs;
    
    // Prove s == true
    Lemma_DrvDevWrite_WrittenTDsMustBeActiveInK(k, td_id_val_map);
    Lemma_TDsStatesDiffIsIncludedInTDIDValMapOfWriteTDs(ActiveTDsState(k), k'_active_tds_state, td_id_val_map);

    Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k.subjects, Dev_ID(dev_sid));
    Lemma_DevWrite_CurrentTDsStateReachNewTDsStateInOneStep(k, Dev_ID(dev_sid), td_id_val_map, k'_active_tds_state);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, 
                Dev_ID(dev_sid), ActiveTDsState(k), k'_active_tds_state);
    Lemma_TDsStateGetTDIDs_SameResultWithMapGetKeys(k'_active_tds_state);
    assert TDsStateGetTDIDs(k'_active_tds_state) == AllActiveTDs(k');
    Lemma_DevWrite_NewReachableActiveTDsStatesIsSubsetOfTheOneInK(k, k_params, Dev_ID(dev_sid), k', k'_active_tds_state);

    Lemma_ValidState_FulfillCanActiveDevReadActiveTDPreConditions(k);
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant(k);
    Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Equivilant_More(k);
    Lemma_DevWrite_ReachableActiveTDsStatesFromNewKActiveTDsStatesMustBeSecure(k, k_params, k'_active_tds_state);
    Lemma_ActiveTDsUnchanged_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(k, k_params, k'_active_tds_state, tds_states, s);
    assert s == true;

    // Prove IsValidState_Objects(k')
    Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
    Lemma_NewK_FulfillIsValidStateObjects(k, k');
    assert IsValidState_Objects(k');

    // Prove IsValidState_Subjects(k')
    assert IsValidState_Subjects(k');

    // Prove IsValidState_ReachableTDsStates(k')
    Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
    Lemma_SameSubjObjPIDsIfSubjPIDsAreUnchanged(k, k');
    Lemma_UnmodifiedSubjObjPIDs_NewKFulfillIsValidState_SubjsOwnObjsThenInSamePartition(k, k');
    Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
        k', tds_states);
    Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
        k', k'_params, tds_states, s);

    assert IsValidState(k'); 
    assert IsSecureState(k');
    assert IsSecureOps(k, k');
    
    Lemma_P_OpsProperties_DevWriteOp_Prove(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k' ,d);
}

// Operation: Create an I/O partition
method EmptyPartitionCreate(
    k:State, 
    new_pid:Partition_ID // The ID of the new partition
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_EmptyPartitionCreateOp(k, EmptyPartitionCreateOp(new_pid))

    ensures EmptyPartitionCreate_Prop(k, new_pid, k', d)
    ensures d == false ==> k' == k
{
    if ((new_pid != NULL) &&
        (new_pid !in k.pids))
    {
        // Add the ID of the creating partition into the new state
        var pids' := k.pids + {new_pid};

        var k'_subjects := k.subjects;
        var k'_objects := k.objects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(k.objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(k.objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(k.objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        var tds' := k.objects.tds;
        var fds' := k.objects.fds;
        var dos' := k.objects.dos;

        // Build k'
        k' := State(k'_subjects, k'_objects, pids', k.tds_to_all_states);
        d := true;

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        assert k'_params == k_params;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        // Prove s == true
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_SameSubjObjPIDsIfSubjPIDsAreUnchanged(k, k');
        Lemma_UnmodifiedSubjObjPIDs_NewKFulfillIsValidState_SubjsOwnObjsThenInSamePartition(k, k');
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');
    }
    else
    {
        k' := k;
        d := false;
    }
    
    Lemma_P_OpsProperties_EmptyPartitionCreateOp_Prove(k, new_pid, k' ,d);
}

// Operation: Destroy an I/O partition
// (needs 160s to verify)
method EmptyPartitionDestroy(
    k:State, 
    pid:Partition_ID // The ID of the partition to be destroyed
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_EmptyPartitionDestroyOp(k, EmptyPartitionDestroyOp(pid))
    
    ensures EmptyPartitionDestroy_Prop(k, pid, k', d)
    ensures d == false ==> k' == k
{
    if ((pid != NULL) &&
        (pid in k.pids) &&
        (forall s_id :: s_id in AllSubjsIDs(k.subjects) ==> SubjPID(k, s_id) != pid) &&
        (forall o_id :: o_id in AllObjsIDs(k.objects) ==> ObjPID(k, o_id) != pid))
    {
        // Remove the ID of the destroying partition
        var pids' := k.pids - {pid};

        var k'_subjects := k.subjects;
        var k'_objects := k.objects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(k.objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(k.objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(k.objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        var tds' := k.objects.tds;
        var fds' := k.objects.fds;
        var dos' := k.objects.dos;

        // Build k'
        k' := State(k'_subjects, k'_objects, pids', k.tds_to_all_states);
        d  := true;

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        assert k'_params == k_params;
        assert FindAllTDsReadByDev_KParams_PreConditions(k'_params);

        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);
        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert KToKParams(k') == KToKParams(k);

        // Prove s == true
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_SameSubjObjPIDsIfSubjPIDsAreUnchanged(k, k');
        Lemma_UnmodifiedSubjObjPIDs_NewKFulfillIsValidState_SubjsOwnObjsThenInSamePartition(k, k');
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);
        
        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');
    }
    else
    {
        k' := k;
        d := false;
    }
    
    Lemma_P_OpsProperties_EmptyPartitionDestroyOp_Prove(k, pid, k' ,d);
}

// Operation: Activate a driver into a partition
// (needs 160s to verify)
method DrvActivate(
    k:State, 
    drv_sid:Subject_ID, // ID of the activating driver
    pid:Partition_ID // ID of the partition to activate the driver into
) returns (k':State,d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires pid != NULL

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_DrvActivateOp(k, DrvActivateOp(drv_sid, pid))
    
    ensures (d == true ==> P_DrvActivate_ModificationToState(k, drv_sid, pid, k'))
    ensures (d == true 
                <==> (SubjPID(k, drv_sid) == NULL) && (pid in k.pids))
    ensures (d == true
                ==> SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, k.subjects.drvs[Drv_ID(drv_sid)].td_ids, pid) &&
                    SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, k.subjects.drvs[Drv_ID(drv_sid)].fd_ids, pid) &&
                    SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, k.subjects.drvs[Drv_ID(drv_sid)].do_ids, pid))
    ensures d == false ==> k' == k
{ 
    var drv_id := Drv_ID(drv_sid);
    var drv_state := IDToDrv(k, drv_id);

    if((SubjPID(k, drv_sid) == NULL) && (pid in k.pids))
    {
        // Set the driver's partition ID to be <pid>
        var new_drv_state := Drv_State(pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
        var new_drvs := k.subjects.drvs[drv_id := new_drv_state];
        
        // Construct k'.subjects
        var new_subjects := Subjects(new_drvs, k.subjects.devs);

        // Construct k'.objects
        var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
        var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
        var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
        //// Clear the objects being activated (i.e., ClearObjs)
        var temp_tds := ClearTDs(k.objects.tds, tds_owned_by_drv);
        var temp_fds := ClearFDs(k.objects.fds, fds_owned_by_drv);
        var temp_dos := ClearDOs(k.objects.dos, dos_owned_by_drv);
        //// Modify the PID of these objects (i.e., SetObjsPIDs)
        var tds' := SetTDsPIDs(temp_tds, tds_owned_by_drv, pid);
        var fds' := SetFDsPIDs(temp_fds, fds_owned_by_drv, pid);
        var dos' := SetDOsPIDs(temp_dos, dos_owned_by_drv, pid);
        var new_objects := Objects(tds', fds', dos');

        // Build <reachable_active_tds_states> for k'
        var k'_subjects := new_subjects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(new_objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(new_objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(new_objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_objects := new_objects;

        // Build k'
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;

        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {drv_sid};
        var toactivate_td_ids := tds_owned_by_drv;
        var toactivate_fd_ids := fds_owned_by_drv;
        var toactivate_do_ids := dos_owned_by_drv;

        Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, drv_id, toactivate_td_ids);
        assert SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        // Prove common properties hold for k'_params and state variables of k' in all operations
        assert K_UniqueIDsAndOwnedObjs(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos));

        var k_params := KToKParams(k);
        Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, k'_subjects.devs, k'_objects, toactivate_td_ids, pid);
        assert forall dev_id :: dev_id in k'_subjects.devs
                ==> tds'[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val;  
        Lemma_DrvActivate_ObjsIDsInDrvsAreUnchanged(k, k'_subjects, drv_id, drv_state, new_drv_state);
        Lemma_SubjObjActivate_NewKParams_HasUnmodifiedVarsFromKParams(k, k'_subjects, k'_objects, k'_params);

        Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs(k, k'_subjects, k'_objects, 
            k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params, k'_params);

        Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects);
        assert forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        Lemma_DrvActivate_SameActiveDevsInKAndNewK(k, k'_subjects, drv_id, drv_state, new_drv_state);
        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert AllActiveDevs(k) == k'_active_devs;
        assert AllActiveDevs(k') == k'_active_devs;

        // Prove s == true
        assert k'_params == KToKParams(k');
        assert SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k');
        Lemma_SubjObjActivate_FulfillCommonPreConditionsOfKAndNewK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
        Lemma_SubjObjActivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
            k', k'_params, k'_active_devs, k'_active_tds_state,
            explored_tds_states, tds_states);
        Lemma_SubjObjActivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, tds_states, s);
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        // Prove SI2
        Lemma_SubjObjActivate_NewK_FulfillSI2(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        // Prove TC2.1
        Lemma_DrvDevActivate_NonHCodedTDsAreClearedAsTC21(k, AllHCodedTDIDs(k'_subjects), k'.objects, toactivate_td_ids, pid);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');
    }
    else
    {
        k' := k;
        d  := false;
    }
    
    Lemma_P_OpsProperties_DrvActivateOp_Prove(k, drv_sid, pid, k' ,d);
}

// Operation: Deactivate a driver
// (needs 800s to verify)
method DrvDeactivate(
    k:State, drv_sid:Subject_ID
) returns (k':State,d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_DrvDeactivateOp(k, DrvDeactivateOp(drv_sid))
    
    ensures (d == true ==> P_DrvDeactivate_ModificationToState(k, drv_sid, k'))
    ensures d == true <==> P_DrvDeactivate_ReturnTrue_Def(k, drv_sid)
    ensures (d == true
                ==> SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, k.subjects.drvs[Drv_ID(drv_sid)].td_ids) &&
                    SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, k.subjects.drvs[Drv_ID(drv_sid)].fd_ids) &&
                    SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, k.subjects.drvs[Drv_ID(drv_sid)].do_ids))
    
    ensures d == false ==> k' == k
{
    var drv_id := Drv_ID(drv_sid);
    var drv_state := IDToDrv(k, drv_id);

    // Calculate reachable snapshots of active TDs in K
    var k_tds_states := ValidSecureState_ReachableStatesOfActiveTDs(k);

    // Build CAS for K
    // CAS is a table showing all potential transfers from active subjects to 
    // active objects. In implementation, CAS is a function of the transitive
    // closure. Thus, checking these transfers in the CAS equals to checking 
    // them in transitive closure
    var k_cas := BuildCAS(k, KToKParams(k), k_tds_states);

    if((SubjPID(k, drv_sid) != NULL) && 
        (forall o_id, drv_id :: o_id in OwnObjIDs(k, drv_sid) && drv_id in AllActiveDevs(k) 
            ==> IsInCAS(k_cas, drv_id, o_id) && CASGetAModes(k_cas, drv_id, o_id) == {}))
                    // Active devices have no transfers to any objects of the 
                    // deactivating driver
    {
        // Set the driver's partition ID to be NULL
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

        // Build <reachable_active_tds_states> for k'
        var k'_subjects := new_subjects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(new_objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(new_objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(new_objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);
  
        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_objects := new_objects;

        // Build k'
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;

        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove properties of k'_subjects, k'_objects, due to todeactivate_td/fd/do_ids and todeactivate_s_ids
        var todeactivate_s_ids:set<Subject_ID> := {drv_sid};
        var todeactivate_td_ids := tds_owned_by_drv;
        var todeactivate_fd_ids := fds_owned_by_drv;
        var todeactivate_do_ids := dos_owned_by_drv;

        Lemma_DrvDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK_PreConditions(
            k, k'_subjects, k'_objects, todeactivate_s_ids, drv_id, new_drv_state);
        Lemma_DrvDevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK(
            k, k'_subjects, todeactivate_s_ids);
        Lemma_DrvDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
            k, k'_subjects, k'_objects, k_cas, drv_id, new_drv_state);
        Lemma_DrvDeactivate_ProveSubjsObjsFulfillProperties(
            k, k'_subjects, k'_objects, k_cas, drv_id, new_drv_state);

        Lemma_DrvDeactivate_SameSetOfActiveDevsInNewKAndK(k, k'_subjects, drv_id, new_drv_state);
        assert AllActiveDevs(k) == k'_active_devs;

        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_SubjObjDeactivate_ProveNewKTDsToAllStatesContainsAllSetsOfTDs(k, tds', k'_objs_td_ids, k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        Lemma_DrvDeactivate_OwnershipOfObjsIsPreserved(k, k'_subjects, drv_id, new_drv_state);
        assert forall drv_id :: drv_id in k'_subjects.devs
                ==> tds'[k.subjects.devs[drv_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[drv_id].hcoded_td_id].val;
        Lemma_SubjObjDeactivate_NewKParams_HasUnmodifiedVarsFromKParams(k, k'_subjects, k'_objects, k'_params);

        Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs(k, k'_subjects, k'_objects, k'_params, 
            todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        
        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params, k'_params);

        Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects);
        Lemma_NewK_HCodedTDsOfAllActiveDevsRefObjInDevs(k, k_params, k'_params, k'_subjects, k'_active_devs);
        assert forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert AllActiveDevs(k) == k'_active_devs;
        assert AllActiveDevs(k') == k'_active_devs;

        // Prove s == true
        assert k'_params == KToKParams(k');
        assert SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k');
        Lemma_SubjObjDeactivate_FulfillCommonPreConditionsOfKAndNewK(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_SubjObjDeactivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
            k', k'_params, k'_active_devs, k'_active_tds_state,
            explored_tds_states, tds_states);
        Lemma_SubjObjDeactivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, tds_states, s);
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        // Prove SI2
        Lemma_SubjObjDeactivate_NewK_FulfillSI2(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');

        Lemma_DrvDeactivate_ReturnTrue_ProveP_DrvDeactivate_ReturnTrue_Def(
            k, drv_id, drv_sid, k_cas, d);
    }
    else
    {
        k' := k;
        d  := false;

        Lemma_DrvDeactivate_ReturnFalse_ProveP_DrvDeactivate_ReturnTrue_Def(
            k, drv_id, drv_sid, k_cas, d);
    }
    
    Lemma_P_OpsProperties_DrvDectivateOp_Prove(k, drv_sid, k' ,d);
}

// Operation: Activate a device into a partition
// (needs 420s to verify)
method DevActivate(
    k:State, 
    dev_sid:Subject_ID, // ID of the activating device
    pid:Partition_ID // ID of the partition to activate the device into
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires pid != NULL

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_DevActivateOp(k, DevActivateOp(dev_sid, pid))
    
    ensures (d == true ==> P_DevActivate_ModificationToState(k, dev_sid, pid, k'))
    ensures (d == true <==> (SubjPID(k, dev_sid) == NULL) && (pid in k.pids) && Edev_Activate(k, Dev_ID(dev_sid)))
    ensures (d == true
                ==> SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, k.subjects.devs[Dev_ID(dev_sid)].td_ids, pid) &&
                    SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, k.subjects.devs[Dev_ID(dev_sid)].fd_ids, pid) &&
                    SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, k.subjects.devs[Dev_ID(dev_sid)].do_ids, pid))
                    
    ensures d == false ==> k' == k
{
    var dev_id := Dev_ID(dev_sid);
    var dev_state := IDToDev(k, dev_id);

    if((SubjPID(k, dev_sid) == NULL) && (pid in k.pids))
    {
        // Set the device's partition ID to be <pid>
        var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
        var new_devs := k.subjects.devs[dev_id := new_dev_state];

        // Construct k'.subjects
        var new_subjects := Subjects(k.subjects.drvs, new_devs);

        // Construct k'.objects
        var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
        var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
        var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
        //// Clear the objects (i.e., ClearObjs) being activated (except the 
        //// hardcoded TD)
        var toactive_hcoded_td_id := dev_state.hcoded_td_id;
        var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
        var temp_tds := ClearTDs(k.objects.tds, toclear_td_ids);
        var temp_fds := ClearFDs(k.objects.fds, fds_owned_by_dev);
        var temp_dos := ClearDOs(k.objects.dos, dos_owned_by_dev);
        //// Modify the PID of these objects (i.e., SetObjsPIDs)
        var tds' := SetTDsPIDs(temp_tds, tds_owned_by_dev, pid);
        var fds' := SetFDsPIDs(temp_fds, fds_owned_by_dev, pid);
        var dos' := SetDOsPIDs(temp_dos, dos_owned_by_dev, pid);
        var new_objects := Objects(tds', fds', dos');

        var s2 := Edev_Activate(k, dev_id);
        if(!s2)
        {    return k, false;}

        // Build <reachable_active_tds_states> for k'
        var k'_subjects := new_subjects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(new_objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(new_objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(new_objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);
        assert forall td_id :: td_id in tds_owned_by_dev
                ==> (td_id != dev_state.hcoded_td_id ==> tds'[td_id] == TD_State(pid, TD_Val(map[], map[], map[]))) &&
                    (td_id == dev_state.hcoded_td_id ==> tds'[td_id] == TD_State(pid, k.objects.tds[td_id].val));
                        // Among all TDs to be activated, only the hardcoded TD 
                        // do not have their value cleared

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_objects := new_objects;

        // Build k'
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;

        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {dev_sid};
        var toactivate_td_ids := tds_owned_by_dev;
        var toactivate_fd_ids := fds_owned_by_dev;
        var toactivate_do_ids := dos_owned_by_dev;

        Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_DevActivate_HCodedTDsToBeActivatedHaveUnmodifiedVals(k, tds', dev_id, toactivate_td_ids);
        assert SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        // Prove common properties hold for k'_params and state variables of k' in all operations
        assert K_UniqueIDsAndOwnedObjs(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos));

        var k_params := KToKParams(k);
        Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(k, k'_subjects.devs, k'_objects, toactivate_td_ids, pid);
        assert forall dev_id :: dev_id in k'_subjects.devs
                ==> tds'[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val;  
        Lemma_DevActivate_ObjsIDsInDevsAreUnchanged(k, k'_subjects, dev_id, dev_state, new_dev_state);
        Lemma_SubjObjActivate_NewKParams_HasUnmodifiedVarsFromKParams(k, k'_subjects, k'_objects, k'_params);

        Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs(k, k'_subjects, k'_objects, 
            k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params, k'_params);

        Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects);
        Lemma_NewK_HCodedTDsOfAllActiveDevsRefObjInDevs(k, k_params, k'_params, k'_subjects, k'_active_devs);
        assert forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert AllActiveDevs(k') == k'_active_devs;

        // Prove s == true
        assert k'_params == KToKParams(k');
        assert SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k');
        Lemma_SubjObjActivate_FulfillCommonPreConditionsOfKAndNewK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
        Lemma_SubjObjActivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
            k', k'_params, k'_active_devs, k'_active_tds_state,
            explored_tds_states, tds_states);
        Lemma_SubjObjActivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, tds_states, s);
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        // Prove SI2
        Lemma_SubjObjActivate_NewK_FulfillSI2(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        // Prove TC2.1
        Lemma_DrvDevActivate_NonHCodedTDsAreClearedAsTC21(k, AllHCodedTDIDs(k'_subjects), k'.objects, toactivate_td_ids, pid);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');
    }
    else
    {
        k' := k;
        d := false;
    }
    
    Lemma_P_OpsProperties_DevActivateOp_Prove(k, dev_sid, pid, k' ,d);
}

// Operation: Deactivate a device
// (need 640s to verify)
method DevDeactivate(
    k:State, dev_sid:Subject_ID
) returns (k':State,d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    
    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_DevDeactivateOp(k, DevDeactivateOp(dev_sid))
    
    ensures (d == true ==> P_DevDeactivate_ModificationToState(k, dev_sid, k'))
    ensures d == true <==> P_DevDeactivate_ReturnTrue_Def(k, dev_sid)
    ensures (d == true
                ==> SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, k.subjects.devs[Dev_ID(dev_sid)].td_ids) &&
                    SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, k.subjects.devs[Dev_ID(dev_sid)].fd_ids) &&
                    SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, k.subjects.devs[Dev_ID(dev_sid)].do_ids))
                    
    ensures d == false ==> k' == k
{
    var dev_id := Dev_ID(dev_sid);
    var dev_state := IDToDev(k, dev_id);

    // Calculate reachable snapshots of active TDs in K
    var k_tds_states := ValidSecureState_ReachableStatesOfActiveTDs(k);

    // Build CAS for K
    // CAS is a table showing all potential transfers from active subjects to 
    // active objects. In implementation, CAS is a function of the transitive
    // closure. Thus, checking these transfers in the CAS equals to checking 
    // them in transitive closure
    var k_cas := BuildCAS(k, KToKParams(k), k_tds_states);

    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    if((SubjPID(k, dev_sid) != NULL) &&
        (forall o_id, dev_id2 :: 
            (o_id in OwnObjIDs(k, dev_sid)) && 
            (dev_id2 in AllActiveDevs(k) - {dev_id})
            ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {}))
                // Other active devices have no transfers to any objects of the 
                // deactivating device
    {
        // Set the device's partition ID to be NULL
        var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
        var new_devs := k.subjects.devs[dev_id := new_dev_state];

        // Construct k'.subjects
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

        var s2 := Edev_Deactivate(k, dev_id);
        if(!s2)
        {    return k, false;}

        // Build <reachable_active_tds_states> for k'
        var k'_subjects := new_subjects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(new_objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(new_objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(new_objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);
  
        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_objects := new_objects;

        Lemma_DevDeactivate_BuildMap_DevsToHCodedTDVals_PreConditions(
            k, k'_subjects, k'_objects, dev_id, new_dev_state);
        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);
        
        // Prove properties of k'_subjects, k'_objects, due to todeactivate_td/fd/do_ids and todeactivate_s_ids
        var todeactivate_s_ids:set<Subject_ID> := {dev_sid};
        var todeactivate_td_ids := tds_owned_by_dev;
        var todeactivate_fd_ids := fds_owned_by_dev;
        var todeactivate_do_ids := dos_owned_by_dev;

        Lemma_DevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK_PreConditions(
            k, k'_subjects, k'_objects, todeactivate_s_ids, dev_id, new_dev_state);
        Lemma_DrvDevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK(
            k, k'_subjects, todeactivate_s_ids);
        Lemma_DevDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
            k, k'_subjects, k'_objects, k_cas, dev_id, new_dev_state);
        Lemma_DevDeactivate_ProveSubjsObjsFulfillProperties(
            k, k'_subjects, k'_objects, k_cas, dev_id, new_dev_state);

        Lemma_DevDeactivate_ActiveDevsInNewKIsActiveDevsInKMinusDevToBeDeactivated(k, k'_subjects, dev_id, new_dev_state);
        assert k'_active_devs == AllActiveDevs(k) - {dev_id}; 
        
        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_SubjObjDeactivate_ProveNewKTDsToAllStatesContainsAllSetsOfTDs(k, tds', k'_objs_td_ids, k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);

        // Prove all preconditions for building <reachable_active_tds_states> for k'
        Lemma_DevDeactivate_OwnershipOfObjsIsPreserved(k, k'_subjects, dev_id, new_dev_state);
        Lemma_DevDeactivate_HCodedTDsHaveUnmodifiedVals(k, k'_subjects, k'_objects, dev_id, new_dev_state);
        assert forall dev_id :: dev_id in k'_subjects.devs
                ==> tds'[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val;
        Lemma_SubjObjDeactivate_NewKParams_HasUnmodifiedVarsFromKParams(k, k'_subjects, k'_objects, k'_params);

        Lemma_DevDeactivate_UnchangedStateVarsBetweenKandNewK(k, k'_subjects, k'_objects, dev_id, new_dev_state);
        Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs(k, k'_subjects, k'_objects, k'_params, 
            todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        
        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params, k'_params);

        Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects);
        Lemma_NewK_HCodedTDsOfAllActiveDevsRefObjInDevs(k, k_params, k'_params, k'_subjects, k'_active_devs);
        assert forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        // Build k'. Defining k' and d here shortens verification time.
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;
        
        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert AllActiveDevs(k') == k'_active_devs;
        assert AllActiveDevs(k') == AllActiveDevs(k) - {dev_id}; 

        // Prove s == true
        assert k'_params == KToKParams(k');
        assert SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k');
        Lemma_SubjObjDeactivate_FulfillCommonPreConditionsOfKAndNewK(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_SubjObjDeactivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
            k', k'_params, k'_active_devs, k'_active_tds_state,
            explored_tds_states, tds_states);
        Lemma_SubjObjDeactivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, tds_states, s);
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        Lemma_DevDeactivate_ProveIsValidState_Subjects(
            k, k', dev_id, new_dev_state);
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        // Prove SI2
        Lemma_SubjObjDeactivate_NewK_FulfillSI2(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');
        
        Lemma_DevDeactivate_ReturnTrue_ProveP_DevDeactivate_ReturnTrue_Def(
            k, dev_id, dev_sid, k_cas, d);
    }
    else
    {
        k' := k;
        d := false;
        
        Lemma_DevDeactivate_ReturnFalse_ProveP_DevDeactivate_ReturnTrue_Def(
            k, dev_id, dev_sid, k_cas, d);
    }
    
    Lemma_P_OpsProperties_DevDeactivateOp_Prove(k, dev_sid, k' ,d);
}


// (needs 110s to verify)
method ExternalObjsActivate(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, // IDs of the objects being activated
    pid:Partition_ID // ID of the partition to activate the driver into
) returns (k':State,d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects 
    requires pid != NULL

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_ExternalObjsActivateOp(k, ExternalObjsActivateOp(td_ids, fd_ids, do_ids, pid))
    
    ensures d == true 
                ==> P_ExternalObjsActivate_ModificationToState(k, td_ids, fd_ids, do_ids, pid, k')
    ensures d == true 
                <==> (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == NULL) &&
                   (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == NULL) &&
                   (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == NULL) &&
                   pid in k.pids
    ensures d == true
                ==> SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, td_ids, pid) &&
                    SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, fd_ids, pid) &&
                    SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, do_ids, pid)
    ensures d == false ==> k' == k
{
    Lemma_ExternalObjActivateDeactivate_NoSubjsOwnsExternalObjs_EquivilantRepresentation(k, td_ids, fd_ids, do_ids);

    if((forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == NULL) &&
       (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == NULL) &&
       (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == NULL) &&
       pid in k.pids)
    {
        // Clear the objects being activated (i.e., ClearObjs)
        var temp_tds := ClearTDs(k.objects.tds, td_ids);
        var temp_fds := ClearFDs(k.objects.fds, fd_ids);
        var temp_dos := ClearDOs(k.objects.dos, do_ids);

        // Modify the PID of these objects (i.e., SetPbjsPIDs)
        var tds' := SetTDsPIDs(temp_tds, td_ids, pid);
        var fds' := SetFDsPIDs(temp_fds, fd_ids, pid);
        var dos' := SetDOsPIDs(temp_dos, do_ids, pid);

        var k'_subjects := k.subjects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(k.objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(k.objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(k.objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_objects := Objects(tds', fds', dos');

        // Build k'
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;

        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove properties of k'_subjects, k'_objects, due to toactivate_td/fd/do_ids and toactivate_s_ids
        var toactivate_s_ids:set<Subject_ID> := {};
        var toactivate_td_ids := td_ids;
        var toactivate_fd_ids := fd_ids;
        var toactivate_do_ids := do_ids;

        Lemma_ExternalObjsActivate_AllObjsToBeActivatedAreExternalObjs(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
        Lemma_ExternalObjsActivate_HCodedTDsAreUnchanged(k, k'_subjects.devs, tds', td_ids);
        assert SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid);
        assert SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid);
        assert SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid);
        assert SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid); 

        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        Lemma_ExternalObjsActivate_HCodedTDsAreUnchanged(k, k'_subjects.devs, tds', td_ids);
        assert forall dev_id :: dev_id in k'_subjects.devs
                ==> tds'[k.subjects.devs[dev_id].hcoded_td_id] == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id];
        Lemma_SubjObjActivate_NewKParams_HasUnmodifiedVarsFromKParams(k, k'_subjects, k'_objects, k'_params);

        Lemma_ExternalObjsActivate_SubjsAndTheirObjsHaveSamePIDs(k, k'_subjects, k'_objects, k'_params, td_ids, fd_ids, do_ids);

        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params, k'_params);

        assert forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert AllActiveDevs(k) == k'_active_devs;
        assert AllActiveDevs(k') == k'_active_devs;

        // Prove s == true
        assert k'_params == KToKParams(k');
        assert SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k');
        Lemma_SubjObjActivate_FulfillCommonPreConditionsOfKAndNewK(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
        Lemma_SubjObjActivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
            k', k'_params, k'_active_devs, k'_active_tds_state,
            explored_tds_states, tds_states);
        Lemma_SubjObjActivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
            k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, tds_states, s);
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        // Prove SI2
        Lemma_SubjObjActivate_NewK_FulfillSI2(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

        // Prove TC2.1
        Lemma_ExternalObjsActivate_FulfillTC21(k, k'.subjects, k'.objects, k'_params, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');
    }
    else
    {
        k' := k;
        d := false;
    }
    
    Lemma_P_OpsProperties_ExternalObjsActivateOp_Prove(k, td_ids, fd_ids, do_ids, pid, k' ,d);
}

// (needs 300s to verify)
method ExternalObjsDeactivate(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, 
    obj_pid:Partition_ID // These objects must be from the same partition
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    ensures P_OpsProperties_ExternalObjsDeactivateOp(k, ExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, obj_pid))
    
    ensures (d == true ==> P_ExternalObjsDeactivate_ModificationToState(k, k', td_ids, fd_ids, do_ids))
    ensures d == true <==> P_ExternalObjsDeactivate_ReturnTrue_Def(k, td_ids, fd_ids, do_ids, obj_pid)
    ensures (d == true
                ==> SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, td_ids) &&
                    SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, fd_ids) &&
                    SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, do_ids))

    ensures d == false ==> k' == k
{
    Lemma_ExternalObjActivateDeactivate_NoSubjsOwnsExternalObjs_EquivilantRepresentation(k, td_ids, fd_ids, do_ids);

    // Calculate reachable snapshots of active TDs in K
    var k_tds_states := ValidSecureState_ReachableStatesOfActiveTDs(k);

    // Build CAS for K
    // CAS is a table showing all potential transfers from active subjects to 
    // active objects. In implementation, CAS is a function of the transitive
    // closure. Thus, checking these transfers in the CAS equals to checking 
    // them in transitive closure
    var k_cas := BuildCAS(k, KToKParams(k), k_tds_states);

    if((obj_pid != NULL) &&
       (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == obj_pid) &&
       (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == obj_pid) &&
       (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == obj_pid) &&
       (forall o_id, dev_id :: o_id in TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids) &&
                dev_id in AllActiveDevs(k)
            ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}))
                    // Active devices have no transfers to any objects to be deactivated
    {
        // Deactivate the given objects
        var tds' := SetTDsPIDs(k.objects.tds, td_ids, NULL);
        var fds' := SetFDsPIDs(k.objects.fds, fd_ids, NULL);
        var dos' := SetDOsPIDs(k.objects.dos, do_ids, NULL);
        var new_objects := Objects(tds', fds', dos');

        // Build <reachable_active_tds_states> for k'
        var k'_subjects := k.subjects;
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(new_objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(new_objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(new_objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');
        var k'_objects := new_objects;

        // Build k'
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;

        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove properties of k'_subjects, k'_objects, due to todeactivate_td/fd/do_ids and todeactivate_s_ids
        var todeactivate_s_ids:set<Subject_ID> := {};
        var todeactivate_td_ids := td_ids;
        var todeactivate_fd_ids := fd_ids;
        var todeactivate_do_ids := do_ids;

        Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
            k, k'_subjects, k_cas, k_tds_states, 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_ExternalObjsDeactivate_AllObjsToBeDeactivatedAreExternalObjs(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        assert SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids);
        assert SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids);
        assert SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids);
        assert SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_SubjObjDeactivate_ProveNewKTDsToAllStatesContainsAllSetsOfTDs(k, tds', k'_objs_td_ids, k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        Lemma_SameAllSubjsIDsBetweenStates(k, k'_subjects);
        Lemma_SameAllObjsIDsBetweenStates(k, k'_objects);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        Lemma_ExternalObjsDeactivate_HCodedTDsAreUnchanged(k, k'_subjects.devs, tds', td_ids);
        assert forall dev_id :: dev_id in k'_subjects.devs
                ==> tds'[k.subjects.devs[dev_id].hcoded_td_id] == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id];
        Lemma_SubjObjDeactivate_NewKParams_HasUnmodifiedVarsFromKParams(k, k'_subjects, k'_objects, k'_params);

        Lemma_ExternalObjsDeactivate_SubjsAndTheirObjsHaveSamePIDs(k, k'_subjects, k'_objects, k'_params, td_ids, fd_ids, do_ids);
        
        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        Lemma_NewKParams_FindAllTDsReadByDev_KParams_PreConditions_StillHold(k_params, k'_params);

        Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects);
        Lemma_NewK_HCodedTDsOfAllActiveDevsRefObjInDevs(k, k_params, k'_params, k'_subjects, k'_active_devs);
        assert forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids;

        // Build <reachable_active_tds_states> for k'
        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
        assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);
        assert AllActiveDevs(k) == k'_active_devs;
        assert AllActiveDevs(k') == k'_active_devs;

        // Prove s == true
        assert k'_params == KToKParams(k');
        assert SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k');
        Lemma_SubjObjDeactivate_FulfillCommonPreConditionsOfKAndNewK(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
        Lemma_SubjObjDeactivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
            k', k'_params, k'_active_devs, k'_active_tds_state,
            explored_tds_states, tds_states);
        Lemma_SubjObjDeactivate_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue(
            k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, tds_states, s);
        assert s == true;

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        // Prove SI2
        Lemma_SubjObjDeactivate_NewK_FulfillSI2(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');

        Lemma_ExternalObjsDeactivate_ReturnTrue_ProveP_ExternalObjsDeactivate_ReturnTrue_Def(
            k, td_ids, fd_ids, do_ids, obj_pid, k_cas, d);
    }
    else
    {
        k' := k;
        d  := false;

        Lemma_ExternalObjsDeactivate_ReturnFalse_ProveP_ExternalObjsDeactivate_ReturnTrue_Def(
            k, td_ids, fd_ids, do_ids, obj_pid, k_cas, d);
    }
    
    Lemma_P_OpsProperties_ExternalObjsDeactivateOp_Prove(k, td_ids, fd_ids, do_ids, obj_pid, k' ,d);
}

// Operation: Driver writes a set of objects with values
// [NOTE] This method defines DrvWrite operation in the paper/slides:
//    (1) This method takes <td_id_val_map>, <fd_id_val_map> and <do_id_val_map>
//        instead of <obj_id_val_map> in the paper.
// (needs 350s to verify)
method DrvWrite(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val> // IDs of DOs, and values to be written
) returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires IDToDrv(k, Drv_ID(drv_sid)).pid != NULL
        // Requirement: The driver is in the state and is active
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures IsValidState(k') && IsSecureState(k')
    ensures IsSecureOps(k, k')
    
    ensures d == true ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property 3: All written objects are in the same partition with the driver
    ensures P_OpsProperties_DrvWriteOp(k, DrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        
    ensures (d == true ==> P_DrvDevWrite_ModificationToState(k, td_id_val_map, fd_id_val_map, do_id_val_map, k'))
    ensures d == true <==> P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    ensures d == false ==> k' == k
{
    var tds' : map<TD_ID, TD_State> := k.objects.tds;
    var fds' : map<FD_ID, FD_State> := k.objects.fds;
    var dos' : map<DO_ID, DO_State> := k.objects.dos;
    
    // Mediate driver's write to FDs and DOs, and modify FDs and DOs accordingly
    if( (forall fd_id :: fd_id in fd_id_val_map ==>    
            SubjPID(k, drv_sid) == ObjPID(k, fd_id.oid)) &&
        (forall do_id :: do_id in do_id_val_map ==>        
            SubjPID(k, drv_sid) == ObjPID(k, do_id.oid)))
                        // The driver and the objects must be in the same partition
    {
        fds' := WriteFDsVals(k.objects.fds, fd_id_val_map);
        dos' := WriteDOsVals(k.objects.dos, do_id_val_map);
    }
    else
    {
        Lemma_P_OpsProperties_DrvWriteOp_Prove(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k, false);
        return k, false;
    }

    // Mediate driver's write to TDs, and modify TDs accordingly
    if (forall td_id :: td_id in td_id_val_map ==>        
            SubjPID(k, drv_sid) == ObjPID(k, td_id.oid))
                        // The driver and the object must be in the same partition
    {
        tds' := WriteTDsVals(k.objects.tds, td_id_val_map);

        var k'_subjects := k.subjects;
        var k'_objects := Objects(tds', fds', dos');
        var k'_objs_td_ids := MapGetKeys<TD_ID, TD_State>(k'_objects.tds);
        var k'_objs_fd_ids := MapGetKeys<FD_ID, FD_State>(k'_objects.fds);
        var k'_objs_do_ids := MapGetKeys<DO_ID, DO_State>(k'_objects.dos);
        ghost var k'_tds_to_all_states := k.tds_to_all_states;
        var k'_active_devs := AllActiveDevs_SlimState(k'_subjects);

        assert MapGetKeys(tds') == MapGetKeys(k.objects.tds);
        assert MapGetKeys(fds') == MapGetKeys(k.objects.fds);
        assert MapGetKeys(dos') == MapGetKeys(k.objects.dos);

        var k'_active_tds := AllActiveTDs_SlimState(tds');
        var k'_active_tds_state := ActiveTDsState_SlimState(tds');

        var k'_params := ReachableTDsKParams(k'_subjects, k'_objs_td_ids, k'_objs_fd_ids, k'_objs_do_ids,
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), k'_active_tds);

        // Prove common properties hold for k'_params and state variables of k' in all operations
        var k_params := KToKParams(k);
        Lemma_KParams_ValidAndSecureK_FindAllTDsReadByDev_PreConditions(k, k_params);
        Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);

        Lemma_NewKTDsToAllStates_ContainsAllSubsetOfTDsInNewK(k, tds', k'_tds_to_all_states);
        Lemma_NewKTDsToAllStates_ContainsActiveTDsInNewK(tds', k'_tds_to_all_states, k'_active_tds);

        // Prove all preconditions for buliding <reachable_active_tds_states> for k'
        Lemma_DrvDevWrite_NewKParams_SameWithKParams(k, k'_subjects, k'_objects, k'_params);
        assert k'_params == k_params;
        assert FindAllTDsReadByDev_KParams_PreConditions(k'_params);

        Lemma_GetExploredTDsStates_IfOneTDsStateExistThenResultOnlyContainsIt(k'_active_tds_state);
        assert forall tds_state2 :: tds_state2 in GetExploredTDsStates([{k'_active_tds_state}], 0)
                    ==> (k'_active_tds_state == tds_state2);
        assert TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k'_params, k'_active_tds_state);

        Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k'_objects);

        var explored_tds_states, s := FindReachableActiveTDsStatesFromActiveTDsState(
                k'_params, k'_tds_to_all_states[k'_active_tds],
                k'_active_devs, k'_active_tds_state, [{k'_active_tds_state}]); 

        // FindReachableActiveTDsStatesFromActiveTDsState returns true, if and only if 
        // forall dev_id, o_id, tds :: dev_id in AllActiveDevs(k') && 
        //          tds in explored_tds_states &&
        //          CanActiveDevIssueTransferToObj(tds, dev_id, o_id)
        //      ==> o_id in AllObjsIDs(k') && o_id !in AllHCodedTDIDs(k') &&
        //          SubjPID(k', dev_id.sid) == ObjPID(k', o_id)
        if(!s)
        {
            var proposed_k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);

            assert proposed_k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map);
            Lemma_SameSubjObjIDsInSuccessiveStates(k, proposed_k');
            Lemma_NewK_FulfillIsValidStateObjects(k, proposed_k');
            assert IsValidState_Objects(proposed_k');
            assert IsValidState_Subjects(proposed_k');
    
            assert KToKParams(proposed_k') == k'_params;
            assert AllActiveDevs(proposed_k') == k'_active_devs;
            assert ActiveTDsState(proposed_k') == k'_active_tds_state;
            Lemma_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(proposed_k');
            Lemma_DrvWrite_ReturnFalse_ProveP_DrvWrite_ReturnTrue_Def(k, Drv_ID(drv_sid), drv_sid, proposed_k',
                td_id_val_map, fd_id_val_map, do_id_val_map, explored_tds_states);

            Lemma_P_OpsProperties_DrvWriteOp_Prove(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k, false);
            return k, false;
        }
        var tds_states := GetExploredTDsStates(explored_tds_states, 0);

        assert s == true;

        // Build k'
        k' := State(k'_subjects, k'_objects, k.pids, k.tds_to_all_states);
        d := true;

        assert k'_params == KToKParams(k');

        // Prove IsValidState_Objects(k')
        Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
        Lemma_NewK_FulfillIsValidStateObjects(k, k');
        assert IsValidState_Objects(k');

        // Prove IsValidState_Subjects(k')
        assert IsValidState_Subjects(k');

        // Prove IsValidState_ReachableTDsStates(k')
        Lemma_IsValidState_SubjectsObjects_Properties(k', k'_params);
        Lemma_SameSubjObjPIDsIfSubjPIDsAreUnchanged(k, k');
        Lemma_UnmodifiedSubjObjPIDs_NewKFulfillIsValidState_SubjsOwnObjsThenInSamePartition(k, k');
        Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(
            k', tds_states);
        Lemma_NewState_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_ThenIsValidStateReachableTDsStates(
            k', k'_params, tds_states, s);

        assert IsValidState(k'); 
        assert IsSecureState(k');
        assert IsSecureOps(k, k');

        Lemma_DrvWrite_ProveProperty3(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map);
        
        assert k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map);
        Lemma_DrvWrite_ReturnTrue_ProveP_DrvWrite_ReturnTrue_Def(k, Drv_ID(drv_sid), drv_sid, k',
            td_id_val_map, fd_id_val_map, do_id_val_map);
    }
    else
    {
        Lemma_P_OpsProperties_DrvWriteOp_Prove(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k, false);
        return k, false;
    }
    
    Lemma_P_OpsProperties_DrvWriteOp_Prove(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k' ,d);
}




//******** Required Functions of Other Models ********//
// Activate an ephemeral device
function method Edev_Activate(k:State, dev_id:Dev_ID) : (d : bool)
    requires (dev_id in k.subjects.devs)
{
    true
}

// Deactivate an ephemeral device
function method Edev_Deactivate(k:State, dev_id:Dev_ID) : (d : bool)
    requires (dev_id in k.subjects.devs)
{
    true
}




//******** Utility Predicates ********//
predicate P_DrvDevWrite_ModificationToState(
    k:State,
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val>,  // IDs of DOs, and values to be written
    k':State
)
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

    k' == State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate DevWrite_ClosureRelationship(
    k:State, k':State
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires IsValidState_Subjects(k') && IsValidState_Objects(k') && IsValidState_Partitions(k') && IsValidState_SubjsOwnObjsThenInSamePartition(k')
{
    var k_active_devs := AllActiveDevs(k);
    var k'_active_devs := AllActiveDevs(k'); 
    var k_active_tds_state:= ActiveTDsState(k);
    var k'_active_tds_state:= ActiveTDsState(k');
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');
    
    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k'_params, 
                            k'_active_devs, k'_active_tds_state, tds_state2)) &&
    (forall tds_state2 :: TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
                ==> IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                            k_active_devs, k_active_tds_state, tds_state2)) &&
        // Properties needed by the property below
        
    AllActiveTDs(k') == AllActiveTDs(k) &&
    (forall tds_state2 :: 
                    TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k') &&
                    (k'_active_tds_state == tds_state2 || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                            k'_active_devs, k'_active_tds_state, tds_state2))
                                                // k'_active_tds_state -->* tds_state2
                ==> IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                        k_active_devs, k_active_tds_state, tds_state2))
                                                // k_active_tds_state -->1+ tds_state2
}

predicate EmptyPartitionCreate_Prop(k:State, new_pid:Partition_ID, k':State, d:bool)
{
    IsValidState(k) && IsSecureState(k) &&

    IsValidState(k') && IsSecureState(k') &&
    IsSecureOps(k, k') &&
    
    (d == true 
        <==> (new_pid != NULL) && (new_pid !in k.pids)) &&
    (d == true
        ==> k' == State(k.subjects, k.objects, k.pids + {new_pid}, k.tds_to_all_states)) &&
    (d == false
        ==> k' == k)
}

predicate EmptyPartitionDestroy_Prop(k:State, pid:Partition_ID, k':State, d:bool)
{
    IsValidState(k) && IsSecureState(k) &&

    IsValidState(k') && IsSecureState(k') &&
    IsSecureOps(k, k') &&
    
    (d == true 
        <==> (pid != NULL) &&
            (pid in k.pids) &&
            (forall s_id :: s_id in AllSubjsIDs(k.subjects) ==> SubjPID(k, s_id) != pid) &&
            (forall o_id :: o_id in AllObjsIDs(k.objects) ==> ObjPID(k, o_id) != pid)) &&
    (d == true
        ==> k' == State(k.subjects, k.objects, k.pids - {pid}, k.tds_to_all_states)) &&
    (d == false
        ==> k' == k)
}

predicate P_DrvActivate_ModificationToState(k:State, drv_sid:Subject_ID, pid:Partition_ID, k':State)
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

    k' == State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate P_DevActivate_ModificationToState(k:State, dev_sid:Subject_ID, pid:Partition_ID, k':State)
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

    k' == State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate P_ExternalObjsActivate_ModificationToState(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID, k':State
)
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

    k' == State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate P_DrvRead_ReturnTrue_Def(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs

    requires read_objs <= AllObjsIDs(k.objects)
    requires DrvRead_ReadSrcObjsToDestObjs_PreConditions(k, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
{
    var td_id_val_map := DrvDevRead_ReplaceSrcTDWithVal(k, tds_dst_src);
    var fd_id_val_map := DrvDevRead_ReplaceSrcFDWithVal(k, fds_dst_src);
    var do_id_val_map := DrvDevRead_ReplaceSrcDOWithVal(k, dos_dst_src);
        
    (forall o_id :: o_id in read_objs
        ==> SubjPID(k, drv_sid) == ObjPID(k, o_id)) &&
        
    P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
}

predicate P_ObjsDeactivate_ReturnTrue_Def(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k)
    
    requires todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    requires todeactivate_fd_ids <= MapGetKeys(k.objects.fds)
    requires todeactivate_do_ids <= MapGetKeys(k.objects.dos)
{
    (forall o_id, dev_id2 :: 
            (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) &&
            dev_id2 in AllActiveDevs(k)
        ==> (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
}

predicate P_DrvDeactivate_ReturnTrue_Def(
    k:State, drv_sid:Subject_ID
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    SubjPID(k, drv_sid) != NULL &&
    P_ObjsDeactivate_ReturnTrue_Def(k, k.subjects.drvs[Drv_ID(drv_sid)].td_ids,
        k.subjects.drvs[Drv_ID(drv_sid)].fd_ids, k.subjects.drvs[Drv_ID(drv_sid)].do_ids)
}

predicate P_DrvDeactivate_ModificationToState(k:State, drv_sid:Subject_ID, k':State)
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

    k' == State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate P_DevDeactivate_ReturnTrue_Def(
    k:State, dev_sid:Subject_ID
)
    requires IsValidState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    Edev_Deactivate(k, Dev_ID(dev_sid)) &&
    SubjPID(k, dev_sid) != NULL &&
    (forall o_id, dev_id2 :: o_id in OwnObjIDs(k, dev_sid) && 
            dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
        ==> (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
}

predicate P_DevDeactivate_ModificationToState(k:State, dev_sid:Subject_ID, k':State)
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

    k' == State(new_subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate P_ExternalObjsDeactivate_ReturnTrue_Def(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, obj_pid:Partition_ID
)
    requires IsValidState(k)

    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    (obj_pid != NULL) &&
    (forall id :: id in td_ids
                ==> ObjPID(k, id.oid) == obj_pid) &&
    (forall id :: id in fd_ids
                ==> ObjPID(k, id.oid) == obj_pid) &&
    (forall id :: id in do_ids
                ==> ObjPID(k, id.oid) == obj_pid) &&
        // Objects to be deactivated are from the same partition
    P_ObjsDeactivate_ReturnTrue_Def(k, td_ids, fd_ids, do_ids)
}

predicate P_ExternalObjsDeactivate_ModificationToState(
    k:State, k':State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
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

    k' == State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}

predicate P_DrvWrite_ReturnTrue_Def(
    k:State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k)

    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs
{
    var k' := DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map);
    Lemma_SameSubjObjIDsInSuccessiveStates(k, k');
    Lemma_NewK_FulfillIsValidStateObjects(k, k');
    assert IsValidState_Objects(k');
    assert IsValidState_Subjects(k');


    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
    assert P_ObjsInSubjsAreAlsoInState(k);

    (forall fd_id :: fd_id in fd_id_val_map ==>
        SubjPID(k, drv_sid) == ObjPID(k, fd_id.oid)) &&
    (forall do_id :: do_id in do_id_val_map ==>
        SubjPID(k, drv_sid) == ObjPID(k, do_id.oid)) &&
    (forall td_id :: td_id in td_id_val_map ==>
        SubjPID(k, drv_sid) == ObjPID(k, td_id.oid)) &&
    AllReachableActiveTDsStatesAreSecure(KToKParams(k'), AllActiveDevs(k'), AllReachableActiveTDsStates(k'))
}




//******** Utility Lemmas ********//
lemma Lemma_DrvDeactivate_ReturnTrue_ProveP_DrvDeactivate_ReturnTrue_Def(
    k:State, drv_id:Drv_ID, drv_sid:Subject_ID, k_cas:CAS, d:bool
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires drv_id == Drv_ID(drv_sid)
    
    requires P_BuildCAS_Properties(k, AllReachableActiveTDsStates(k), k_cas)
        // Property of BuildCAS
    
    requires (SubjPID(k, drv_sid) != NULL)
    requires (forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, drv_sid)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    requires d == true
    
    ensures d == true <==> P_DrvDeactivate_ReturnTrue_Def(k, drv_sid)
{
    assert forall id :: id in k.subjects.drvs[drv_id].td_ids 
        ==> DoOwnObj(k, drv_sid, id.oid);
    assert forall id :: id in k.subjects.drvs[drv_id].fd_ids 
        ==> DoOwnObj(k, drv_sid, id.oid);
    assert forall id :: id in k.subjects.drvs[drv_id].do_ids 
        ==> DoOwnObj(k, drv_sid, id.oid);
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);

    Lemma_AllReachableActiveTDsStates_PreConditions(k);

    Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant(k, 
        k.subjects.drvs[drv_id].td_ids, k.subjects.drvs[drv_id].fd_ids, k.subjects.drvs[drv_id].do_ids, 
        k_cas, AllReachableActiveTDsStates(k));
}

lemma Lemma_DrvDeactivate_ReturnFalse_ProveP_DrvDeactivate_ReturnTrue_Def(
    k:State, drv_id:Drv_ID, drv_sid:Subject_ID, k_cas:CAS, d:bool
)
    requires IsValidState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires drv_id == Drv_ID(drv_sid)
    
    requires P_BuildCAS_Properties(k, AllReachableActiveTDsStates(k), k_cas)
        // Property of BuildCAS
    
    requires !(SubjPID(k, drv_sid) != NULL) ||
             !(forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, drv_sid)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    requires d == false
    
    ensures d == true <==> P_DrvDeactivate_ReturnTrue_Def(k, drv_sid)
{
    if(SubjPID(k, drv_sid) == NULL)
    {
        assert !P_DrvDeactivate_ReturnTrue_Def(k, drv_sid);
    }
    else
    {
        assert forall id :: id in k.subjects.drvs[drv_id].td_ids 
            ==> DoOwnObj(k, drv_sid, id.oid);
        assert forall id :: id in k.subjects.drvs[drv_id].fd_ids 
            ==> DoOwnObj(k, drv_sid, id.oid);
        assert forall id :: id in k.subjects.drvs[drv_id].do_ids 
            ==> DoOwnObj(k, drv_sid, id.oid);
        assert IsValidState_SubjsOwnObjsThenInSamePartition(k);

        Lemma_AllReachableActiveTDsStates_PreConditions(k);

        Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant(k, 
            k.subjects.drvs[drv_id].td_ids, k.subjects.drvs[drv_id].fd_ids, k.subjects.drvs[drv_id].do_ids, 
            k_cas, AllReachableActiveTDsStates(k));
        assert !P_DrvDeactivate_ReturnTrue_Def(k, drv_sid);
    }
}

lemma Lemma_DevDeactivate_ReturnTrue_ProveP_DevDeactivate_ReturnTrue_Def(
    k:State, dev_id:Dev_ID, dev_sid:Subject_ID, k_cas:CAS, d:bool
)
    requires IsValidState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires dev_id == Dev_ID(dev_sid)
    
    requires P_BuildCAS_Properties(k, AllReachableActiveTDsStates(k), k_cas)
        // Property of BuildCAS
    
    requires (SubjPID(k, dev_sid) != NULL)
    requires Edev_Deactivate(k, dev_id) == true
    requires (forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, dev_sid)) && 
                (dev_id2 in AllActiveDevs(k) - {dev_id})
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    requires d == true
    
    ensures d == true <==> P_DevDeactivate_ReturnTrue_Def(k, dev_sid)
{
    Lemma_DevDeactivate_NoTransferToDevToBeDeactivated_Equivilant(k, dev_sid, k_cas, AllReachableActiveTDsStates(k));
}

lemma Lemma_DevDeactivate_ReturnFalse_ProveP_DevDeactivate_ReturnTrue_Def(
    k:State, dev_id:Dev_ID, dev_sid:Subject_ID, k_cas:CAS, d:bool
)
    requires IsValidState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires dev_id == Dev_ID(dev_sid)
    
    requires P_BuildCAS_Properties(k, AllReachableActiveTDsStates(k), k_cas)
        // Property of BuildCAS
    
    requires !(SubjPID(k, dev_sid) != NULL) ||
             !(Edev_Deactivate(k, dev_id) == true) ||
             !(forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, dev_sid)) && 
                (dev_id2 in AllActiveDevs(k) - {dev_id})
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    requires d == false
    
    ensures d == true <==> P_DevDeactivate_ReturnTrue_Def(k, dev_sid)
{
    if(SubjPID(k, dev_sid) == NULL)
    {
        assert !P_DevDeactivate_ReturnTrue_Def(k, dev_sid);
    }
    else
    {
        Lemma_DevDeactivate_NoTransferToDevToBeDeactivated_Equivilant(k, dev_sid, k_cas, AllReachableActiveTDsStates(k));
        assert !P_DevDeactivate_ReturnTrue_Def(k, dev_sid);
    }
}

lemma Lemma_ExternalObjsDeactivate_ReturnTrue_ProveP_ExternalObjsDeactivate_ReturnTrue_Def(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, obj_pid:Partition_ID, 
    k_cas:CAS, d:bool
)
    requires IsValidState(k)
    requires P_BuildCAS_Properties(k, AllReachableActiveTDsStates(k), k_cas)
        // Property of BuildCAS
    
    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)

    requires obj_pid != NULL
    requires forall id :: id in td_ids
                ==> ObjPID(k, id.oid) == obj_pid
    requires forall id :: id in fd_ids
                ==> ObjPID(k, id.oid) == obj_pid
    requires forall id :: id in do_ids
                ==> ObjPID(k, id.oid) == obj_pid
        // Requirement: Objects to be deactivated are from the same partition

    requires (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    requires d == true
    
    ensures d == true <==> P_ExternalObjsDeactivate_ReturnTrue_Def(k, td_ids, fd_ids, do_ids, obj_pid)
{
    Lemma_AllReachableActiveTDsStates_PreConditions(k);

    Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant(k, 
        td_ids, fd_ids, do_ids, 
        k_cas, AllReachableActiveTDsStates(k));
}

lemma Lemma_ExternalObjsDeactivate_ReturnFalse_ProveP_ExternalObjsDeactivate_ReturnTrue_Def(
    k:State,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, obj_pid:Partition_ID,
    k_cas:CAS, d:bool
)
    requires IsValidState(k)   
    requires P_BuildCAS_Properties(k, AllReachableActiveTDsStates(k), k_cas)
        // Property of BuildCAS

    requires td_ids <= MapGetKeys(k.objects.tds)
    requires fd_ids <= MapGetKeys(k.objects.fds)
    requires do_ids <= MapGetKeys(k.objects.dos)
    
    requires !(obj_pid != NULL) ||
             !(forall id :: id in td_ids
                ==> ObjPID(k, id.oid) == obj_pid)||
             !(forall id :: id in fd_ids
                ==> ObjPID(k, id.oid) == obj_pid)||
             !(forall id :: id in do_ids
                ==> ObjPID(k, id.oid) == obj_pid)||
             !(forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    requires d == false
    
    ensures d == true <==> P_ExternalObjsDeactivate_ReturnTrue_Def(k, td_ids, fd_ids, do_ids, obj_pid)
{
    if((obj_pid != NULL) &&
        (forall id :: id in td_ids
                    ==> ObjPID(k, id.oid) == obj_pid) &&
        (forall id :: id in fd_ids
                    ==> ObjPID(k, id.oid) == obj_pid) &&
        (forall id :: id in do_ids
                    ==> ObjPID(k, id.oid) == obj_pid))
    {
        Lemma_AllReachableActiveTDsStates_PreConditions(k);

        Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant(k, 
            td_ids, fd_ids, do_ids, 
            k_cas, AllReachableActiveTDsStates(k));
        assert !P_ExternalObjsDeactivate_ReturnTrue_Def(k, td_ids, fd_ids, do_ids, obj_pid);
    }
    else
    {
        assert !P_ExternalObjsDeactivate_ReturnTrue_Def(k, td_ids, fd_ids, do_ids, obj_pid);
    }
}

lemma Lemma_DrvWrite_ReturnTrue_ProveP_DrvWrite_ReturnTrue_Def(
    k:State, drv_id:Drv_ID, drv_sid:Subject_ID, k':State,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires IsValidState(k)

    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires drv_id == Drv_ID(drv_sid)

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs
    
    requires k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires IsValidState_Subjects(k') && IsValidState_Objects(k')
    
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k')
            ==> DevHCodedTDRefsObjsInSameDev_SlimState(KToKParams(k').subjects, KToKParams(k').hcoded_tds, dev_id2) &&
                IDToDev_SlimState(KToKParams(k').subjects, dev_id2).td_ids <= KToKParams(k').objs_td_ids
    
    requires AllReachableActiveTDsStatesAreSecure(KToKParams(k'), AllActiveDevs(k'), AllReachableActiveTDsStates(k'))
    requires (forall fd_id :: fd_id in fd_id_val_map ==>
                SubjPID(k, drv_sid) == ObjPID(k, fd_id.oid)) &&
            (forall do_id :: do_id in do_id_val_map ==>
                SubjPID(k, drv_sid) == ObjPID(k, do_id.oid)) &&
            (forall td_id :: td_id in td_id_val_map ==>
                SubjPID(k, drv_sid) == ObjPID(k, td_id.oid))
    
    ensures P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvWrite_ReturnFalse_ProveP_DrvWrite_ReturnTrue_Def(
    k:State, drv_id:Drv_ID, drv_sid:Subject_ID, k':State,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    explored_tds_states':seq<set<TDs_Vals>>
)
    requires IsValidState(k)

    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires drv_id == Drv_ID(drv_sid)

    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs
    
    requires k' == DrvWrite_ProposedNewState(k, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires IsValidState_Subjects(k') && IsValidState_Objects(k')
    
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k')
            ==> DevHCodedTDRefsObjsInSameDev_SlimState(KToKParams(k').subjects, KToKParams(k').hcoded_tds, dev_id2) &&
                IDToDev_SlimState(KToKParams(k').subjects, dev_id2).td_ids <= KToKParams(k').objs_td_ids
    
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> TDsStateGetTDIDs(tds_state2) == KToKParams(k').all_active_tds
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states', 0)
                ==> (ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(KToKParams(k'), AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
    requires !AllReachableActiveTDsStatesAreSecure(KToKParams(k'), AllActiveDevs(k'), GetExploredTDsStates(explored_tds_states', 0))
    
    ensures !P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
{
    assert !AllReachableActiveTDsStatesAreSecure(KToKParams(k'), AllActiveDevs(k'), AllReachableActiveTDsStates(k'));
}

lemma Lemma_P_OpsProperties_DrvReadOp_Prove(
    k:State, drv_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    k':State, d:bool
)
    requires DrvRead_PreConditions(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DrvRead_PostConditions(k, drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, k' ,d)

    ensures P_OpsProperties_DrvReadOp(k, DrvReadOp(drv_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DevReadOp_Prove(
    k:State, dev_sid:Subject_ID, read_objs:set<Object_ID>, 
    tds_dst_src:map<TD_ID, TD_ID>, fds_dst_src:map<FD_ID, FD_ID>, dos_dst_src:map<DO_ID, DO_ID>,
    k':State, d:bool
)
    requires DevRead_PreConditions(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_PostConditions(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src, k' ,d)

    ensures P_OpsProperties_DevReadOp(k, DevReadOp(dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DevWriteOp_Prove(
    k:State, dev_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    k':State, d:bool
)
    requires DevWrite_PreConditions(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires DevWrite_PostConditions(k, dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k' ,d)

    ensures P_OpsProperties_DevWriteOp(k, DevWriteOp(dev_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_EmptyPartitionCreateOp_Prove(
    k:State, new_pid:Partition_ID,
    k':State, d:bool
)
    requires (IsValidState(k) && IsSecureState(k))
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_EmptyPartitionCreateOp(k, EmptyPartitionCreateOp(new_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_EmptyPartitionDestroyOp_Prove(
    k:State, pid:Partition_ID,
    k':State, d:bool
)
    requires (IsValidState(k) && IsSecureState(k))
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_EmptyPartitionDestroyOp(k, EmptyPartitionDestroyOp(pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DrvActivateOp_Prove(
    k:State, drv_sid:Subject_ID, pid:Partition_ID,
    k':State, d:bool
)
    requires (IsValidState(k) && IsSecureState(k))
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_DrvActivateOp(k, DrvActivateOp(drv_sid, pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DrvDectivateOp_Prove(
    k:State, drv_sid:Subject_ID, 
    k':State, d:bool
)
    requires (IsValidState(k) && IsSecureState(k))
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_DrvDeactivateOp(k, DrvDeactivateOp(drv_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DevActivateOp_Prove(
    k:State, dev_sid:Subject_ID, pid:Partition_ID,
    k':State, d:bool
)
    requires (IsValidState(k) && IsSecureState(k))
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_DevActivateOp(k, DevActivateOp(dev_sid, pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DevDeactivateOp_Prove(
    k:State, dev_sid:Subject_ID, 
    k':State, d:bool
)
    requires (IsValidState(k) && IsSecureState(k))
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_DevDeactivateOp(k, DevDeactivateOp(dev_sid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_ExternalObjsActivateOp_Prove(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID,
    k':State, d:bool
)
    requires ExternalObjsActivate_PreConditions(k, td_ids, fd_ids, do_ids, pid)
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_ExternalObjsActivateOp(k, ExternalObjsActivateOp(td_ids, fd_ids, do_ids, pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_ExternalObjsDeactivateOp_Prove(
    k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, obj_pid:Partition_ID,
    k':State, d:bool
)
    requires ExternalObjsDeactivate_PreConditions(k, td_ids, fd_ids, do_ids, obj_pid)
    requires Common_PostConditions(k, k', d)

    ensures P_OpsProperties_ExternalObjsDeactivateOp(k, ExternalObjsDeactivateOp(td_ids, fd_ids, do_ids, obj_pid))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_P_OpsProperties_DrvWriteOp_Prove(
    k:State, drv_sid:Subject_ID,
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>,
    k':State, d:bool
)
    requires DrvWrite_PreConditions(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
    requires DrvWrite_PostConditions(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map, k', d)

    ensures P_OpsProperties_DrvWriteOp(k, DrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
{
    // Dafny can automatically prove this lemma
}