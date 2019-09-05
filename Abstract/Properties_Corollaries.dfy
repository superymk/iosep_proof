include "Properties.dfy"

//******** Corolaries  ********//
predicate StatePropertiesCorollary1(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
{
    //// Condition 5.4 For each active TDs' state in the closure 
    //// <AllReachableActiveTDsStates(k)>, if the state enables an
    //// active device to perform transfers to an object, then the device and
    //// the object must be in the same partition
    (forall tds_state2, dev_id, o_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
            dev_id in AllActiveDevs(k) &&
            (DevAModesToObj(k, tds_state2, dev_id, o_id) != {})
                                        // The active device has transfers to the object
        ==> o_id in AllObjsIDs(k.objects) &&
            SubjPID_DevID(k, dev_id) == ObjPID(k, o_id)) &&
                                        // The device and the object must be in the same partition

    (true)
}

predicate StatePropertiesCorollary2(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
{
    // SI1: If an active device has transfers to an object, then the device 
    // and the object must be in the same partition
    (forall dev_id, o_id :: dev_id in AllActiveDevs(k) && 
            DevAModesToObj(k, ActiveTDsState(k), dev_id, o_id) != {}
                                        // If an active device has transfers to an object
        ==> o_id in AllObjsIDs(k.objects) &&
            SubjPID_DevID(k, dev_id) == ObjPID(k, o_id)) &&
                                        // Then the device and the object must be in the same partition

    (true)
}




//******** Lemmas  ********//
lemma Lemma_SecureState_FulfillsStatePropertyCorollary1(k:State)
    requires IsValidState(k) && IsSecureState(k)

    ensures StatePropertiesCorollary1(k)
{
    Lemma_IfFulfillCondition55AndIsValidState_SubjsOwnObjsThenInSamePartition_ThenFulfillCorollary1(
        k, KToKParams(k), AllReachableActiveTDsStates(k));
}

lemma Lemma_StatePropertyCorollary1_ImpliesCorollary2(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)

    requires StatePropertiesCorollary1(k)

    ensures StatePropertiesCorollary2(k)
{
    // Dafny can automatically prove this lemma
}

// Lemma: If a state fulfills Condition5.5 and IsValidState_SubjsOwnObjsThenInSamePartition, then the state fulfills StatePropertiesCorollary1
// (needs 160s to verify)
lemma Lemma_IfFulfillCondition55AndIsValidState_SubjsOwnObjsThenInSamePartition_ThenFulfillCorollary1(
    k:State, k_params:ReachableTDsKParams, k_reachable_active_tds_states:set<TDs_Vals>
)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id 
        // Requirements: Objects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are TDs
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    // Requirements required by functions in this function method

    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
                ==> o_id in AllObjsIDs(k.objects) &&
                    SubjPID(k, s_id) == ObjPID(k, o_id)
        // Requirement: k fulfills IsValidState_SubjsOwnObjsThenInSamePartition
    requires IsValidState_TDsToAllStates(k)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method
    requires k_params == KToKParams(k)
    requires k_reachable_active_tds_states == AllReachableActiveTDsStates(k)

    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: <tds_states> must includes all active TDs
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires AllReachableActiveTDsStatesAreSecure(k_params, AllActiveDevs(k), k_reachable_active_tds_states)
        // Property: k fulfills Condition 5.5 of <IsValidState_ReachableTDsStates> 

    ensures forall tds_state2, dev_id, o_id :: tds_state2 in k_reachable_active_tds_states &&
                    dev_id in AllActiveDevs(k) &&
                    (DevAModesToObj(k, tds_state2, dev_id, o_id) != {})
                                                // The active device has transfers to the object
                ==> o_id in AllObjsIDs(k.objects) &&
                    SubjPID_DevID(k, dev_id) == ObjPID(k, o_id)
                                                // The device and the object must be in the same partition
        // Property: k fulfills Condition 5.4 of <IsValidState_ReachableTDsStates> 
{
    forall tds_state2, dev_id, o_id | tds_state2 in k_reachable_active_tds_states &&
                dev_id in AllActiveDevs(k) &&
                (DevAModesToObj(k, tds_state2, dev_id, o_id) != {})
        ensures o_id in AllObjsIDs(k.objects)
        ensures SubjPID_DevID(k, dev_id) == ObjPID(k, o_id)
    {
        var td_id :| td_id in tds_state2 &&        // Exist an active TD (<td_id>)
                    CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id) &&
                                // The device (<dev_id>) can read the (active) TD
                    o_id in GetObjIDsRefedInTD(tds_state2, td_id) &&
                    GetAModesOfObjRefedInTD(tds_state2, td_id, o_id) != {};
                                // The TD refs the object (<o_id>) with non-empty access mode
        assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2);

        Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(k, k_params, AllActiveDevs(k), tds_state2, dev_id, td_id);
        Lemma_SecureActiveTDsState_TransfersInTDsRefsObjsInSamePartitionOnly(k, k_params, tds_state2, dev_id, td_id, o_id);


        assert o_id in AllObjsIDs(k.objects);
        assert SubjPID_DevID(k, dev_id) == ObjPID(k, o_id);
    }
}