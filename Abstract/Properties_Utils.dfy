include "Utils.dfy"
include "./BuildCAS/Utils_BuildCAS.dfy" 
include "HCodedTD_Ops.dfy"


//******** Devices' Requested Access Modes  ********//
// Return the device's (<dev_id>) requested access modes to the object (<o_id>)
// This includes the requested access modes from (1) all TDs read by the 
// device
// [NOTE] the requested access modes do not contain modes defined in 
// hardcoded TDs
//
// <tds> is the state of active TDs. <tds> needs not to be the state of all  
// TDs because (1) no active TD carries transfers to any inactive objects, and 
// (2) active devices never have hardcoded transfers to inactive objects. 
// Thus, an active device cannot read any inactive TDs, and hence only performs
// accesses based on hardcoded transfers and active TDs read by the device.
// [Note] This function further defines CanActiveDevAccessObj; i.e., 
// CanActiveDevAccessObj() = true, iff DevAModesToObj() != {} or o_id is the 
// hardcoded TD of the device
// (needs 60s to verify)
function DevAModesToObj(
    k:State, 
    tds:TDs_Vals, // The given active TDs' state
    dev_id:Dev_ID, // ID of the given device
    o_id:Object_ID // ID of the target object
) : set<AMode>
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
    requires TDsStateGetTDIDs(tds) == AllActiveTDs(k)

    requires IsDevID(k, dev_id)
    requires SubjPID(k, dev_id.sid) != NULL
    // Requirement: The device is active

    ensures SubjPID_DevID(k, dev_id) != NULL
    ensures DevAModesToObj_SlimState_PreConditions(KToKParams(k), tds, dev_id, o_id)
    ensures DevAModesToObj(k, tds, dev_id, o_id) == 
            DevAModesToObj_SlimState(KToKParams(k), tds, dev_id, o_id)
{
    Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k.subjects, dev_id);
    DevAModesToObj_SlimState(KToKParams(k), tds, dev_id, o_id)
}

// Return the device's (<dev_id>) requested access modes to the object (<o_id>)
// only recorded in all TDs that can be read by the device
function DevAModesToObjFromTDs(
    k:State, tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : set<AMode>
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
    requires TDsStateGetTDIDs(tds) == AllActiveTDs(k)

    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
    // Requirement: The device is active

    ensures DevAModesToObjFromTDs(k, tds, dev_id, o_id) == 
            DevAModesToObjFromTDs_SlimState(KToKParams(k), tds, dev_id, o_id)
{
    DevAModesToObjFromTDs_SlimState(KToKParams(k), tds, dev_id, o_id)
}

// Return if there is an active TD that (1) can be read by the device 
// (<dev_id>), and (2) records R access mode to the object (<o_id>)
function DevAModesToObjFromTDs_ExistR(
    k:State, tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : bool
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
    requires TDsStateGetTDIDs(tds) == AllActiveTDs(k)

    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
    // Requirement: The device is active

    ensures DevAModesToObjFromTDs_ExistR(k, tds, dev_id, o_id) == 
            DevAModesToObjFromTDs_ExistR_SlimState(KToKParams(k), tds, dev_id, o_id)
{
    DevAModesToObjFromTDs_ExistR_SlimState(KToKParams(k), tds, dev_id, o_id)
}

// Return if there is an active TD that (1) can be read by the device 
// (<dev_id>), and (2) records W access mode to the object (<o_id>)
function DevAModesToObjFromTDs_ExistW(
    k:State, tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : bool
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
    requires TDsStateGetTDIDs(tds) == AllActiveTDs(k)
    
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
    // Requirement: The device is active

    ensures DevAModesToObjFromTDs_ExistW(k, tds, dev_id, o_id) == 
            DevAModesToObjFromTDs_ExistW_SlimState(KToKParams(k), tds, dev_id, o_id)
{
    DevAModesToObjFromTDs_ExistW_SlimState(KToKParams(k), tds, dev_id, o_id)
}

predicate CanActiveDevReadActiveTD_KParams_PreConditions(k_params:ReachableTDsKParams)
{
    (forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids) &&
    (forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids) &&
    (forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids) &&
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    (forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL) &&
        // Requirement: <k_params.all_active_tds> holds all active TDs
    (MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)) &&
        // <k_params.hcoded_tds> include all devices

    (true)
}

// Requirements of the CanActiveDevReadActiveTD function
predicate CanActiveDevReadActiveTD_PreConditions(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID
)
{
    CanActiveDevReadActiveTD_KParams_PreConditions(k_params) &&
        // <k_params.hcoded_tds> include all devices

    (TDsStateGetTDIDs(tds) == k_params.all_active_tds) &&
        // Requirement: The TDs' state includes all active TDs 
    (td_id in tds) &&
        // Requirement: The TD (<td_id>) is active

    (IsDevID_SlimState(k_params.subjects, dev_id)) &&
    (SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL) &&
    (ObjPID_SlimState(k_params.objs_pids, td_id.oid) != NULL) &&
        // Requirement: The device and the TD are active

    (true)
}

// Return if an active device can read an active TD.
// The function return true, iff there exists a list of active TDs, which 
// starts from a hardcoded TD to the TD (<td_id>), and one refs the next one in  
// the list with read access mode.
// Note: the length of the list can be 1, when <td_id> is a hardcoded TD
function CanActiveDevReadActiveTD(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID
) : bool
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)

    ensures CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id)
                <==> (exists td_ids:seq<TD_ID> :: |td_ids| >= 1 && 
                     (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
                                                      // A list of active TDs
                     td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                     td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                     (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]])))
                                                      // previous TD always refs the current TD with R access mode
        // Property: The function return true, iff there exists a list of 
        // active TDs, which starts from a hardcoded TD to the TD (<td_id>),
        // and one refs the next one in the list
{
     exists td_ids:seq<TD_ID> :: |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]))
                                            // previous TD always refs the current TD with R access mode
}




//******** Devices' Requested Access Modes  ********//
predicate DevAModesToObj_SlimState_PreConditions(
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
)
{
    (forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids) &&
    (forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids) &&
    (forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids) &&
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    (forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL) &&
        // Requirement: <k_params.all_active_tds> holds all active TDs
    (MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)) &&
        // <k_params.hcoded_tds> include all devices

    (TDsStateGetTDIDs(tds) == k_params.all_active_tds) &&
        // Requirement: The TDs' state includes all active TDs 
    (MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)) &&
        // <k_params.hcoded_tds> include all devices

    (IsDevID_SlimState(k_params.subjects, dev_id)) &&
    (SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL) &&
        // Requirement: The device is active

    (true)
}

// Return the device's (<dev_id>) requested access modes to the object (<o_id>)
// This includes the requested access modes from (1) all TDs read by the 
// device
function DevAModesToObj_SlimState(
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : set<AMode>
    requires DevAModesToObj_SlimState_PreConditions(k_params, tds, dev_id, o_id)
{
    DevAModesToObjFromTDs_SlimState(k_params, tds, dev_id, o_id)
}

// Return the device's (<dev_id>) requested access modes to the object (<o_id>)
// only recorded in all TDs that can be read by the device
// It should be noted that, if a device can read two TDs (TD1 and TD2), and TD1
// has R to obj1, TD2 has W to obj1, then the device has RW transfer to obj1
// from TD1 and TD2.
function DevAModesToObjFromTDs_SlimState(
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : set<AMode>
    requires DevAModesToObj_SlimState_PreConditions(k_params, tds, dev_id, o_id)
{
    if DevAModesToObjFromTDs_ExistR_SlimState(k_params, tds, dev_id, o_id) then
        if DevAModesToObjFromTDs_ExistW_SlimState(k_params, tds, dev_id, o_id) then
            {R,W}
        else
            {R}
    else
        if DevAModesToObjFromTDs_ExistW_SlimState(k_params, tds, dev_id, o_id) then
            {W}
        else
            {}
}

// Return if there is an active TD that (1) can be read by the device 
// (<dev_id>), and (2) records R access mode to the object (<o_id>)
function DevAModesToObjFromTDs_ExistR_SlimState(
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : bool
    requires DevAModesToObj_SlimState_PreConditions(k_params, tds, dev_id, o_id)
{
    if (exists td_id :: 
            td_id in tds &&        // Exist an active TD (<td_id>)
            CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id) &&
                                // The device (<dev_id>) can read the (active) TD
            o_id in GetObjIDsRefedInTD(tds, td_id) &&
            R in GetAModesOfObjRefedInTD(tds, td_id, o_id)
                                // The TD refs the object (<o_id>) with R access mode
        )
    then true
    else false
}

// Return if there is an active TD that (1) can be read by the device 
// (<dev_id>), and (2) records W access mode to the object (<o_id>)
function DevAModesToObjFromTDs_ExistW_SlimState(
    k_params:ReachableTDsKParams,
    tds:TDs_Vals, dev_id:Dev_ID, o_id:Object_ID
) : bool
    requires DevAModesToObj_SlimState_PreConditions(k_params, tds, dev_id, o_id)
{
    if (exists td_id :: 
            td_id in tds &&        // Exist an active TD (<td_id>)
            CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id) &&
                                // The device (<dev_id>) can read the (active) TD
            o_id in GetObjIDsRefedInTD(tds, td_id) &&
            W in GetAModesOfObjRefedInTD(tds, td_id, o_id)
                                // The TD refs the object (<o_id>) with W access mode
        )
    then true
    else false
}

predicate ActiveTDsStateIsSecure(
    k_params:ReachableTDsKParams,
    active_devs:set<Dev_ID>, tds_state:TDs_Vals
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
{
    (forall td_id2, dev_id :: 
        dev_id in active_devs && 
            // The device (<dev_id>) is active
        td_id2 in TDsStateGetTDIDs(tds_state) &&
            // The TD (<td_id2>) is active
        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
            // The TD is read by the device
    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2))
}

predicate AllReachableActiveTDsStatesAreSecure(
    k_params:ReachableTDsKParams,
    active_devs:set<Dev_ID>, reachable_tds_states:set<TDs_Vals>
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires forall dev_id2 :: dev_id2 in active_devs
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL
        // Requirement: The devices in <active_devs> must be active
    requires forall dev_id2 :: dev_id2 in active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in reachable_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: Each known TDs' state includes all active TDs
{
    (forall tds_state2 :: tds_state2 in reachable_tds_states
        ==> MapGetKeys<TD_ID, TD_Val>(tds_state2) == 
                k_params.all_active_tds &&
            ActiveTDsStateIsSecure(k_params, active_devs, tds_state2))
}




//******** Utility Lemmas ********//
lemma Lemma_ActiveTDsStateIsSecure_TDReadByActiveDevMustHaveValidRefsOnly(
    k:State, tds_state:TDs_Vals, dev_id:Dev_ID, td_id1:TD_ID, td_id2:TD_ID
)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))
   
    requires TDsStateGetTDIDs(tds_state) == KToKParams(k).all_active_tds
    requires ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state)

    requires td_id1 in tds_state
    requires td_id1.oid in AllObjsIDs(k.objects)
    requires td_id2.oid in AllObjsIDs(k.objects)
    requires ObjPID(k, td_id1.oid) != ObjPID(k, td_id2.oid)

    requires dev_id in AllActiveDevs(k)

    requires CanActiveDevReadActiveTD(KToKParams(k), tds_state, dev_id, td_id1);

    ensures td_id2 !in TDIDReadsInTDCfg(tds_state[td_id1])
{
    assert forall td_id :: td_id in k.objects.tds <==> td_id in MapGetKeys(k.objects.tds);
    assert forall fd_id :: fd_id in k.objects.fds <==> fd_id in MapGetKeys(k.objects.fds);
    assert forall do_id :: do_id in k.objects.dos <==> do_id in MapGetKeys(k.objects.dos);
}

lemma Lemma_CanActiveDevReadActiveTD_DevCanAlwaysReadHCodedTD(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, dev_id:Dev_ID
)
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, k_params.subjects.devs[dev_id].hcoded_td_id)

    ensures CanActiveDevReadActiveTD(k_params, tds, dev_id, k_params.subjects.devs[dev_id].hcoded_td_id)
{
    var td_ids:seq<TD_ID> := [k_params.subjects.devs[dev_id].hcoded_td_id];

    assert |td_ids| >= 1;
    assert (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds);
                                            // A list of active TDs
    assert td_ids[|td_ids| - 1] == k_params.subjects.devs[dev_id].hcoded_td_id; // last TD is the TD (<td_id>)
    assert td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id;
                                            // first TD must be the hardcoded TD
    assert (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]));
}

lemma Lemma_CanActiveDevReadActiveTD_ThenTDIsHCodedTDOrDevAModesToObjHasRTransfer(
    k:State, k_params:ReachableTDsKParams, tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID
)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))

    requires k_params == KToKParams(k)

    requires MapGetKeys<TD_ID, TD_Val>(tds) == AllActiveTDs(k)

    requires IsDevID(k, dev_id)
    requires SubjPID(k, dev_id.sid) != NULL
    // Requirement: The device is active

    requires td_id in tds

    ensures CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id)
        ==> R in DevAModesToObj(k, tds, dev_id, td_id.oid) || td_id == k.subjects.devs[dev_id].hcoded_td_id
{
    if(CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id))
    {
        var td_ids:seq<TD_ID> := Lemma_CanActiveDevReadActiveTD_Apply(k_params, tds, dev_id, td_id);

        if(|td_ids| == 1)
        {
            assert td_id == k.subjects.devs[dev_id].hcoded_td_id;
        }
        else
        {
            Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, tds, dev_id, td_ids, td_id);
            var check_td_id := td_ids[|td_ids| - 2];

            assert check_td_id in tds;
            assert CanActiveDevReadActiveTD(k_params, tds, dev_id, check_td_id);
            assert td_id.oid in GetObjIDsRefedInTD(tds, check_td_id) &&
                    R in GetAModesOfObjRefedInTD(tds, check_td_id, td_id.oid);

            assert DevAModesToObjFromTDs_ExistR(k, tds, dev_id, td_id.oid);
            assert R in DevAModesToObj(k, tds, dev_id, td_id.oid);
        }
    }
}

// Lemma: If an active device (<dev_id>) can read an active TD (<td_id>) via a 
// sequence of active intermediate TDs (<td_ids>), then the device can read all
// these TDs 
lemma Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(
    k_params:ReachableTDsKParams, tds_state:TDs_Vals, dev_id:Dev_ID, td_ids:seq<TD_ID>, td_id:TD_ID
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds

    requires forall td_id2 :: td_id2 in td_ids
                ==> td_id2 in tds_state

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device is active

    requires |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]))
        // Rquirement: The device (<dev_id>) can read the TD by following this 
        // TD chain

    ensures forall td_id2 :: td_id2 in td_ids
                ==> CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
{
    var i := 0;
    var new_td_ids := td_ids[..i+1]; 

    while (i < |td_ids|)
        invariant i <= |td_ids|

        invariant forall td_id2 :: td_id2 in td_ids[..i]
                    ==> CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
    {
        var new_td_ids := td_ids[..i+1];

        i := i + 1;
    }

    Lemma_AllElemsIndexedInSeqAreInSeq(td_ids);
}

predicate P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(
   tds:map<TD_ID, TD_Val>, td_ids:seq<TD_ID>
)
    requires |td_ids| >= 1
    requires forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds
{
    forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]])
}

lemma Lemma_CanActiveDevReadActiveTD_Apply(
    k_params:ReachableTDsKParams,
    tds:map<TD_ID, TD_Val>, dev_id:Dev_ID, td_id:TD_ID
) returns (td_ids:seq<TD_ID>)
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds, dev_id, td_id)
    requires CanActiveDevReadActiveTD(k_params, tds, dev_id, td_id)

    ensures |td_ids| >= 1 && 
                     (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds) &&
                                                      // A list of active TDs
                     td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                     td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                     (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds[td_ids[i]]))
    ensures P_CanActiveDevReadActiveTD_EachTDAlwaysRefedByPreviousTDWithRInChain(tds, td_ids)
{
    var result_td_ids:seq<TD_ID> :| |result_td_ids| >= 1 && 
                     (forall td_id2 :: td_id2 in result_td_ids ==> td_id2 in tds) &&
                                                      // A list of active TDs
                     result_td_ids[|result_td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
                     result_td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                     (forall i :: 0<=i<|result_td_ids| - 1 ==> result_td_ids[i+1] in TDIDReadsInTDCfg(tds[result_td_ids[i]]));
    return result_td_ids;
}