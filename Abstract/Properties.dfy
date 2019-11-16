include "Syntax.dfy"
include "Properties_Utils.dfy"
include "./BuildCAS/ReachableTDsStates.dfy"
include "Lemmas.dfy"

// IsValidState_* defines trivial state invariants
predicate IsValidState_Subjects(k:State)
{
    // 1. Subjects
    //// Condition 1.1 Drivers and devices must have different subject IDs
    //// [NOTE] The model syntax defines that different subjects of the same  
    //// type (Driver/Device) have different IDs
    (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)) &&

    //// Condition 1.2 Non-empty set of subjects
    (|MapGetKeys<Drv_ID, Drv_State>(k.subjects.drvs)| + 
     |MapGetKeys<Dev_ID, Dev_State>(k.subjects.devs)| > 0) &&

    (true)
}

predicate IsValidState_Objects(k:State)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
{
    // 2. Objects
    //// Condition 2.1 TDs, FDs and DOs must have different object IDs
    //// [NOTE] The model syntax defines that different objects of the same  
    //// type (TD/FD/DO) have different IDs
    (forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
        ==> td_id != fd_id) &&
    (forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
        ==> td_id != do_id) &&
    (forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
        ==> fd_id != do_id) &&
    
    //// Condition 2.2 Non-empty set of objects
    //// [NOTE] An I/O system may have 0 TD or 0 FD or 0 DO. For example, a 
    //// device may just poll the DOs of the device and perform fixed operation  
    //// on them, and hence has no TD or FD in the device
    (|MapGetKeys<TD_ID, TD_State>(k.objects.tds)| + 
     |MapGetKeys<FD_ID, FD_State>(k.objects.fds)| + 
     |MapGetKeys<DO_ID, DO_State>(k.objects.dos)| > 0) &&

    //// Condition 2.n1 Each device's TDs must include its hardcoded TD
    (forall dev_id :: dev_id in k.subjects.devs
        ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids) &&

    //// Condition 2.6 No two subjects associates (owns) the same object
    (forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2) && 

    //// Condition 2.n2 TDs/FDs/DOs in subjects are also in the state
    (forall drv_id, td_id :: 
        drv_id in k.subjects.drvs && td_id in k.subjects.drvs[drv_id].td_ids
        ==> td_id in k.objects.tds) && 
    (forall dev_id, td_id :: 
        dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
        ==> td_id in k.objects.tds) &&

    (forall drv_id, fd_id :: 
        drv_id in k.subjects.drvs && fd_id in k.subjects.drvs[drv_id].fd_ids
        ==> fd_id in k.objects.fds) && 
    (forall dev_id, fd_id :: 
        dev_id in k.subjects.devs && fd_id in k.subjects.devs[dev_id].fd_ids
        ==> fd_id in k.objects.fds) &&

    (forall drv_id, do_id :: 
        drv_id in k.subjects.drvs && do_id in k.subjects.drvs[drv_id].do_ids
        ==> do_id in k.objects.dos) && 
    (forall dev_id, do_id :: 
        dev_id in k.subjects.devs && do_id in k.subjects.devs[dev_id].do_ids
        ==> do_id in k.objects.dos) &&

    //// Condition 2.5 No hardcoded TD defines direct transfers to any TD with both read and write access modes
    var hcoded_tds := BuildMap_DevsToHCodedTDVals(k.subjects, k.objects);
    (forall dev_id :: dev_id in k.subjects.devs
        ==> (forall td_id :: td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
            ==> HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds[td_id].amodes != {R,W})) &&

    //// Condition 2.n4 Hardcoded TDs do not reference any hardcoded TDs
    (forall dev_id, td_id :: dev_id in k.subjects.devs &&
                td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
        ==> td_id !in AllHCodedTDIDs(k.subjects)) &&

    //// Condition 2.4 Objects refed in hardcoded TDs must be associated (owned) by the device
    (forall dev_id :: dev_id in k.subjects.devs
        ==> (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
                IDToDev(k, dev_id).td_ids) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
                IDToDev(k, dev_id).fd_ids) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
                IDToDev(k, dev_id).do_ids)) &&
    //// Known from Axioms: Arbitary set of TDs have finite ranges
    IsValidState_TDsToAllStates(k) &&

    (true)
}

predicate IsValidState_Partitions(k:State)
{
    (NULL !in k.pids) &&

    (true)
}

predicate IsValidState_ReachableTDsStates(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
{
    //// Condition 5.5 For each tds_state2 in <AllReachableActiveTDsStates(k)>, any 
    //// active TDs read by any active devices have no invalid references to 
    //// I/O objects. A TD contains valid references only: For all transfers in the 
    //// TD, they can only point to objects in the same partition with the TD
    (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
        ==> (forall td_id2, dev_id :: 
            dev_id in AllActiveDevs(k) && 
                // The device (<dev_id>) is active
            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(KToKParams(k), tds_state2, td_id2))) &&
                // The TD contains valid references only
                // This is DoTDOnlyRefsNonHCodedTDObjsInState

    (true)
}

predicate IsValidState_SubjsOwnObjsThenInSamePartition(k:State)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires forall drv_id, td_id :: 
                drv_id in k.subjects.drvs && td_id in k.subjects.drvs[drv_id].td_ids
                ==> td_id in k.objects.tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    requires forall drv_id, fd_id :: 
                drv_id in k.subjects.drvs && fd_id in k.subjects.drvs[drv_id].fd_ids
                ==> fd_id in k.objects.fds
    requires forall dev_id, fd_id :: 
                dev_id in k.subjects.devs && fd_id in k.subjects.devs[dev_id].fd_ids
                ==> fd_id in k.objects.fds
    requires forall drv_id, do_id :: 
                drv_id in k.subjects.drvs && do_id in k.subjects.drvs[drv_id].do_ids
                ==> do_id in k.objects.dos 
    requires forall dev_id, do_id :: 
                dev_id in k.subjects.devs && do_id in k.subjects.devs[dev_id].do_ids
                ==> do_id in k.objects.dos
{
    Lemma_ObjsInSubjsAreAlsoInState(k);

    // For all objects in subjects, the PID of each object is the same
    // with the PID of its owner subject
    (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
        ==> SubjPID(k, s_id) == ObjPID(k, o_id)) &&

    (true)
}

// Does the state <k> fulfill all the trival state invariants
predicate IsValidState(k:State)
{
    IsValidState_Subjects(k) && IsValidState_Objects(k) && 
    IsValidState_Partitions(k) && IsValidState_ReachableTDsStates(k) && 
    IsValidState_SubjsOwnObjsThenInSamePartition(k)
}




//******** SIs and TCs  ********//
predicate IsSecureState_SI1(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires IsValidState_ReachableTDsStates(k)
{
    // SI1: For each reachable active TDs' state, any active TDs read by any 
    // active devices only point to objects in the same partition with the TD
    (forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
        ==> (forall td_id2, dev_id :: 
            dev_id in AllActiveDevs(k) && 
                // The device (<dev_id>) is active
            td_id2 in TDsStateGetTDIDs(tds_state2) &&
                // The TD (<td_id2>) is active
            CanActiveDevReadActiveTD(KToKParams(k), tds_state2, dev_id, td_id2)
                // The TD is read by the device
            ==> !DoActiveTDIncludeTransfersToObjOutsidePartition(KToKParams(k), tds_state2, td_id2))) &&
                // The TD contains secure references only 
                // This is DoTDOnlyRefsObjsInSamePartition
    
    (true)
}

predicate IsSecureState_SI2(k:State)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id
{
    // SI2: Active subjects and objects must be belong to existing partitions
    (forall s_id :: s_id in AllSubjsIDs(k.subjects) && SubjPID(k, s_id) != NULL
        ==> SubjPID(k, s_id) in k.pids) &&
    (forall o_id :: o_id in AllObjsIDs(k.objects) && ObjPID(k, o_id) != NULL
        ==> ObjPID(k, o_id) in k.pids) &&

    (true)
}

// Returns if a state fulfills all the non-trival state invariants (SIs)
predicate IsSecureState(k:State)
    requires (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid))
    requires IsValidState_Objects(k)
    requires IsValidState_ReachableTDsStates(k)
{
    IsSecureState_SI1(k) && IsSecureState_SI2(k)
}

// Returns if an operation fulfills all transition constraints (TCs)
// The operation transits from <k> to <k'>
predicate IsSecureOps(k:State, k':State)
    requires forall dev_id :: dev_id in k.subjects.devs
        ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
{
    // 3. State variables to ease the verification
    (k'.tds_to_all_states == k.tds_to_all_states) &&
                     
    // Known from Axioms: immutable and unique IDs 
    (forall drv_id :: 
        drv_id in k'.subjects.drvs <==> drv_id in k.subjects.drvs) &&
    (forall dev_id :: 
        dev_id in k'.subjects.devs <==> dev_id in k.subjects.devs) && 
    (forall td_id :: 
        td_id in k'.objects.tds <==> td_id in k.objects.tds) && 
    (forall fd_id :: 
        fd_id in k'.objects.fds <==> fd_id in k.objects.fds) && 
    (forall do_id :: 
        do_id in k'.objects.dos <==> do_id in k.objects.dos) &&

    // TC1: All fields of subjects except the partition ID field are immutable
    (forall drv_id :: 
        drv_id in k'.subjects.drvs
        ==>
        (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
        (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
        (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: 
        dev_id in k'.subjects.devs
        ==>
        (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
        (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
        (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
        (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)) &&

    // TC2: No TD (except hardcoded TD)/FD/DO reuse in a new partition
    //// TC2.1: No TD (except hardcoded TD) reuse in a new partition
    (forall td_id :: td_id in k'.objects.tds &&
                    k'.objects.tds[td_id].pid != k.objects.tds[td_id].pid &&
                    k'.objects.tds[td_id].pid != NULL &&
                        // For a transition from k to k', if a TD is activated (or moved) into a partition
                    td_id !in AllHCodedTDIDs(k'.subjects)
                        // TD is not a hardcoded TD
        ==> IsTDClearVal(k'.objects.tds, td_id)) &&
                // TD is cleared
    //// TC2.2: No FD reuse in a new partition
    (forall fd_id :: fd_id in k'.objects.fds &&
                    k'.objects.fds[fd_id].pid != k.objects.fds[fd_id].pid &&
                    k'.objects.fds[fd_id].pid != NULL
                        // For a transition from k to k', if a FD is activated (or moved) into a partition
        ==> IsFDClearVal(k'.objects.fds, fd_id)) &&
                // FD is cleared
    //// TC2.3: No DO reuse in a new partition
    (forall do_id :: do_id in k'.objects.dos &&
                    k'.objects.dos[do_id].pid != k.objects.dos[do_id].pid &&
                    k'.objects.dos[do_id].pid != NULL
                        // For a transition from k to k', if a DO is activated (or moved) into a partition
        ==> IsDOClearVal(k'.objects.dos, do_id)) &&
                // DO is cleared
        
    // TC3: Hardcoded TDs' values are immutable
    (forall dev_id :: 
        dev_id in k'.subjects.devs
        ==>
        (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
        (k'.objects.tds[k'.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val)) &&

    (true)
}
