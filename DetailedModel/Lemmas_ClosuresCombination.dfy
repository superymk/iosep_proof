include "../Abstract/Properties.dfy"
include "K_AdditionalPropertiesLemmas.dfy"
include "Util_Lemmas.dfy"
include "Lemmas_Ops_Common.dfy"

predicate ReachableTDsStates_PreConditionsOfK(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
{
    var k_subjects := k_params.subjects;
    var k_objs_td_ids := k_params.objs_td_ids;
    var k_objs_fd_ids := k_params.objs_fd_ids;
    var k_objs_do_ids := k_params.objs_do_ids;

    K_UniqueIDsAndOwnedObjs(k_subjects, k_objs_td_ids, k_objs_fd_ids, k_objs_do_ids) &&
    (forall drv_id :: drv_id in k_subjects.drvs
                ==> (forall td_id :: td_id in k_subjects.drvs[drv_id].td_ids
                        ==> td_id.oid in k_all_objs_ids) &&
                    (forall fd_id :: fd_id in k_subjects.drvs[drv_id].fd_ids
                        ==> fd_id.oid in k_all_objs_ids) &&
                    (forall do_id :: do_id in k_subjects.drvs[drv_id].do_ids
                        ==> do_id.oid in k_all_objs_ids))&&
    (forall dev_id :: dev_id in k_subjects.devs
                ==> (forall td_id :: td_id in k_subjects.devs[dev_id].td_ids
                        ==> td_id.oid in k_all_objs_ids) &&
                    (forall fd_id :: fd_id in k_subjects.devs[dev_id].fd_ids
                        ==> fd_id.oid in k_all_objs_ids) &&
                    (forall do_id :: do_id in k_subjects.devs[dev_id].do_ids
                        ==> do_id.oid in k_all_objs_ids))&&
    (forall dev_id2 :: dev_id2 in k_subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_subjects, dev_id2).td_ids <= k_objs_td_ids)&&

    (true)
}

predicate WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>, 
    active_clrX_devs:set<Dev_ID>, clrX_tds_state0:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires active_clrX_devs <= AllActiveDevs_SlimState(k_params.subjects)
{
    var k_subjects := k_params.subjects;
    var k_objs_td_ids := k_params.objs_td_ids;
    var k_objs_fd_ids := k_params.objs_fd_ids;
    var k_objs_do_ids := k_params.objs_do_ids;

    (forall clrX_tds_state2 :: TDsStateGetTDIDs(clrX_tds_state2) == k_params.all_active_tds &&
                    (clrX_tds_state0 == clrX_tds_state2 || 
                        (    IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                active_clrX_devs, clrX_tds_state0, clrX_tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params,  
                                active_clrX_devs, clrX_tds_state0, clrX_tds_state2)))
                                    // clrX_tds_state0 -->* clrX_tds_state2
                ==> (forall td_id2, dev_id :: 
                        dev_id in active_clrX_devs && 
                            // The device (<dev_id>) is an active OS device
                        td_id2 in TDsStateGetTDIDs(clrX_tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD_PreConditions(k_params, clrX_tds_state2, dev_id, td_id2) &&
                        CanActiveDevReadActiveTD(k_params, clrX_tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrX_tds_state2, td_id2))) &&
        // Requirement: Forall clrX_tds_state2 that can be reached from 
        // clrX_tds_state0 (due to TD writes by active_clrX_devs only), TDs readable
        // by active_clrX_devs have no invalid refs

    (true)
}

predicate WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(
    k_params:ReachableTDsKParams,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    k_tds_state:TDs_Vals, clrA_tds_state:TDs_Vals, clrB_tds_state:TDs_Vals
)
{
    TDsStateGetTDIDs(k_tds_state) == k_params.all_active_tds &&
    TDsStateGetTDIDs(clrA_tds_state) == k_params.all_active_tds &&
    TDsStateGetTDIDs(clrB_tds_state) == k_params.all_active_tds &&

    (forall td_id :: td_id in clrA_tds_state
                ==> (td_id in active_clrA_tds ==> k_tds_state[td_id] == clrA_tds_state[td_id]) &&
                    (td_id !in active_clrA_tds ==> clrA_tds_state[td_id] == TD_Val(map[], map[], map[]))) &&
    (forall td_id :: td_id in clrB_tds_state
                ==> (td_id in active_clrB_tds ==> k_tds_state[td_id] == clrB_tds_state[td_id]) &&
                    (td_id !in active_clrB_tds ==> clrB_tds_state[td_id] == TD_Val(map[], map[], map[]))) &&
        // Requirement: <k_tds_state> is the merge of <clrA_tds_state> and 
        // <clrB_tds_state>

    (true)
}

predicate WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,
    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    k_tds_state:TDs_Vals, clrA_tds_state:TDs_Vals, clrB_tds_state:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    
    requires k_params.all_active_tds <= k_params.objs_td_ids
    requires forall td_id :: td_id in k_params.objs_td_ids
                ==> td_id.oid in k_params.objs_pids
{
    var k_subjects := k_params.subjects;
    Lemma_K_AllActiveSubjs_SlimState_Property(k_subjects);
    assert forall s_id :: s_id in AllActiveSubjs_SlimState(k_subjects)
                ==> IsSubjID(k_subjects, s_id);

    (active_clrA_subjs + active_clrB_subjs == AllActiveSubjs_SlimState(k_subjects)) &&
    (active_clrA_subjs * active_clrB_subjs == {}) &&
        // Requirement: All active subjects include the disjunction sets  
        // <active_clrA_subjs> and <active_clrB_subjs>
    (forall s_id1, s_id2 :: s_id1 in active_clrA_subjs && s_id2 in active_clrB_subjs
        ==> SubjPID_SlimState(k_subjects, s_id1) != SubjPID_SlimState(k_subjects, s_id2)) &&
        // Requirement: <active_clrA_subjs> and <active_clrB_subjs> are in different I/O partitions
    (active_clrA_devs + active_clrB_devs == AllActiveDevs_SlimState(k_subjects)) &&
    (active_clrA_devs * active_clrB_devs == {}) &&
        // Requirement: All active devs include the disjunction sets  
        // <active_clrA_devs> and <active_clrB_devs>
    (forall dev_id1, dev_id2 :: dev_id1 in active_clrA_devs && dev_id2 in active_clrB_devs
        ==> SubjPID_DevID_SlimState(k_subjects, dev_id1) != SubjPID_DevID_SlimState(k_subjects, dev_id2)) &&
        // Requirement: <active_clrA_devs> and <active_clrB_devs> are in different
        // I/O partitions

    (active_clrA_tds + active_clrB_tds == k_params.all_active_tds) &&
    (active_clrA_tds * active_clrB_tds == {}) &&
        // Requirement: All active TDs include the disjunction sets <active_clrA_tds> 
        // and <active_clrB_tds>
    (forall td_id1, td_id2 :: td_id1 in active_clrA_tds && td_id2 in active_clrB_tds
                ==> ObjPID_SlimState(k_params.objs_pids, td_id1.oid) != 
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid)) &&
        // Requirement: <active_clrA_tds> and <active_clrB_tds> are in different I/O partitions
    (forall dev_id :: dev_id in active_clrA_devs
        ==> OwnedTDs_SlimState(k_subjects, dev_id.sid) <= active_clrA_tds) &&
    (forall dev_id :: dev_id in active_clrA_devs
        <==> IsDevID_SlimState(k_subjects, dev_id) && dev_id.sid in active_clrA_subjs) &&
    (forall dev_id :: dev_id in active_clrB_devs
        ==> OwnedTDs_SlimState(k_subjects, dev_id.sid) <= active_clrB_tds) &&
    (forall dev_id :: dev_id in active_clrB_devs
        <==> IsDevID_SlimState(k_subjects, dev_id) && dev_id.sid in active_clrB_subjs) &&
        // Requirement: <active_clrA_tds> are all TDs of <active_clrA_devs>, and
        // <active_clrB_tds> are all TDs of <active_clrB_devs>,

    (forall dev_id, td_id :: dev_id in active_clrA_devs && td_id in active_clrB_tds
                ==> SubjPID_DevID_SlimState(k_params.subjects, dev_id) != 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)) &&
    (forall dev_id, td_id :: dev_id in active_clrB_devs && td_id in active_clrA_tds
                ==> SubjPID_DevID_SlimState(k_params.subjects, dev_id) != 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)) &&

    WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
        active_clrA_tds, active_clrB_tds,
        k_tds_state, clrA_tds_state, clrB_tds_state) &&
        
    (true)
}

predicate WKStateToKState_SubjsOwnObjsThenInSamePartition(
    k_params:ReachableTDsKParams
)
    requires K_UniqueIDsAndOwnedObjs(k_params.subjects, k_params.objs_td_ids, k_params.objs_fd_ids, k_params.objs_do_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
{
    var k_subjects := k_params.subjects;

    (forall s_id, o_id :: s_id in AllSubjsIDs(k_subjects) && DoOwnObj_SlimState(k_subjects, s_id, o_id)
        ==> SubjPID_SlimState(k_subjects, s_id) == ObjPID_SlimState(k_params.objs_pids, o_id)) &&
        // Requirement from IsValidState_SubjsOwnObjsThenInSamePartition

    (true)
}




//******** Utility Lemmas ********//
// (needs 200s to verify)
lemma Lemma_WKStateToKState_ActiveClrADevsNeverReadClrBTDs(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    dev_id:Dev_ID,
    k_tds_state:TDs_Vals, clrA_tds_state:TDs_Vals, clrB_tds_state:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_state, clrA_tds_state, clrB_tds_state)

    requires forall td_id2, dev_id :: 
                dev_id in active_clrA_devs && 
                    // The device (<dev_id>) is an active OS device
                td_id2 in TDsStateGetTDIDs(clrA_tds_state) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD_PreConditions(k_params, clrA_tds_state, dev_id, td_id2) &&
                CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id2)
                    // The TD is read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrA_tds_state, td_id2)
        // Requirement: <clrA_tds_state> has no invalid refs in TDs read by 
        // active OS/wimp devices

    requires dev_id in active_clrA_devs
        // The device (<dev_id>) is active and with clrA

    ensures forall td_id2 :: 
                    td_id2 in TDsStateGetTDIDs(k_tds_state)
                ==> CanActiveDevReadActiveTD_PreConditions(k_params, k_tds_state, dev_id, td_id2)

    ensures forall td_id2 :: 
                    td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
                        // The TD is read by the device
                ==> td_id2 in active_clrA_tds

    ensures forall td_id2 :: 
                    td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
                        // The TD is read by the device
                ==> CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id2)
{
    var k_subjects := k_params.subjects;

    forall td_id2 | td_id2 in TDsStateGetTDIDs(k_tds_state)
        ensures CanActiveDevReadActiveTD_PreConditions(k_params, k_tds_state, dev_id, td_id2)
    {
        assert CanActiveDevReadActiveTD_KParams_PreConditions(k_params);
    }

    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(active_clrA_tds, active_clrB_tds);
    forall td_id2 | td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
        ensures td_id2 in active_clrA_tds
        ensures CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id2)
    {
        var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
                (forall td_id3 :: td_id3 in td_ids ==> td_id3 in k_tds_state) &&
                                                // A list of active TDs
                td_ids[|td_ids| - 1] == td_id2 && // last TD is the TD (<td_id2>)
                td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[i]]));
        
        assert td_ids[0] in active_clrA_tds;

        var new_td_ids:seq<TD_ID> := [td_ids[0]];
        assert |new_td_ids| >= 1 && 
                (forall td_id3 :: td_id3 in new_td_ids ==> td_id3 in clrA_tds_state) &&
                                                // A list of active TDs
                new_td_ids[|new_td_ids| - 1] == new_td_ids[0] && // last TD is the TD (<td_id2>)
                new_td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id;
                                            // first TD must be the hardcoded TD
        assert CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_ids[0]);
        
        var i := 1;
        while (1 <= i < |td_ids|)
            invariant 1 <= i <= |td_ids|

            invariant forall td_id :: td_id in td_ids[..i]
                        ==> td_id in active_clrA_tds

            invariant (forall j :: 0<=j<i - 1 ==> td_ids[j+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[j]])); 
            invariant forall td_id :: td_id in td_ids[..i]
                        ==> CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id)

            decreases |td_ids| - i
        {
            var td_id := td_ids[i];
            var tdx_id := td_ids[i-1];

            assert tdx_id in active_clrA_tds;
            assert CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, tdx_id);

            assert td_id in TDIDReadsInTDCfg(k_tds_state[tdx_id]);

            // Prove td_id !in active_clrB_tds
            if(td_id in active_clrB_tds)
            {
                assert ObjPID_SlimState(k_params.objs_pids, td_id.oid) != 
                       ObjPID_SlimState(k_params.objs_pids, tdx_id.oid);
                assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrA_tds_state, tdx_id);
            }
            assert td_id in active_clrA_tds;
            assert td_id in TDIDReadsInTDCfg(clrA_tds_state[tdx_id]);

            // Prove Invariant 1
            Lemma_Set_NextElemIsInSet_ThenAllElemInSet(td_ids, i, active_clrA_tds);
            // Prove Invariant 2
            i := i + 1;
        }
    }
}

// (needs 70s to verify)
lemma Lemma_WKStateToKState_NoInvalidRefInClrAAndClrBTDsState_ThenNoInvalidRefInKTDsState(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    k_tds_state:TDs_Vals, clrA_tds_state:TDs_Vals, clrB_tds_state:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_state, clrA_tds_state, clrB_tds_state)

    requires forall td_id2, dev_id :: 
                dev_id in active_clrA_devs && 
                    // The device (<dev_id>) is an active OS device
                td_id2 in TDsStateGetTDIDs(clrA_tds_state) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id2)
                    // The TD is read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrA_tds_state, td_id2)
    requires forall td_id2, dev_id :: 
                dev_id in active_clrB_devs && 
                    // The device (<dev_id>) is an active OS device
                td_id2 in TDsStateGetTDIDs(clrB_tds_state) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, clrB_tds_state, dev_id, td_id2)
                    // The TD is read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrB_tds_state, td_id2)
        // Requirement: <clrA_tds_state> and <clrB_tds_state> have no invalid 
        // refs in TDs read by active OS/wimp devices

    ensures forall td_id2, dev_id :: 
                dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                    // The device (<dev_id>) is active
                td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
                    // The TD is read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id2)
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(active_clrA_tds, active_clrB_tds);
    forall td_id2, dev_id | 
                    dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id2)
    {
        if(dev_id in active_clrA_devs)
        {
            // Prove td_id2 !in active_clrB_tds
            Lemma_WKStateToKState_ActiveClrADevsNeverReadClrBTDs(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                dev_id,
                k_tds_state, clrA_tds_state, clrB_tds_state);

            assert td_id2 !in active_clrB_tds;
            assert td_id2 in active_clrA_tds;

            assert CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id2);

            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrA_tds_state, td_id2);
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id2);
        }
        else
        {
            Lemma_WKStateToKState_ActiveClrADevsNeverReadClrBTDs(
                k_params, k_all_objs_ids,
                active_clrB_subjs, active_clrA_subjs,
                active_clrB_devs, active_clrA_devs,
                active_clrB_tds, active_clrA_tds,
                dev_id,
                k_tds_state, clrB_tds_state, clrA_tds_state);

            assert td_id2 !in active_clrA_tds;
            assert td_id2 in active_clrB_tds;

            assert CanActiveDevReadActiveTD(k_params, clrB_tds_state, dev_id, td_id2);

            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrB_tds_state, td_id2);
            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id2);
        }
    }
}

// Lemma: If k_from_tds_state have no invalid refs, and k_from_tds_state --> 
// k_to_tds_state, then active OS devices cannot modify wimp TDs
// (needs 100s to verify)
lemma Lemma_WKStateToKState_ActiveClrADevsNeverModifyClrBTDs(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    k_from_tds_state:TDs_Vals, clrA_from_tds_state:TDs_Vals, clrB_from_tds_state:TDs_Vals,
    k_to_tds_state:TDs_Vals, clrA_to_tds_state:TDs_Vals, clrB_to_tds_state:TDs_Vals,
    active_clrA_dev:Dev_ID
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_from_tds_state, clrA_from_tds_state, clrB_from_tds_state)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_to_tds_state, clrA_to_tds_state, clrB_to_tds_state)
    // Requirements required by functions in this function method
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids

    requires TDsStateGetTDIDs(k_from_tds_state) == TDsStateGetTDIDs(k_to_tds_state)
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_from_tds_state)
        // Requirement: In k_from_tds_state, all TDs read by active devices 
        // do not have invalid refs

    requires active_clrA_dev in AllActiveDevs_SlimState(k_params.subjects)
        // Requirement: <active_clrA_dev> is an active device
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, active_clrA_dev, k_from_tds_state, k_to_tds_state)
        // Requirement: k_from_tds_state --> k_to_tds_state
    requires active_clrA_dev in active_clrA_devs

    ensures clrB_from_tds_state == clrB_to_tds_state
{
    var k_subjects := k_params.subjects;

    // Prove by contradiction
    if (clrB_from_tds_state != clrB_to_tds_state)
    {
        var writing_td_id :| writing_td_id in TDsStateDiff(clrB_to_tds_state, clrB_from_tds_state);
        var writing_td_cfg := TDsStateDiff(clrB_to_tds_state, clrB_from_tds_state)[writing_td_id];

        assert (exists td_id2 :: td_id2 in k_params.all_active_tds &&
                                CanActiveDevReadActiveTD(k_params, k_from_tds_state, active_clrA_dev, td_id2) &&
                                        // There must be a TD (<td_id2>) can be 
                                        // read by the device (<active_clrA_dev>)
                                IsTDWriteInTD(k_from_tds_state, td_id2, writing_td_id, writing_td_cfg)) ||
                                        // The TD (<td_id2>) must contain a write TD 
                                        // transfer to modify <clrB_from_tds_state>
                (TDWriteTransferInTD(GetTransfersToTDsInHCodedTD_SlimState(k_params, active_clrA_dev),
                    writing_td_id, writing_td_cfg));
                           
        assert writing_td_id in active_clrB_tds;
        if(TDWriteTransferInTD(GetTransfersToTDsInHCodedTD_SlimState(k_params, active_clrA_dev),
                    writing_td_id, writing_td_cfg))
        {
            // Show conflicts
            assert writing_td_id !in OwnedTDs_SlimState(k_subjects, active_clrA_dev.sid);

            assert DevHCodedTDRefsObjsInSameDev_SlimState(k_subjects, k_params.hcoded_tds, active_clrA_dev);
            assert forall td_id :: td_id in GetTransfersToTDsInHCodedTD_SlimState(k_params, active_clrA_dev)
                    ==> td_id in OwnedTDs_SlimState(k_subjects, active_clrA_dev.sid);
        }
        else
        {
            var k_td_id :| k_td_id in k_params.all_active_tds &&
                                CanActiveDevReadActiveTD(k_params, k_from_tds_state, active_clrA_dev, k_td_id) &&
                                        // There must be a TD (<k_td_id>) can be 
                                        // read by the device (<active_clrA_dev>)
                                IsTDWriteInTD(k_from_tds_state, k_td_id, writing_td_id, writing_td_cfg);

            assert !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_from_tds_state, k_td_id);
            assert ObjPID_SlimState(k_params.objs_pids, k_td_id.oid) == 
                ObjPID_SlimState(k_params.objs_pids, writing_td_id.oid);

            // Prove SubjPID(k, active_clrA_dev) != ObjPID(k, k_td_id)
            Lemma_ActiveClrADevsHaveDifferentPIDsWithActiveClrBTDs_AndViceVersa(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_from_tds_state, clrA_from_tds_state, clrB_from_tds_state);
            assert SubjPID_DevID_SlimState(k_subjects, active_clrA_dev) != 
                ObjPID_SlimState(k_params.objs_pids, k_td_id.oid);

            // Show conflicts
            Lemma_CanActiveDevReadActiveTD_ActiveDevsCannotReadTDsInAnotherPartition(
                k_params, k_all_objs_ids,
                k_from_tds_state, active_clrA_dev, k_td_id);
        }
    }
}

// (needs 210s to verify)
lemma Lemma_IfClrADevCauseKTDsStateCanBeReachedInOneStep_ThenClrATDsStateCanBeReachedInOneStep(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    k_from_tds_state:TDs_Vals, clrA_from_tds_state:TDs_Vals, clrB_from_tds_state:TDs_Vals,
    k_to_tds_state:TDs_Vals, clrA_to_tds_state:TDs_Vals, clrB_to_tds_state:TDs_Vals,
    active_clrA_dev:Dev_ID
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_from_tds_state, clrA_from_tds_state, clrB_from_tds_state)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_to_tds_state, clrA_to_tds_state, clrB_to_tds_state)
    // Requirements required by functions in this function method
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids
    requires (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.hcoded_td_ids)

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_from_tds_state)
        // Requirement: In k_from_tds_state, all TDs read by active devices 
        // do not have invalid refs

    requires ActiveTDsStateIsSecure(k_params, active_clrA_devs, clrA_from_tds_state)
        // Requirement: <clrA_from_tds_state> has no invalid refs in TDs read by 
        // active OS/wimp devices

    requires active_clrA_dev in active_clrA_devs
        // Requirement: active_clrA_dev is an active OS device

    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, active_clrA_dev, k_from_tds_state, k_to_tds_state)
        // Requirement: k_from_tds_state --> k_to_tds_state

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, active_clrA_dev, clrA_from_tds_state, clrA_to_tds_state)
        // Property: clrA_from_tds_state --> clrA_to_tds_state
{
    var k_subjects := k_params.subjects;

    Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_Property(k_params,
                active_clrA_dev, k_from_tds_state, k_to_tds_state);
    Lemma_IsActiveTDsStateReachActiveTDsStateInOneStep_Property(k_params,
                active_clrA_dev, clrA_from_tds_state, clrA_to_tds_state);

    // Prove TDsStateDiff(clrA_to_tds_state, clrA_from_tds_state) == 
    //       TDsStateDiff(k_to_tds_state, k_from_tds_state)
    Lemma_WKStateToKState_ActiveClrADevsNeverModifyClrBTDs(
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_from_tds_state, clrA_from_tds_state, clrB_from_tds_state,
        k_to_tds_state, clrA_to_tds_state, clrB_to_tds_state,
        active_clrA_dev);
    assert clrB_from_tds_state == clrB_to_tds_state;
    assert TDsStateDiff(clrA_to_tds_state, clrA_from_tds_state) == 
           TDsStateDiff(k_to_tds_state, k_from_tds_state);

    var tds_diff := TDsStateDiff(clrA_to_tds_state, clrA_from_tds_state);
    
    assert IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, active_clrA_dev, k_from_tds_state, tds_diff);
    forall td_id, td_new_cfg | td_id in tds_diff &&
                    td_new_cfg == tds_diff[td_id]
        ensures ((exists tdx_id :: 
                            tdx_id in TDsStateGetTDIDs(clrA_from_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, clrA_from_tds_state, active_clrA_dev, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(clrA_from_tds_state, tdx_id, td_id, td_new_cfg)) ||
                                    // the active TD refs the TD with W and the new TD cfg
                    (TDWriteTransferInTD(GetTransfersToTDsInHCodedTD_SlimState(k_params, active_clrA_dev),
                            td_id, td_new_cfg)))
    {
        assert td_id in TDsStateDiff(k_to_tds_state, k_from_tds_state) &&
               td_new_cfg == TDsStateDiff(k_to_tds_state, k_from_tds_state)[td_id];

        Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_Apply(k_params,   
            active_clrA_dev, td_id, k_from_tds_state, tds_diff);
        assert ((exists tdx_id :: tdx_id in TDsStateGetTDIDs(k_from_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                                    CanActiveDevReadActiveTD(k_params, k_from_tds_state, active_clrA_dev, tdx_id) && 
                                            // exists an active TD readable by the device 
                                    IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg)) ||
                                            // the active TD refs the TD with W and the new TD cfg
                            (TDWriteTransferInTD(GetTransfersToTDsInHCodedTD_SlimState(k_params, active_clrA_dev),
                                    td_id, td_new_cfg)));

        if(TDWriteTransferInTD(GetTransfersToTDsInHCodedTD_SlimState(k_params, active_clrA_dev),
                                    td_id, td_new_cfg))
        {
            // Trival proof here
        }
        else
        {
            var tdx_id :| tdx_id in TDsStateGetTDIDs(k_from_tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, k_from_tds_state, active_clrA_dev, tdx_id) && 
                                    // exists an active TD readable by the device 
                            IsTDWriteInTD(k_from_tds_state, tdx_id, td_id, td_new_cfg);

            Lemma_WKStateToKState_ActiveClrADevsNeverReadClrBTDs(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                active_clrA_dev,
                k_from_tds_state, clrA_from_tds_state, clrB_from_tds_state);
            assert CanActiveDevReadActiveTD(k_params, clrA_from_tds_state, active_clrA_dev, tdx_id);
            assert IsTDWriteInTD(clrA_from_tds_state, tdx_id, td_id, td_new_cfg);
        }
    }
}

lemma Lemma_WKStateToState_AllReachableStatesAreSecure(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    tds_state2:TDs_Vals, os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires k_params == KToKParams(k)

    requires ActiveTDsState(k) == tds_state2 ||
                (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, AllActiveDevs(k), ActiveTDsState(k), tds_state2) &&
                 IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), tds_state2))
        // Requirement: ActiveTDsState(k) -->1+ tds_state2

    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
                ActiveTDsState(k), os_tds_state0, wimps_tds_state0)
    requires ReachableTDsStates_PreConditionsOfK(k_params, AllObjsIDs(k.objects))
    
    requires DM_DevsInRed(ws) <= AllActiveDevs_SlimState(k.subjects)
    requires DM_DevsInGreen(ws) <= AllActiveDevs_SlimState(k.subjects)
    requires DM_TDIDsInRed(ws) * DM_TDIDsInGreen(ws) == {}
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInRed(ws), os_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInGreen(ws), wimps_tds_state0)
        // Reachable red and green TDs' states have no invalid transfers in their closures

    ensures TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
{
    var k_params := KToKParams(k);

    if(ActiveTDsState(k) == tds_state2)
    {
        Lemma_WKStateToState_AllReachableStatesAreSecure_FirstTDsState(ws, k, k_params,
            tds_state2, os_tds_state0, wimps_tds_state0);
    }
    else
    {
        Lemma_WKStateToState_AllReachableStatesAreSecure_ChainedTDsStates(ws, k, k_params,
            tds_state2, os_tds_state0, wimps_tds_state0);
    }
}




//******** Utility Lemmas of Utility Lemmas  ********//
// Lemma: Forall dev_id in active_os_devs, and td_id in active_wimps_tds, 
// SubjPID(dev_id) != ObjPID(td_id), and same for wimp devs and OS TDs
// (needs 50s to verify)
lemma Lemma_ActiveClrADevsHaveDifferentPIDsWithActiveClrBTDs_AndViceVersa(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    k_tds_state:TDs_Vals, clrA_tds_state:TDs_Vals, clrB_tds_state:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_state, clrA_tds_state, clrB_tds_state)

    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
 
    ensures forall dev_id, td_id :: dev_id in active_clrA_devs && td_id in active_clrB_tds
                ==> SubjPID_DevID_SlimState(k_params.subjects, dev_id) != 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)
    ensures forall dev_id, td_id :: dev_id in active_clrB_devs && td_id in active_clrA_tds
                ==> SubjPID_DevID_SlimState(k_params.subjects, dev_id) != 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)
{
    // Dafny can automatically prove this lemma
}

// Lemma: If clr_tds_state0 -->* target_clr_tds_state, then TDs in target_clr_tds_state 
// readable by active_clr_devs have no invalid references
lemma Lemma_ReachableClrTDsStateHasNoInvalidRef(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,
    active_clr_devs:set<Dev_ID>,
    clr_tds_state0:TDs_Vals, target_clr_tds_state:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires active_clr_devs <= AllActiveDevs_SlimState(k_params.subjects)
    requires TDsStateGetTDIDs(clr_tds_state0) == k_params.all_active_tds
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(clr_tds_state0) == TDsStateGetTDIDs(target_clr_tds_state)

    requires forall clr_tds_state2 :: TDsStateGetTDIDs(clr_tds_state2) == k_params.all_active_tds &&
                    (clr_tds_state0 == clr_tds_state2 || 
                        (    IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                active_clr_devs, clr_tds_state0, clr_tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                active_clr_devs, clr_tds_state0, clr_tds_state2)))
                                    // clr_tds_state0 -->* clr_tds_state2
                ==> ActiveTDsStateIsSecure(k_params, active_clr_devs, clr_tds_state2)
        // Requirement: Forall clr_tds_state2 that can be reached from 
        // clr_tds_state0 (due to TD writes by active_clr_devs only), TDs readable
        // by active_clr_devs have no invalid refs

    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    active_clr_devs, clr_tds_state0, target_clr_tds_state);
        // Requirement: clr_tds_state0 -->* target_clr_tds_state

     ensures ActiveTDsStateIsSecure(k_params, active_clr_devs, target_clr_tds_state)
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas ********//
lemma Lemma_WKStateToState_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue_ReachableActiveTDsStatesHaveNoInvalidRefs_Summary(
    k_params:ReachableTDsKParams, tds_states:seq<TDs_Vals>, tds_state2:TDs_Vals
)
    requires |tds_states| > 0
    requires tds_states[|tds_states| - 1] == tds_state2

    requires forall tds_state3 :: tds_state3 in tds_states
                ==> (forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state3) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD_PreConditions(k_params, tds_state3, dev_id, td_id2) &&
                        CanActiveDevReadActiveTD(k_params, tds_state3, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state3, td_id2))

    ensures forall td_id2, dev_id :: 
                        dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                            // The device (<dev_id>) is active
                        td_id2 in TDsStateGetTDIDs(tds_state2) &&
                            // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD_PreConditions(k_params, tds_state2, dev_id, td_id2) &&
                        CanActiveDevReadActiveTD(k_params, tds_state2, dev_id, td_id2)
                            // The TD is read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state2, td_id2)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_ActiveRedGreenTDsAreInKTDsState(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,

    active_os_tds:set<TD_ID>, active_wimps_tds:set<TD_ID>,
    k_tds_state:TDs_Vals
)
    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    
    requires TDsStateGetTDIDs(k_tds_state) == k_params.all_active_tds
    requires active_os_tds + active_wimps_tds == k_params.all_active_tds
    requires active_os_tds * active_wimps_tds == {}

    ensures forall td_id :: td_id in active_os_tds ==> td_id in k_tds_state
    ensures forall td_id :: td_id in active_wimps_tds ==> td_id in k_tds_state
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_MultipleTDsStates_Summary(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>, k_objects_tds:map<TD_ID, TD_State>, 

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    clrA_tds_state0:TDs_Vals, clrB_tds_state0:TDs_Vals,
    k_tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>
)
    requires |k_tds_states| > 2

    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_states[0], clrA_tds_state0, clrB_tds_state0)
    // Requirements required by functions in this function method

    requires forall dev_id :: dev_id in k_devs
                ==> (IsDevID_SlimState(k_params.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL)

    requires (forall tds_state2 :: tds_state2 in k_tds_states
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
            |k_devs| == |k_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in AllActiveDevs_SlimState(k_params.subjects)) &&
            k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds) && // first TDs' state is the <ActiveTDsState(k)>
            (forall i :: 0<=i<|k_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                        k_devs[i], k_tds_states[i], k_tds_states[i+1]))
                    // ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]
        // Requirement: ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]

    requires forall tds_state2 :: tds_state2 in k_tds_states[..|k_tds_states|-1]
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_tds_states[|k_tds_states|-1])

    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
{
    // Dafny can automatically prove this lemma
}

// (needs 60s to verify)
lemma Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_MultipleTDsStates(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>, k_objects_tds:map<TD_ID, TD_State>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    clrA_tds_state0:TDs_Vals, clrB_tds_state0:TDs_Vals,
    clrA_tds_stateNMinus1:TDs_Vals, clrB_tds_stateNMinus1:TDs_Vals,
    clrA_tds_stateN:TDs_Vals, clrB_tds_stateN:TDs_Vals,
    k_tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>
)
    requires |k_tds_states| > 2

    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_states[0], clrA_tds_state0, clrB_tds_state0)
    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                active_clrA_tds, active_clrB_tds,
                k_tds_states[|k_tds_states|-2], clrA_tds_stateNMinus1, clrB_tds_stateNMinus1)
    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                active_clrA_tds, active_clrB_tds,
                k_tds_states[|k_tds_states|-1], clrA_tds_stateN, clrB_tds_stateN)
    // Requirements required by functions in this function method
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids
    requires (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.hcoded_td_ids)
    
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_clrA_devs, clrA_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_clrB_devs, clrB_tds_state0)

    requires |k_devs| == |k_tds_states| - 1 
    requires forall dev_id :: dev_id in k_devs
                ==> (IsDevID_SlimState(k_params.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL)
        // Requirement: Devices in <k_devs> are active in k

    requires k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds)
        // First TDs' state is the <ActiveTDsState(k)>
    requires (forall tds_state2 :: tds_state2 in k_tds_states
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
            |k_devs| == |k_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in AllActiveDevs_SlimState(k_params.subjects)) &&
            k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds) && // first TDs' state is the <ActiveTDsState(k)>
            (forall i :: 0<=i<|k_tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_devs[i], k_tds_states[i], k_tds_states[i+1]))
                    // ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]
        // Requirement: ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]

    requires k_devs[|k_devs|-1] in active_clrA_devs

    requires forall clr_tds_state2 :: TDsStateGetTDIDs(clr_tds_state2) == k_params.all_active_tds &&
                    (clrA_tds_state0 == clr_tds_state2 || 
                        (   IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, 
                                active_clrA_devs, clrA_tds_state0, clr_tds_state2) &&
                            IsActiveTDsStateReachActiveTDsStateInChain(k_params, 
                                active_clrA_devs, clrA_tds_state0, clr_tds_state2)))
                                    // clrA_tds_state0 -->* clr_tds_state2
                ==> ActiveTDsStateIsSecure(k_params, active_clrA_devs, clr_tds_state2)
        // Requirement 0: The closure of red TDs are secure
    requires (clrA_tds_state0 == clrA_tds_stateNMinus1) ||
             IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrA_devs, clrA_tds_state0, clrA_tds_stateNMinus1)
    requires (clrB_tds_state0 == clrB_tds_stateNMinus1) ||
             IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrB_devs, clrB_tds_state0, clrB_tds_stateNMinus1)
        // Requirement 1                
    requires forall tds_state2 :: tds_state2 in k_tds_states[..|k_tds_states|-1]
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
        // Requirement 2
     
    ensures TDsStateGetTDIDs(k_tds_states[|k_tds_states|-2]) == TDsStateGetTDIDs(k_tds_states[|k_tds_states|-1])
        // Properties needed by the properties below
    ensures (clrA_tds_state0 == clrA_tds_stateN) ||
            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrA_devs, clrA_tds_state0, clrA_tds_stateN)
    ensures (clrB_tds_state0 == clrB_tds_stateN) || 
            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrB_devs, clrB_tds_state0, clrB_tds_stateN)
        // Property 1:
    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
        // Property 2: In any active TDs' state (active TDs of k) reachable from 
        // ActiveTDsState(k), TDs readable by active devs have no invalid refs
{
    var k_from_tds_state := k_tds_states[|k_tds_states|-2];
    var k_to_tds_state := k_tds_states[|k_tds_states|-1];
    var k_dev := k_devs[|k_devs|-1];

    // Prove active_clrA_tds and active_clrB_tds in k_to_tds_state
    assert TDsStateGetTDIDs(k_to_tds_state) == TDsStateGetTDIDs(k_from_tds_state);
    assert forall td_id :: td_id in active_clrB_tds ==> td_id in k_to_tds_state;
    assert forall td_id :: td_id in active_clrA_tds ==> td_id in k_to_tds_state;

    var from_clrA_tds_state := clrA_tds_stateNMinus1;
    var to_clrA_tds_state := clrA_tds_stateN;
    var from_clrB_tds_state := clrB_tds_stateNMinus1;
    var to_clrB_tds_state := clrB_tds_stateN;
  
    assert forall td_id :: td_id in to_clrA_tds_state
        ==> (td_id in active_clrA_tds ==> k_to_tds_state[td_id] == to_clrA_tds_state[td_id]) &&
            (td_id !in active_clrA_tds ==> to_clrA_tds_state[td_id] == TD_Val(map[], map[], map[]));

    // Prove from_clrA_tds_state --> to_clrA_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, k_from_tds_state, k_to_tds_state);
    
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_tds_states[|k_tds_states|-2]);
    Lemma_K_WholeClosureIsGood_ThenSubsetClosureIsGood(k_params, active_clrA_devs, active_clrA_tds, k_tds_states[|k_tds_states|-2], from_clrA_tds_state);
    assert ActiveTDsStateIsSecure(k_params, active_clrA_devs, from_clrA_tds_state);
    Lemma_IfClrADevCauseKTDsStateCanBeReachedInOneStep_ThenClrATDsStateCanBeReachedInOneStep( 
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_from_tds_state, from_clrA_tds_state, from_clrB_tds_state,
        k_to_tds_state, to_clrA_tds_state, to_clrB_tds_state,
        k_dev);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, from_clrA_tds_state, to_clrA_tds_state);

    // Prove clrA_tds_state0 -->* to_clrA_tds_state with active_clrA_devs
    if (clrA_tds_state0 != from_clrA_tds_state)
    {
        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                    active_clrA_devs, clrA_tds_state0, from_clrA_tds_state);
        Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(k_params,
            k_dev, active_clrA_devs,
            clrA_tds_state0, from_clrA_tds_state, to_clrA_tds_state);
    }
    else
    {
        Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params,
            k_dev, active_clrA_devs, clrA_tds_state0, to_clrA_tds_state);
    }
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                active_clrA_devs, clrA_tds_state0, to_clrA_tds_state);

    Lemma_ReachableClrTDsStateHasNoInvalidRef(k_params, k_all_objs_ids,
            active_clrA_devs, clrA_tds_state0, to_clrA_tds_state);
    assert ActiveTDsStateIsSecure(k_params, active_clrA_devs, to_clrA_tds_state);

    // Prove from_clrB_tds_state == to_clrB_tds_state
    Lemma_WKStateToKState_ActiveClrADevsNeverModifyClrBTDs(
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_from_tds_state, from_clrA_tds_state, from_clrB_tds_state,
        k_to_tds_state, to_clrA_tds_state, to_clrB_tds_state,
        k_dev);
    assert from_clrB_tds_state == to_clrB_tds_state;

    // Prove clrB_tds_state0 -->* to_clrB_tds_state with active_clrB_devs
    assert clrB_tds_state0 == to_clrB_tds_state ||
            IsActiveTDsStateReachActiveTDsStateInChain(k_params,
                active_clrB_devs, clrB_tds_state0, to_clrB_tds_state);

    Lemma_WKStateToKState_NoInvalidRefInClrAAndClrBTDsState_ThenNoInvalidRefInKTDsState(
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_to_tds_state, to_clrA_tds_state, to_clrB_tds_state
    );

    // Summary
    Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_MultipleTDsStates_Summary(
        k_params, k_all_objs_ids, k_objects_tds,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        clrA_tds_state0, clrB_tds_state0,
        k_tds_states, k_devs);
}

// (needs 230s to verify)
lemma Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_TwoTDsStates(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>, k_objects_tds:map<TD_ID, TD_State>,

    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    clrA_tds_state0:TDs_Vals, clrB_tds_state0:TDs_Vals,
    clrA_tds_stateN:TDs_Vals, clrB_tds_stateN:TDs_Vals,
    k_tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>
)
    requires |k_tds_states| == 2

    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_states[0], clrA_tds_state0, clrB_tds_state0)
    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                active_clrA_tds, active_clrB_tds,
                k_tds_states[1], clrA_tds_stateN, clrB_tds_stateN)
    // Requirements required by functions in this function method
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids
    requires (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.hcoded_td_ids)

    requires |k_devs| == |k_tds_states| - 1 
    requires forall dev_id :: dev_id in k_devs
                ==> (IsDevID_SlimState(k_params.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL)
        // Requirement: Devices in <k_devs> are active in k

    requires k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds)
        // First TDs' state is the <ActiveTDsState(k)>
    requires (|k_tds_states| == 1 && k_tds_states[|k_tds_states|-1] == ActiveTDsState_SlimState(k_objects_tds)) ||
                    // k_tds_states == [ActiveTDsState(k)], Or
             (|k_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                |k_devs| == |k_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in AllActiveDevs_SlimState(k_params.subjects)) &&
                k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds) && // first TDs' state is the <ActiveTDsState(k)>
                (forall i :: 0<=i<|k_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_devs[i], k_tds_states[i], k_tds_states[i+1])))
                    // ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]
        // Requirement: ActiveTDsState(k) -->* k_tds_states[|k_tds_states| - 1]

    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_clrA_devs, clrA_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_clrB_devs, clrB_tds_state0)

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_tds_states[0])
        // Requirement: In k_tds_states[0], all TDs read by active devs have no
        // invalid refs

    requires k_devs[0] in active_clrA_devs
         
    ensures (clrA_tds_state0 == clrA_tds_stateN) ||
            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrA_devs, clrA_tds_state0, clrA_tds_stateN)
    ensures (clrB_tds_state0 == clrB_tds_stateN) || 
            IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrB_devs, clrB_tds_state0, clrB_tds_stateN)
    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
        // Property: In any active TDs' state (active TDs of k) reachable from 
        // ActiveTDsState(k), TDs readable by active devs have no invalid refs
{
    var k_from_tds_state := k_tds_states[0];
    var k_to_tds_state :=  k_tds_states[1];
    var k_dev := k_devs[0];

    var from_clrA_tds_state := clrA_tds_state0;
    var to_clrA_tds_state := clrA_tds_stateN;
    var from_clrB_tds_state := clrB_tds_state0;
    var to_clrB_tds_state := clrB_tds_stateN;

    assert forall td_id :: td_id in to_clrA_tds_state
        ==> (td_id in active_clrA_tds ==> k_to_tds_state[td_id] == to_clrA_tds_state[td_id]) &&
            (td_id !in active_clrA_tds ==> to_clrA_tds_state[td_id] == TD_Val(map[], map[], map[]));

    // Prove from_clrA_tds_state --> to_clrA_tds_state
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, k_from_tds_state, k_to_tds_state);
    Lemma_IfClrADevCauseKTDsStateCanBeReachedInOneStep_ThenClrATDsStateCanBeReachedInOneStep(
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_from_tds_state, from_clrA_tds_state, from_clrB_tds_state,
        k_to_tds_state, to_clrA_tds_state, to_clrB_tds_state,
        k_dev);
    assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, from_clrA_tds_state, to_clrA_tds_state);

    // Prove from_clrA_tds_state -->* to_clrA_tds_state with active_clrA_devs
    Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params,
            k_dev, active_clrA_devs, from_clrA_tds_state, to_clrA_tds_state);
    assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_clrA_devs, from_clrA_tds_state, to_clrA_tds_state);

    Lemma_ReachableClrTDsStateHasNoInvalidRef(
            k_params, k_all_objs_ids,
            active_clrA_devs, from_clrA_tds_state, to_clrA_tds_state);
    assert ActiveTDsStateIsSecure(k_params, active_clrA_devs, to_clrA_tds_state);

    // Prove from_clrB_tds_state == to_clrB_tds_state
    Lemma_WKStateToKState_ActiveClrADevsNeverModifyClrBTDs(
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_from_tds_state, from_clrA_tds_state, from_clrB_tds_state,
        k_to_tds_state, to_clrA_tds_state, to_clrB_tds_state,
        k_dev);
    assert from_clrB_tds_state == to_clrB_tds_state;

    Lemma_WKStateToKState_NoInvalidRefInClrAAndClrBTDsState_ThenNoInvalidRefInKTDsState(
        k_params, k_all_objs_ids,
        active_clrA_subjs, active_clrB_subjs,
        active_clrA_devs, active_clrB_devs,
        active_clrA_tds, active_clrB_tds,
        k_to_tds_state, to_clrA_tds_state, to_clrB_tds_state
    );
}

// (needs 270s to verify)
lemma Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_Internal(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>, k_objects_tds:map<TD_ID, TD_State>,
    
    active_os_subjs:set<Subject_ID>, active_wimps_subjs:set<Subject_ID>,
    active_os_devs:set<Dev_ID>, active_wimps_devs:set<Dev_ID>,
    active_os_tds:set<TD_ID>, active_wimps_tds:set<TD_ID>,
    os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals,
    os_tds_stateN:TDs_Vals, wimps_tds_stateN:TDs_Vals,
    k_tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>
)
    requires |k_tds_states| >= 1

    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_os_subjs, active_wimps_subjs,
                active_os_devs, active_wimps_devs,
                active_os_tds, active_wimps_tds,
                k_tds_states[0], os_tds_state0, wimps_tds_state0)
    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                active_os_tds, active_wimps_tds,
                k_tds_states[|k_tds_states|-1], os_tds_stateN, wimps_tds_stateN)
    // Requirements required by functions in this function method
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids
    requires (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.hcoded_td_ids)

    requires |k_devs| == |k_tds_states| - 1 
    requires forall dev_id :: dev_id in k_devs
                ==> (IsDevID_SlimState(k_params.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL &&
                    DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id) &&
                    IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= MapGetKeys(k_objects_tds))
        // Requirement: Devices in <k_devs> are active in k

    requires k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds)
        // First TDs' state is the <ActiveTDsState(k)>
    requires (|k_tds_states| == 1 && k_tds_states[|k_tds_states|-1] == ActiveTDsState_SlimState(k_objects_tds)) ||
                    // k_tds_states == [ActiveTDsState(k)], Or
             (|k_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                |k_devs| == |k_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in AllActiveDevs_SlimState(k_params.subjects)) &&
                k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds) && // first TDs' state is the <ActiveTDsState(k)>
                (forall i :: 0<=i<|k_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_devs[i], k_tds_states[i], k_tds_states[i+1])))
                    // ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]
        // Requirement: ActiveTDsState(k) -->* k_tds_states[|k_tds_states| - 1]

    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_os_devs, os_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_wimps_devs, wimps_tds_state0)

    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_tds_states[0])
        // Requirement: In k_tds_states[0], all TDs read by active devs have no
        // invalid refs
         
    ensures |k_tds_states| >= 2 
                 ==> (os_tds_state0 == os_tds_stateN || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_os_devs, os_tds_state0, os_tds_stateN))
    ensures |k_tds_states| >= 2 
                  ==> (wimps_tds_state0 == wimps_tds_stateN || 
                        IsActiveTDsStateReachActiveTDsStateInChain(k_params, active_wimps_devs, wimps_tds_state0, wimps_tds_stateN))
    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
        // Property: In any active TDs' state (active TDs of k) reachable from 
        // ActiveTDsState(k), TDs readable by active devs have no invalid refs
{
    if(|k_tds_states| == 1)
    {
        assert TDsStateGetTDIDs(k_tds_states[0]) == k_params.all_active_tds;
        assert ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_tds_states[0]);
        Lemma_OneElemSeq_AllElemsAreTheElem(k_tds_states);
    }
    else if(|k_tds_states| == 2)
    {
        var k_dev := k_devs[0];

        Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(active_os_tds, active_wimps_tds);
        if(k_dev in active_os_devs)
        {
            Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_TwoTDsStates(
                k_params, k_all_objs_ids, k_objects_tds,
                active_os_subjs, active_wimps_subjs,
                active_os_devs, active_wimps_devs,
                active_os_tds, active_wimps_tds,
                os_tds_state0, wimps_tds_state0,
                os_tds_stateN, wimps_tds_stateN,
                k_tds_states, k_devs);
        }
        else
        {
            assert k_dev in active_wimps_devs;

            Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_TwoTDsStates(
                k_params, k_all_objs_ids, k_objects_tds,
                active_wimps_subjs, active_os_subjs,
                active_wimps_devs, active_os_devs,
                active_wimps_tds, active_os_tds,
                wimps_tds_state0, os_tds_state0,
                wimps_tds_stateN, os_tds_stateN,
                k_tds_states, k_devs);
        }
    }
    else
    {
        assert |k_tds_states| > 2;

        var k'_tds_states := k_tds_states[..|k_tds_states|-1];
        var k'_devs := k_devs[..|k_devs|-1];
        Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_ActiveRedGreenTDsAreInKTDsState(
            k_params, k_all_objs_ids,
            active_os_tds, active_wimps_tds,
            k'_tds_states[|k'_tds_states|-1]
        );
        var os_tds_stateN' := MaskTDsState(k'_tds_states[|k'_tds_states|-1], active_wimps_tds);
        var wimps_tds_stateN' := MaskTDsState(k'_tds_states[|k'_tds_states|-1], active_os_tds);

        Lemma_SequenceHighlightLastElemOfSubSeq(k_tds_states, k'_tds_states);
        assert k'_tds_states[|k'_tds_states|-1] == k_tds_states[|k_tds_states|-2];
        Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(active_os_tds, active_wimps_tds);
        Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_Internal(
            k_params, k_all_objs_ids, k_objects_tds,
            active_os_subjs, active_wimps_subjs,
            active_os_devs, active_wimps_devs,
            active_os_tds, active_wimps_tds,
            os_tds_state0, wimps_tds_state0,
            os_tds_stateN', wimps_tds_stateN',
            k'_tds_states, k'_devs);

        var k_dev := k_devs[|k_devs|-1];
        var os_tds_stateNMinus1 := MaskTDsState(k_tds_states[|k_tds_states|-2], active_wimps_tds);
        var wimps_tds_stateNMinus1 := MaskTDsState(k_tds_states[|k_tds_states|-2], active_os_tds);
        Lemma_SequenceHighlightLastElemOfSubSeq(k_tds_states, k'_tds_states);
        assert k'_tds_states[|k'_tds_states|-1] == k_tds_states[|k_tds_states|-2];
       
        assert os_tds_stateN' == os_tds_stateNMinus1;
        assert wimps_tds_stateN' == wimps_tds_stateNMinus1;

        if(k_dev in active_os_devs)
        {
            Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_MultipleTDsStates(
                k_params, k_all_objs_ids, k_objects_tds,
                active_os_subjs, active_wimps_subjs,
                active_os_devs, active_wimps_devs,
                active_os_tds, active_wimps_tds,
                os_tds_state0, wimps_tds_state0,
                os_tds_stateNMinus1, wimps_tds_stateNMinus1,
                os_tds_stateN, wimps_tds_stateN,
                k_tds_states, k_devs);
        }
        else
        {
            assert k_dev in active_wimps_devs;

            Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_MultipleTDsStates(
                k_params, k_all_objs_ids, k_objects_tds,
                active_wimps_subjs, active_os_subjs,
                active_wimps_devs, active_os_devs,
                active_wimps_tds, active_os_tds,
                wimps_tds_state0, os_tds_state0, 
                wimps_tds_stateNMinus1, os_tds_stateNMinus1,
                wimps_tds_stateN, os_tds_stateN,
                k_tds_states, k_devs);
        }
    }
}

// (needs 80s to verify)
lemma Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>, k_objects_tds:map<TD_ID, TD_State>,

    active_os_subjs:set<Subject_ID>, active_wimps_subjs:set<Subject_ID>,
    active_os_devs:set<Dev_ID>, active_wimps_devs:set<Dev_ID>,
    active_os_tds:set<TD_ID>, active_wimps_tds:set<TD_ID>,
    os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals,
    k_tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>
)
    requires |k_tds_states| >= 1

    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> dev_id2 in k_params.hcoded_tds
    requires ReachableTDsStates_PreConditionsOfK(k_params, k_all_objs_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, k_all_objs_ids,
                active_os_subjs, active_wimps_subjs,
                active_os_devs, active_wimps_devs,
                active_os_tds, active_wimps_tds,
                k_tds_states[0], os_tds_state0, wimps_tds_state0)
    // Requirements required by functions in this function method
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids
    requires (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.hcoded_td_ids)

    requires |k_devs| == |k_tds_states| - 1 
    requires forall dev_id :: dev_id in k_devs
                ==> (IsDevID_SlimState(k_params.subjects, dev_id) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL &&
                    DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id) &&
                    IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= MapGetKeys(k_objects_tds))
        // Requirement: Devices in <k_devs> are active in k

    requires k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds)
        // First TDs' state is the <ActiveTDsState(k)>
    requires (|k_tds_states| == 1 && k_tds_states[|k_tds_states|-1] == ActiveTDsState_SlimState(k_objects_tds)) ||
                    // k_tds_states == [ActiveTDsState(k)], Or
             (|k_tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in k_tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
                |k_devs| == |k_tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in AllActiveDevs_SlimState(k_params.subjects)) &&
                k_tds_states[0] == ActiveTDsState_SlimState(k_objects_tds) && // first TDs' state is the <ActiveTDsState(k)>
                (forall i :: 0<=i<|k_tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_devs[i], k_tds_states[i], k_tds_states[i+1])))
                    // ActiveTDsState(k) -->1+ k_tds_states[|k_tds_states| - 1]
        // Requirement: ActiveTDsState(k) -->* k_tds_states[|k_tds_states| - 1]

    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_os_devs, os_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, k_all_objs_ids,
                active_wimps_devs, wimps_tds_state0)

    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    ensures forall tds_state2 :: tds_state2 in k_tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
        // Property: In any active TDs' state (active TDs of k) reachable from 
        // ActiveTDsState(k), TDs readable by active devs have no invalid refs
{
    Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_ActiveRedGreenTDsAreInKTDsState(
        k_params, k_all_objs_ids,
        active_os_tds, active_wimps_tds,
        k_tds_states[|k_tds_states|-1]
    );
    var os_tds_stateN := MaskTDsState(k_tds_states[|k_tds_states|-1], active_wimps_tds);
    var wimps_tds_stateN := MaskTDsState(k_tds_states[|k_tds_states|-1], active_os_tds);

    // Prove: In k_tds_states[0], all TDs read by active devs have no
    // invalid refs
    Lemma_WKStateToKState_NoInvalidRefInClrAAndClrBTDsState_ThenNoInvalidRefInKTDsState(
        k_params, k_all_objs_ids,
        active_os_subjs, active_wimps_subjs,
        active_os_devs, active_wimps_devs,
        active_os_tds, active_wimps_tds,
        k_tds_states[0], os_tds_state0, wimps_tds_state0);
    
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(active_os_tds, active_wimps_tds);
    Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs_Internal(
        k_params, k_all_objs_ids, k_objects_tds,
        active_os_subjs, active_wimps_subjs,
        active_os_devs, active_wimps_devs,
        active_os_tds, active_wimps_tds,
        os_tds_state0, wimps_tds_state0,
        os_tds_stateN, wimps_tds_stateN,
        k_tds_states, k_devs);
}

lemma Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions1(
    ws:DM_State, k:State, k_params:ReachableTDsKParams
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires k_params == KToKParams(k)
    
    ensures K_UniqueIDsAndOwnedObjs(k_params.subjects, k_params.objs_td_ids, k_params.objs_fd_ids, k_params.objs_do_ids)
    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    ensures WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)
{
    assert k_params.subjects == k.subjects;
    assert forall id :: id in AllSubjsIDs(k.subjects) ==> SubjPID_SlimState(k.subjects, id) == SubjPID(k, id);
    assert forall id :: id in AllObjsIDs(k.objects) ==> ObjPID_SlimState(k_params.objs_pids, id) == ObjPID(k, id);
    
    var k_subjects := k_params.subjects;
    forall s_id, o_id | s_id in AllSubjsIDs(k_subjects) && DoOwnObj_SlimState(k_subjects, s_id, o_id)
        ensures SubjPID_SlimState(k_subjects, s_id) == ObjPID_SlimState(k_params.objs_pids, o_id)
    {
        assert DoOwnObj(k, s_id, o_id);
        assert SubjPID(k, s_id) == ObjPID(k, o_id);
    }
}

// (needs 50s to verify)
lemma Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions2(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals,
    k_tds_state:TDs_Vals
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Partitions(ws)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    
    requires k == DMStateToState(ws)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires k_params == KToKParams(k)
    
    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
                k_tds_state, os_tds_state0, wimps_tds_state0)
    requires ReachableTDsStates_PreConditionsOfK(k_params, AllObjsIDs(k.objects))
    
    ensures k_params.all_active_tds <= k_params.objs_td_ids
    ensures WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, AllObjsIDs(k.objects),
                DM_SubjsInRed(ws), DM_SubjsInGreen(ws),
                DM_DevsInRed(ws), DM_DevsInGreen(ws),
                DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
                k_tds_state, os_tds_state0, wimps_tds_state0)
{
    assert forall id :: id in DM_SubjsInRed(ws)
                <==> id in AllSubjsIDs(k.subjects) &&
                    SubjPID(k, id) == ws.red_pid;
    assert forall id :: id in DM_SubjsInGreen(ws)
                <==> id in AllSubjsIDs(k.subjects) &&
                    SubjPID(k, id) != NULL &&
                    SubjPID(k, id) != ws.red_pid;
    
    Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions2_Inner(k, k_params, ws.red_pid,
        DM_SubjsInRed(ws), DM_SubjsInGreen(ws),
        DM_DevsInRed(ws), DM_DevsInGreen(ws),
        DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
        os_tds_state0, wimps_tds_state0,
        k_tds_state);
}

// (needs 30s to verify)
lemma Lemma_WKStateToState_AllReachableStatesAreSecure_FirstTDsState(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    tds_state2:TDs_Vals, os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires k_params == KToKParams(k)

    requires ActiveTDsState(k) == tds_state2
        // Requirement: ActiveTDsState(k) == tds_state2

   requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
                ActiveTDsState(k), os_tds_state0, wimps_tds_state0)
    requires ReachableTDsStates_PreConditionsOfK(k_params, AllObjsIDs(k.objects))
    
    requires DM_DevsInRed(ws) <= AllActiveDevs_SlimState(k.subjects)
    requires DM_DevsInGreen(ws) <= AllActiveDevs_SlimState(k.subjects)
    requires DM_TDIDsInRed(ws) * DM_TDIDsInGreen(ws) == {}
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInRed(ws), os_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInGreen(ws), wimps_tds_state0)
        // Reachable red and green TDs' states have no invalid transfers in their closures
    
    ensures TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
{
    var tds_states:seq<TDs_Vals> := [ActiveTDsState(k)];
    var devs:seq<Dev_ID> := [];

    Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions1(ws, k, k_params);
    Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions2(ws, k, k_params,
        os_tds_state0, wimps_tds_state0, tds_states[0]);

    assert |tds_states| == 1 && tds_states[|tds_states|-1] == ActiveTDsState_SlimState(k.objects.tds);
    Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs(
        k_params, AllObjsIDs(k.objects), k.objects.tds,
        DM_SubjsInRed(ws), DM_SubjsInGreen(ws),
        DM_DevsInRed(ws), DM_DevsInGreen(ws),
        DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
        os_tds_state0, wimps_tds_state0,
        tds_states, devs);

    assert ActiveTDsState(k) == tds_state2;
    Lemma_WKStateToState_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue_ReachableActiveTDsStatesHaveNoInvalidRefs_Summary(
        k_params, tds_states, tds_state2);
}

// (needs 40s to verify)
lemma Lemma_WKStateToState_AllReachableStatesAreSecure_ChainedTDsStates(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    tds_state2:TDs_Vals, os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires k_params == KToKParams(k)

    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, AllActiveDevs(k), ActiveTDsState(k), tds_state2) &&
                 IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), ActiveTDsState(k), tds_state2)
        // Requirement: ActiveTDsState(k) -->1+ tds_state2

    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
                ActiveTDsState(k), os_tds_state0, wimps_tds_state0)
    requires ReachableTDsStates_PreConditionsOfK(k_params, AllObjsIDs(k.objects))
    
    requires DM_DevsInRed(ws) <= AllActiveDevs_SlimState(k.subjects)
    requires DM_DevsInGreen(ws) <= AllActiveDevs_SlimState(k.subjects)
    requires DM_TDIDsInRed(ws) * DM_TDIDsInGreen(ws) == {}
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInRed(ws), os_tds_state0)
    requires WKStateToKState_AnyClrXTDsStatesReachableFromClrXTDsStates0HaveNoInvalidRefsInTDs(
                k_params, AllObjsIDs(k.objects), DM_DevsInGreen(ws), wimps_tds_state0)
        // Reachable red and green TDs' states have no invalid transfers in their closures

    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), tds_state2)
{
    var k_params := KToKParams(k);

    var tds_states:seq<TDs_Vals>, devs:seq<Dev_ID> := 
            Lemma_IsActiveTDsStateReachActiveTDsStateInChain_PostConditions_ReturnVals(k_params, 
                AllActiveDevs(k), ActiveTDsState(k), tds_state2);
    assert |tds_states| >= 2 && 
            (forall tds_state2 :: tds_state2 in tds_states 
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds) &&
            |devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in devs ==> dev_id2 in AllActiveDevs(k)) &&
            tds_states[|tds_states| - 1] == tds_state2 && // last TDs' state is the <tds_state2>
            tds_states[0] == ActiveTDsState(k) && // first TDs' state is the ActiveTDsState(k)
            (forall i :: 0<=i<|tds_states| - 1 
                ==> IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, devs[i], tds_states[i], tds_states[i+1]));
                    
    Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions1(ws, k, k_params);
    Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions2(ws, k, k_params,
        os_tds_state0, wimps_tds_state0, tds_states[0]);

    Lemma_WKStateToKState_ReachableActiveTDsStatesHaveNoInvalidRefs(
        k_params, AllObjsIDs(k.objects), k.objects.tds,
        DM_SubjsInRed(ws), DM_SubjsInGreen(ws),
        DM_DevsInRed(ws), DM_DevsInGreen(ws),
        DM_TDIDsInRed(ws), DM_TDIDsInGreen(ws),
        os_tds_state0, wimps_tds_state0,
        tds_states, devs);
            
    Lemma_WKStateToState_FindReachableTDsStatesFromTDsState_AlwaysReturnsTrue_ReachableActiveTDsStatesHaveNoInvalidRefs_Summary(
        k_params, tds_states, tds_state2);
}




//******** Private Functions and Lemmas From Abstract Model ********//
function method MaskTDsState(
    tds_state:TDs_Vals, mask_td_ids:set<TD_ID>
) : (tds_state':TDs_Vals)
    requires forall td_id :: td_id in mask_td_ids ==> td_id in tds_state

    ensures TDsStateGetTDIDs(tds_state) == TDsStateGetTDIDs(tds_state')
    ensures forall td_id :: td_id in tds_state <==> td_id in tds_state'
    ensures forall td_id :: td_id in tds_state
                ==> (td_id in mask_td_ids ==> tds_state'[td_id] == TD_Val( 
                        map[], map[], map[])) &&
                    (td_id !in mask_td_ids ==> tds_state'[td_id] == tds_state[td_id])
{
    map i | i in tds_state :: if i in mask_td_ids then TD_Val(map[], map[], map[]) else tds_state[i]
}

function method MergeTDsState(
    tds_state1:TDs_Vals, tds_state2:TDs_Vals, merge_td_ids:set<TD_ID>
) : (tds_state':TDs_Vals)
    requires forall td_id :: td_id in merge_td_ids ==> td_id in tds_state1
    requires forall td_id :: td_id in tds_state1 <==> td_id in tds_state2

    ensures TDsStateGetTDIDs(tds_state1) == TDsStateGetTDIDs(tds_state')
    ensures forall td_id :: td_id in tds_state1 <==> td_id in tds_state'
    ensures forall td_id :: td_id in tds_state1
                ==> (td_id in merge_td_ids ==> tds_state'[td_id] == tds_state2[td_id]) &&
                    (td_id !in merge_td_ids ==> tds_state'[td_id] == tds_state1[td_id])
{
    map i | i in tds_state1 :: if i in merge_td_ids then tds_state2[i] else tds_state1[i]
}

function method HCodedTDOfDev(k_params:ReachableTDsKParams, dev_id:Dev_ID) : TD_Val
    requires dev_id in k_params.hcoded_tds
{
    k_params.hcoded_tds[dev_id]
}

function method GetTransfersToTDsInHCodedTD_SlimState(
    k_params:ReachableTDsKParams, dev_id:Dev_ID
) : map<TD_ID, TD_Trans_Param>
    requires dev_id in k_params.hcoded_tds
{
    HCodedTDOfDev(k_params, dev_id).trans_params_tds
}

lemma Lemma_MergeTDsState_SameTDsDiff(
    from_tds_state:TDs_Vals, to_tds_state:TDs_Vals, 
    merged_tds_state:TDs_Vals, merged_td_ids:set<TD_ID>,
    expanded_from_tds_state:TDs_Vals, expanded_to_tds_state:TDs_Vals
)
    requires TDsStateGetTDIDs(from_tds_state) == TDsStateGetTDIDs(to_tds_state)
    requires TDsStateGetTDIDs(from_tds_state) == TDsStateGetTDIDs(merged_tds_state)
    requires merged_td_ids <= TDsStateGetTDIDs(from_tds_state)

    requires forall id :: id in merged_td_ids
                ==> from_tds_state[id] == to_tds_state[id]
        // Requirement: <from_tds_state> and <to_tds_state> have same values for TDs <merged_td_ids>
    requires expanded_from_tds_state == MergeTDsState(from_tds_state, merged_tds_state, merged_td_ids)
    requires expanded_to_tds_state == MergeTDsState(to_tds_state, merged_tds_state, merged_td_ids)
        
    ensures TDsStateDiff(expanded_from_tds_state, expanded_to_tds_state) == TDsStateDiff(from_tds_state, to_tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_CanActiveDevReadActiveTD_ActiveDevsCannotReadTDsInAnotherPartition(
    k_params:ReachableTDsKParams, k_all_objs_ids:set<Object_ID>,
    k_tds_state:TDs_Vals, active_dev:Dev_ID, target_td_id:TD_ID
)
    requires K_UniqueIDsAndOwnedObjs(k_params.subjects, k_params.objs_td_ids, k_params.objs_fd_ids, k_params.objs_do_ids)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params)

    requires forall dev_id2 :: dev_id2 in k_params.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids
    requires forall o_id  :: TD_ID(o_id) in k_params.objs_td_ids
                ==> o_id in k_all_objs_ids

    requires active_dev in k_params.subjects.devs
    requires SubjPID_DevID_SlimState(k_params.subjects, active_dev) != NULL
        // Requirement: <active_dev> and <target_td_id> are in different 
        // partition

    requires TDsStateGetTDIDs(k_tds_state) == k_params.all_active_tds

    requires forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
                        // The TD is read by the device
                    ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id2)
        // Requirement: In k_tds_state, all TDs read by active devices 
        // do not have invalid refs

    ensures forall td_id2, dev_id :: 
                    dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                        // The device (<dev_id>) is active
                    td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                        // The TD (<td_id2>) is active
                    CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
                        // The TD is read by the device
                ==> SubjPID_DevID_SlimState(k_params.subjects, dev_id) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid)
        // Property: TDs read by a device are in the same partition with the device
{
    var k_subjects := k_params.subjects;

    forall td_id2, dev_id | dev_id in AllActiveDevs_SlimState(k_params.subjects) && 
                                // The device (<dev_id>) is active
                            td_id2 in TDsStateGetTDIDs(k_tds_state) &&
                                // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2)
        ensures SubjPID_DevID_SlimState(k_subjects, dev_id) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid)
    {
        var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
                (forall td_id3 :: td_id3 in td_ids ==> td_id3 in k_tds_state) &&
                                                // A list of active TDs
                td_ids[|td_ids| - 1] == td_id2 && // last TD is the TD (<td_id2>)
                td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
                (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[i]]));

        assert DoOwnObj_SlimState(k_subjects, dev_id.sid, td_ids[0].oid);
        assert WKStateToKState_SubjsOwnObjsThenInSamePartition(k_params);
        assert SubjPID_DevID_SlimState(k_subjects, dev_id) == 
                    ObjPID_SlimState(k_params.objs_pids, td_ids[0].oid);

        var i := 1;
        while (1 <= i < |td_ids|)
            invariant 1 <= i <= |td_ids|

            invariant forall td_id :: td_id in td_ids[..i]
                        ==> SubjPID_DevID_SlimState(k_subjects, dev_id) == 
                            ObjPID_SlimState(k_params.objs_pids, td_id.oid)

            decreases |td_ids| - i
        {
            var td_id := td_ids[i];
            var tdx_id := td_ids[i-1];

            assert SubjPID_DevID_SlimState(k_subjects, dev_id) == 
                   ObjPID_SlimState(k_params.objs_pids, tdx_id.oid);

            assert td_id in TDIDReadsInTDCfg(k_tds_state[tdx_id]);

            // Prove ObjPID(tdx_id) == ObjPID(td_id)
            if(ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != 
               ObjPID_SlimState(k_params.objs_pids, td_id.oid))
            {
                assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, tdx_id);
            }

            i := i + 1;
        }
    }
}

lemma Lemma_K_ActiveSubjsDevsIsActiveRedSubjsDevsPlusActiveGreenSubjsDevs(
    k:State, clrA_pid:Partition_ID,
    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>
)
    requires IsValidState_Subjects(k)

    requires forall id :: id in active_clrA_subjs
                <==> id in AllSubjsIDs(k.subjects) &&
                    SubjPID(k, id) == clrA_pid
    requires forall id :: id in active_clrB_subjs
                <==> id in AllSubjsIDs(k.subjects) &&
                    SubjPID(k, id) != NULL &&
                    SubjPID(k, id) != clrA_pid
    requires forall id :: id in active_clrA_devs
                <==> id in k.subjects.devs &&
                    SubjPID(k, id.sid) == clrA_pid
    requires forall id :: id in active_clrB_devs
                <==> id in k.subjects.devs &&
                    SubjPID(k, id.sid) != NULL &&
                    SubjPID(k, id.sid) != clrA_pid

    requires clrA_pid != NULL

    ensures AllActiveSubjs_SlimState(k.subjects) == active_clrA_subjs + active_clrB_subjs
    ensures AllActiveDevs_SlimState(k.subjects) == active_clrA_devs + active_clrB_devs
    ensures active_clrA_subjs * active_clrB_subjs == {}
    ensures active_clrA_devs * active_clrB_devs == {}
{
    assert forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                          s_id in active_clrA_subjs + active_clrB_subjs
            ==> SubjPID(k, s_id) != NULL;

    Lemma_DM_SameIDsIffSameInternalIDs();
    forall s_id | s_id in active_clrA_subjs + active_clrB_subjs
        ensures s_id in AllActiveSubjs_SlimState(k.subjects)
    {
        assert s_id in AllSubjsIDs(k.subjects);
        assert SubjPID(k, s_id) != NULL;
        assert s_id in AllActiveSubjs_SlimState(k.subjects);
    }

    forall dev_id | dev_id in active_clrA_devs + active_clrB_devs
        ensures dev_id in AllActiveDevs_SlimState(k.subjects)
    {
        assert dev_id in k.subjects.devs;

        assert dev_id.sid in active_clrA_subjs || dev_id.sid in active_clrB_subjs;
        Lemma_AllDevsInStateReturnsSamePIDBySubjPIDDevIDAndSubjPID(k);
        assert SubjPID_DevID(k, dev_id) != NULL;
    }

    forall dev_id | dev_id in AllActiveDevs_SlimState(k.subjects)
        ensures dev_id in active_clrA_devs + active_clrB_devs
    {
        assert SubjPID_DevID(k, dev_id) != NULL;
        Lemma_AllDevsInStateReturnsSamePIDBySubjPIDDevIDAndSubjPID(k);
        assert SubjPID(k, dev_id.sid) != NULL;
        assert dev_id.sid in AllSubjsIDs(k.subjects);

        assert dev_id.sid in active_clrA_subjs || dev_id.sid in active_clrB_subjs;
        assert dev_id in k.subjects.devs;
        assert dev_id in active_clrA_devs + active_clrB_devs;
    }
}

lemma Lemma_K_ActiveSubjsOwnedTDsAreInActiveTDsSet(
    k:State, clrA_pid:Partition_ID,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)

    requires forall id :: id in active_clrA_devs
                <==> id in k.subjects.devs &&
                    SubjPID(k, id.sid) == clrA_pid
    requires forall id :: id in active_clrB_devs
                <==> id in k.subjects.devs &&
                    SubjPID(k, id.sid) != NULL &&
                    SubjPID(k, id.sid) != clrA_pid
    requires forall id :: id in active_clrA_tds
                <==> id in k.objects.tds &&
                    ObjPID(k, id.oid) == clrA_pid
    requires forall id :: id in active_clrB_tds
                <==> id in k.objects.tds &&
                    ObjPID(k, id.oid) != NULL &&
                    ObjPID(k, id.oid) != clrA_pid

    requires clrA_pid != NULL

    ensures forall dev_id :: dev_id in active_clrA_devs
                ==> OwnedTDs_SlimState(k.subjects, dev_id.sid) <= active_clrA_tds
    ensures forall dev_id :: dev_id in active_clrB_devs
                ==> OwnedTDs_SlimState(k.subjects, dev_id.sid) <= active_clrB_tds
{
    forall dev_id | dev_id in active_clrA_devs
        ensures OwnedTDs_SlimState(k.subjects, dev_id.sid) <= active_clrA_tds
    {
        forall td_id | td_id in OwnedTDs_SlimState(k.subjects, dev_id.sid)
            ensures td_id in active_clrA_tds
        {
            assert DoOwnObj(k, dev_id.sid, td_id.oid);
        }
        
        Lemma_SetInclusion_Prove(OwnedTDs_SlimState(k.subjects, dev_id.sid), active_clrA_tds);
    }

    forall dev_id | dev_id in active_clrB_devs
        ensures OwnedTDs_SlimState(k.subjects, dev_id.sid) <= active_clrB_tds
    {
        forall td_id | td_id in OwnedTDs_SlimState(k.subjects, dev_id.sid)
            ensures td_id in active_clrB_tds
        {
            assert DoOwnObj(k, dev_id.sid, td_id.oid);
        }
        
        Lemma_SetInclusion_Prove(OwnedTDs_SlimState(k.subjects, dev_id.sid), active_clrB_tds);
    }
}

lemma Lemma_K_ActiveTDsIsTDsInRedPlusTDsInGreen(
    k:State, clrA_pid:Partition_ID,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    requires forall id :: id in active_clrA_tds
                <==> id in k.objects.tds &&
                    ObjPID(k, id.oid) == clrA_pid
    requires forall id :: id in active_clrB_tds
                <==> id in k.objects.tds &&
                    ObjPID(k, id.oid) != NULL &&
                    ObjPID(k, id.oid) != clrA_pid

    requires clrA_pid != NULL
    
    ensures active_clrA_tds + active_clrB_tds == AllActiveTDs(k)
    ensures active_clrA_tds * active_clrB_tds == {}
{
    Lemma_DM_SameIDsIffSameInternalIDs();
    forall id | id in active_clrA_tds + active_clrB_tds
        ensures id in AllActiveTDs(k)
    {
        assert id in k.objects.tds;
        assert ObjPID(k, id.oid) != NULL;
        assert id in AllActiveTDs(k);
    }
}

lemma Lemma_WKStateToState_AllReachableStatesAreSecure_PreConditions2_Inner(
    k:State, k_params:ReachableTDsKParams, clrA_pid:Partition_ID,
    active_clrA_subjs:set<Subject_ID>, active_clrB_subjs:set<Subject_ID>,
    active_clrA_devs:set<Dev_ID>, active_clrB_devs:set<Dev_ID>,
    active_clrA_tds:set<TD_ID>, active_clrB_tds:set<TD_ID>,
    os_tds_state0:TDs_Vals, wimps_tds_state0:TDs_Vals,
    k_tds_state:TDs_Vals
)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k) && IsValidState_Partitions(k) && IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires k_params == KToKParams(k)

    requires forall id :: id in active_clrA_subjs
                <==> id in AllSubjsIDs(k.subjects) &&
                    SubjPID(k, id) == clrA_pid
    requires forall id :: id in active_clrB_subjs
                <==> id in AllSubjsIDs(k.subjects) &&
                    SubjPID(k, id) != NULL &&
                    SubjPID(k, id) != clrA_pid
    requires forall id :: id in active_clrA_devs
                <==> id in k.subjects.devs &&
                    SubjPID(k, id.sid) == clrA_pid
    requires forall id :: id in active_clrB_devs
                <==> id in k.subjects.devs &&
                    SubjPID(k, id.sid) != NULL &&
                    SubjPID(k, id.sid) != clrA_pid
    requires forall id :: id in active_clrA_tds
                <==> id in k.objects.tds &&
                    ObjPID(k, id.oid) == clrA_pid
    requires forall id :: id in active_clrB_tds
                <==> id in k.objects.tds &&
                    ObjPID(k, id.oid) != NULL &&
                    ObjPID(k, id.oid) != clrA_pid

    requires WKStateToKState_WKTDsStateAreTheMergeOfClrATDsStateAndClrBTDsState(k_params,
                active_clrA_tds, active_clrB_tds,
                k_tds_state, os_tds_state0, wimps_tds_state0)
                
    requires clrA_pid != NULL

    requires ReachableTDsStates_PreConditionsOfK(k_params, AllObjsIDs(k.objects))

    ensures k_params.all_active_tds <= k_params.objs_td_ids
    ensures WKStateToKState_ClrAAndClrBHaveOwnTDsAndTDsStates(
                k_params, AllObjsIDs(k.objects),
                active_clrA_subjs, active_clrB_subjs,
                active_clrA_devs, active_clrB_devs,
                active_clrA_tds, active_clrB_tds,
                k_tds_state, os_tds_state0, wimps_tds_state0)
{
    Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);

    assert k_params.subjects == k.subjects;
    assert forall id :: id in AllSubjsIDs(k.subjects) ==> SubjPID_SlimState(k.subjects, id) == SubjPID(k, id);
    assert forall id :: id in AllObjsIDs(k.objects) ==> ObjPID_SlimState(k_params.objs_pids, id) == ObjPID(k, id);

    Lemma_K_ActiveSubjsDevsIsActiveRedSubjsDevsPlusActiveGreenSubjsDevs(k, clrA_pid, 
        active_clrA_subjs, active_clrB_subjs, active_clrA_devs, active_clrB_devs);

    Lemma_K_ActiveSubjsOwnedTDsAreInActiveTDsSet(k, clrA_pid,
        active_clrA_devs, active_clrB_devs, active_clrA_tds, active_clrB_tds);
    Lemma_K_ActiveTDsIsTDsInRedPlusTDsInGreen(k, clrA_pid, active_clrA_tds, active_clrB_tds);
}

lemma Lemma_K_WholeClosureIsGood_ThenSubsetClosureIsGood(
    k_params:ReachableTDsKParams, active_clrA_devs:set<Dev_ID>, active_clrA_tds:set<TD_ID>, k_tds_state:TDs_Vals, clrA_tds_state:TDs_Vals
)
    requires CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    requires forall dev_id2 :: dev_id2 in AllActiveDevs_SlimState(k_params.subjects)
                ==> IsDevID_SlimState(k_params.subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k_params.subjects, dev_id2) != NULL

    requires TDsStateGetTDIDs(clrA_tds_state) == k_params.all_active_tds
    requires TDsStateGetTDIDs(k_tds_state) == k_params.all_active_tds
    requires (forall td_id :: td_id in clrA_tds_state
                ==> (td_id in active_clrA_tds ==> k_tds_state[td_id] == clrA_tds_state[td_id]) &&
                    (td_id !in active_clrA_tds ==> clrA_tds_state[td_id] == TD_Val(map[], map[], map[])))
    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs_SlimState(k_params.subjects), k_tds_state)

    requires active_clrA_devs <= AllActiveDevs_SlimState(k_params.subjects)

    ensures ActiveTDsStateIsSecure(k_params, active_clrA_devs, clrA_tds_state)
{
    forall td_id2, dev_id | dev_id in active_clrA_devs && 
                    // The device (<dev_id>) is active
                td_id2 in TDsStateGetTDIDs(clrA_tds_state) &&
                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, clrA_tds_state, dev_id, td_id2)
                    // The TD is read by the device
        ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, clrA_tds_state, td_id2)
    {
        var td_ids := Lemma_CanActiveDevReadActiveTD_Apply(k_params, clrA_tds_state, dev_id, td_id2);

        assert (forall td_id2 :: td_id2 in td_ids ==> td_id2 in k_tds_state);
        assert (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(k_tds_state[td_ids[i]]));

        assert CanActiveDevReadActiveTD(k_params, k_tds_state, dev_id, td_id2);
    }
}