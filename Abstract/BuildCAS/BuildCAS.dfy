include "../Syntax.dfy"
include "../Utils.dfy"
include "../HCodedTD_Ops.dfy"
include "../CASOps.dfy"
include "../Properties.dfy"
include "../Lemmas.dfy"
include "../Lemmas_Ops.dfy"
include "ReachableTDs.dfy"
include "ReachableTDsStates.dfy"

method ValidSecureState_ReachableStatesOfActiveTDs(k:State) returns (k_tds_states:set<TDs_Vals>)
    requires IsValidState(k) && IsSecureState(k)

    ensures k_tds_states == AllReachableActiveTDsStates(k)
{
    // Calculate reachable snapshots of active TDs in K
    var k_active_tds_state := ActiveTDsState(k);
    ghost var k_tds_to_all_states := k.tds_to_all_states;
    var k_explored_tds_states, k_s := FindReachableActiveTDsStatesFromActiveTDsState(
            KToKParams(k), k_tds_to_all_states[AllActiveTDs(k)],
            AllActiveDevs(k), k_active_tds_state, [{k_active_tds_state}]); 
    k_tds_states := GetExploredTDsStates(k_explored_tds_states, 0);
    assert k_s == true;

    Lemma_FindReachableActiveTDsStatesFromActiveTDsStateReturnsTrue_AllReachableActiveTDsStatesIsResult(k, k_tds_states);
}

predicate P_BuildCAS_Properties(
    k:State, tds_states_set:set<TDs_Vals>, cas':CAS
)
    requires TDsStateToCASForDev_PreConditions(k)

    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
{
    (CASGetSubjs(cas') == AllActiveDevs(k)) &&
    (CASGetObjs(cas') == AllActiveObjs(k)) &&
    (forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == cas'.o_ids) &&
        // Property: The result CAS is a matrix
    (forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(cas', dev_id2, o_id2)) &&
    (forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(cas', dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in tds_states_set &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))) &&
    (forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(cas', dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in tds_states_set &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))) &&
        // Property: Access modes in the result CAS (<cas'>) are from 
        // TDs' states (<tds_states_set>)
        
    (true)
}

// BuildCAS Algorithm
// (needs 140s to verify)
method BuildCAS(
    k:State, k_params:ReachableTDsKParams, tds_states_set:set<TDs_Vals>
) returns (cas':CAS)
    requires TDsStateToCASForDev_PreConditions(k)
    requires k_params == KToKParams(k)

    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' states includes all TDs
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires forall tds_state2 :: tds_state2 in tds_states_set
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)

    ensures P_BuildCAS_Properties(k, tds_states_set, cas')
{
    var t_cas := CAS(map[], {});
    
    var active_devs_set := AllActiveDevs(k);
    var active_objs_set := AllActiveObjs(k);
    var active_devs := SetToSeq<Dev_ID>(active_devs_set);
    
    // Add active devices and objects
    t_cas := CASAddSubjs(t_cas, active_devs_set);
    t_cas := CASAddObjs(t_cas, active_objs_set);

    // Fill requested access modes
    t_cas := BuildCAS_FillReqAModes(k, k_params, t_cas, active_devs, tds_states_set);        

    return t_cas;
}




//******** Utility Functions ********//
method BuildCAS_FillReqAModes(
    k:State, k_params:ReachableTDsKParams,
    cas:CAS, active_devs:seq<Dev_ID>, tds_states_set:set<TDs_Vals>
) returns (cas':CAS)
    requires TDsStateToCASForDev_PreConditions(k)
    requires k_params == KToKParams(k)

    requires forall tds_state :: tds_state in tds_states_set
                ==> TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' states includes all TDs
    requires forall dev_id2 :: dev_id2 in active_devs 
                ==> dev_id2 in AllActiveDevs(k)
        // Requirement: <active_devs> contain active devices
    requires forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                    ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                        cas.o_ids
    requires CASGetSubjs(cas) == AllActiveDevs(k)
    requires CASGetObjs(cas) == AllActiveObjs(k)

    requires forall tds_state2 :: tds_state2 in tds_states_set
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
        // Requirement: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects in all <tds_states_set>

    ensures CASGetSubjs(cas') == AllActiveDevs(k)
    ensures CASGetObjs(cas') == AllActiveObjs(k)
    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == cas'.o_ids
        // Property: The result CAS is a matrix
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) && 
                    dev_id2 !in active_devs
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: Other devices in <cas> have unchanged requested access modes

    ensures forall dev_id2, o_id2 :: dev_id2 in active_devs && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: dev_id2 in active_devs && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(cas', dev_id2, o_id2)
                        <==> R in CASGetAModes(cas, dev_id2, o_id2) || 
                            (exists tds_state2 :: tds_state2 in tds_states_set &&
                                R in DevAModesToObjFromTDs(k, tds_state2, dev_id2, o_id2)))
    ensures forall dev_id2, o_id2 :: dev_id2 in active_devs && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(cas', dev_id2, o_id2)
                        <==> W in CASGetAModes(cas, dev_id2, o_id2) ||  
                            (exists tds_state2 :: tds_state2 in tds_states_set &&
                                W in DevAModesToObjFromTDs(k, tds_state2, dev_id2, o_id2)))
        // Property: Access modes in the result CAS (<cas'>) are from 
        // TDs' states (<tds_states_set>), and the input CAS (<cas>)

    decreases |active_devs| 
{
    if(|active_devs| == 0)
    {    return cas;}
    else
    {
        var dev_id := active_devs[0];
        var active_devs_step := active_devs[1..];
        var tds_states := SetToSeq<TDs_Vals>(tds_states_set);
        var t_cas := cas;

        assert IsDevID(k, dev_id);
        assert SubjPID_DevID(k, dev_id) != NULL;

        // Requirement: The devices <dev_id> must be active
        // Build CAS from each TDs' state
        t_cas := TDsStatesToCASForDev(k, k_params, t_cas, dev_id, tds_states);

        cas' := BuildCAS_FillReqAModes(k, k_params, t_cas, active_devs_step, tds_states_set);
    }
}

method TDsStatesToCASForDev(
    k:State, k_params:ReachableTDsKParams,
    cas:CAS, dev_id:Dev_ID, tds_states:seq<TDs_Vals>
) returns (cas':CAS)
    requires TDsStateToCASForDev_PreConditions(k)
    requires k_params == KToKParams(k)

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)
        // Requirement: The TDs' states include all TDs
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The devices <dev_id> must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires CASGetSubjs(cas) == AllActiveDevs(k)
    requires CASGetObjs(cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == cas.o_ids
        // Property: The CAS (<cas>) is a matrix
    requires forall tds_state2 :: tds_state2 in tds_states
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
        // Requirement: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects in all <tds_states>

    ensures CASGetSubjs(cas') == AllActiveDevs(k)
    ensures CASGetObjs(cas') == AllActiveObjs(k)
    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == cas'.o_ids
        // Property: The result CAS is a matrix
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) && 
                    dev_id2 != dev_id
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: Other devices in <cas> have unchanged requested access modes

    ensures forall o_id2:: o_id2 in AllActiveObjs(k)
                ==> CASGetAModes(cas, dev_id, o_id2) <= CASGetAModes(cas', dev_id, o_id2)
    ensures forall tds_state2, o_id2:: tds_state2 in tds_states && 
                    o_id2 in AllActiveObjs(k)
                ==> DevAModesToObjFromTDs(k, tds_state2, dev_id, o_id2) <= CASGetAModes(cas', dev_id, o_id2)
        // Property: All requested access modes in TDs are recorded in <cas'>
    ensures forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(cas', dev_id, o_id2)
                        <==> R in CASGetAModes(cas, dev_id, o_id2) || 
                            (exists tds_state2 :: tds_state2 in tds_states &&
                                R in DevAModesToObjFromTDs(k, tds_state2, dev_id, o_id2))) &&
                    (W in CASGetAModes(cas', dev_id, o_id2)
                        <==> W in CASGetAModes(cas, dev_id, o_id2) || 
                            (exists tds_state2 :: tds_state2 in tds_states &&
                                W in DevAModesToObjFromTDs(k, tds_state2, dev_id, o_id2)))
        // Property: For each active object <o_id2> in each <tds_states>, the  
        // device's (<dev_id> requested access modes (due to TDs) to the object 
        // is appended into the CAS 

    decreases |tds_states|
{
    if(|tds_states| == 0)
    {    return cas;}
    else
    {
        var tds_state := tds_states[0]; 
        var tds_states_step := tds_states[1..];

        forall td_id2 | td_id2 in TDsStateGetTDIDs(tds_state) &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
            ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
        {
            assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state);
            assert dev_id in AllActiveDevs(k);
        }

        var t_cas := TDsStateToCASForDev(k, k_params, cas, dev_id, tds_state);

        assert forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> CASGetAModes(cas, dev_id, o_id2) <= CASGetAModes(t_cas, dev_id, o_id2);
        assert forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> DevAModesToObjFromTDs(k, tds_state, dev_id, o_id2) <= CASGetAModes(t_cas, dev_id, o_id2);

        cas' := TDsStatesToCASForDev(k, k_params, t_cas, dev_id, tds_states_step);
    }
}

predicate TDsStateToCASForDev_PreConditions(k:State)
{
    K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos)) &&

    var hcoded_tds := BuildMap_DevsToHCodedTDVals(k.subjects, k.objects);
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)) &&

    (forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
        ==> SubjPID(k, s_id) == ObjPID(k, o_id)) &&

    (true)
}

// Fill CAS for the device (<dev_id>) according to the TDs' state (<tds_state>)
// (needs 200s to verify)
method TDsStateToCASForDev(
    k:State, k_params:ReachableTDsKParams, 
    cas:CAS, dev_id:Dev_ID, tds_state:TDs_Vals
) returns (cas':CAS)
    requires TDsStateToCASForDev_PreConditions(k)
    requires k_params == KToKParams(k) 

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' state includes all active TDs
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The devices <dev_id> must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires CASGetSubjs(cas) == AllActiveDevs(k)
    requires CASGetObjs(cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == cas.o_ids
        // Property: The CAS (<cas>) is a matrix

    requires forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) && 
                                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                    // For all active TDs can be read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
        // Requirement: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects

    ensures CASGetSubjs(cas') == AllActiveDevs(k)
    ensures CASGetObjs(cas') == AllActiveObjs(k)
    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == cas'.o_ids
        // Property: The result CAS is a matrix

    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) && 
                dev_id2 != dev_id
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: Other devices in <cas> have unchanged requested access modes
    ensures forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> CASGetAModes(cas, dev_id, o_id2) + DevAModesToObjFromTDs(k, tds_state, dev_id, o_id2) == CASGetAModes(cas', dev_id, o_id2)
        // Property: For each active object <o_id2>, the device's (<dev_id> 
        // requested access modes (due to TDs) to the object is appended into 
        // the CAS
{
    Lemma_TDsStateToCASForDev_ProveFulfillFindAllTDsReadByDevKParamsPreConditions(k, k_params);
    var t_cas := cas;
    var active_devs := AllActiveDevs(k);
    var active_objs := AllActiveObjs(k);
    var read_tds_set, s := FindAllTDsReadByDev(k_params, tds_state, dev_id);
    var read_tds := SetToSeq<TD_ID>(read_tds_set);
    var i := 0;

    AllReqAModesPermsSubsetOfRW();
    assert forall td_id2 :: td_id2 in read_tds
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) && 
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2);
    assert forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) && 
                    CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                        // For all active TDs can be read by the device
                    ==> td_id2 in read_tds;
    assert forall read_td2 :: read_td2 in read_tds
            ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, read_td2);

    assert dev_id in active_devs;
    // Fill requested access modes due to TDs' state.
    while (i < |read_tds|)
        invariant i <= |read_tds|

        invariant CASGetSubjs(t_cas) == active_devs
        invariant CASGetObjs(t_cas) == active_objs
        invariant dev_id in CASGetSubjs(t_cas)
        invariant forall dev_id2 :: IsSubjInCAS(t_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(t_cas.m[dev_id2]) == t_cas.o_ids
        invariant forall read_td2 :: read_td2 in read_tds[..i]
                ==> read_td2 in tds_state

        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) && 
                dev_id2 != dev_id
                ==> IsInCAS(t_cas, dev_id2, o_id2) &&
                    CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(t_cas, dev_id2, o_id2)
        
        invariant forall read_td2, o_id2 :: read_td2 in read_tds[..i] && 
                    o_id2 in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td2)
                ==> o_id2 in CASGetObjs(t_cas) &&
                    CASGetAModes(t_cas, dev_id, o_id2) >= GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2)
                // Invariant: Referenced objects with non-empty access modes 
                // have requested accesses recorded in <t_cas>

        invariant forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(t_cas, dev_id, o_id2)
                        <==> R in CASGetAModes(cas, dev_id, o_id2) || 
                            (exists read_td2 :: read_td2 in read_tds[..i] &&
                                o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                                R in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2))) &&
                    (W in CASGetAModes(t_cas, dev_id, o_id2)
                        <==> W in CASGetAModes(cas, dev_id, o_id2) || 
                            (exists read_td2 :: read_td2 in read_tds[..i] && 
                                o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                                W in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2)))
                // Invariant: Access modes recorded in CAS must be derived from 
                // TDs read by the device
    {
        var read_td := read_tds[i];
        var old_t_cas := t_cas;

        Lemma_TDsStateToCASForDev_Private(k, k_params, tds_state, dev_id, read_td);

        t_cas := TDsStateToCASForDev_ProcessOneReadableTD(k, k_params, t_cas, dev_id, tds_state, read_td);

        i := i + 1;
    }
    assert forall read_td2 :: read_td2 in read_tds[..i] <==> read_td2 in read_tds;

    Lemma_TDsStateToCASForDev_AModesInTDsStateAreAppendedToCAS(k, k_params, cas, t_cas, dev_id, tds_state, read_tds);

    return t_cas;
}

method TDsStateToCASForDev_ProcessOneReadableTD(
    k:State, k_params:ReachableTDsKParams, 
    cas:CAS, dev_id:Dev_ID, tds_state:TDs_Vals, read_td:TD_ID
) returns (cas':CAS)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))
    requires k_params == KToKParams(k)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' state includes all active TDs
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The devices <dev_id> must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires CASGetSubjs(cas) == AllActiveDevs(k)
    requires CASGetObjs(cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == cas.o_ids
    requires forall o_id2 :: o_id2 in AllObjsIDs(k.objects) && 
                ObjPID(k, o_id2) != NULL
            ==> IsInCAS(cas, dev_id, o_id2) 
        // Requirement: All active devices and objects are in CAS
    requires read_td in tds_state
    requires !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, read_td)
        // Requirement: <read_td> have no invalid references to I/O objects
    requires forall o_id2 :: o_id2 in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td)
                ==> o_id2 in AllActiveObjs(k)

    ensures CASGetSubjs(cas') == AllActiveDevs(k)
    ensures CASGetObjs(cas') == AllActiveObjs(k)
        // Property: No new active devices and objects is added into the result 
        // CAS
    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == cas'.o_ids
    ensures forall o_id2 :: o_id2 in AllActiveObjs(k)
            ==> IsInCAS(cas', dev_id, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(cas', dev_id2, o_id2)

    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) && 
                dev_id2 != dev_id
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: Other devices in <cas> have unchanged requested access modes
    ensures forall o_id2 :: o_id2 in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td)
                ==> CASGetAModes(cas', dev_id, o_id2) == CASGetAModes(cas, dev_id, o_id2) + GetAModesOfObjRefedInTD(tds_state, read_td, o_id2)
    ensures forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(cas', dev_id, o_id2)
                        <==> R in CASGetAModes(cas, dev_id, o_id2) || 
                            (    o_id2 in GetObjIDsRefedInTD(tds_state, read_td) &&
                                R in GetAModesOfObjRefedInTD(tds_state, read_td, o_id2))) &&
                    (W in CASGetAModes(cas', dev_id, o_id2)
                        <==> W in CASGetAModes(cas, dev_id, o_id2) || 
                            (    o_id2 in GetObjIDsRefedInTD(tds_state, read_td) &&
                                W in GetAModesOfObjRefedInTD(tds_state, read_td, o_id2)))
    ensures forall o_id2 :: o_id2 in AllActiveObjs(k) &&
                            o_id2 !in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td)
                ==>  CASGetAModes(cas', dev_id, o_id2) == CASGetAModes(cas, dev_id, o_id2)
        // Property: the result CAS (<cas'>) is the input CAS appended with all 
        // access modes recorded in read_td
{
    var t_cas := cas;
    var refed_obj_ids:= SetToSeq<Object_ID>(GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td));
    var j := 0;

    while (j < |refed_obj_ids|)
        invariant j <= |refed_obj_ids|

        invariant CASGetSubjs(t_cas) == AllActiveDevs(k)
        invariant CASGetObjs(t_cas) == AllActiveObjs(k)
        invariant forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> IsInCAS(t_cas, dev_id, o_id2)
        invariant forall dev_id2 :: IsSubjInCAS(t_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(t_cas.m[dev_id2]) == t_cas.o_ids
        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(t_cas, dev_id2, o_id2)
        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) && 
                dev_id2 != dev_id
                ==> CASGetAModes(t_cas, dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)

        invariant forall o_id2 :: o_id2 in refed_obj_ids[..j]
                ==> o_id2 in GetObjIDsRefedInTD(tds_state, read_td)
        invariant forall o_id2 :: o_id2 in refed_obj_ids[..j]
                ==> o_id2 in AllActiveObjs(k)
        invariant forall o_id2 :: o_id2 in refed_obj_ids[..j]
                ==> CASGetAModes(t_cas, dev_id, o_id2) == CASGetAModes(cas, dev_id, o_id2) + GetAModesOfObjRefedInTD(tds_state, read_td, o_id2)
        invariant forall q :: j <= q < |refed_obj_ids|
                ==> CASGetAModes(t_cas, dev_id, refed_obj_ids[q]) == CASGetAModes(cas, dev_id, refed_obj_ids[q])
        invariant forall o_id2 :: o_id2 in AllActiveObjs(k) &&
                    o_id2 !in refed_obj_ids
                ==> CASGetAModes(t_cas, dev_id, o_id2) == CASGetAModes(cas, dev_id, o_id2)
    {
        var refed_obj_id := refed_obj_ids[j];
        var amodes := GetAModesOfObjRefedInTD(tds_state, read_td, refed_obj_id) + CASGetAModes(t_cas, dev_id, refed_obj_id);

        assert IsInCAS(t_cas, dev_id, refed_obj_id);
        t_cas := CASSetAModes(t_cas, dev_id, refed_obj_id, amodes);

        j := j + 1;
    }

    return t_cas;
}




//******** Utility Lemmas ********//
// Lemma: For all active objects, the device's (<dev_id>) requested access mode 
// to the object as configured in TDs are appended to the CAS (<cas>) and
// result in the new CAS (<cas'>)
lemma Lemma_TDsStateToCASForDev_AModesInTDsStateAreAppendedToCAS(
    k:State, k_params:ReachableTDsKParams,
    cas:CAS, cas':CAS, dev_id:Dev_ID, tds_state:TDs_Vals, read_tds:seq<TD_ID>
)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))
    requires k_params == KToKParams(k)

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' state includes all active TDs
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The devices <dev_id> must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    
    requires |read_tds| >= 0
    requires forall read_td2 :: read_td2 in read_tds 
            ==> read_td2 in tds_state
        // Requirements related to <read_tds>
    requires CASGetSubjs(cas) == AllActiveDevs(k)
    requires CASGetObjs(cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == cas.o_ids
    requires CASGetSubjs(cas') == AllActiveDevs(k)
    requires CASGetObjs(cas') == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == cas'.o_ids
        // Requirements related to <cas> and <cas'>

    requires forall td_id2 :: td_id2 in read_tds
                        ==> td_id2 in TDsStateGetTDIDs(tds_state) && 
                                    // The TD (<td_id2>) is active
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        // Requirement: Each returned TD in <read_tds> is active, and can be 
        // read by the device (<dev_id>)
    requires forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) && 
                                    // The TD (<td_id2>) is active
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                            // For all active TDs can be read by the device
                        ==> td_id2 in read_tds
        // Requirement: All active TDs can be read by the device exist in 
        // <read_tds>
    requires forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(cas', dev_id, o_id2)
                        <==> R in CASGetAModes(cas, dev_id, o_id2) || 
                            (exists read_td2 :: read_td2 in read_tds &&
                                o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                                R in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2))) &&
                    (W in CASGetAModes(cas', dev_id, o_id2)
                        <==> W in CASGetAModes(cas, dev_id, o_id2) || 
                            (exists read_td2 :: read_td2 in read_tds && 
                                o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                                W in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2)))
    requires forall read_td2, o_id2 :: read_td2 in read_tds && 
                    o_id2 in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td2)
                ==> o_id2 in CASGetObjs(cas') &&
                    CASGetAModes(cas', dev_id, o_id2) >= GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2)

    ensures forall o_id2 :: o_id2 in AllActiveObjs(k)
                ==> CASGetAModes(cas, dev_id, o_id2) + DevAModesToObjFromTDs(k, tds_state, dev_id, o_id2) == CASGetAModes(cas', dev_id, o_id2)
{
    AllReqAModesPermsSubsetOfRW();
    forall o_id2 | o_id2 in AllActiveObjs(k)
        ensures DevAModesToObjFromTDs_ExistR(k, tds_state, dev_id, o_id2) ==
                (exists read_td2 :: read_td2 in read_tds &&
                    o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                    R in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2))
    {
        // Dafny can automatically verify it
    }

    forall o_id2 | o_id2 in AllActiveObjs(k)
        ensures DevAModesToObjFromTDs_ExistW(k, tds_state, dev_id, o_id2) ==
                (exists read_td2 :: read_td2 in read_tds &&
                    o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                    W in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2))
    {
        // Dafny can automatically verify it
    }

    forall o_id2 | o_id2 in AllActiveObjs(k)
        ensures R in CASGetAModes(cas', dev_id, o_id2)
            <==> R in CASGetAModes(cas, dev_id, o_id2) ||
                (exists read_td2 :: read_td2 in read_tds &&
                    o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                    R in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2))
    {
        // Dafny can automatically verify it
    }

    forall o_id2 | o_id2 in AllActiveObjs(k)
        ensures W in CASGetAModes(cas', dev_id, o_id2)
            <==> W in CASGetAModes(cas, dev_id, o_id2) || 
                (exists read_td2 :: read_td2 in read_tds &&
                    o_id2 in GetObjIDsRefedInTD(tds_state, read_td2) &&
                    W in GetAModesOfObjRefedInTD(tds_state, read_td2, o_id2))
    {
        // Dafny can automatically verify it
    }
}

lemma Lemma_TDsStateToCASForDev_ProveFulfillFindAllTDsReadByDevKParamsPreConditions(
    k:State, k_params:ReachableTDsKParams
)
    requires TDsStateToCASForDev_PreConditions(k)

    requires k_params == KToKParams(k) 
     
    ensures FindAllTDsReadByDev_KParams_PreConditions(k_params)
{
    forall s_id, o_id | s_id in AllSubjsIDs(k_params.subjects) &&
                DoOwnObj_SlimState(k_params.subjects, s_id, o_id)
        ensures o_id in k_params.objs_pids
        ensures k_params.objs_pids[o_id] == SubjPID_SlimState(k_params.subjects, s_id)
    {
        assert DoOwnObj(k, s_id, o_id);
        assert SubjPID_SlimState(k_params.subjects, s_id) == SubjPID(k, s_id);
        if(TD_ID(o_id) in k.objects.tds)
        {
            var td_id := TD_ID(o_id);
            assert k_params.objs_pids[o_id] == k.objects.tds[td_id].pid;
            assert ObjPID(k, o_id) == k.objects.tds[td_id].pid;
        }
        else if(FD_ID(o_id) in k.objects.fds)
        {
            var fd_id := FD_ID(o_id);
            assert k_params.objs_pids[o_id] == k.objects.fds[fd_id].pid;
            assert ObjPID(k, o_id) == k.objects.fds[fd_id].pid;
        }
        else
        {
            var do_id := DO_ID(o_id);
            assert DO_ID(o_id) in k.objects.dos;
            assert k_params.objs_pids[o_id] == k.objects.dos[do_id].pid;
            assert ObjPID(k, o_id) == k.objects.dos[do_id].pid;
        }
    }

    assert FindAllTDsReadByDev_KParams_PreConditions(k_params);
}




//******** Private Lemmas ********//
lemma Lemma_TDsStateToCASForDev_Private(
    k:State, k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, dev_id:Dev_ID, read_td:TD_ID
)
    requires TDsStateToCASForDev_PreConditions(k)
    requires k_params == KToKParams(k) 

    requires TDsStateGetTDIDs(tds_state) == AllActiveTDs(k)
        // Requirement: The TDs' state includes all active TDs
    requires IsDevID(k, dev_id)
    requires SubjPID_DevID(k, dev_id) != NULL
        // Requirement: The devices <dev_id> must be active
    requires DevHCodedTDRefsObjsInSameDev(k, dev_id)
    requires IDToDev(k, dev_id).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)

    requires read_td in TDsStateGetTDIDs(tds_state) 
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, read_td)

    requires forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) && 
                                    // The TD (<td_id2>) is active
                CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                    // For all active TDs can be read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2)
        // Requirement: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects

    ensures forall o_id2 :: o_id2 in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, read_td)
                ==> o_id2 in AllActiveObjs(k)
{
    // Dafny can automatically prove this lemma
}