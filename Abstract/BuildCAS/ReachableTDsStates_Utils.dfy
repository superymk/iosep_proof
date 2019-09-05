include "../Syntax.dfy"
include "../Utils.dfy"
include "../Properties_Utils.dfy"
include "Utils_BuildCAS.dfy"
include "ReachableTDs.dfy"

predicate FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params:ReachableTDsKParams)
    ensures FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params) 
                ==> MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    ensures FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params) 
                ==> (forall dev_id :: dev_id in k_params.subjects.devs
                        ==> (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_tds) <= 
                                IDToDev_SlimState(k_params.subjects, dev_id).td_ids) &&
                            (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_fds) <= 
                                IDToDev_SlimState(k_params.subjects, dev_id).fd_ids) &&
                            (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_dos) <= 
                                IDToDev_SlimState(k_params.subjects, dev_id).do_ids))
{
    FindAllTDsReadByDev_KParams_PreConditions(k_params)
}

// Given a set of states of active TDs (<known_tds_states>), this method finds
// what states of active TDs can be set due to TD writings by the device (<dev>)
//
// Devices cannot modify the states of any inactive I/O objects, because active
// devices have no tranfers to these objects.
//
// Returns empty set, if there is no additional states of active TDs
// Returns empty set, if status is false
method FindAllActiveTDsStatesByDev(
    k_params:ReachableTDsKParams,  
    known_tds_states:seq<TDs_Vals>, dev_id:Dev_ID
) returns (tds_states:set<TDs_Vals>, status:bool)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: Each known TDs' state includes all active TDs

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Requirement: If hardcoded TDs are in <known_tds_state>, their values are always from <k_params.hcoded_tds>

    ensures (status == false) ==> (tds_states == {})
        // Property: Returns empty set, if status is false
    ensures forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Property: Each new TDs' state includes all active TDs
    ensures (status == true) ==> (SeqToSet<TDs_Vals>(known_tds_states) <= tds_states)
        // Property 3: <known_tds_states> must be in <tds_states>
    ensures FindAllActiveTDsStatesByDev2_Property4(k_params, known_tds_states, dev_id, tds_states)
        // Property 4: Foreach result TDs' state (<tds_state2>), there must exist  
        // a known TDs' state (<known_tds_state>), the corresponding updates to 
        // the known TD state are requested in the known TD state, and the 
        // updates can be issued by the device (<dev_id>)

    ensures FindAllActiveTDsStatesByDev2_Property5(k_params, known_tds_states, dev_id, tds_states, status)
        // Property 5: Foreach requested update of TDs' state (<tds_diff>) to
        // a known TDs' state (<known_tds_state>), the update leads to a new 
        // TDs' state in the result; i.e., new to the <known_tds_state>
    ensures FindAllActiveTDsStatesByDev2_Property6(k_params, known_tds_states, dev_id, status)
        // Property 6: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects
    ensures forall tds_state2 :: tds_state2 in tds_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Property 7: Hardcoded TDs are always mapped to their initial values

    decreases |known_tds_states|
{
    if(|known_tds_states| == 0)
    {    return {}, true; }
    else
    {
        var known_tds_state := known_tds_states[0];
        var known_tds_states_step := known_tds_states[1..];

        var tds_states_dev:set<TDs_Vals>;
        var tds_states_next; 
        var s;

        tds_states_dev, s := FindAllActiveTDsStatesByDev_FromOneTDsState(k_params, known_tds_state, dev_id);
        if (!s)
        { return {}, false;} 
        assert known_tds_state in tds_states_dev;

        tds_states_next, s := FindAllActiveTDsStatesByDev(k_params, known_tds_states_step, dev_id);
        if (!s)
        { return {}, false;} 

        Lemma_FindAllActiveTDsStatesByDev_Property3(
            dev_id, known_tds_states, known_tds_state, known_tds_states_step, tds_states_dev, tds_states_next);

        Lemma_FindAllActiveTDsStatesByDev_FromOneTDsStateReturnsCorrectResult(
            k_params,
            dev_id, known_tds_state, tds_states_dev);
        Lemma_FindAllActiveTDsStatesByDev_Property4(
            k_params,
            dev_id, known_tds_states, known_tds_state, known_tds_states_step, tds_states_dev, tds_states_next);
        Lemma_FindAllActiveTDsStatesByDev_Property5(
            k_params,
            dev_id, known_tds_states, known_tds_state, known_tds_states_step, tds_states_dev, tds_states_next);
        Lemma_FindAllActiveTDsStatesByDev_Property6(
            k_params,
            dev_id, known_tds_states, known_tds_state, known_tds_states_step, tds_states_dev, tds_states_next);

        assert FindAllActiveTDsStatesByDev2_Property4(k_params, known_tds_states, dev_id, tds_states_dev + tds_states_next);

        return tds_states_dev + tds_states_next, true;
    }
}

predicate FindAllActiveTDsStatesByDev2_Property4(
    k_params:ReachableTDsKParams,  
    known_tds_states:seq<TDs_Vals>, dev_id:Dev_ID, tds_states:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: Each known TDs' state includes all active TDs
{
    forall tds_state2 :: tds_state2 in tds_states
                ==> (exists known_tds_state, tds_diff :: known_tds_state in known_tds_states && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                        tds_diff == TDsStateDiff(tds_state2, known_tds_state) && 
                        IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff))
        // Property 4: Foreach result TDs' state (<tds_state2>), there must exist  
        // a known TDs' state (<known_tds_state>), the corresponding updates to 
        // the known TD state are requested in the known TD state, and the 
        // updates can be issued by the device (<dev_id>)
}

predicate FindAllActiveTDsStatesByDev2_Property5(
    k_params:ReachableTDsKParams,  
    known_tds_states:seq<TDs_Vals>, dev_id:Dev_ID, tds_states:set<TDs_Vals>, status:bool
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: Each known TDs' state includes all active TDs
{
    (status == true)
        ==> (forall known_tds_state, tds_diff:map<TD_ID, TD_Val> :: 
            known_tds_state in known_tds_states && 
            MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
            TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds &&
            IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
            ==> (exists tds_state2 :: tds_state2 in tds_states && 
                TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                TDsStateDiff(tds_state2, known_tds_state) == tds_diff))
        // Property 5: Foreach requested update of TDs' state (<tds_diff>) to
        // a known TDs' state (<known_tds_state>), the update leads to a new 
        // TDs' state in the result; i.e., new to the <known_tds_state>
}

predicate FindAllActiveTDsStatesByDev2_Property6(
    k_params:ReachableTDsKParams,  
    known_tds_states:seq<TDs_Vals>, dev_id:Dev_ID, status:bool
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: Each known TDs' state includes all active TDs
{
    (status == true)
        <==> (forall known_tds_state, td_id2 :: 
                known_tds_state in known_tds_states && 
                td_id2 in TDsStateGetTDIDs(known_tds_state) &&
                td_id2 in k_params.objs_td_ids &&
                ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, td_id2)
                    // For all active TDs can be read by the device
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, known_tds_state, td_id2))
        // Property 6: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects
}

// Function: Are TD writes in <tds_diff>: (1) requested in <tds_state> (
// including hardcoded TD write transfers of the device), and (2) can be issued
// by the device (<dev_id>)
function IsTDsDiffReqInActiveTDsStateAndIssuedByDev(
    k_params:ReachableTDsKParams,   
    dev_id:Dev_ID, tds_state:TDs_Vals, tds_diff:map<TD_ID, TD_Val>
) : bool
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The known TDs' state includes all active TDs
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids
{
    // All <td_id> and <td_new_cfg> in <tds_diff> must be requested in the <known_tds_state>
    forall td_id, td_new_cfg :: td_id in tds_diff &&
        td_new_cfg == tds_diff[td_id]
            ==> (exists tdx_id :: 
                        tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg))
                                // the active TD refs the TD with W and the new TD cfg
}

// Function: Are TD writes in <tds_diff>: (1) requested in <tds_state> (
// including hardcoded TD write transfers of the device), and (2) can be issued
// by the device (<dev_id>), and (3) can cause new state of active TDs 
// (i.e., new to the <tds_state>)
function IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(
    k_params:ReachableTDsKParams,   
    dev_id:Dev_ID, tds_state:TDs_Vals, tds_diff:map<TD_ID, TD_Val>
) : bool
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The known TDs' state includes all active TDs
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids
{
    IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, tds_state, tds_diff) &&
    (forall td_id2 :: td_id2 in tds_diff 
        ==> td_id2 in tds_state &&
            tds_diff[td_id2] != tds_state[td_id2])
                                // <tds_diff> must hold TDs' state differences 
}




//******** Private Functions ********//
// Predicate: In an active TDs' state, all hardcoded TDs of active devices 
// must be mapped to their initial values
predicate TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params:ReachableTDsKParams, tds_state:TDs_Vals)
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
{
    forall dev_id :: IsDevID_SlimState(k_params.subjects, dev_id) &&
                     k_params.subjects.devs[dev_id].hcoded_td_id in tds_state
        ==> tds_state[k_params.subjects.devs[dev_id].hcoded_td_id] == k_params.hcoded_tds[dev_id]
}

// Given one state of active TDs (<known_tds_state>), this method returns what   
// states of all active TDs can be set due to TD writings by the device
// Property: Returns empty set, if status is false
method FindAllActiveTDsStatesByDev_FromOneTDsState(
    k_params:ReachableTDsKParams,   
    known_tds_state:TDs_Vals, dev_id:Dev_ID
) returns (tds_states:set<TDs_Vals>, status:bool)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, known_tds_state)
        // Requirement: If hardcoded TDs are in <known_tds_state>, their values are always from <k_params.hcoded_tds>
        
    ensures (status == false) ==> (tds_states == {})
        // Property 1: Returns empty set, if status is false
    ensures forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Property 2: Each new TDs' state includes all active TDs
    ensures status == true
                ==> known_tds_state in tds_states
        // Property 3: <known_tds_state> must be in <tds_states>
    ensures status == true
                ==> (forall tds_state2 :: tds_state2 in tds_states
                    ==> exists tds_diff :: tds_diff == TDsStateDiff(tds_state2, known_tds_state))

    ensures forall tds_state2, tds_diff :: tds_state2 in tds_states && tds_diff == TDsStateDiff(tds_state2, known_tds_state)
                ==> IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff)
        // Property 4: Foreach result state of active TDs (<tds_state2>), the  
        // corresponding updates to the known TD state must be requested in the 
        // known TD state, and the updates can be issued by the device (<dev_id>)
    ensures status == true
                ==> (forall tds_diff:map<TD_ID, TD_Val> :: 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
                    ==> (exists tds_state2 :: tds_state2 in tds_states && TDsStateDiff(tds_state2, known_tds_state) == tds_diff))
        // Property 5: Foreach requested state update (<tds_diff>) to the 
        // <known_tds_state>, the update leads to a new state of active TDs in 
        // the result; i.e., new to the <known_tds_state>
    ensures status == true
                <==> (forall td_id2 :: td_id2 in TDsStateGetTDIDs(known_tds_state) && 
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, td_id2)
                            // For all active TDs can be read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, known_tds_state, td_id2))
        // Property 6: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects
    ensures forall tds_state2 :: tds_state2 in tds_states
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2)
        // Property 7: If hardcoded TDs are in <tds_state2>, their values are always from <k_params.hcoded_tds>
{
    var tds_dev_writes, s := FindAllTDWritesByDev(k_params, known_tds_state, dev_id);
    assert forall td_id :: td_id in tds_dev_writes
            ==> td_id !in k_params.hcoded_td_ids;

    if(!s)
    { return {}, false;} 

    tds_dev_writes := TDWriteInfoCauseNewTDsState(known_tds_state, tds_dev_writes);

    // <result_set> holds all active TDs' states due to the device issues 0+ TD 
    // writes due to reading <known_tds_state> and hardcoded TD write transfers
    var result_set := TDsWritesInfoToTDsStates(known_tds_state, tds_dev_writes);

    assert MapGetKeys(tds_dev_writes) <= MapGetKeys(known_tds_state);
    assert forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                (forall td_id2 :: td_id2 in tds_diff 
                    ==> tds_diff[td_id2] != known_tds_state[td_id2] &&
                        (exists tdx_id ::  
                                tdx_id in k_params.objs_td_ids && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                                CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, tdx_id) && 
                                            // exists an active TD readable by the device 
                                IsTDWriteInTD(known_tds_state, tdx_id, td_id2, tds_diff[td_id2])))
                                            // the active TD refs the <td_id2> with W and the TD cfg 
                                            // (<tds_diff[td_id2]>)    
            <==> 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2]);

    assert forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2])
                ==> (exists tds_state2 :: tds_state2 in result_set && TDsStateDiff(tds_state2, known_tds_state) == tds_diff);

    Lemma_FindAllActiveTDsStatesByDev_FromOneTDsState_Property4(
        k_params,   
        known_tds_state, dev_id, tds_dev_writes, result_set);

    Lemma_FindAllActiveTDsStatesByDev_FromOneTDsState_Property5(
        k_params,   
        known_tds_state, dev_id, tds_dev_writes, result_set);

    // Prove Property 7
    if(exists tds_state2, td_id :: tds_state2 in result_set &&
                    td_id in k_params.hcoded_td_ids &&
                    td_id in known_tds_state &&
                    tds_state2[td_id] != known_tds_state[td_id])
    {
        var tds_state2, td_id :| tds_state2 in result_set &&
                    td_id in k_params.hcoded_td_ids &&
                    td_id in known_tds_state &&
                    tds_state2[td_id] != known_tds_state[td_id];
        var tds_diff := TDsStateDiff(tds_state2, known_tds_state);

        assert td_id in tds_diff;

        // Show conflicts
        assert IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff);
    }
    assert forall tds_state2, td_id :: tds_state2 in result_set &&
                    td_id in k_params.hcoded_td_ids &&
                    td_id in known_tds_state
            ==> tds_state2[td_id] == known_tds_state[td_id];

    assert forall tds_state2 :: tds_state2 in result_set
                ==> TDsState_ActiveHCodedTDsAlwaysHaveTheirInitialValues(k_params, tds_state2);

    return result_set, true; 
}

// Given one state of all TDs (<known_tds_state>), and return all the requested 
// TD writes can be issued by the device (<dev>)
// Return empty map, if there is no additional TD writes by the device
method FindAllTDWritesByDev(
    k_params:ReachableTDsKParams,  
    tds_state:TDs_Vals, dev_id:Dev_ID
) returns (tds_writes:TDs_Writes_Info, status:bool)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires k_params.subjects.devs[dev_id].hcoded_td_id in tds_state
                ==> tds_state[k_params.subjects.devs[dev_id].hcoded_td_id] == k_params.hcoded_tds[dev_id]
        // Requirement: If hardcoded TDs are in <tds_state>, their values are always from <k_params.hcoded_tds>

    ensures forall td_id2 :: td_id2 in tds_writes
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Property: TDs in <tds_writes> must be active TDs in the I/O system
    ensures status == true 
                ==> (forall td_id, td_cfg :: td_id in tds_writes && 
                        td_cfg in tds_writes[td_id]
                        ==> (exists tdx_id :: 
                                tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                                CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                                                // exists an active TD readable by the device 
                                IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg)))
                                                            // the active TD refs the TD with W and the new TD cfg 
        // Property: Foreach TD write (<td_id> with <td_cfg>) in <tds_writes>, 
        // there must be an active TD (<tdx_id>) readable by the device writes 
        // the TD (<td_id>) with the new configuration (<td_cfg>)
    ensures status == true 
                ==> (forall tdx_id :: tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id)  
                                                            // Forall active TD readable by the device
                        ==> (forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                                                            // the active TD refs the TD with W and the new TD cfg
                                ==> td_id in tds_writes && td_cfg in tds_writes[td_id]))
        // Property: Foreach active TD readable by the device, all TD writes 
        // requested in these TDs are recorded in <tds_writes>
    ensures status == true
                <==> (forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) && 
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                            // For all active TDs can be read by the device
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2))
        // Property: Any active TDs can be read by the device (<dev_id>) 
        // have no invalid references to I/O objects
    ensures forall td_id2 :: td_id2 in tds_writes
                ==> td_id2 !in k_params.hcoded_td_ids
{
    var read_tds_set, s := FindAllTDsReadByDev(k_params, tds_state, dev_id);
    var read_tds := SetToSeq<TD_ID>(read_tds_set);
    var t_tds_writes:TDs_Writes_Info := map[];
    var i := 0;

    if (!s)
    { return map[], false;} 

    assert forall td_id2 :: td_id2 in read_tds_set
                ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2);

    while (i < |read_tds|)
        invariant i <= |read_tds|

        invariant forall td_id2 :: td_id2 in t_tds_writes
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) 
        invariant forall td_id2 :: td_id2 in t_tds_writes
                    ==> ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL

        invariant forall td_id, td_cfg :: td_id in t_tds_writes && 
                    td_cfg in t_tds_writes[td_id]
                    ==> (exists tdx_id :: 
                        tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                                            // exists an active TD readable by the device 
                        IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg))

        invariant forall tdx_id :: tdx_id in read_tds[..i]
                        ==> (forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                                                            // the active TD refs the TD with W and the new TD cfg
                                ==> td_id in t_tds_writes && td_cfg in t_tds_writes[td_id])
                    // Loop invariant 5

        invariant forall td_id2 :: td_id2 in t_tds_writes
                    ==> td_id2 !in k_params.hcoded_td_ids
    {
        var read_td := read_tds[i];
        var tds_writes_from_td:TDs_Writes_Info := TDWritesInTDCfg(tds_state[read_td]);
        var old_tds_writes;
        assert MapGetKeys<TD_ID, set<TD_Val>>(tds_writes_from_td) <= TDsStateGetTDIDs(tds_state);
        assert forall td_id2 :: td_id2 in tds_writes_from_td
                    ==> ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL;

        old_tds_writes := t_tds_writes;
        t_tds_writes := TDWritesInfoMerge(t_tds_writes, tds_writes_from_td);

        Lemma_FindAllTDWritesByDev_LoopInvariant5(tds_state, dev_id, 
            t_tds_writes, old_tds_writes, tds_writes_from_td,
            read_tds[..i+1], read_tds[..i], read_td);
        
        i := i + 1;
    }

    assert forall tdx_id :: tdx_id in read_tds[..i] <==> tdx_id in read_tds;
    assert forall tdx_id :: tdx_id in read_tds
                        ==> (forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                                                            // the active TD refs the TD with W and the new TD cfg
                                ==> td_id in t_tds_writes && td_cfg in t_tds_writes[td_id]);
    
    return t_tds_writes, true; 
}

predicate FindAllTDsReadByDev_KParams_PreConditions(k_params:ReachableTDsKParams)
    ensures FindAllTDsReadByDev_KParams_PreConditions(k_params) 
                ==> MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
    ensures FindAllTDsReadByDev_KParams_PreConditions(k_params) 
                ==> (forall dev_id :: dev_id in k_params.subjects.devs
                        ==> (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_tds) <= 
                                IDToDev_SlimState(k_params.subjects, dev_id).td_ids) &&
                            (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_fds) <= 
                                IDToDev_SlimState(k_params.subjects, dev_id).fd_ids) &&
                            (MapGetKeys(HCodedTDValOfDev(k_params.hcoded_tds, dev_id).trans_params_dos) <= 
                                IDToDev_SlimState(k_params.subjects, dev_id).do_ids))
{
    FindAllTDsReachableFromTDWithR_KParams_PreConditions(k_params) &&

    (forall td_id, fd_id :: TD_ID(td_id) in k_params.objs_td_ids && FD_ID(fd_id) in k_params.objs_fd_ids
        ==> td_id != fd_id) &&
    (forall td_id, do_id :: TD_ID(td_id) in k_params.objs_td_ids && DO_ID(do_id) in k_params.objs_do_ids
        ==> td_id != do_id) &&
    (forall fd_id, do_id :: FD_ID(fd_id) in k_params.objs_fd_ids && DO_ID(do_id) in k_params.objs_do_ids
        ==> fd_id != do_id) &&
        // Requirement: Objects have different internal IDs
    (forall dev_id, td_id :: 
                dev_id in k_params.subjects.devs && td_id in k_params.subjects.devs[dev_id].td_ids
                ==> td_id in k_params.objs_td_ids) &&
    (forall dev_id, fd_id :: 
                dev_id in k_params.subjects.devs && fd_id in k_params.subjects.devs[dev_id].fd_ids
                ==> fd_id in k_params.objs_fd_ids) &&
    (forall dev_id, do_id :: 
                dev_id in k_params.subjects.devs && do_id in k_params.subjects.devs[dev_id].do_ids
                ==> do_id in k_params.objs_do_ids) &&
        // Requirement: Objects in devices must be in the state
    (forall dev_id, td_id :: dev_id in k_params.hcoded_tds && td_id in k_params.hcoded_tds[dev_id].trans_params_tds
                ==> td_id in IDToDev_SlimState(k_params.subjects, dev_id).td_ids) &&
    (forall dev_id, fd_id :: dev_id in k_params.hcoded_tds && fd_id in k_params.hcoded_tds[dev_id].trans_params_fds
                ==> fd_id in IDToDev_SlimState(k_params.subjects, dev_id).fd_ids) &&
    (forall dev_id, do_id :: dev_id in k_params.hcoded_tds && do_id in k_params.hcoded_tds[dev_id].trans_params_dos
                ==> do_id in IDToDev_SlimState(k_params.subjects, dev_id).do_ids) &&
        // Requirement: Objects refed in a hardcoded TD must be in the device own the TD
    (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.subjects.devs[dev_id].td_ids) &&
        // Requirement: Hardcoded TDs are in devices
    (forall dev_id :: dev_id in k_params.subjects.devs
                ==> k_params.subjects.devs[dev_id].hcoded_td_id in k_params.hcoded_td_ids) &&
        // Requirement: Hardcoded TDs are recorded in <k_params.hcoded_td_ids>

    (true)
}

// Given one state of all TDs (<known_tds_state>), and return all TDs read by
// the device (<dev_id>)
// Return empty set and false, if any TDs read by the device include invalid
// references to I/O objects
method  FindAllTDsReadByDev(
    k_params:ReachableTDsKParams,   
    tds_state:TDs_Vals, dev_id:Dev_ID
) returns (td_ids:set<TD_ID>, status:bool)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    ensures forall td_id2 :: td_id2 in td_ids
                        ==> td_id2 in TDsStateGetTDIDs(tds_state) && 
                            ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                            CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
        // Property: Each returned TD in <td_ids> is active, and can be
        // read by the device (<dev_id>)
    ensures status == true
                ==> (forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) && 
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id2)
                            // For all active TDs can be read by the device
                        ==> td_id2 in td_ids)
        // Property: All active TDs can be read by the device exist in <td_ids>
    ensures status == true
                <==> (forall td_id2 :: td_id2 in td_ids
                    ==> td_id2 in TDsStateGetTDIDs(tds_state) &&
                        !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id2))
        // Property: Each returned TD in <td_ids> has no invalid references to
        // any I/O objects
{
    var hcoded_td_id := k_params.subjects.devs[dev_id].hcoded_td_id;
    
    var t_td_ids, s := FindAllTDsReachableFromHCodedTDsWithR(k_params, tds_state, dev_id, hcoded_td_id);
    if (!s)
    { return t_td_ids, false;}
    
    {
        assert forall td_id2 :: td_id2 in TDsStateGetTDIDs(tds_state) &&
                ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                IsActiveTDRefActiveTDInChainWithR(k_params, tds_state, hcoded_td_id, td_id2)
                ==> td_id2 in t_td_ids;
    }
    Lemma_RootTDsAndAllActiveTDsRefedByRootTDsAreAllTDsReadByDev(k_params, tds_state, dev_id, hcoded_td_id, t_td_ids);

    return t_td_ids, true;
}




//******** Utility Lemmas ********//
// Proof of the loop invariant 5 of <FindAllTDWritesByDev> method 
lemma Lemma_FindAllTDWritesByDev_LoopInvariant5(
    tds_state:TDs_Vals, dev_id:Dev_ID,
    new_tds_writes:TDs_Writes_Info, old_tds_writes:TDs_Writes_Info, add_tds_writes:TDs_Writes_Info,
    new_read_tds:seq<TD_ID>, old_read_tds:seq<TD_ID>, add_read_td:TD_ID
)
    requires forall td_id :: td_id in old_read_tds 
                ==> td_id in TDsStateGetTDIDs(tds_state)
    requires add_read_td in TDsStateGetTDIDs(tds_state)

    requires forall td_id :: td_id in new_tds_writes
                <==> td_id in old_tds_writes || td_id in add_tds_writes
        // Requirement: <new_tds_writes> merges the TD IDs in <old_tds_writes>
        // and <add_tds_writes>
    requires forall td_id :: td_id in new_tds_writes && td_id !in old_tds_writes
                ==> new_tds_writes[td_id] == add_tds_writes[td_id]
    requires forall td_id :: td_id in new_tds_writes && td_id !in add_tds_writes
                ==> new_tds_writes[td_id] == old_tds_writes[td_id]
    requires forall td_id :: td_id in new_tds_writes && td_id in old_tds_writes &&
                            td_id in add_tds_writes
                ==> new_tds_writes[td_id] == add_tds_writes[td_id] + old_tds_writes[td_id]
        // Requirement: <new_tds_writes> merges the TD write params in <old_tds_writes>
        // and <add_tds_writes>        
    
    requires |new_read_tds| == |old_read_tds| + 1
    requires |old_read_tds| >= 0
    requires new_read_tds[..|old_read_tds|] == old_read_tds
    requires new_read_tds[|new_read_tds|-1] == add_read_td
        // Requirement: <new_read_tds> is the <old_read_tds> appended with <add_read_td>
    requires forall i, j :: 0 <= i < |old_read_tds| && 0 <= j < |old_read_tds|
                ==> (i == j <==> old_read_tds[i] == old_read_tds[j])
        // Requirement: No duplicate TD IDs in <old_read_tds>
    requires forall i, j :: 0 <= i < |new_read_tds| && 0 <= j < |new_read_tds|
                ==> (i == j <==> new_read_tds[i] == new_read_tds[j])
        // Requirement: No duplicate TD IDs in <new_read_tds>
    
    requires forall tdx_id :: tdx_id in old_read_tds
                ==> (forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                                                    // the active TD refs the TD with W and the new TD cfg
                        ==> td_id in old_tds_writes && td_cfg in old_tds_writes[td_id])
    requires forall td_id, td_cfg :: IsTDWriteInTD(tds_state, add_read_td, td_id, td_cfg) 
                                ==> td_id in add_tds_writes && td_cfg in add_tds_writes[td_id]
    
    ensures forall tdx_id :: tdx_id in new_read_tds
                ==> (forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                                                    // the active TD refs the TD with W and the new TD cfg
                        ==> td_id in new_tds_writes && td_cfg in new_tds_writes[td_id])
{
    forall tdx_id | tdx_id in new_read_tds
        ensures forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                        ==> td_id in new_tds_writes && td_cfg in new_tds_writes[td_id]
    {
        if(tdx_id != add_read_td)
        {
            assert tdx_id in old_read_tds;
            assert forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                        ==> td_id in new_tds_writes && td_cfg in new_tds_writes[td_id];
        }
        else
        {
            assert tdx_id == add_read_td;
            assert forall td_id, td_cfg :: IsTDWriteInTD(tds_state, tdx_id, td_id, td_cfg) 
                        ==> td_id in new_tds_writes && td_cfg in new_tds_writes[td_id];
        }
    }
}

lemma Lemma_FindAllActiveTDsStatesByDev_FromOneTDsStateReturnsCorrectResult(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, known_tds_state:TDs_Vals, tds_states_dev:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds
        // Requirement: The known TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in tds_states_dev
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds

    requires forall tds_state2, tds_diff :: tds_state2 in tds_states_dev && tds_diff == TDsStateDiff(tds_state2, known_tds_state)
                ==> IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff)
    requires (forall tds_diff:map<TD_ID, TD_Val> :: 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
                    ==> (exists tds_state2 :: tds_state2 in tds_states_dev && TDsStateDiff(tds_state2, known_tds_state) == tds_diff))

    ensures forall tds_state2 :: tds_state2 in tds_states_dev
            ==> (exists tds_diff ::  
                    TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                    tds_diff == TDsStateDiff(tds_state2, known_tds_state) && 
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff))
    ensures forall tds_diff:map<TD_ID, TD_Val> :: 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                    TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
                    ==> (exists tds_state2 :: tds_state2 in tds_states_dev && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                        TDsStateDiff(tds_state2, known_tds_state) == tds_diff)
{
    forall tds_state2 | tds_state2 in tds_states_dev
        ensures exists tds_diff ::  
                    TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                    tds_diff == TDsStateDiff(tds_state2, known_tds_state) && 
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff)
    {
        if(tds_state2 != known_tds_state)
        {
            var tds_diff := TDsStateDiff(tds_state2, known_tds_state);
            assert tds_state2 in tds_states_dev;
            assert IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff);
        }
        else
        {
            var tds_diff := map[];
            assert tds_state2 == known_tds_state;
            assert tds_state2 in tds_states_dev;
            assert tds_diff == TDsStateDiff(tds_state2, known_tds_state);
            assert IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff);
        }
    }

    forall tds_diff2:map<TD_ID, TD_Val> | 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff2) <= TDsStateGetTDIDs(known_tds_state) &&
                    TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff2)
        ensures exists tds_state2 :: tds_state2 in tds_states_dev && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                        TDsStateDiff(tds_state2, known_tds_state) == tds_diff2
    {
        assert exists tds_state2 :: tds_state2 in tds_states_dev && 
                TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                TDsStateDiff(tds_state2, known_tds_state) == tds_diff2;
    }
}

lemma Lemma_FindAllActiveTDsStatesByDev_Property3(
    dev_id:Dev_ID,
    known_tds_states:seq<TDs_Vals>, known_tds_state:TDs_Vals, known_tds_states_step:seq<TDs_Vals>,
    tds_states_dev:set<TDs_Vals>, tds_states_next:set<TDs_Vals>
)
    requires |known_tds_states| > 0
    requires known_tds_states[0] == known_tds_state
    requires known_tds_states[1..] == known_tds_states_step

    requires known_tds_state in tds_states_dev
    requires forall tds_state2 :: tds_state2 in known_tds_states_step 
            ==> tds_state2 in tds_states_next

    ensures forall tds_state2 :: tds_state2 in known_tds_states 
            ==> tds_state2 in tds_states_dev + tds_states_next

    ensures SeqToSet<TDs_Vals>(known_tds_states) <= tds_states_dev + tds_states_next
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindAllActiveTDsStatesByDev_Property4(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, known_tds_states:seq<TDs_Vals>, known_tds_state:TDs_Vals, known_tds_states_step:seq<TDs_Vals>,
    tds_states_dev:set<TDs_Vals>, tds_states_next:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: The known TDs' states includes all active TDs

    requires |known_tds_states| > 0
    requires known_tds_states[0] == known_tds_state
    requires known_tds_states[1..] == known_tds_states_step

    requires FindAllActiveTDsStatesByDev2_Property4(k_params, known_tds_states, dev_id, tds_states_dev)
    requires FindAllActiveTDsStatesByDev2_Property4(k_params, known_tds_states, dev_id, tds_states_next)

    ensures FindAllActiveTDsStatesByDev2_Property4(k_params, known_tds_states, dev_id, tds_states_dev + tds_states_next)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindAllActiveTDsStatesByDev_Property5(
    k_params:ReachableTDsKParams,  
    dev_id:Dev_ID, known_tds_states:seq<TDs_Vals>, known_tds_state:TDs_Vals, known_tds_states_step:seq<TDs_Vals>,
    tds_states_dev:set<TDs_Vals>, tds_states_next:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: The known TDs' states includes all active TDs

    requires |known_tds_states| > 0
    requires known_tds_states[0] == known_tds_state
    requires known_tds_states[1..] == known_tds_states_step

    requires forall tds_diff:map<TD_ID, TD_Val> :: 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                    TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
                    ==> (exists tds_state2 :: tds_state2 in tds_states_dev && 
                        TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state) && 
                        TDsStateDiff(tds_state2, known_tds_state) == tds_diff)
    requires FindAllActiveTDsStatesByDev2_Property5(k_params, known_tds_states_step, dev_id, tds_states_next, true)

    ensures FindAllActiveTDsStatesByDev2_Property5(k_params, known_tds_states, dev_id, tds_states_dev + tds_states_next, true)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindAllActiveTDsStatesByDev_Property6(
    k_params:ReachableTDsKParams, 
    dev_id:Dev_ID, known_tds_states:seq<TDs_Vals>, known_tds_state:TDs_Vals, known_tds_states_step:seq<TDs_Vals>,
    tds_states_dev:set<TDs_Vals>, tds_states_next:set<TDs_Vals>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires forall tds_state2 :: tds_state2 in known_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: The known TDs' states includes all active TDs

    requires |known_tds_states| > 0
    requires known_tds_states[0] == known_tds_state
    requires known_tds_states[1..] == known_tds_states_step

    requires forall td_id2 :: td_id2 in TDsStateGetTDIDs(known_tds_state) && 
                        ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, td_id2)
                        ==> !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, known_tds_state, td_id2)
    requires FindAllActiveTDsStatesByDev2_Property6(k_params, known_tds_states_step, dev_id, true)

    ensures FindAllActiveTDsStatesByDev2_Property6(k_params, known_tds_states, dev_id, true)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_DefApply(
    k_params:ReachableTDsKParams,   
    dev_id:Dev_ID, tds_state:TDs_Vals, tds_diff:map<TD_ID, TD_Val>
)
    requires forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    requires forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    requires forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    requires forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    requires MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
        // <k_params.hcoded_tds> include all devices
    // Requirements required by functions in this function

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The known TDs' state includes all active TDs
    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids
    
    ensures IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, tds_state, tds_diff)
                == (forall td_id, td_new_cfg :: td_id in tds_diff &&
                        td_new_cfg == tds_diff[td_id]
                            ==> (exists tdx_id :: 
                                        tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                                // exists an active TD readable by the device 
                                        IsTDWriteInTD(tds_state, tdx_id, td_id, td_new_cfg)))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_IsTDsDiffReqInActiveTDsStateAndIssuedByDev_Apply(
    k_params:ReachableTDsKParams,   
    dev_id:Dev_ID, td_id:TD_ID, tds_state:TDs_Vals, tds_diff:map<TD_ID, TD_Val>
)
    requires FindAllActiveTDsStatesByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The known TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, tds_state, tds_diff)
    requires td_id in tds_diff

    ensures exists tdx_id :: 
                        tdx_id in TDsStateGetTDIDs(tds_state) && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                        CanActiveDevReadActiveTD(k_params, tds_state, dev_id, tdx_id) && 
                                // exists an active TD readable by the device 
                        IsTDWriteInTD(tds_state, tdx_id, td_id, tds_diff[td_id])
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas ********//
lemma Lemma_FindAllActiveTDsStatesByDev_FromOneTDsState_Property4(
    k_params:ReachableTDsKParams,   
    known_tds_state:TDs_Vals, dev_id:Dev_ID, tds_dev_writes:TDs_Writes_Info, tds_states:set<TDs_Vals>
)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires MapGetKeys(tds_dev_writes) <= MapGetKeys(known_tds_state)
    requires forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                (forall td_id2 :: td_id2 in tds_diff 
                    ==> tds_diff[td_id2] != known_tds_state[td_id2] &&
                        (exists tdx_id ::  
                                tdx_id in k_params.objs_td_ids && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                                CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, tdx_id) && 
                                            // exists an active TD readable by the device 
                                IsTDWriteInTD(known_tds_state, tdx_id, td_id2, tds_diff[td_id2])))
                                            // the active TD refs the <td_id2> with W and the TD cfg 
                                            // (<tds_diff[td_id2]>)
            <==> 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2])

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state)
    requires forall tds_state2, td_id2 :: tds_state2 in tds_states && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> (TDsStateGetTDCfg(tds_state2, td_id2) == TDsStateGetTDCfg(known_tds_state, td_id2) ||
                        (td_id2 in tds_dev_writes &&
                        TDsStateGetTDCfg(tds_state2, td_id2) in tds_dev_writes[td_id2]))
        //// Property: Foreach result TDs' state, it is <tds_state> overwritten 
        //// with <tds_dev_writes>
    requires forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2])
                ==> (exists tds_state2 :: tds_state2 in tds_states && TDsStateDiff(tds_state2, known_tds_state) == tds_diff)
        //// Property: Foreach <tds_diff> in tds_dev_writes, there is a state 
        //// result from the <tds_diff>
    requires known_tds_state in tds_states
        // Requirements from TDsWritesInfoToTDsStates

    ensures forall tds_state2, tds_diff :: tds_state2 in tds_states && tds_diff == TDsStateDiff(tds_state2, known_tds_state)
                ==> IsTDsDiffReqInActiveTDsStateAndIssuedByDev(k_params, dev_id, known_tds_state, tds_diff)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_FindAllActiveTDsStatesByDev_FromOneTDsState_Property5(
    k_params:ReachableTDsKParams,   
    known_tds_state:TDs_Vals, dev_id:Dev_ID, tds_dev_writes:TDs_Writes_Info, tds_states:set<TDs_Vals>
)
    requires FindAllTDsReadByDev_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(known_tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs

    requires IsDevID_SlimState(k_params.subjects, dev_id)
    requires SubjPID_DevID_SlimState(k_params.subjects, dev_id) != NULL
        // Requirement: The device must be active
    requires DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id)
    requires IDToDev_SlimState(k_params.subjects, dev_id).td_ids <= k_params.objs_td_ids

    requires MapGetKeys(tds_dev_writes) <= MapGetKeys(known_tds_state)
    requires forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                (forall td_id2 :: td_id2 in tds_diff 
                    ==> tds_diff[td_id2] != known_tds_state[td_id2] &&
                        (exists tdx_id ::  
                                tdx_id in k_params.objs_td_ids && ObjPID_SlimState(k_params.objs_pids, tdx_id.oid) != NULL &&
                                CanActiveDevReadActiveTD(k_params, known_tds_state, dev_id, tdx_id) && 
                                            // exists an active TD readable by the device 
                                IsTDWriteInTD(known_tds_state, tdx_id, td_id2, tds_diff[td_id2])))
                                            // the active TD refs the <td_id2> with W and the TD cfg 
                                            // (<tds_diff[td_id2]>)
            <==> 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2])

    requires forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(known_tds_state)
    requires forall tds_state2, td_id2 :: tds_state2 in tds_states && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> (TDsStateGetTDCfg(tds_state2, td_id2) == TDsStateGetTDCfg(known_tds_state, td_id2) ||
                        (td_id2 in tds_dev_writes &&
                        TDsStateGetTDCfg(tds_state2, td_id2) in tds_dev_writes[td_id2]))
        //// Property: Foreach result TDs' state, it is <tds_state> overwritten 
        //// with <tds_dev_writes>
    requires forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2])
                ==> (exists tds_state2 :: tds_state2 in tds_states && TDsStateDiff(tds_state2, known_tds_state) == tds_diff)
        //// Property: Foreach <tds_diff> in tds_dev_writes, there is a state 
        //// result from the <tds_diff>
    requires known_tds_state in tds_states
        // Requirements from TDsWritesInfoToTDsStates(known_tds_state, tds_dev_writes)

    ensures forall tds_diff:map<TD_ID, TD_Val> :: 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
                    ==> (exists tds_state2 :: tds_state2 in tds_states && TDsStateDiff(tds_state2, known_tds_state) == tds_diff)
{
    assert forall tds_diff:map<TD_ID, TD_Val> :: 
                    MapGetKeys<TD_ID, TD_Val>(tds_diff) <= TDsStateGetTDIDs(known_tds_state) &&
                    IsTDsDiffReqInActiveTDsStateAndIssuedByDevAndCauseNewActiveTDsState(k_params, dev_id, known_tds_state, tds_diff)
                ==> MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes);
}

// Lemma: In a secure state, All TDs read by a device are in the same 
// partition with the device
lemma Lemma_SecureActiveTDsState_TDsReadByActiveDevAreInSamePartitionWithDev_ForSubsetOfActiveDevs(
    k:State, k_params:ReachableTDsKParams, active_devs:set<Dev_ID>,
    tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID
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
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds_state, dev_id, td_id)
    requires k_params == KToKParams(k)

    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
                ==> o_id in AllObjsIDs(k.objects) &&
                    SubjPID(k, s_id) == ObjPID(k, o_id)
        // Requirement: k fulfills IsValidState_SubjsOwnObjsThenInSamePartition
    requires active_devs <= AllActiveDevs(k)
    requires dev_id in active_devs
    requires ActiveTDsStateIsSecure(k_params, active_devs, tds_state)
        // Requirement: <tds_state> is secure
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: Device (<dev_id>) can read the TD (<td_id>)

    ensures SubjPID_DevID(k, dev_id) == ObjPID(k, td_id.oid)
{
    var td_ids:seq<TD_ID> :| |td_ids| >= 1 && 
            (forall td_id2 :: td_id2 in td_ids ==> td_id2 in tds_state) &&
                                            // A list of active TDs
            td_ids[|td_ids| - 1] == td_id && // last TD is the TD (<td_id>)
            td_ids[0] == k_params.subjects.devs[dev_id].hcoded_td_id &&
                                            // first TD must be the hardcoded TD
            (forall i :: 0<=i<|td_ids| - 1 ==> td_ids[i+1] in TDIDReadsInTDCfg(tds_state[td_ids[i]]));
    
    assert DoOwnObj(k, dev_id.sid, td_ids[0].oid);
    assert SubjPID_DevID(k, dev_id) == ObjPID(k, td_ids[0].oid);

    Lemma_CanActiveDevReadActiveTD_DevCanReadAllIntermediateTDs(k_params, tds_state, dev_id, td_ids, td_id);

    var i := 0;

    while (i < |td_ids| - 1)
        invariant i <= |td_ids| - 1

        invariant ObjPID(k, td_ids[0].oid) == ObjPID(k, td_ids[i].oid)
    {
        if(ObjPID(k, td_ids[i].oid) != ObjPID(k, td_ids[i+1].oid))
        {
            assert DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_ids[i]);

            assert CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_ids[i]);
            assert !ActiveTDsStateIsSecure(k_params, active_devs, tds_state);
        }
        assert ObjPID(k, td_ids[i].oid) == ObjPID(k, td_ids[i+1].oid);
        i := i + 1; 
    }
}

// Lemma: If a TD is read by an active device, and the TD has transfers to 
// objects, then the objects must be in the same partition with the TD
lemma Lemma_SecureActiveTDsState_TransfersInTDsRefsObjsInSamePartitionOnly(
    k:State, k_params:ReachableTDsKParams, tds_state:TDs_Vals, dev_id:Dev_ID, td_id:TD_ID, target_oid:Object_ID
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
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds
    
    requires CanActiveDevReadActiveTD_PreConditions(k_params, tds_state, dev_id, td_id)
    requires k_params == KToKParams(k)


    requires ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state)
        // Requirement: <tds_state> is secure
    requires CanActiveDevReadActiveTD(k_params, tds_state, dev_id, td_id)
        // Requirement: Device (<dev_id>) can read the TD (<td_id>)

    requires target_oid in GetObjIDsRefedInTD(tds_state, td_id) &&
             GetAModesOfObjRefedInTD(tds_state, td_id, target_oid) != {}

    ensures target_oid in AllObjsIDs(k.objects);
    ensures ObjPID(k, td_id.oid) == ObjPID(k, target_oid);
{
    // Dafny can automatically prove this lemma
}