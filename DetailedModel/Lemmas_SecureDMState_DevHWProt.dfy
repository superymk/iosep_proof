include "Lemmas_SecureDMState.dfy"
include "Lemmas_DevHWProt.dfy"

predicate P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
{
    (forall td_id :: td_id in tds_state
                ==> td_id in ActiveTDsState(k)) &&
    (forall td_id :: td_id in tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> tds_state[td_id] == ActiveTDsState(k)[td_id])) &&
    ((tds_state == ActiveTDsState(k)) ||
            (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state) &&
             IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state))) &&
    (ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state)) &&
        // Requirement: Proved due to recursion

    (true)
}

// Lemma: In a secure DM state, any reachable active TDs' states is secure
lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(
    ws:DM_State, k:State, k_params:ReachableTDsKParams
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirements from DevDevHWProt
    requires DM_IsSecureState_SI2(ws)
        // Requirements from SecureDMState

    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
{
    forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
        ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), tds_state2)
    {
        var k_tds_state := ActiveTDsState(k);
        Lemma_K_AllReachableActiveTDsStates_Apply(k, tds_state2);
        assert tds_state2 == k_tds_state || IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), k_tds_state, tds_state2);

        if(tds_state2 == k_tds_state)
        {
            var tds_states:seq<TDs_Vals> := [tds_state2];
            var k_devs:seq<Dev_ID> := [];

            assert |tds_states| == 1;
            assert tds_states[|tds_states|-1] == ActiveTDsState(k);
            assert tds_states[|tds_states|-1] == tds_state2;
            Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                ws, k, k_params, tds_states, k_devs, tds_state2);
        }
        else
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), k_tds_state, tds_state2);
            var tds_states, k_devs := Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Apply(
                                        k_params, AllActiveDevs(k), k_tds_state, tds_state2);
            Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                ws, k, k_params, tds_states, k_devs, tds_state2);
        }
    }
}




//******** Corollaries ********//
// Lemma: Any reachable active TDs' state can be reached with devices in red only
lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateCanAlwaysBeReachedWithDevsInRedOnly(
    ws:DM_State, k:State, k_params:ReachableTDsKParams
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirements from DevDevHWProt
    requires DM_IsSecureState_SI2(ws)
        // Requirements from SecureDMState

    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ((tds_state2 == ActiveTDsState(k)) ||
                        (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state2) &&
                         IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state2)))
    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> (forall td_id :: td_id in tds_state2
                        ==> td_id in ActiveTDsState(k) &&
                            (td_id in DM_TDIDsInGreen(ws) ==> tds_state2[td_id] == ActiveTDsState(k)[td_id]))
{
    forall tds_state2 | tds_state2 in AllReachableActiveTDsStates(k)
        ensures ((tds_state2 == ActiveTDsState(k)) ||
                        (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state2) &&
                         IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), tds_state2)))
        ensures (forall td_id :: td_id in tds_state2
                        ==> td_id in ActiveTDsState(k))
        ensures (forall td_id :: td_id in tds_state2
                        ==> (td_id in DM_TDIDsInGreen(ws) ==> tds_state2[td_id] == ActiveTDsState(k)[td_id]))
    {
        var k_tds_state := ActiveTDsState(k);
        Lemma_K_AllReachableActiveTDsStates_Apply(k, tds_state2);
        assert tds_state2 == k_tds_state || IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), k_tds_state, tds_state2);

        if(tds_state2 == k_tds_state)
        {
            var tds_states:seq<TDs_Vals> := [tds_state2];
            var k_devs:seq<Dev_ID> := [];

            assert |tds_states| == 1;
            assert tds_states[|tds_states|-1] == ActiveTDsState(k);
            assert tds_states[|tds_states|-1] == tds_state2;
            Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                ws, k, k_params, tds_states, k_devs, tds_state2);
        }
        else
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, AllActiveDevs(k), k_tds_state, tds_state2);
            var tds_states, k_devs := Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Apply(
                                        k_params, AllActiveDevs(k), k_tds_state, tds_state2);
            Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                ws, k, k_params, tds_states, k_devs, tds_state2);
        }
    }
}



//******** Private Lemmas ********//
lemma Lemma_P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_ProveInRecursion(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, 
    from_tds_state:TDs_Vals, to_tds_state:TDs_Vals, tds_state:TDs_Vals, last_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, tds_state)
    requires from_tds_state == to_tds_state
    requires from_tds_state == tds_state
    requires to_tds_state == last_tds_state

    ensures P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, last_tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_TwoOrMoreElems_IsActiveTDsStateReachActiveTDsStateInOneStep_Equal(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, k_dev:Dev_ID,
    from_tds_state:TDs_Vals, to_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params, k_dev, from_tds_state, to_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, from_tds_state, to_tds_state)
    requires from_tds_state == ActiveTDsState(k)

    ensures IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, ActiveTDsState(k), to_tds_state)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_ProveRecursionPreCondition(
    k_params:ReachableTDsKParams, k_active_tds:set<TD_ID>, k_active_devs:set<Dev_ID>, k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>, tds_states':seq<TDs_Vals>, k_devs':seq<Dev_ID>
)
    requires P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                k_params, k_active_tds, k_active_devs, k_tds_state, tds_states, k_devs)
    requires |tds_states| >= 2

    requires tds_states' == tds_states[..|tds_states|-1];
    requires k_devs' == k_devs[..|k_devs|-1];

    ensures P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                k_params, k_active_tds, k_active_devs, k_tds_state, tds_states', k_devs')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_OneElem(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>, last_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirements from DevDevHWProt
    requires DM_IsSecureState_SI2(ws)
    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
        // Requirements from SecureDMState

    requires (|tds_states| == 1 && tds_states[|tds_states|-1] == ActiveTDsState(k)) 
        // Requirement: |tds_states| == 1
    requires tds_states[0] == ActiveTDsState(k)  
        // First TDs' state is the <ActiveTDsState(k')>
    requires tds_states[|tds_states|-1] == last_tds_state
        // Requirement: Last TDs' state is <last_tds_state>

    requires DM_AllActiveDevs(ws.subjects) == DM_DevsInRed(ws) + DM_DevsInGreen(ws)
    requires DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k)
        // Requirement: Properties better to be proved in the caller

    ensures forall td_id :: td_id in last_tds_state
                ==> td_id in ActiveTDsState(k)
        // Property needed by the properties below
    ensures forall td_id :: td_id in last_tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> last_tds_state[td_id] == ActiveTDsState(k)[td_id])
        // Property: Green TDs (Active wimp TDs) are never changed
    ensures (last_tds_state == ActiveTDsState(k)) ||
            (IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), ActiveTDsState(k), last_tds_state) &&
             IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), last_tds_state))
        // Property: ActiveTDsState(k) -->* last_tds_state by red devices
    ensures ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), last_tds_state)
        // Property: The reachable TDs' state is secure
{
    assert last_tds_state == tds_states[0];

    Lemma_K_ActiveTDsStateIsSecure_Property_MergeOfTwo_ProveAllPreConditions(
        k, k_params, DM_DevsInRed(ws), DM_DevsInGreen(ws), last_tds_state);

    // Prove ActiveTDsStateIsSecure(k_params, DM_DevsInRed(ws), last_tds_state)
    Lemma_DevHWProt_GoodDM_TDsReadByRedDevs_ThenDoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartitionIsFalse(ws);
    assert P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(ws);

    Lemma_P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Apply(ws, k, k_params, last_tds_state);
    assert ActiveTDsStateIsSecure(k_params, DM_DevsInRed(ws), last_tds_state);

    // Prove ActiveTDsStateIsSecure(k_params, DM_DevsInGreen(ws), last_tds_state)
    Lemma_SecureDMState_ActiveTDsReadByWimpDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(ws, k, last_tds_state);
    assert ActiveTDsStateIsSecure(k_params, DM_DevsInGreen(ws), last_tds_state);

    Lemma_K_ActiveTDsStateIsSecure_Property_MergeOfTwo(k, k_params, DM_DevsInRed(ws), DM_DevsInGreen(ws), last_tds_state);
    assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), last_tds_state);
}

lemma Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_WrapperIsActiveTDsStateReachActiveTDsStateInChain(
    ws:DM_State, k:State, k_params:ReachableTDsKParams, k_tds_state:TDs_Vals,
    to_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(ws)

    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)
    requires k_tds_state == ActiveTDsState_SlimState(k.objects.tds)

    requires IsActiveTDsStateReachActiveTDsStateInChain_PreConditions(k_params, DM_DevsInRed(ws), k_tds_state, to_tds_state)
    requires IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), k_tds_state, to_tds_state)

    ensures forall td_id :: td_id in to_tds_state
                ==> td_id in ActiveTDsState(k)
        // Property needed by the following property
    ensures (forall td_id :: td_id in to_tds_state
                ==> (td_id in DM_TDIDsInGreen(ws) ==> to_tds_state[td_id] == ActiveTDsState(k)[td_id]))
{
    // Prove property 1
    assert TDsStateGetTDIDs(to_tds_state) == AllActiveTDs(k);
    Lemma_K_ActiveTDsState_AllActiveTDs(k, to_tds_state);

    // Prove property 2
    var k_tds_state := ActiveTDsState(k);
    var red_tds_states, red_devs := Lemma_K_IsActiveTDsStateReachActiveTDsStateInChain_Apply(
                                        k_params, DM_DevsInRed(ws), ActiveTDsState(k), to_tds_state);
    
    Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs(
        ws, k, k_params, k_tds_state, red_tds_states, red_devs);

    assert P_DevHWProt_GreenTDsAreUnmodifiedByRedDevs(k, red_tds_states, ws.red_pid);

    forall td_id | td_id in to_tds_state
        ensures td_id in DM_TDIDsInGreen(ws) ==> to_tds_state[td_id] == ActiveTDsState(k)[td_id]
    {
        assert to_tds_state in red_tds_states;
        assert td_id in TDsStateGetTDIDs(to_tds_state);

        if(td_id in DM_TDIDsInGreen(ws))
        {
            assert ObjPID(k, td_id.oid) == DM_ObjPID(ws.objects, td_id.oid);
            assert ObjPID(k, td_id.oid) != ws.red_pid;

            assert to_tds_state[td_id] == ActiveTDsState(k)[td_id];
        }
    }
}

lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_TwoOrMoreElems(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>, last_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirements from DevDevHWProt
    requires DM_IsSecureState_SI2(ws)
    requires DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
        // Requirements from SecureDMState

    requires (|tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)) &&
                |k_devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in AllActiveDevs(k)) &&
                tds_states[0] == ActiveTDsState(k) && // first TDs' state is the <ActiveTDsState(k')>
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            k_devs[i], tds_states[i], tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            k_devs[i], tds_states[i], tds_states[i+1])))
                    // ActiveTDsState(k') -->1+ tds_states[|tds_states| - 1]
        // Requirement: ActiveTDsState(k') -->* tds_states[|tds_states| - 1]
    requires tds_states[0] == ActiveTDsState(k)  
        // First TDs' state is the <ActiveTDsState(k')>
    requires tds_states[|tds_states|-1] == last_tds_state
        // Requirement: Last TDs' state is <last_tds_state>

    requires DM_AllActiveDevs(ws.subjects) == DM_DevsInRed(ws) + DM_DevsInGreen(ws)
    requires DM_AllActiveDevs(ws.subjects) == AllActiveDevs(k)
        // Requirement: Properties better to be proved in the caller

    requires P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, tds_states[|tds_states|-2])

    ensures P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, last_tds_state)
{
    var k_dev := k_devs[|k_devs|-1];
    var from_tds_state := tds_states[|tds_states|-2];
    var to_tds_state := last_tds_state;

    // Prove property 1
    assert TDsStateGetTDIDs(last_tds_state) == AllActiveTDs(k);
    Lemma_K_ActiveTDsState_AllActiveTDs(k, last_tds_state);

    // Prove other properties
    Lemma_K_ActiveTDsStateIsSecure_Property_MergeOfTwo_ProveAllPreConditions(
        k, k_params, DM_DevsInRed(ws), DM_DevsInGreen(ws), last_tds_state);

    if(k_dev in DM_DevsInGreen(ws))
    {
        Lemma_SecureDMState_GreenDevsDoNotModifyAnyTDs(ws, k, from_tds_state, to_tds_state, k_dev);
        assert from_tds_state == to_tds_state;

        assert from_tds_state == tds_states[|tds_states|-2];
        assert to_tds_state == last_tds_state;
        assert P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, tds_states[|tds_states|-2]);

        Lemma_P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_ProveInRecursion(
            ws, k, k_params, from_tds_state, to_tds_state, tds_states[|tds_states|-2], last_tds_state);
        assert P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, last_tds_state);
    }
    else
    {
        assert k_dev in DM_DevsInRed(ws);

        // Prove property 3
        assert DM_DevsInRed(ws) <= AllActiveDevs(k);

        Lemma_K_IsValidState_HCodedTDsOnlyRefObjsInOwnerDevs(k);
        
        assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, from_tds_state, to_tds_state);

        if(tds_states[|tds_states|-2] == ActiveTDsState(k))
        {
            assert from_tds_state == ActiveTDsState(k);
            Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_TwoOrMoreElems_IsActiveTDsStateReachActiveTDsStateInOneStep_Equal(
                ws, k, k_params, k_dev, from_tds_state, to_tds_state);
            assert IsActiveTDsStateReachActiveTDsStateInOneStep(k_params, k_dev, ActiveTDsState(k), to_tds_state);
            Lemma_TDsStateReachedInOneStepAlsoReachedInChain(k_params, k_dev, DM_DevsInRed(ws), ActiveTDsState(k), to_tds_state);
            assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), to_tds_state);
        }
        else
        {
            assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), from_tds_state);
            Lemma_TDsStateAReachTDsStateBInChainAndBReachTDsStateCInOneStep_ThenAReachesCInChain(
                k_params, k_dev, DM_DevsInRed(ws), ActiveTDsState(k), from_tds_state, to_tds_state);
        }
        assert IsActiveTDsStateReachActiveTDsStateInChain(k_params, DM_DevsInRed(ws), ActiveTDsState(k), to_tds_state);

        // Prove property 2
        Lemma_DevHWProt_GoodDM_TDsReadByRedDevs_ThenDoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartitionIsFalse(ws);
        assert P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(ws);

        Lemma_DevHWProt_GoodDM_GreenTDsAreUnmodifiedInClosureByRedDevs_WrapperIsActiveTDsStateReachActiveTDsStateInChain(
            ws, k, k_params, ActiveTDsState(k), to_tds_state);

        // Prove property 4
        //// Prove ActiveTDsStateIsSecure(k_params, DM_DevsInRed(ws), last_tds_state)
        Lemma_P_DevHWProt_TDsReadByRedDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime_Apply(ws, k, k_params, last_tds_state);
        assert ActiveTDsStateIsSecure(k_params, DM_DevsInRed(ws), last_tds_state);

        //// Prove ActiveTDsStateIsSecure(k_params, DM_DevsInGreen(ws), last_tds_state)
        Lemma_SecureDMState_ActiveTDsReadByWimpDevsOnlyHaveValidAndSecureTransfersToObjsAtAnyTime(ws, k, last_tds_state);
        assert ActiveTDsStateIsSecure(k_params, DM_DevsInGreen(ws), last_tds_state);

        Lemma_K_ActiveTDsStateIsSecure_Property_MergeOfTwo(k, k_params, DM_DevsInRed(ws), DM_DevsInGreen(ws), last_tds_state);
        assert ActiveTDsStateIsSecure(k_params, AllActiveDevs(k), last_tds_state);
    }
}

predicate P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
    k_params:ReachableTDsKParams, k_active_tds:set<TD_ID>, k_active_devs:set<Dev_ID>, k_tds_state:TDs_Vals,
    tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>
)
{
    (|tds_states| == 1 && tds_states[|tds_states|-1] == k_tds_state) ||
                    // tds_states == [k_tds_state], Or
             (|tds_states| >= 2 && 
                (forall tds_state2 :: tds_state2 in tds_states 
                    ==> TDsStateGetTDIDs(tds_state2) == k_active_tds) &&
                |k_devs| == |tds_states| - 1 && (forall dev_id2 :: dev_id2 in k_devs ==> dev_id2 in k_active_devs) &&
                tds_states[0] == k_tds_state && // first TDs' state is the <k_tds_state>
                (forall i :: 0<=i<|tds_states| - 1 
                    ==> IsActiveTDsStateReachActiveTDsStateInOneStep_PreConditions(k_params,
                            k_devs[i], tds_states[i], tds_states[i+1]) &&
                        IsActiveTDsStateReachActiveTDsStateInOneStep(k_params,
                            k_devs[i], tds_states[i], tds_states[i+1])))
            // k_tds_state -->1+ tds_states[|tds_states| - 1]
        // Requirement: k_tds_state -->* tds_states[|tds_states| - 1]
}

lemma Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
    ws:DM_State, k:State, k_params:ReachableTDsKParams,
    tds_states:seq<TDs_Vals>, k_devs:seq<Dev_ID>, last_tds_state:TDs_Vals
)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)
    requires k_params == KToKParams(k)

    requires P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws)
        // Requirements from DevDevHWProt
    requires DM_IsSecureState_SI2(ws)
        // Requirements from SecureDMState

    requires P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
                k_params, AllActiveTDs(k), AllActiveDevs(k), ActiveTDsState(k), tds_states, k_devs)
        // Requirement: ActiveTDsState(k) -->* tds_states[|tds_states| - 1]
    requires tds_states[0] == ActiveTDsState(k)  
        // First TDs' state is the <ActiveTDsState(k')>
    requires tds_states[|tds_states|-1] == last_tds_state
        // Requirement: Last TDs' state is <last_tds_state>

    ensures P_Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, k_params, last_tds_state)

    decreases |tds_states|
{
    // Prove DM_TDIDsInGreen(ws) <= AllActiveTDs(k)
    assert DM_TDIDsInGreen(ws) <= AllActiveTDs(k);

    // Prove properties
    Lemma_DM_AllActiveDevs_IsCombinationOfGreenAndRedDevs(ws);
    if(|tds_states| == 1)
    {
        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_OneElem(
            ws, k, k_params, tds_states, k_devs, last_tds_state);
    }
    else
    {
        assert |tds_states| >= 2;

        var tds_states' := tds_states[..|tds_states|-1];
        var k_devs' := k_devs[..|k_devs|-1];
        var last_tds_state' := tds_states'[|tds_states'|-1];

        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_ProveRecursionPreCondition(
            k_params, AllActiveTDs(k), AllActiveDevs(k), ActiveTDsState(k), tds_states, k_devs, tds_states', k_devs');
        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_Inner(
            ws, k, k_params, tds_states', k_devs', last_tds_state');

        Lemma_SequenceHighlightLastElemOfSubSeq(tds_states, tds_states');
        assert tds_states[|tds_states|-2] == tds_states'[|tds_states'|-1];
        Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure_TwoOrMoreElems(
            ws, k, k_params, tds_states, k_devs, last_tds_state);
    }
}