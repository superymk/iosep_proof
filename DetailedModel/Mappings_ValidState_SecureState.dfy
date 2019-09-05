include "Properties_SecureDMState.dfy"
include "Lemmas_SecureDMState_DevHWProt.dfy"

lemma Lemma_DMStateToState_SecureK(ws:DM_State, k:State)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires k == DMStateToState(ws)

    ensures IsValidState(k) && IsSecureState(k)
    ensures forall tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k)
                ==> ActiveTDsStateIsSecure(KToKParams(k), AllActiveDevs(k), tds_state2)
{
    // Prove IsValidState(k)
    Lemma_DM_IsValidState_SubjsOwnObjsThenInSamePartition_Property(ws);

    Lemma_SecureDMStateWithDevHWProt_ReachableTDsStateInAGivenSeqIsSecure(ws, k, KToKParams(k));
    Lemma_K_ActiveTDsStateIsSecure_ThenIsValidState_ReachableTDsStatesAndSI1ReturnsTrue(k);
    assert IsValidState_ReachableTDsStates(k);

    assert IsValidState(k);
    assert IsSecureState_SI1(k);

    // Prove IsSecureState(k)
    assert IsSecureState_SI2(k);
}