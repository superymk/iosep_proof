include "Utils.dfy"
include "Properties_ValidDMState.dfy"

lemma Lemma_ValidDMStateToState_DMDevsInRedAreActiveInK(ws:DM_State, k:State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)

    ensures forall dev_id :: dev_id in DM_DevsInRed(ws) ==> dev_id in k.subjects.devs && SubjPID_DevID(k, dev_id) != NULL
{
    forall dev_id | dev_id in DM_DevsInRed(ws) 
        ensures dev_id in k.subjects.devs 
        ensures SubjPID_DevID(k, dev_id) != NULL
    {
        assert dev_id.sid in DM_AllSubjsIDs(ws.subjects);
        assert DM_IsDevID(ws.subjects, dev_id);

        assert DM_SubjPID(ws.subjects, dev_id.sid) != NULL;
    }
}

lemma Lemma_DM_DevsInRed_IsSubsetOfAllActiveDevs(ws:DM_State, k:State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)

    ensures DM_DevsInRed(ws) <= AllActiveDevs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DMOwnedObjsEqualsOwnObjIDs(ws:DM_State, k:State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
                ==> OwnObjIDs(k, s_id) == DM_OwnedObjs(ws.subjects, s_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_ObjsOwnedByActiveSubjs_AreActive(ws:DM_State, k:State, s_id:Subject_ID, o_id:Object_ID)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
    requires k == DMStateToState(ws)

    requires s_id in AllSubjsIDs(k.subjects)
    requires s_id in AllActiveSubjs(k)
    requires o_id in DM_OwnedObjs(ws.subjects, s_id)
    
    ensures o_id in AllActiveObjs(k)
{
    assert DoOwnObj(k, s_id, o_id);
    assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
}

lemma Lemma_DM_TDIDsInRed_Prove(ws:DM_State, td_id:TD_ID)
    requires DM_IsValidState_ObjIDs(ws)

    requires td_id in DM_AllTDIDs(ws.objects)

    requires DM_ObjPID(ws.objects, td_id.oid) == ws.red_pid

    ensures td_id in DM_TDIDsInRed(ws)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_TDIDsInGreen_Prove(ws:DM_State, td_id:TD_ID)
    requires DM_IsValidState_ObjIDs(ws)

    requires td_id in DM_AllTDIDs(ws.objects)

    requires DM_ObjPID(ws.objects, td_id.oid) != NULL
    requires DM_ObjPID(ws.objects, td_id.oid) != ws.red_pid

    ensures td_id in DM_TDIDsInGreen(ws)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_AllActiveDevs_IsCombinationOfGreenAndRedDevs(ws:DM_State)
    requires DM_IsValidState_Subjects(ws)

    ensures DM_AllActiveDevs(ws.subjects) == DM_DevsInRed(ws) + DM_DevsInGreen(ws)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevsInRed_Prove(ws:DM_State, dev_id:Dev_ID)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)

    requires dev_id in DM_AllDevIDs(ws.subjects)
    requires DM_SubjPID(ws.subjects, dev_id.sid) == ws.red_pid
    requires ws.red_pid != NULL

    ensures dev_id in DM_DevsInRed(ws)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevsInGreen_Prove(ws:DM_State, dev_id:Dev_ID)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)

    requires dev_id in DM_AllDevIDs(ws.subjects)
    requires DM_SubjPID(ws.subjects, dev_id.sid) != NULL
    requires DM_SubjPID(ws.subjects, dev_id.sid) != ws.red_pid
    requires ws.red_pid != NULL

    ensures dev_id in DM_DevsInGreen(ws)
{
    // Dafny can automatically prove this lemma
}
