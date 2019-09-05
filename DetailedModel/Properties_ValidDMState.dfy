include "../Abstract/Properties.dfy"
include "../Abstract/BuildCAS/Utils_BuildCAS.dfy"
include "Utils.dfy"
include "Syntax.dfy"
include "HCodedTD_Ops.dfy"

predicate DM_IsValidState_Subjects(ws:DM_State)
{
    // 1. Subjects
    IsValidState_Subjects(DMStateToState(ws)) &&

    (true)
}

predicate DM_IsValidState_ObjIDs(ws:DM_State)
{
    P_DMObjectsHasUniqueIDs(ws.objects) &&

    (true)
}

predicate DM_IsValidState_Objects(ws:DM_State)
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)
{
    // 2. Objects
    IsValidState_Objects(DMStateToState(ws)) &&

    (true)
}

predicate DM_IsValidState_Partitions(ws:DM_State)
{
    (NULL !in ws.pids) &&

    //// I/O partition of untrusted OS and apps (red partition) is already exist
    (ws.red_pid in ws.pids) &&

    (true)
}

predicate DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws:DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)
{
    IsValidState_SubjsOwnObjsThenInSamePartition(DMStateToState(ws))
}

predicate DM_IsValidState_DevsActivateCond(ws:DM_State)
{
    //// Condition 5.1 Keys and values of <devs_activatecond> must be existing devices
    (forall dev_id :: dev_id in ws.devs_activatecond
        ==> dev_id in MapGetKeys(ws.subjects.devs)) &&
    (forall dev_id :: dev_id in ws.devs_activatecond
        ==> ws.devs_activatecond[dev_id] <= MapGetKeys(ws.subjects.devs)) &&

    //// Condition 5.2 The keys of <devs_activatecond> can only 
    //// be activated into red partition
    (forall dev_id :: dev_id in ws.devs_activatecond
        ==> DM_SubjPID(ws.subjects, dev_id.sid) == NULL ||  DM_SubjPID(ws.subjects, dev_id.sid) == ws.red_pid) &&
    
    //// Condition 5.3 The values of <devs_activatecond> can only be activated
    //// into green partitions; i.e., either inactive or in a green partition
    (forall dev_id, dev_id2 :: dev_id in ws.devs_activatecond &&
            dev_id2 in ws.devs_activatecond[dev_id]
        ==> DM_SubjPID(ws.subjects, dev_id2.sid) != ws.red_pid) &&

    //// Condition 5.5 No common devices between keys and values
    (forall dev_id :: dev_id in ws.devs_activatecond
        ==> ws.devs_activatecond[dev_id] * MapGetKeys(ws.devs_activatecond) == {}) &&

    //// Condition 5.6 If a device is active in red partition, then all mapped 
    //// devices are inactive
    (forall dev_id :: dev_id in ws.devs_activatecond &&
            DM_SubjPID(ws.subjects, dev_id.sid) != NULL
        ==> (forall dev_id2 :: dev_id2 in ws.devs_activatecond[dev_id]
                ==> DM_SubjPID(ws.subjects, dev_id2.sid) == NULL)) &&

    (true)
}

predicate DM_IsValidState_TDsToAllStates(ws:DM_State)
{
    IsValidState_TDsToAllStates(DMStateToState(ws))
}

predicate DM_IsValidState_SubjsObjsPIDs(ws:DM_State)
{
    DM_IsValidState_Subjects(ws) && 
    DM_IsValidState_Partitions(ws) && 
    DM_IsValidState_Objects(ws) && 
    DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws) &&
    DM_IsValidState_TDsToAllStates(ws)
}

predicate DM_IsValidState(ws:DM_State)
{
    DM_IsValidState_SubjsObjsPIDs(ws) && DM_IsValidState_DevsActivateCond(ws)
}




//******** Util Lemmas ********//
lemma Lemma_DM_ObjsInSubjsAreAlsoInState(ws:DM_State)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)

    ensures forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) && DM_DoOwnObj(ws.subjects, s_id, o_id)
                ==> o_id in DM_AllObjsIDs(ws.objects)
{
    Lemma_ObjsInSubjsAreAlsoInState(DMStateToState(ws));
}

lemma Lemma_DM_IsValidState_SubjsOwnObjsThenInSamePartition_Property(ws:DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires P_ObjsInSubjsAreInSetOfAllObjs(ws.subjects, ws.objects)

    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)

    ensures forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) && DM_DoOwnObj(ws.subjects, s_id, o_id)
                ==> o_id in DM_AllObjsIDs(ws.objects) &&
                    DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, o_id)
{
    Lemma_DM_ObjsInSubjsAreAlsoInState(ws);
    forall s_id, o_id | s_id in DM_AllSubjsIDs(ws.subjects) && DM_DoOwnObj(ws.subjects, s_id, o_id)
        ensures o_id in DM_AllObjsIDs(ws.objects)
        ensures DM_SubjPID(ws.subjects, s_id) == DM_ObjPID(ws.objects, o_id)
    {
        var k := DMStateToState(ws);
        assert s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id);
    }
}