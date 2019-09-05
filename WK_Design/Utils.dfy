include "../DetailedModel/Model.dfy"
include "DM_AdditionalPropertiesLemmas.dfy"

lemma Lemma_SeqSameIndexYieldSameElem<T>(s:seq<T>, a:int, b:int)
    requires a == b
    requires 0<a<|s|
    
    ensures s[a] == s[b]
{
    // Dafny can automatically prove this lemma
}




//******** Sub-Operations ********//
// (needs 30s to verify)
method WS_WimpDrvActivate_Multi(
    ws:DM_State,
    drv_ids:seq<Drv_ID>, // ID of the drivers to be deactivated
    pid:Partition_ID // ID of the target partition
) returns (ghost t:DM_Trace, ghost t_detailed:DM_Trace_Detailed, last_ws:DM_State, d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires pid != NULL
    requires pid != ws.red_pid

    requires forall i, j :: 0 <= i < |drv_ids| && 0 <= j < |drv_ids|
                ==> (i == j <==> drv_ids[i] == drv_ids[j])
        // Requirement: No duplicate device ID in <drv_ids>
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs

    ensures d ==> t.ws0 == ws
    ensures d ==> |t.ops| == |drv_ids|
    ensures d ==> (forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DrvActivateToGreenPartitionOp(drv_ids[i].sid, pid))
    ensures d ==> t.ops == WimpDrvActivateMulti_ToTraceOps(drv_ids, pid)
        // Property 3
    ensures d ==> DM_IsValidTrace(t)
                
    ensures d ==> last_ws == SeqLastElem(DM_CalcNewStates(t))
        // Property 5: <last_ws> is the last state of the trace <t>

    ensures d ==> ConvertTraceToDetailedTrace(t) == (t_detailed, true)
    ensures d ==> DM_DetailedTrace_IsValidTrace(t_detailed)
        // Property 7
    ensures d ==> (forall i :: 0 <= i < |t_detailed.ops|
                    ==> DM_IsSecureOps(t_detailed.states[i], t_detailed.states[i+1]))
    ensures d ==> (last_ws == SeqLastElem(t_detailed.states))
    ensures d ==> DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)
        // Properties from DM_IsSecureOps

    ensures d ==> P_WS_DrvActivate_Multi_ObjModifications(ws, last_ws, SeqToSet(drv_ids), pid)
        // Properties of drivers activation
        // Property 11

    decreases |drv_ids|
{
    if(|drv_ids| == 0)
    {
        return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, true;
    }
    else
    {
        var dev_id := drv_ids[0];
        var ws', ws_d := DM_DrvActivateToGreenPartition(ws, dev_id.sid, pid);
        if(!ws_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}

        assert forall id :: id in drv_ids[1..] ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid);
        var next_t, detailed_next_t, next_last_ws, next_d := WS_WimpDrvActivate_Multi(ws', drv_ids[1..], pid); 
        if(!next_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}
        else
        {
            var op := DM_DrvActivateToGreenPartitionOp(dev_id.sid, pid);

            t := DM_Trace(ws, [op] + next_t.ops);
            last_ws := next_last_ws;
            d := true;

            // Prove property 3
            Lemma_WS_DrvActivate_Multi_Private(next_t, drv_ids[1..], op, t, drv_ids, pid);

            // Prove property 4
            ghost var result := ConvertTraceToDetailedTrace(next_t);
            assert detailed_next_t == result.0;
            ghost var status := result.1;

            assert status == true;

            t_detailed := DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);

            assert DM_CalcNewState(ws, op) == (ws', ws_d);
            Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(detailed_next_t, ws, op, t_detailed);
            assert DM_DetailedTrace_IsValidTrace(t_detailed);

            assert t == ConvertDetailedTraceToTrace(t_detailed);
            assert DM_IsValidTrace(t);

            // Prove property 5
            assert DM_CalcNewStates(t) == t_detailed.states;
            Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst(t_detailed.states, detailed_next_t.states, ws);
            assert SeqLastElem(t_detailed.states) == SeqLastElem(detailed_next_t.states);

            // Prove property 7
            assert DM_IsSecureOps(ws, ws');

            // Prove property 11
            Lemma_WS_DrvActivate_Multi_ProveProperty11(
                ws, ws', last_ws, drv_ids, pid);
        }
    }
}

predicate P_WS_DrvDevDeactivate_Multi_ObjModifications(
    ws:DM_State, ws':DM_State,
    s_ids:set<Subject_ID>
)
    requires forall id :: id in s_ids ==> DM_IsSubjID(ws.subjects, id)

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
{
    // Unchanged state vars
    ws'.pids == ws.pids &&
    ws'.tds_to_all_states == ws.tds_to_all_states &&
    ws'.red_pid == ws.red_pid &&
    ws'.devs_activatecond == ws.devs_activatecond &&
    
    MapGetKeys(ws'.subjects.drvs) == MapGetKeys(ws.subjects.drvs) &&
    MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs) &&
    MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds) &&
    MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds) &&
    MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos) &&
    
    (forall drv_id :: drv_id in ws'.subjects.drvs
        ==> (ws'.subjects.drvs[drv_id].td_ids == ws.subjects.drvs[drv_id].td_ids &&
            ws'.subjects.drvs[drv_id].fd_ids == ws.subjects.drvs[drv_id].fd_ids &&
            ws'.subjects.drvs[drv_id].do_ids == ws.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in ws'.subjects.devs
        ==> (ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
            ws'.subjects.devs[dev_id].td_ids == ws.subjects.devs[dev_id].td_ids &&
            ws'.subjects.devs[dev_id].fd_ids == ws.subjects.devs[dev_id].fd_ids &&
            ws'.subjects.devs[dev_id].do_ids == ws.subjects.devs[dev_id].do_ids)) &&

    // Objects to be deactivated are correctly modified
    (forall id :: id in WS_TDsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.tds[id].pid == NULL &&
            DM_IsSameTDVal(ws'.objects, ws.objects, id)) &&
    (forall id :: id in WS_FDsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.fds[id].pid == NULL &&
            DM_IsSameFDVal(ws'.objects, ws.objects, id)) &&
    (forall id :: id in WS_DOsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.dos[id].pid == NULL &&
            DM_IsSameDOVal(ws'.objects, ws.objects, id)) &&  
    
    // Objects not to be deactivated are unchanged
    (forall id :: id in ws.objects.tds &&
            id !in WS_TDsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in ws.objects.fds &&
            id !in WS_FDsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in ws.objects.dos &&
            id !in WS_DOsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameDO(ws'.objects, ws.objects, id)) &&

    (true)
}

// (needs 30s to verify)
method WS_WimpDrvDeactivate_Multi(
    ws:DM_State,
    drv_ids:seq<Drv_ID> // ID of the drivers to be deactivated
) returns (ghost t:DM_Trace, ghost t_detailed:DM_Trace_Detailed, last_ws:DM_State, d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |drv_ids| && 0 <= j < |drv_ids|
                ==> (i == j <==> drv_ids[i] == drv_ids[j])
        // Requirement: No duplicate device ID in <drv_ids>
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs
    requires forall id :: id in drv_ids
                ==> DM_SubjPID(ws.subjects, id.sid) != NULL &&
                    DM_SubjPID(ws.subjects, id.sid) != ws.red_pid

    ensures d ==> t.ws0 == ws
    ensures d ==> |t.ops| == |drv_ids|
    ensures d ==> (forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_GreenDrvDeactivateOp(drv_ids[i].sid))
    ensures d ==> t.ops == WimpDrvDeactivateMulti_ToTraceOps(drv_ids)
        // Property 3
    ensures d ==> DM_IsValidTrace(t)
                
    ensures d ==> last_ws == SeqLastElem(DM_CalcNewStates(t))
        // Property 5: <last_ws> is the last state of the trace <t>

    ensures d ==> ConvertTraceToDetailedTrace(t) == (t_detailed, true)
    ensures d ==> DM_DetailedTrace_IsValidTrace(t_detailed)
        // Property 7
    ensures d ==> (forall i :: 0 <= i < |t_detailed.ops|
                    ==> DM_IsSecureOps(t_detailed.states[i], t_detailed.states[i+1]))
    ensures d ==> (last_ws == SeqLastElem(t_detailed.states))
    ensures d ==> DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)
        // Properties from DM_IsSecureOps
    ensures d ==> (forall id :: id in ws.subjects.devs 
                    ==> DM_IsSubjID(last_ws.subjects, id.sid) &&
                        DM_SubjPID(ws.subjects, id.sid) == DM_SubjPID(last_ws.subjects, id.sid))
        // Property 11: 
        
    ensures d ==> P_WS_DrvDevDeactivate_Multi_ObjModifications(ws, last_ws, DrvIDsToSubjIDs(SeqToSet(drv_ids)))
        // Properties of drivers activation
        // Property 12

    decreases |drv_ids|
{
    if(|drv_ids| == 0)
    {
        t := DM_Trace(ws, []);
        t_detailed := DM_Trace_Detailed([ws], []);
        last_ws := ws; 
        d := true;

        forall id | id in ws.subjects.devs
            ensures DM_IsSubjID(last_ws.subjects, id.sid)
            ensures DM_SubjPID(ws.subjects, id.sid) == DM_SubjPID(last_ws.subjects, id.sid)
        {
            assert DM_IsSubjID(ws.subjects, id.sid);
        }
    }
    else
    {
        var dev_id := drv_ids[0];
        var ws', ws_d := DM_GreenDrvDeactivate(ws, dev_id.sid);
        if(!ws_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}

        // Prove property 11
        forall id | id in ws.subjects.devs
            ensures DM_IsSubjID(ws'.subjects, id.sid)
            ensures DM_SubjPID(ws.subjects, id.sid) == DM_SubjPID(ws'.subjects, id.sid)
        {
            assert DM_IsSubjID(ws.subjects, id.sid);
        }

        assert forall id :: id in drv_ids[1..] ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid);
        var next_t, detailed_next_t, next_last_ws, next_d := WS_WimpDrvDeactivate_Multi(ws', drv_ids[1..]); 
        if(!next_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}
        else
        {
            var op := DM_GreenDrvDeactivateOp(dev_id.sid);

            t := DM_Trace(ws, [op] + next_t.ops);
            last_ws := next_last_ws;
            d := true;

            // Prove property 3
            Lemma_WS_DrvDeactivate_Multi_Private(next_t, drv_ids[1..], op, t, drv_ids);

            // Prove property 4
            ghost var result := ConvertTraceToDetailedTrace(next_t);
            assert detailed_next_t == result.0;
            ghost var status := result.1;

            assert status == true;

            t_detailed := DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);

            assert DM_CalcNewState(ws, op) == (ws', ws_d);
            Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(detailed_next_t, ws, op, t_detailed);
            assert DM_DetailedTrace_IsValidTrace(t_detailed);

            assert t == ConvertDetailedTraceToTrace(t_detailed);
            assert DM_IsValidTrace(t);

            // Prove property 5
            assert DM_CalcNewStates(t) == t_detailed.states;
            Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst(t_detailed.states, detailed_next_t.states, ws);
            assert SeqLastElem(t_detailed.states) == SeqLastElem(detailed_next_t.states);

            // Prove property 7
            assert DM_IsSecureOps(ws, ws');
            
            // Prove property 12
            Lemma_WS_DrvDeactivate_Multi_ProveProperty12(ws, ws', last_ws, drv_ids);
        }
    }
}

method WS_DevActivate_Multi(
    ws:DM_State,
    dev_ids:seq<Dev_ID>, // ID of the devices to be deactivated
    pid:Partition_ID // ID of the target partition
) returns (ghost t:DM_Trace, ghost t_detailed:DM_Trace_Detailed, last_ws:DM_State, d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires pid != NULL

    requires forall i, j :: 0 <= i < |dev_ids| && 0 <= j < |dev_ids|
                ==> (i == j <==> dev_ids[i] == dev_ids[j])
        // Requirement: No duplicate device ID in <dev_ids>
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    ensures d ==> t.ws0 == ws
    ensures d ==> |t.ops| == |dev_ids|
    ensures d ==> (forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DevActivateOp(dev_ids[i].sid, pid))
    ensures d ==> t.ops == DevActivateMulti_ToTraceOps(dev_ids, pid)
        // Property 3
    ensures d ==> DM_IsValidTrace(t)
                
    ensures d ==> last_ws == SeqLastElem(DM_CalcNewStates(t))
        // Property 5: <last_ws> is the last state of the trace <t>

    ensures d ==> ConvertTraceToDetailedTrace(t) == (t_detailed, true)
    ensures d ==> DM_DetailedTrace_IsValidTrace(t_detailed) 
        // Property 7
    ensures d ==> (forall i :: 0 <= i < |t_detailed.ops|
                    ==> DM_IsSecureOps(t_detailed.states[i], t_detailed.states[i+1]))
    ensures d ==> (last_ws == SeqLastElem(t_detailed.states))
    ensures d ==> DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)
        // Properties from DM_IsSecureOps

    ensures d ==> P_WS_DevActivate_Multi_ObjModifications(ws, last_ws, SeqToSet(dev_ids), pid)
        // Properties of devices activation
        // Property 11

    decreases |dev_ids|
{
    if(|dev_ids| == 0)
    {
        return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, true;
    }
    else
    {
        var dev_id := dev_ids[0];
        var ws', ws_d := DM_DevActivate(ws, dev_id.sid, pid);
        if(!ws_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}

        assert forall id :: id in dev_ids[1..] ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid);
        var next_t, detailed_next_t, next_last_ws, next_d := WS_DevActivate_Multi(ws', dev_ids[1..], pid); 
        if(!next_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}
        else
        {
            var op := DM_DevActivateOp(dev_id.sid, pid);

            t := DM_Trace(ws, [op] + next_t.ops);
            last_ws := next_last_ws;
            d := true;

            // Prove property 3
            Lemma_WS_DevActivate_Multi_Private(next_t, dev_ids[1..], op, t, dev_ids, pid);

            // Prove property 4
            ghost var result := ConvertTraceToDetailedTrace(next_t);
            assert detailed_next_t == result.0;
            ghost var status := result.1;

            assert status == true;

            t_detailed := DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);

            assert DM_CalcNewState(ws, op) == (ws', ws_d);
            Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(detailed_next_t, ws, op, t_detailed);
            assert DM_DetailedTrace_IsValidTrace(t_detailed);

            assert t == ConvertDetailedTraceToTrace(t_detailed);
            assert DM_IsValidTrace(t);

            // Prove property 5
            assert DM_CalcNewStates(t) == t_detailed.states;
            Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst(t_detailed.states, detailed_next_t.states, ws);
            assert SeqLastElem(t_detailed.states) == SeqLastElem(detailed_next_t.states);
            assert t_detailed.states[|t_detailed.states|-1] == SeqLastElem(DM_CalcNewStates(t));

            // Prove property 7
            assert DM_IsSecureOps(ws, ws');
            
            // Prove property 11
            Lemma_WS_DevActivate_Multi_ProveProperty11(
                ws, ws', last_ws, dev_ids, pid);
        }
    }
}

method WS_DevDeactivate_FromGreen_Multi(
    ws:DM_State,
    dev_ids:seq<Dev_ID> // ID of the devices to be deactivated
) returns (ghost t:DM_Trace, ghost t_detailed:DM_Trace_Detailed, last_ws:DM_State, d:bool)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires forall i, j :: 0 <= i < |dev_ids| && 0 <= j < |dev_ids|
                ==> (i == j <==> dev_ids[i] == dev_ids[j])
        // Requirement: No duplicate device ID in <dev_ids>
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    requires forall id :: id in dev_ids 
                ==> DM_SubjPID(ws.subjects, id.sid) != NULL && 
                    DM_SubjPID(ws.subjects, id.sid) != ws.red_pid

    ensures d ==> t.ws0 == ws
    ensures d ==> |t.ops| == |dev_ids|
    ensures d ==> (forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DevDeactivateOp(dev_ids[i].sid))
    ensures d ==> t.ops == GreenDevDeactivateMulti_ToTraceOps(dev_ids)
        // Property 3
    ensures d ==> DM_IsValidTrace(t)
                
    ensures d ==> last_ws == SeqLastElem(DM_CalcNewStates(t))
        // Property 5: <last_ws> is the last state of the trace <t>

    ensures d ==> ConvertTraceToDetailedTrace(t) == (t_detailed, true)
    ensures d ==> DM_DetailedTrace_IsValidTrace(t_detailed)
    ensures d ==> (forall i :: 0 <= i < |t_detailed.ops|
                    ==> DM_IsSecureOps(t_detailed.states[i], t_detailed.states[i+1]))
    ensures d ==> (last_ws == SeqLastElem(t_detailed.states))
        // Property 9
    ensures d ==> DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)
        // Properties from DM_IsSecureOps

    ensures d ==> P_WS_DrvDevDeactivate_Multi_ObjModifications(ws, last_ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
        // Properties of drivers activation
        // Property 12

    decreases |dev_ids|
{
    if(|dev_ids| == 0)
    {
        return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, true;
    }
    else
    {
        var dev_id := dev_ids[0];
        var ws', ws_d := DM_DevDeactivate(ws, dev_id.sid);
        if(!ws_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}

        var next_dev_ids := dev_ids[1..];
        assert forall id :: id in next_dev_ids ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid);

        var next_t, detailed_next_t, next_last_ws, next_d := WS_DevDeactivate_FromGreen_Multi(ws', next_dev_ids);
        if(!next_d)
        { return DM_Trace(ws, []), DM_Trace_Detailed([ws], []), ws, false;}
        else
        {
            var op := DM_DevDeactivateOp(dev_id.sid);

            t := DM_Trace(ws, [op] + next_t.ops);
            last_ws := next_last_ws;
            d := true;

            // Prove property 3
            assert |next_t.ops| == |next_dev_ids|;
            assert |t.ops| == |next_t.ops| + 1;
            assert |dev_ids| == |next_dev_ids| + 1;
            Lemma_WS_DevDeactivate_Multi_Private(next_t, next_dev_ids, op, t, dev_ids);

            // Prove property 4
            ghost var result := ConvertTraceToDetailedTrace(next_t);
            assert detailed_next_t == result.0;
            ghost var status := result.1;

            assert status == true;

            t_detailed := DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops);

            assert DM_CalcNewState(ws, op) == (ws', ws_d);
            Lemma_ValidDetailedTraceInsertValidStateAndChainedAtFirst(detailed_next_t, ws, op, t_detailed);
            assert DM_DetailedTrace_IsValidTrace(t_detailed);

            Lemma_WS_DevDeactivate_FromGreen_Multi_Private(ws, op, next_t, detailed_next_t, t, t_detailed);
            assert t == ConvertDetailedTraceToTrace(t_detailed);
            assert DM_IsValidTrace(t);

            // Prove property 5
            assert DM_CalcNewStates(t) == t_detailed.states;
            Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst(t_detailed.states, detailed_next_t.states, ws);
            assert SeqLastElem(t_detailed.states) == SeqLastElem(detailed_next_t.states);
            
            // Prove property 7
            assert DM_IsSecureOps(ws, ws');

            // Prove property 9
            Lemma_WS_DevDeactivate_FromRed_Multi_ProveProperty9(t, t_detailed, last_ws);
            assert d == true;
            assert last_ws == SeqLastElem(t_detailed.states);

            // Prove property 12
            Lemma_WS_DevDeactivate_FromGreen_ProveProperty11(ws, ws', last_ws, dev_ids);
        }
    }
}

function method WimpDrvActivateMulti_ToTraceOps(drv_ids:seq<Drv_ID>, pid:Partition_ID) : (t:seq<DM_Op>)
    ensures |t| == |drv_ids|
    ensures forall i :: 0 <= i < |t| ==> t[i] == DM_DrvActivateToGreenPartitionOp(drv_ids[i].sid, pid)
{
    if(|drv_ids| == 0) then
        []
    else
        [DM_DrvActivateToGreenPartitionOp(drv_ids[0].sid, pid)] + WimpDrvActivateMulti_ToTraceOps(drv_ids[1..], pid)
}

function method WimpDrvDeactivateMulti_ToTraceOps(drv_ids:seq<Drv_ID>) : (t:seq<DM_Op>)
    ensures |t| == |drv_ids|
    ensures forall i :: 0 <= i < |t| ==> t[i] == DM_GreenDrvDeactivateOp(drv_ids[i].sid)
{
    if(|drv_ids| == 0) then
        []
    else
        [DM_GreenDrvDeactivateOp(drv_ids[0].sid)] + WimpDrvDeactivateMulti_ToTraceOps(drv_ids[1..])
}

function method DevActivateMulti_ToTraceOps(dev_ids:seq<Dev_ID>, pid:Partition_ID) : (t:seq<DM_Op>)
    ensures |t| == |dev_ids|
    ensures forall i :: 0 <= i < |t| ==> t[i] == DM_DevActivateOp(dev_ids[i].sid, pid)
{
    if(|dev_ids| == 0) then
        []
    else
        [DM_DevActivateOp(dev_ids[0].sid, pid)] + DevActivateMulti_ToTraceOps(dev_ids[1..], pid)
}

function method GreenDevDeactivateMulti_ToTraceOps(dev_ids:seq<Dev_ID>) : (t:seq<DM_Op>)
    ensures |t| == |dev_ids|
    ensures forall i :: 0 <= i < |t| ==> t[i] == DM_DevDeactivateOp(dev_ids[i].sid)
{
    if(|dev_ids| == 0) then
        []
    else
        [DM_DevDeactivateOp(dev_ids[0].sid)] + GreenDevDeactivateMulti_ToTraceOps(dev_ids[1..])
}




//******** Activate Multiple Subjects/Objects ********//
function method WS_TDsOwnedBySubjs(ws:DM_State, s_ids:set<Subject_ID>) : (result:set<TD_ID>)
    requires forall id :: id in s_ids ==> DM_IsSubjID(ws.subjects, id)

    ensures forall id :: id in result
                ==> (exists s_id :: s_id in s_ids && DM_DoOwnObj(ws.subjects, s_id, id.oid))
    ensures forall s_id, id :: s_id in s_ids && id in ws.objects.tds &&
                    DM_DoOwnObj(ws.subjects, s_id, id.oid)
                ==> id in result
{
    set s_id, id | s_id in s_ids && id in ws.objects.tds && DM_DoOwnObj(ws.subjects, s_id, id.oid) :: id
}

function method WS_FDsOwnedBySubjs(ws:DM_State, s_ids:set<Subject_ID>) : (result:set<FD_ID>)
    requires forall id :: id in s_ids ==> DM_IsSubjID(ws.subjects, id)

    ensures forall id :: id in result
                ==> (exists s_id :: s_id in s_ids && DM_DoOwnObj(ws.subjects, s_id, id.oid))
    ensures forall s_id, id :: s_id in s_ids && id in ws.objects.fds &&
                    DM_DoOwnObj(ws.subjects, s_id, id.oid)
                ==> id in result
{
    set s_id, id | s_id in s_ids && id in ws.objects.fds && DM_DoOwnObj(ws.subjects, s_id, id.oid) :: id
}

function method WS_DOsOwnedBySubjs(ws:DM_State, s_ids:set<Subject_ID>) : (result:set<DO_ID>)
    requires forall id :: id in s_ids ==> DM_IsSubjID(ws.subjects, id)

    ensures forall id :: id in result
                ==> (exists s_id :: s_id in s_ids && DM_DoOwnObj(ws.subjects, s_id, id.oid))
    ensures forall s_id, id :: s_id in s_ids && id in ws.objects.dos &&
                    DM_DoOwnObj(ws.subjects, s_id, id.oid)
                ==> id in result
{
    set s_id, id | s_id in s_ids && id in ws.objects.dos && DM_DoOwnObj(ws.subjects, s_id, id.oid) :: id
}

predicate P_WS_DevActivate_Multi_ObjModifications(
    ws:DM_State, ws':DM_State,
    dev_ids:set<Dev_ID>, // ID of the devices to be activated
    pid:Partition_ID // ID of the target partition
)
    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs

    requires P_DMObjectsHasUniqueIDs(ws.objects)
{
    var s_ids := DevIDsToSubjIDs(dev_ids);

    // Unchanged state vars
    ws'.pids == ws.pids &&
    ws'.tds_to_all_states == ws.tds_to_all_states &&
    ws'.red_pid == ws.red_pid &&
    ws'.devs_activatecond == ws.devs_activatecond &&
    
    MapGetKeys(ws'.subjects.drvs) == MapGetKeys(ws.subjects.drvs) &&
    MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs) &&
    MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds) &&
    MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds) &&
    MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos) &&
    
    (forall drv_id :: drv_id in ws'.subjects.drvs
        ==> (ws'.subjects.drvs[drv_id].td_ids == ws.subjects.drvs[drv_id].td_ids &&
            ws'.subjects.drvs[drv_id].fd_ids == ws.subjects.drvs[drv_id].fd_ids &&
            ws'.subjects.drvs[drv_id].do_ids == ws.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in ws'.subjects.devs
        ==> (ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
            ws'.subjects.devs[dev_id].td_ids == ws.subjects.devs[dev_id].td_ids &&
            ws'.subjects.devs[dev_id].fd_ids == ws.subjects.devs[dev_id].fd_ids &&
            ws'.subjects.devs[dev_id].do_ids == ws.subjects.devs[dev_id].do_ids)) &&

    // Objects to be activated are correctly modified
    (forall id :: id in WS_TDsOwnedBySubjs(ws, s_ids) &&
            id !in DM_AllHCodedTDIDs(ws.subjects)
        ==> ws'.objects.tds[id].pid == pid &&
            IsTDClearVal(ws'.objects.tds, id)) &&
    (forall id :: id in WS_TDsOwnedBySubjs(ws, s_ids) &&
            id in DM_AllHCodedTDIDs(ws.subjects)
        ==> ws'.objects.tds[id].pid == pid &&
            DM_IsSameTDVal(ws'.objects, ws.objects, id)) &&
        // Only hardcoded TDs can be reused
    (forall id :: id in WS_FDsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.fds[id].pid == pid &&
            IsFDClearVal(ws'.objects.fds, id)) &&
    (forall id :: id in WS_DOsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.dos[id].pid == pid &&
            IsDOClearVal(ws'.objects.dos, id)) &&  
    
    // Objects not to be activated are unchanged
    (forall id :: id in ws.objects.tds &&
            id !in WS_TDsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in ws.objects.fds &&
            id !in WS_FDsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in ws.objects.dos &&
            id !in WS_DOsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameDO(ws'.objects, ws.objects, id)) &&

    (true)
}

predicate P_WS_DrvActivate_Multi_ObjModifications(
    ws:DM_State, ws':DM_State,
    drv_ids:set<Drv_ID>, // ID of the drivers to be deactivated
    pid:Partition_ID // ID of the target partition
)
    requires pid != NULL  
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
{
    P_WS_DrvActivate_Multi_ObjModifications_Others(ws, ws', drv_ids, pid) &&
    P_WS_DrvActivate_Multi_ObjModifications_HCodedTDs(ws, ws')
}





//******** Utility Lemmas ********//
lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually(
    ws:DM_State, ws1:DM_State, ws2:DM_State, t1:DM_Trace, t2:DM_Trace
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires t1.ws0 == ws
    requires DM_IsValidTrace(t1)
    requires ws1 == SeqLastElem(DM_CalcNewStates(t1))
    requires DM_IsValidState(ws1) && DM_IsSecureState(ws1)
    
    requires t2.ws0 == ws1
    requires DM_IsValidTrace(t2)
    requires ws2 == SeqLastElem(DM_CalcNewStates(t2))

    ensures ws2 == SeqLastElem(DM_CalcNewStates(ValidDMTrace_Concat(t1, t2)))
{
    var t := ValidDMTrace_Concat(t1, t2);
    assert DM_IsValidTrace(t);

    var result;
    var d;
    var t1_detailed, t2_detailed, t_detailed;
    result := ConvertTraceToDetailedTrace(t1);
    t1_detailed := result.0;
    d := result.1;
    assert d;

    result := ConvertTraceToDetailedTrace(t2);
    t2_detailed := result.0;
    d := result.1;
    assert d;

    result := ConvertTraceToDetailedTrace(t);
    t_detailed := result.0;
    d := result.1;
    assert d;
    
    assert t_detailed.ops == t1_detailed.ops + t2_detailed.ops;
    
    // Prove the main property
    var i := Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private(
                ws, ws1, ws2, t1, t2, t, t1_detailed, t2_detailed, t_detailed);
    assert |t_detailed.states| - |t1_detailed.states| == |t2_detailed.states| - 1;

    
    if(|t2_detailed.states| == 1)
    {
        assert SeqLastElem(t1_detailed.states) == SeqLastElem(t2_detailed.states) == ws1;
        assert t_detailed.states[|t_detailed.states|-1] == ws1;
        assert t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1];
    }
    else
    {
        assert |t2_detailed.states| > 1;
        assert |t_detailed.states|-1 >= |t1_detailed.states|;
        assert t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|];
        assert i == |t_detailed.states| - 1;
        assert t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1];
    }

    var seq1 := t_detailed.states;
    var seq2 := t2_detailed.states;

    assert t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1];
    Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_EquivilantEndOfSeq(
        t_detailed, t2_detailed, seq1, seq2);
    assert seq1[|seq1|-1] == seq2[|seq2|-1]; 
    Lemma_SeqLastElem_Property(seq1, seq2);
    assert SeqLastElem(t_detailed.states) == SeqLastElem(t2_detailed.states);
}

// Lemma: If a DM_Trace comprises one operation only, and the operation returns 
// true, then the return state is the last state
lemma Lemma_DM_CalcNewStates_OneDMOp_Property(ws:DM_State, op:DM_Op, ws':DM_State)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    requires P_DM_OpsFulfillPreConditions(ws, op)
    
    requires DM_CalcNewState(ws, op) == (ws', true)
     
    ensures ws' == SeqLastElem(DM_CalcNewStates(DM_Trace(ws, [op])))
{
    assert DM_CalcNewStates(DM_Trace(ws, [op])) == [ws, ws'];
    assert SeqLastElem([ws, ws']) == ws';
}

lemma Lemma_DM_CalcNewStates_NoDMOp_Property(ws:DM_State)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
    
     
    ensures ws == SeqLastElem(DM_CalcNewStates(DM_Trace(ws, [])))
{
    assert DM_CalcNewStates(DM_Trace(ws, [])) == [ws];
    assert SeqLastElem([ws]) == ws;
}




//******** Private Lemmas of Utility Functions ********//
lemma Lemma_WS_DrvActivate_Multi_Private(
    next_t:DM_Trace, next_drv_ids:seq<Drv_ID>, op:DM_Op, t:DM_Trace, drv_ids:seq<Drv_ID>, pid:Partition_ID
)
    requires |drv_ids| > 0

    requires t.ops == [op] + next_t.ops
    requires next_drv_ids == drv_ids[1..]
   
    requires op == DM_DrvActivateToGreenPartitionOp(drv_ids[0].sid, pid)

    requires |next_drv_ids| == |next_t.ops|
    requires (forall i :: 0 <= i < |next_t.ops| ==> next_t.ops[i] == DM_DrvActivateToGreenPartitionOp(next_drv_ids[i].sid, pid))

    requires |drv_ids| == |t.ops|

    ensures forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DrvActivateToGreenPartitionOp(drv_ids[i].sid, pid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DrvDeactivate_Multi_Private(
    next_t:DM_Trace, next_drv_ids:seq<Drv_ID>, op:DM_Op, t:DM_Trace, drv_ids:seq<Drv_ID>
)
    requires |drv_ids| > 0

    requires t.ops == [op] + next_t.ops
    requires next_drv_ids == drv_ids[1..]
   
    requires op == DM_GreenDrvDeactivateOp(drv_ids[0].sid)

    requires |next_drv_ids| == |next_t.ops|
    requires (forall i :: 0 <= i < |next_t.ops| ==> next_t.ops[i] == DM_GreenDrvDeactivateOp(next_drv_ids[i].sid))

    requires |drv_ids| == |t.ops|

    ensures forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_GreenDrvDeactivateOp(drv_ids[i].sid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DevActivate_Multi_Private(
    next_t:DM_Trace, next_dev_ids:seq<Dev_ID>, op:DM_Op, t:DM_Trace, dev_ids:seq<Dev_ID>, pid:Partition_ID
)
    requires |dev_ids| > 0

    requires t.ops == [op] + next_t.ops
    requires next_dev_ids == dev_ids[1..]
   
    requires op == DM_DevActivateOp(dev_ids[0].sid, pid)

    requires |next_dev_ids| == |next_t.ops|
    requires (forall i :: 0 <= i < |next_t.ops| ==> next_t.ops[i] == DM_DevActivateOp(next_dev_ids[i].sid, pid))

    requires |dev_ids| == |t.ops|

    ensures forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DevActivateOp(dev_ids[i].sid, pid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DevDeactivate_Multi_Private(
    next_t:DM_Trace, next_dev_ids:seq<Dev_ID>, op:DM_Op, t:DM_Trace, dev_ids:seq<Dev_ID>
)
    requires |dev_ids| > 0

    requires t.ops == [op] + next_t.ops
    requires next_dev_ids == dev_ids[1..]
   
    requires op == DM_DevDeactivateOp(dev_ids[0].sid)

    requires |next_dev_ids| == |next_t.ops|
    requires (forall i :: 0 <= i < |next_t.ops| ==> next_t.ops[i] == DM_DevDeactivateOp(next_dev_ids[i].sid))

    requires |dev_ids| == |t.ops|

    ensures forall i :: 0 <= i < |t.ops| ==> t.ops[i] == DM_DevDeactivateOp(dev_ids[i].sid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DevDeactivate_FromGreen_Multi_Private(
    ws:DM_State, op:DM_Op,
    next_t:DM_Trace, detailed_next_t:DM_Trace_Detailed,
    t:DM_Trace, t_detailed:DM_Trace_Detailed
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    requires DM_IsValidState(ws) && DM_IsSecureState(ws)
     
    requires P_DM_OpsFulfillPreConditions(ws, op)
    requires DM_CalcNewState(ws, op) == (next_t.ws0, true)

    requires t == DM_Trace(ws, [op] + next_t.ops)
    requires t_detailed == DM_Trace_Detailed([ws] + detailed_next_t.states, [op] + detailed_next_t.ops)
    requires ConvertTraceToDetailedTrace(next_t) == (detailed_next_t, true)

    requires DM_DetailedTrace_IsValidTrace(t_detailed)

    ensures t == ConvertDetailedTraceToTrace(t_detailed)
{
    // Dafny can automatically prove this lemma
}

// (needs 30s to verify)
lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private(
    ws:DM_State, ws1:DM_State, ws2:DM_State, t1:DM_Trace, t2:DM_Trace, t:DM_Trace,
    t1_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, t_detailed:DM_Trace_Detailed
) returns (i:int)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(ws) && DM_IsSecureState(ws)

    requires t1.ws0 == ws
    requires DM_IsValidTrace(t1)
    requires ws1 == SeqLastElem(DM_CalcNewStates(t1))
    requires DM_IsValidState(ws1) && DM_IsSecureState(ws1)
    
    requires t2.ws0 == ws1
    requires DM_IsValidTrace(t2)
    requires ws2 == SeqLastElem(DM_CalcNewStates(t2))


    requires t1_detailed == ConvertTraceToDetailedTrace(t1).0
    requires t2_detailed == ConvertTraceToDetailedTrace(t2).0
    requires t == ValidDMTrace_Concat(t1, t2);
    requires t_detailed == ConvertTraceToDetailedTrace(t).0

    ensures i == |t_detailed.states|-1
    ensures 0 <= i < |t1_detailed.states| ==> t_detailed.states[i] == t1_detailed.states[i]
    ensures |t1_detailed.states| <= i < |t_detailed.states| ==> t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|]
{
    assert DM_IsValidTrace(t);

    assert ConvertTraceToDetailedTrace(t1).1;
    assert ConvertTraceToDetailedTrace(t2).1;
    assert ConvertTraceToDetailedTrace(t).1;

    assert t_detailed.ops == t1_detailed.ops + t2_detailed.ops;

    i := 0;

    assert t1_detailed.states[|t1_detailed.states|-1] == ws1;
    assert t2_detailed.states[0] == ws1;
    assert |t_detailed.states| >= |t1_detailed.states|;

    while (i < |t_detailed.states|-1)
        invariant 0 <= i <= |t_detailed.states|-1

        invariant 0 <= i < |t1_detailed.ops| ==> t_detailed.ops[i] == t1_detailed.ops[i]
        invariant 0 <= i < |t1_detailed.states| ==> t_detailed.states[i] == t1_detailed.states[i]

        invariant |t1_detailed.ops| <= i < |t_detailed.ops| ==> t_detailed.ops[i] == t2_detailed.ops[i-|t1_detailed.ops|]
        invariant |t1_detailed.states| <= i < |t_detailed.states| ==> t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|]
    {
        if (|t1_detailed.states| <= i < |t_detailed.states| && 
            |t1_detailed.states| <= i+1 < |t_detailed.states|)
        {
            var from_t2_detailed_state := t2_detailed.states[i+1-|t1_detailed.states|];
            var to_t2_detailed_state := t2_detailed.states[i+2-|t1_detailed.states|];
            
            assert t_detailed.states[i] == from_t2_detailed_state;
            
            assert t_detailed.states[i+1] == DM_CalcNewState(t_detailed.states[i], t_detailed.ops[i]).0;
            
            assert to_t2_detailed_state == DM_CalcNewState(from_t2_detailed_state, t2_detailed.ops[i+1-|t1_detailed.states|]).0;
            assert |t1_detailed.states| == |t1_detailed.ops|+1;
            assert i+1-|t1_detailed.states| == i-|t1_detailed.ops|;
            Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private_ForT2Detailed(t1_detailed, t2_detailed, i);
            assert t2_detailed.ops[i+1-|t1_detailed.states|] == t2_detailed.ops[i-|t1_detailed.ops|];
            assert to_t2_detailed_state == DM_CalcNewState(from_t2_detailed_state, t2_detailed.ops[i-|t1_detailed.ops|]).0;
            
            // Prove same op in <t_detailed> and <t2_detailed>
            assert |t1_detailed.ops| <= i < |t_detailed.ops|;
            assert t_detailed.ops[i] == t2_detailed.ops[i-|t1_detailed.ops|];
            
            assert to_t2_detailed_state == DM_CalcNewState(from_t2_detailed_state, t_detailed.ops[i]).0;
            assert t_detailed.states[i+1] == to_t2_detailed_state; 
        }

        i := i + 1;
    }

    assert 0 <= i < |t1_detailed.states| ==> t_detailed.states[i] == t1_detailed.states[i];
    assert |t1_detailed.states| <= i < |t_detailed.states| ==> t_detailed.states[i] == t2_detailed.states[i+1-|t1_detailed.states|];
}

lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_Private_ForT2Detailed(
    t1_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, i:int
)
    requires i+1-|t1_detailed.states| == i-|t1_detailed.ops|
    requires 0 <= i-|t1_detailed.ops| < |t2_detailed.ops|

    ensures t2_detailed.ops[i+1-|t1_detailed.states|] == t2_detailed.ops[i-|t1_detailed.ops|]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DrvActivate_Multi_ProveProperty11(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    drv_ids:seq<Drv_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs
    
    requires |drv_ids| > 0
    requires drv_ids[0] in ws.subjects.drvs
    requires pid != NULL
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DrvActivate_ModificationToState(DMStateToState(ws), drv_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WS_DrvActivate_Multi_ObjModifications(ws', last_ws, SeqToSet(drv_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures P_WS_DrvActivate_Multi_ObjModifications(ws, last_ws, SeqToSet(drv_ids), pid)
        // Properties of activate devices
        // Property 11 
{
    Lemma_WS_DrvActivate_Multi_ProveProperty11_ProveOthersProperties(ws, ws', last_ws, drv_ids, pid);
    Lemma_WS_DrvActivate_Multi_ProveProperty11_ProveHCodedTDsProperties(ws, ws', last_ws, drv_ids, pid);
}

// (needs 60s to verify)
lemma Lemma_WS_DevActivate_Multi_ProveProperty11(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WS_DevActivate_Multi_ObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures P_WS_DevActivate_Multi_ObjModifications(ws, last_ws, SeqToSet(dev_ids), pid)
        // Properties of activate devices
        // Property 11 
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    Lemma_WS_TDsOwnedBySubjs_PropertyOfOneDev(ws, dev_ids[0]);
    assert WS_TDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].td_ids;
    assert WS_FDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].fd_ids;
    assert WS_DOsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].do_ids;
            
    Lemma_WS_TDsOwnedBySubjs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WS_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds);
    assert MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds);
    assert MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos);

    var s_ids := DevIDsToSubjIDs(dev_ids_set);
    forall id | id in WS_TDsOwnedBySubjs(ws, s_ids) &&
            id !in DM_AllHCodedTDIDs(ws.subjects)
        ensures last_ws.objects.tds[id].pid == pid
        ensures IsTDClearVal(last_ws.objects.tds, id)
    {
        assert id in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) || id in ws.subjects.devs[dev_ids[0]].td_ids;
        
        if(id in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))))
        {
            Lemma_WS_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs(ws', last_ws, dev_ids, pid, id);
            assert last_ws.objects.tds[id].pid == pid;
            assert IsTDClearVal(last_ws.objects.tds, id);
        }
    }

    forall id | id in WS_TDsOwnedBySubjs(ws, s_ids) &&
            id in DM_AllHCodedTDIDs(ws.subjects)
        ensures last_ws.objects.tds[id].pid == pid
        ensures DM_IsSameTDVal(last_ws.objects, ws.objects, id)
    {
        assert id in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) || id in ws.subjects.devs[dev_ids[0]].td_ids;
        
        if(id in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))))
        {
            Lemma_WS_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs(ws', last_ws, dev_ids, pid, id);
            assert last_ws.objects.tds[id].pid == pid;
            assert DM_IsSameTDVal(last_ws.objects, ws.objects, id);
        }
    }

    forall id | id in WS_FDsOwnedBySubjs(ws, s_ids)
        ensures last_ws.objects.fds[id].pid == pid
        ensures IsFDClearVal(last_ws.objects.fds, id)
    {
        assert id in WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) || id in ws.subjects.devs[dev_ids[0]].fd_ids;

        if(id in WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))))
        {
            assert last_ws.objects.fds[id].pid == pid;
            assert IsFDClearVal(last_ws.objects.fds, id);
        }
    }
    
    Lemma_WS_DevActivate_Multi_ProveProperty11_Sub(ws, ws', last_ws, dev_ids, pid);
}

// (needs 30s to verify)
lemma Lemma_WS_DrvDeactivate_Multi_ProveProperty12(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    drv_ids:seq<Drv_ID>
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs
    
    requires |drv_ids| > 0
    requires drv_ids[0] in ws.subjects.drvs
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DrvDeactivate_ModificationToState(DMStateToState(ws), drv_ids[0].sid, DMStateToState(ws'))
    
    requires P_WS_DrvDevDeactivate_Multi_ObjModifications(ws', last_ws, DrvIDsToSubjIDs(SeqToSet(drv_ids[1..])))
        // Property 12 Recursion
        
    ensures P_WS_DrvDevDeactivate_Multi_ObjModifications(ws, last_ws, DrvIDsToSubjIDs(SeqToSet(drv_ids)))
        // Properties of activate devices
        // Property 12
{
    var next_drv_ids := drv_ids[1..];
    var drv_ids_set := SeqToSet(drv_ids);
    var next_drv_ids_set := SeqToSet(next_drv_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(drv_ids)
            ==> dev_id == drv_ids[0] || dev_id in SeqToSet(next_drv_ids);
            
    assert WS_TDsOwnedBySubjs(ws, {drv_ids[0].sid}) == ws.subjects.drvs[drv_ids[0]].td_ids;
            
    Lemma_WS_TDsOwnedBySubjs_HighlightADrv(ws, drv_ids_set, next_drv_ids_set, drv_ids[0]);
}

// (needs 40s to verify)
lemma Lemma_WS_DevDeactivate_FromGreen_ProveProperty11(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DevDeactivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, DMStateToState(ws'))
    
    requires P_WS_DrvDevDeactivate_Multi_ObjModifications(ws', last_ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
        // Property 11 Recursion
        
    ensures P_WS_DrvDevDeactivate_Multi_ObjModifications(ws, last_ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
        // Properties of activate devices
        // Property 11
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);
            
    Lemma_WS_TDsOwnedBySubjs_PropertyOfOneDev(ws, dev_ids[0]);
    assert WS_TDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].td_ids;
    assert WS_FDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].fd_ids;
    assert WS_DOsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].do_ids;
            
    Lemma_WS_TDsOwnedBySubjs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WS_DevDeactivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids);
    assert MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds);
    assert MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds);
    assert MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos);

    Lemma_WS_DevDeactivate_FromGreen_ProveProperty11_Sub(ws, ws', last_ws, dev_ids);
}

predicate P_WS_DrvActivate_Multi_ObjModifications_Others(
    ws:DM_State, ws':DM_State,
    drv_ids:set<Drv_ID>, // ID of the drivers to be activated
    pid:Partition_ID // ID of the target partition
)
    requires pid != NULL  
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
{
    var s_ids := DrvIDsToSubjIDs(drv_ids);
    
    // Unchanged state vars
    ws'.pids == ws.pids &&
    ws'.tds_to_all_states == ws.tds_to_all_states &&
    ws'.red_pid == ws.red_pid &&
    ws'.devs_activatecond == ws.devs_activatecond &&
    
    MapGetKeys(ws'.subjects.drvs) == MapGetKeys(ws.subjects.drvs) &&
    MapGetKeys(ws'.subjects.devs) == MapGetKeys(ws.subjects.devs) &&
    MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds) &&
    MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds) &&
    MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos) &&
    
    (forall drv_id :: drv_id in ws'.subjects.drvs
        ==> (ws'.subjects.drvs[drv_id].td_ids == ws.subjects.drvs[drv_id].td_ids &&
            ws'.subjects.drvs[drv_id].fd_ids == ws.subjects.drvs[drv_id].fd_ids &&
            ws'.subjects.drvs[drv_id].do_ids == ws.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in ws'.subjects.devs
        ==> (ws'.subjects.devs[dev_id].hcoded_td_id == ws.subjects.devs[dev_id].hcoded_td_id &&
            ws'.subjects.devs[dev_id].td_ids == ws.subjects.devs[dev_id].td_ids &&
            ws'.subjects.devs[dev_id].fd_ids == ws.subjects.devs[dev_id].fd_ids &&
            ws'.subjects.devs[dev_id].do_ids == ws.subjects.devs[dev_id].do_ids)) &&

    // Objects to be activated are correctly modified
    (forall id :: id in WS_TDsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.tds[id].pid == pid &&
            IsTDClearVal(ws'.objects.tds, id)) &&
    (forall id :: id in WS_FDsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.fds[id].pid == pid &&
            IsFDClearVal(ws'.objects.fds, id)) &&
    (forall id :: id in WS_DOsOwnedBySubjs(ws, s_ids)
        ==> ws'.objects.dos[id].pid == pid &&
            IsDOClearVal(ws'.objects.dos, id)) &&  
    
    // Objects not to be activated are unchanged
    (forall id :: id in ws.objects.tds &&
            id !in WS_TDsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in ws.objects.fds &&
            id !in WS_FDsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameFD(ws'.objects, ws.objects, id)) &&
    (forall id :: id in ws.objects.dos &&
            id !in WS_DOsOwnedBySubjs(ws, s_ids)
        ==> DM_IsSameDO(ws'.objects, ws.objects, id)) &&

    (true)
}

predicate P_WS_DrvActivate_Multi_ObjModifications_HCodedTDs(
    ws:DM_State, ws':DM_State
)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds)
{
    // Especially, Hardcoded TDs are unchanged
    // [Note] This statement can be also defined as a property
    (forall id :: id in ws.objects.tds && id in DM_AllHCodedTDIDs(ws.subjects)
        ==> DM_IsSameTD(ws'.objects, ws.objects, id)) &&

    (true)
}

lemma Lemma_WS_TDsOwnedBySubjs_HighlightADrv(
    ws:DM_State, drv_ids_set:set<Drv_ID>, next_drv_ids_set:set<Drv_ID>, drv0_id:Drv_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
     
    requires forall id :: id in drv_ids_set ==> id in ws.subjects.drvs
    requires drv_ids_set == next_drv_ids_set + {drv0_id}

    ensures WS_TDsOwnedBySubjs(ws, DrvIDsToSubjIDs(drv_ids_set)) == WS_TDsOwnedBySubjs(ws, DrvIDsToSubjIDs(next_drv_ids_set)) + ws.subjects.drvs[drv0_id].td_ids
    ensures WS_FDsOwnedBySubjs(ws, DrvIDsToSubjIDs(drv_ids_set)) == WS_FDsOwnedBySubjs(ws, DrvIDsToSubjIDs(next_drv_ids_set)) + ws.subjects.drvs[drv0_id].fd_ids
    ensures WS_DOsOwnedBySubjs(ws, DrvIDsToSubjIDs(drv_ids_set)) == WS_DOsOwnedBySubjs(ws, DrvIDsToSubjIDs(next_drv_ids_set)) + ws.subjects.drvs[drv0_id].do_ids
{
    assert DrvIDsToSubjIDs(drv_ids_set) == DrvIDsToSubjIDs(next_drv_ids_set) + {drv0_id.sid};
}

lemma Lemma_WS_TDsOwnedBySubjs_HighlightADev(
    ws:DM_State, dev_ids_set:set<Dev_ID>, next_dev_ids_set:set<Dev_ID>, dev0_id:Dev_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
     
    requires forall id :: id in dev_ids_set ==> id in ws.subjects.devs
    requires dev_ids_set == next_dev_ids_set + {dev0_id}

    ensures WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(dev_ids_set)) == WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(next_dev_ids_set)) + ws.subjects.devs[dev0_id].td_ids;
    ensures WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(dev_ids_set)) == WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(next_dev_ids_set)) + ws.subjects.devs[dev0_id].fd_ids;
    ensures WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(dev_ids_set)) == WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(next_dev_ids_set)) + ws.subjects.devs[dev0_id].do_ids;
{
    assert DevIDsToSubjIDs(dev_ids_set) == DevIDsToSubjIDs(next_dev_ids_set) + {dev0_id.sid};
}

lemma Lemma_WS_TDsOwnedBySubjs_PropertyOfOneDev(ws:DM_State, dev_id:Dev_ID)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires dev_id in ws.subjects.devs

    ensures WS_TDsOwnedBySubjs(ws, {dev_id.sid}) == ws.subjects.devs[dev_id].td_ids
    ensures WS_FDsOwnedBySubjs(ws, {dev_id.sid}) == ws.subjects.devs[dev_id].fd_ids
    ensures WS_DOsOwnedBySubjs(ws, {dev_id.sid}) == ws.subjects.devs[dev_id].do_ids
{
    var result := WS_TDsOwnedBySubjs(ws, {dev_id.sid});

    Lemma_DM_SameIDsIffSameInternalIDs();
    forall id | id in result
        ensures id in ws.subjects.devs[dev_id].td_ids
    {
        var s_id :| s_id in {dev_id.sid} && DM_DoOwnObj(ws.subjects, s_id, id.oid);
        assert s_id == dev_id.sid;
    }

    assert WS_TDsOwnedBySubjs(ws, {dev_id.sid}) >= ws.subjects.devs[dev_id].td_ids;
}

// (needs 100s to verify)
lemma Lemma_WS_DrvActivate_Multi_ProveProperty11_ProveOthersProperties(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    drv_ids:seq<Drv_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs
    
    requires |drv_ids| > 0
    requires drv_ids[0] in ws.subjects.drvs
    requires pid != NULL
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DrvActivate_ModificationToState(DMStateToState(ws), drv_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WS_DrvActivate_Multi_ObjModifications(ws', last_ws, SeqToSet(drv_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures P_WS_DrvActivate_Multi_ObjModifications_Others(ws, last_ws, SeqToSet(drv_ids), pid)
        // Properties of activate devices
        // Property 11
{
    var next_drv_ids := drv_ids[1..];
    var drv_ids_set := SeqToSet(drv_ids);
    var next_drv_ids_set := SeqToSet(next_drv_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(drv_ids)
            ==> dev_id == drv_ids[0] || dev_id in SeqToSet(next_drv_ids);

    assert WS_TDsOwnedBySubjs(ws, {drv_ids[0].sid}) == ws.subjects.drvs[drv_ids[0]].td_ids;
            
    Lemma_WS_TDsOwnedBySubjs_HighlightADrv(ws, drv_ids_set, next_drv_ids_set, drv_ids[0]);
    assert P_WS_DrvActivate_Multi_ObjModifications_Others(ws, last_ws, drv_ids_set, pid);
}

// (needs 40s to verify)
lemma Lemma_WS_DrvActivate_Multi_ProveProperty11_ProveHCodedTDsProperties(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    drv_ids:seq<Drv_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires forall id :: id in drv_ids ==> id in ws.subjects.drvs
    
    requires |drv_ids| > 0
    requires drv_ids[0] in ws.subjects.drvs
    requires pid != NULL
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.drvs[drv_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DrvActivate_ModificationToState(DMStateToState(ws), drv_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WS_DrvActivate_Multi_ObjModifications_Others(ws, last_ws, SeqToSet(drv_ids), pid)
        
    ensures P_WS_DrvActivate_Multi_ObjModifications_HCodedTDs(ws, last_ws)
        // Properties of activate devices
        // Property 11
{
    var next_drv_ids := drv_ids[1..];
    var drv_ids_set := SeqToSet(drv_ids);
    var next_drv_ids_set := SeqToSet(next_drv_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(drv_ids)
            ==> dev_id == drv_ids[0] || dev_id in SeqToSet(next_drv_ids);

    assert WS_TDsOwnedBySubjs(ws, {drv_ids[0].sid}) == ws.subjects.drvs[drv_ids[0]].td_ids;
            
    
    forall id | id in ws.objects.tds && id in DM_AllHCodedTDIDs(ws.subjects)
        ensures DM_IsSameTD(last_ws.objects, ws.objects, id)
    {
        var drv_tds_set := WS_TDsOwnedBySubjs(ws, DrvIDsToSubjIDs(drv_ids_set));
        if(id in drv_tds_set)
        {
            var drv_id :| drv_id in drv_ids_set && DM_DoOwnObj(ws.subjects, drv_id.sid, id.oid);
            var dev_id :| dev_id in ws.subjects.devs && id == ws.subjects.devs[dev_id].hcoded_td_id;
            
            // Show conflicts
            assert DM_DoOwnObj(ws.subjects, drv_id.sid, id.oid);
            assert DM_DoOwnObj(ws.subjects, dev_id.sid, id.oid);
            assert drv_id.sid != dev_id.sid;

            Lemma_DM_TwoSubjectsCannotOwnSameObj(ws);
            assert drv_id.sid == dev_id.sid;

            assert false;
        }
        assert id !in drv_tds_set;
    }
}

lemma Lemma_WS_DevActivate_Multi_ProveProperty11_PropertiesOfSubDevIDs(
    ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID, td_id:TD_ID
)
    requires pid != NULL  
    requires forall id :: id in dev_ids ==> id in ws'.subjects.devs
    requires |dev_ids| > 0

    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    
    requires P_WS_DevActivate_Multi_ObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)

    requires td_id in WS_TDsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))

    ensures last_ws.objects.tds[td_id].pid == pid
    ensures (td_id !in DM_AllHCodedTDIDs(ws'.subjects)) ==> IsTDClearVal(last_ws.objects.tds, td_id)
    ensures (td_id in DM_AllHCodedTDIDs(ws'.subjects)) ==> DM_IsSameTDVal(last_ws.objects, ws'.objects, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(
    ws:DM_State, ws':DM_State, 
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires pid != NULL

    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    ensures WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) == 
            WS_TDsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
    ensures WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) == 
            WS_FDsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
    ensures WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) == 
            WS_DOsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
{
    // Dafny can automatically prove this lemma
}

// (needs 60s to verify)
lemma Lemma_WS_DevActivate_Multi_ProveProperty11_Sub(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>, 
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires pid != NULL
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DevActivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, pid, DMStateToState(ws'))
    
    requires P_WS_DevActivate_Multi_ObjModifications(ws', last_ws, SeqToSet(dev_ids[1..]), pid)
        // Property 11 Recursion
        
    ensures (forall id :: id in ws.objects.tds &&
                    id !in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
                ==> DM_IsSameTD(last_ws.objects, ws.objects, id))
    ensures (forall id :: id in ws.objects.fds &&
                    id !in WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
                ==> DM_IsSameFD(last_ws.objects, ws.objects, id))
    ensures (forall id :: id in ws.objects.dos &&
                    id !in WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
                ==> DM_IsSameDO(last_ws.objects, ws.objects, id))
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);

    Lemma_WS_TDsOwnedBySubjs_PropertyOfOneDev(ws, dev_ids[0]);
    assert WS_TDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].td_ids;
    assert WS_FDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].fd_ids;
    assert WS_DOsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].do_ids;
            
    Lemma_WS_TDsOwnedBySubjs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WS_DevActivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids, pid);
    assert MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds);
    assert MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds);
    assert MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos);

    var s_ids := DevIDsToSubjIDs(dev_ids_set);
    forall id | id in ws.objects.tds &&
            id !in WS_TDsOwnedBySubjs(ws, s_ids)
        ensures DM_IsSameTD(last_ws.objects, ws.objects, id)
    {
        assert id !in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) && id !in ws.subjects.devs[dev_ids[0]].td_ids;
        
        assert DM_IsSameTD(last_ws.objects, ws'.objects, id);
        assert DM_IsSameTD(ws'.objects, ws.objects, id);
        assert DM_IsSameTD(last_ws.objects, ws.objects, id);
    }
    
    forall id | id in ws.objects.fds &&
            id !in WS_FDsOwnedBySubjs(ws, s_ids)
        ensures DM_IsSameFD(last_ws.objects, ws.objects, id)
    {
        assert id !in WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) && id !in ws.subjects.devs[dev_ids[0]].fd_ids;
        
        assert DM_IsSameFD(last_ws.objects, ws'.objects, id);
        assert DM_IsSameFD(ws'.objects, ws.objects, id);
        assert DM_IsSameFD(last_ws.objects, ws.objects, id);
    }
    
    forall id | id in ws.objects.dos &&
            id !in WS_DOsOwnedBySubjs(ws, s_ids)
        ensures DM_IsSameDO(last_ws.objects, ws.objects, id)
    {
        assert id !in WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) && id !in ws.subjects.devs[dev_ids[0]].do_ids;
        
        assert DM_IsSameDO(last_ws.objects, ws'.objects, id);
        assert DM_IsSameDO(ws'.objects, ws.objects, id);
        assert DM_IsSameDO(last_ws.objects, ws.objects, id);
    }
}

lemma Lemma_ConcatTwoTraceEndUpAtSameStateAsCalcTwoTraceIndividually_EquivilantEndOfSeq(
    t_detailed:DM_Trace_Detailed, t2_detailed:DM_Trace_Detailed, seq1:seq<DM_State>, seq2:seq<DM_State>
)
    requires |t_detailed.states| > 0
    requires |t2_detailed.states| > 0
    requires t_detailed.states[|t_detailed.states|-1] == t2_detailed.states[|t2_detailed.states|-1]
    requires seq1 == t_detailed.states
    requires seq2 == t2_detailed.states
    
    ensures seq1[|seq1|-1] == seq2[|seq2|-1]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DevDeactivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(
    ws:DM_State, ws':DM_State, 
    dev_ids:seq<Dev_ID>
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(ws'.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0

    requires P_DevDeactivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, DMStateToState(ws'))
    
    ensures WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) == 
            WS_TDsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
    ensures WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) == 
            WS_FDsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
    ensures WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) == 
            WS_DOsOwnedBySubjs(ws', DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WS_DevDeactivate_FromGreen_ProveProperty11_Sub(
    ws:DM_State, ws':DM_State, last_ws:DM_State,
    dev_ids:seq<Dev_ID>
)
    requires DM_IsValidState(ws)
    requires P_DMObjectsHasUniqueIDs(last_ws.objects)
    requires forall id :: id in dev_ids ==> id in ws.subjects.devs
    
    requires |dev_ids| > 0
    requires dev_ids[0] in ws.subjects.devs
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].td_ids <= MapGetKeys(DMStateToState(ws).objects.tds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].fd_ids <= MapGetKeys(DMStateToState(ws).objects.fds)
    requires DMStateToState(ws).subjects.devs[dev_ids[0]].do_ids <= MapGetKeys(DMStateToState(ws).objects.dos)

    requires DM_IsSecureOps(ws, ws')
    requires P_DevDeactivate_ModificationToState(DMStateToState(ws), dev_ids[0].sid, DMStateToState(ws'))
    
    requires P_WS_DrvDevDeactivate_Multi_ObjModifications(ws', last_ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..])))
        // Property 11 Recursion
        
    ensures (forall id :: id in ws.objects.tds &&
                    id !in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
                ==> DM_IsSameTD(last_ws.objects, ws.objects, id))
    ensures (forall id :: id in ws.objects.fds &&
                    id !in WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
                ==> DM_IsSameFD(last_ws.objects, ws.objects, id))
    ensures (forall id :: id in ws.objects.dos &&
                    id !in WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids)))
                ==> DM_IsSameDO(last_ws.objects, ws.objects, id))
{
    var next_dev_ids := dev_ids[1..];
    var dev_ids_set := SeqToSet(dev_ids);
    var next_dev_ids_set := SeqToSet(next_dev_ids);
    
    assert forall dev_id :: dev_id in SeqToSet(dev_ids)
            ==> dev_id == dev_ids[0] || dev_id in SeqToSet(next_dev_ids);
            
    Lemma_WS_TDsOwnedBySubjs_PropertyOfOneDev(ws, dev_ids[0]);
    assert WS_TDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].td_ids;
    assert WS_FDsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].fd_ids;
    assert WS_DOsOwnedBySubjs(ws, {dev_ids[0].sid}) == ws.subjects.devs[dev_ids[0]].do_ids;
            
    Lemma_WS_TDsOwnedBySubjs_HighlightADev(ws, dev_ids_set, next_dev_ids_set, dev_ids[0]);
    Lemma_WS_DevDeactivate_Multi_ProveProperty11_ObjsOwnedByDevsInWSEqualToOnesOwnedByDevsInNewWS(ws, ws', dev_ids);
    assert MapGetKeys(ws'.objects.tds) == MapGetKeys(ws.objects.tds);
    assert MapGetKeys(ws'.objects.fds) == MapGetKeys(ws.objects.fds);
    assert MapGetKeys(ws'.objects.dos) == MapGetKeys(ws.objects.dos);

    var s_ids := DevIDsToSubjIDs(dev_ids_set);
    forall id | id in ws.objects.tds &&
            id !in WS_TDsOwnedBySubjs(ws, s_ids)
        ensures DM_IsSameTD(last_ws.objects, ws.objects, id)
    {
        assert id !in WS_TDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) && id !in ws.subjects.devs[dev_ids[0]].td_ids;
        
        assert DM_IsSameTD(last_ws.objects, ws'.objects, id);
        assert DM_IsSameTD(ws'.objects, ws.objects, id);
        assert DM_IsSameTD(last_ws.objects, ws.objects, id);
    }
    
    forall id | id in ws.objects.fds &&
            id !in WS_FDsOwnedBySubjs(ws, s_ids)
        ensures DM_IsSameFD(last_ws.objects, ws.objects, id)
    {
        assert id !in WS_FDsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) && id !in ws.subjects.devs[dev_ids[0]].fd_ids;
        
        assert DM_IsSameFD(last_ws.objects, ws'.objects, id);
        assert DM_IsSameFD(ws'.objects, ws.objects, id);
        assert DM_IsSameFD(last_ws.objects, ws.objects, id);
    }
    
    forall id | id in ws.objects.dos &&
            id !in WS_DOsOwnedBySubjs(ws, s_ids)
        ensures DM_IsSameDO(last_ws.objects, ws.objects, id)
    {
        assert id !in WS_DOsOwnedBySubjs(ws, DevIDsToSubjIDs(SeqToSet(dev_ids[1..]))) && id !in ws.subjects.devs[dev_ids[0]].do_ids;
        
        assert DM_IsSameDO(last_ws.objects, ws'.objects, id);
        assert DM_IsSameDO(ws'.objects, ws.objects, id);
        assert DM_IsSameDO(last_ws.objects, ws.objects, id);
    }
}




//******** Private Lemmas of Operations ********//
lemma Lemma_WK_WimpDrvsDevs_Registration_ProveValidTrace_AfterActivateExternalObjsToGreenPartition(
    last_ws:DM_State, t:DM_Trace,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)

    requires to_assign_external_td_ids <= MapGetKeys(last_ws.objects.tds)
    requires to_assign_external_fd_ids <= MapGetKeys(last_ws.objects.fds)
    requires to_assign_external_do_ids <= MapGetKeys(last_ws.objects.dos)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(last_ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(last_ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires t == DM_Trace(last_ws, [DM_ExternalObjsActivateToGreenPartitionOp(to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid)])
    
    requires green_pid != NULL
    requires green_pid != last_ws.red_pid
    requires green_pid in last_ws.pids
        // Requirement: We have already create a green partition

    ensures DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
    ensures DM_IsValidTrace(t)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WK_WimpDrvsDevs_Unregistration_ProveValidTrace_AfterDestroyPartition(
    last_ws:DM_State, t:DM_Trace,
    green_pid:Partition_ID
)
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)

    requires DM_IsValidState(last_ws) && DM_IsSecureState(last_ws)


    requires t == DM_Trace(last_ws, [DM_EmptyPartitionDestroyOp(green_pid)])
    
    requires green_pid != NULL
    requires green_pid != last_ws.red_pid

    ensures DM_IsValidState(t.ws0) && DM_IsSecureState(t.ws0)
    ensures DM_IsValidTrace(t)
{
    // Dafny can automatically prove this lemma
}

// (needs 80s to verify)
lemma Lemma_WK_WimpDrvsDevs_Registration_AssignWimpDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
    ws:DM_State, ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State,
    to_deactivate_dev_id:Dev_ID, to_assign_drv_ids:seq<Drv_ID>, to_assign_dev_ids:seq<Dev_ID>,
    to_assign_external_td_ids:set<TD_ID>, to_assign_external_fd_ids:set<FD_ID>, to_assign_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_IsValidState(ws)

    requires to_deactivate_dev_id in ws.subjects.devs

    requires forall id :: id in to_assign_drv_ids ==> id in ws.subjects.drvs
    requires forall id :: id in to_assign_dev_ids ==> id in ws.subjects.devs

    requires to_assign_external_td_ids <= MapGetKeys(ws.objects.tds)
    requires to_assign_external_fd_ids <= MapGetKeys(ws.objects.fds)
    requires to_assign_external_do_ids <= MapGetKeys(ws.objects.dos)

    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: We have already create a green partition

    requires DM_IsSecureOps(ws, ws2)
    requires P_DevDeactivate_ModificationToState(DMStateToState(ws), to_deactivate_dev_id.sid, DMStateToState(ws2))
        // From device deactivation
    requires P_DMObjectsHasUniqueIDs(ws3.objects)
    requires P_WS_DevActivate_Multi_ObjModifications(ws2, ws3, SeqToSet(to_assign_dev_ids), green_pid)
        // From devices activation
    requires P_DMObjectsHasUniqueIDs(ws4.objects)
    requires P_WS_DrvActivate_Multi_ObjModifications(ws3, ws4, SeqToSet(to_assign_drv_ids), green_pid)
        // From drivers activation
    requires DM_IsValidState(ws4) //&& DM_IsSecureState(ws4)
    requires DM_IsSecureOps(ws4, ws5)
    requires IsValidState(DMStateToState(ws4))
    requires to_assign_external_td_ids <= MapGetKeys(DMStateToState(ws4).objects.tds)
    requires to_assign_external_fd_ids <= MapGetKeys(DMStateToState(ws4).objects.fds)
    requires to_assign_external_do_ids <= MapGetKeys(DMStateToState(ws4).objects.dos)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(DMStateToState(ws4).subjects) &&
                    o_id in (TDIDsToObjIDs(to_assign_external_td_ids) + FDIDsToObjIDs(to_assign_external_fd_ids) + DOIDsToObjIDs(to_assign_external_do_ids))
                ==> !DoOwnObj(DMStateToState(ws4), s_id, o_id)
        // Requirement: no subject owns these external objects
    requires P_ExternalObjsActivate_ModificationToState(DMStateToState(ws4), 
                    to_assign_external_td_ids, to_assign_external_fd_ids, to_assign_external_do_ids, green_pid, DMStateToState(ws5))

    ensures DM_IsSecureOps(ws, ws5)
{
    assert DM_IsSecureOps(ws, ws2);
    assert DM_IsSecureOps(ws, ws3);
    assert DM_IsSecureOps(ws, ws4);
    assert DM_IsSecureOps(ws, ws5);
}

// (needs 60s to verify)
lemma Lemma_WK_WimpDrvsDevs_Unregistration_ReassignDrvsDevsObjs_ProveSameTransitionContraintOverInputAndOutputState(
    ws:DM_State, ws2:DM_State, ws3:DM_State, ws4:DM_State, ws5:DM_State,
    to_deactivate_drv_ids:seq<Drv_ID>, to_deactivate_dev_ids:seq<Dev_ID>, devs_to_activate_in_red:seq<Dev_ID>, 
    to_deactivate_external_td_ids:set<TD_ID>, to_deactivate_external_fd_ids:set<FD_ID>, to_deactivate_external_do_ids:set<DO_ID>,
    green_pid:Partition_ID
)
    requires DM_IsValidState(ws)

    requires forall id :: id in to_deactivate_drv_ids ==> id in ws.subjects.drvs
    requires forall id :: id in to_deactivate_dev_ids ==> id in ws.subjects.devs
    requires forall id :: id in devs_to_activate_in_red ==> id in ws.subjects.devs

    requires to_deactivate_external_td_ids <= MapGetKeys(ws.objects.tds)
    requires to_deactivate_external_fd_ids <= MapGetKeys(ws.objects.fds)
    requires to_deactivate_external_do_ids <= MapGetKeys(ws.objects.dos)
    requires forall s_id, o_id :: s_id in DM_AllSubjsIDs(ws.subjects) &&
                    o_id in (TDIDsToObjIDs(to_deactivate_external_td_ids) + FDIDsToObjIDs(to_deactivate_external_fd_ids) + DOIDsToObjIDs(to_deactivate_external_do_ids))
                ==> !DM_DoOwnObj(ws.subjects, s_id, o_id)
        // Requirement: No subject owns these external objects

    requires green_pid != NULL
    requires green_pid != ws.red_pid
    requires green_pid in ws.pids
        // Requirement: We have already create a green partition

    requires DM_IsSecureOps(ws, ws2)
    requires P_ExternalObjsDeactivate_ModificationToState(DMStateToState(ws), DMStateToState(ws2),
                    to_deactivate_external_td_ids, to_deactivate_external_fd_ids, to_deactivate_external_do_ids)
        // From external objects deactivation
    requires P_DMObjectsHasUniqueIDs(ws3.objects)
    requires P_WS_DrvDevDeactivate_Multi_ObjModifications(ws2, ws3, DrvIDsToSubjIDs(SeqToSet(to_deactivate_drv_ids)))
        // From drivers deactivation
    requires P_DMObjectsHasUniqueIDs(ws4.objects)
    requires P_WS_DrvDevDeactivate_Multi_ObjModifications(ws3, ws4, DevIDsToSubjIDs(SeqToSet(to_deactivate_dev_ids)))
        // From devices deactivation
    requires P_DMObjectsHasUniqueIDs(ws5.objects)
    requires P_WS_DevActivate_Multi_ObjModifications(ws4, ws5, SeqToSet(devs_to_activate_in_red), ws.red_pid)
        // From devices activation

    ensures DM_IsSecureOps(ws, ws5)
{
    assert DM_IsSecureOps(ws, ws2);
    assert DM_IsSecureOps(ws, ws3);
    assert DM_IsSecureOps(ws, ws4);
    assert DM_IsSecureOps(ws, ws5);
}