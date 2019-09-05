include "../Syntax.dfy"
include "../Utils.dfy"
include "../HCodedTD_Ops.dfy"
include "../Lemmas.dfy"

datatype ReachableTDsKParams   = ReachableTDsKParams(
                                    subjects:Subjects, objs_td_ids:set<TD_ID>, objs_fd_ids:set<FD_ID>, objs_do_ids:set<DO_ID>,
                                    hcoded_td_ids:set<TD_ID>, hcoded_tds:map<Dev_ID, TD_Val>, 
                                    objs_pids:map<Object_ID, Partition_ID>, all_active_tds:set<TD_ID>)
type TDs_Vals        = map<TD_ID, TD_Val> // Values (snapshot) of a set of TDs
type TDs_Writes_Info = map<TD_ID, set<TD_Val>>

predicate IsValidState_TDsToAllStates(k:State)
{
    // Condition: Exists a map (<tds_to_all_states>) mapping arbitary set of  
    // TDs to all their possbile values
    (forall td_ids :: td_ids in k.tds_to_all_states <==> td_ids <= MapGetKeys(k.objects.tds)) &&
        // Any subset of TDs in model state are in the k.tds_to_all_states map
    (forall td_ids, tds_state :: td_ids in k.tds_to_all_states &&
            tds_state in k.tds_to_all_states[td_ids]
        ==> TDsStateGetTDIDs(tds_state) == td_ids) &&
    (forall td_ids, tds_state :: td_ids in k.tds_to_all_states &&
            TDsStateGetTDIDs(tds_state) == td_ids
        ==> tds_state in k.tds_to_all_states[td_ids])
        // The mapped set comprises all combinations of values of these TDs
}

predicate KToKParams_PostConditions(k_params:ReachableTDsKParams)
{
    (forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids) &&
    (forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids) &&
    (forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids) &&

    (true)
}

function method KToKParams(k:State) : ReachableTDsKParams
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

    ensures KToKParams_PostConditions(KToKParams(k))
{
    ReachableTDsKParams(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos),
                                AllHCodedTDIDs(k.subjects), BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), 
                                BuildMap_ObjIDsToPIDs(k.objects), AllActiveTDs(k))
}

// From the TD write info <write_info>, pick up the ones cause new TDs' state 
// (i.e., the ones different from <tds_state>)
method TDWriteInfoCauseNewTDsState(
    tds_state:TDs_Vals, write_info:TDs_Writes_Info
) returns (new_write_info:TDs_Writes_Info)
    requires MapGetKeys<TD_ID, set<TD_Val>>(write_info) <= TDsStateGetTDIDs(tds_state)

    ensures MapGetKeys<TD_ID, set<TD_Val>>(new_write_info) == MapGetKeys<TD_ID, set<TD_Val>>(write_info)
    ensures forall td_id2 :: td_id2 in new_write_info
                ==> new_write_info[td_id2] <= write_info[td_id2]
        // Property: <new_write_info> is derived from <write_info>
    ensures forall td_id2, td_val :: td_id2 in write_info && td_val in write_info[td_id2]
                ==> (td_val == TDsStateGetTDCfg(tds_state, td_id2) ==> td_val !in new_write_info[td_id2]) &&
                    (td_val != TDsStateGetTDCfg(tds_state, td_id2) ==> td_val in new_write_info[td_id2])
        // Property: TD configurations in <write_info> must not exist in <tds_state> 
{
    var td_ids := SetToSeq<TD_ID>(MapGetKeys<TD_ID, set<TD_Val>>(write_info));
    var i := 0;
    new_write_info := map[];

    while (i < |td_ids|)
        invariant i <= |td_ids|

        invariant forall td_id2 :: td_id2 in new_write_info
                <==> td_id2 in td_ids[..i]
        invariant forall td_id2 :: td_id2 in new_write_info
                ==> new_write_info[td_id2] <= write_info[td_id2]
        invariant forall td_id2, td_val :: td_id2 in td_ids[..i] && td_val in write_info[td_id2]
                ==> (td_val == TDsStateGetTDCfg(tds_state, td_id2) ==> td_val !in new_write_info[td_id2]) &&
                    (td_val != TDsStateGetTDCfg(tds_state, td_id2) ==> td_val in new_write_info[td_id2])
    {
        var td_id := td_ids[i];
        var new_td_cfgs := set td_val | td_val in write_info[td_id] && td_val != TDsStateGetTDCfg(tds_state, td_id) :: td_val;

        new_write_info := MapConcat<TD_ID, set<TD_Val>>(new_write_info, map[td_id := new_td_cfgs]);

        i := i + 1;
    }
}

// Merge TD write info <info1> and <info2>
method TDWritesInfoMerge(
    info1:TDs_Writes_Info, info2:TDs_Writes_Info
) returns (info:TDs_Writes_Info)
    ensures forall td_id :: td_id in info
                <==> td_id in info1 || td_id in info2
        // Property: <info> merges the TD IDs in <info1>
        // and <info2>
    ensures forall td_id :: td_id in info && td_id !in info1
                ==> info[td_id] == info2[td_id]
    ensures forall td_id :: td_id in info && td_id !in info2
                ==> info[td_id] == info1[td_id]
    ensures forall td_id :: td_id in info && td_id in info1 &&
                            td_id in info2
                ==> info[td_id] == info2[td_id] + info1[td_id]
        // Property: <info> merges the TD write params in <info1>
        // and <info2>        
{
    var i := 0;
    var td_id_seq := SetToSeq<TD_ID>(MapGetKeys<TD_ID, set<TD_Val>>(info2));
    var t_info : TDs_Writes_Info := info1;

    while (i < |td_id_seq|)
        invariant forall td_id2 :: td_id2 in t_info 
                <==> td_id2 in info1 || 
                    (exists p :: 0 <= p < i && p < |td_id_seq| && td_id2 == td_id_seq[p])
        invariant forall p :: 0 <= p < i && p < |td_id_seq|
                ==> (td_id_seq[p] !in info1
                        ==> td_id_seq[p] in t_info &&
                            t_info[td_id_seq[p]] == info2[td_id_seq[p]]) &&
                    (td_id_seq[p] in info1
                        ==> td_id_seq[p] in t_info &&
                            t_info[td_id_seq[p]] == info1[td_id_seq[p]] + info2[td_id_seq[p]])
        invariant forall td_id2 :: td_id2 in t_info && td_id2 !in info2
                ==> t_info[td_id2] == info1[td_id2]
        
        invariant i <= |td_id_seq|
    {
        var td_id := td_id_seq[i];

        if (td_id !in info1)
        {    t_info := t_info[td_id := info2[td_id]];}
        else
        {    t_info := t_info[td_id := info1[td_id] + info2[td_id]];}

        i := i + 1;
    }

    info := t_info;
}




//******** Devices' Requested Access Modes  ********//
// Get all TD write transfers in the given <hcoded_transfers_tds>
function method GetTDWritesInFromHCodedTDTransfers(
    hcoded_transfers_tds:map<TD_ID, TD_Trans_Param>
) : TDs_Writes_Info
    ensures MapGetKeys(GetTDWritesInFromHCodedTDTransfers(hcoded_transfers_tds)) <= MapGetKeys(hcoded_transfers_tds)
    ensures forall td_id, td_val :: td_id in GetTDWritesInFromHCodedTDTransfers(hcoded_transfers_tds) &&
                    td_val in GetTDWritesInFromHCodedTDTransfers(hcoded_transfers_tds)[td_id]
                <==> TDWriteTransferInTD(hcoded_transfers_tds, td_id, td_val)
{
    map td_id | td_id in hcoded_transfers_tds &&
                W in hcoded_transfers_tds[td_id].amodes
                        // Hardcoded write to the TD (<td_id>)
              :: hcoded_transfers_tds[td_id].vals
}




//******** TDs' States ********//
// Return the updates from <old_tds_state> to <new_tds_state>
function method TDsStateDiff(new_tds_state:TDs_Vals, old_tds_state:TDs_Vals):map<TD_ID, TD_Val>
    requires TDsStateGetTDIDs(new_tds_state) == TDsStateGetTDIDs(old_tds_state)

    ensures MapGetKeys<TD_ID, TD_Val>(TDsStateDiff(new_tds_state, old_tds_state)) <= TDsStateGetTDIDs(new_tds_state)
        // Property: The diff does not contain any new TD ID not in <new_tds_state>
    ensures forall td_id :: td_id in TDsStateDiff(new_tds_state, old_tds_state)
                ==> TDsStateDiff(new_tds_state, old_tds_state)[td_id] != old_tds_state[td_id]
        // Property: The diff of TDs' state is new
    ensures forall td_id :: td_id in new_tds_state
                ==> (td_id in TDsStateDiff(new_tds_state, old_tds_state)
                        ==> new_tds_state[td_id] == TDsStateDiff(new_tds_state, old_tds_state)[td_id]) &&
                    (td_id !in TDsStateDiff(new_tds_state, old_tds_state)
                        ==> new_tds_state[td_id] == old_tds_state[td_id])
        // Property: The new TD state equals to the known TD state replaced with the diff
{
    map td_id | td_id in TDsStateGetTDIDs(new_tds_state) && 
                new_tds_state[td_id] != old_tds_state[td_id]
            ::  new_tds_state[td_id]
}

// Returns all TDs' states, due to any combinations of TDs' writes (i.e., by
// applying 0 or 1 new config in <tds_dev_writes> to each TD) to <tds_state>.
// In other words, <tds_states> holds all TDs' states due to any 0+ TD writes 
// (according to <tds_dev_writes>) to <tds_state>
method TDsWritesInfoToTDsStates(
    tds_state:TDs_Vals, tds_dev_writes:TDs_Writes_Info
) returns (tds_states:set<TDs_Vals>)
    requires MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) <= TDsStateGetTDIDs(tds_state)
    requires forall td_id2 :: td_id2 in tds_dev_writes
                    ==> TDsStateGetTDCfg(tds_state, td_id2) !in tds_dev_writes[td_id2]
        // Requirement: New TD configurations in <tds_dev_writes> must not 
        // exist in <tds_state>

    ensures forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state)
    ensures forall tds_state2, td_id2 :: tds_state2 in tds_states && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> (TDsStateGetTDCfg(tds_state2, td_id2) == TDsStateGetTDCfg(tds_state, td_id2) ||
                        (td_id2 in tds_dev_writes &&
                        TDsStateGetTDCfg(tds_state2, td_id2) in tds_dev_writes[td_id2]))
        // Property: Foreach result TDs' state, it is <tds_state> overwritten 
        // with <tds_dev_writes>
    ensures forall tds_diff:map<TD_ID, TD_Val> :: 
                MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                (forall td_id2 :: td_id2 in tds_diff ==> tds_diff[td_id2] in tds_dev_writes[td_id2])
                ==> (exists tds_state2 :: tds_state2 in tds_states && TDsStateDiff(tds_state2, tds_state) == tds_diff)
        // Property: Foreach <tds_diff> in tds_dev_writes, there is a state 
        // result from the <tds_diff>
    ensures tds_state in tds_states

    decreases |MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes)|
{
    if(tds_dev_writes == map[])
    {    return {tds_state}; }
    else
    {
        var td_id :| td_id in tds_dev_writes;
        var td_cfgs := SetToSeq<TD_Val>(tds_dev_writes[td_id] + {TDsStateGetTDCfg(tds_state, td_id)}); // choose 0 or 1 new config
        var i := 0;
        var tds_dev_writes_step := MapRemoveKey<TD_ID, set<TD_Val>>(tds_dev_writes, td_id);
        tds_states := {tds_state};
        assert forall i, j :: 0 <= i < |td_cfgs| && 0 <= j < |td_cfgs|
                ==> (i == j <==> td_cfgs[i] == td_cfgs[j]);

        // DFS
        while (i < |td_cfgs|)
            invariant i <= |td_cfgs|

            invariant forall tds_state2 :: tds_state2 in tds_states
                ==> TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state)
            invariant tds_state in tds_states
    
            invariant forall tds_state2, td_id2 :: tds_state2 in tds_states && td_id2 in TDsStateGetTDIDs(tds_state2)
                ==> (TDsStateGetTDCfg(tds_state2, td_id2) == TDsStateGetTDCfg(tds_state, td_id2) ||
                        (td_id2 in tds_dev_writes &&
                        TDsStateGetTDCfg(tds_state2, td_id2) in tds_dev_writes[td_id2]))
            invariant forall td_val :: td_val in td_cfgs[..i]
                ==> (forall tds_diff:map<TD_ID, TD_Val> ::
                        MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                        (forall td_id2 :: td_id2 in tds_diff && td_id2 != td_id ==> tds_diff[td_id2] in tds_dev_writes[td_id2]) &&
                        (td_id in tds_diff ==> tds_diff[td_id] == td_val && td_val != TDsStateGetTDCfg(tds_state, td_id))&&
                        (td_id !in tds_diff ==> td_val == TDsStateGetTDCfg(tds_state, td_id))
                    ==> (exists tds_state2 :: tds_state2 in tds_states && TDsStateDiff(tds_state2, tds_state) == tds_diff))
        {
            var td_val := td_cfgs[i];
            var tds_new_state := TDsStateUpdateTD(tds_state, td_id, td_val);
            assert TDsStateGetTDCfg(tds_new_state, td_id) in td_cfgs;

            var tds_states_next := TDsWritesInfoToTDsStates(tds_new_state, tds_dev_writes_step);

            forall td_cfg2, tds_diff:map<TD_ID, TD_Val> | 
                        td_cfg2 in td_cfgs[..i+1] &&
                        MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes) &&
                        (forall td_id2 :: td_id2 in tds_diff && td_id2 != td_id ==> tds_diff[td_id2] in tds_dev_writes[td_id2]) &&
                        (td_id in tds_diff ==> tds_diff[td_id] == td_cfg2 && td_cfg2 != TDsStateGetTDCfg(tds_state, td_id)) &&
                        (td_id !in tds_diff ==> td_cfg2 == TDsStateGetTDCfg(tds_state, td_id))
                    ensures exists tds_state2 :: tds_state2 in (tds_states + tds_states_next) && 
                            TDsStateDiff(tds_state2, tds_state) == tds_diff
            {
                if (td_cfg2 == td_cfgs[i])
                {
                    var tds_diff2 := map td_id2 | td_id2 in tds_diff && td_id2 != td_id :: tds_diff[td_id2];
                    assert td_cfg2 == td_val;
                    assert MapGetKeys<TD_ID, TD_Val>(tds_diff) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes);
                    assert (forall td_id2 :: td_id2 in tds_diff && td_id2 != td_id ==> tds_diff[td_id2] in tds_dev_writes[td_id2]) &&
                        (td_id in tds_diff ==> tds_diff[td_id] == td_val && td_val != TDsStateGetTDCfg(tds_state, td_id)) &&
                        (td_id !in tds_diff ==> td_val == TDsStateGetTDCfg(tds_state, td_id));

                    assert MapGetKeys<TD_ID, TD_Val>(tds_diff2) <= MapGetKeys<TD_ID, set<TD_Val>>(tds_dev_writes_step) &&
                        (forall td_id2 :: td_id2 in tds_diff2 ==> tds_diff2[td_id2] in tds_dev_writes_step[td_id2]);
                    assert (exists tds_state2 :: tds_state2 in tds_states_next && TDsStateDiff(tds_state2, tds_new_state) == tds_diff2);
                    forall tds_state2 | tds_state2 in tds_states_next && 
                            TDsStateDiff(tds_state2, tds_new_state) == tds_diff2
                        ensures TDsStateDiff(tds_state2, tds_state) == tds_diff
                    {
                        assert tds_new_state == tds_state[td_id := td_val];

                        if(td_id in tds_diff)
                        {
                            assert tds_diff == tds_diff2[td_id := td_val];
                            assert TDsStateDiff(tds_state2, tds_state) == tds_diff;
                        }
                        else
                        {
                            assert tds_diff == tds_diff2;
                            assert tds_state[td_id] == td_val;
                            assert TDsStateDiff(tds_state2, tds_state) == tds_diff;
                        }
                    }

                    assert exists tds_state2 :: tds_state2 in tds_states_next && 
                            TDsStateDiff(tds_state2, tds_state) == tds_diff;
                }
                else
                {
                    assert td_cfg2 in td_cfgs[..i];
                    assert exists tds_state2 :: tds_state2 in (tds_states + tds_states_next) && 
                            TDsStateDiff(tds_state2, tds_state) == tds_diff;
                }
            }

            tds_states := tds_states + tds_states_next;

            i := i + 1;
        }
        assert forall td_val :: td_val in td_cfgs[..i] <==> td_val in td_cfgs;
    }
}

// Append a set of TDs and their values to each TDs' state in <tds_states>
ghost method TDsStatesAppendTDsInEach(tds_states:seq<TDs_Vals>, add_td_ids_vals:map<TD_ID, TD_Val>) returns (result_tds_states:seq<TDs_Vals>)
    requires forall tds_state :: tds_state in tds_states
                ==> MapGetKeys<TD_ID, TD_Val>(tds_state) * MapGetKeys<TD_ID, TD_Val>(add_td_ids_vals) == {}
        // Requirement: <add_td_ids_vals> does not include TDs in <tds_states>

    ensures |tds_states| == |result_tds_states|
    ensures forall i :: 0 <= i < |tds_states|
                ==> (MapGetKeys<TD_ID, TD_Val>(result_tds_states[i]) == MapGetKeys<TD_ID, TD_Val>(tds_states[i]) + 
                                                                          MapGetKeys<TD_ID, TD_Val>(add_td_ids_vals)) &&
                    (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(tds_states[i])
                        ==> result_tds_states[i][td_id] == tds_states[i][td_id]) &&
                    (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(add_td_ids_vals)
                        ==> result_tds_states[i][td_id] == add_td_ids_vals[td_id])
{
    var i := 0;
    result_tds_states := [];

    while (i < |tds_states|)
        invariant i <= |tds_states|

        invariant |result_tds_states| == i
        invariant forall p :: 0 <= p < i
                    ==> (MapGetKeys<TD_ID, TD_Val>(result_tds_states[p]) == MapGetKeys<TD_ID, TD_Val>(tds_states[p]) + 
                                                                              MapGetKeys<TD_ID, TD_Val>(add_td_ids_vals)) &&
                        (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(tds_states[p])
                            ==> result_tds_states[p][td_id] == tds_states[p][td_id]) &&
                        (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(add_td_ids_vals)
                            ==> result_tds_states[p][td_id] == add_td_ids_vals[td_id])
    {
        var tds_state := tds_states[i];

        Lemma_SetsHaveEmptyIntersectionHasNoCommonElems<TD_ID>(MapGetKeys<TD_ID, TD_Val>(tds_state), 
            MapGetKeys<TD_ID, TD_Val>(add_td_ids_vals));
        var new_tds_state := MapConcat<TD_ID, TD_Val>(tds_state, add_td_ids_vals);

        result_tds_states := SeqAppend<TDs_Vals>(result_tds_states, new_tds_state);
        i := i + 1;
    }
}

// Remove a set of TDs from each TDs' state in <tds_states>
ghost method TDsStatesRemoveTDsInEach(tds_states:seq<TDs_Vals>, remove_td_ids:set<TD_ID>) returns (result_tds_states:seq<TDs_Vals>)
    requires forall tds_state :: tds_state in tds_states
                ==> remove_td_ids <= MapGetKeys<TD_ID, TD_Val>(tds_state)

    ensures |tds_states| == |result_tds_states|
    ensures forall i :: 0 <= i < |tds_states|
                ==> (MapGetKeys<TD_ID, TD_Val>(result_tds_states[i]) == MapGetKeys<TD_ID, TD_Val>(tds_states[i]) - remove_td_ids) &&
                    (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(tds_states[i]) && td_id !in remove_td_ids 
                        ==> result_tds_states[i][td_id] == tds_states[i][td_id]) &&
                    (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(tds_states[i]) && td_id in remove_td_ids 
                        ==> td_id !in result_tds_states[i])
{
    var i := 0;
    result_tds_states := [];

    while (i < |tds_states|)
        invariant i <= |tds_states|

        invariant |result_tds_states| == i
        invariant forall p :: 0 <= p < i
                    ==> (MapGetKeys<TD_ID, TD_Val>(result_tds_states[p]) == MapGetKeys<TD_ID, TD_Val>(tds_states[p]) - remove_td_ids) &&
                        (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(tds_states[p]) && td_id !in remove_td_ids 
                            ==> result_tds_states[p][td_id] == tds_states[p][td_id]) &&
                        (forall td_id :: td_id in MapGetKeys<TD_ID, TD_Val>(tds_states[p]) && td_id in remove_td_ids 
                            ==> td_id !in result_tds_states[p])
    {
        var tds_state := tds_states[i];
        var new_tds_state := MapRemoveKeys<TD_ID, TD_Val>(tds_state, remove_td_ids);

        result_tds_states := SeqAppend<TDs_Vals>(result_tds_states, new_tds_state);
        i := i + 1;
    }
}

// Lemma: <tds_state1> == <tds_state2> iff 
// TDsStateDiff(tds_state1, base_state) == TDsStateDiff(tds_state2, base_state)
lemma Lemma_SameTDsStateIffSameDiffWithATDState()
    ensures forall tds_state1, tds_state2, base_state ::
            TDsStateGetTDIDs(tds_state1) == TDsStateGetTDIDs(base_state) &&
            TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(base_state)
            ==> (tds_state1 == tds_state2
                    <==> TDsStateDiff(tds_state1, base_state) == TDsStateDiff(tds_state2, base_state))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_TDsStateDiffAreUnchangedAfterAppendedWithMoreTDs(
    tds_state1:TDs_Vals, tds_state1':TDs_Vals, add_tds:map<TD_ID, TD_Val>, tds_state2:TDs_Vals, tds_state2':TDs_Vals
)
    requires TDsStateGetTDIDs(tds_state1) == TDsStateGetTDIDs(tds_state1')
    requires TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state2')
    requires MapGetKeys<TD_ID, TD_Val>(add_tds) * TDsStateGetTDIDs(tds_state1) == {}
    requires TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state1) + MapGetKeys<TD_ID, TD_Val>(add_tds)
        
    requires add_tds ==  MapSubmap(tds_state2, MapGetKeys(add_tds))

    requires tds_state1 == MapRemoveKeys<TD_ID, TD_Val>(tds_state2, MapGetKeys(add_tds))
    requires tds_state1' == MapRemoveKeys<TD_ID, TD_Val>(tds_state2', MapGetKeys(add_tds))
    requires forall td_id :: td_id in add_tds
                ==> tds_state2'[td_id] == tds_state2[td_id];
        // Requirement: tds_state2/tds_state2' is tds_state1/tds_state1' appended with <add_tds>

    ensures TDsStateDiff(tds_state2', tds_state2) == TDsStateDiff(tds_state1', tds_state1)
{
    forall td_id | td_id in TDsStateGetTDIDs(tds_state2)
        ensures (td_id in TDsStateGetTDIDs(tds_state1) ==> tds_state2[td_id] == tds_state1[td_id]) &&
                (td_id in MapGetKeys<TD_ID, TD_Val>(add_tds) ==> tds_state2[td_id] == add_tds[td_id])
    {
        if(td_id in TDsStateGetTDIDs(tds_state1))
        {
            assert tds_state2[td_id] == tds_state1[td_id];
        }

        if(td_id in MapGetKeys<TD_ID, TD_Val>(add_tds))
        {
            if (tds_state2[td_id] != add_tds[td_id])
            {}
        }
    }
}

lemma Lemma_AddTDs_Property(
    tds_state1:TDs_Vals, add_tds:map<TD_ID, TD_Val>, tds_state2:TDs_Vals
)
    requires MapGetKeys<TD_ID, TD_Val>(add_tds) * TDsStateGetTDIDs(tds_state1) == {}
    requires forall k1, k2 :: k1 in add_tds && k2 in tds_state1 ==> k1 != k2
    requires TDsStateGetTDIDs(tds_state2) == TDsStateGetTDIDs(tds_state1) + MapGetKeys<TD_ID, TD_Val>(add_tds)
    requires tds_state2 == MapConcat<TD_ID, TD_Val>(tds_state1, add_tds)
    
    ensures tds_state1 == MapRemoveKeys<TD_ID, TD_Val>(tds_state2, MapGetKeys(add_tds))
{
    // Dafny can automatically prove this lemma
}




//******** TDs' State ********//
function method GetTDVal(k:State, td_id:TD_ID) : TD_Val
    requires td_id in k.objects.tds
{
    k.objects.tds[td_id].val
}

// Returns the TD IDs recorded in <tds_states>
function method TDsStateGetTDIDs(tds_state:TDs_Vals) : set<TD_ID>
{
    MapGetKeys<TD_ID, TD_Val>(tds_state)
}

function method TDsStateGetTDCfg(tds_state:TDs_Vals, td_id:TD_ID) : TD_Val
    requires td_id in TDsStateGetTDIDs(tds_state)
{
    tds_state[td_id]
}

predicate DoesTDValContainWriteToTD(td:TD_Val)
{
    (exists td_id2 :: td_id2 in td.trans_params_tds &&
        W in td.trans_params_tds[td_id2].amodes)
}

function method GetTDWritingValsToTD(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID) : set<TD_Val>
    requires td_id in tds_state
    requires IsTDRefTDWithAModes(tds_state, td_id, target_td_id, {W})
    ensures GetTDWritingValsToTD(tds_state, td_id, target_td_id) == 
            GetTDWritingValsToTD_FromTransParams(tds_state[td_id], target_td_id)
{
    GetTDWritingValsToTD_FromTransParams(tds_state[td_id], target_td_id)
}

function method GetTDWritingValsToTD_FromTransParams(
    td_val:TD_Val, target_td_id:TD_ID
) : set<TD_Val>
    requires IsTDRefTDWithAModes_FromTransParams(td_val, target_td_id, {W})
{
    td_val.trans_params_tds[target_td_id].vals
}

// If the target TD (<target_td_id>) is refed by the TD (<td_id>) with 
// indicated access modes
function method IsTDRefTDWithAModes(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID, amodes:set<AMode>) : bool
    requires td_id in tds_state
    ensures IsTDRefTDWithAModes(tds_state, td_id, target_td_id, amodes) ==
            IsTDRefTDWithAModes_FromTransParams(tds_state[td_id], target_td_id, amodes)
{
    IsTDRefTDWithAModes_FromTransParams(tds_state[td_id], target_td_id, amodes)
}

function method IsTDRefTDWithAModes_FromTransParams(
    td_val:TD_Val, target_td_id:TD_ID, amodes:set<AMode>) : bool
{
    if (target_td_id in td_val.trans_params_tds &&
        (amodes <= td_val.trans_params_tds[target_td_id].amodes))
    then true
    else false
}

// If the target FD (<target_fd_id>) is refed by the TD (<td_id>) with 
// indicated access modes
function method IsTDRefFDWithAModes(
    tds_state:TDs_Vals, td_id:TD_ID, target_fd_id:FD_ID, amodes:set<AMode>) : bool
    requires td_id in tds_state
{
    if (target_fd_id.oid in GetObjIDsRefedInTD(tds_state, td_id) &&
        amodes <= GetAModesOfObjRefedInTD(tds_state, td_id, target_fd_id.oid))
    then true
    else false
}

// If the target DO (<target_do_id>) is refed by the TD (<td_id>) with 
// indicated access modes
function method IsTDRefDOWithAModes(
    tds_state:TDs_Vals, td_id:TD_ID, target_do_id:DO_ID, amodes:set<AMode>) : bool
    requires td_id in tds_state
{
    if (target_do_id.oid in GetObjIDsRefedInTD(tds_state, td_id) &&
        amodes <= GetAModesOfObjRefedInTD(tds_state, td_id, target_do_id.oid))
    then true
    else false
}

// Returns if the TD (<td_id>) in the TDs' state (<tds_state>) references the 
// target TD (<target_td_id>) with a W access mode and the new state <td_new_state>
function method IsTDWriteInTD(
    tds_state:TDs_Vals, td_id:TD_ID, target_td_id:TD_ID, td_new_state:TD_Val
) : bool
    requires td_id in tds_state
{
    if( IsTDRefTDWithAModes(tds_state, td_id, target_td_id, {W}) &&
        td_new_state in GetTDWritingValsToTD(tds_state, td_id, target_td_id))
    then true
    else false
}

// Returns object IDs referenced in the TD (<td_id>)
function method GetObjIDsRefedInTD(tds_state:TDs_Vals, td_id:TD_ID) : set<Object_ID>
    requires td_id in tds_state
{
    (set ref_td_id:TD_ID | ref_td_id in tds_state[td_id].trans_params_tds 
        :: ref_td_id.oid) +
    (set ref_fd_id:FD_ID | ref_fd_id in tds_state[td_id].trans_params_fds 
        :: ref_fd_id.oid) +
    (set ref_do_id:DO_ID | ref_do_id in tds_state[td_id].trans_params_dos 
        :: ref_do_id.oid)
}

// Returns object IDs referenced in the TD (<td_id>) with non-empty requested
// access modes
function method GetObjIDsRefedInTDWithNonEmptyAModes(tds_state:TDs_Vals, td_id:TD_ID) : set<Object_ID>
    requires td_id in tds_state
    ensures GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, td_id) <= GetObjIDsRefedInTD(tds_state, td_id)
    ensures forall o_id2 :: o_id2 in GetObjIDsRefedInTDWithNonEmptyAModes(tds_state, td_id)
                <==> (o_id2 in GetObjIDsRefedInTD(tds_state, td_id) &&
                        GetAModesOfObjRefedInTD(tds_state, td_id, o_id2) != {})
{
    set o_id2 | o_id2 in GetObjIDsRefedInTD(tds_state, td_id) &&
                GetAModesOfObjRefedInTD(tds_state, td_id, o_id2) != {}
        :: o_id2
}

// Returns the requested access modes of the object, as recorded in the TD (<td_id>)
// [Note] This function can further define DoTDDefTransferToObj; i.e.,
// DoTDDefTransferToObj() = true, iff o_id in GetObjIDsRefedInTD(tds_state, td_id), 
// and GetAModesOfObjRefedInTD() != {}
function method GetAModesOfObjRefedInTD(tds_state:TDs_Vals, td_id:TD_ID, o_id:Object_ID) : set<AMode>
    requires td_id in tds_state
    requires o_id in GetObjIDsRefedInTD(tds_state, td_id)
{
    if (TD_ID(o_id) in tds_state[td_id].trans_params_tds) then
        tds_state[td_id].trans_params_tds[TD_ID(o_id)].amodes
    else if (FD_ID(o_id) in tds_state[td_id].trans_params_fds) then
        tds_state[td_id].trans_params_fds[FD_ID(o_id)].amodes
    else
        tds_state[td_id].trans_params_dos[DO_ID(o_id)].amodes
}

// If the target object (<target_obj_id>) is refed by the TD (<td_id>) with 
// indicated access modes
function method IsTDRefObjWithAModes(
    tds_state:TDs_Vals, td_id:TD_ID, target_obj_id:Object_ID, amodes:set<AMode>) : bool
    requires td_id in tds_state
{
    if (target_obj_id in GetObjIDsRefedInTD(tds_state, td_id) &&
        amodes <= GetAModesOfObjRefedInTD(tds_state, td_id, target_obj_id))
    then true
    else false    
}

function method TDsStateUpdateTD(tds_state:TDs_Vals, td_id:TD_ID, td_val:TD_Val) : TDs_Vals
    requires td_id in tds_state
    ensures TDsStateGetTDIDs(TDsStateUpdateTD(tds_state, td_id, td_val)) == TDsStateGetTDIDs(tds_state)
    ensures TDsStateUpdateTD(tds_state, td_id, td_val) == tds_state[td_id := td_val]
{
    tds_state[td_id := td_val]
}




//******** TD's Configuration ********//
// Returns all TD writes requested in the TD configuration (<td_val>)
function method TDWritesInTDCfg(td_val:TD_Val) : TDs_Writes_Info
    ensures forall td_id2 :: td_id2 in TDWritesInTDCfg(td_val) 
                ==> td_id2 in td_val.trans_params_tds && 
                    IsTDRefTDWithAModes_FromTransParams(td_val, td_id2, {W}) &&
                    TDWritesInTDCfg(td_val)[td_id2] == GetTDWritingValsToTD_FromTransParams(td_val, td_id2)
        // Property: The result are derived from the <td_val>
    ensures forall td_id2 :: td_id2 in td_val.trans_params_tds &&
                    IsTDRefTDWithAModes_FromTransParams(td_val, td_id2, {W})
                ==> td_id2 in TDWritesInTDCfg(td_val) &&
                    TDWritesInTDCfg(td_val)[td_id2] == GetTDWritingValsToTD_FromTransParams(td_val, td_id2)
        // Property: Forall writes to TDs (<td_id2>), the write info is in the result
{
    map td_id | td_id in td_val.trans_params_tds &&
                IsTDRefTDWithAModes_FromTransParams(td_val, td_id, {W})
                :: GetTDWritingValsToTD_FromTransParams(td_val, td_id)
}

// Returns all IDs of TDs read in (<td_val>)
function method TDIDReadsInTDCfg(td_val:TD_Val) : set<TD_ID>
    ensures forall td_id2 :: td_id2 in TDIDReadsInTDCfg(td_val)
                <==> td_id2 in td_val.trans_params_tds && 
                    IsTDRefTDWithAModes_FromTransParams(td_val, td_id2, {R})
{
    set ref_td_id | ref_td_id in td_val.trans_params_tds &&
                IsTDRefTDWithAModes_FromTransParams(td_val, ref_td_id, {R})
        :: ref_td_id
}

predicate DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params:ReachableTDsKParams)
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

// If the TD refs an object not in the I/O system, or refs an inactive
// object with non-empty requested access mode.
function method DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID
) : bool
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    ensures DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                k_params, tds_state, td_id)
            <==> (exists td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
                && (td_id2 !in k_params.objs_td_ids || td_id2 in k_params.hcoded_td_ids ||
                    (ObjPID_SlimState(k_params.objs_pids, td_id2.oid) !=
                        ObjPID_SlimState(k_params.objs_pids, td_id.oid) && 
                     tds_state[td_id].trans_params_tds[td_id2].amodes != {}))) || 
                (exists fd_id2 :: fd_id2 in tds_state[td_id].trans_params_fds
                && (fd_id2 !in k_params.objs_fd_ids || 
                    (ObjPID_SlimState(k_params.objs_pids, fd_id2.oid) !=
                        ObjPID_SlimState(k_params.objs_pids, td_id.oid) && 
                     tds_state[td_id].trans_params_fds[fd_id2].amodes != {}))) || 
                (exists do_id2 :: do_id2 in tds_state[td_id].trans_params_dos
                && (do_id2 !in k_params.objs_do_ids || 
                    (ObjPID_SlimState(k_params.objs_pids, do_id2.oid) != 
                        ObjPID_SlimState(k_params.objs_pids, td_id.oid) && 
                     tds_state[td_id].trans_params_dos[do_id2].amodes != {})))
{
    if (forall td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
            ==> td_id2 in k_params.objs_td_ids &&
                td_id2 !in k_params.hcoded_td_ids &&
                (ObjPID_SlimState(k_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_tds[td_id2].amodes == {})) &&
                        // The TD does not contain a transfer to the target TD
        (forall fd_id2 :: fd_id2 in tds_state[td_id].trans_params_fds
            ==> fd_id2 in k_params.objs_fd_ids &&
                ((ObjPID_SlimState(k_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)) ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_fds[fd_id2].amodes == {})) &&
                        // The TD does not contain a transfer to the target FD
        (forall do_id2 :: do_id2 in tds_state[td_id].trans_params_dos
            ==> do_id2 in k_params.objs_do_ids && 
                (ObjPID_SlimState(k_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_dos[do_id2].amodes == {}))
                        // The TD does not contain a transfer to the target DO
    then false
    else true
}

// If the TD refs an object not in the I/O system, or refs an inactive
// object with non-empty requested access mode.
function method DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID
) : bool
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    ensures DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, tds_state, td_id)
            <==> (exists td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
                && (td_id2 !in k_params.objs_td_ids || td_id2 in k_params.hcoded_td_ids)) || 
                (exists fd_id2 :: fd_id2 in tds_state[td_id].trans_params_fds
                && (fd_id2 !in k_params.objs_fd_ids)) || 
                (exists do_id2 :: do_id2 in tds_state[td_id].trans_params_dos
                && (do_id2 !in k_params.objs_do_ids))
{
    if (forall td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
            ==> td_id2 in k_params.objs_td_ids &&
                td_id2 !in k_params.hcoded_td_ids) &&
                        // All transfers point to existing TDs and not hardcoded TDs
        (forall fd_id2 :: fd_id2 in tds_state[td_id].trans_params_fds
            ==> fd_id2 in k_params.objs_fd_ids) &&
                        // All transfers point to existing FDs
        (forall do_id2 :: do_id2 in tds_state[td_id].trans_params_dos
            ==> do_id2 in k_params.objs_do_ids)
                        // All transfers point to existing DOs
    then false
    else true
}

function method DoActiveTDIncludeTransfersToObjOutsidePartition(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID
) : bool
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    requires !DoActiveTDIncludeTransfersToNonExistingObjsOrHCodedTDs(k_params, tds_state, td_id)
   
    ensures DoActiveTDIncludeTransfersToObjOutsidePartition(k_params, tds_state, td_id)
              <==> DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id)
{
    if (forall td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
            ==> (ObjPID_SlimState(k_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_tds[td_id2].amodes == {})) &&
                        // The TD does not contain a transfer to the target TD
        (forall fd_id2 :: fd_id2 in tds_state[td_id].trans_params_fds
            ==> ((ObjPID_SlimState(k_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)) ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_fds[fd_id2].amodes == {})) &&
                        // The TD does not contain a transfer to the target FD
        (forall do_id2 :: do_id2 in tds_state[td_id].trans_params_dos
            ==> (ObjPID_SlimState(k_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 tds_state[td_id].trans_params_dos[do_id2].amodes == {}))
                        // The TD does not contain a transfer to the target DO
    then false
    else true
}




//******** Utility Lemmas ********//
lemma Lemma_KToKParams_KParamsFulfillPropertiesInKIsValid(k:State, k_params:ReachableTDsKParams)
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

    requires k_params == KToKParams(k)

    ensures forall td_id2 :: td_id2 in k_params.objs_td_ids
                ==> td_id2.oid in k_params.objs_pids
    ensures forall fd_id2 :: fd_id2 in k_params.objs_fd_ids
                ==> fd_id2.oid in k_params.objs_pids
    ensures forall do_id2 :: do_id2 in k_params.objs_do_ids
                ==> do_id2.oid in k_params.objs_pids
        // Requirement: All Object IDs must be in <k_params.objs_pids>
    ensures forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL
        // Requirement: <k_params.all_active_tds> holds all active TDs
    ensures MapGetKeys(k_params.hcoded_tds) == MapGetKeys(k_params.subjects.devs)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SameTDIDsInTDsStateIfTDIDsSetIsSame(tds:TDs_Vals, tds':TDs_Vals)
    requires forall td_id :: td_id in tds <==> td_id in tds'
    ensures TDsStateGetTDIDs(tds') == TDsStateGetTDIDs(tds) 
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_TDsStateGetTDIDs_SameResultWithMapGetKeys(tds:TDs_Vals)
    ensures TDsStateGetTDIDs(tds) == MapGetKeys(tds)
{
    // Dafny can automatically prove this lemma.
}

// Lemma: The differences between <tds> and <tds'> must be recorded in 
// <td_id_val_map>
lemma Lemma_TDsStatesDiffIsIncludedInTDIDValMapOfWriteTDs(tds:TDs_Vals, tds':TDs_Vals, td_id_val_map:map<TD_ID, TD_Val>)
    requires forall td_id:: td_id in td_id_val_map ==> td_id in tds
    requires forall td_id :: td_id in tds <==> td_id in tds' 
    requires forall td_id :: td_id in tds
                ==> (td_id in td_id_val_map ==> tds'[td_id] == td_id_val_map[td_id]) &&
                    (td_id !in td_id_val_map ==> tds'[td_id] == tds[td_id])
        // Property: The values in <td_id_val_map> is written into <tds'>

    ensures forall td_id :: td_id in TDsStateDiff(tds', tds)
                ==>  td_id in td_id_val_map &&
                     TDsStateDiff(tds', tds)[td_id] == td_id_val_map[td_id];
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_GetObjIDsRefedInTD_Property(tds_state:TDs_Vals, td_id:TD_ID)
    requires td_id in tds_state
    requires tds_state[td_id].trans_params_tds == map[] &&
             tds_state[td_id].trans_params_fds == map[] &&
             tds_state[td_id].trans_params_dos == map[]

    ensures GetObjIDsRefedInTD(tds_state, td_id) == {}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DoesTDsStateContainWriteToTD_EmptyTDMustReturnFalse(td:TD_Val)
    requires td == TD_Val(map[], map[], map[])

    ensures !DoesTDValContainWriteToTD(td)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_EmptyTDMustReturnFalse(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID
)
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active

    requires tds_state[td_id] == TD_Val(map[], map[], map[])

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                k_params, tds_state, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_EquivilantTDReturnsSameResult(
    k_params:ReachableTDsKParams,
    tds_state1:TDs_Vals, tds_state2:TDs_Vals, td_id:TD_ID
)
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
    // Requirements required by functions in this function method

    requires TDsStateGetTDIDs(tds_state1) == k_params.all_active_tds
    requires TDsStateGetTDIDs(tds_state2) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state1
    requires td_id in tds_state2
        // Requirement: The TD (<td_id>) is active
    requires tds_state1[td_id] == tds_state2[td_id]

    ensures DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                k_params, tds_state1, td_id)
            <==>
            DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(
                k_params, tds_state2, td_id)

{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevsOwnHCodedTDs(k_subjects:Subjects, dev_id:Dev_ID, hcoded_td_id:TD_ID)
    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs

    requires forall dev_id :: dev_id in k_subjects.devs
                ==> k_subjects.devs[dev_id].hcoded_td_id in k_subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices

    requires IsDevID_SlimState(k_subjects, dev_id)

    requires hcoded_td_id == k_subjects.devs[dev_id].hcoded_td_id

    ensures DoOwnObj_SlimState(k_subjects, dev_id.sid, hcoded_td_id.oid)
{
    var s_id := dev_id.sid;
    var o_id := hcoded_td_id.oid;
    assert Dev_ID(s_id) in k_subjects.devs;

    assert (TD_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].td_ids) ||
        (FD_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].fd_ids) ||
        (DO_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].do_ids);
}

lemma Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Prove(
    k_params:ReachableTDsKParams,
    k_tds_state:TDs_Vals, td_id:TD_ID
)
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
    requires TDsStateGetTDIDs(k_tds_state) == k_params.all_active_tds
    requires td_id in k_tds_state

    requires forall td_id2 :: td_id2 in k_tds_state[td_id].trans_params_tds
            ==> td_id2 in k_params.objs_td_ids &&
                td_id2 !in k_params.hcoded_td_ids &&
                (ObjPID_SlimState(k_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 k_tds_state[td_id].trans_params_tds[td_id2].amodes == {})
    requires forall fd_id2 :: fd_id2 in k_tds_state[td_id].trans_params_fds
            ==> fd_id2 in k_params.objs_fd_ids &&
                ((ObjPID_SlimState(k_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid)) ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 k_tds_state[td_id].trans_params_fds[fd_id2].amodes == {})
    requires forall do_id2 :: do_id2 in k_tds_state[td_id].trans_params_dos
            ==> do_id2 in k_params.objs_do_ids && 
                (ObjPID_SlimState(k_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k_params.objs_pids, td_id.oid) ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 k_tds_state[td_id].trans_params_dos[do_id2].amodes == {})

    ensures !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id)
{
    // Dafny can automatically prove this lemma
}