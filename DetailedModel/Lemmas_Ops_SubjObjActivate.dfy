include "../Abstract/Model.dfy"
include "Lemmas_Ops_Common.dfy"
include "Util_Lemmas.dfy"
include "Utils_DevsActivateCond.dfy"
include "Properties_SecureDMState.dfy"

// (needs 20s to verify)
lemma Lemma_NewDM_SubjObjActivate_FulfillSI2(
    ws:DM_State, k:State, ws':DM_State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires pid != NULL

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)
    requires forall td_id2, td_id3 :: td_id2 in AllHCodedTDIDs(k.subjects) && 
                    td_id2 in toactivate_td_ids &&
                    td_id3 in k.objects.tds[td_id2].val.trans_params_tds
                ==> W !in k.objects.tds[td_id2].val.trans_params_tds[td_id3].amodes
        // Requirement: If a hardcoded TD is going to be activated, then
        // it must not contain any write transfers to TDs

    requires (forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))

    ensures (forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id))
{
    if(pid == ws.red_pid)
    {
        assert DM_TDIDsInGreen(ws') == DM_TDIDsInGreen(ws);
        Lemma_NewDM_FulfillSI2_IfGreenTDsAreUnchanged(ws, k, ws', k');
    }
    else
    {
        Lemma_NewDM_SubjObjActivate_FulfillSI2_ActivateIntoGreenPartition(ws, k, ws', k',
            toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    }
}

lemma Lemma_DM_DevActivate_ProveCheckOfDevActivateInK(
    ws:DM_State, k:State, dev_sid:Subject_ID, pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires k == DMStateToState(ws)

    requires dev_sid in DM_AllSubjsIDs(ws.subjects)

    requires DM_SubjPID(ws.subjects, dev_sid) == NULL && pid in ws.pids
    
    ensures (SubjPID(k, dev_sid) == NULL) && (pid in k.pids)
{
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(ws, k);
}

lemma Lemma_NewDM_DevActivate_OtherDevsHaveUnchangedPIDs(
    ws:DM_State, ws':DM_State, wimpdev_id:Dev_ID, pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)

    requires pid != NULL
    requires wimpdev_id in ws.subjects.devs

    requires ws.subjects.devs[wimpdev_id].hcoded_td_id in ws.objects.tds
    requires forall id :: id in ws.subjects.devs[wimpdev_id].fd_ids ==> id in ws.objects.fds
    requires forall id :: id in ws.subjects.devs[wimpdev_id].do_ids ==> id in ws.objects.dos

    requires P_DMAndNewDM_SameObjectID(ws, ws')

    requires P_DevActivate_ModificationToState(DMStateToState(ws), wimpdev_id.sid, pid, DMStateToState(ws'))

    ensures forall id :: id in ws.subjects.devs &&
                    id != wimpdev_id
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
{
    forall id | id in ws.subjects.devs && id != wimpdev_id
        ensures DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
    {
        assert ws'.subjects.devs[id] == ws.subjects.devs[id];
    }
}

lemma Lemma_NewDM_IsValidState_DevActivate_DevsActivateCond(
    ws:DM_State, ws':DM_State, toactivate_wimpdev_id:Dev_ID, pid:Partition_ID
)
    requires DM_IsValidState_DevsActivateCond(ws)

    requires ws'.devs_activatecond == ws.devs_activatecond
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires DM_AllSubjsIDs(ws'.subjects) == DM_AllSubjsIDs(ws.subjects)

    requires toactivate_wimpdev_id in ws.subjects.devs
        // Requirement: <ws.subjects.devs> in <devs>
    requires pid != NULL
    requires pid == ws.red_pid
                ==> TryActivateDevInRed(ws, toactivate_wimpdev_id)
    requires pid != ws.red_pid
                ==> TryActivateDevInGreen(ws, toactivate_wimpdev_id)

    requires forall id :: id in ws.subjects.devs &&
                    id != toactivate_wimpdev_id
                ==> DM_SubjPID(ws'.subjects, id.sid) == DM_SubjPID(ws.subjects, id.sid)
    requires DM_SubjPID(ws'.subjects, toactivate_wimpdev_id.sid) == pid

    ensures DM_IsValidState_DevsActivateCond(ws')
{
    forall wimpdev_id | wimpdev_id in ws'.devs_activatecond
        ensures DM_SubjPID(ws'.subjects, wimpdev_id.sid) == NULL ||  DM_SubjPID(ws'.subjects, wimpdev_id.sid) == ws'.red_pid
    {
        if(wimpdev_id != toactivate_wimpdev_id)
        {
            assert DM_SubjPID(ws'.subjects, wimpdev_id.sid) == DM_SubjPID(ws.subjects, wimpdev_id.sid);
            assert DM_SubjPID(ws'.subjects, wimpdev_id.sid) == NULL ||  DM_SubjPID(ws'.subjects, wimpdev_id.sid) == ws'.red_pid;
        }
        else
        {
            assert wimpdev_id == toactivate_wimpdev_id;

            assert pid == ws.red_pid;
        }
    }

    forall wimpdev_id, wimpdev_id2 | wimpdev_id in ws'.devs_activatecond &&
                    wimpdev_id2 in ws'.devs_activatecond[wimpdev_id]
        ensures DM_SubjPID(ws'.subjects, wimpdev_id2.sid) != ws'.red_pid
    {
        if(wimpdev_id2 != toactivate_wimpdev_id)
        {
            assert DM_SubjPID(ws'.subjects, wimpdev_id2.sid) == DM_SubjPID(ws.subjects, wimpdev_id2.sid);
            assert DM_SubjPID(ws'.subjects, wimpdev_id2.sid) != ws'.red_pid;
        }
        else
        {
            assert wimpdev_id2 == toactivate_wimpdev_id;

            assert pid != ws.red_pid;
        }
    }

    forall wimpdev_id | wimpdev_id in ws'.devs_activatecond &&
                    DM_SubjPID(ws'.subjects, wimpdev_id.sid) != NULL
        ensures (forall wimpdev_id2 :: wimpdev_id2 in ws'.devs_activatecond[wimpdev_id]
                        ==> DM_SubjPID(ws'.subjects, wimpdev_id2.sid) == NULL)
    {
        if(wimpdev_id != toactivate_wimpdev_id)
        {
            if(toactivate_wimpdev_id in ws'.devs_activatecond[wimpdev_id])
            {
                assert TryActivateDevInGreen(ws, toactivate_wimpdev_id);
                // Show conflicts 
                assert false;
            }
        }
    }

    Lemma_NewDM_IsValidState_DevsActivateCond(ws, ws');
}

lemma Lemma_DevActivate_HCodedTDsBeingActivatedHaveNoWriteTransfersToTDs(k:State, dev_id:Dev_ID)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
    requires k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall hcoded_td_id, td_id :: hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id &&
                        td_id in k.objects.tds[hcoded_td_id].val.trans_params_tds
                    ==> W !in k.objects.tds[hcoded_td_id].val.trans_params_tds[td_id].amodes

    requires forall td_id2 :: td_id2 in AllHCodedTDIDs(k.subjects)
                ==> td_id2 in k.objects.tds
    ensures forall td_id2, td_id3 :: td_id2 in AllHCodedTDIDs(k.subjects) && 
                    td_id2 in k.subjects.devs[dev_id].td_ids &&
                    td_id3 in k.objects.tds[td_id2].val.trans_params_tds
                ==> W !in k.objects.tds[td_id2].val.trans_params_tds[td_id3].amodes
{
    forall td_id2, td_id3 | td_id2 in AllHCodedTDIDs(k.subjects) && 
                    td_id2 in k.subjects.devs[dev_id].td_ids &&
                    td_id3 in k.objects.tds[td_id2].val.trans_params_tds
        ensures W !in k.objects.tds[td_id2].val.trans_params_tds[td_id3].amodes
    {
        Lemma_K_IntersectionOfDevTDIDsAndHCodedTDIDsIsHCodedTDOfDev(k, dev_id);
        assert td_id2 == k.subjects.devs[dev_id].hcoded_td_id;
    }
}

lemma Lemma_DM_ExternalObjActivate_ProveCheckOfDevActivateInK(
    ws:DM_State, k:State, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires DM_IsValidState(ws)
    requires k == DMStateToState(ws)

    requires forall td_id :: td_id in td_ids ==> td_id in ws.objects.tds
    requires fd_ids <= MapGetKeys(ws.objects.fds)
    requires do_ids <= MapGetKeys(ws.objects.dos)

    requires (forall td_id :: td_id in td_ids ==> DM_ObjPID(ws.objects, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> DM_ObjPID(ws.objects, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> DM_ObjPID(ws.objects, do_id.oid) == NULL) &&
           pid in ws.pids
     
    ensures IsValidState_Subjects(k) && IsValidState_Objects(k)
    ensures (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) == NULL) &&
           (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) == NULL) &&
           (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) == NULL) &&
           pid in k.pids
{
    Lemma_ValidDMState_SameObjIDsPIDsBetweenWKAndK(ws, k);

    forall td_id | td_id in td_ids 
        ensures ObjPID(k, td_id.oid) == NULL
    {
        assert DM_ObjPID(ws.objects, td_id.oid) == NULL;
        assert td_id.oid in AllObjsIDs(k.objects);
    }

    forall fd_id | fd_id in fd_ids 
        ensures ObjPID(k, fd_id.oid) == NULL
    {
        assert DM_ObjPID(ws.objects, fd_id.oid) == NULL;
        assert fd_id.oid in AllObjsIDs(k.objects);
    }

    forall do_id | do_id in do_ids 
        ensures ObjPID(k, do_id.oid) == NULL
    {
        assert DM_ObjPID(ws.objects, do_id.oid) == NULL;
        assert do_id.oid in AllObjsIDs(k.objects);
    }
}




//******** Private Lemmas ********//
// (needs 90s to verify)
lemma Lemma_NewDM_SubjObjActivate_FulfillSI2_ActivateIntoGreenPartition(
    ws:DM_State, k:State, ws':DM_State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires pid != ws.red_pid
    requires pid != NULL

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)
    requires forall td_id2, td_id3 :: td_id2 in AllHCodedTDIDs(k.subjects) && 
                    td_id2 in toactivate_td_ids &&
                    td_id3 in k.objects.tds[td_id2].val.trans_params_tds
                ==> W !in k.objects.tds[td_id2].val.trans_params_tds[td_id3].amodes
        // Requirement: If a hardcoded TD is going to be activated, then
        // it must not contain any write transfers to TDs

    requires (forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))

    ensures (forall td_id :: td_id in DM_TDIDsInGreen(ws')
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id))
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'.subjects, k'.objects);
    assert k'_params.hcoded_td_ids == k_params.hcoded_td_ids;
    assert k'_params.objs_td_ids == k_params.objs_td_ids;
    assert k'_params.objs_fd_ids == k_params.objs_fd_ids;
    assert k'_params.objs_do_ids == k_params.objs_do_ids;

    assert forall id :: id in AllObjsIDs(k.objects) && ObjPID(k, id) != NULL
            ==> ObjPID(k', id) == ObjPID(k, id);

    forall td_id | td_id in DM_TDIDsInGreen(ws')
        ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id)
    {
        assert td_id in DM_TDIDsInGreen(ws) || td_id in toactivate_td_ids;
        if(td_id in DM_TDIDsInGreen(ws))
        {
            assert ws'.objects.tds[td_id] == ws.objects.tds[td_id];
            assert ActiveTDsState(k')[td_id] == ActiveTDsState(k)[td_id];

            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, ActiveTDsState(k), td_id);
            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id); 
        }
        else
        {
            assert td_id in toactivate_td_ids;
            Lemma_NewDM_SubjObjActivate_FulfillSI2_ActivateIntoGreenPartition_TDInToActiveTDIDs(ws, k, ws', k', 
                toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, td_id, pid);
            assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, ActiveTDsState(k'), td_id); 
        }
    }
}

// (needs 50s to verify)
lemma Lemma_NewDM_SubjObjActivate_FulfillSI2_ActivateIntoGreenPartition_TDInToActiveTDIDs(
    ws:DM_State, k:State, ws':DM_State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>, td_id:TD_ID,
    pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires pid != ws.red_pid
    requires pid != NULL

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)
    requires forall td_id2, td_id3 :: td_id2 in AllHCodedTDIDs(k.subjects) && 
                    td_id2 in toactivate_td_ids &&
                    td_id3 in k.objects.tds[td_id2].val.trans_params_tds
                ==> W !in k.objects.tds[td_id2].val.trans_params_tds[td_id3].amodes
        // Requirement: If a hardcoded TD is going to be activated, then
        // it must not contain any write transfers to TDs

    requires (forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))

    requires td_id in DM_TDIDsInGreen(ws')
    requires td_id in toactivate_td_ids

    ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k'), ActiveTDsState(k'), td_id)
{
    var k_params := KToKParams(k);
    var k'_params := KToKParams(k');
     
    var k_tds_state := ActiveTDsState(k);
    var k'_tds_state := ActiveTDsState(k');
    var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
    var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

    assert forall id :: id in AllObjsIDs(k.objects) && ObjPID(k, id) != NULL
            ==> ObjPID(k', id) == ObjPID(k, id);

    if(td_id !in toactivate_hcoded_td_ids)
    {
        assert k'_tds_state[td_id] == TD_Val(map[], map[], map[]);
        Lemma_K_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_EmptyTDProperty(k'_params, k'_tds_state, td_id);
        assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, k'_tds_state, td_id);
    }
    else
    {
        assert td_id in hcoded_td_ids && td_id in toactivate_td_ids;
        assert k'_tds_state[td_id] == k.objects.tds[td_id].val;
        Lemma_NewDM_SubjObjActivate_FulfillSI2_ActivateIntoGreenPartition_TDInToActiveTDIDs_Private(
            ws, k, ws', k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, td_id, pid);
        var s_id :| s_id in toactivate_s_ids && DoOwnObj(k, s_id, td_id.oid);

        forall td_id2 | td_id2 in k'_tds_state[td_id].trans_params_tds
            ensures td_id2 in k'_params.objs_td_ids &&
                td_id2 !in k'_params.hcoded_td_ids &&
                (ObjPID_SlimState(k'_params.objs_pids, td_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid) || 
                        // The TD (<td_id>) contains a transfer, the target TD 
                        // (<td_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_tds[td_id2].amodes == {})
        {
            Lemma_K_IfSubjOwnHCodedTD_ThenSubjOwnRefedTDs(k, s_id, td_id, td_id2);
            assert td_id2 in OwnedTDs(k, s_id);
            assert td_id2 in toactivate_td_ids;
        }

        forall fd_id2 | fd_id2 in k'_tds_state[td_id].trans_params_fds
            ensures fd_id2 in k'_params.objs_fd_ids &&
                ((ObjPID_SlimState(k'_params.objs_pids, fd_id2.oid) == 
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid)) ||
                        // The TD (<td_id>) contains a transfer, the target FD 
                        // (<fd_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_fds[fd_id2].amodes == {})
        {
            Lemma_K_IfSubjOwnHCodedTD_ThenSubjOwnRefedFDs(k, s_id, td_id, fd_id2);
            assert fd_id2 in OwnedFDs(k, s_id);
            assert fd_id2 in toactivate_fd_ids;
        }

        forall do_id2 | do_id2 in k'_tds_state[td_id].trans_params_dos
            ensures do_id2 in k'_params.objs_do_ids && 
                (ObjPID_SlimState(k'_params.objs_pids, do_id2.oid) ==
                    ObjPID_SlimState(k'_params.objs_pids, td_id.oid) ||
                        // The TD (<td_id>) contains a transfer, the target DO
                        // (<do_id2>) must be in the same partition with the TD
                 k'_tds_state[td_id].trans_params_dos[do_id2].amodes == {})
        {
            Lemma_K_IfSubjOwnHCodedTD_ThenSubjOwnRefedDOs(k, s_id, td_id, do_id2);
            assert do_id2 in OwnedDOs(k, s_id);
            assert do_id2 in toactivate_do_ids;
        }

        Lemma_DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_Prove(k'_params, k'_tds_state, td_id);
        assert DoTDsIncludeSecureNoTDWriteTransfersOnly(k'_params, k'_tds_state, td_id);
    }
}

lemma Lemma_NewDM_SubjObjActivate_FulfillSI2_ActivateIntoGreenPartition_TDInToActiveTDIDs_Private(
    ws:DM_State, k:State, ws':DM_State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>, td_id:TD_ID,
    pid:Partition_ID
)
    requires DM_IsValidState_Subjects(ws)
    requires DM_IsValidState_Objects(ws)
    requires DM_IsValidState_Subjects(ws')
    requires DM_IsValidState_Objects(ws')
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws)
    requires DM_IsValidState_SubjsOwnObjsThenInSamePartition(ws')
    requires k == DMStateToState(ws)
    requires k' == DMStateToState(ws')

    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires P_DMAndNewDM_SameSubjectIDAndObjOwnership(ws, ws')

    requires ws'.red_pid == ws.red_pid
    requires pid != ws.red_pid
    requires pid != NULL

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    requires (forall td_id :: td_id in DM_TDIDsInGreen(ws)
                ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))

    requires td_id in DM_TDIDsInGreen(ws')
    requires td_id in toactivate_td_ids
    requires td_id in AllHCodedTDIDs(k.subjects)

    ensures exists s_id :: s_id in toactivate_s_ids && DoOwnObj(k, s_id, td_id.oid)
{
    assert (forall dev_id :: dev_id in k.subjects.devs
        ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids);
    assert exists s_id :: IsSubjID(k.subjects, s_id) && DoOwnObj(k, s_id, td_id.oid);
    var s_id :| IsSubjID(k.subjects, s_id) && DoOwnObj(k, s_id, td_id.oid);
    
    assert IsSubjID(k'.subjects, s_id);
    assert DoOwnObj(k', s_id, td_id.oid);
    if(s_id !in toactivate_s_ids)
    {
        assert ObjPID(k, td_id.oid) == NULL;
        assert ObjPID(k', td_id.oid) != NULL;

        // Show conflicts
        assert SubjPID(k, s_id) == NULL;
        assert SubjPID(k', s_id) != NULL;
        assert !SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    }
}