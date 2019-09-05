include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"
include "Lemmas_SubjActivate_ReachableTDsStates.dfy"

predicate SubjObjActivate_PropertiesOfNewTDs(k:State, k'_objects:Objects, toactivate_td_ids:set<TD_ID>, pid:Partition_ID)
{
    var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
    var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

    (MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)) &&
    (toactivate_td_ids <= MapGetKeys(k.objects.tds)) &&
    (forall td_id :: td_id in toactivate_td_ids
            ==> k.objects.tds[td_id].pid == NULL) &&
    (forall td_id :: td_id in toactivate_td_ids
            ==> k'_objects.tds[td_id].pid == pid) &&

    (toactivate_hcoded_td_ids <= toactivate_td_ids) &&
    (forall td_id :: td_id in toactivate_td_ids &&
                td_id !in toactivate_hcoded_td_ids
            ==> k'_objects.tds[td_id].val == TD_Val(map[], map[], map[])) &&
    (forall td_id :: td_id in toactivate_hcoded_td_ids
            ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val) &&
        // Forall TDs to be activated, hardcoded TDs preserve their values,
        // and other TDs are cleared

    (forall td_id :: td_id in k.objects.tds &&
                td_id !in toactivate_td_ids
            ==> k'_objects.tds[td_id] == k.objects.tds[td_id]) &&

    (true)
}

predicate SubjObjActivate_PropertiesOfNewFDs(k:State, k'_objects:Objects, toactivate_fd_ids:set<FD_ID>, pid:Partition_ID)
{
    (MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)) &&
    (toactivate_fd_ids <= MapGetKeys(k.objects.fds)) &&
    (forall fd_id :: fd_id in toactivate_fd_ids
            ==> k.objects.fds[fd_id].pid == NULL) &&
    (forall fd_id :: fd_id in toactivate_fd_ids
            ==> k'_objects.fds[fd_id].pid == pid) &&
    (forall fd_id :: fd_id in toactivate_fd_ids
            ==> k'_objects.fds[fd_id].val == FD_Val("")) &&
    (forall fd_id :: fd_id in k.objects.fds &&
                fd_id !in toactivate_fd_ids
            ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]) &&

    (true)
}

predicate SubjObjActivate_PropertiesOfNewDOs(k:State, k'_objects:Objects, toactivate_do_ids:set<DO_ID>, pid:Partition_ID)
{
    (MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)) &&
    (toactivate_do_ids <= MapGetKeys(k.objects.dos)) &&
    (forall do_id :: do_id in toactivate_do_ids
            ==> k.objects.dos[do_id].pid == NULL) &&
    (forall do_id :: do_id in toactivate_do_ids
            ==> k'_objects.dos[do_id].pid == pid) &&
    (forall do_id :: do_id in toactivate_do_ids
            ==> k'_objects.dos[do_id].val == DO_Val("")) &&
    (forall do_id :: do_id in k.objects.dos &&
                do_id !in toactivate_do_ids
            ==> k'_objects.dos[do_id] == k.objects.dos[do_id]) &&

    (true)
}

predicate SubjObjActivate_PropertiesOfNewSubjs(
    k:State, k'_subjects:Subjects, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
{
    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&

    (toactivate_s_ids <= AllSubjsIDs(k.subjects)) &&
    (forall s_id :: s_id in toactivate_s_ids 
                ==> OwnedTDs(k, s_id) <= toactivate_td_ids &&
                    OwnedFDs(k, s_id) <= toactivate_fd_ids &&
                    OwnedDOs(k, s_id) <= toactivate_do_ids) &&
        // If a subject is to be activated, then its objects are also to be activated
    (forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) == NULL) &&
    (forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == pid) &&

    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])) &&
    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}) &&
        // If a subject is not to be activated, then its objects must not to be
        // activated

    (true)
}

lemma Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
{
    forall s_id, o_id | s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
        ensures SubjPID(k', s_id) == ObjPID(k', o_id)
    {
        if(s_id !in toactivate_s_ids)
        {
            assert DoOwnObj(k, s_id, o_id);
            Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, s_id, o_id);
            assert TD_ID(o_id) !in toactivate_td_ids;
            assert FD_ID(o_id) !in toactivate_fd_ids;
            assert DO_ID(o_id) !in toactivate_do_ids;

            if(Drv_ID(s_id) in k.subjects.drvs)
            {
                assert SubjPID_SlimState(k'.subjects, s_id) == k.subjects.drvs[Drv_ID(s_id)].pid;

                assert ObjPID(k', o_id) == ObjPID(k, o_id);
                assert SubjPID(k', s_id) == ObjPID(k', o_id);
            }
            else
            {
                assert Dev_ID(s_id) in k.subjects.devs;

                assert ObjPID(k', o_id) == ObjPID(k, o_id);
                assert SubjPID(k', s_id) == ObjPID(k', o_id);
            }
        }
        else
        {
            assert s_id in toactivate_s_ids;

            assert SubjPID_SlimState(k'.subjects, s_id) == pid;
            if(Drv_ID(s_id) in k.subjects.drvs)
            {
                assert TD_ID(o_id) in toactivate_td_ids || 
                       FD_ID(o_id) in toactivate_fd_ids ||
                       DO_ID(o_id) in toactivate_do_ids;

                assert ObjPID(k', o_id) == pid;
            }
            else
            {
                assert Dev_ID(s_id) in k.subjects.devs;
                assert TD_ID(o_id) in toactivate_td_ids || 
                       FD_ID(o_id) in toactivate_fd_ids ||
                       DO_ID(o_id) in toactivate_do_ids;

                assert ObjPID(k', o_id) == pid;
            }
        }
    }
}

lemma Lemma_SubjObjActivate_NewK_UniqueIDsAndOwnedObjs(k:State, k':State)
    requires IsValidState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    ensures K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_FulfillCommonPreConditionsOfKAndNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures SubjObjActivate_PreConditionsOfK(k')
    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjActivate_CommonPreConditionsOfKAndNewK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids)
{
    Lemma_SubjObjActivate_NewK_UniqueIDsAndOwnedObjs(k ,k');
    Lemma_SubjObjActivate_NewK_SubjsObjsPIDsInNewK(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_CertainTDsToActivateMustBeCleared(k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_FulfillNextThreePredicates(k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfK(k, k_params);
    Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfNewK(k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
}

lemma Lemma_SubjObjActivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, k'_active_devs:set<Dev_ID>, k'_active_tds_state:TDs_Vals,
    explored_tds_states:seq<set<TDs_Vals>>, found_tds_states:set<TDs_Vals>
)
    requires SubjObjActivate_PreConditionsOfK(k')
    
    requires k'_params == KToKParams(k')
    requires k'_active_devs == AllActiveDevs(k')
    requires k'_active_tds_state == ActiveTDsState_SlimState(k'.objects.tds)
    requires found_tds_states == GetExploredTDsStates(explored_tds_states, 0)

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k'_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (k'_active_tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, k'_active_devs, k'_active_tds_state, tds_state2))

    ensures forall tds_state2 :: tds_state2 in found_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
    ensures forall tds_state2 :: tds_state2 in found_tds_states
                ==> (ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_NewK_FulfillSI2(
    k:State, k':State,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k.pids == k'.pids

    requires pid != NULL
    requires pid in k'.pids
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)

    ensures IsSecureState_SI2(k')
{
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    forall s_id | s_id in AllSubjsIDs(k'.subjects) && SubjPID(k', s_id) != NULL
        ensures SubjPID(k', s_id) in k'.pids
    {
        assert s_id in toactivate_s_ids || SubjPID(k, s_id) != NULL;
        assert s_id in AllSubjsIDs(k.subjects);
    }

    forall o_id | o_id in AllObjsIDs(k'.objects) && ObjPID(k', o_id) != NULL
        ensures ObjPID(k', o_id) in k'.pids
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(
    k:State, toactivate_s_ids:set<Subject_ID>,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) == NULL
        // Requirement: All subjects to be activated are inactive in k 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall s_id :: s_id in toactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k.subjects)
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}
{
    assert forall s_id :: s_id in toactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k.subjects);

    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    forall s_id | s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
        ensures OwnedTDs(k, s_id) * toactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * toactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * toactivate_do_ids == {}
    { 
        if(exists td_id :: td_id in OwnedTDs(k, s_id) && td_id in toactivate_td_ids)
        {
            var td_id :| td_id in OwnedTDs(k, s_id) && td_id in toactivate_td_ids;
            var s_id2 :| s_id2 in toactivate_s_ids && td_id in OwnedTDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, td_id.oid);
            assert DoOwnObj(k, s_id2, td_id.oid);
        }

        if(exists fd_id :: fd_id in OwnedFDs(k, s_id) && fd_id in toactivate_fd_ids)
        {
            var fd_id :| fd_id in OwnedFDs(k, s_id) && fd_id in toactivate_fd_ids;
            var s_id2 :| s_id2 in toactivate_s_ids && fd_id in OwnedFDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, fd_id.oid);
            assert DoOwnObj(k, s_id2, fd_id.oid);
        }

        if(exists do_id :: do_id in OwnedDOs(k, s_id) && do_id in toactivate_do_ids)
        {
            var do_id :| do_id in OwnedDOs(k, s_id) && do_id in toactivate_do_ids;
            var s_id2 :| s_id2 in toactivate_s_ids && do_id in OwnedDOs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, do_id.oid);
            assert DoOwnObj(k, s_id2, do_id.oid);
        }
    }
}

lemma Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(
    k:State, toactivate_s_ids:set<Subject_ID>,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) == NULL
        // Requirement: All subjects to be activated are inactive in k 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall td_id :: td_id in toactivate_td_ids
            ==> k.objects.tds[td_id].pid == NULL
    ensures forall fd_id :: fd_id in toactivate_fd_ids
            ==> k.objects.fds[fd_id].pid == NULL
    ensures forall do_id :: do_id in toactivate_do_ids
            ==> k.objects.dos[do_id].pid == NULL
{
    forall td_id | td_id in toactivate_td_ids
        ensures k.objects.tds[td_id].pid == NULL
    {
        assert exists s_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, td_id.oid);
        assert k.objects.tds[td_id].pid == NULL;
    }

    forall fd_id | fd_id in toactivate_fd_ids
        ensures k.objects.fds[fd_id].pid == NULL
    {
        assert exists s_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, fd_id.oid);
        assert k.objects.fds[fd_id].pid == NULL;
    }

    forall do_id | do_id in toactivate_do_ids
        ensures k.objects.dos[do_id].pid == NULL
    {
        assert exists s_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, do_id.oid);
        assert k.objects.dos[do_id].pid == NULL;
    }
}

predicate P_Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k:State, toactivate_td_ids:set<TD_ID>)
{
    var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
    var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

    toactivate_hcoded_td_ids == {}
}

lemma Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k:State, toactive_drv_id:Drv_ID, toactivate_td_ids:set<TD_ID>)
    requires IsValidState(k) && IsSecureState(k)

    requires IsDrvID(k, toactive_drv_id)
    requires forall td_id :: td_id in toactivate_td_ids
                ==> td_id in OwnedTDs(k, toactive_drv_id.sid)

    ensures P_Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, toactivate_td_ids)
{
    assert (forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2);
    if(!P_Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, toactivate_td_ids))
    {
        var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
        var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

        var td_id :| td_id in toactivate_hcoded_td_ids;

        assert td_id in toactivate_td_ids;
        assert td_id in hcoded_td_ids;

        assert td_id in OwnedTDs(k, toactive_drv_id.sid);
        assert DoOwnObj(k, toactive_drv_id.sid, td_id.oid);

        // Show conflict
        assert exists dev_id :: dev_id in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id].hcoded_td_id;
        var dev_id :| dev_id in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id].hcoded_td_id;
        assert DoOwnObj(k, dev_id.sid, td_id.oid);
        assert false;
    }
}

lemma Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(
    k:State, k'_subjects_devs:map<Dev_ID, Dev_State>, k'_objects:Objects, toactivate_td_ids:set<TD_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k) 
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid);

    requires MapGetKeys(k'_subjects_devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    
    ensures forall dev_id :: dev_id in k'_subjects_devs
                ==> k'_objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvActivate_ObjsIDsInDrvsAreUnchanged(k:State, k'_subjects:Subjects, drv_id:Drv_ID, old_drv_state:Drv_State, new_drv_state:Drv_State)
    requires drv_id in k.subjects.drvs

    requires old_drv_state == IDToDrv(k, drv_id)
    requires new_drv_state.td_ids == old_drv_state.td_ids
    requires new_drv_state.fd_ids == old_drv_state.fd_ids
    requires new_drv_state.do_ids == old_drv_state.do_ids
    requires k'_subjects.drvs == k.subjects.drvs[drv_id := new_drv_state]

    ensures forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires K_UniqueIDsAndOwnedObjs(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in k'_objects.tds

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids &&
                    k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(k, k'_subjects, k'_objects, k'_params, 
        toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
    {
        if(s_id in toactivate_s_ids)
        {
            Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingActivated(
                k, k'_subjects, k'_objects, k'_params, 
                toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid, s_id, o_id);
        }
        else
        {
            Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingActivated(
                k, k'_subjects, k'_objects, k'_params, 
                toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid, s_id, o_id);
        }
    }
}

lemma Lemma_DrvActivate_SameActiveDevsInKAndNewK(
    k:State, k'_subjects:Subjects, drv_id:Drv_ID, old_drv_state:Drv_State, new_drv_state:Drv_State
)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)

    requires drv_id in k.subjects.drvs

    requires old_drv_state == IDToDrv(k, drv_id)
    requires new_drv_state.td_ids == old_drv_state.td_ids
    requires new_drv_state.fd_ids == old_drv_state.fd_ids
    requires new_drv_state.do_ids == old_drv_state.do_ids
    requires k'_subjects.drvs == k.subjects.drvs[drv_id := new_drv_state]
    requires k'_subjects.devs == k.subjects.devs

    ensures AllActiveDevs(k) == AllActiveDevs_SlimState(k'_subjects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevActivate_NonHCodedTDsAreClearedAsTC21(
    k:State, k'_hcoded_td_ids:set<TD_ID>, k'_objects:Objects, toactivate_td_ids:set<TD_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k) 
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid);

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires k'_hcoded_td_ids == AllHCodedTDIDs(k.subjects)

    ensures forall td_id :: td_id in k'_objects.tds &&
                    k'_objects.tds[td_id].pid != k.objects.tds[td_id].pid &&
                    k'_objects.tds[td_id].pid != NULL &&
                        // For a transition from k to k', if a TD is activated (or moved) into a partition
                    td_id !in k'_hcoded_td_ids
                        // TD is not a hardcoded TD
                ==> IsTDClearVal(k'_objects.tds, td_id)
{
    // Dafny can automatically prove this lemma
}

// (needs 70s to verify)
lemma Lemma_DevActivate_HCodedTDsToBeActivatedHaveUnmodifiedVals(
    k:State, tds':map<TD_ID, TD_State>, toactive_dev_id:Dev_ID, toactivate_td_ids:set<TD_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires IsDevID(k, toactive_dev_id)
    requires forall td_id :: td_id in toactivate_td_ids
                ==> td_id in OwnedTDs(k, toactive_dev_id.sid)
    
    requires MapGetKeys(tds') == MapGetKeys(k.objects.tds)

    requires forall td_id :: td_id in toactivate_td_ids
                ==> td_id == k.subjects.devs[toactive_dev_id].hcoded_td_id ==> tds'[td_id].val == k.objects.tds[td_id].val

    ensures forall td_id :: td_id in (set td_id2 | td_id2 in AllHCodedTDIDs(k.subjects) && td_id2 in toactivate_td_ids :: td_id2)
                    // The set is hardcoded TDs to be activated
                ==> tds'[td_id].val == k.objects.tds[td_id].val
        // Property: Forall hardcoded TDs to be activated, their value is unchanged
{
    assert forall o_id, s_id1, s_id2 :: 
            s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
            DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
            ==> s_id1 == s_id2;

    forall td_id | td_id in (set td_id2 | td_id2 in AllHCodedTDIDs(k.subjects) && td_id2 in toactivate_td_ids :: td_id2)
        ensures tds'[td_id].val == k.objects.tds[td_id].val
    {
        var hcoded_td_id := k.subjects.devs[toactive_dev_id].hcoded_td_id;

        assert td_id in AllHCodedTDIDs(k.subjects);
        assert td_id in toactivate_td_ids;
        
        assert DoOwnObj(k, toactive_dev_id.sid, td_id.oid);
        assert DoOwnObj(k, toactive_dev_id.sid, hcoded_td_id.oid);
        assert td_id == hcoded_td_id;

        assert td_id == k.subjects.devs[toactive_dev_id].hcoded_td_id;
    }
}

lemma Lemma_DevActivate_ObjsIDsInDevsAreUnchanged(k:State, k'_subjects:Subjects, dev_id:Dev_ID, old_dev_state:Dev_State, new_dev_state:Dev_State)
    requires dev_id in k.subjects.devs

    requires old_dev_state == IDToDev(k, dev_id)
    requires new_dev_state.hcoded_td_id == old_dev_state.hcoded_td_id
    requires new_dev_state.td_ids == old_dev_state.td_ids
    requires new_dev_state.fd_ids == old_dev_state.fd_ids
    requires new_dev_state.do_ids == old_dev_state.do_ids
    requires k'_subjects.devs == k.subjects.devs[dev_id := new_dev_state]

    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects:Subjects)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k'_subjects.drvs) && (Dev_ID(dev_sid) in k'_subjects.devs)
         ==> (drv_sid != dev_sid)

    ensures forall dev_id2 :: dev_id2 in AllActiveDevs_SlimState(k'_subjects)
                ==> IsDevID_SlimState(k'_subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k'_subjects, dev_id2) != NULL
{
    forall dev_id2 | dev_id2 in AllActiveDevs_SlimState(k'_subjects)
        ensures IsDevID_SlimState(k'_subjects, dev_id2)
        ensures SubjPID_DevID_SlimState(k'_subjects, dev_id2) != NULL
    {
        assert IsDevID_SlimState(k'_subjects, dev_id2);
        assert SubjPID_SlimState(k'_subjects, dev_id2.sid) != NULL;
    }
}

lemma Lemma_NewK_HCodedTDsOfAllActiveDevsRefObjInDevs(
    k:State, k_params:ReachableTDsKParams,
    k'_params:ReachableTDsKParams, k'_subjects:Subjects, k'_active_devs:set<Dev_ID>
)
    requires IsValidState(k) && IsSecureState(k) 
    requires k_params == KToKParams(k) 

    requires AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)
    
    requires MapGetKeys(k'_params.subjects.drvs) == MapGetKeys(KToKParams(k).subjects.drvs)
    requires MapGetKeys(k'_params.subjects.devs) == MapGetKeys(KToKParams(k).subjects.devs)
    requires k'_params.objs_td_ids == KToKParams(k).objs_td_ids
    requires k'_params.hcoded_td_ids == KToKParams(k).hcoded_td_ids
    requires k'_params.hcoded_tds == KToKParams(k).hcoded_tds

    requires k'_params.subjects == k'_subjects

    requires forall dev_id :: dev_id in k'_active_devs
                ==> dev_id.sid in AllSubjsIDs(k'_subjects)
    requires forall dev_id :: dev_id in k'_active_devs
                ==> IsDevID_SlimState(k'_subjects, dev_id)

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)

    ensures forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids
{
    Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);
    assert forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids;

    forall dev_id2 | dev_id2 in k'_active_devs
        ensures DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2)
        ensures IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids
    {
        assert IsDevID_SlimState(k_params.subjects, dev_id2);
    }
}

lemma Lemma_ExternalObjsActivate_AllObjsToBeActivatedAreExternalObjs(
    k:State,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in toactivate_td_ids || FD_ID(o_id) in toactivate_fd_ids || DO_ID(o_id) in toactivate_do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}
{
    forall s_id | s_id in AllSubjsIDs(k.subjects)
        ensures OwnedTDs(k, s_id) * toactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * toactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * toactivate_do_ids == {}
    {
        assert forall td_id :: td_id in toactivate_td_ids
                ==> !DoOwnObj(k, s_id, td_id.oid);
        assert forall fd_id :: fd_id in toactivate_fd_ids
                ==> !DoOwnObj(k, s_id, fd_id.oid);
        assert forall do_id :: do_id in toactivate_do_ids
                ==> !DoOwnObj(k, s_id, do_id.oid);

        assert forall td_id :: td_id in toactivate_td_ids
                ==> td_id !in OwnedTDs(k, s_id);
        assert forall fd_id :: fd_id in toactivate_fd_ids
                ==> fd_id !in OwnedFDs(k, s_id);
        assert forall do_id :: do_id in toactivate_do_ids
                ==> do_id !in OwnedDOs(k, s_id);
    }
}

lemma Lemma_ExternalObjsActivate_HCodedTDsAreUnchanged(
    k:State, k'_subjects_devs:map<Dev_ID, Dev_State>, tds':map<TD_ID, TD_State>, tds_to_activate:set<TD_ID>
)
    requires forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                 ==> (drv_sid != dev_sid)
        // Requirement: Subjects have different internal IDs
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices

    requires MapGetKeys(k'_subjects_devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(tds') == MapGetKeys(k.objects.tds)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
        // Requirement: Hardcoded TDs are in the TDs of the state
    requires forall dev_id :: dev_id in k'_subjects_devs
                ==> k'_subjects_devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id
        // Requirement: IDs of hardcoded TDs are not changed
    requires tds_to_activate <= MapGetKeys(k.objects.tds)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_activate
                ==> !DoOwnObj(k, s_id, td_id.oid)
        // Requirement: TDs to be activated must be external TDs
    requires forall td_id :: td_id in k.objects.tds && td_id !in tds_to_activate
                ==> tds'[td_id] == k.objects.tds[td_id]
        // Requirement: Other TDs are not modified
    
    ensures forall dev_id :: dev_id in k'_subjects_devs
                ==> tds'[k.subjects.devs[dev_id].hcoded_td_id] == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id]
{
    forall dev_id, hcoded_td_id | dev_id in k.subjects.devs &&
                hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id
        ensures DoOwnObj_SlimState(k.subjects, dev_id.sid, hcoded_td_id.oid)
    {
        Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, hcoded_td_id);
    }

    forall dev_id | dev_id in k'_subjects_devs
        ensures tds'[k.subjects.devs[dev_id].hcoded_td_id] == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id]
    {
        var hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;

        assert dev_id.sid in AllSubjsIDs(k.subjects);
        if (hcoded_td_id in tds_to_activate)
        {
            // Show conflict
            assert !DoOwnObj(k, dev_id.sid, hcoded_td_id.oid);
            assert DoOwnObj(k, dev_id.sid, hcoded_td_id.oid);
        }
        assert hcoded_td_id !in tds_to_activate;
    }
}

lemma Lemma_SubjObjActivate_NewKParams_HasUnmodifiedVarsFromKParams(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)
        // Requriement: TD/FD/DO IDs are not changed

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_objects.tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val
        // Requirement: Hardcoded TDs are immutable

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))

    ensures MapGetKeys(k'_params.subjects.drvs) == MapGetKeys(KToKParams(k).subjects.drvs)
    ensures MapGetKeys(k'_params.subjects.devs) == MapGetKeys(KToKParams(k).subjects.devs)
    ensures k'_params.objs_td_ids == KToKParams(k).objs_td_ids
    ensures k'_params.objs_fd_ids == KToKParams(k).objs_fd_ids
    ensures k'_params.objs_do_ids == KToKParams(k).objs_do_ids
    ensures k'_params.hcoded_td_ids == KToKParams(k).hcoded_td_ids
    ensures k'_params.hcoded_tds == KToKParams(k).hcoded_tds
    ensures MapGetKeys(k'_params.objs_pids) == MapGetKeys(KToKParams(k).objs_pids)
{
    assert MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos);

    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids;
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val);

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'_subjects, k'_objects);
}

lemma Lemma_ExternalObjsActivate_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams,
    tds_to_activate:set<TD_ID>, fds_to_activate:set<FD_ID>, dos_to_activate:set<DO_ID>
)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))

    requires k'_subjects == k.subjects
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)
    requires AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)
    requires AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
        // Requirement: Hardcoded TDs are in the TDs of the state
    requires tds_to_activate <= MapGetKeys(k.objects.tds)
    requires fds_to_activate <= MapGetKeys(k.objects.fds)
    requires dos_to_activate <= MapGetKeys(k.objects.dos)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_activate
                ==> !DoOwnObj(k, s_id, td_id.oid)
    requires forall s_id, fd_id :: s_id in AllSubjsIDs(k.subjects) &&
                    fd_id in fds_to_activate
                ==> !DoOwnObj(k, s_id, fd_id.oid)
    requires forall s_id, do_id :: s_id in AllSubjsIDs(k.subjects) &&
                    do_id in dos_to_activate
                ==> !DoOwnObj(k, s_id, do_id.oid)
        // Requirement: TDs/FDs/DOs to be activated must be external TDs/FDs/DOs
    requires forall td_id :: td_id in k.objects.tds && td_id !in tds_to_activate
                ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    requires forall fd_id :: fd_id in k.objects.fds && fd_id !in fds_to_activate
                ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    requires forall do_id :: do_id in k.objects.dos && do_id !in dos_to_activate
                ==> k'_objects.dos[do_id] == k.objects.dos[do_id]
        // Requirement: Other TDs/FDs/DOs are not modified

    requires forall s_id, o_id :: s_id in AllSubjsIDs(KToKParams(k).subjects) &&
                    DoOwnObj_SlimState(KToKParams(k).subjects, s_id, o_id)
                ==> o_id in KToKParams(k).objs_pids &&
                    KToKParams(k).objs_pids[o_id] == SubjPID_SlimState(KToKParams(k).subjects, s_id)
        // Requirement: In k, if a subject owns an object, then the subject 
        // and the object must be in the same partition
    
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in k'_objects.tds 
    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids &&
                    k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    assert MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds);
    assert MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds);
    assert MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos);

    assert k'_params.subjects == KToKParams(k).subjects;

    forall dev_id, hcoded_td_id | dev_id in k.subjects.devs &&
                hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id
        ensures DoOwnObj_SlimState(k.subjects, dev_id.sid, hcoded_td_id.oid)
    {
        Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, hcoded_td_id);
    }

    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                        DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures o_id in k'_params.objs_pids &&
                k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
    {
        assert IsSubjID(k.subjects, s_id);
        assert o_id in AllObjsIDs(k'_objects);
        assert MapGetKeys(BuildMap_ObjIDsToPIDs(k'_objects)) == AllObjsIDs(k'_objects);
        assert k'_params.objs_pids == BuildMap_ObjIDsToPIDs(k'_objects);
        assert o_id in k'_params.objs_pids;

        assert SubjPID_SlimState(k'_params.subjects, s_id) == SubjPID(k, s_id);
        if(TD_ID(o_id) in k.objects.tds)
        {
            var td_id := TD_ID(o_id);
            assert td_id !in tds_to_activate;
            assert k'_objects.tds[td_id] == k.objects.tds[td_id];
            assert k'_params.objs_pids[o_id] == k.objects.tds[td_id].pid;
        }
        else if(FD_ID(o_id) in k.objects.fds)
        {
            var fd_id := FD_ID(o_id);
            assert fd_id !in fds_to_activate;
            assert k'_objects.fds[fd_id] == k.objects.fds[fd_id];
            assert k'_params.objs_pids[o_id] == k.objects.fds[fd_id].pid;
        }
        else
        {
            var do_id := DO_ID(o_id);
            assert DO_ID(o_id) in k.objects.dos;
            assert do_id !in dos_to_activate;
            assert k'_objects.dos[do_id] == k.objects.dos[do_id];
            assert k'_params.objs_pids[o_id] == k.objects.dos[do_id].pid;
        }
    }
}

lemma Lemma_ExternalObjsActivate_FulfillTC21(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams,
    tds_to_activate:set<TD_ID>, fds_to_activate:set<FD_ID>, dos_to_activate:set<DO_ID>,
    pid:Partition_ID
)
    requires K_UniqueIDsAndOwnedObjs(k.subjects, MapGetKeys(k.objects.tds), MapGetKeys(k.objects.fds), MapGetKeys(k.objects.dos))

    requires k'_subjects == k.subjects
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)
    requires AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)
    requires AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.tds
        // Requirement: Hardcoded TDs are in the TDs of the state
    requires tds_to_activate <= MapGetKeys(k.objects.tds)
    requires fds_to_activate <= MapGetKeys(k.objects.fds)
    requires dos_to_activate <= MapGetKeys(k.objects.dos)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_activate
                ==> !DoOwnObj(k, s_id, td_id.oid)
    requires forall s_id, fd_id :: s_id in AllSubjsIDs(k.subjects) &&
                    fd_id in fds_to_activate
                ==> !DoOwnObj(k, s_id, fd_id.oid)
    requires forall s_id, do_id :: s_id in AllSubjsIDs(k.subjects) &&
                    do_id in dos_to_activate
                ==> !DoOwnObj(k, s_id, do_id.oid)
        // Requirement: TDs/FDs/DOs to be activated must be external TDs/FDs/DOs
    requires forall td_id :: td_id in k.objects.tds && td_id !in tds_to_activate
                ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    requires forall fd_id :: fd_id in k.objects.fds && fd_id !in fds_to_activate
                ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    requires forall do_id :: do_id in k.objects.dos && do_id !in dos_to_activate
                ==> k'_objects.dos[do_id] == k.objects.dos[do_id]
        // Requirement: Other TDs/FDs/DOs are not modified

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, tds_to_activate, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, fds_to_activate, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, dos_to_activate, pid)

    ensures forall td_id :: td_id in k'_objects.tds &&
                    k'_objects.tds[td_id].pid != k.objects.tds[td_id].pid &&
                    k'_objects.tds[td_id].pid != NULL &&
                        // For a transition from k to k', if a TD is activated (or moved) into a partition
                    td_id !in AllHCodedTDIDs(k'_subjects)
                        // TD is not a hardcoded TD
                ==> IsTDClearVal(k'_objects.tds, td_id)
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas  ********//
lemma Lemma_SubjObjActivate_NewK_SubjsObjsPIDsInNewK(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjActivate_SubjsObjsPIDsInNewK(k')
{
    Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

    forall dev_id | dev_id in k'.subjects.devs
        ensures forall td_id :: td_id in IDToDev(k', dev_id).td_ids
                    ==> ObjPID(k', td_id.oid) == SubjPID(k', dev_id.sid)
        ensures forall fd_id :: fd_id in IDToDev(k', dev_id).fd_ids
                    ==> ObjPID(k', fd_id.oid) == SubjPID(k', dev_id.sid)
        ensures forall do_id :: do_id in IDToDev(k', dev_id).do_ids
                    ==> ObjPID(k', do_id.oid) == SubjPID(k', dev_id.sid)
    {
        assert dev_id.sid in AllSubjsIDs(k'.subjects);
        assert forall td_id :: td_id in IDToDev(k', dev_id).td_ids
                    ==> DoOwnObj(k', dev_id.sid, td_id.oid);
        assert forall fd_id :: fd_id in IDToDev(k', dev_id).fd_ids
                    ==> DoOwnObj(k', dev_id.sid, fd_id.oid);
        assert forall do_id :: do_id in IDToDev(k', dev_id).do_ids
                    ==> DoOwnObj(k', dev_id.sid, do_id.oid);
    }
}

lemma Lemma_SubjObjActivate_NewK_PreConditionsOfSubjObjToActivate(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires pid != NULL
    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    ensures SubjObjActivate_PreConditionsOfK(k)
    ensures SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
{
    Lemma_AllActiveObjs_SlimState_Property(k.objects);

    forall drv_id2:Drv_ID | IsDrvID(k, drv_id2) &&
                    drv_id2.sid !in toactivate_s_ids
        ensures k'.subjects.drvs[drv_id2] == k.subjects.drvs[drv_id2]
    {
        assert drv_id2.sid in AllSubjsIDs(k.subjects);
        assert drv_id2 in k.subjects.drvs;
    }
}

// (needs 40s to verify)
lemma Lemma_SubjObjActivate_NewK_CertainTDsToActivateMustBeCleared(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures SubjObjActivate_CertainTDsToActivateMustBeCleared(k, k', toactivate_s_ids)
{
    Lemma_NewKParams_SameSubjIDsOwnershipInSuccessiveStates(k, k'.subjects, k_params, k'_params);

    forall dev_id2:Dev_ID, td_id2 | IsDevID(k, dev_id2) && 
                    dev_id2.sid in toactivate_s_ids &&
                    td_id2 in TDsRefedByDevHCodedTDWithR(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id2)
        ensures td_id2 in k'.objects.tds
        ensures IsTDClearVal(k'.objects.tds, td_id2)
    {
        assert DoOwnObj(k, dev_id2.sid, td_id2.oid);
    }
}

lemma Lemma_SubjObjActivate_NewK_FulfillNextThreePredicates(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    ensures SubjObjActivate_PreConditionsOfK(k')
{
    Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD_PreConditions(
        k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids);
}

lemma Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfK(
    k:State, k_params:ReachableTDsKParams
)
    requires IsValidState(k) && IsSecureState(k)
    requires k_params == KToKParams(k)

    ensures forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: In k, no two subjects own the same object
    ensures forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
    ensures forall dev_id2, td_id2 :: IsDevID(k, dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(KToKParams(k).hcoded_tds, dev_id2)
                ==> td_id2 != k.subjects.devs[dev_id2].hcoded_td_id

    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds
                        ==> td_id !in k_params.hcoded_td_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures forall dev_id:Dev_ID :: dev_id.sid in toactivate_s_ids && dev_id in k.subjects.devs
                ==> (dev_id in k'.subjects.devs &&
                    (forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                        ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R,W}))
        // Requirement: Activating devices do not have hardcoded R and W to the 
        // same object
    ensures forall td_id:TD_ID, dev_id:Dev_ID :: dev_id in k.subjects.devs &&
                dev_id.sid in toactivate_s_ids && 
                td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
            ==> td_id in k'.objects.tds &&
                k'.objects.tds[td_id].val == TD_Val(map[], map[], map[])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(
    k:State,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)

    requires toactivate_td_ids <= MapGetKeys(k.objects.tds)
    requires toactivate_fd_ids <= MapGetKeys(k.objects.fds)
    requires toactivate_do_ids <= MapGetKeys(k.objects.dos)

    requires s_id in AllSubjsIDs(k.subjects)

    requires OwnedTDs(k, s_id) * toactivate_td_ids == {}
    requires OwnedFDs(k, s_id) * toactivate_fd_ids == {}
    requires OwnedDOs(k, s_id) * toactivate_do_ids == {}

    requires DoOwnObj(k, s_id, o_id)

    ensures TD_ID(o_id) !in toactivate_td_ids
    ensures FD_ID(o_id) !in toactivate_fd_ids
    ensures DO_ID(o_id) !in toactivate_do_ids 
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedTDs(k, s_id), toactivate_td_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedFDs(k, s_id), toactivate_fd_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedDOs(k, s_id), toactivate_do_ids);
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires K_UniqueIDsAndOwnedObjs(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids
{
    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures o_id in k'_params.objs_pids
    {
        assert IsSubjID(k.subjects, s_id);
        assert o_id in AllObjsIDs(k'_objects);
        assert MapGetKeys(BuildMap_ObjIDsToPIDs(k'_objects)) == AllObjsIDs(k'_objects);
        assert k'_params.objs_pids == BuildMap_ObjIDsToPIDs(k'_objects);
        assert o_id in k'_params.objs_pids;
    }
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingActivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID, s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires K_UniqueIDsAndOwnedObjs(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    requires IsSubjID(k.subjects, s_id)
    requires s_id in toactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    requires o_id in k'_params.objs_pids

    ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    assert TD_ID(o_id) in toactivate_td_ids || FD_ID(o_id) in toactivate_fd_ids || DO_ID(o_id) in toactivate_do_ids;
    assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingActivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID, s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in toactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in k'_objects.tds 

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    requires o_id in k'_params.objs_pids

    ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    Lemma_DrvDevActivate_InSubjsNotBeingActivated_ObjsAreUnchanged(k, k'_subjects, k'_objects, k'_params, 
        toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, s_id, o_id);
    assert TD_ID(o_id) !in toactivate_td_ids && FD_ID(o_id) !in toactivate_fd_ids && DO_ID(o_id) !in toactivate_do_ids;

    Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k, k'_subjects, k'_objects);
    if(TD_ID(o_id) in k.objects.tds)
    {
        assert k'_objects.tds[TD_ID(o_id)] == k.objects.tds[TD_ID(o_id)];
        assert k.objects.tds[TD_ID(o_id)].pid == ObjPID(k, o_id);
        assert k.objects.tds[TD_ID(o_id)].pid == SubjPID(k, s_id);
        assert k'_params.objs_pids[o_id] == k'_objects.tds[TD_ID(o_id)].pid;

        assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
    }

    if(FD_ID(o_id) in k.objects.fds)
    {
        assert k'_objects.fds[FD_ID(o_id)] == k.objects.fds[FD_ID(o_id)];
        assert k.objects.fds[FD_ID(o_id)].pid == ObjPID(k, o_id);
        assert k.objects.fds[FD_ID(o_id)].pid == SubjPID(k, s_id);
        assert k'_params.objs_pids[o_id] == k'_objects.fds[FD_ID(o_id)].pid;

        assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
    }

    if(DO_ID(o_id) in k.objects.dos)
    {
        assert k'_objects.dos[DO_ID(o_id)] == k.objects.dos[DO_ID(o_id)];
        assert k.objects.dos[DO_ID(o_id)].pid == ObjPID(k, o_id);
        assert k.objects.dos[DO_ID(o_id)].pid == SubjPID(k, s_id);
        assert k'_params.objs_pids[o_id] == k'_objects.dos[DO_ID(o_id)].pid;

        assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
    }
}

predicate SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k:State, k'_subjects:Subjects, k'_objects:Objects)
{
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&
    (MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)) &&
    (MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)) &&
    (MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)) &&
    (forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)) &&

    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)) &&

    (true)
}

lemma Lemma_DrvDevActivate_InSubjsNotBeingActivated_ObjsAreUnchanged(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in toactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated
  
    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    ensures TD_ID(o_id) !in toactivate_td_ids && FD_ID(o_id) !in toactivate_fd_ids && DO_ID(o_id) !in toactivate_do_ids
{
    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k, k'_subjects, k'_objects);
    if(TD_ID(o_id) in toactivate_td_ids)
    {
        assert exists s_id2 :: s_id2 in toactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        var s_id2 :| s_id2 in toactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in toactivate_s_ids;
    }

    if(FD_ID(o_id) in toactivate_fd_ids)
    {
        assert exists s_id2 :: s_id2 in toactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        var s_id2 :| s_id2 in toactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in toactivate_s_ids;
    }

    if(DO_ID(o_id) in toactivate_do_ids)
    {
        assert exists s_id2 :: s_id2 in toactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        var s_id2 :| s_id2 in toactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in toactivate_s_ids;
    }
}