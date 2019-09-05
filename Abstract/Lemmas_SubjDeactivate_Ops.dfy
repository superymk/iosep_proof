include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"
include "Lemmas_SubjDeactivate_ReachableTDsStates.dfy"
include "./BuildCAS/BuildCAS.dfy"

predicate SubjObjDeactivate_PropertiesOfTDs(k:State, k'_subjects:Subjects, k'_objects:Objects, todeactivate_td_ids:set<TD_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
{
    (MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)) &&
    (todeactivate_td_ids <= MapGetKeys(k.objects.tds)) &&
    (forall td_id :: td_id in todeactivate_td_ids
            ==> k'_objects.tds[td_id].pid == NULL) &&
    (forall td_id :: td_id in todeactivate_td_ids
            ==> k.objects.tds[td_id].pid != NULL) &&

    (forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val) &&
    (forall td_id :: td_id in k.objects.tds &&
                td_id !in todeactivate_td_ids
            ==> k'_objects.tds[td_id] == k.objects.tds[td_id]) &&

    (forall tds_state2, td_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}) &&

    (true) 
}

predicate SubjObjDeactivate_PropertiesOfFDs(k:State, k'_subjects:Subjects, k'_objects:Objects, todeactivate_fd_ids:set<FD_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
{
    (MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)) &&
    (todeactivate_fd_ids <= MapGetKeys(k.objects.fds)) &&
    (forall fd_id :: fd_id in todeactivate_fd_ids
            ==> k'_objects.fds[fd_id].pid == NULL) &&
    (forall fd_id :: fd_id in todeactivate_fd_ids
            ==> k.objects.fds[fd_id].pid != NULL) &&

    (forall fd_id :: fd_id in k.objects.fds
                ==> k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val) &&
    (forall fd_id :: fd_id in k.objects.fds &&
                fd_id !in todeactivate_fd_ids
            ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]) &&

    (forall tds_state2, fd_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to FDs 
        // being deactivated

    (true)
}

predicate SubjObjDeactivate_PropertiesOfDOs(k:State, k'_subjects:Subjects, k'_objects:Objects, todeactivate_do_ids:set<DO_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
{
    (MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)) &&
    (todeactivate_do_ids <= MapGetKeys(k.objects.dos)) &&
    (forall do_id :: do_id in todeactivate_do_ids
            ==> k'_objects.dos[do_id].pid == NULL) &&
    (forall do_id :: do_id in todeactivate_do_ids
            ==> k.objects.dos[do_id].pid != NULL) &&

    (forall do_id :: do_id in k.objects.dos
                ==> k'_objects.dos[do_id].val == k.objects.dos[do_id].val) &&
    (forall do_id :: do_id in k.objects.dos &&
                do_id !in todeactivate_do_ids
            ==> k'_objects.dos[do_id] == k.objects.dos[do_id]) &&

    (forall tds_state2, do_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to DOs 
        // being deactivated

    (true)
}

predicate SubjObjDeactivate_PropertiesOfSubjs(
    k:State, k'_subjects:Subjects, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
{
    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&

    (todeactivate_s_ids <= AllSubjsIDs(k.subjects)) &&
    (forall s_id :: s_id in todeactivate_s_ids 
                ==> OwnedTDs(k, s_id) <= todeactivate_td_ids &&
                    OwnedFDs(k, s_id) <= todeactivate_fd_ids &&
                    OwnedDOs(k, s_id) <= todeactivate_do_ids) &&
        // If a subject is to be deactivated, then its objects are also to be deactivated
    (forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL) &&
    (forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL) &&

    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])) &&
    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> OwnedTDs(k, s_id) * todeactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * todeactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * todeactivate_do_ids == {}) &&
        // If a subject is not to be deactivated, then its objects must not to be
        // deactivated

    (true)
}

lemma Lemma_SubjObjDeactivate_NewK_UniqueIDsAndOwnedObjs(k:State, k':State)
    requires IsValidState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    ensures K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_FulfillCommonPreConditionsOfKAndNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_PreConditionsOfK(k')
    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjDeactivate_CommonPreConditionsOfKAndNewK(k, k_params, k', k'_params,
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
{
    Lemma_SubjObjDeactivate_NewK_UniqueIDsAndOwnedObjs(k ,k');
    Lemma_SubjObjDeactivate_NewK_SubjsObjsPIDsInNewK(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_FulfillNextThreePredicates(k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_ReachableActiveTDsStatesInK_FulfillConditionsToObjsBeingDeactivated(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_ActiveObjsInNewKHasUnchangedPIDs(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

lemma Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
    k:State, k'_subjects:Subjects, k_cas:CAS, k_reachable_active_tds_states:set<TDs_Vals>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k)

    requires AllActiveDevs_SlimState(k'_subjects) <= AllActiveDevs(k)

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}

    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in k_reachable_active_tds_states &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in k_reachable_active_tds_states &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), k.reachable_active_tds_states)

    ensures forall tds_state2, td_id, dev_id :: tds_state2 in k_reachable_active_tds_states &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}
    ensures forall tds_state2, fd_id, dev_id :: tds_state2 in k_reachable_active_tds_states &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}
    ensures forall tds_state2, do_id, dev_id :: tds_state2 in k_reachable_active_tds_states &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}
{
    forall tds_state2, td_id, dev_id | tds_state2 in k_reachable_active_tds_states &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
        ensures DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}
    {
        var o_id := td_id.oid;
        var amodes := DevAModesToObj(k, tds_state2, dev_id, td_id.oid);
        assert IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {};
        assert R !in amodes;
        assert W !in amodes;
        Lemma_EmptyAModesIsNoRAndNoW(amodes);
    }

    forall tds_state2, fd_id, dev_id | tds_state2 in k_reachable_active_tds_states &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
        ensures DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}
    {
        var o_id := fd_id.oid;
        var amodes := DevAModesToObj(k, tds_state2, dev_id, fd_id.oid);
        assert IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {};
        assert R !in amodes;
        assert W !in amodes;
        Lemma_EmptyAModesIsNoRAndNoW(amodes);
    }

    forall tds_state2, do_id, dev_id | tds_state2 in k_reachable_active_tds_states &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
        ensures DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}
    {
        var o_id := do_id.oid;
        var amodes := DevAModesToObj(k, tds_state2, dev_id, do_id.oid);
        assert IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {};
        assert R !in amodes;
        assert W !in amodes;
        Lemma_EmptyAModesIsNoRAndNoW(amodes);
    }
}

lemma Lemma_ExternalObjsDeactivate_AllObjsToBeDeactivatedAreExternalObjs(
    k:State,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in todeactivate_td_ids || FD_ID(o_id) in todeactivate_fd_ids || DO_ID(o_id) in todeactivate_do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
            ==> OwnedTDs(k, s_id) * todeactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * todeactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * todeactivate_do_ids == {}

    ensures {} <= AllSubjsIDs(k.subjects)
{
    forall s_id | s_id in AllSubjsIDs(k.subjects)
        ensures OwnedTDs(k, s_id) * todeactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * todeactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * todeactivate_do_ids == {}
    {
        assert forall td_id :: td_id in todeactivate_td_ids
                ==> !DoOwnObj(k, s_id, td_id.oid);
        assert forall fd_id :: fd_id in todeactivate_fd_ids
                ==> !DoOwnObj(k, s_id, fd_id.oid);
        assert forall do_id :: do_id in todeactivate_do_ids
                ==> !DoOwnObj(k, s_id, do_id.oid);

        assert forall td_id :: td_id in todeactivate_td_ids
                ==> td_id !in OwnedTDs(k, s_id);
        assert forall fd_id :: fd_id in todeactivate_fd_ids
                ==> fd_id !in OwnedFDs(k, s_id);
        assert forall do_id :: do_id in todeactivate_do_ids
                ==> do_id !in OwnedDOs(k, s_id);
    }

    Lemma_EmptySetIsSubsetOfAnySet(AllSubjsIDs(k.subjects));
}

lemma Lemma_ExternalObjsDeactivate_HCodedTDsAreUnchanged(
    k:State, k'_subjects_devs:map<Dev_ID, Dev_State>, tds':map<TD_ID, TD_State>, tds_to_deactivate:set<TD_ID>
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
    requires tds_to_deactivate <= MapGetKeys(k.objects.tds)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_deactivate
                ==> !DoOwnObj(k, s_id, td_id.oid)
        // Requirement: TDs to be activated must be external TDs
    requires forall td_id :: td_id in k.objects.tds && td_id !in tds_to_deactivate
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
        if (hcoded_td_id in tds_to_deactivate)
        {
            // Show conflict
            assert !DoOwnObj(k, dev_id.sid, hcoded_td_id.oid);
            assert DoOwnObj(k, dev_id.sid, hcoded_td_id.oid);
        }
        assert hcoded_td_id !in tds_to_deactivate;
    }
}

lemma Lemma_SubjObjDeactivate_NewKParams_HasUnmodifiedVarsFromKParams(
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

lemma Lemma_ExternalObjsDeactivate_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams,
    tds_to_deactivate:set<TD_ID>, fds_to_deactivate:set<FD_ID>, dos_to_deactivate:set<DO_ID>
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
    requires tds_to_deactivate <= MapGetKeys(k.objects.tds)
    requires fds_to_deactivate <= MapGetKeys(k.objects.fds)
    requires dos_to_deactivate <= MapGetKeys(k.objects.dos)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_deactivate
                ==> !DoOwnObj(k, s_id, td_id.oid)
    requires forall s_id, fd_id :: s_id in AllSubjsIDs(k.subjects) &&
                    fd_id in fds_to_deactivate
                ==> !DoOwnObj(k, s_id, fd_id.oid)
    requires forall s_id, do_id :: s_id in AllSubjsIDs(k.subjects) &&
                    do_id in dos_to_deactivate
                ==> !DoOwnObj(k, s_id, do_id.oid)
        // Requirement: TDs/FDs/DOs to be activated must be external TDs/FDs/DOs
    requires forall td_id :: td_id in k.objects.tds && td_id !in tds_to_deactivate
                ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    requires forall fd_id :: fd_id in k.objects.fds && fd_id !in fds_to_deactivate
                ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    requires forall do_id :: do_id in k.objects.dos && do_id !in dos_to_deactivate
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
            assert td_id !in tds_to_deactivate;
            assert k'_objects.tds[td_id] == k.objects.tds[td_id];
            assert k'_params.objs_pids[o_id] == k.objects.tds[td_id].pid;
        }
        else if(FD_ID(o_id) in k.objects.fds)
        {
            var fd_id := FD_ID(o_id);
            assert fd_id !in fds_to_deactivate;
            assert k'_objects.fds[fd_id] == k.objects.fds[fd_id];
            assert k'_params.objs_pids[o_id] == k.objects.fds[fd_id].pid;
        }
        else
        {
            var do_id := DO_ID(o_id);
            assert DO_ID(o_id) in k.objects.dos;
            assert do_id !in dos_to_deactivate;
            assert k'_objects.dos[do_id] == k.objects.dos[do_id];
            assert k'_params.objs_pids[o_id] == k.objects.dos[do_id].pid;
        }
    }
}

lemma Lemma_SubjObjDeactivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, k'_active_devs:set<Dev_ID>, k'_active_tds_state:TDs_Vals,
    explored_tds_states:seq<set<TDs_Vals>>, found_tds_states:set<TDs_Vals>
)
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
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

lemma Lemma_SubjObjDeactivate_NewK_FulfillSI2(
    k:State, k':State,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k.pids == k'.pids

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures IsSecureState_SI2(k')
{
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    forall s_id | s_id in AllSubjsIDs(k'.subjects) && SubjPID(k', s_id) != NULL
        ensures SubjPID(k', s_id) in k'.pids
    {
        assert s_id in todeactivate_s_ids || SubjPID(k, s_id) != NULL;
        assert s_id in AllSubjsIDs(k.subjects);
    }

    forall o_id | o_id in AllObjsIDs(k'.objects) && ObjPID(k', o_id) != NULL
        ensures ObjPID(k', o_id) in k'.pids
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_DrvDevDeactivate_SubjsNotBeingDeactivatedDoNotOwnAnyObjsBeingDeactivated(
    k:State, k'_subjects:Subjects, todeactivate_s_ids:set<Subject_ID>,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
        // Requirement: All subjects to be activated are inactive in k' 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k'_subjects)
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> OwnedTDs(k, s_id) * todeactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * todeactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * todeactivate_do_ids == {}
{
    assert forall s_id :: s_id in todeactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k'_subjects);

    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    forall s_id | s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
        ensures OwnedTDs(k, s_id) * todeactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * todeactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * todeactivate_do_ids == {}
    { 
        if(exists td_id :: td_id in OwnedTDs(k, s_id) && td_id in todeactivate_td_ids)
        {
            var td_id :| td_id in OwnedTDs(k, s_id) && td_id in todeactivate_td_ids;
            var s_id2 :| s_id2 in todeactivate_s_ids && td_id in OwnedTDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, td_id.oid);
            assert DoOwnObj(k, s_id2, td_id.oid);
        }

        if(exists fd_id :: fd_id in OwnedFDs(k, s_id) && fd_id in todeactivate_fd_ids)
        {
            var fd_id :| fd_id in OwnedFDs(k, s_id) && fd_id in todeactivate_fd_ids;
            var s_id2 :| s_id2 in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, fd_id.oid);
            assert DoOwnObj(k, s_id2, fd_id.oid);
        }

        if(exists do_id :: do_id in OwnedDOs(k, s_id) && do_id in todeactivate_do_ids)
        {
            var do_id :| do_id in OwnedDOs(k, s_id) && do_id in todeactivate_do_ids;
            var s_id2 :| s_id2 in todeactivate_s_ids && do_id in OwnedDOs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, do_id.oid);
            assert DoOwnObj(k, s_id2, do_id.oid);
        }
    }
}

lemma Lemma_DrvDeactivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires IsValidState(k) && IsSecureState(k)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)

    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires new_drv_state.pid == NULL

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), AllReachableActiveTDsStates(k))

    requires SubjPID_SlimState(k.subjects, todeactivate_drv_id.sid) != NULL
        // Requirement: the driver to be deactivated must be active in k
    requires forall td_id :: td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
                ==> k.objects.tds[td_id].pid != NULL && k'_objects.tds[td_id].pid == NULL
    requires forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val
    requires forall td_id :: td_id in k.objects.tds &&
                td_id !in k.subjects.drvs[todeactivate_drv_id].td_ids
            ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    requires forall fd_id :: fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
                ==> k.objects.fds[fd_id].pid != NULL && k'_objects.fds[fd_id].pid == NULL
    requires forall fd_id :: fd_id in k.objects.fds
                ==> k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val
    requires forall fd_id :: fd_id in k.objects.fds &&
                fd_id !in k.subjects.drvs[todeactivate_drv_id].fd_ids
            ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    requires forall do_id :: do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
                ==> k.objects.dos[do_id].pid != NULL && k'_objects.dos[do_id].pid == NULL
    requires forall do_id :: do_id in k.objects.dos
                ==> k'_objects.dos[do_id].val == k.objects.dos[do_id].val
    requires forall do_id :: do_id in k.objects.dos &&
                do_id !in k.subjects.drvs[todeactivate_drv_id].do_ids
            ==> k'_objects.dos[do_id] == k.objects.dos[do_id]

    ensures SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, k.subjects.drvs[todeactivate_drv_id].td_ids)
    ensures SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, k.subjects.drvs[todeactivate_drv_id].fd_ids)
    ensures SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, k.subjects.drvs[todeactivate_drv_id].do_ids)
    ensures SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, {todeactivate_drv_id.sid}, 
                k.subjects.drvs[todeactivate_drv_id].td_ids, k.subjects.drvs[todeactivate_drv_id].fd_ids, k.subjects.drvs[todeactivate_drv_id].do_ids)
{
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[todeactivate_drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[todeactivate_drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[todeactivate_drv_id].do_ids;

    var todeactivate_s_ids:set<Subject_ID> := {todeactivate_drv_id.sid};
    var todeactivate_td_ids := tds_owned_by_drv;
    var todeactivate_fd_ids := fds_owned_by_drv;
    var todeactivate_do_ids := dos_owned_by_drv;

    Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
            k, k'_subjects, k_cas, AllReachableActiveTDsStates(k), 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_SubjsNotBeingDeactivatedDoNotOwnAnyObjsBeingDeactivated(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_AllObjsToBeActivatedAreActiveInK(k, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids);
    assert SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids);
    assert SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

lemma Lemma_DrvDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires SubjPID(k, todeactivate_drv_id.sid) != NULL
    requires new_drv_state.pid == NULL
    requires todeactivate_s_ids == {todeactivate_drv_id.sid}

    ensures todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    ensures MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)

    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires IsValidState(k) && IsSecureState(k)

    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires SubjPID(k, todeactivate_drv_id.sid) != NULL
    requires new_drv_state.pid == NULL

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)

    requires forall td_id :: td_id in k.objects.tds
                ==> (td_id in k.subjects.drvs[todeactivate_drv_id].td_ids ==> (k'_objects.tds[td_id].pid == NULL && k'_objects.tds[td_id].val == k.objects.tds[td_id].val)) &&
                    (td_id !in k.subjects.drvs[todeactivate_drv_id].td_ids ==> k'_objects.tds[td_id] == k.objects.tds[td_id])
    requires forall fd_id :: fd_id in k.objects.fds
                ==> (fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids ==> (k'_objects.fds[fd_id].pid == NULL && k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val)) &&
                    (fd_id !in k.subjects.drvs[todeactivate_drv_id].fd_ids ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id])
    requires forall do_id :: do_id in k.objects.dos
                ==> (do_id in k.subjects.drvs[todeactivate_drv_id].do_ids ==> (k'_objects.dos[do_id].pid == NULL && k'_objects.dos[do_id].val == k.objects.dos[do_id].val)) &&
                    (do_id !in k.subjects.drvs[todeactivate_drv_id].do_ids ==> k'_objects.dos[do_id] == k.objects.dos[do_id])

    requires P_ObjsInSubjsAreAlsoInState(k)
    requires forall o_id, dev_id :: o_id in OwnObjIDs(k, todeactivate_drv_id.sid) && dev_id in AllActiveDevs(k) 
            ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}

    ensures forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    ensures forall td_id :: td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
                ==> k.objects.tds[td_id].pid != NULL && k'_objects.tds[td_id].pid == NULL
    ensures forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val
    ensures forall td_id :: td_id in k.objects.tds &&
                td_id !in k.subjects.drvs[todeactivate_drv_id].td_ids
            ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    ensures forall fd_id :: fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
                ==> k.objects.fds[fd_id].pid != NULL && k'_objects.fds[fd_id].pid == NULL
    ensures forall fd_id :: fd_id in k.objects.fds
                ==> k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val
    ensures forall fd_id :: fd_id in k.objects.fds &&
                fd_id !in k.subjects.drvs[todeactivate_drv_id].fd_ids
            ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    ensures forall do_id :: do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
                ==> k.objects.dos[do_id].pid != NULL && k'_objects.dos[do_id].pid == NULL
    ensures forall do_id :: do_id in k.objects.dos
                ==> k'_objects.dos[do_id].val == k.objects.dos[do_id].val
    ensures forall do_id :: do_id in k.objects.dos &&
                do_id !in k.subjects.drvs[todeactivate_drv_id].do_ids
            ==> k'_objects.dos[do_id] == k.objects.dos[do_id]
{
    forall td_id | td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
        ensures k.objects.tds[td_id].pid != NULL
    {
        assert DoOwnObj(k, todeactivate_drv_id.sid, td_id.oid);
    }
    forall fd_id | fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
        ensures k.objects.fds[fd_id].pid != NULL
    {
        assert DoOwnObj(k, todeactivate_drv_id.sid, fd_id.oid);
    }
    forall do_id | do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
        ensures k.objects.dos[do_id].pid != NULL
    {
        assert DoOwnObj(k, todeactivate_drv_id.sid, do_id.oid);
    }
}

lemma Lemma_DrvDevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK(
    k:State, k'_subjects:Subjects, todeactivate_s_ids:set<Subject_ID>
)
    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)

    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
    requires forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])

    ensures AllActiveDevs_SlimState(k'_subjects) <= AllActiveDevs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

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
    Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(k, k'_subjects, k'_objects, k'_params, 
        todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
    {
        if(s_id in todeactivate_s_ids)
        {
            Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingDeactivated(
                k, k'_subjects, k'_objects, k'_params, 
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
        }
        else
        {
            Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingDeactivated(
                k, k'_subjects, k'_objects, k'_params, 
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
        }
    }
}

lemma Lemma_DrvDeactivate_OwnershipOfObjsIsPreserved(
    k:State, k'_subjects:Subjects,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires new_drv_state.td_ids == IDToDrv(k, todeactivate_drv_id).td_ids
    requires new_drv_state.fd_ids == IDToDrv(k, todeactivate_drv_id).fd_ids
    requires new_drv_state.do_ids == IDToDrv(k, todeactivate_drv_id).do_ids

    ensures forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDeactivate_SameSetOfActiveDevsInNewKAndK(
    k:State, k'_subjects:Subjects,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires IsValidState(k)
    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    ensures AllActiveDevs_SlimState(k'_subjects) == AllActiveDevs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires SubjPID(k, todeactivate_dev_id.sid) != NULL
    requires new_dev_state.pid == NULL
    requires todeactivate_s_ids == {todeactivate_dev_id.sid}

    ensures todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    ensures MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    ensures MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)

    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])
{
    // Dafny can automatically prove this lemma
    forall s_id | s_id in todeactivate_s_ids
        ensures SubjPID_SlimState(k'_subjects, s_id) == NULL
    {
        assert s_id == todeactivate_dev_id.sid;
        assert Dev_ID(s_id) in k.subjects.devs;
        assert Dev_ID(s_id) in k'_subjects.devs;
        assert Drv_ID(s_id) !in k'_subjects.drvs;

        assert SubjPID_SlimState(k'_subjects, s_id) == k'_subjects.devs[Dev_ID(s_id)].pid;
    }
}

lemma Lemma_DevDeactivate_BuildMap_DevsToHCodedTDVals_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.hcoded_td_id == k.subjects.devs[todeactivate_dev_id].hcoded_td_id
    requires new_dev_state.td_ids == k.subjects.devs[todeactivate_dev_id].td_ids

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds) 

    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    ensures forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in k'_objects.tds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k) && IsSecureState(k)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.pid == NULL

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), AllReachableActiveTDsStates(k))

    requires SubjPID_SlimState(k.subjects, todeactivate_dev_id.sid) != NULL
        // Requirement: the driver to be deactivated must be active in k
    requires forall td_id :: td_id in k.subjects.devs[todeactivate_dev_id].td_ids
                ==> k.objects.tds[td_id].pid != NULL && k'_objects.tds[td_id].pid == NULL
    requires forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val
    requires forall td_id :: td_id in k.objects.tds &&
                td_id !in k.subjects.devs[todeactivate_dev_id].td_ids
            ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    requires forall fd_id :: fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
                ==> k.objects.fds[fd_id].pid != NULL && k'_objects.fds[fd_id].pid == NULL
    requires forall fd_id :: fd_id in k.objects.fds
                ==> k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val
    requires forall fd_id :: fd_id in k.objects.fds &&
                fd_id !in k.subjects.devs[todeactivate_dev_id].fd_ids
            ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    requires forall do_id :: do_id in k.subjects.devs[todeactivate_dev_id].do_ids
                ==> k.objects.dos[do_id].pid != NULL && k'_objects.dos[do_id].pid == NULL
    requires forall do_id :: do_id in k.objects.dos
                ==> k'_objects.dos[do_id].val == k.objects.dos[do_id].val
    requires forall do_id :: do_id in k.objects.dos &&
                do_id !in k.subjects.devs[todeactivate_dev_id].do_ids
            ==> k'_objects.dos[do_id] == k.objects.dos[do_id]

    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
        // Property needed by the proeprties below
    ensures SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, k.subjects.devs[todeactivate_dev_id].td_ids)
    ensures SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, k.subjects.devs[todeactivate_dev_id].fd_ids)
    ensures SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, k.subjects.devs[todeactivate_dev_id].do_ids)
    ensures SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, {todeactivate_dev_id.sid}, 
                k.subjects.devs[todeactivate_dev_id].td_ids, k.subjects.devs[todeactivate_dev_id].fd_ids, k.subjects.devs[todeactivate_dev_id].do_ids)
{
    var tds_owned_by_drv:set<TD_ID> := k.subjects.devs[todeactivate_dev_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.devs[todeactivate_dev_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.devs[todeactivate_dev_id].do_ids;

    var todeactivate_s_ids:set<Subject_ID> := {todeactivate_dev_id.sid};
    var todeactivate_td_ids := tds_owned_by_drv;
    var todeactivate_fd_ids := fds_owned_by_drv;
    var todeactivate_do_ids := dos_owned_by_drv;

    Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
            k, k'_subjects, k_cas, AllReachableActiveTDsStates(k), 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_SubjsNotBeingDeactivatedDoNotOwnAnyObjsBeingDeactivated(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_AllObjsToBeActivatedAreActiveInK(k, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids);
    assert SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids);
    assert SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

lemma Lemma_DevDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k) && IsSecureState(k)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires SubjPID(k, todeactivate_dev_id.sid) != NULL
    requires new_dev_state.pid == NULL

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)

    requires forall td_id :: td_id in k.objects.tds
                ==> (td_id in k.subjects.devs[todeactivate_dev_id].td_ids ==> (k'_objects.tds[td_id].pid == NULL && k'_objects.tds[td_id].val == k.objects.tds[td_id].val)) &&
                    (td_id !in k.subjects.devs[todeactivate_dev_id].td_ids ==> k'_objects.tds[td_id] == k.objects.tds[td_id])
    requires forall fd_id :: fd_id in k.objects.fds
                ==> (fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids ==> (k'_objects.fds[fd_id].pid == NULL && k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val)) &&
                    (fd_id !in k.subjects.devs[todeactivate_dev_id].fd_ids ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id])
    requires forall do_id :: do_id in k.objects.dos
                ==> (do_id in k.subjects.devs[todeactivate_dev_id].do_ids ==> (k'_objects.dos[do_id].pid == NULL && k'_objects.dos[do_id].val == k.objects.dos[do_id].val)) &&
                    (do_id !in k.subjects.devs[todeactivate_dev_id].do_ids ==> k'_objects.dos[do_id] == k.objects.dos[do_id])

    requires P_ObjsInSubjsAreAlsoInState(k)
    requires forall o_id, dev_id2 :: 
            (o_id in OwnObjIDs(k, todeactivate_dev_id.sid)) && 
            (dev_id2 in AllActiveDevs(k) - {todeactivate_dev_id})
            ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {}

    ensures forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    ensures forall td_id :: td_id in k.subjects.devs[todeactivate_dev_id].td_ids
                ==> k.objects.tds[td_id].pid != NULL && k'_objects.tds[td_id].pid == NULL
    ensures forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val
    ensures forall td_id :: td_id in k.objects.tds &&
                td_id !in k.subjects.devs[todeactivate_dev_id].td_ids
            ==> k'_objects.tds[td_id] == k.objects.tds[td_id]
    ensures forall fd_id :: fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
                ==> k.objects.fds[fd_id].pid != NULL && k'_objects.fds[fd_id].pid == NULL
    ensures forall fd_id :: fd_id in k.objects.fds
                ==> k'_objects.fds[fd_id].val == k.objects.fds[fd_id].val
    ensures forall fd_id :: fd_id in k.objects.fds &&
                fd_id !in k.subjects.devs[todeactivate_dev_id].fd_ids
            ==> k'_objects.fds[fd_id] == k.objects.fds[fd_id]
    ensures forall do_id :: do_id in k.subjects.devs[todeactivate_dev_id].do_ids
                ==> k.objects.dos[do_id].pid != NULL && k'_objects.dos[do_id].pid == NULL
    ensures forall do_id :: do_id in k.objects.dos
                ==> k'_objects.dos[do_id].val == k.objects.dos[do_id].val
    ensures forall do_id :: do_id in k.objects.dos &&
                do_id !in k.subjects.devs[todeactivate_dev_id].do_ids
            ==> k'_objects.dos[do_id] == k.objects.dos[do_id]
{
    forall td_id | td_id in k.subjects.devs[todeactivate_dev_id].td_ids
        ensures k.objects.tds[td_id].pid != NULL
    {
        assert DoOwnObj(k, todeactivate_dev_id.sid, td_id.oid);
    }
    forall fd_id | fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
        ensures k.objects.fds[fd_id].pid != NULL
    {
        assert DoOwnObj(k, todeactivate_dev_id.sid, fd_id.oid);
    }
    forall do_id | do_id in k.subjects.devs[todeactivate_dev_id].do_ids
        ensures k.objects.dos[do_id].pid != NULL
    {
        assert DoOwnObj(k, todeactivate_dev_id.sid, do_id.oid);
    }
}

lemma Lemma_DevDeactivate_ActiveDevsInNewKIsActiveDevsInKMinusDevToBeDeactivated(
    k:State, k'_subjects:Subjects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires SubjPID(k, todeactivate_dev_id.sid) != NULL
    requires new_dev_state.pid == NULL

    ensures AllActiveDevs_SlimState(k'_subjects) == AllActiveDevs(k) - {todeactivate_dev_id}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_OwnershipOfObjsIsPreserved(
    k:State, k'_subjects:Subjects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.hcoded_td_id == IDToDev(k, todeactivate_dev_id).hcoded_td_id
    requires new_dev_state.td_ids == IDToDev(k, todeactivate_dev_id).td_ids
    requires new_dev_state.fd_ids == IDToDev(k, todeactivate_dev_id).fd_ids
    requires new_dev_state.do_ids == IDToDev(k, todeactivate_dev_id).do_ids

    ensures forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_HCodedTDsHaveUnmodifiedVals(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)

    requires forall td_id :: td_id in k.objects.tds
                ==> k'_objects.tds[td_id].val == k.objects.tds[td_id].val

    requires new_dev_state.hcoded_td_id == k.subjects.devs[todeactivate_dev_id].hcoded_td_id

    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.tds[k.subjects.devs[dev_id].hcoded_td_id].val
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_UnchangedStateVarsBetweenKandNewK(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.hcoded_td_id == k.subjects.devs[todeactivate_dev_id].hcoded_td_id
    requires new_dev_state.td_ids == k.subjects.devs[todeactivate_dev_id].td_ids
    requires new_dev_state.fd_ids == k.subjects.devs[todeactivate_dev_id].fd_ids
    requires new_dev_state.do_ids == k.subjects.devs[todeactivate_dev_id].do_ids

    requires MapGetKeys(k'_objects.tds) == MapGetKeys(k.objects.tds)
    requires MapGetKeys(k'_objects.fds) == MapGetKeys(k.objects.fds)
    requires MapGetKeys(k'_objects.dos) == MapGetKeys(k.objects.dos)

    ensures SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ProveIsValidState_Subjects(
    k:State, k':State,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState_Subjects(k)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'.subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)

    ensures IsValidState_Subjects(k')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_ProveNewKTDsToAllStatesContainsAllSetsOfTDs(
    k:State, tds':map<TD_ID, TD_State>, k'_objs_td_ids:set<TD_ID>, k'_tds_to_all_states:map<set<TD_ID>, set<TDs_Vals>>
)
    requires IsValidState_TDsToAllStates(k)
    
    requires MapGetKeys(tds') == MapGetKeys(k.objects.tds)
    requires k'_objs_td_ids == MapGetKeys<TD_ID, TD_State>(tds')
    requires k'_tds_to_all_states == k.tds_to_all_states
    
    ensures forall td_ids :: td_ids in k'_tds_to_all_states
                <==> td_ids <= MapGetKeys<TD_ID, TD_State>(k.objects.tds)
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas  ********//
lemma Lemma_SubjObjDeactivate_NewK_ActiveObjsInNewKHasUnchangedPIDs(
    k:State, k':State,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures forall o_id :: o_id in AllActiveObjs(k')
                ==> ObjPID(k, o_id) == ObjPID(k', o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_NewK_ReachableActiveTDsStatesInK_FulfillConditionsToObjsBeingDeactivated(
    k:State, k':State,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)
    ensures SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToFDsAndDOsBeingDeactivated(
                k, k', todeactivate_fd_ids, todeactivate_do_ids)
{
    // Dafny can automatically prove this lemma
}

// (needs 100s to verify)
lemma Lemma_SubjObjDeactivate_NewK_FulfillNextThreePredicates(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    ensures SubjObjDeactivate_PreConditionsOfK(k')
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_NewK_PreConditionsOfSubjObjToDeactivate(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_PreConditionsOfK(k)
    ensures SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
{
    Lemma_AllActiveObjs_SlimState_Property(k.objects);

    forall drv_id2:Drv_ID | IsDrvID(k, drv_id2) &&
                    drv_id2.sid !in todeactivate_s_ids
        ensures k'.subjects.drvs[drv_id2] == k.subjects.drvs[drv_id2]
    {
        assert drv_id2.sid in AllSubjsIDs(k.subjects);
        assert drv_id2 in k.subjects.drvs;
    }
}

lemma Lemma_SubjObjDeactivate_NewK_SubjsObjsPIDsInNewK(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
{
    Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(
        k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

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

lemma Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, MapGetKeys(k'.objects.tds), MapGetKeys(k'.objects.fds), MapGetKeys(k'.objects.dos))
    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
{
    forall s_id, o_id | s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
        ensures SubjPID(k', s_id) == ObjPID(k', o_id)
    {
        if(s_id !in todeactivate_s_ids)
        {
            assert DoOwnObj(k, s_id, o_id);
            Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(
                k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
            assert TD_ID(o_id) !in todeactivate_td_ids;
            assert FD_ID(o_id) !in todeactivate_fd_ids;
            assert DO_ID(o_id) !in todeactivate_do_ids;

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
            assert s_id in todeactivate_s_ids;

            assert SubjPID_SlimState(k'.subjects, s_id) == NULL;
            if(Drv_ID(s_id) in k.subjects.drvs)
            {
                assert TD_ID(o_id) in todeactivate_td_ids || 
                       FD_ID(o_id) in todeactivate_fd_ids ||
                       DO_ID(o_id) in todeactivate_do_ids;

                assert ObjPID(k', o_id) == NULL;
            }
            else
            {
                assert Dev_ID(s_id) in k.subjects.devs;
                assert TD_ID(o_id) in todeactivate_td_ids || 
                       FD_ID(o_id) in todeactivate_fd_ids ||
                       DO_ID(o_id) in todeactivate_do_ids;

                assert ObjPID(k', o_id) == NULL;
            }
        }
    }
}

lemma Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(
    k:State,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)

    requires todeactivate_td_ids <= MapGetKeys(k.objects.tds)
    requires todeactivate_fd_ids <= MapGetKeys(k.objects.fds)
    requires todeactivate_do_ids <= MapGetKeys(k.objects.dos)

    requires s_id in AllSubjsIDs(k.subjects)

    requires OwnedTDs(k, s_id) * todeactivate_td_ids == {}
    requires OwnedFDs(k, s_id) * todeactivate_fd_ids == {}
    requires OwnedDOs(k, s_id) * todeactivate_do_ids == {}

    requires DoOwnObj(k, s_id, o_id)

    ensures TD_ID(o_id) !in todeactivate_td_ids
    ensures FD_ID(o_id) !in todeactivate_fd_ids
    ensures DO_ID(o_id) !in todeactivate_do_ids 
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedTDs(k, s_id), todeactivate_td_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedFDs(k, s_id), todeactivate_fd_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedDOs(k, s_id), todeactivate_do_ids);
}

lemma Lemma_DrvDevDeactivate_AllObjsToBeActivatedAreActiveInK(
    k:State, todeactivate_s_ids:set<Subject_ID>,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
        // Requirement: All subjects to be activated are inactive in k 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall td_id :: td_id in todeactivate_td_ids
            ==> k.objects.tds[td_id].pid != NULL
    ensures forall fd_id :: fd_id in todeactivate_fd_ids
            ==> k.objects.fds[fd_id].pid != NULL
    ensures forall do_id :: do_id in todeactivate_do_ids
            ==> k.objects.dos[do_id].pid != NULL
{
    forall td_id | td_id in todeactivate_td_ids
        ensures k.objects.tds[td_id].pid != NULL
    {
        assert exists s_id :: s_id in todeactivate_s_ids && DoOwnObj(k, s_id, td_id.oid);
        assert k.objects.tds[td_id].pid != NULL;
    }

    forall fd_id | fd_id in todeactivate_fd_ids
        ensures k.objects.fds[fd_id].pid != NULL
    {
        assert exists s_id :: s_id in todeactivate_s_ids && DoOwnObj(k, s_id, fd_id.oid);
        assert k.objects.fds[fd_id].pid != NULL;
    }

    forall do_id | do_id in todeactivate_do_ids
        ensures k.objects.dos[do_id].pid != NULL
    {
        assert exists s_id :: s_id in todeactivate_s_ids && DoOwnObj(k, s_id, do_id.oid);
        assert k.objects.dos[do_id].pid != NULL;
    }
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

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

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingDeactivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

    requires IsSubjID(k.subjects, s_id)
    requires s_id in todeactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated

    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    requires o_id in k'_params.objs_pids

    ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    assert TD_ID(o_id) in todeactivate_td_ids || FD_ID(o_id) in todeactivate_fd_ids || DO_ID(o_id) in todeactivate_do_ids;
    assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingDeactivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in todeactivate_s_ids
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
    Lemma_DrvDevDeactivate_InSubjsNotBeingDeactivated_ObjsAreUnchanged(k, k'_subjects, k'_objects, k'_params, 
        todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
    assert TD_ID(o_id) !in todeactivate_td_ids && FD_ID(o_id) !in todeactivate_fd_ids && DO_ID(o_id) !in todeactivate_do_ids;

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

lemma Lemma_DrvDevDeactivate_InSubjsNotBeingDeactivated_ObjsAreUnchanged(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds 

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in todeactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated
  
    requires k'_params == ReachableTDsKParams(k'_subjects, MapGetKeys(k'_objects.tds), MapGetKeys(k'_objects.fds), MapGetKeys(k'_objects.dos),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects.tds))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    ensures TD_ID(o_id) !in todeactivate_td_ids && FD_ID(o_id) !in todeactivate_fd_ids && DO_ID(o_id) !in todeactivate_do_ids
{
    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k, k'_subjects, k'_objects);
    if(TD_ID(o_id) in todeactivate_td_ids)
    {
        assert exists s_id2 :: s_id2 in todeactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        var s_id2 :| s_id2 in todeactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in todeactivate_s_ids;
    }

    if(FD_ID(o_id) in todeactivate_fd_ids)
    {
        assert exists s_id2 :: s_id2 in todeactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        var s_id2 :| s_id2 in todeactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in todeactivate_s_ids;
    }

    if(DO_ID(o_id) in todeactivate_do_ids)
    {
        assert exists s_id2 :: s_id2 in todeactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        var s_id2 :| s_id2 in todeactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in todeactivate_s_ids;
    }
}

lemma Lemma_DevDeactivate_NoTransferToDevToBeDeactivated_Equivilant(
    k:State, dev_sid:Subject_ID, k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
    requires tds_states_set == AllReachableActiveTDsStates(k)
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, dev_sid)) && 
                (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)})
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            <==>
            (forall o_id, dev_id2 :: o_id in OwnObjIDs(k, dev_sid) && 
                        dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);

    if(forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, dev_sid)) && 
                (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)})
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    {
        forall o_id, dev_id2 | o_id in OwnObjIDs(k, dev_sid) && 
                        dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
            ensures forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            assert IsInCAS(k_cas, dev_id2, o_id);
            assert CASGetAModes(k_cas, dev_id2, o_id) == {};

            assert dev_id2 in AllActiveDevs(k) && o_id in AllActiveObjs(k);
            if(exists tds_state2 :: tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
            {
                var tds_state2 :| tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};

                AllReqNonEmptyAModesMustContainROrW();
                assert R in DevAModesToObj(k, tds_state2, dev_id2, o_id) ||
                       W in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in  CASGetAModes(k_cas, dev_id2, o_id);
                IfAModesContainROrWThenNotEmpty();
                assert CASGetAModes(k_cas, dev_id2, o_id) != {};
            }
        }
    }

    if(forall o_id, dev_id2 :: o_id in OwnObjIDs(k, dev_sid) && 
                        dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
    {
        forall o_id, dev_id2 |(o_id in OwnObjIDs(k, dev_sid)) &&
                (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)})
            ensures IsInCAS(k_cas, dev_id2, o_id) 
            ensures CASGetAModes(k_cas, dev_id2, o_id) == {}
        {
            assert dev_id2 in AllActiveDevs(k);

            assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
            Lemma_OwnObjIDs_Property(k, dev_sid);
            assert DoOwnObj(k, dev_sid, o_id);
            assert ObjPID(k, o_id) != NULL;
            assert o_id in AllActiveObjs(k);

            assert IsInCAS(k_cas, dev_id2, o_id);

            assert (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {});
            if(CASGetAModes(k_cas, dev_id2, o_id) != {})
            {
                AllReqNonEmptyAModesMustContainROrW();
                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in CASGetAModes(k_cas, dev_id2, o_id);

                assert (exists tds_state2 :: tds_state2 in tds_states_set && R in DevAModesToObj(k, tds_state2, dev_id2, o_id)) ||
                       (exists tds_state2 :: tds_state2 in tds_states_set && W in DevAModesToObj(k, tds_state2, dev_id2, o_id));
                IfAModesContainROrWThenNotEmpty();
                assert exists tds_state2 :: tds_state2 in tds_states_set && DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};
            }
        }
    }
}

lemma Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires tds_states_set == AllReachableActiveTDsStates(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in k.objects.tds
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in k.objects.fds
    requires forall id :: id in todeactivate_do_ids 
                ==> id in k.objects.dos

    requires forall id :: id in todeactivate_td_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_fd_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_do_ids 
                ==> ObjPID(k, id.oid) != NULL
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            <==>
            (forall o_id, dev_id2 :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Right(
        k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set);
    Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Left(
        k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set);
}

// (needs 30s to verify)
lemma Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Right(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires tds_states_set == AllReachableActiveTDsStates(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in k.objects.tds
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in k.objects.fds
    requires forall id :: id in todeactivate_do_ids 
                ==> id in k.objects.dos
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            ==>
            (forall o_id, dev_id2 :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    var all_objs_todeactivate := TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids);
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);

    if(forall o_id, dev_id2 :: 
                (o_id in all_objs_todeactivate) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    {
        forall o_id, dev_id2 | o_id in all_objs_todeactivate && 
                        dev_id2 in AllActiveDevs(k)
            ensures forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            assert IsInCAS(k_cas, dev_id2, o_id);
            assert CASGetAModes(k_cas, dev_id2, o_id) == {};

            assert dev_id2 in AllActiveDevs(k) && o_id in AllActiveObjs(k);
            if(exists tds_state2 :: tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
            {
                var tds_state2 :| tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};

                AllReqNonEmptyAModesMustContainROrW();
                assert R in DevAModesToObj(k, tds_state2, dev_id2, o_id) ||
                       W in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in  CASGetAModes(k_cas, dev_id2, o_id);
                IfAModesContainROrWThenNotEmpty();
                assert CASGetAModes(k_cas, dev_id2, o_id) != {};
            }
        }
    }
}

// (needs 50s to verify)
lemma Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Left(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires tds_states_set == AllReachableActiveTDsStates(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in k.objects.tds
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in k.objects.fds
    requires forall id :: id in todeactivate_do_ids 
                ==> id in k.objects.dos

    requires forall id :: id in todeactivate_td_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_fd_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_do_ids 
                ==> ObjPID(k, id.oid) != NULL
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            <==
            (forall o_id, dev_id2 :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    var all_objs_todeactivate := TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids);
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);

    if(forall o_id, dev_id2 :: o_id in all_objs_todeactivate && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
    {
        forall o_id, dev_id2 |(o_id in all_objs_todeactivate) &&
                (dev_id2 in AllActiveDevs(k))
            ensures IsInCAS(k_cas, dev_id2, o_id) 
            ensures CASGetAModes(k_cas, dev_id2, o_id) == {}
        {
            assert dev_id2 in AllActiveDevs(k);

            assert ObjPID(k, o_id) != NULL;
            assert o_id in AllActiveObjs(k);

            assert IsInCAS(k_cas, dev_id2, o_id);

            assert (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {});
            if(CASGetAModes(k_cas, dev_id2, o_id) != {})
            {
                AllReqNonEmptyAModesMustContainROrW();
                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in CASGetAModes(k_cas, dev_id2, o_id);

                assert (exists tds_state2 :: tds_state2 in tds_states_set && R in DevAModesToObj(k, tds_state2, dev_id2, o_id)) ||
                       (exists tds_state2 :: tds_state2 in tds_states_set && W in DevAModesToObj(k, tds_state2, dev_id2, o_id));
                IfAModesContainROrWThenNotEmpty();
                assert exists tds_state2 :: tds_state2 in tds_states_set && DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};
            }
        }
    }
}