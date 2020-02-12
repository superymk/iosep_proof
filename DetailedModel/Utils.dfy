include "../Abstract/utils/Collections.dfy"
include "Syntax.dfy"


//******** State Interpretation ********//
function method DMStateToState(ws:DM_State) : State
    ensures DMStateToState(ws).subjects == ws.subjects
    ensures DMStateToState(ws).objects == ws.objects
    ensures DMStateToState(ws).pids == ws.pids
    ensures DMStateToState(ws).tds_to_all_states == ws.tds_to_all_states
{
    State(ws.subjects, ws.objects, ws.pids, ws.tds_to_all_states)
}




//******** Utility Functions for Properties ********//
function method DoTDsIncludeSecureNoTDWriteTransfersOnly(
    k_params:ReachableTDsKParams,
    tds_state:TDs_Vals, td_id:TD_ID
) : bool
    requires DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition_KParams_PreConditions(k_params)
        // Requirements required by functions in this function method
    requires TDsStateGetTDIDs(tds_state) == k_params.all_active_tds
        // Requirement: The TDs' state includes all active TDs 
    requires td_id in tds_state
        // Requirement: The TD (<td_id>) is active
{
    !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, tds_state, td_id) &&

    // No write transfers to TDs 
    (forall td_id2 :: td_id2 in tds_state[td_id].trans_params_tds
        ==> W !in tds_state[td_id].trans_params_tds[td_id2].amodes)
}




//******** Subjects' IDs ********//
predicate P_DMSubjectsHasUniqueIDs(ws_subjects:Subjects)
{
    (forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in ws_subjects.drvs) && (Dev_ID(dev_sid) in ws_subjects.devs)
         ==> (drv_sid != dev_sid))
}

// Return the IDs of all subjects of the WK state <ws_k>
function method DM_AllSubjsIDs(ws_subjects:Subjects) : set<Subject_ID>
    ensures DM_AllSubjsIDs(ws_subjects) == AllSubjsIDs(ws_subjects)
    ensures forall s_id :: s_id in DM_AllSubjsIDs(ws_subjects)
                <==> DM_IsSubjID(ws_subjects, s_id)
{
    AllSubjsIDs(ws_subjects)
}

function method DM_IsDrvID(ws_subjects:Subjects, drv_id:Drv_ID) : bool
{
    IsDrvID_SlimState(ws_subjects, drv_id)
}

function method DM_IsDevID(ws_subjects:Subjects, dev_id:Dev_ID) : bool
{
    IsDevID_SlimState(ws_subjects, dev_id)
}

function method DM_IsSubjID(ws_subjects:Subjects, s_id:Subject_ID) : bool
{
    IsSubjID(ws_subjects, s_id)
}

function method DM_AllDevIDs(ws_subjects:Subjects) : set<Dev_ID>
{
    MapGetKeys(ws_subjects.devs)
}





//******** Objects' IDs ********//
predicate P_DMObjectsHasUniqueIDs(ws_objects:Objects)
{
    (forall td_id, fd_id :: TD_ID(td_id) in ws_objects.tds && FD_ID(fd_id) in ws_objects.fds
        ==> td_id != fd_id) &&
    (forall td_id, do_id :: TD_ID(td_id) in ws_objects.tds && DO_ID(do_id) in ws_objects.dos
        ==> td_id != do_id) &&
    (forall fd_id, do_id :: FD_ID(fd_id) in ws_objects.fds && DO_ID(do_id) in ws_objects.dos
        ==> fd_id != do_id)
}

predicate P_ObjsInSubjsAreInSetOfAllObjs(ws_subjects:Subjects, ws_objects:Objects)
{
    (forall drv_id, td_id :: 
                drv_id in ws_subjects.drvs && td_id in ws_subjects.drvs[drv_id].td_ids
                ==> td_id in ws_objects.tds) &&
    (forall dev_id, td_id :: 
                dev_id in ws_subjects.devs && td_id in ws_subjects.devs[dev_id].td_ids
                ==> td_id in ws_objects.tds) &&
    (forall drv_id, fd_id :: 
                drv_id in ws_subjects.drvs && fd_id in ws_subjects.drvs[drv_id].fd_ids
                ==> fd_id in ws_objects.fds) &&
    (forall dev_id, fd_id :: 
                dev_id in ws_subjects.devs && fd_id in ws_subjects.devs[dev_id].fd_ids
                ==> fd_id in ws_objects.fds) &&
    (forall drv_id, do_id :: 
                drv_id in ws_subjects.drvs && do_id in ws_subjects.drvs[drv_id].do_ids
                ==> do_id in ws_objects.dos) &&
    (forall dev_id, do_id :: 
                dev_id in ws_subjects.devs && do_id in ws_subjects.devs[dev_id].do_ids
                ==> do_id in ws_objects.dos) &&

    (true)
}

function method DM_TDIDsToObjIDs(td_ids:set<TD_ID>) : set<Object_ID>
    ensures forall o_id :: TD_ID(o_id) in td_ids
                <==> o_id in DM_TDIDsToObjIDs(td_ids)
{
    TDIDsToObjIDs(td_ids)
}

function method DM_FDIDsToObjIDs(fd_ids:set<FD_ID>) : set<Object_ID>
    ensures forall o_id :: FD_ID(o_id) in fd_ids
                <==> o_id in DM_FDIDsToObjIDs(fd_ids)
{
    FDIDsToObjIDs(fd_ids)
}

function method DM_DOIDsToObjIDs(do_ids:set<DO_ID>) : set<Object_ID>
    ensures forall o_id :: DO_ID(o_id) in do_ids
                <==> o_id in DM_DOIDsToObjIDs(do_ids)
{
    DOIDsToObjIDs(do_ids)
}

// Get internal object IDs of a set of objects in WK
function method DM_AllObjsIDs(objects:Objects) : set<Object_ID>
    ensures DM_AllObjsIDs(objects) == AllObjsIDs(objects)
{
    AllObjsIDs(objects)
}

function method DM_AllTDIDs(ws_objects:Objects) : set<TD_ID>
{
    MapGetKeys(ws_objects.tds)
}

function method DM_AllFDIDs(ws_objects:Objects) : set<FD_ID>
{
    MapGetKeys(ws_objects.fds)
}

function method DM_AllDOIDs(ws_objects:Objects) : set<DO_ID>
{
    MapGetKeys(ws_objects.dos)
}




//******** Objects Ownership ********//
// Does the subject (id == <s_id> own the object (id == <o_id>)
function method DM_DoOwnObj(ws_subjects:Subjects, s_id:Subject_ID, o_id:Object_ID) : bool
    requires DM_IsSubjID(ws_subjects, s_id)
{
    DoOwnObj_SlimState(ws_subjects, s_id, o_id)
}

function method DM_OwnedTDs(ws_subjects:Subjects, s_id:Subject_ID) : set<TD_ID>
    requires DM_IsSubjID(ws_subjects, s_id)
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    ensures DM_OwnedTDs(ws_subjects, s_id) == OwnedTDs_SlimState(ws_subjects, s_id)
{
    OwnedTDs_SlimState(ws_subjects, s_id)
}

function method DM_OwnedFDs(ws_subjects:Subjects, s_id:Subject_ID) : set<FD_ID>
    requires DM_IsSubjID(ws_subjects, s_id)
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    ensures DM_OwnedFDs(ws_subjects, s_id) == OwnedFDs_SlimState(ws_subjects, s_id)
{
    OwnedFDs_SlimState(ws_subjects, s_id)
}

function method DM_OwnedDOs(ws_subjects:Subjects, s_id:Subject_ID) : set<DO_ID>
    requires DM_IsSubjID(ws_subjects, s_id)
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    ensures DM_OwnedDOs(ws_subjects, s_id) == OwnedDOs_SlimState(ws_subjects, s_id)
{
    OwnedDOs_SlimState(ws_subjects, s_id)
}

function method DM_OwnedObjs(ws_subjects:Subjects, s_id:Subject_ID) : set<Object_ID>
    requires DM_IsSubjID(ws_subjects, s_id)
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    ensures forall o_id :: o_id in DM_OwnedObjs(ws_subjects, s_id)
                ==> TD_ID(o_id) in DM_OwnedTDs(ws_subjects, s_id) || 
                    FD_ID(o_id) in DM_OwnedFDs(ws_subjects, s_id) || 
                    DO_ID(o_id) in DM_OwnedDOs(ws_subjects, s_id)
    ensures forall td_id :: td_id in DM_OwnedTDs(ws_subjects, s_id)
                ==> td_id.oid in DM_OwnedObjs(ws_subjects, s_id)
    ensures forall fd_id :: fd_id in DM_OwnedFDs(ws_subjects, s_id)
                ==> fd_id.oid in DM_OwnedObjs(ws_subjects, s_id)
    ensures forall do_id :: do_id in DM_OwnedDOs(ws_subjects, s_id)
                ==> do_id.oid in DM_OwnedObjs(ws_subjects, s_id)
{
    if(Drv_ID(s_id) in ws_subjects.drvs) then
        var result := TDIDsToObjIDs(ws_subjects.drvs[Drv_ID(s_id)].td_ids) +
                    FDIDsToObjIDs(ws_subjects.drvs[Drv_ID(s_id)].fd_ids) +
                    DOIDsToObjIDs(ws_subjects.drvs[Drv_ID(s_id)].do_ids);
        assert forall td_id :: td_id in DM_OwnedTDs(ws_subjects, s_id)
                    ==> td_id.oid in result;
        assert forall fd_id :: fd_id in DM_OwnedFDs(ws_subjects, s_id)
                    ==> fd_id.oid in result;
        assert forall do_id :: do_id in DM_OwnedDOs(ws_subjects, s_id)
                    ==> do_id.oid in result;

        result
    else
        var result := TDIDsToObjIDs(ws_subjects.devs[Dev_ID(s_id)].td_ids) +
                    FDIDsToObjIDs(ws_subjects.devs[Dev_ID(s_id)].fd_ids) +
                    DOIDsToObjIDs(ws_subjects.devs[Dev_ID(s_id)].do_ids);
        assert forall td_id :: td_id in DM_OwnedTDs(ws_subjects, s_id)
                    ==> td_id.oid in result;
        assert forall fd_id :: fd_id in DM_OwnedFDs(ws_subjects, s_id)
                    ==> fd_id.oid in result;
        assert forall do_id :: do_id in DM_OwnedDOs(ws_subjects, s_id)
                    ==> do_id.oid in result;

        result
}




//******** Subjects/Objects PID  ********//
function method DM_BuildMap_ObjIDsToPIDs(ws_objects:Objects) : map<Object_ID, Partition_ID> 
    requires P_DMObjectsHasUniqueIDs(ws_objects)
    
    ensures MapGetKeys(DM_BuildMap_ObjIDsToPIDs(ws_objects)) == DM_AllObjsIDs(ws_objects)
    ensures DM_BuildMap_ObjIDsToPIDs(ws_objects) == BuildMap_ObjIDsToPIDs(ws_objects)
{
    BuildMap_ObjIDsToPIDs(ws_objects)
}

// Return the ID of the partition that the object (id == <o_id>) 
// belongs to. 
// Return NULL if the object does not belong to any partition 
function method DM_ObjPID(ws_objects:Objects, o_id:Object_ID) : Partition_ID
    requires P_DMObjectsHasUniqueIDs(ws_objects)

    requires o_id in DM_AllObjsIDs(ws_objects)

    ensures (TD_ID(o_id) in ws_objects.tds ==> BuildMap_ObjIDsToPIDs(ws_objects)[o_id] == ws_objects.tds[TD_ID(o_id)].pid) &&
            (FD_ID(o_id) in ws_objects.fds ==> BuildMap_ObjIDsToPIDs(ws_objects)[o_id] == ws_objects.fds[FD_ID(o_id)].pid) &&
            (DO_ID(o_id) in ws_objects.dos ==> BuildMap_ObjIDsToPIDs(ws_objects)[o_id] == ws_objects.dos[DO_ID(o_id)].pid)
{
    ObjPID_KObjects(ws_objects, o_id)
}

function method DM_SubjPID(ws_subjects:Subjects, s_id:Subject_ID) : Partition_ID
    requires DM_IsSubjID(ws_subjects, s_id)
{
    SubjPID_SlimState(ws_subjects, s_id)
}

function method DM_SubjPID_DevID(ws_subjects:Subjects, dev_id:Dev_ID) : Partition_ID
    requires DM_IsDevID(ws_subjects, dev_id)
{
    SubjPID_DevID_SlimState(ws_subjects, dev_id)
}

function method DM_AllActiveDevs(ws_subjects:Subjects) : set<Dev_ID>
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)
    ensures forall dev_id :: dev_id in DM_AllActiveDevs(ws_subjects) 
                ==> DM_IsDevID(ws_subjects, dev_id)
    ensures forall dev_id :: dev_id in DM_AllActiveDevs(ws_subjects) 
                ==> DM_SubjPID_DevID(ws_subjects, dev_id) != NULL
{
    AllActiveDevs_SlimState(ws_subjects)
}

function method DM_AllActiveSubjs(ws_subjects:Subjects) : set<Subject_ID>
{
    AllActiveSubjs_SlimState(ws_subjects)
}

function method DM_AllActiveTDs(ws_objects:Objects) : set<TD_ID>
    requires P_DMObjectsHasUniqueIDs(ws_objects)
{
    AllActiveTDs_SlimState(ws_objects.tds)
}

function method TDStateToTDVal(tds:map<TD_ID, TD_State>) : map<TD_ID, TD_Val>
    ensures MapGetKeys(tds) == MapGetKeys(TDStateToTDVal(tds))
    ensures forall id :: id in tds
                ==> tds[id].val == TDStateToTDVal(tds)[id]
{
    map td_id | td_id in tds :: tds[td_id].val
}




//******** Active Subjects, Devices and TDs In Partitions ********//
function method DM_SubjsInRed(ws:DM_State) : set<Subject_ID>
    ensures forall s_id :: s_id in DM_SubjsInRed(ws)
                <==> (s_id in DM_AllActiveSubjs(ws.subjects) &&
                      DM_SubjPID(ws.subjects, s_id) == ws.red_pid)
{
    set s_id | s_id in DM_AllActiveSubjs(ws.subjects) &&
               DM_SubjPID(ws.subjects, s_id) == ws.red_pid
            :: s_id
}

function method DM_SubjsInGreen(ws:DM_State) : set<Subject_ID>
    ensures forall s_id :: s_id in DM_SubjsInGreen(ws)
                <==> (s_id in DM_AllActiveSubjs(ws.subjects) &&
                      DM_SubjPID(ws.subjects, s_id) != NULL &&
                      DM_SubjPID(ws.subjects, s_id) != ws.red_pid)
{
    set s_id | s_id in DM_AllActiveSubjs(ws.subjects) &&
               DM_SubjPID(ws.subjects, s_id) != NULL &&
               DM_SubjPID(ws.subjects, s_id) != ws.red_pid
            :: s_id
}

function method DM_DevsInRed(ws:DM_State) : set<Dev_ID>
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)

    ensures forall dev_id :: dev_id in DM_DevsInRed(ws)
                <==> (dev_id in DM_AllActiveDevs(ws.subjects) &&
                      DM_SubjPID_DevID(ws.subjects, dev_id) == ws.red_pid)
    ensures forall dev_id :: dev_id in DM_DevsInRed(ws)
                <==> DM_IsDevID(ws.subjects, dev_id) && dev_id.sid in DM_SubjsInRed(ws)
        // Property: DM_DevsInRed(ws) contains all active devices in 
        // DM_SubjsInRed(ws)
{
    assert forall dev_id :: dev_id in DM_AllDevIDs(ws.subjects)
            ==> dev_id.sid in DM_AllSubjsIDs(ws.subjects);
    Lemma_DM_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID_AllDevIDs(ws.subjects);
    set dev_id | dev_id in DM_AllActiveDevs(ws.subjects) &&
                 DM_SubjPID_DevID(ws.subjects, dev_id) == ws.red_pid
               :: dev_id
}

function method DM_DevsInGreen(ws:DM_State) : set<Dev_ID>
    requires P_DMSubjectsHasUniqueIDs(ws.subjects)

    ensures forall dev_id :: dev_id in DM_DevsInGreen(ws)
                <==> (dev_id in DM_AllActiveDevs(ws.subjects) &&
                      DM_SubjPID_DevID(ws.subjects, dev_id) != NULL &&
                      DM_SubjPID_DevID(ws.subjects, dev_id) != ws.red_pid)
    ensures forall dev_id :: dev_id in DM_DevsInGreen(ws)
                <==> DM_IsDevID(ws.subjects, dev_id) && dev_id.sid in DM_SubjsInGreen(ws)
        // Property: DM_DevsInGreen(ws) contains all active devices in 
        // DM_SubjsInGreen(ws)
{
    assert forall dev_id :: dev_id in DM_AllDevIDs(ws.subjects)
            ==> dev_id.sid in DM_AllSubjsIDs(ws.subjects);
    Lemma_DM_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID_AllDevIDs(ws.subjects);
    set dev_id | dev_id in DM_AllActiveDevs(ws.subjects) &&
                 DM_SubjPID_DevID(ws.subjects, dev_id) != NULL &&
                 DM_SubjPID_DevID(ws.subjects, dev_id) != ws.red_pid
               :: dev_id
}

function method DM_TDIDsInRed(ws:DM_State) : set<TD_ID>
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    ensures forall td_id :: td_id in DM_TDIDsInRed(ws)
                <==> (td_id in DM_AllTDIDs(ws.objects) &&
                      DM_ObjPID(ws.objects, td_id.oid) == ws.red_pid)
{
    set td_id | td_id in DM_AllTDIDs(ws.objects) &&
                DM_ObjPID(ws.objects, td_id.oid) == ws.red_pid
            :: td_id
}

function method DM_TDIDsInGreen(ws:DM_State) : set<TD_ID>
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    ensures forall td_id :: td_id in DM_TDIDsInGreen(ws)
                <==> (td_id in DM_AllTDIDs(ws.objects) &&
                      DM_ObjPID(ws.objects, td_id.oid) != NULL &&
                      DM_ObjPID(ws.objects, td_id.oid) != ws.red_pid)
{
    set td_id | td_id in DM_AllTDIDs(ws.objects) &&
               DM_ObjPID(ws.objects, td_id.oid) != NULL &&
               DM_ObjPID(ws.objects, td_id.oid) != ws.red_pid
            :: td_id
}

function method DM_FDIDsInGreen(ws:DM_State) : set<FD_ID>
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    ensures forall fd_id :: fd_id in DM_FDIDsInGreen(ws)
                <==> (fd_id in DM_AllFDIDs(ws.objects) &&
                      DM_ObjPID(ws.objects, fd_id.oid) != NULL &&
                      DM_ObjPID(ws.objects, fd_id.oid) != ws.red_pid)
{
    set fd_id | fd_id in DM_AllFDIDs(ws.objects) &&
               DM_ObjPID(ws.objects, fd_id.oid) != NULL &&
               DM_ObjPID(ws.objects, fd_id.oid) != ws.red_pid
            :: fd_id
}

function method DM_DOIDsInGreen(ws:DM_State) : set<DO_ID>
    requires P_DMObjectsHasUniqueIDs(ws.objects)

    ensures forall do_id :: do_id in DM_DOIDsInGreen(ws)
                <==> (do_id in DM_AllDOIDs(ws.objects) &&
                      DM_ObjPID(ws.objects, do_id.oid) != NULL &&
                      DM_ObjPID(ws.objects, do_id.oid) != ws.red_pid)
{
    set do_id | do_id in DM_AllDOIDs(ws.objects) &&
               DM_ObjPID(ws.objects, do_id.oid) != NULL &&
               DM_ObjPID(ws.objects, do_id.oid) != ws.red_pid
            :: do_id
}




//******** Check Value of Objects and Subjects ********//
function method DM_IsTDClearVal(ws_objects:Objects, td_id:TD_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects)
    
    requires td_id in DM_AllTDIDs(ws_objects)
{
    IsTDClearVal(ws_objects.tds, td_id)
}

function method DM_IsFDClearVal(ws_objects:Objects, fd_id:FD_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects)
    
    requires fd_id in DM_AllFDIDs(ws_objects)
{
    IsFDClearVal(ws_objects.fds, fd_id)
}

function method DM_IsDOClearVal(ws_objects:Objects, do_id:DO_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects)
    
    requires do_id in DM_AllDOIDs(ws_objects)
{
    IsDOClearVal(ws_objects.dos, do_id)
}

function method DM_IsSameTD(ws_objects':Objects, ws_objects:Objects, td_id:TD_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects')
    
    requires MapGetKeys(ws_objects'.tds) == MapGetKeys(ws_objects.tds)
    requires td_id in DM_AllTDIDs(ws_objects)

    ensures DM_IsSameTD(ws_objects', ws_objects, td_id)
                ==> ws_objects'.tds[td_id] == ws_objects.tds[td_id]
{
    ws_objects'.tds[td_id] == ws_objects.tds[td_id]
}

function method DM_IsSameFD(ws_objects':Objects, ws_objects:Objects, fd_id:FD_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects')
    
    requires MapGetKeys(ws_objects'.fds) == MapGetKeys(ws_objects.fds)
    requires fd_id in DM_AllFDIDs(ws_objects)

    ensures DM_IsSameFD(ws_objects', ws_objects, fd_id)
                ==> ws_objects'.fds[fd_id] == ws_objects.fds[fd_id]
{
    ws_objects'.fds[fd_id] == ws_objects.fds[fd_id]
}

function method DM_IsSameDO(ws_objects':Objects, ws_objects:Objects, do_id:DO_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects')
    
    requires MapGetKeys(ws_objects'.dos) == MapGetKeys(ws_objects.dos)
    requires do_id in DM_AllDOIDs(ws_objects)

    ensures DM_IsSameDO(ws_objects', ws_objects, do_id)
                ==> ws_objects'.dos[do_id] == ws_objects.dos[do_id]
{
    ws_objects'.dos[do_id] == ws_objects.dos[do_id]
}

function method DM_IsSameTDVal(ws_objects':Objects, ws_objects:Objects, td_id:TD_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects')
    
    requires MapGetKeys(ws_objects'.tds) == MapGetKeys(ws_objects.tds)
    requires td_id in DM_AllTDIDs(ws_objects)

    ensures DM_IsSameTDVal(ws_objects', ws_objects, td_id)
                ==> ws_objects'.tds[td_id].val == ws_objects.tds[td_id].val
{
    ws_objects'.tds[td_id].val == ws_objects.tds[td_id].val
}

function method DM_IsSameFDVal(ws_objects':Objects, ws_objects:Objects, fd_id:FD_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects')
    
    requires MapGetKeys(ws_objects'.fds) == MapGetKeys(ws_objects.fds)
    requires fd_id in DM_AllFDIDs(ws_objects)

    ensures DM_IsSameFDVal(ws_objects', ws_objects, fd_id)
                ==> ws_objects'.fds[fd_id].val == ws_objects.fds[fd_id].val
{
    ws_objects'.fds[fd_id].val == ws_objects.fds[fd_id].val
}

function method DM_IsSameDOVal(ws_objects':Objects, ws_objects:Objects, do_id:DO_ID) : bool
    requires P_DMObjectsHasUniqueIDs(ws_objects')
    
    requires MapGetKeys(ws_objects'.dos) == MapGetKeys(ws_objects.dos)
    requires do_id in DM_AllDOIDs(ws_objects)

    ensures DM_IsSameDOVal(ws_objects', ws_objects, do_id)
                ==> ws_objects'.dos[do_id].val == ws_objects.dos[do_id].val
{
    ws_objects'.dos[do_id].val == ws_objects.dos[do_id].val
}

function method DM_IsSameSubj(ws_subjects':Subjects, ws_subjects:Subjects, s_id:Subject_ID) : bool
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    requires MapGetKeys(ws_subjects'.drvs) == MapGetKeys(ws_subjects.drvs) &&
            MapGetKeys(ws_subjects'.devs) == MapGetKeys(ws_subjects.devs)

    requires s_id in DM_AllSubjsIDs(ws_subjects)

    ensures DM_IsSameSubj(ws_subjects', ws_subjects, s_id) 
                ==> (Drv_ID(s_id) in ws_subjects.drvs ==> ws_subjects'.drvs[Drv_ID(s_id)] == ws_subjects.drvs[Drv_ID(s_id)]) &&
                    (Dev_ID(s_id) in ws_subjects.devs ==> ws_subjects'.devs[Dev_ID(s_id)] == ws_subjects.devs[Dev_ID(s_id)])
{
    if(Drv_ID(s_id) in ws_subjects.drvs) then
        ws_subjects'.drvs[Drv_ID(s_id)] == ws_subjects.drvs[Drv_ID(s_id)]
    else
        assert Dev_ID(s_id) in ws_subjects.devs;
        ws_subjects'.devs[Dev_ID(s_id)] == ws_subjects.devs[Dev_ID(s_id)]
}




//******** Utility Lemmas ********//
lemma Lemma_DM_SameIDsIffSameInternalIDs()
    ensures forall drv_id1:Drv_ID, drv_id2:Drv_ID :: drv_id1 == drv_id2
               <==> drv_id1.sid == drv_id2.sid
    ensures forall dev_id1:Dev_ID, dev_id2:Dev_ID :: dev_id1 == dev_id2
               <==> dev_id1.sid == dev_id2.sid

    ensures forall td_id1:TD_ID, td_id2:TD_ID :: td_id1 == td_id2
               <==> td_id1.oid == td_id2.oid
    ensures forall fd_id1:FD_ID, fd_id2:FD_ID :: fd_id1 == fd_id2
               <==> fd_id1.oid == fd_id2.oid
    ensures forall do_id1:DO_ID, do_id2:DO_ID :: do_id1 == do_id2
               <==> do_id1.oid == do_id2.oid
{
    assert forall drv_id1:Drv_ID, drv_id2:Drv_ID :: drv_id1 == drv_id2
               <==> drv_id1.sid == drv_id2.sid;
    assert forall dev_id1:Dev_ID, dev_id2:Dev_ID :: dev_id1 == dev_id2
               <==> dev_id1.sid == dev_id2.sid;

    assert forall td_id1:TD_ID, td_id2:TD_ID :: td_id1 == td_id2
               <==> td_id1.oid == td_id2.oid;
    assert forall fd_id1:FD_ID, fd_id2:FD_ID :: fd_id1 == fd_id2
               <==> fd_id1.oid == fd_id2.oid;
    assert forall do_id1:DO_ID, do_id2:DO_ID :: do_id1 == do_id2
               <==> do_id1.oid == do_id2.oid;
}

// Lemma: DM_SubjPID_DevID of a device <dev_id> returns the same PID as
// DM_SubjPID of the s_id of the <dev_id>
lemma Lemma_DM_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(ws_subjects:Subjects, dev_id:Dev_ID)
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    requires DM_IsDevID(ws_subjects, dev_id)

    ensures DM_SubjPID_DevID(ws_subjects, dev_id) == DM_SubjPID(ws_subjects, dev_id.sid)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DM_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID_AllDevIDs(ws_subjects:Subjects)
    requires P_DMSubjectsHasUniqueIDs(ws_subjects)

    ensures forall dev_id :: dev_id in DM_AllDevIDs(ws_subjects)
                ==> DM_SubjPID_DevID(ws_subjects, dev_id) == DM_SubjPID(ws_subjects, dev_id.sid)
{
    forall dev_id | dev_id in DM_AllDevIDs(ws_subjects)
        ensures DM_SubjPID_DevID(ws_subjects, dev_id) == DM_SubjPID(ws_subjects, dev_id.sid)
    {
        Lemma_DM_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(ws_subjects, dev_id);
    }
}

lemma Lemma_DM_AllObjsIDs_Property()
    ensures forall objs1:Objects, objs2:Objects ::
            (MapGetKeys(objs1.tds) == MapGetKeys(objs2.tds) &&
             MapGetKeys(objs1.fds) == MapGetKeys(objs2.fds) &&
             MapGetKeys(objs1.dos) == MapGetKeys(objs2.dos))
        ==> DM_AllObjsIDs(objs1) == DM_AllObjsIDs(objs2)
{
    Lemma_DM_SameIDsIffSameInternalIDs();
    // Dafny can automatically prove this lemma
}




//******** Copy Values ********//
function method DM_DrvDevRead_ReplaceSrcTDWithVal(
    ws:DM_State, tds_dst_src:map<TD_ID, TD_ID>
) : (td_id_val_map:map<TD_ID, TD_Val>)
    requires forall td_id :: td_id in tds_dst_src
                ==> td_id in ws.objects.tds && tds_dst_src[td_id] in ws.objects.tds

    ensures MapGetKeys(td_id_val_map) == MapGetKeys(tds_dst_src)
    ensures forall td_id :: td_id in td_id_val_map
                ==> td_id_val_map[td_id] == ws.objects.tds[tds_dst_src[td_id]].val

    ensures DM_DrvDevRead_ReplaceSrcTDWithVal(ws, tds_dst_src) == DrvDevRead_ReplaceSrcTDWithVal(DMStateToState(ws), tds_dst_src)
{
    map td_id | td_id in tds_dst_src :: ws.objects.tds[tds_dst_src[td_id]].val
}

function method DM_DrvDevRead_ReplaceSrcFDWithVal(
    ws:DM_State, fds_dst_src:map<FD_ID, FD_ID>
) : (fd_id_val_map:map<FD_ID, FD_Val>)
    requires forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in ws.objects.fds && fds_dst_src[fd_id] in ws.objects.fds

    ensures MapGetKeys(fd_id_val_map) == MapGetKeys(fds_dst_src)
    ensures forall fd_id :: fd_id in fd_id_val_map
                ==> fd_id_val_map[fd_id] == ws.objects.fds[fds_dst_src[fd_id]].val

    ensures DM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src) == DrvDevRead_ReplaceSrcFDWithVal(DMStateToState(ws), fds_dst_src)
{
    map fd_id | fd_id in fds_dst_src :: ws.objects.fds[fds_dst_src[fd_id]].val
}

function method DM_DrvDevRead_ReplaceSrcDOWithVal(
    ws:DM_State, dos_dst_src:map<DO_ID, DO_ID>
) : (do_id_val_map:map<DO_ID, DO_Val>)
    requires forall do_id :: do_id in dos_dst_src
                ==> do_id in ws.objects.dos && dos_dst_src[do_id] in ws.objects.dos

    ensures MapGetKeys(do_id_val_map) == MapGetKeys(dos_dst_src)
    ensures forall do_id :: do_id in do_id_val_map
                ==> do_id_val_map[do_id] == ws.objects.dos[dos_dst_src[do_id]].val

    ensures DM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src) == DrvDevRead_ReplaceSrcDOWithVal(DMStateToState(ws), dos_dst_src)
{
    map do_id | do_id in dos_dst_src :: ws.objects.dos[dos_dst_src[do_id]].val
}