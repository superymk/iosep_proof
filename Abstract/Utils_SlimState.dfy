include "Syntax.dfy"
include "./utils/Collections.dfy"

//******** Fetcher of Helper Variables  ********//
// Return the subject IDs of all drivers
function method AllSubjsIDsInDrvs(k_subjects:Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in AllSubjsIDsInDrvs(k_subjects)
                <==> Drv_ID(s_id) in k_subjects.drvs
{
    Lemma_SameIDsIffSameInternalIDs();
    (set drv_id, s_id | drv_id in k_subjects.drvs && s_id == drv_id.sid
              :: s_id)
}

// Return the subject IDs of all devices
function method AllSubjsIDsInDevs(k_subjects:Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in AllSubjsIDsInDevs(k_subjects)
                <==> Dev_ID(s_id) in k_subjects.devs
{
    Lemma_SameIDsIffSameInternalIDs();
    (set dev_id, s_id | dev_id in k_subjects.devs && s_id == dev_id.sid
              :: s_id)
}

// Return the IDs of all subjects
function method AllSubjsIDs(k_subjects:Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in AllSubjsIDs(k_subjects)
                <==> (Drv_ID(s_id) in k_subjects.drvs) || (Dev_ID(s_id) in k_subjects.devs)
    ensures forall s_id :: s_id in AllSubjsIDs(k_subjects)
                <==> IsSubjID(k_subjects, s_id)
{
    AllSubjsIDsInDrvs(k_subjects) + AllSubjsIDsInDevs(k_subjects)
}

// Return the object IDs of all TDs
function method AllObjsIDsInTDs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDsInTDs(k_objects) 
                <==> (TD_ID(o_id) in k_objects.tds)
{
    Lemma_SameIDsIffSameInternalIDs();
    (set td_id, o_id | td_id in k_objects.tds && o_id == td_id.oid
              :: o_id)
}

// Return the object IDs of all FDs
function method AllObjsIDsInFDs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDsInFDs(k_objects) 
                <==> (FD_ID(o_id) in k_objects.fds)
{
    Lemma_SameIDsIffSameInternalIDs();
    (set fd_id, o_id | fd_id in k_objects.fds && o_id == fd_id.oid
              :: o_id)
}

// Return the object IDs of all DOs
function method AllObjsIDsInDOs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDsInDOs(k_objects) 
                <==> (DO_ID(o_id) in k_objects.dos)
{
    Lemma_SameIDsIffSameInternalIDs();
    (set do_id, o_id | do_id in k_objects.dos && o_id == do_id.oid
              :: o_id)
}

// Return the IDs of all objects
function method AllObjsIDs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDs(k_objects) 
                <==> 
                (TD_ID(o_id) in k_objects.tds) || (FD_ID(o_id) in k_objects.fds) ||
                (DO_ID(o_id) in k_objects.dos)
{
    AllObjsIDsInTDs(k_objects) + AllObjsIDsInFDs(k_objects) + AllObjsIDsInDOs(k_objects)
}




//******** Subjects/Objects ID  ********//
function method IsDrvID_SlimState(k_subjects:Subjects, drv_id:Drv_ID) : bool
{
    drv_id in k_subjects.drvs
}

function method IsDevID_SlimState(k_subjects:Subjects, dev_id:Dev_ID) : bool
{
    dev_id in k_subjects.devs
}

function method IDToDev_SlimState(k_subjects:Subjects, dev_id:Dev_ID) : Dev_State
    requires dev_id in k_subjects.devs
{
    k_subjects.devs[dev_id]
}

function method IsSubjID(k_subjects:Subjects, s_id:Subject_ID) : bool
    ensures IsSubjID(k_subjects, s_id) 
                <==> (Drv_ID(s_id) in k_subjects.drvs || Dev_ID(s_id) in k_subjects.devs)
{
    Drv_ID(s_id) in k_subjects.drvs || Dev_ID(s_id) in k_subjects.devs
}

function method IsObjID(
    k_objs_td_ids:set<TD_ID>, k_objs_fd_ids:set<FD_ID>, k_objs_do_ids:set<DO_ID>, o_id:Object_ID
) : bool
{
    TD_ID(o_id) in k_objs_td_ids || FD_ID(o_id) in k_objs_fd_ids || DO_ID(o_id) in k_objs_do_ids
}




//******** Objects Ownership ********//
// Does the subject (id == <s_id> own the object (id == <o_id>)
function method DoOwnObj_SlimState(k_subjects:Subjects, s_id:Subject_ID, o_id:Object_ID) : bool
    requires IsSubjID(k_subjects, s_id)
{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (TD_ID(o_id) in k_subjects.drvs[Drv_ID(s_id)].td_ids) ||
        (FD_ID(o_id) in k_subjects.drvs[Drv_ID(s_id)].fd_ids) ||
        (DO_ID(o_id) in k_subjects.drvs[Drv_ID(s_id)].do_ids)
    else
        (TD_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].td_ids) ||
        (FD_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].fd_ids) ||
        (DO_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].do_ids)
}

function method OwnedTDs_SlimState(k_subjects:Subjects, s_id:Subject_ID) : set<TD_ID>
    requires IsSubjID(k_subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures Drv_ID(s_id) in k_subjects.drvs
                ==> OwnedTDs_SlimState(k_subjects, s_id) == k_subjects.drvs[Drv_ID(s_id)].td_ids
    ensures Dev_ID(s_id) in k_subjects.devs
                ==> OwnedTDs_SlimState(k_subjects, s_id) == k_subjects.devs[Dev_ID(s_id)].td_ids

{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (k_subjects.drvs[Drv_ID(s_id)].td_ids)
    else
        (k_subjects.devs[Dev_ID(s_id)].td_ids)
}

function method OwnedFDs_SlimState(k_subjects:Subjects, s_id:Subject_ID) : set<FD_ID>
    requires IsSubjID(k_subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures Drv_ID(s_id) in k_subjects.drvs
                ==> OwnedFDs_SlimState(k_subjects, s_id) == k_subjects.drvs[Drv_ID(s_id)].fd_ids
    ensures Dev_ID(s_id) in k_subjects.devs
                ==> OwnedFDs_SlimState(k_subjects, s_id) == k_subjects.devs[Dev_ID(s_id)].fd_ids

{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (k_subjects.drvs[Drv_ID(s_id)].fd_ids)
    else
        (k_subjects.devs[Dev_ID(s_id)].fd_ids)
}

function method OwnedDOs_SlimState(k_subjects:Subjects, s_id:Subject_ID) : set<DO_ID>
    requires IsSubjID(k_subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures Drv_ID(s_id) in k_subjects.drvs
                ==> OwnedDOs_SlimState(k_subjects, s_id) == k_subjects.drvs[Drv_ID(s_id)].do_ids
    ensures Dev_ID(s_id) in k_subjects.devs
                ==> OwnedDOs_SlimState(k_subjects, s_id) == k_subjects.devs[Dev_ID(s_id)].do_ids
{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (k_subjects.drvs[Drv_ID(s_id)].do_ids)
    else
        (k_subjects.devs[Dev_ID(s_id)].do_ids)
}




//******** Partition ID  ********//
function method BuildMap_ObjIDsToPIDs(k_objects:Objects) : map<Object_ID, Partition_ID> 
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id
    
    ensures MapGetKeys(BuildMap_ObjIDsToPIDs(k_objects)) == AllObjsIDs(k_objects)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects)
                ==> (TD_ID(o_id) in k_objects.tds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.tds[TD_ID(o_id)].pid) &&
                    (FD_ID(o_id) in k_objects.fds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.fds[FD_ID(o_id)].pid) &&
                    (DO_ID(o_id) in k_objects.dos ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.dos[DO_ID(o_id)].pid)
                    
{
    MapConcat(
        MapConcat(BuildMap_ObjIDsToPIDs_ForTDs(k_objects), BuildMap_ObjIDsToPIDs_ForFDs(k_objects)),
        BuildMap_ObjIDsToPIDs_ForDOs(k_objects)
    )
}

function method ObjPID_SlimState(
    k_objs_pids:map<Object_ID, Partition_ID>, o_id:Object_ID
) : Partition_ID
    requires o_id in k_objs_pids
{
    k_objs_pids[o_id]
}

function method SubjPID_SlimState(k_subjects:Subjects, s_id:Subject_ID) : Partition_ID
    requires IsSubjID(k_subjects, s_id)
{
    if Drv_ID(s_id) in k_subjects.drvs then
        k_subjects.drvs[Drv_ID(s_id)].pid
    else
        k_subjects.devs[Dev_ID(s_id)].pid
}

function method SubjPID_DevID_SlimState(k_subjects:Subjects, dev_id:Dev_ID) : Partition_ID
    requires IsDevID_SlimState(k_subjects, dev_id)
{
    k_subjects.devs[dev_id].pid
}




//******** Active/Inactive Subjects/Objects  ********//
// Return all active subjects in the current state <k>
function method AllActiveSubjs_SlimState(k_subjects:Subjects) : set<Subject_ID>
{
    set s_id | s_id in AllSubjsIDs(k_subjects) && SubjPID_SlimState(k_subjects, s_id) != NULL :: s_id 
}

// Return all active objects in the current state <k>
function method AllActiveObjs_SlimState(k_objects:Objects) : set<Object_ID>
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id

    ensures forall td_id :: td_id in k_objects.tds && k_objects.tds[td_id].pid != NULL
                ==> td_id.oid in AllActiveObjs_SlimState(k_objects)
    ensures forall fd_id :: fd_id in k_objects.fds && k_objects.fds[fd_id].pid != NULL
                ==> fd_id.oid in AllActiveObjs_SlimState(k_objects)
    ensures forall do_id :: do_id in k_objects.dos && k_objects.dos[do_id].pid != NULL
                ==> do_id.oid in AllActiveObjs_SlimState(k_objects)
        // Property 1: All active objects are in the result
    ensures forall o_id :: o_id in AllActiveObjs_SlimState(k_objects)
                ==> (TD_ID(o_id) in k_objects.tds ==> k_objects.tds[TD_ID(o_id)].pid != NULL) &&
                    (FD_ID(o_id) in k_objects.fds ==> k_objects.fds[FD_ID(o_id)].pid != NULL) &&
                    (DO_ID(o_id) in k_objects.dos ==> k_objects.dos[DO_ID(o_id)].pid != NULL)
        // Property 2: All objects in the result are active
{
    Lemma_AllActiveObjs_SlimState_Property(k_objects);
    set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id 
}

function method AllActiveDrvs_SlimState(k_subjects:Subjects) : set<Drv_ID>
    ensures forall drv_id :: drv_id in AllActiveDrvs_SlimState(k_subjects) 
                ==> drv_id.sid in AllActiveSubjs_SlimState(k_subjects)
    ensures forall drv_id :: drv_id in AllActiveDrvs_SlimState(k_subjects) 
                ==> IsDrvID_SlimState(k_subjects, drv_id)
{
    set drv_id | drv_id in k_subjects.drvs && SubjPID_SlimState(k_subjects, drv_id.sid) != NULL :: drv_id 
}

function method AllActiveDevs_SlimState(k_subjects:Subjects) : set<Dev_ID>
    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k_subjects) 
                ==> dev_id.sid in AllActiveSubjs_SlimState(k_subjects)
    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k_subjects) 
                ==> IsDevID_SlimState(k_subjects, dev_id)
{
    set dev_id | dev_id in k_subjects.devs && SubjPID_SlimState(k_subjects, dev_id.sid) != NULL :: dev_id 
}

function method AllActiveTDs_SlimState(k_objects_tds:map<TD_ID, TD_State>) : set<TD_ID>
    ensures forall td_id :: td_id in AllActiveTDs_SlimState(k_objects_tds) 
                <==> td_id in k_objects_tds && k_objects_tds[td_id].pid != NULL
{
    set td_id | td_id in k_objects_tds && k_objects_tds[td_id].pid != NULL :: td_id 
}

function method AllActiveFDs_SlimState(k_objects_fds:map<FD_ID, FD_State>) : set<FD_ID>
    ensures forall fd_id :: fd_id in AllActiveFDs_SlimState(k_objects_fds) 
                <==> fd_id in k_objects_fds && k_objects_fds[fd_id].pid != NULL
{
    set fd_id | fd_id in k_objects_fds && k_objects_fds[fd_id].pid != NULL :: fd_id 
}

function method AllActiveDOs_SlimState(k_objects_dos:map<DO_ID, DO_State>) : set<DO_ID>
    ensures forall do_id :: do_id in AllActiveDOs_SlimState(k_objects_dos) 
                <==> do_id in k_objects_dos && k_objects_dos[do_id].pid != NULL
{
    set do_id | do_id in k_objects_dos && k_objects_dos[do_id].pid != NULL :: do_id 
}

function method ActiveTDsState_SlimState(k_objects_tds:map<TD_ID, TD_State>) : map<TD_ID, TD_Val>
    ensures MapGetKeys(ActiveTDsState_SlimState(k_objects_tds)) == AllActiveTDs_SlimState(k_objects_tds)
        // Property: The result includes active TDs only
    ensures forall td_id :: td_id in ActiveTDsState_SlimState(k_objects_tds)
                ==> ActiveTDsState_SlimState(k_objects_tds)[td_id] == k_objects_tds[td_id].val
        // Property: The values of active TDs are from <k_objects_tds>
{
    map td_id | td_id in AllActiveTDs_SlimState(k_objects_tds) 
              :: k_objects_tds[td_id].val
}




//******** Private Functions ********//
function method BuildMap_ObjIDsToPIDs_ForTDs(k_objects:Objects) : map<Object_ID, Partition_ID>
    ensures MapGetKeys(BuildMap_ObjIDsToPIDs_ForTDs(k_objects)) == AllObjsIDsInTDs(k_objects)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects) &&
                           TD_ID(o_id) in k_objects.tds
                ==> BuildMap_ObjIDsToPIDs_ForTDs(k_objects)[o_id] == k_objects.tds[TD_ID(o_id)].pid
{
    map o_id | o_id in AllObjsIDs(k_objects) &&
               TD_ID(o_id) in k_objects.tds
            :: k_objects.tds[TD_ID(o_id)].pid
}

function method BuildMap_ObjIDsToPIDs_ForFDs(k_objects:Objects) : map<Object_ID, Partition_ID>
    ensures MapGetKeys(BuildMap_ObjIDsToPIDs_ForFDs(k_objects)) == AllObjsIDsInFDs(k_objects)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects) &&
                           FD_ID(o_id) in k_objects.fds
                ==> BuildMap_ObjIDsToPIDs_ForFDs(k_objects)[o_id] == k_objects.fds[FD_ID(o_id)].pid
{
    map o_id | o_id in AllObjsIDs(k_objects) &&
               FD_ID(o_id) in k_objects.fds
            :: k_objects.fds[FD_ID(o_id)].pid
}

function method BuildMap_ObjIDsToPIDs_ForDOs(k_objects:Objects) : map<Object_ID, Partition_ID>
    ensures MapGetKeys(BuildMap_ObjIDsToPIDs_ForDOs(k_objects)) == AllObjsIDsInDOs(k_objects)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects) &&
                           DO_ID(o_id) in k_objects.dos
                ==> BuildMap_ObjIDsToPIDs_ForDOs(k_objects)[o_id] == k_objects.dos[DO_ID(o_id)].pid
{
    map o_id | o_id in AllObjsIDs(k_objects) &&
               DO_ID(o_id) in k_objects.dos
            :: k_objects.dos[DO_ID(o_id)].pid
}




//******** Utility Lemmas  ********//
// Lemma: TDs returned by AllActiveTDs_SlimState are also in 
// AllActiveObjs_SlimState(k_objects)
lemma Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k_objects:Objects)
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id

    ensures forall td_id :: td_id in AllActiveTDs_SlimState(k_objects.tds) 
                ==> td_id.oid in AllActiveObjs_SlimState(k_objects)
    ensures forall td_id :: td_id in AllActiveTDs_SlimState(k_objects.tds) 
                <==> td_id in k_objects.tds && td_id.oid in AllActiveObjs_SlimState(k_objects)
{
    assert forall td_id :: td_id in AllActiveTDs_SlimState(k_objects.tds) 
                <==> td_id in k_objects.tds && td_id.oid in AllActiveObjs_SlimState(k_objects);
}

lemma Lemma_SameSubjectsOwnSameObjectsInSuccessiveStates(k_subjects:Subjects, k'_subjects:Subjects)
    requires MapGetKeys<Drv_ID, Drv_State>(k'_subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k_subjects.drvs)
    requires MapGetKeys<Dev_ID, Dev_State>(k'_subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k_subjects.devs)
    requires forall drv_id :: drv_id in k_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k_subjects.drvs[drv_id].td_ids) &&
                    (k'_subjects.drvs[drv_id].fd_ids == k_subjects.drvs[drv_id].fd_ids) &&
                    (k'_subjects.drvs[drv_id].do_ids == k_subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].td_ids == k_subjects.devs[dev_id].td_ids) &&
                    (k'_subjects.devs[dev_id].fd_ids == k_subjects.devs[dev_id].fd_ids) &&
                    (k'_subjects.devs[dev_id].do_ids == k_subjects.devs[dev_id].do_ids)

    ensures forall s_id, o_id :: (Drv_ID(s_id) in k_subjects.drvs || Dev_ID(s_id) in k_subjects.devs) &&
                    DoOwnObj_SlimState(k_subjects, s_id, o_id)
                ==> DoOwnObj_SlimState(k'_subjects, s_id, o_id)
{
    // Dafny can automatically prove this lemma
}

// Drv_ID/Dev_ID/TD_ID/FD_ID/DO_ID are same, iff internal Subject_ID/Object_ID is same
lemma Lemma_SameIDsIffSameInternalIDs()
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




//******** Private Lemmas  ********//
lemma Lemma_AllActiveObjs_SlimState_Property(k_objects:Objects)
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id

    ensures forall td_id :: td_id in k_objects.tds && k_objects.tds[td_id].pid != NULL
                ==> td_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    ensures forall fd_id :: fd_id in k_objects.fds && k_objects.fds[fd_id].pid != NULL
                ==> fd_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    ensures forall do_id :: do_id in k_objects.dos && k_objects.dos[do_id].pid != NULL
                ==> do_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
{
    forall td_id | td_id in k_objects.tds && k_objects.tds[td_id].pid != NULL
        ensures td_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert td_id.oid in objs_pids;
        assert objs_pids[td_id.oid] == k_objects.tds[td_id].pid;
    }

    forall fd_id | fd_id in k_objects.fds && k_objects.fds[fd_id].pid != NULL
        ensures fd_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert fd_id.oid in objs_pids;
        assert objs_pids[fd_id.oid] == k_objects.fds[fd_id].pid;
    }

    forall do_id | do_id in k_objects.dos && k_objects.dos[do_id].pid != NULL
        ensures do_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert do_id.oid in objs_pids;
        assert objs_pids[do_id.oid] == k_objects.dos[do_id].pid;
    }
}