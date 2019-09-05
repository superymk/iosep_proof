include "Syntax.dfy"
include "./utils/Collections.dfy"
include "Utils_SlimState.dfy"

//******** Subjects/Objects ID  ********//
// Convert the set of Drv_ID to Subject_ID
function method DrvIDsToSubjIDs(drv_ids:set<Drv_ID>) : set<Subject_ID>
    ensures forall subj_id :: Drv_ID(subj_id) in drv_ids
                <==> subj_id in DrvIDsToSubjIDs(drv_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set drv_id, id | drv_id in drv_ids && drv_id.sid == id :: id
}

// Convert the set of Dev_ID to Subject_ID
function method DevIDsToSubjIDs(dev_ids:set<Dev_ID>) : set<Subject_ID>
    ensures forall subj_id :: Dev_ID(subj_id) in dev_ids
                <==> subj_id in DevIDsToSubjIDs(dev_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set dev_id, id | dev_id in dev_ids && dev_id.sid == id :: id
}

// Convert the set of TD_ID to Object_ID
function method TDIDsToObjIDs(td_ids:set<TD_ID>) : set<Object_ID>
    ensures forall id :: TD_ID(id) in td_ids
                <==> id in TDIDsToObjIDs(td_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set td_id, id | td_id in td_ids && td_id.oid == id :: id
}

// Convert the set of FD_ID to Object_ID
function method FDIDsToObjIDs(fd_ids:set<FD_ID>) : set<Object_ID>
    ensures forall id :: FD_ID(id) in fd_ids
                <==> id in FDIDsToObjIDs(fd_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set fd_id, id | fd_id in fd_ids && fd_id.oid == id :: id
}

// Convert the set of DO_ID to Object_ID
function method DOIDsToObjIDs(do_ids:set<DO_ID>) : set<Object_ID>
    ensures forall id :: DO_ID(id) in do_ids
                <==> id in DOIDsToObjIDs(do_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set do_id, id | do_id in do_ids && do_id.oid == id :: id
}

function method IsDevID(k:State, dev_id:Dev_ID) : bool
    ensures IsDevID(k, dev_id) == IsDevID_SlimState(k.subjects, dev_id)
{
    IsDevID_SlimState(k.subjects, dev_id)
}

function method IsDrvID(k:State, drv_id:Drv_ID) : bool
{
    drv_id in k.subjects.drvs
}

// Is the object (id == <o_id>) is a TD?
function method IsTD(k:State, o_id:Object_ID) : bool
{
    TD_ID(o_id) in k.objects.tds
}

// Get the TD state mapped to the <td_id>
function method IDToTD(tds:map<TD_ID, TD_State>, td_id:TD_ID) : TD_State
    requires td_id in tds
{
    tds[td_id]
}

// Is the object (id == <o_id>) is a FD?
function method IsFD(k:State, o_id:Object_ID) : bool
{
    FD_ID(o_id) in k.objects.fds
}

// Get the FD state mapped to the <fd_id>
function method IDToFD(k:State, fd_id:FD_ID) : FD_State
    requires fd_id in k.objects.fds
{
    k.objects.fds[fd_id]
}

// Is the object (id == <o_id>) is a DO?
function method IsDO(k:State, o_id:Object_ID) : bool
{
    DO_ID(o_id) in k.objects.dos
}

// Get the DO state mapped to the <do_id>
function method IDToDO(k:State, do_id:DO_ID) : DO_State
    requires do_id in k.objects.dos
{
    k.objects.dos[do_id]
}

// Get the driver state mapped to the <drv_id>
function method IDToDrv(k:State, drv_id:Drv_ID) : Drv_State
    requires drv_id in k.subjects.drvs
{
    k.subjects.drvs[drv_id]
}

// Get the device state mapped to the <dev_id>
function method IDToDev(k:State, dev_id:Dev_ID) : Dev_State
    requires dev_id in k.subjects.devs
    ensures IDToDev(k, dev_id) == IDToDev_SlimState(k.subjects, dev_id)
{
    IDToDev_SlimState(k.subjects, dev_id)
}

// Return if the TD (<td_id>) is referenced in the <td_state>
function method DoRefTD(td_state:TD_Val, td_id:TD_ID) : bool
    ensures DoRefTD(td_state, td_id) == true
                <==> td_id in td_state.trans_params_tds
{
    td_id in td_state.trans_params_tds
}




//******** Objects Ownership ********//
// Does the subject (id == <s_id> own the object (id == <o_id>)
function method DoOwnObj(k:State, s_id:Subject_ID, o_id:Object_ID) : bool
    requires IsSubjID(k.subjects, s_id)
    ensures DoOwnObj(k, s_id, o_id) == DoOwnObj_SlimState(k.subjects, s_id, o_id)
{
    DoOwnObj_SlimState(k.subjects, s_id, o_id)
}

predicate P_ObjsInSubjsAreAlsoInState(k:State)
{
    (forall drv_id :: drv_id in k.subjects.drvs
                ==> (forall td_id :: td_id in k.subjects.drvs[drv_id].td_ids
                        ==> td_id.oid in AllObjsIDs(k.objects)) &&
                    (forall fd_id :: fd_id in k.subjects.drvs[drv_id].fd_ids
                        ==> fd_id.oid in AllObjsIDs(k.objects)) &&
                    (forall do_id :: do_id in k.subjects.drvs[drv_id].do_ids
                        ==> do_id.oid in AllObjsIDs(k.objects))) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.subjects.devs[dev_id].td_ids
                        ==> td_id.oid in AllObjsIDs(k.objects)) &&
                    (forall fd_id :: fd_id in k.subjects.devs[dev_id].fd_ids
                        ==> fd_id.oid in AllObjsIDs(k.objects)) &&
                    (forall do_id :: do_id in k.subjects.devs[dev_id].do_ids
                        ==> do_id.oid in AllObjsIDs(k.objects))) &&

    (true)
}

// Return the IDs of all objects owned by the subject (id == <s_id>)
function method OwnObjIDs(k:State, s_id:Subject_ID) : set<Object_ID>
    requires P_ObjsInSubjsAreAlsoInState(k)
    requires IsSubjID(k.subjects, s_id) 
    ensures OwnObjIDs(k, s_id) <= AllObjsIDs(k.objects)
{
    if(Drv_ID(s_id) in k.subjects.drvs) then
        TDIDsToObjIDs(k.subjects.drvs[Drv_ID(s_id)].td_ids) +
        FDIDsToObjIDs(k.subjects.drvs[Drv_ID(s_id)].fd_ids) +
        DOIDsToObjIDs(k.subjects.drvs[Drv_ID(s_id)].do_ids)
    else
        TDIDsToObjIDs(k.subjects.devs[Dev_ID(s_id)].td_ids) +
        FDIDsToObjIDs(k.subjects.devs[Dev_ID(s_id)].fd_ids) +
        DOIDsToObjIDs(k.subjects.devs[Dev_ID(s_id)].do_ids)
}

function method OwnedTDs(k:State, s_id:Subject_ID) : set<TD_ID>
    requires IsSubjID(k.subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)

    ensures OwnedTDs(k, s_id) == OwnedTDs_SlimState(k.subjects, s_id)
{
    OwnedTDs_SlimState(k.subjects, s_id)
}

function method OwnedFDs(k:State, s_id:Subject_ID) : set<FD_ID>
    requires IsSubjID(k.subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures OwnedFDs(k, s_id) == OwnedFDs_SlimState(k.subjects, s_id)
{
    OwnedFDs_SlimState(k.subjects, s_id)
}

function method OwnedDOs(k:State, s_id:Subject_ID) : set<DO_ID>
    requires IsSubjID(k.subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures OwnedDOs(k, s_id) == OwnedDOs_SlimState(k.subjects, s_id)
{
    OwnedDOs_SlimState(k.subjects, s_id)
}




//******** Partition ID  ********//
// Return the ID of the partition that the subject (id == <s_id>)
// belongs to.
// Return NULL if the subject does not belong to any partition 
function method SubjPID(k:State, s_id:Subject_ID): Partition_ID
    requires IsSubjID(k.subjects, s_id)
    ensures SubjPID(k, s_id) == SubjPID_SlimState(k.subjects, s_id)
{
    SubjPID_SlimState(k.subjects, s_id)
}

// Return the ID of the partition that the object (id == <o_id>) 
// belongs to. 
// Return NULL if the object does not belong to any partition 
function method ObjPID(k:State, o_id:Object_ID) : Partition_ID
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id
    requires o_id in AllObjsIDs(k.objects)

    ensures (TD_ID(o_id) in k.objects.tds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.tds[TD_ID(o_id)].pid) &&
            (FD_ID(o_id) in k.objects.fds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.fds[FD_ID(o_id)].pid) &&
            (DO_ID(o_id) in k.objects.dos ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.dos[DO_ID(o_id)].pid)

    ensures ObjPID_KObjects(k.objects, o_id) == ObjPID(k, o_id)
{
    ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k.objects), o_id)
}

function method ObjPID_KObjects(k_objects:Objects, o_id:Object_ID) : Partition_ID
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id
    requires o_id in AllObjsIDs(k_objects)

    ensures (TD_ID(o_id) in k_objects.tds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.tds[TD_ID(o_id)].pid) &&
            (FD_ID(o_id) in k_objects.fds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.fds[FD_ID(o_id)].pid) &&
            (DO_ID(o_id) in k_objects.dos ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.dos[DO_ID(o_id)].pid)
{
    ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id)
}

// Return the ID of the partition that the device (id == <dev_id>)
// belongs to.
// Return NULL if the device does not belong to any partition 
function method SubjPID_DevID(k:State, dev_id:Dev_ID): Partition_ID
    requires IsDevID(k, dev_id)
    ensures SubjPID_DevID(k, dev_id) == SubjPID_DevID_SlimState(k.subjects, dev_id)
{
    SubjPID_DevID_SlimState(k.subjects, dev_id)
}




//******** Active/Inactive Subjects/Objects  ********//
// Return all active subjects in the current state <k>
function method AllActiveSubjs(k:State) : set<Subject_ID>
    ensures AllActiveSubjs(k) == AllActiveSubjs_SlimState(k.subjects)
{
    AllActiveSubjs_SlimState(k.subjects)
}

// Return all active objects in the current state <k>
function method AllActiveObjs(k:State) : set<Object_ID>
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    ensures AllActiveObjs(k) == AllActiveObjs_SlimState(k.objects)
{
    AllActiveObjs_SlimState(k.objects)
}

function method AllActiveTDs(k:State) : set<TD_ID>
    ensures AllActiveTDs(k) == AllActiveTDs_SlimState(k.objects.tds)
{
    AllActiveTDs_SlimState(k.objects.tds)
}

function method AllActiveFDs(k:State) : set<FD_ID>
    ensures AllActiveFDs(k) == AllActiveFDs_SlimState(k.objects.fds)
{
    AllActiveFDs_SlimState(k.objects.fds)
}

function method AllActiveDOs(k:State) : set<DO_ID>
    ensures AllActiveDOs(k) == AllActiveDOs_SlimState(k.objects.dos)
{
    AllActiveDOs_SlimState(k.objects.dos)
}

function method TDsToTDsVals(tds:map<TD_ID, TD_State>) : map<TD_ID, TD_Val>
    ensures MapGetKeys(TDsToTDsVals(tds)) == MapGetKeys(tds)
{
    map td_id | td_id in tds
              :: tds[td_id].val
}

// Get the current state of active TDs of <k>
function method ActiveTDsState(k:State) : map<TD_ID, TD_Val>
    ensures MapGetKeys(ActiveTDsState(k)) == AllActiveTDs(k)
    ensures ActiveTDsState(k) == ActiveTDsState_SlimState(k.objects.tds)
{
    ActiveTDsState_SlimState(k.objects.tds)
}

// Return all active devices in the current state <k>
function method AllActiveDrvs(k:State) : set<Drv_ID>
    ensures AllActiveDrvs(k) == AllActiveDrvs_SlimState(k.subjects)
{
    AllActiveDrvs_SlimState(k.subjects)
}

// Return all active devices in the current state <k>
function method AllActiveDevs(k:State) : set<Dev_ID>
    ensures AllActiveDevs(k) == AllActiveDevs_SlimState(k.subjects)
{
    AllActiveDevs_SlimState(k.subjects)
}

// Return all active subjects in the partition (id == <pid>)
function method ActiveSubjsInPartition(k:State, pid:Partition_ID) : set<Subject_ID>
    requires pid != NULL

    ensures ActiveSubjsInPartition(k, pid) <= AllActiveSubjs(k)
{
    set s_id | s_id in AllSubjsIDs(k.subjects) && SubjPID(k, s_id) == pid :: s_id 
}

// Return all active objects in the partition (id == <pid>)
function method ActiveObjsInPartition(k:State, pid:Partition_ID) : set<Object_ID>
    requires forall td_id, fd_id :: TD_ID(td_id) in k.objects.tds && FD_ID(fd_id) in k.objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k.objects.tds && DO_ID(do_id) in k.objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k.objects.fds && DO_ID(do_id) in k.objects.dos
                ==> fd_id != do_id

    requires pid != NULL

    ensures ActiveObjsInPartition(k, pid) <= AllActiveObjs(k)
{
    set o_id |  o_id in AllObjsIDs(k.objects) && 
                ObjPID(k, o_id) == pid
             :: o_id
}

// Return all active devices in the partition (id == <pid>)
function method ActiveDevsInPartition(
    k_subjects:Subjects, pid:Partition_ID
) : set<Dev_ID>
    requires pid != NULL

    ensures ActiveDevsInPartition(k_subjects, pid) <= AllActiveDevs_SlimState(k_subjects)
{
    set dev_id | dev_id in k_subjects.devs && SubjPID_SlimState(k_subjects, dev_id.sid) == pid :: dev_id 
}




//******** TDs/FDs/DOs  ********//
function method TDRefedObjs(td:TD_Val) : set<Object_ID>
{
    TDIDsToObjIDs(MapGetKeys(td.trans_params_tds)) + 
    FDIDsToObjIDs(MapGetKeys(td.trans_params_fds)) +
    DOIDsToObjIDs(MapGetKeys(td.trans_params_dos))
}

function method IsTDClearVal(tds:map<TD_ID, TD_State>, td_id:TD_ID) : bool
    requires td_id in tds
{
    tds[td_id].val == TD_Val(map[], map[], map[])
}

function method IsFDClearVal(fds:map<FD_ID, FD_State>, fd_id:FD_ID) : bool
    requires fd_id in fds
{
    fds[fd_id].val == FD_Val("")
}

function method IsDOClearVal(dos:map<DO_ID, DO_State>, do_id:DO_ID) : bool
    requires do_id in dos
{
    dos[do_id].val == DO_Val("")
}

function method WriteTDsVals(
    tds:map<TD_ID, TD_State>, td_id_val_map:map<TD_ID, TD_Val>
) : map<TD_ID, TD_State>
    requires forall td_id:: td_id in td_id_val_map ==> td_id in tds

    ensures forall td_id :: td_id in tds <==> td_id in WriteTDsVals(tds, td_id_val_map)
    ensures MapGetKeys(WriteTDsVals(tds, td_id_val_map)) == MapGetKeys(tds)
    ensures forall td_id :: td_id in tds
                ==> (td_id in td_id_val_map ==> WriteTDsVals(tds, td_id_val_map)[td_id].val == td_id_val_map[td_id]) &&
                    (td_id !in td_id_val_map ==> WriteTDsVals(tds, td_id_val_map)[td_id] == tds[td_id])
        // Property: The values in <td_id_val_map> is written into result
    ensures forall td_id :: td_id in tds
                ==> tds[td_id].pid == WriteTDsVals(tds, td_id_val_map)[td_id].pid
        // Property: WriteTD does not change the pids of any TDs
{
    map td_id | td_id in tds 
            :: if td_id !in td_id_val_map then tds[td_id] else TD_State(tds[td_id].pid, td_id_val_map[td_id])
}

function method WriteFDsVals(
    fds:map<FD_ID, FD_State>, fd_id_val_map:map<FD_ID, FD_Val>
) : map<FD_ID, FD_State>
    requires forall fd_id:: fd_id in fd_id_val_map ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in WriteFDsVals(fds, fd_id_val_map)
    ensures MapGetKeys(WriteFDsVals(fds, fd_id_val_map)) == MapGetKeys(fds)
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in fd_id_val_map ==> WriteFDsVals(fds, fd_id_val_map)[fd_id].val == fd_id_val_map[fd_id]) &&
                    (fd_id !in fd_id_val_map ==> WriteFDsVals(fds, fd_id_val_map)[fd_id] == fds[fd_id])
        // Property: The values in <fd_id_val_map> is written into result
    ensures forall fd_id :: fd_id in fds
                ==> fds[fd_id].pid == WriteFDsVals(fds, fd_id_val_map)[fd_id].pid
        // Property: WriteFD does not change the pids of any FDs
{
    map fd_id | fd_id in fds 
            :: if fd_id !in fd_id_val_map then fds[fd_id] else FD_State(fds[fd_id].pid, fd_id_val_map[fd_id])
}

function method WriteDOsVals(
    dos:map<DO_ID, DO_State>, do_id_val_map:map<DO_ID, DO_Val>
) : map<DO_ID, DO_State>
    requires forall do_id:: do_id in do_id_val_map ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in WriteDOsVals(dos, do_id_val_map)
    ensures MapGetKeys(WriteDOsVals(dos, do_id_val_map)) == MapGetKeys(dos)
    ensures forall do_id :: do_id in dos
                ==> (do_id in do_id_val_map ==> WriteDOsVals(dos, do_id_val_map)[do_id].val == do_id_val_map[do_id]) &&
                    (do_id !in do_id_val_map ==> WriteDOsVals(dos, do_id_val_map)[do_id] == dos[do_id])
        // Property: The values in <do_id_val_map> is written into result
    ensures forall do_id :: do_id in dos
                ==> dos[do_id].pid == WriteDOsVals(dos, do_id_val_map)[do_id].pid
        // Property: WriteDO does not change the pids of any DOs
{
    map do_id | do_id in dos 
            :: if do_id !in do_id_val_map then dos[do_id] else DO_State(dos[do_id].pid, do_id_val_map[do_id])
}

function method SetTDsPIDs(
    tds:map<TD_ID, TD_State>, tds_to_modify:set<TD_ID>, new_pid:Partition_ID
) : map<TD_ID, TD_State>
    requires forall td_id:: td_id in tds_to_modify ==> td_id in tds

    ensures forall td_id :: td_id in tds <==> td_id in SetTDsPIDs(tds, tds_to_modify, new_pid)
    ensures MapGetKeys(SetTDsPIDs(tds, tds_to_modify, new_pid)) == MapGetKeys(tds)
    ensures forall td_id :: td_id in tds
                ==> (td_id in tds_to_modify ==> (SetTDsPIDs(tds, tds_to_modify, new_pid)[td_id].pid == new_pid && SetTDsPIDs(tds, tds_to_modify, new_pid)[td_id].val == tds[td_id].val)) &&
                    (td_id !in tds_to_modify ==> SetTDsPIDs(tds, tds_to_modify, new_pid)[td_id] == tds[td_id])
        // Property: In <SetTDsPIDs(tds, tds_to_modify, new_pid)>, all PIDs of <tds_to_modify> are modified
{
    map td_id | td_id in tds 
            :: if td_id !in tds_to_modify then tds[td_id] else TD_State(new_pid, tds[td_id].val)
}

function method SetFDsPIDs(
    fds:map<FD_ID, FD_State>, fds_to_modify:set<FD_ID>, new_pid:Partition_ID
) : map<FD_ID, FD_State>
    requires forall fd_id:: fd_id in fds_to_modify ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in SetFDsPIDs(fds, fds_to_modify, new_pid)
    ensures MapGetKeys(SetFDsPIDs(fds, fds_to_modify, new_pid)) == MapGetKeys(fds)
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in fds_to_modify ==> (SetFDsPIDs(fds, fds_to_modify, new_pid)[fd_id].pid == new_pid && SetFDsPIDs(fds, fds_to_modify, new_pid)[fd_id].val == fds[fd_id].val)) &&
                    (fd_id !in fds_to_modify ==> SetFDsPIDs(fds, fds_to_modify, new_pid)[fd_id] == fds[fd_id])
        // Property: In <SetFDsPIDs(fds, fds_to_modify, new_pid)>, all PIDs of <fds_to_modify> are modified
{
    map fd_id | fd_id in fds 
            :: if fd_id !in fds_to_modify then fds[fd_id] else FD_State(new_pid, fds[fd_id].val)
}

function method SetDOsPIDs(
    dos:map<DO_ID, DO_State>, dos_to_modify:set<DO_ID>, new_pid:Partition_ID
) : map<DO_ID, DO_State>
    requires forall do_id:: do_id in dos_to_modify ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in SetDOsPIDs(dos, dos_to_modify, new_pid)
    ensures MapGetKeys(SetDOsPIDs(dos, dos_to_modify, new_pid)) == MapGetKeys(dos)
    ensures forall do_id :: do_id in dos
                ==> (do_id in dos_to_modify ==> (SetDOsPIDs(dos, dos_to_modify, new_pid)[do_id].pid == new_pid && SetDOsPIDs(dos, dos_to_modify, new_pid)[do_id].val == dos[do_id].val)) &&
                    (do_id !in dos_to_modify ==> SetDOsPIDs(dos, dos_to_modify, new_pid)[do_id] == dos[do_id])
        // Property: In <SetDOsPIDs(dos, dos_to_modify, new_pid)>, all PIDs of <dos_to_modify> are modified
{
    map do_id | do_id in dos 
            :: if do_id !in dos_to_modify then dos[do_id] else DO_State(new_pid, dos[do_id].val)
}

function method ClearTDs(
    tds:map<TD_ID, TD_State>, clear_tds:set<TD_ID>
) : map<TD_ID, TD_State>
    requires forall td_id:: td_id in clear_tds ==> td_id in tds

    ensures forall td_id :: td_id in tds <==> td_id in ClearTDs(tds, clear_tds)
    ensures forall td_id :: td_id in tds
                ==> (td_id in clear_tds ==> ClearTDs(tds, clear_tds)[td_id].val == TD_Val(map[], map[], map[])) &&
                    (td_id !in clear_tds ==> ClearTDs(tds, clear_tds)[td_id] == tds[td_id])
    ensures forall td_id :: td_id in tds
                ==> (td_id in clear_tds ==> IsTDClearVal(ClearTDs(tds, clear_tds), td_id)) &&
                    (td_id !in clear_tds ==> ClearTDs(tds, clear_tds)[td_id] == tds[td_id])
        // Property: In <ClearTDs(tds, clear_tds)>, all TD IDs in <clear_tds> are map to {}
    ensures forall td_id :: td_id in tds
                ==> tds[td_id].pid == ClearTDs(tds, clear_tds)[td_id].pid
        // Property: WriteTD does not change the pids of any TDs
{
    map td_id | td_id in tds 
            :: if td_id !in clear_tds then tds[td_id] else TD_State(tds[td_id].pid, TD_Val(map[], map[], map[]))
}

function method ClearFDs(
    fds:map<FD_ID, FD_State>, clear_fds:set<FD_ID>
) : map<FD_ID, FD_State>
    requires forall fd_id:: fd_id in clear_fds ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in ClearFDs(fds, clear_fds)
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in clear_fds ==> ClearFDs(fds, clear_fds)[fd_id].val == FD_Val("")) &&
                    (fd_id !in clear_fds ==> ClearFDs(fds, clear_fds)[fd_id] == fds[fd_id])
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in clear_fds ==> IsFDClearVal(ClearFDs(fds, clear_fds), fd_id)) &&
                    (fd_id !in clear_fds ==> ClearFDs(fds, clear_fds)[fd_id] == fds[fd_id])
        // Property: In <ClearFDs(fds, clear_fds)>, all FD IDs in <clear_fds> are map to {}
    ensures forall fd_id :: fd_id in fds
                ==> fds[fd_id].pid == ClearFDs(fds, clear_fds)[fd_id].pid
        // Property: WriteFD does not change the pids of any FDs
{
    map fd_id | fd_id in fds 
            :: if fd_id !in clear_fds then fds[fd_id] else FD_State(fds[fd_id].pid, FD_Val(""))
}

function method ClearDOs(
    dos:map<DO_ID, DO_State>, clear_dos:set<DO_ID>
) : map<DO_ID, DO_State>
    requires forall do_id:: do_id in clear_dos ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in ClearDOs(dos, clear_dos)
    ensures forall do_id :: do_id in dos
                ==> (do_id in clear_dos ==> ClearDOs(dos, clear_dos)[do_id].val == DO_Val("")) &&
                    (do_id !in clear_dos ==> ClearDOs(dos, clear_dos)[do_id] == dos[do_id])
    ensures forall do_id :: do_id in dos
                ==> (do_id in clear_dos ==> IsDOClearVal(ClearDOs(dos, clear_dos), do_id)) &&
                    (do_id !in clear_dos ==> ClearDOs(dos, clear_dos)[do_id] == dos[do_id])
        // Property: In <ClearDOs(dos, clear_dos)>, all DO IDs in <clear_dos> are map to {}
    ensures forall do_id :: do_id in dos
                ==> dos[do_id].pid == ClearDOs(dos, clear_dos)[do_id].pid
        // Property: WriteDO does not change the pids of any DOs
{
    map do_id | do_id in dos 
            :: if do_id !in clear_dos then dos[do_id] else DO_State(dos[do_id].pid, DO_Val(""))
}

function method DrvDevRead_ReplaceSrcTDWithVal(
    k:State, tds_dst_src:map<TD_ID, TD_ID>
) : (td_id_val_map:map<TD_ID, TD_Val>)
    requires forall td_id :: td_id in tds_dst_src
                ==> td_id in k.objects.tds && tds_dst_src[td_id] in k.objects.tds

    ensures MapGetKeys(td_id_val_map) == MapGetKeys(tds_dst_src)
    ensures forall td_id :: td_id in td_id_val_map
                ==> td_id_val_map[td_id] == k.objects.tds[tds_dst_src[td_id]].val
{
    map td_id | td_id in tds_dst_src :: k.objects.tds[tds_dst_src[td_id]].val
}

function method DrvDevRead_ReplaceSrcFDWithVal(
    k:State, fds_dst_src:map<FD_ID, FD_ID>
) : (fd_id_val_map:map<FD_ID, FD_Val>)
    requires forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in k.objects.fds && fds_dst_src[fd_id] in k.objects.fds

    ensures MapGetKeys(fd_id_val_map) == MapGetKeys(fds_dst_src)
    ensures forall fd_id :: fd_id in fd_id_val_map
                ==> fd_id_val_map[fd_id] == k.objects.fds[fds_dst_src[fd_id]].val
{
    map fd_id | fd_id in fds_dst_src :: k.objects.fds[fds_dst_src[fd_id]].val
}

function method DrvDevRead_ReplaceSrcDOWithVal(
    k:State, dos_dst_src:map<DO_ID, DO_ID>
) : (do_id_val_map:map<DO_ID, DO_Val>)
    requires forall do_id :: do_id in dos_dst_src
                ==> do_id in k.objects.dos && dos_dst_src[do_id] in k.objects.dos

    ensures MapGetKeys(do_id_val_map) == MapGetKeys(dos_dst_src)
    ensures forall do_id :: do_id in do_id_val_map
                ==> do_id_val_map[do_id] == k.objects.dos[dos_dst_src[do_id]].val
{
    map do_id | do_id in dos_dst_src :: k.objects.dos[dos_dst_src[do_id]].val
}




//******** Utilities for specific operations ********//
function method DrvWrite_ProposedNewState(k:State, 
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
) : (k':State)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.dos)
{
    var tds' := WriteTDsVals(k.objects.tds, td_id_val_map);
    var fds' := WriteFDsVals(k.objects.fds, fd_id_val_map);
    var dos' := WriteDOsVals(k.objects.dos, do_id_val_map);
    var k'_objects := Objects(tds', fds', dos');

    State(k.subjects, k'_objects, k.pids, k.tds_to_all_states)
}


