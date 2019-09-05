include "Utils.dfy"

function method AllHCodedTDIDs(k_subjects:Subjects) : set<TD_ID>
    ensures forall td_id :: td_id in AllHCodedTDIDs(k_subjects)
                <==> (exists dev_id :: dev_id in k_subjects.devs &&
                      td_id == k_subjects.devs[dev_id].hcoded_td_id)
{
    set dev_id | dev_id in k_subjects.devs
               :: k_subjects.devs[dev_id].hcoded_td_id
}

function method BuildMap_DevsToHCodedTDVals(k_subjects:Subjects, k_objects:Objects) : map<Dev_ID, TD_Val>
    requires forall dev_id :: dev_id in k_subjects.devs
                ==> k_subjects.devs[dev_id].hcoded_td_id in k_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k_subjects.devs && td_id in k_subjects.devs[dev_id].td_ids
                ==> td_id in k_objects.tds

    ensures MapGetKeys(BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)) == MapGetKeys(k_subjects.devs)
    ensures forall dev_id :: dev_id in k_subjects.devs
                ==> BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id] == 
                    k_objects.tds[k_subjects.devs[dev_id].hcoded_td_id].val
{
    map dev_id | dev_id in k_subjects.devs
               :: k_objects.tds[k_subjects.devs[dev_id].hcoded_td_id].val
}

function method HCodedTDValOfDev(hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID) : TD_Val
    requires dev_id in hcoded_tds
{
    hcoded_tds[dev_id]
}

// Returns true if all transfers in hardcoded TD of a device (<dev_id>) point
// to I/O objects in the device
predicate DevHCodedTDRefsObjsInSameDev(k:State, dev_id:Dev_ID)
    requires IsDevID(k, dev_id)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    ensures DevHCodedTDRefsObjsInSameDev(k, dev_id) == 
            DevHCodedTDRefsObjsInSameDev_SlimState(k.subjects, BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id)
{
    var hcoded_tds := BuildMap_DevsToHCodedTDVals(k.subjects, k.objects);
    (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
        IDToDev(k, dev_id).td_ids) &&
    (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
        IDToDev(k, dev_id).fd_ids) &&
    (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
        IDToDev(k, dev_id).do_ids)
}

predicate DevHCodedTDRefsObjsInSameDev_SlimState(k_subjects:Subjects, hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID)
    requires dev_id in k_subjects.devs
    requires dev_id in hcoded_tds
{
   (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
        IDToDev_SlimState(k_subjects, dev_id).td_ids) &&
   (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
        IDToDev_SlimState(k_subjects, dev_id).fd_ids) &&
   (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
        IDToDev_SlimState(k_subjects, dev_id).do_ids)
}

// Returns true if hardcoded TDs of all devices are unchanged between k and k'
predicate SameMapDevsToHCodedTDVals(k:State, k':State)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in k.objects.tds

    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'.objects.tds) == MapGetKeys(k.objects.tds)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id
{
    BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)
}

function method GetTransfersToTDsInHCodedTD(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
) : map<TD_ID, TD_Trans_Param>
    requires dev_id in hcoded_tds
{
    HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
}

function method GetTransfersToFDsInHCodedTD(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
) : map<FD_ID, FD_Trans_Param>
    requires dev_id in hcoded_tds
{
    HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds
}

function method GetTransfersToDOsInHCodedTD(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
) : map<DO_ID, DO_Trans_Param>
    requires dev_id in hcoded_tds
{
    HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos
}

// Returns if the device (<dev_id>) refs the object (<o_id>) in the hardcoded 
// TD of the device
function method DoObjRefedInDevHCodedTD(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID, o_id:Object_ID
) : bool
    requires dev_id in hcoded_tds
{
    TD_ID(o_id) in GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id) ||
    FD_ID(o_id) in GetTransfersToFDsInHCodedTD(hcoded_tds, dev_id) ||
    DO_ID(o_id) in GetTransfersToDOsInHCodedTD(hcoded_tds, dev_id)
}

// Returns the access modes to the object (<o_id>) as recorded in the hardcoded 
// TD of the device
function method AModesToObjInDevHCodedTD(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID, o_id:Object_ID
) : set<AMode>
    requires dev_id in hcoded_tds
    requires DoObjRefedInDevHCodedTD(hcoded_tds, dev_id, o_id)
{
    if (TD_ID(o_id) in GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id)) then
        GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id)[TD_ID(o_id)].amodes
    else if (FD_ID(o_id) in GetTransfersToFDsInHCodedTD(hcoded_tds, dev_id)) then
        GetTransfersToFDsInHCodedTD(hcoded_tds, dev_id)[FD_ID(o_id)].amodes 
    else
        GetTransfersToDOsInHCodedTD(hcoded_tds, dev_id)[DO_ID(o_id)].amodes
}

// Return the TDs referenced by the device (<dev_id>)'s hardcoded TD with R
function method TDsRefedByDevHCodedTDWithR(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
) : set<TD_ID>
    requires dev_id in hcoded_tds
{
    set td_id | td_id in GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id) &&
                R in AModesToObjInDevHCodedTD(hcoded_tds, dev_id, td_id.oid)
            :: td_id
}

// Return the TDs referenced by the device (<dev_id>)'s hardcoded TD with W
function method TDsDevHCodedWrite(
    hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
) : set<TD_ID>
    requires dev_id in hcoded_tds
{
    set td_id | td_id in GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id) &&
                W in AModesToObjInDevHCodedTD(hcoded_tds, dev_id, td_id.oid)
            :: td_id
}

lemma Lemma_TDsDevHCodedRead_ReturnsAllTDsReadRefedInHCodedTD(
    k_subjects:Subjects, k_objects:Objects, hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id
        // Requirement: Internal IDs of TDs/FDs/DOs are different
    requires IsDevID_SlimState(k_subjects, dev_id)
    requires forall dev_id :: dev_id in k_subjects.devs
                ==> k_subjects.devs[dev_id].hcoded_td_id in k_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k_subjects.devs && td_id in k_subjects.devs[dev_id].td_ids
                ==> td_id in k_objects.tds 

    requires IDToDev_SlimState(k_subjects, dev_id).td_ids <= MapGetKeys(k_objects.tds)
    requires IDToDev_SlimState(k_subjects, dev_id).fd_ids <= MapGetKeys(k_objects.fds)
    requires IDToDev_SlimState(k_subjects, dev_id).do_ids <= MapGetKeys(k_objects.dos)
        // Requirement: Objects in the device are also in the state
    requires forall dev_id2, td_id :: dev_id2 in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects) &&
                    td_id in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id2].trans_params_tds
                ==> td_id in IDToDev_SlimState(k_subjects, dev_id2).td_ids
    requires forall dev_id2, fd_id :: dev_id2 in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects) &&
                    fd_id in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id2].trans_params_fds
                ==> fd_id in IDToDev_SlimState(k_subjects, dev_id2).fd_ids
    requires forall dev_id2, do_id :: dev_id2 in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects) &&
                    do_id in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id2].trans_params_dos
                ==> do_id in IDToDev_SlimState(k_subjects, dev_id2).do_ids
        // Requirement: Hardcoded TDs in each device must ref objects in the same device
    requires hcoded_tds == BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)
                     
    ensures TDsRefedByDevHCodedTDWithR(hcoded_tds, dev_id) <= IDToDev_SlimState(k_subjects, dev_id).td_ids
    ensures TDsRefedByDevHCodedTDWithR(hcoded_tds, dev_id) <= MapGetKeys(k_objects.tds)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects) &&
                TD_ID(o_id) in IDToDev_SlimState(k_subjects, dev_id).td_ids &&
                DoObjRefedInDevHCodedTD(hcoded_tds, dev_id, o_id) &&
                R in AModesToObjInDevHCodedTD(hcoded_tds, dev_id, o_id) 
                <==> TD_ID(o_id) in TDsRefedByDevHCodedTDWithR(hcoded_tds, dev_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_TDsDevHCodedWrite_ReturnsAllTDsWriteRefedInHCodedTD(
    k_subjects:Subjects, k_objects:Objects, hcoded_tds:map<Dev_ID, TD_Val>, dev_id:Dev_ID
)
    requires forall td_id, fd_id :: TD_ID(td_id) in k_objects.tds && FD_ID(fd_id) in k_objects.fds
                ==> td_id != fd_id
    requires forall td_id, do_id :: TD_ID(td_id) in k_objects.tds && DO_ID(do_id) in k_objects.dos
                ==> td_id != do_id
    requires forall fd_id, do_id :: FD_ID(fd_id) in k_objects.fds && DO_ID(do_id) in k_objects.dos
                ==> fd_id != do_id
        // Requirement: Internal IDs of TDs/FDs/DOs are different
    requires IsDevID_SlimState(k_subjects, dev_id)
    requires forall dev_id :: dev_id in k_subjects.devs
                ==> k_subjects.devs[dev_id].hcoded_td_id in k_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k_subjects.devs && td_id in k_subjects.devs[dev_id].td_ids
                ==> td_id in k_objects.tds 

    requires IDToDev_SlimState(k_subjects, dev_id).td_ids <= MapGetKeys(k_objects.tds)
    requires IDToDev_SlimState(k_subjects, dev_id).fd_ids <= MapGetKeys(k_objects.fds)
    requires IDToDev_SlimState(k_subjects, dev_id).do_ids <= MapGetKeys(k_objects.dos)
        // Requirement: Objects in the device are also in the state
    requires forall dev_id2, td_id :: dev_id2 in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects) &&
                    td_id in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id2].trans_params_tds
                ==> td_id in IDToDev_SlimState(k_subjects, dev_id2).td_ids
    requires forall dev_id2, fd_id :: dev_id2 in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects) &&
                    fd_id in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id2].trans_params_fds
                ==> fd_id in IDToDev_SlimState(k_subjects, dev_id2).fd_ids
    requires forall dev_id2, do_id :: dev_id2 in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects) &&
                    do_id in BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)[dev_id2].trans_params_dos
                ==> do_id in IDToDev_SlimState(k_subjects, dev_id2).do_ids
        // Requirement: Hardcoded TDs in each device must ref objects in the same device
    requires hcoded_tds == BuildMap_DevsToHCodedTDVals(k_subjects, k_objects)
                     
    ensures TDsDevHCodedWrite(hcoded_tds, dev_id) <= IDToDev_SlimState(k_subjects, dev_id).td_ids
    ensures TDsDevHCodedWrite(hcoded_tds, dev_id) <= MapGetKeys(k_objects.tds)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects) &&
                TD_ID(o_id) in IDToDev_SlimState(k_subjects, dev_id).td_ids &&
                DoObjRefedInDevHCodedTD(hcoded_tds, dev_id, o_id) &&
                W in AModesToObjInDevHCodedTD(hcoded_tds, dev_id, o_id) 
                <==> TD_ID(o_id) in TDsDevHCodedWrite(hcoded_tds, dev_id)
{
    // Dafny can automatically prove this lemma
}

function method GetDevHCodedObjs(
    hcoded_tds:map<Dev_ID, TD_Val>,
    dev_id:Dev_ID
) : set<Object_ID>
    requires dev_id in hcoded_tds
    
    ensures forall o_id :: o_id in GetDevHCodedObjs(hcoded_tds, dev_id)
                <==> (TD_ID(o_id) in GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id) ||
                      FD_ID(o_id) in GetTransfersToFDsInHCodedTD(hcoded_tds, dev_id) ||
                      DO_ID(o_id) in GetTransfersToDOsInHCodedTD(hcoded_tds, dev_id))
{
    Lemma_SameIDsIffSameInternalIDs();
    (set td_id, o_id | td_id in GetTransfersToTDsInHCodedTD(hcoded_tds, dev_id) && o_id == td_id.oid :: o_id) +
    (set fd_id, o_id | fd_id in GetTransfersToFDsInHCodedTD(hcoded_tds, dev_id) && o_id == fd_id.oid :: o_id) +
    (set do_id, o_id | do_id in GetTransfersToDOsInHCodedTD(hcoded_tds, dev_id) && o_id == do_id.oid :: o_id)
}

function method TDWriteTransferInTD(
    trans_param_tds:map<TD_ID, TD_Trans_Param>, target_td_id:TD_ID, new_val:TD_Val
) : bool
{
    target_td_id in trans_param_tds &&
    W in trans_param_tds[target_td_id].amodes &&
    new_val in trans_param_tds[target_td_id].vals
}