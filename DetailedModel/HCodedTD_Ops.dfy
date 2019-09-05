include "Utils.dfy"

function method DM_AllHCodedTDIDs(ws_subjects:Subjects) : set<TD_ID>
    ensures forall td_id :: td_id in DM_AllHCodedTDIDs(ws_subjects)
                <==> (exists dev_id :: dev_id in ws_subjects.devs &&
                      td_id == ws_subjects.devs[dev_id].hcoded_td_id)
{
    AllHCodedTDIDs(ws_subjects)
}

function method DM_BuildMap_DevsToHCodedTDVals(ws_subjects:Subjects, ws_objects:Objects) : map<Dev_ID, TD_Val>
    requires forall dev_id :: dev_id in ws_subjects.devs
                ==> ws_subjects.devs[dev_id].hcoded_td_id in ws_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in ws_subjects.devs && td_id in ws_subjects.devs[dev_id].td_ids
                ==> td_id in ws_objects.tds

    ensures MapGetKeys(DM_BuildMap_DevsToHCodedTDVals(ws_subjects, ws_objects)) == DM_AllDevIDs(ws_subjects)
        // Property: The result map contains all devices in wimp system
    ensures forall dev_id :: dev_id in ws_subjects.devs
                ==> DM_BuildMap_DevsToHCodedTDVals(ws_subjects, ws_objects)[dev_id] == 
                    ws_objects.tds[ws_subjects.devs[dev_id].hcoded_td_id].val
{
    BuildMap_DevsToHCodedTDVals(ws_subjects, ws_objects)
}