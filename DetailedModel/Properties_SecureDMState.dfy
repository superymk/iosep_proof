include "../Abstract/Utils.dfy"
include "../Abstract/BuildCAS/Utils_BuildCAS.dfy"
include "Utils.dfy"
include "Syntax.dfy"
include "HCodedTD_Ops.dfy"
include "Properties_DevHWProt.dfy"
include "Properties_ValidDMState.dfy"

predicate DM_IsSecureState(ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
{
    DM_IsSecureState_SI1(ws) && DM_IsSecureState_SI2(ws) && DM_IsSecureState_SI3(ws)
}

predicate DM_IsSecureState_SI1(ws:DM_State)
    requires DM_IsValidState_SubjsObjsPIDs(ws)
{
    //// SI1: The snapshot of red TDs must be from the abstraction of 
    //// hardware protection mechanisms
    ////// SI1.2
    P_DevHWProt_TDsReadByRedDevsOnlyHaveTransfersToRedObjsAtAnyTime(ws) &&
        
    (true)
}

predicate DM_IsSecureState_SI2(ws:DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
    requires forall dev_id :: dev_id in ws.subjects.devs
                ==> ws.subjects.devs[dev_id].hcoded_td_id in ws.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in ws.subjects.devs && td_id in ws.subjects.devs[dev_id].td_ids
                ==> td_id in ws.objects.tds
{
    var k := DMStateToState(ws);

    //// SI2: All active USB TDs in green partitions contain secure transfers 
    //// to I/O objects only.
    //// The transfers in a USB TD are secure, iff (1) the linked USB TD must 
    //// exist, and (2) FDs/DOs refed in USB data transfers contains must exist,
    //// and (3) USB data transfers do not ref any TDs, and (4) all these 
    //// drivers must be in the same partition with the USB TD (<usb_td_id>)
    //// USB data transfers are used to access FDs and DOs in USB hubs and 
    //// peripheral devices
    (forall td_id :: td_id in DM_TDIDsInGreen(ws)
            ==> DoTDsIncludeSecureNoTDWriteTransfersOnly(KToKParams(k), ActiveTDsState(k), td_id))
}

predicate DM_IsSecureState_SI3(ws:DM_State)
    requires P_DMObjectsHasUniqueIDs(ws.objects)
{
    var k := DMStateToState(ws);

    IsSecureState_SI2(DMStateToState(ws))
}

// Returns if an operation fulfills all transition constraints (TCs)
// The operation transits from <ws> to <ws'>
predicate DM_IsSecureOps(ws:DM_State, ws':DM_State)
    requires DM_IsValidState(ws)
{
    IsSecureOps(DMStateToState(ws), DMStateToState(ws')) &&

    ws.red_pid == ws'.red_pid &&
    ws.devs_activatecond == ws'.devs_activatecond
}