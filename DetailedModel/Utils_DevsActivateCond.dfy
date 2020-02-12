include "Utils.dfy"
include "Properties_ValidDMState.dfy"

// Returns all other wimp devices that can be activated into red partition
function method DevsCanBeActivatedInRed(ws:DM_State) : set<Dev_ID>
    requires DM_IsValidState_DevsActivateCond(ws)

    ensures forall dev_id :: dev_id in ws.subjects.devs &&
                    dev_id !in DevsCanBeActivatedInRed(ws)
                ==> DM_SubjPID(ws.subjects, dev_id.sid) != ws.red_pid
{
    set dev_id | dev_id in ws.subjects.devs &&
                  (forall dev_id2 :: dev_id2 in ws.devs_activatecond
                        ==> dev_id !in ws.devs_activatecond[dev_id2])
                :: dev_id
}

// Returns all other wimp devices that can be activated into green partitions
function method DevsCanBeActivatedInGreen(ws:DM_State) : set<Dev_ID>
    requires DM_IsValidState_DevsActivateCond(ws)

    ensures forall dev_id :: dev_id in ws.subjects.devs &&
                    dev_id !in DevsCanBeActivatedInGreen(ws)
                ==> DM_SubjPID(ws.subjects, dev_id.sid) == NULL ||  DM_SubjPID(ws.subjects, dev_id.sid) == ws.red_pid
{
    set dev_id | dev_id in ws.subjects.devs &&
                  dev_id !in ws.devs_activatecond
                :: dev_id
}

function method TryActivateDevInRed(ws:DM_State, dev_id:Dev_ID) : bool
    requires DM_IsValidState_DevsActivateCond(ws)
{
    dev_id in DevsCanBeActivatedInRed(ws) &&
    (dev_id in ws.devs_activatecond
            // If <dev_id> is in <devs_activatecond>
        ==> (forall dev_id2 :: dev_id2 in ws.devs_activatecond[dev_id]
                ==> DM_SubjPID(ws.subjects, dev_id2.sid) == NULL))
            // Then all mapped devices must be inactive
}

function method TryActivateDevInGreen(ws:DM_State, dev_id:Dev_ID) : bool
    requires DM_IsValidState_DevsActivateCond(ws)
{
    dev_id in DevsCanBeActivatedInGreen(ws) &&
    (forall dev_id2 :: dev_id2 in ws.devs_activatecond &&
            dev_id in ws.devs_activatecond[dev_id2]
            // For any red device mapped to this <dev_id>
        ==> DM_SubjPID(ws.subjects, dev_id2.sid) == NULL)
            // These red devices must be inactive
}