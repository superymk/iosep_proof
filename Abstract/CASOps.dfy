include "Syntax.dfy"
include "./utils/Collections.dfy"

datatype CAS_Key            = CAS_Key(dev_id:Dev_ID, obj_id:Object_ID)
                                // Current Access Set (CAS) maps from each pair
                                // (device's ID, object's ID) to a set of requested 
                                // access modes

datatype CAS                = CAS(m: map<Dev_ID, map<Object_ID, set<AMode>>>,
                                o_ids:set<Object_ID>) 
                                // <o_ids> is a helper field records objects in 
                                // the current CAS

function method IsSubjInCAS(
    cas:CAS, dev_id:Dev_ID
) : bool
{
    if (dev_id in cas.m) then
        true
    else
        false
}

function method IsObjInCAS(
    cas:CAS, o_id:Object_ID
) : bool
{
    if (o_id in cas.o_ids) then
        true
    else
        false
}

function method IsInCAS(
    cas:CAS, dev_id:Dev_ID, o_id:Object_ID
) : bool
{
    dev_id in cas.m && o_id in cas.m[dev_id]
}

function method CASGetSubjs(cas:CAS) : set<Dev_ID>
{
    MapGetKeys<Dev_ID, map<Object_ID, set<AMode>>>(cas.m)
}

function method CASGetObjs(cas:CAS) : set<Object_ID>
{        
    cas.o_ids
}

function method CASGetAModes(
    cas:CAS, dev_id:Dev_ID, o_id:Object_ID
) : set<AMode>
    requires IsInCAS(cas, dev_id, o_id)
{
    cas.m[dev_id][o_id]
}

method CASAddSubj(cas:CAS, dev_id:Dev_ID) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires !IsSubjInCAS(cas, dev_id)
        // Requirement: The subject (<dev_id>) is not present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) + {dev_id}
    ensures CASGetObjs(cas') == CASGetObjs(cas)
        // Property: The new CAS only adds the new subject into subjects, and
        // has the same set of objects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: The new CAS includes the permissions in the current CAS
    ensures forall o_id2 :: o_id2 in CASGetObjs(cas')
                ==> CASGetAModes(cas', dev_id, o_id2) == {}
        // Property: In the new CAS, the added subject has no permission to any
        // objects
{
    var new_perm : set<AMode> := {};
    
    var dev_id_m := MapCreateFromSet<Object_ID, set<AMode>>(map[], CASGetObjs(cas), new_perm);

    cas' := CAS(cas.m[dev_id := dev_id_m], cas.o_ids);
}

method CASAddObj(cas:CAS, o_id:Object_ID) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires !IsObjInCAS(cas, o_id)
        // Requirement: The object (<o_id>) is not present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas) + {o_id}
        // Property: The new CAS only adds the new object into objects, and
        // has the same set of subjects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: The new CAS includes the permissions in the current CAS
    ensures forall dev_id2 :: dev_id2 in CASGetSubjs(cas')
                ==> CASGetAModes(cas', dev_id2, o_id) == {}
        // Property: In the new CAS, all subjects has no permission to the added
        // object
{
    var i := 0;
    var sid_seq := SetToSeq<Dev_ID>(CASGetSubjs(cas));
    var new_oids := cas.o_ids + {o_id};
    var m_t : map<Dev_ID, map<Object_ID, set<AMode>>> := map[];
    var new_sid_m;  // the new map binding to the dev_id

    assert(forall dev_id2 :: dev_id2 in cas.m <==> dev_id2 in sid_seq);
     
    while(i < |sid_seq|)
        invariant (forall j :: 0 <= j < i && j < |sid_seq|
                ==> sid_seq[j] in m_t)
        invariant (forall j ::  i <= j < |sid_seq|
                ==>  sid_seq[j] !in m_t)
        invariant (forall dev_id2 :: dev_id2 in m_t ==> dev_id2 in sid_seq)

        invariant (forall dev_id2 :: dev_id2 in m_t 
                ==> MapGetKeys<Object_ID, set<AMode>>(m_t[dev_id2]) == new_oids)

        invariant (forall dev_id2, o_id2 :: dev_id2 in m_t 
                ==> (dev_id2 in cas.m && o_id2 in cas.m[dev_id2])
                        ==> (dev_id2 in m_t && o_id2 in m_t[dev_id2])) 
                // Corresponding to IsInCAS(cas, dev_id2, o_id2 ) ==> IsInCAS(cas', dev_id2, o_id2)
        invariant (forall dev_id2 :: dev_id2 in m_t ==> dev_id2 in cas.m)
        invariant (forall dev_id2, o_id2 :: dev_id2 in m_t && o_id2 in cas.m[dev_id2]
                ==> cas.m[dev_id2][o_id2] == m_t[dev_id2][o_id2])
                // Corresponding to CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)

        invariant (forall dev_id2 :: dev_id2 in m_t ==> m_t[dev_id2][o_id] == {})
                // Corresponding to CASGetAModes(cas', dev_id2, o_id) == {}
        invariant (|m_t| == i)
        invariant (i <= |sid_seq|)
    {
        var dev_id := sid_seq[i];
        var new_oid_m := cas.m[dev_id][o_id := {}];
        m_t := m_t[dev_id := new_oid_m];

        i := i + 1;
    }

    new_sid_m := m_t;

    cas' := CAS(new_sid_m, new_oids);
}

method CASAddSubjs(cas:CAS, dev_ids:set<Dev_ID>) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires forall dev_id :: dev_id in dev_ids ==> !IsSubjInCAS(cas, dev_id)
        // Requirement: The device (<dev_id>) is not present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) + dev_ids
    ensures CASGetObjs(cas') == CASGetObjs(cas)
        // Property: The new CAS only adds the new devices (<dev_ids>), and has 
        // the same set of objects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: The new CAS includes the permissions in the current CAS
    ensures forall dev_id2, o_id2 :: o_id2 in CASGetObjs(cas') && dev_id2 in dev_ids
                ==> CASGetAModes(cas', dev_id2, o_id2) == {}
        // Property: In the new CAS, all added subjects has no permission to the
        // objects

    decreases |dev_ids|
{
    if(|dev_ids| == 0)
    {    cas' := cas;    }
    else
    {
        var dev_id:| dev_id in dev_ids;

        var cas_step := CASAddSubj(cas, dev_id);
        var dev_ids_step := dev_ids - {dev_id};

        cas' := CASAddSubjs(cas_step, dev_ids_step);        
    }
}


method CASAddObjs(cas:CAS, o_ids:set<Object_ID>) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires forall o_id :: o_id in o_ids ==> !IsObjInCAS(cas, o_id)
        // Requirement: The object (<o_id>) is not present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas) + o_ids
        // Property: The new CAS only adds the new objects (<o_ids>), and has 
        // the same set of subjects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)
        // Property: The new CAS includes the permissions in the current CAS
    ensures forall dev_id2, o_id :: dev_id2 in CASGetSubjs(cas') && o_id in o_ids
                ==> CASGetAModes(cas', dev_id2, o_id) == {}
        // Property: In the new CAS, all subjects has no permission to the added
        // object

    decreases |o_ids|
{
    if(|o_ids| == 0)
    {    cas' := cas;    }
    else
    {
        var o_id:| o_id in o_ids;

        var cas_step := CASAddObj(cas, o_id);
        var o_ids_step := o_ids - {o_id};

        cas' := CASAddObjs(cas_step, o_ids_step);        
    }
} 

method CASDelSubj(cas:CAS, dev_id:Dev_ID) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires IsSubjInCAS(cas, dev_id)
        // Requirement: The subject (<dev_id>) must be present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) - {dev_id}
    ensures CASGetObjs(cas') == CASGetObjs(cas)
        // Property: The new CAS only removes the subject (<dev_id>), and has the
        // same set of objects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas', dev_id2, o_id2)
                ==> IsInCAS(cas, dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas', dev_id2, o_id2)
                ==> CASGetAModes(cas', dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)
        // Property: The current CAS includes the new CAS
{
    var m_new := map dev_id2 | (dev_id2 in cas.m) && (dev_id2 != dev_id) :: cas.m[dev_id2];

    cas' := CAS(m_new, cas.o_ids);
}

method CASDelObj(cas:CAS, o_id:Object_ID) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires IsObjInCAS(cas, o_id)
        // Requirement: The object (<o_id>) must be present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas) - {o_id}
        // Property: The new CAS only removes the object (<o_id>), and has the 
        // same set of subjects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas', dev_id2, o_id2)
                ==> IsInCAS(cas, dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas', dev_id2, o_id2)
                ==> CASGetAModes(cas', dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)
        // Property: The current CAS includes the new CAS
{
    var i := 0;
    var sid_seq := SetToSeq<Dev_ID>(CASGetSubjs(cas));
    var new_oids := cas.o_ids - {o_id};
    var m_t : map<Dev_ID, map<Object_ID, set<AMode>>> := map[];
    var new_sid_m;  // the new map binding to the dev_id

    assert(forall dev_id2 :: dev_id2 in cas.m <==> dev_id2 in sid_seq);
     
    while(i < |sid_seq|)
        invariant (forall j :: 0 <= j < i && j < |sid_seq|
                ==> sid_seq[j] in m_t)
        invariant (forall j ::  i <= j < |sid_seq|
                ==>  sid_seq[j] !in m_t)
        invariant (forall dev_id2 :: dev_id2 in m_t ==> dev_id2 in sid_seq)

        invariant (forall dev_id2 :: dev_id2 in m_t 
                ==> MapGetKeys<Object_ID, set<AMode>>(m_t[dev_id2]) == new_oids)

        invariant (forall dev_id2, o_id2 :: (dev_id2 in m_t && o_id2 in m_t[dev_id2])
                ==> (dev_id2 in cas.m && o_id2 in cas.m[dev_id2])) 
                // Corresponding to IsInCAS(cas', dev_id2, o_id2 ) ==> IsInCAS(cas, dev_id2, o_id2)
        invariant (forall dev_id2 :: dev_id2 in m_t ==> dev_id2 in cas.m)
        invariant (forall dev_id2, o_id2 :: dev_id2 in m_t && o_id2 in m_t[dev_id2]
                ==> cas.m[dev_id2][o_id2] == m_t[dev_id2][o_id2])
                // Corresponding to CASGetAModes(cas, dev_id2, o_id2) == CASGetAModes(cas', dev_id2, o_id2)

        invariant (|m_t| == i)
        invariant (i <= |sid_seq|)
    {
        var dev_id := sid_seq[i];
        var new_oid_m := MapRemoveKey<Object_ID, set<AMode>>(cas.m[dev_id], o_id);
        m_t := m_t[dev_id := new_oid_m];

        i := i + 1;
    }

    new_sid_m := m_t;

    cas' := CAS(new_sid_m, new_oids);
}

method CASDelObjs(cas:CAS, o_ids:set<Object_ID>) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires forall o_id :: o_id in o_ids ==> IsObjInCAS(cas, o_id)
        // Requirement: The objects (<o_ids>) must be present in the current CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas) - o_ids
        // Property: The new CAS only removes the objects (<o_ids>), and has the 
        // same set of subjects
    ensures forall dev_id2, o_id2 :: IsInCAS(cas', dev_id2, o_id2)
                ==> IsInCAS(cas, dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas', dev_id2, o_id2)
                ==> CASGetAModes(cas', dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)
        // Property: The current CAS includes the new CAS

    decreases |o_ids|
{
    if(|o_ids| == 0)
    {    cas' := cas;    }
    else
    {
        var o_id:| o_id in o_ids;

        var cas_step := CASDelObj(cas, o_id);
        var o_ids_step := o_ids - {o_id};

        cas' := CASDelObjs(cas_step, o_ids_step);        
    }
}


// Set the subject's permission to the object in the CAS 
method CASSetAModes(
    cas:CAS, dev_id:Dev_ID, 
    o_id:Object_ID, perm:set<AMode>
) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires IsInCAS(cas, dev_id, o_id)
        // Requirement: the subject (<dev_id>) and the object (<o_id>) are in the CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas)
        // Property: The new CAS has the same set of subjects and objects with
        // the CAS
     
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> (dev_id2 != dev_id || o_id2 != o_id 
                        ==> CASGetAModes(cas', dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)) &&
                    (dev_id2 == dev_id && o_id2 == o_id 
                        ==> CASGetAModes(cas', dev_id2, o_id2) == perm)
        // Property: Only the permission for the indicated subject-object pair
        // updates    
{
    var m_new : map<Dev_ID, map<Object_ID, set<AMode>>>  := cas.m[dev_id := cas.m[dev_id][o_id := perm]];

    cas' := CAS(m_new, cas.o_ids);
}

// Set permissions for a subject to a group of objects
method CASSetAModesObjs(
    cas:CAS, dev_id:Dev_ID, 
    o_ids:set<Object_ID>, perm:set<AMode> 
) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires forall o_id :: o_id in o_ids ==> IsInCAS(cas, dev_id, o_id)
        // Requirement: the subject (<dev_id>) and the objects (<o_ids>) are in the CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas)
        // Property: The new CAS has the same set of subjects and objects with
        // the CAS
     
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) 
                ==> (dev_id2 != dev_id || o_id2 !in o_ids
                        ==> CASGetAModes(cas', dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)) &&
                    (dev_id2 == dev_id && o_id2 in o_ids
                        ==> CASGetAModes(cas', dev_id2, o_id2) == perm)
        // Property: Only the permission for the indicated subject-object pairs
        // updates    

    decreases |o_ids|
{
    var i := 0;
    var o_ids_seq := SetToSeq<Object_ID>(o_ids);
    var cas_t := cas;

    while (i < |o_ids_seq|)
        invariant forall j :: 0 <= j < i && j < |o_ids_seq|
                ==> IsInCAS(cas_t, dev_id, o_ids_seq[j]) &&
                    CASGetAModes(cas_t, dev_id, o_ids_seq[j]) == perm
        invariant forall j ::  i <= j < |o_ids_seq|
                ==>  IsInCAS(cas_t, dev_id, o_ids_seq[j])

        invariant forall dev_id2 :: IsSubjInCAS(cas_t, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas_t.m[dev_id2]) == 
                    cas_t.o_ids
        invariant CASGetSubjs(cas_t) == CASGetSubjs(cas) 
        invariant CASGetObjs(cas_t) == CASGetObjs(cas)
        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas_t, dev_id2, o_id2)
        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> (dev_id2 != dev_id || o_id2 !in o_ids
                        ==> CASGetAModes(cas_t, dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2))
        invariant (i <= |o_ids_seq|)
    {
        var o_id := o_ids_seq[i];

        cas_t := CASSetAModes(cas_t, dev_id, o_id, perm);

        i := i + 1;
    }

    cas' := cas_t;
}

// Set permissions for a group of subjects to a group of objects
method CASSetAModesSubjsObjs(
    cas:CAS, dev_ids:set<Dev_ID>,
    o_ids:set<Object_ID>, perm:set<AMode> 
) returns (cas':CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
        // Requirement: The current CAS is an matrix
    requires (forall dev_id, o_id :: dev_id in dev_ids && o_id in o_ids
                ==> IsInCAS(cas, dev_id, o_id))
        // Requirement: the subject (<dev_id>) and the objects (<o_ids>) are in the CAS

    ensures forall dev_id2 :: IsSubjInCAS(cas', dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas'.m[dev_id2]) == 
                    cas'.o_ids
        // Property: The new CAS is an matrix
    ensures CASGetSubjs(cas') == CASGetSubjs(cas) 
    ensures CASGetObjs(cas') == CASGetObjs(cas)
        // Property: The new CAS has the same set of subjects and objects with
        // the CAS
     
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas', dev_id2, o_id2)
    ensures forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2) 
                ==> (dev_id2 !in dev_ids || o_id2 !in o_ids
                        ==> CASGetAModes(cas', dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2)) &&
                    (dev_id2 in dev_ids && o_id2 in o_ids
                        ==> CASGetAModes(cas', dev_id2, o_id2) == perm)
        // Property: Only the permission for the indicated subject-object pairs
        // updates    

    decreases |dev_ids|
{
    var i := 0;
    var dev_ids_seq := SetToSeq<Dev_ID>(dev_ids);
    var cas_t := cas;

    while (i < |dev_ids_seq|)
        invariant forall j :: 0 <= j < i && j < |dev_ids_seq|
                ==> (forall o_id :: o_id in o_ids 
                    ==> IsInCAS(cas_t, dev_ids_seq[j], o_id) &&
                        CASGetAModes(cas_t, dev_ids_seq[j], o_id) == perm)
        invariant forall j ::  i <= j < |dev_ids_seq|
                ==> (forall o_id :: o_id in o_ids
                    ==> IsInCAS(cas_t, dev_ids_seq[j], o_id))

        invariant forall dev_id2 :: IsSubjInCAS(cas_t, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas_t.m[dev_id2]) == 
                    cas_t.o_ids
        invariant CASGetSubjs(cas_t) == CASGetSubjs(cas) 
        invariant CASGetObjs(cas_t) == CASGetObjs(cas)
        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                <==> IsInCAS(cas_t, dev_id2, o_id2)
        invariant forall dev_id2, o_id2 :: IsInCAS(cas, dev_id2, o_id2)
                ==> (dev_id2 !in dev_ids || o_id2 !in o_ids
                        ==> CASGetAModes(cas_t, dev_id2, o_id2) == CASGetAModes(cas, dev_id2, o_id2))
        invariant (i <= |dev_ids_seq|)
    {
        var dev_id := dev_ids_seq[i];

        cas_t := CASSetAModesObjs(cas_t, dev_id, o_ids, perm);

        i := i + 1;
    }

    cas' := cas_t;
}

// Lemma: An entry in the CAS, iff the subject and the object is in the CAS
lemma Lemma_CASEntryInCASIffDevObjInCAS(cas:CAS, dev_id:Dev_ID, o_id:Object_ID)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
    ensures IsSubjInCAS(cas, dev_id) && IsObjInCAS(cas, o_id)
                <==> IsInCAS(cas, dev_id, o_id)
{
    assert IsInCAS(cas, dev_id, o_id) <==> dev_id in cas.m && o_id in cas.m[dev_id];
    assert dev_id in cas.m ==> (o_id in cas.m[dev_id] <==> o_id in cas.o_ids);
}

// Lemma: For all entries in the CAS, Lemma_CASEntryInCASIffSubjObjInCAS holds
lemma Lemma_CASEntriesInCASIffSubjsObjsInCAS(cas:CAS)
    requires forall dev_id2 :: IsSubjInCAS(cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(cas.m[dev_id2]) == 
                    cas.o_ids
    ensures forall dev_id, o_id :: IsSubjInCAS(cas, dev_id) && IsObjInCAS(cas, o_id)
                <==> IsInCAS(cas, dev_id, o_id)
{
    forall dev_id, o_id | IsSubjInCAS(cas, dev_id) && IsObjInCAS(cas, o_id)
        ensures IsSubjInCAS(cas, dev_id) && IsObjInCAS(cas, o_id) ==> IsInCAS(cas, dev_id, o_id)
    {
        Lemma_CASEntryInCASIffDevObjInCAS(cas, dev_id, o_id);
        assert IsInCAS(cas, dev_id, o_id);
    }

    forall dev_id, o_id | IsInCAS(cas, dev_id, o_id)
        ensures IsInCAS(cas, dev_id, o_id) ==> IsSubjInCAS(cas, dev_id) && IsObjInCAS(cas, o_id)
    {
        Lemma_CASEntryInCASIffDevObjInCAS(cas, dev_id, o_id);
        assert IsSubjInCAS(cas, dev_id) && IsObjInCAS(cas, o_id);
    }
}

// Lemma: If cas' is unchanged from cas, then cas' == cas
lemma Lemma_SameCASIfCASIsUnchanged(cas:CAS, cas':CAS)
    requires cas' == cas

    ensures CASGetSubjs(cas') == CASGetSubjs(cas)
    ensures CASGetObjs(cas') == CASGetObjs(cas)
    ensures forall dev_id, o_id :: IsInCAS(cas, dev_id, o_id) 
                ==> CASGetAModes(cas', dev_id, o_id) == CASGetAModes(cas, dev_id, o_id)
{
    assert cas'.m == cas.m;
    assert cas'.o_ids == cas.o_ids;
}