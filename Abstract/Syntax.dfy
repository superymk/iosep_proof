/*
    [Note] The abstract model is also known as "I/O separation model" in the paper
*/

//******** Syntax  ********//
datatype Subject_ID          = Subject_ID(nat)
                                // ID of each subject
datatype Object_ID           = Object_ID(nat)
                                // ID of each object
datatype Partition_ID        = NULL | Partition_ID(pid:nat)

datatype TD_ID               = TD_ID(oid:Object_ID)
                                // ID of each Transfer Descriptor (TD).
                                // TD_ID is a restricted use of Object_ID
datatype FD_ID               = FD_ID(oid:Object_ID)
                                // ID of each Function Descriptor (FD).
                                // FD_ID is a restricted use of Object_ID
datatype DO_ID               = DO_ID(oid:Object_ID)
                                // ID of each Data Object (DO).
                                // DO_ID is a restricted use of Object_ID

datatype Drv_ID              = Drv_ID(sid:Subject_ID)        
                                // ID of each driver.
                                // Drv_ID is a restricted use of Subject_ID
datatype Dev_ID              = Dev_ID(sid:Subject_ID)
                                // ID of each device.
                                // Dev_ID is a restricted use of Subject_ID

datatype AMode               = R | W            
                                // Access modes, and permissions of I/O accesses

datatype TD_Trans_Param      = TD_Trans_Param(amodes:set<AMode>, 
                                vals:set<TD_Val>)    // Parameter of transfers to a TD 
datatype FD_Trans_Param      = FD_Trans_Param(amodes:set<AMode>, 
                                vals:set<FD_Val>)    // Parameter of transfers to a FD
datatype DO_Trans_Param      = DO_Trans_Param(amodes:set<AMode>, 
                                vals:set<DO_Val>)    // Parameter of transfers to a DO

datatype TD_Val              = TD_Val(trans_params_tds:map<TD_ID, TD_Trans_Param>,
                                        trans_params_fds:map<FD_ID, FD_Trans_Param>,
                                        trans_params_dos:map<DO_ID, DO_Trans_Param>) 
datatype FD_Val              = FD_Val(string)
datatype DO_Val              = DO_Val(string)

datatype TD_State            = TD_State(pid:Partition_ID, val:TD_Val) 
                                // State of Transfer Descriptor (TD)
datatype FD_State            = FD_State(pid:Partition_ID, val:FD_Val)
                                // State of Function Descriptor (FD)
datatype DO_State            = DO_State(pid:Partition_ID, val:DO_Val)
                                // State of Data Object (DO)


datatype Drv_State           = Drv_State(pid:Partition_ID, td_ids:set<TD_ID>, 
                                fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
                                // Driver state
datatype Dev_State           = Dev_State(pid:Partition_ID, 
                                hcoded_td_id:TD_ID,
                                    // Hardcoded TD
                                td_ids:set<TD_ID>, fd_ids:set<FD_ID>,
                                do_ids:set<DO_ID>)
                                // Device state

datatype Subjects            = Subjects(drvs:map<Drv_ID, Drv_State>, 
                                devs:map<Dev_ID, Dev_State>)
                                // Subjects include all drivers and devices
datatype Objects             = Objects(tds:map<TD_ID, TD_State>,
                                fds:map<FD_ID, FD_State>,
                                dos:map<DO_ID, DO_State>)
                                // Objects include all TDs, FDs, and DOs
    
datatype State               = State(subjects:Subjects, objects:Objects, pids:set<Partition_ID>,
                                     // Helper info to ease the proof
                                     ghost tds_to_all_states:map<set<TD_ID>, set<map<TD_ID, TD_Val>>>
                                     // The combination of values of any set of TDs is a finite set
                                    )