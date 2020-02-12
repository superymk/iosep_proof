/*
    The detailed model is for general I/O kernels that (1) perform I/O 
    separation between red-green partitions and green-green partitions, (2) 
    can call underlying functions to REPLACE transfers in the red partition to 
    secure ones.

    The detailed model forbids ANY TD write transfers in green partitions.

    [Note] The detailed model is also known as "concrete model" in the paper
*/

include "../Abstract/Syntax.dfy"
include "../Abstract/BuildCAS/Utils_BuildCAS.dfy"

datatype DM_State               = DM_State( // Detailed system state
                                    subjects:Subjects, objects:Objects, pids:set<Partition_ID>,

                                    red_pid:Partition_ID,
                                        // Assumption: Untrusted OS and Apps and their 
                                        // devices are in one I/O partition only.
                                        // This assumption holds, because WK does not 
                                        // enforce red-red separation
                                    devs_activatecond:map<Dev_ID, set<Dev_ID>>,
                                        // In WK, if an ephemeral device is activated into red,
                                        // then no corresponding ephemeral devices can be activated 
                                        // into green partitions, and vice versa.
                                        // Reason: A physical device can be mapped to multiple 
                                        // ephemeral devices to be activated in different partitions.
                                    ghost tds_to_all_states:map<set<TD_ID>, set<map<TD_ID, TD_Val>>>
                                  )