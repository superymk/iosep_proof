dafny /trace /stats /errorTrace:2 /compile:0 /timeLimit:60 Lemmas_Ops.dfy

@rem Method1.dfy
@rem ./BuildCAS/Utils_BuildCAS.dfy
@rem ./BuildCAS/ReachableTDs.dfy
@rem ./BuildCAS/ReachableTDsStates.dfy
@rem ./BuildCAS/ReachableTDsStates_Utils.dfy
@rem ./BuildCAS/ReachableTDsStates_Slow.dfy
@rem ./BuildCAS/BuildCAS.dfy

@rem ./BuildCAS/BuildCAS.dfy
@rem Properties_Utils.dfy Utils_SlimState.dfy
@rem Lemmas_SubjDeactivate_Ops.dfy Lemmas_SubjActivate_Ops.dfy Lemmas_Ops.dfy

@rem ./utils/Collections.dfy Syntax.dfy Model.dfy Utils.dfy Main.dfy Properties.dfy Lemmas.dfy
@rem Method1.dfy MethodTest.dfy  Utils_BuildCAS.dfy   BuildCAS.dfy BuildCAS_ReachableTDs.dfy BuildCAS_ReachableTDsStates.dfy

@rem dafny /trace /stats /proverMemoryLimit:2000 /timeLimit:60 /errorTrace:2 /out Model.exe BuildCAS2.dfy

@rem dafny /traceTimes /stats /proverMemoryLimit:2000 /timeLimit:40 /errorTrace:2 /out Model.exe BuildCAS_TDsStatesBFS.dfy