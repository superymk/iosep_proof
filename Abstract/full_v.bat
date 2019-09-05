mkdir .\Result
mkdir .\Result\BuildCAS
mkdir .\Result\utils

start "./BuildCAS/BuildCAS.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./BuildCAS/BuildCAS.dfy ^> ./Result/BuildCAS/BuildCAS.txt
start "./BuildCAS/ReachableTDs.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./BuildCAS/ReachableTDs.dfy ^> ./Result/BuildCAS/ReachableTDs.txt
start "./BuildCAS/ReachableTDsStates.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./BuildCAS/ReachableTDsStates.dfy ^> ./Result/BuildCAS/ReachableTDsStates.txt
start "./BuildCAS/ReachableTDsStates_Utils.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./BuildCAS/ReachableTDsStates_Utils.dfy ^> ./Result/BuildCAS/ReachableTDsStates_Utils.txt
start "./BuildCAS/Utils_BuildCAS.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./BuildCAS/Utils_BuildCAS.dfy ^> ./Result/BuildCAS/Utils_BuildCAS.txt

start "./utils/Collections.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./utils/Collections.dfy ^> ./Result/utils/Collections.txt

start "CASOps.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 CASOps.dfy ^> ./Result/CASOps.txt
start "HCodedTD_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 HCodedTD_Ops.dfy ^> ./Result/HCodedTD_Ops.txt
start "Lemmas.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas.dfy ^> ./Result/Lemmas.txt
start "Lemmas_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops.dfy ^> ./Result/Lemmas_Ops.txt
start "Lemmas_SubjActivate_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_SubjActivate_Ops.dfy ^> ./Result/Lemmas_SubjActivate_Ops.txt
start "Lemmas_SubjActivate_ReachableTDsStates.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_SubjActivate_ReachableTDsStates.dfy ^> ./Result/Lemmas_SubjActivate_ReachableTDsStates.txt
start "Lemmas_SubjDeactivate_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_SubjDeactivate_Ops.dfy ^> ./Result/Lemmas_SubjDeactivate_Ops.txt
start "Lemmas_SubjDeactivate_ReachableTDsStates.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_SubjDeactivate_ReachableTDsStates.dfy ^> ./Result/Lemmas_SubjDeactivate_ReachableTDsStates.txt
start "Model.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:4000 Model.dfy ^> ./Result/Model.txt
start "Properties.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Properties.dfy ^> ./Result/Properties.txt
start "Properties_Corollaries.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Properties_Corollaries.dfy ^> ./Result/Properties_Corollaries.txt
start "Properties_Utils.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Properties_Utils.dfy ^> ./Result/Properties_Utils.txt
start "SecurityProperties.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 SecurityProperties.dfy ^> ./Result/SecurityProperties.txt
start "SecurityProperties_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 SecurityProperties_Ops.dfy ^> ./Result/SecurityProperties_Ops.txt
start "Syntax.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Syntax.dfy ^> ./Result/Syntax.txt
start "Utils.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Utils.dfy ^> ./Result/Utils.txt
start "Utils_SlimState.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Utils_SlimState.dfy ^> ./Result/Utils_SlimState.txt

@rem dafny /trace /stats Model.dfy


@rem dafny /trace /stats /proverMemoryLimit:2000 ./utils/Collections.dfy Syntax.dfy Axioms.dfy Utils.dfy Properties.dfy Lemmas.dfy AMOps.dfy CASOps.dfy Utils_BuildCAS.dfy BuildCAS_ReachableTDs.dfy BuildCAS_ReachableTDsStates.dfy BuildCAS.dfy 
@rem Model.dfy


