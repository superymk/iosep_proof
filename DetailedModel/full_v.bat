mkdir .\Result
mkdir .\Result\utils

start "./utils/Collections.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 ./utils/Collections.dfy ^> ./Result/utils/Collections.txt

start "HCodedTD_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 HCodedTD_Ops.dfy ^> ./Result/HCodedTD_Ops.txt
start "K_AdditionalPropertiesLemmas.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 K_AdditionalPropertiesLemmas.dfy ^> ./Result/K_AdditionalPropertiesLemmas.txt

start "Lemmas_ClosuresCombination.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_ClosuresCombination.dfy ^> ./Result/Lemmas_ClosuresCombination.txt
start "Lemmas_DevHWProt.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_DevHWProt.dfy ^> ./Result/Lemmas_DevHWProt.txt
start "Lemmas_Model_InnerFuncs.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Model_InnerFuncs.dfy ^> ./Result/Lemmas_Model_InnerFuncs.txt
start "Lemmas_Ops_Common.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops_Common.dfy ^> ./Result/Lemmas_Ops_Common.txt
start "Lemmas_Ops_GreenDrvWrite_SI1.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:4000 Lemmas_Ops_GreenDrvWrite_SI1.dfy ^> ./Result/Lemmas_Ops_GreenDrvWrite_SI1.txt
start "Lemmas_Ops_SI1_Common.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops_SI1_Common.dfy ^> ./Result/Lemmas_Ops_SI1_Common.txt

start "Lemmas_Ops_SubjObjActivate.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops_SubjObjActivate.dfy ^> ./Result/Lemmas_Ops_SubjObjActivate.txt
start "Lemmas_Ops_SubjObjDeactivate.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops_SubjObjDeactivate.dfy ^> ./Result/Lemmas_Ops_SubjObjDeactivate.txt
start "Lemmas_Ops_SubjRead.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops_SubjRead.dfy ^> ./Result/Lemmas_Ops_SubjRead.txt
start "Lemmas_Ops_SubjWrite.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_Ops_SubjWrite.dfy ^> ./Result/Lemmas_Ops_SubjWrite.txt
start "Lemmas_SecureDMState.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_SecureDMState.dfy ^> ./Result/Lemmas_SecureDMState.txt
start "Lemmas_SecureDMState_DevHWProt.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Lemmas_SecureDMState_DevHWProt.dfy ^> ./Result/Lemmas_SecureDMState_DevHWProt.txt

start "Mappings_ValidState_SecureState.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Mappings_ValidState_SecureState.dfy ^> ./Result/Mappings_ValidState_SecureState.txt
start "Model.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Model.dfy ^> ./Result/Model.txt
start "Model_InnerFuncs.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Model_InnerFuncs.dfy ^> ./Result/Model_InnerFuncs.txt
start "Model_Ops_Predicates.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Model_Ops_Predicates.dfy ^> ./Result/Model_Ops_Predicates.txt

start "Properties_DevHWProt.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Properties_DevHWProt.dfy ^> ./Result/Properties_DevHWProt.txt
start "Properties_SecureDMState.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Properties_SecureDMState.dfy ^> ./Result/Properties_SecureDMState.txt
start "Properties_ValidDMState.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Properties_ValidDMState.dfy ^> ./Result/Properties_ValidDMState.txt

start "SecurityProperties.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 SecurityProperties.dfy ^> ./Result/SecurityProperties.txt
start "SecurityProperties_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 SecurityProperties_Ops.dfy ^> ./Result/SecurityProperties_Ops.txt
start "Syntax.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Syntax.dfy ^> ./Result/Syntax.txt

start "Util_Lemmas.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Util_Lemmas.dfy ^> ./Result/Util_Lemmas.txt
start "Utils.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Utils.dfy ^> ./Result/Utils.txt
start "Utils_DevsActivateCond.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Utils_DevsActivateCond.dfy ^> ./Result/Utils_DevsActivateCond.txt