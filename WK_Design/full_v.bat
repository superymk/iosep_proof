mkdir .\Result

start "DM_AdditionalPropertiesLemmas.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 DM_AdditionalPropertiesLemmas.dfy ^> ./Result/DM_AdditionalPropertiesLemmas.txt
start "Model.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Model.dfy ^> ./Result/Model.txt

start "SecurityProperties.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 SecurityProperties.dfy ^> ./Result/SecurityProperties.txt
start "SecurityProperties_Ops.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 SecurityProperties_Ops.dfy ^> ./Result/SecurityProperties_Ops.txt

start "Utils.dfy" cmd /c dafny /trace /stats /compile:0 /timeLimit:2000 Utils.dfy ^> ./Result/Utils.txt