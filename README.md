# Formal Spec and Verification of I/O Separation Model, Interpretation for General On-Demand I/O Kernels, and Further Instantiation to Wimpy Kernel
Folders
=======================
<Abstract> - I/O Separation model, aka. abstract model
<DetailedModel> - Concrete model, aka. detailed model, 
<WK_Design> - the model of sound Wimpy Kernel design. This model uses the same state, hardware mediation mechanisms, state invariants, transition constraints, initial state definitions as the one in the detailed model. Thus, there is no syntax.dfy in this folder


Steps to Run Verification (tested on Windows only)
=======================
(1) Download Dafny 2.1.1.10209 x64 binaries from https://github.com/Microsoft/dafny/releases
(2) Instruct the OS to be able to run dafny command under any directory, e.g., by setting the PATH variable of "environment variables" in Windows.
(3) In each folder of models, execute "full_v.bat" to run the verification. The file needs to be modified on Linux/MacOS. 

Important Notes: 
(1) Run "full_v.bat" only if your machine has more than 3GB*n memory, n is the number of CPU cores (e.g., my machine has 8 cores and 24GB memory). Otherwise, use dafny to verify each file serially.

(2) Run ONLY ONE "full_v.bat" at a time. This batch command will try to utilize all CPU cores. My machine has 8 cores, and the verification takes 1-2 hour for each model on my machine.

How to Know Verification Succeed
=======================
(1) After verification is done in <Abstract>, <DetailedModel> or <WK_Design> folder, a <Result> folder is created as a subfolder under these folders.
(2) In the <Result> folder, run "grep -RsIn "errors" ." command. In each line displayed, there should be "0 errors" at the end.


