# Reading List

##### ARM 

- [arm manual](./public_html/ARM/arm_manual.pdf)
- Anton Podkopaev, et al. *Promising Compilation to ARMv8 POP* (Extended Version) ([copy](./public_html/ARM/ecoop2017-arm-full.pdf))
- Christonpher Pulte, et al. *Simplifying ARM Concurrency: Multicopy-Atomic Axiomatic and Operational Models for ARMv8* ([copy](./public_html/ARM/Simplifying-ARM-Concurrency-Multicopy-Atomic.pdf))
- Christopher Pulte, et al. *Promising-ARM/RISC-V: A Simpler and Faster Operational Concurrency Model* ([copy](./public_html/mem_model/Promising-ARM_RISC-V.pdf)) ([coq impl](https://github.com/snu-sf/promising-arm/)) ([tr](https://www.cl.cam.ac.uk/~jp622/promising-arm-riscv.pdf))

##### Machine Code Verification 

- Yu Guo, et al. *Modular Verification of Concurrent Thread Management* (Extended Version) ([copy](./public_html/Certi-Machine-Code/Module_Verification_of_Concurrent_Thread_Management.pdf))
- Ni, et al. *Using XCAP to Certify Realistic Systems Code: Machine Context Management* ([pdf](http://flint.cs.yale.edu/certikos/publications/mctxtr.pdf))

##### CompCert 

- [CASCompCert-final-version](./public_html/CompCert/CASComp.pdf)
- [CASCompCert-popl-draft](./public_html/CompCert/paper.pdf)
- [CASCompCert-original-version](./public_html/CompCert/TR-Jiang.pdf)
- [CompCert Backend](./public_html/CompCert/compcert-backend.pdf)
- [CompCert Memory Model](./public_html/CompCert/compcert-memory-model.pdf)
- [CompCertTSO](./public_html/CompCert/CompCertTSO.pdf)
- [Compositional CompCert](https://www.cs.princeton.edu/~appel/papers/compcomp.pdf)
- [CompCertM](https://sf.snu.ac.kr/compcertm/)
- [Stack-Aware Compcert](./public_html/CompCert/An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code.pdf)
- [Oracle Semantics](https://www.cs.princeton.edu/~appel/papers/concurrent.pdf) (here is a local [copy](./public_html/CompCert/Oracle-Semantics.pdf)) 

##### Other works about compiler verification

- [Crellvm:Verified Credible Compilation for LLVM](https://sf.snu.ac.kr/publications/crellvm.pdf)
- Daniel Patterson and Amal Ahmed, et al. *The Next 700 Compiler Correctness Theorems (Funtional Pearl)* ([copy](./Compiler/next700ccc.pdf))

##### Compiler Testing and Validation

- Xuejun Yang, et al. *Finding and Understanding Bugs in C Compilers* ([copy](./public_html/Compiler%20Testing%20and%20Validation/pldi11-preprint.pdf))
- Robin Morisset, et al. *Compiler Testing via a Theory of Sound Optimisations in the C11/C++11 Memory Model* ([link](https://fzn.fr/projects/wmc/readings/pldi13.pdf))
- Soham Chakraborty, et al. *Validating Optimizations of Concurrent C/C++ Programs* ([link](https://plv.mpi-sws.org/validc/paper.pdf))
- Jeehoon Kang, et al. *Crellvm: Verified Credible Compilation for LLVM* ([link](https://sf.snu.ac.kr/crellvm/))
- Nuno P. Lopes, et al. *Alive2: Bounded Translation Validation for LLVM* ([link](https://sf.snu.ac.kr/publications/alive2.pdf)) 

##### OS Kernel Verification

- Ronghui Gu, et al. *Deep Speciﬁcations and Certiﬁed Abstraction Layers* ([copy](./public_html/OSVeri/dscal-tr.pdf))
- Ronghui Gu, et al. *Certifed Concurrent Abstraction Layers* ([copy](./public_html/OSVeri/Certified_Concurrent_Abstract_Layer.pdf))
- [Preemptive OS Kernel Verification Framework](./public_html/OSVeri/framework.pdf) (here is a [book](./public_html/OSVeri/uCOS-III.pdf) introducing uCos-III)
- Hao Chen, et al. *Toward Compositional Veriﬁcation of Interruptible OS Kernels and Device Drivers* ([copy](./public_html/OSVeri/Toward_Compositional_Veriﬁcation_of_Interruptible_OS_Kernels_and_Device_Drivers.pdf))

##### C Program Verification

- [VST-Floyd](./public_html/Verify-C/VST-Floyd.pdf)
- [Concurrent Abstract Predicates](./public_html/Verify-C/CAP.pdf)
- [iCAP:Impredicative Concurrent Abstract Predicates](./public_html/Verify-C/iCAP.pdf) (PPT slides [1](./public_html/Verify-C/iCAP-slides1.pdf) [2](./public_html/Verify-C/iCAP-slides2.pdf))

##### Relaxed Memory Model

- A Course of Weak Memory Concurrency ([link](https://people.mpi-sws.org/~viktor/wmc/))
- A Course: Semantics and tools for low-level concurrent programming ([link](https://fzn.fr/teaching/lyon13/))
- Morisset's PhD thesis. *Compiler Optimisations and Relaxed Memory Consistency Models* ([link](https://fzn.fr/students/morisset-phd.pdf))
- Sung-Hwan Lee, et al. *Promising2.0: Global Optimizations in Relaxed Memory Concurrency* ([copy](./public_html/mem_model/promising2.pdf))
- Conrad Watt, et al. *Repairing and Mechanising the JavaScript Relaxed Memory Model* ([copy](./public_html/mem_model/JavaScript-Relaxed-Memory-Model-PLDI-2020.pdf)) 
- Jeehoon Kang, et al. *A Promising Semantics for Relaxed-Memory Concurrency* ([copy](./public_html/mem_model/A_Promising_Semantics_for_Relaxed-Memory_Concurrency.pdf))
- Kasper Svendsen, et al. *A Separation Logic for a Promising Semantics* ([copy](./public_html/mem_model/A_Separation_Logic_for_a_Promising_Semantics.pdf))
- Anton Podkopaev, et al. *Bridging the Gap between Programming Languages and Hardware Weak Memory Models* ([copy](./public_html/mem_model/pl_mem.pdf))
- Azalea Raad, et al. *On Library Correctness under Weak Memory Consistency* ([copy](./public_html/mem_model/Libraries-POPL-2019.pdf))
- Hans-J. Boehm, et al. *Threads Cannot be Implemented as a Library* ([copy](./public_html/mem_model/Threads_can't_be_implemented_as_a_library.pdf))
- Mark Batty, et al. *Mathematizing C++ Concurrency* ([copy](./public_html/mem_model/Mathematizing C++ Concurrency.pdf))
- [PhD thesis of Yang Zhang](./public_html/mem_model/张扬论文_v3.pdf)
- Viktor Vafeiadis, et al. *Relaxed Separation Logic: A Program Logic for C11 Concurrency* ([copy](./public_html/mem_model/Relaxed Separation Logic.pdf))
- [Taming release-acquire consistency](https://www.cs.tau.ac.il/~orilahav/papers/popl16.pdf)

##### Static Analysis for Concurrent Program

- [Static analysis by abstract interpetation of concurrent program](./Static analysis by abstract interpetation of concurrent program.pdf)
- [Static analysis of concurrent programs based on behavioral type systems](./Static analysis of concurrent programs based on behavioral type systems.pdf)

##### Machine Learning Compilation

- Tianqi Chen, et al. *TVM: An Automated End-to-End Optimizing  Compiler for Deep Learning* ([copy](./public_html/MLC/osdi18-chen.pdf))

##### Polyhedral Compilation

- Chanadan Reddy, et al. *Polyhedral Compilation for Domain Specific Languages* ([copy](./public_html/Polyhedral-Compilation/Polyhedral%20Compilation%20for%20Domain%20Specific%20Languages.pdf))
- Chris Lattner, et al. *MLIR: A Compiler Infrastructure for the End of Moore’s Law* ([copy](./public_html/Polyhedral-Compilation/MLIR-A Compiler Infrastructure for the End of Moore's Law.pdf))
- *Polyhedral Compilation as a Design Pattern for Compiler Construction* ([copy](./public_html/Polyhedral-Compilation/albert_cohen_slides.pdf))

##### Understanding of Undefined Behaviors

- Xi Wang, et al. *Towards Optimization-Safe Systems: Analyzing the Impact of Undefined Behavior* ([copy](./public_html/Undefined%20behaviors/stack_sosp13.pdf))

##### Latex

- [The Not So Short Introduction to LATEX](./public_html/Latex/lshort.pdf)
- [The Great, Big List of LATEX Symbols ](./public_html/Latex/LaTex_symbols.pdf)
- [XYMatrix](./public_html/Latex/xymatrix.pdf)
- [Strunk & White - The Elements of Style, 4th Edition](./public_html/Latex/Strunk & White - The Elements of Style, 4th Edition.pdf)

