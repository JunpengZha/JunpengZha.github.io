Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc. 

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Language.
Require Import Thread.
Require Import Configuration.
Require Import NPThread.

(** * Thread step in the non-preemptive semantics *)

(** This file define the program step in the non-preemptive semantics (in Figure 7 in paper). *)

Module NPConfiguration.
  (** ** Program configuraiton in the non-preemptive semantics *)
  (** The program configuration. It includes:
      - [cfg]: the program configuration in promising semantics 2.1
      - [preempt]: A 'switch bit' [preempt] indicate whether a switch step is allowed
        + [preempt = true]: a switch step is allowed
        + [preempt = false]: a switch step is disallowed *)
  Structure t := mk { 
    cfg: Configuration.t;
    preempt: bool;  (*True for preempt point, False for preempt disallowing *)
  }.

  (** Initialization of the program configuration in the non-preemptive semantics *)
  Definition init {lang: language} (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key) :=
    match Configuration.init fs code ctid with
    | Some c => Some (mk c true)
    | None => None
    end.

  Definition is_terminal (conf:t): Prop := Configuration.is_terminal (cfg conf).
  Definition wf (conf:t): Prop :=  Configuration.wf (cfg conf). 

  Definition consistent (c: t) (lo: Ordering.LocOrdMap): Prop := 
    Threads.consistent_nprm (Configuration.threads (cfg c)) (Configuration.sc (cfg c)) (Configuration.memory (cfg c)) lo.

  (** ** Machine level semantics *)
  (** Program transition in the non-preemptive semantics.
      - [step_tau]: current thread takes some steps;
      - [step_sw]: thread switching, which is only permitted when the 'switch bit' is true;
      - [step_thread_term]: current thread termination;
      - [step_out]: output step, generating observable event. *) 
  Inductive step: forall (e:MachineEvent.t) (lo: Ordering.LocOrdMap) (npc1 npc2:t), Prop :=
    | step_tau
      lang lo npc1 npc2 tid1 thrd_conf1 thrd_conf1' thrd_conf2 st1 st2 lc1 lc2 sc2 m2 b
      (CTID: Configuration.tid (cfg npc1) = tid1)
      (TID1: IdentMap.find tid1 (Configuration.threads (cfg npc1)) = Some (existT _ lang st1, lc1))
      (THRD1: thrd_conf1 = NPAuxThread.mk lang ((Thread.mk lang) st1 lc1 (Configuration.sc (cfg npc1)) (Configuration.memory (cfg npc1))) (preempt npc1))
      (STEPS: rtc (@NPAuxThread.tau_step lang lo) thrd_conf1 thrd_conf1')
      (STEP: NPAuxThread.tau_step lang lo thrd_conf1' thrd_conf2)
      (THRD2: thrd_conf2 = NPAuxThread.mk lang ((Thread.mk lang) st2 lc2 sc2 m2) b)
      (CONSISTENT: NPAuxThread.consistent lang ((Thread.mk lang) st2 lc2 sc2 m2) lo)
      (NPC2: npc2 = mk (Configuration.mk (IdentMap.add tid1 (existT _ _ st2, lc2) (Configuration.threads (cfg npc1)))
                                         tid1 sc2 m2) b)
      :
      step MachineEvent.silent lo npc1 npc2
    | step_sw
      lang lo npc1 npc2 tid2 st2 lc2  
      (TID2: IdentMap.find tid2 (Configuration.threads (cfg npc1)) = Some (existT _ lang st2, lc2))
      (PREEMPT: (preempt npc1) = true)
      (NPC2: npc2 = mk (Configuration.mk (Configuration.threads (cfg npc1)) tid2
                                         (Configuration.sc (cfg npc1))
                                         (Configuration.memory (cfg npc1))) true)
      :
      step MachineEvent.switch lo npc1 npc2
    | step_thread_term
      lang lo npc1 npc2 st1 lc1 st2 lc2 tid1 tid2 threads2
      (CTID: Configuration.tid (cfg npc1) = tid1)
      (OLD_TID: IdentMap.find tid1 (Configuration.threads (cfg npc1)) = Some (existT _ lang st1, lc1))
      (THRD_DONE: Thread.is_done (Thread.mk _ st1 lc1 (Configuration.sc (cfg npc1)) (Configuration.memory (cfg npc1))))
      (THRDS_REMOVE: IdentMap.remove tid1 (Configuration.threads (cfg npc1)) = threads2)
      (NEW_TID_OK: IdentMap.find tid2 (Configuration.threads (cfg npc2)) = Some (existT _ lang st2, lc2))
      (NPC2: npc2 = mk (Configuration.mk threads2 tid2
                                         (Configuration.sc (cfg npc1))
                                         (Configuration.memory (cfg npc1))) true)
      :
      step MachineEvent.switch lo npc1 npc2
    | step_out
      lang lo e npc1 npc2 st1 lc1 thrd_conf1 st2 lc2 thrd_conf2 tid1 sc2 m2
      (CTID: Configuration.tid (cfg npc1) = tid1)  
      (TID1: IdentMap.find tid1 (Configuration.threads (cfg npc1)) = Some (existT _ lang st1, lc1))
      (THRD1: thrd_conf1 = NPAuxThread.mk lang ((Thread.mk lang) st1 lc1 (Configuration.sc (cfg npc1)) (Configuration.memory (cfg npc1))) (preempt npc1))
      (STEP: NPAuxThread.out_step lang lo e thrd_conf1 thrd_conf2)
      (CONSISTENT: NPAuxThread.consistent lang (NPAuxThread.state lang thrd_conf2) lo)
      (THRD2: thrd_conf2 = NPAuxThread.mk lang ((Thread.mk lang) st2 lc2 sc2 m2) true)
      (NPC2: npc2 = mk (Configuration.mk (IdentMap.add tid1 (existT _ _ st2, lc2) (Configuration.threads (cfg npc1)))
                                         tid1 sc2 m2) true)
      :
      step (MachineEvent.syscall e) lo npc1 npc2. 

  (** ** Done configuration *)
  Definition is_done (npc: t): Prop :=
    Configuration.is_done (cfg npc).

  Definition is_abort (npc: t) (lo: Ordering.LocOrdMap): Prop := 
    exists lang st1 lc1 e e' c b,
      c = (cfg npc) /\ 
      IdentMap.find (Configuration.tid c) (Configuration.threads c) = Some (existT _ lang st1, lc1) /\
      (e = Thread.mk _ st1 lc1 (Configuration.sc c) (Configuration.memory c)) /\ 
      rtc (@NPAuxThread.tau_step _ lo)
          (NPAuxThread.mk lang e (NPConfiguration.preempt npc)) (NPAuxThread.mk lang e' b) /\ 
      Thread.is_abort e' lo.

  Inductive tau_step : Ordering.LocOrdMap -> t -> t -> Prop :=
  | tau_step_intro: forall (e: MachineEvent.t) (lo: Ordering.LocOrdMap) (npc1 npc2: t),
      step e lo npc1 npc2 -> ~(exists e0, e = MachineEvent.syscall e0) ->
      tau_step lo npc1 npc2.

  Inductive all_step : Ordering.LocOrdMap -> t -> t -> Prop :=
  | all_step_intro : forall (e: MachineEvent.t) (lo: Ordering.LocOrdMap) (npc1 npc2: t),
      step e lo npc1 npc2 -> all_step lo npc1 npc2.

  (** ** Abort configuration *)
  Inductive abort_config: forall (lo: Ordering.LocOrdMap) (npc: t), Prop :=
  | Abort_config_intro
      lo npc npc'
      (STEPS: rtc (all_step lo) npc npc')
      (ABORT: NPConfiguration.is_abort npc' lo):
      abort_config lo npc.

  (** ** Safe program *)
  (** A program is safe, if its executions on the non-preemptive semantics will
      never reach an abort configuraiton. *)
  Inductive safe {lang: language} :
    forall (lo: Ordering.LocOrdMap) (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key), Prop :=
  | Safe_intro
      lo fs code ctid
      (*(SAFE_INIT: exists npc, init fs code ctid = Some npc)*)
      (SAFE_EXEC: forall npc, init fs code ctid = Some npc -> ~(abort_config lo npc)):
      safe lo fs code ctid.

End NPConfiguration.
