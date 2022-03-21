Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Language.

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.

(** * The program step in promising semantics 2.1 *)

(** This file defines the program steps (machine steps) in promising semantics 2.1. *)
(** The program steps in PS2.1 defined in this file corresponds to
    the definitions in Figure 6 in our paper. *)

Module Threads.
  (** ** Thread pool: a set of threads  *)
  (** It corresponds to (ThrdPool) defined in Figure 5 in paper. *)
  Definition t := IdentMap.t ({lang:language & (Language.state lang)} * Local.t).

  (** Add new threads in the thread pool (for initialization). *)
  Definition add_th {lang: language}
             (ths:t) (tid:IdentMap.key) (f: Language.fid) (code: Language.syntax lang) : option t :=
    match ((Language.init lang) code f) with
    | Some s => Some (IdentMap.add tid (existT _ _ s, Local.init) ths)
    | _ => None
    end.
  
  Definition tid_incr := POrderedType.Positive_as_DT.succ.
  Fixpoint add_ths {lang: language}
           (ths: t) (tid: IdentMap.key) (fs: list Language.fid) (code: Language.syntax lang) : option t :=
    match fs with
    | f::fs' => match add_ths ths (tid_incr tid) fs' code with
               | Some ths' => add_th ths' tid f code
               | _ => None
               end
    | _ => Some ths
    end. 

  Definition empty_ths := IdentMap.empty ({lang:language & (Language.state lang)} * Local.t).

  Definition init {lang: language} (fs: list Language.fid) (code: Language.syntax lang) :=
    add_ths empty_ths BinNums.xH fs code.

  Definition is_terminal (ths:t): Prop :=
    forall tid lang st lc (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      <<STATE: (Language.is_terminal lang) st>> /\
      <<THREAD: Local.is_terminal lc>>.

  Inductive wf (ths:t) (mem:Memory.t): Prop :=
  | wf_intro
      (DISJOINT:
         forall tid1 lang1 st1 lc1
           tid2 lang2 st2 lc2
           (TID: tid1 <> tid2)
           (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
           (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2)),
           Local.disjoint lc1 lc2)
      (THREADS: forall tid lang st lc
                  (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
          Local.wf lc mem)
  .

  Definition consistent (ths:t) (sc:TimeMap.t) (mem:Memory.t) (lo: Ordering.LocOrdMap): Prop :=
    forall tid lang st lc
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      Thread.consistent (Thread.mk lang st lc sc mem) lo.

  Definition consistent_nprm (ths:t) (sc:TimeMap.t) (mem:Memory.t) (lo: Ordering.LocOrdMap): Prop :=
    forall tid lang st lc
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      Thread.consistent_nprm (Thread.mk lang st lc sc mem) lo.


  Inductive is_promised tid (loc:Loc.t) (to:Time.t) (threads:t): Prop :=
  | is_promised_intro
      lang st lc from msg
      (TID: IdentMap.find tid threads = Some (existT _ lang st, lc))
      (PROMISES: Memory.get loc to (Local.promises lc) = Some (from, msg))
  .


  (* tids *)

  Definition tids (ths: t): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements ths).
End Threads.


Module Configuration.
  (** ** Program configuration *)
  (** The program configuration in promising semantics 2.1. It includes:
      - [threads]: thread pool;
      - [tid]: the identifier of the current thread;
      - [sc]: the timemap for SC fence;
      - [memory]: memory shared by all threads;

      It corresponds to (World) defined in Figure 5 in paper. *)
  Structure t := mk { 
    threads: Threads.t;
    tid: IdentMap.key;
    sc: TimeMap.t;
    memory: Memory.t;
  }.

  (** ** Initialization of the program in promising semantics 2.1. *)
  (** The program initialization is shown as the (init)-rule in Figure 6 in paper. *)
  Definition init {lang: language} (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key) :=
    match (Threads.init fs code) with
    | Some ths => Some (mk ths ctid TimeMap.bot Memory.init)
    | _ => None
    end.

  Definition is_terminal (conf:t): Prop := Threads.is_terminal (threads conf).

  Inductive wf (conf:t): Prop :=
  | wf_intro
      (WF: Threads.wf (threads conf) (memory conf))
      (SC: Memory.closed_timemap (sc conf) (memory conf))
      (MEM: Memory.closed (memory conf))
  .

  Definition sw_tid (c1: t) (new_tid: IdentMap.key): t := mk (threads c1) new_tid (sc c1) (memory c1).
  Lemma tid_eq_dec: forall (tid1 tid2: IdentMap.key),
      {tid1 = tid2} + {tid1 <> tid2}.
  Proof. eapply IdentSet.Raw.L.MO.eq_dec; eauto. Qed.

  Lemma sw_to_self
        c:
    c = sw_tid c (tid c).
  Proof.
    destruct c; ss.
  Qed.

  Lemma sw_tid_twice
        c tid1 tid2:
    Configuration.sw_tid (Configuration.sw_tid c tid1) tid2 =
    Configuration.sw_tid c tid2.
  Proof.
    destruct c; ss.
  Qed.
    
  Definition consistent (lo: Ordering.LocOrdMap) (c: t): Prop :=
    Threads.consistent (threads c) (sc c) (memory c) lo.

  Definition no_promise (c: t): Prop :=
    forall tid lang st lc (FIND: IdentMap.find tid (threads c) = Some (existT _ lang st, lc)),
      (Local.promises lc) = Memory.bot.

  (** ** Program step *)
  (** Program step (or machine step) in promising semantics 2.1.
      It takes four parameters:
      - [e]: machine event;
      - [lo]: a set of atomic locations;
      - [c1] and [c2]: program configurations before and after transition *)
  Inductive step: forall (e:MachineEvent.t) (lo: Ordering.LocOrdMap) (c1 c2:t), Prop :=
  | step_tau
      lang lo c1 c2 st1 st2 lc1 lc2 e1 tid1
      (CTID: tid c1 = tid1)
      (TID1: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _ lo) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e1)
      (STEP: Thread.tau_step lo e1 (Thread.mk _ st2 lc2 (sc c2) (memory c2)))
      (** The execution of current thread must reach a promise certified state. *)
      (CONSISTENT: Thread.consistent (Thread.mk _ st2 lc2 (sc c2) (memory c2)) lo)
      (C2: c2 = mk (IdentMap.add tid1 (existT _ _ st2, lc2) (threads c1)) tid1 (sc c2) (memory c2)):
      step MachineEvent.silent lo c1 c2
  | step_out
      lang lo c1 c2 st1 st2 lc1 lc2 e1 e tid1
      (CTID: tid c1 = tid1)
      (TID1: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _ lo) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e1)
      (STEP_OUT: Thread.out_step lo e e1 (Thread.mk _ st2 lc2 (sc c2) (memory c2)))
      (CONSISTENT: Thread.consistent (Thread.mk _ st2 lc2 (sc c2) (memory c2)) lo)
      (C2: c2 = mk (IdentMap.add tid1 (existT _ _ st2, lc2) (threads c1)) tid1 (sc c2) (memory c2)):
      step (MachineEvent.syscall e) lo c1 c2
  | step_sw 
      tid' lang c1 c2 st2 lc2 lo 
      (TID2_OK: IdentMap.find tid' (threads c1) = Some (existT _ lang st2, lc2))
      (C2: c2 = Configuration.mk (threads c1) tid' (sc c1) (memory c1)):
      step MachineEvent.switch lo c1 c2
  | step_thread_term
      lang c1 c2 st1 lc1 st2 lc2 lo tid1 tid'
      (CTID: tid c1 = tid1)
      (OLD_TID: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
      (THRD_DONE: Thread.is_done (Thread.mk _ st1 lc1 (sc c1) (memory c1)))
      (THRDS_REMOVE: ((IdentMap.remove tid1 (threads c1)) = (threads c2)))
      (NEW_TID_OK: IdentMap.find tid' (threads c2) = Some (existT _ lang st2, lc2))
      (C2: c2 = mk (threads c2) tid' (sc c1) (memory c1)):
      step MachineEvent.switch lo c1 c2
  .
  Hint Constructors step.

  (** ** Done configuration *)
  (** All of threads terminate. *)
  Definition is_done (c: t): Prop :=
    exists lang st lc,
      (IdentMap.find (tid c) (threads c) = Some (existT _ lang st, lc)) /\
      Thread.is_done (Thread.mk _ st lc (sc c) (memory c)) /\ 
      IdentMap.is_empty (IdentMap.remove (tid c) (threads c)) = true.

  Definition is_abort (c: t) (lo: Ordering.LocOrdMap): Prop := 
      exists lang st1 lc1  e', 
        IdentMap.find (tid c) (threads c) = Some (existT _ lang st1, lc1) /\ 
        rtc (@Thread.tau_step _ lo) (Thread.mk _ st1 lc1 (sc c) (memory c)) e' /\ 
        Thread.is_abort e' lo. 

  Inductive tau_step: Ordering.LocOrdMap -> t -> t -> Prop :=
  | tau_step_intro
      e lo c1 c2
      (WP_STEP: step e lo c1 c2)
      (TAU: ~(exists e0, e = MachineEvent.syscall e0)):
      tau_step lo c1 c2.

  Inductive all_step: Ordering.LocOrdMap -> t -> t -> Prop :=
  | all_step_intro
      e lo c1 c2
      (WP_STEP: step e lo c1 c2):
      all_step lo c1 c2.

  (** ** Abort configuration *)
  Inductive abort_config: forall (lo: Ordering.LocOrdMap) (c: t), Prop :=
  | Abort_config_intro
      lo c c'
      (STEPS: rtc (all_step lo) c c')
      (ABORT: is_abort c' lo):
      abort_config lo c.

  (** ** Safe program *)
  (** A program is safe, if its executions will never reach an abort configuration *)
  Inductive safe {lang: language} :
    forall (lo: Ordering.LocOrdMap) (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key), Prop :=
  | Safe_intro
      lo fs code ctid
      (*(SAFE_INIT: exists c, init fs code ctid = Some c)*)
      (SAFR_EXEC: forall c, init fs code ctid = Some c -> ~(abort_config lo c)):
      safe lo fs code ctid.
  
  (** Aux promising semantics (machine step). 
      1. same init/term/sw/done/abort rule, done/abort definition
      2. we have na/prc/atm step now (substitute for single tau step) 
    *)
  Inductive aux_step: forall (e:AuxEvent.t) (lo: Ordering.LocOrdMap) (c1 c2:t), Prop :=
  | aux_step_na
    lang lo c1 c2 st1 st2 lc1 lc2 e1 tid1
    (CTID: tid c1 = tid1)
    (TID1: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.na_step _ lo) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e1)
    (STEP: Thread.na_step lo e1 (Thread.mk _ st2 lc2 (sc c2) (memory c2)))
    (CONSISTENT: Thread.consistent (Thread.mk _ st2 lc2 (sc c2) (memory c2)) lo)
    (C2: c2 = mk (IdentMap.add tid1 (existT _ _ st2, lc2) (threads c1)) tid1 (sc c2) (memory c2)):
    aux_step AuxEvent.na lo c1 c2
  | aux_step_prc 
    lang lo c1 c2 st1 st2 lc1 lc2 e1 tid1
    (CTID: tid c1 = tid1)
    (TID1: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.prc_step _ lo) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e1)
    (STEP: Thread.prc_step lo e1 (Thread.mk _ st2 lc2 (sc c2) (memory c2)))
    (CONSISTENT: Thread.consistent (Thread.mk _ st2 lc2 (sc c2) (memory c2)) lo)
    (C2: c2 = mk (IdentMap.add tid1 (existT _ _ st2, lc2) (threads c1)) tid1 (sc c2) (memory c2)):
    aux_step AuxEvent.prc lo c1 c2
  | aux_step_at
    lang lo c1 c2 st1 st2 lc1 lc2 e1 e1' tid1
    (CTID: tid c1 = tid1)
    (TID1: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
    (STEPS_PRC: rtc (@Thread.prc_step _ lo) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e1)
    (STEPS_ATM: rtc (@Thread.atmblk_step _ lo) e1 e1')
    (STEP_ATM: Thread.atmblk_step lo e1' (Thread.mk _ st2 lc2 (sc c2) (memory c2)))
    (CONSISTENT: Thread.consistent (Thread.mk _ st2 lc2 (sc c2) (memory c2)) lo)
    (C2: c2 = mk (IdentMap.add tid1 (existT _ _ st2, lc2) (threads c1)) tid1 (sc c2) (memory c2)):
    aux_step AuxEvent.atm lo c1 c2
  | aux_step_out
    lang lo c1 c2 st1 st2 lc1 lc2 e1 e tid1
    (CTID: tid c1 = tid1)
    (TID1: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.na_step _ lo) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e1)
    (STEP_OUT: Thread.out_step lo e e1 (Thread.mk _ st2 lc2 (sc c2) (memory c2)))
    (CONSISTENT: Thread.consistent (Thread.mk _ st2 lc2 (sc c2) (memory c2)) lo)
    (C2: c2 = mk (IdentMap.add tid1 (existT _ _ st2, lc2) (threads c1)) tid1 (sc c2) (memory c2)):
    aux_step (AuxEvent.out e) lo c1 c2
  | aux_step_sw 
      tid' lang c1 c2 st2 lc2 lo 
      (TID2_OK: IdentMap.find tid' (threads c1) = Some (existT _ lang st2, lc2))
      (C2: c2 = Configuration.mk (threads c1) tid' (sc c1) (memory c1)):
      aux_step AuxEvent.sw lo c1 c2
  | aux_step_thread_term
      lang c1 c2 st1 lc1 st2 lc2 lo tid1 tid'
      (CTID: tid c1 = tid1)
      (OLD_TID: IdentMap.find tid1 (threads c1) = Some (existT _ lang st1, lc1))
      (THRD_DONE: Thread.is_done (Thread.mk _ st1 lc1 (sc c1) (memory c1)))
      (THRDS_REMOVE: ((IdentMap.remove tid1 (threads c1)) = (threads c2)))
      (NEW_TID_OK: IdentMap.find tid' (threads c2) = Some (existT _ lang st2, lc2))
      (C2: c2 = mk (threads c2) tid' (sc c1) (memory c1)):
      aux_step AuxEvent.tterm lo c1 c2
  .
  Hint Constructors aux_step.

  Inductive aux_tau_step: Ordering.LocOrdMap -> t -> t -> Prop :=
  | aux_tau_step_intro
      e lo c1 c2
      (WP_STEP: aux_step e lo c1 c2)
      (TAU: ~(exists e0, e =  AuxEvent.out e0)):
    aux_tau_step lo c1 c2.

  Inductive aux_all_step: Ordering.LocOrdMap -> t -> t -> Prop :=
  | aux_all_step_intro
      e lo c1 c2
      (WP_STEP: aux_step e lo c1 c2):
    aux_all_step lo c1 c2.
    
End Configuration.


