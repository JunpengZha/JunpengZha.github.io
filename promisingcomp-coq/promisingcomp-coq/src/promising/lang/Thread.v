Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.

Set Implicit Arguments.

(** * Thread steps in promising semantics 2.1 *)

(** This file defines the thread transitions in promising semantics 2.1 (PS2.1). *)
(** It corresponds to the thread transitions in figure 6 in our paper *)
Inductive tau T
          (step: forall (lo: Ordering.LocOrdMap) 
                        (e:ThreadEvent.t) (e1 e2:T), Prop) (lo: Ordering.LocOrdMap) (e1 e2:T) : Prop :=
| tau_intro
    e
    (TSTEP: step lo e e1 e2)
    (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
.

Hint Constructors tau.

Inductive union E T (step: forall (lo: Ordering.LocOrdMap) (e:E) (e1 e2:T), Prop) (lo: Ordering.LocOrdMap)
          (e1 e2:T): Prop :=
| union_intro
    e
    (USTEP: step lo e e1 e2)
.
Hint Constructors union.


Module Thread.
  Section Thread.
    Variable (lang:language).

    (** ** Thread state *)
    (** The thread state contains:
        - [state]: thread-local state;
        - [local]: thread view and thread promise set;
        - [sc]: timemap for SC fence;
        - [memory]: memory in PS2.1 *)
    Structure t := mk {
      state: (Language.state lang);
      local: Local.t;
      sc: TimeMap.t;
      memory: Memory.t;
    }.

    (** ** Thread promise step *)
    (** It includes promise insert/lower/split, reservation and cancel step.
        The pf label marks whether such step is a promise-free step.
        For cancel step, pf = true. *)
    Inductive promise_step: forall (pf: bool) (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | promise_step_intro
        st lc1 sc1 mem1
        loc from to msg kind
        lc2 mem2 pf
        (LOCAL: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (PF: pf = orb (andb (Memory.op_kind_is_lower_concrete kind) (Message.is_released_none msg))
                      (Memory.op_kind_is_cancel kind))
        :
        promise_step pf (ThreadEvent.promise loc from to msg kind) (mk st lc1 sc1 mem1) (mk st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like a SC fence. *)
    (** ** Thread program step *)
    (**  thread-local state transition +
         transistion on (thread-view, promises, timemap for SC fence, memory)  *)
    Inductive program_step (e:ThreadEvent.t) (lo: Ordering.LocOrdMap): forall (e1 e2:t), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2) 
        (LOCAL: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2 lo):
        program_step e lo (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem2)
    .
    Hint Constructors program_step.

    (** ** Thread step (thread transition) *)
    (** Thread step in promising semantics contains two types of steps:
        - [step_promise]: promise step;
        - [step_program]: program step that executes the instruction *)
    Inductive step: forall (lo: Ordering.LocOrdMap) (pf: bool) (e:ThreadEvent.t) (e1 e2:t) , Prop :=
    | step_promise
        e e1 e2 lo pf
        (STEP: promise_step pf e e1 e2):
        step lo pf e e1 e2
    | step_program
        e e1 e2 lo
        (STEP: program_step e lo e1 e2):
        step lo true e e1 e2
    .
    Hint Constructors step.

    Inductive step_allpf (lo: Ordering.LocOrdMap) (e:ThreadEvent.t) (e1 e2:t) : Prop :=
    | step_nopf_intro
        pf (STEP: step lo pf e e1 e2)
    .
    Hint Constructors step_allpf.

    Definition tau_step (lo: Ordering.LocOrdMap):= tau step_allpf lo.
    Hint Unfold tau_step.

    Definition all_step (lo:Ordering.LocOrdMap) := union step_allpf lo.
    Hint Unfold all_step.

    Inductive opt_step: forall (lo: Ordering.LocOrdMap) (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_none
        e lo:
        opt_step lo ThreadEvent.silent e e
    | step_some
        pf e e1 e2 lo
        (STEP: step lo pf e e1 e2):
        opt_step lo e e1 e2
    .
    Hint Constructors opt_step.

    Inductive opt_promise_step: forall (lo: Ordering.LocOrdMap) (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | opt_promise_step_none
        lo e1:
        opt_promise_step lo ThreadEvent.silent e1 e1
    | opt_promise_step_some
        pf lo e e1 e2
        (STEP: promise_step pf e e1 e2):
        opt_promise_step lo e e1 e2
    . 

    Inductive opt_program_step: forall (lo: Ordering.LocOrdMap) (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | opt_program_step_none
        lo e1:
        opt_program_step lo ThreadEvent.silent e1 e1
    | opt_program_step_some
        lo e e1 e2
        (STEP: program_step e lo e1 e2):
        opt_program_step lo e e1 e2
    .

    Lemma tau_opt_tau
          e1 e2 e3 e lo
          (STEPS: rtc (tau_step lo) e1 e2)
          (STEP: opt_step lo e e2 e3)
          (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
      rtc (tau_step lo) e1 e3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto.
    Qed.

    Lemma tau_opt_all
          e1 e2 e3 e lo
          (STEPS: rtc (tau_step lo) e1 e2)
          (STEP: opt_step lo e e2 e3):
      rtc (all_step lo) e1 e3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto. i.
        econs 2; eauto.
        inv H. inv TSTEP. econs. econs. eauto.
    Qed.
    
    (** ** Consistency *)
    (** A thread state is consistent if the thread is able to fulfill
        all its promises when executed in isolation. *)
    Definition consistent (e:t) (lo: Ordering.LocOrdMap): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap (memory e) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        exists e2,
          <<STEPS: rtc (tau_step lo) (mk (state e) (local e) sc1 mem1) e2>> /\
          <<PROMISES: (Local.promises (local e2)) = Memory.bot>>. 

    (* step_future *)
    Lemma promise_step_future
          pf e e1 e2 
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP. ss.
      exploit Local.promise_step_future; eauto. i. des.
      splits; eauto. 2: refl.
      eapply Memory.future_closed_timemap; eauto.
    Qed.

    Lemma program_step_future
          lo e e1 e2
          (STEP: program_step lo e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_future; eauto.
    Qed.

    Lemma step_future
          lo pf e e1 e2
          (STEP: step lo pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma opt_step_future
          lo e e1 e2
          (STEP: opt_step lo e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2 lo
          (STEP: rtc (all_step lo) e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - i. inv H. inv USTEP.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          e1 e2 lo
          (STEP: rtc (tau_step lo) e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      eapply rtc_all_step_future; eauto.
      eapply rtc_implies; [|eauto].
      intros.
      inv H; econstructor; eauto.
    Qed.

    (* step_inhabited *)
    Lemma promise_step_inhabited
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (INHABITED1: Memory.inhabited (memory e1)):
      <<INHABITED2: Memory.inhabited (memory e2)>>.
    Proof.
      inv STEP. ss.
      eapply Local.promise_step_inhabited; eauto.
    Qed.

    Lemma program_step_inhabited
          lo e e1 e2
          (STEP: program_step lo e e1 e2)
          (INHABITED1: Memory.inhabited (memory e1)):
      <<INHABITED2: Memory.inhabited (memory e2)>>.
    Proof.
      inv STEP. ss.
      eapply Local.program_step_inhabited; eauto.
    Qed.

    Lemma step_inhabited
          pf lo e e1 e2
          (STEP: step lo pf e e1 e2)
          (INHABITED1: Memory.inhabited (memory e1)):
      <<INHABITED2: Memory.inhabited (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_inhabited; eauto.
      - eapply program_step_inhabited; eauto.
    Qed.

    Inductive reserve_step (lo: Ordering.LocOrdMap) (e1 e2:t) : Prop :=
    | reserve_step_intro
        loc pf from to
        (STEP: promise_step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) e1 e2)
    .
    Hint Constructors reserve_step.

    Inductive cancel_step (lo: Ordering.LocOrdMap) (e1 e2:t): Prop :=
    | cancel_step_intro
        loc pf from to
        (STEP: promise_step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) e1 e2)
    .
    Hint Constructors cancel_step.

    (*AuxStep:
      1. na (plain) 
      2. PRC: promise (write/split/lowering), reserve, cancel
      3. atmBlk
      4. out(v)
     *)
    (** ** Non-atomic step *)
    (** It corresponds to (NA) in Figure 7 in paper and includes:
        + non-atomic memory read;
        + non-atomic memory write;
        + silent step that does not do memory accesses. *)
    Inductive na_step (lo: Ordering.LocOrdMap) (e1 e2:t) : Prop := 
    | na_plain_read_step_intro
      loc ts v R
      (STEP: program_step (ThreadEvent.read loc ts v R Ordering.plain) lo e1 e2)
    | na_plain_write_step_intro
      loc from to v R
      (STEP: program_step (ThreadEvent.write loc from to v R Ordering.plain) lo e1 e2)
    | na_tau_step_intro 
      (STEP: program_step ThreadEvent.silent lo e1 e2)
    .

    (* set of locations written *)
    Definition WriteLoc := IdentSet.t.
    Definition wloc_empty : WriteLoc := IdentSet.empty.

    Lemma wloc_union_empty:
      IdentSet.union IdentSet.empty IdentSet.empty = IdentSet.empty.
    Proof.
      eapply IdentSet.Self.eq_leibniz. ii. split; ii.
      - eapply IdentSet.union_spec in H. des; eauto.
      - eapply IdentSet.union_spec. eauto.
    Qed.

    (* na step with location written *)
    Inductive na_step_wloc: forall (lo: Ordering.LocOrdMap) (wloc: WriteLoc) (e1 e2: t), Prop :=
    | na_read_step_wloc_intro
        lo e1 e2 loc ts v R
        (STEP: program_step (ThreadEvent.read loc ts v R Ordering.plain) lo e1 e2):
        na_step_wloc lo IdentSet.empty e1 e2
    | na_write_step_wloc_intro
        lo e1 e2 loc from to v R
        (STEP: program_step (ThreadEvent.write loc from to v R Ordering.plain) lo e1 e2): 
        na_step_wloc lo (IdentSet.singleton loc) e1 e2
    | na_tau_step_wloc_intro
        lo e1 e2
        (STEP: program_step ThreadEvent.silent lo e1 e2):
        na_step_wloc lo IdentSet.empty e1 e2.

    (* na steps with locations writen *) 
    Inductive na_steps_wloc: forall (lo: Ordering.LocOrdMap) (wloc: WriteLoc) (e1 e2: t), Prop :=
    | nil_na_steps_wloc
        lo e:
        na_steps_wloc lo IdentSet.empty e e
    | plus_na_steps_wloc
        lo  e1 e2 e3 wloc1 wloc2
        (STEP: na_step_wloc lo wloc1 e1 e2)
        (STEPS: na_steps_wloc lo wloc2 e2 e3):
        na_steps_wloc lo (IdentSet.union wloc1 wloc2) e1 e3.

    (** ** PRC step *)
    (** It corresponds to (PRC) in Figure 7 in paper.
        In Coq formalization, the promise, reservation and cancel steps are
        all called [promise_step]. *)
    Inductive prc_step (lo: Ordering.LocOrdMap) (e1 e2: t): Prop :=
    | prc_step_intro
        pf loc from to msg kind
        (PRC: promise_step pf (ThreadEvent.promise loc from to msg kind) e1 e2).
  
    Inductive out_step (lo: Ordering.LocOrdMap) (e: Event.t) (e1 e2: t): Prop :=
    | out_step_intro
      e 
      (OUT: program_step (ThreadEvent.syscall e) lo e1 e2)
    . 

    Inductive at_read_step (lo: Ordering.LocOrdMap) (e1 e2: t) : Prop :=
    | at_read_step_intro
        loc ts v R o
        (STEP: program_step (ThreadEvent.read loc ts v R o) lo e1 e2)
        (AT: Ordering.le Ordering.relaxed o).

    Inductive at_write_step (lo: Ordering.LocOrdMap) (e1 e2: t) : Prop :=
    | at_write_step_intro
       loc from to v R o
       (STEP: program_step (ThreadEvent.write loc from to v R o) lo e1 e2)
       (AT: Ordering.le Ordering.relaxed o).

    Inductive rmw_step (lo: Ordering.LocOrdMap) (e1 e2: t) : Prop :=
    | rmw_step_intro
        loc from to v1 v2 R1 R2 o1 o2
        (STEP: program_step (ThreadEvent.update loc from to v1 v2 R1 R2 o1 o2) lo e1 e2).

    Inductive fence_step (lo: Ordering.LocOrdMap) (e1 e2: t) : Prop :=
    | fence_step_intro
        o1 o2
        (STEP: program_step (ThreadEvent.fence o1 o2) lo e1 e2).

    (** ** Atomic step *)
    (** It corresponds to (AT) in Figure 7 in paper. *)
    Inductive at_step (lo: Ordering.LocOrdMap) (e1 e2:t) : Prop := 
    | at_step_intro
        (AT_STEP: at_read_step lo e1 e2 \/ at_write_step lo e1 e2 \/
                  rmw_step lo e1 e2 \/ fence_step lo e1 e2).

    Inductive pf_promise_step (e1 e2: t): Prop :=
    | pf_promise_step_intro
        e
        (PF_STEP: promise_step true e e1 e2).

    Definition atmblk_step (lo: Ordering.LocOrdMap) (e1 e2: t): Prop :=
      exists e' e'', 
      <<NA_STEPS: rtc (@na_step lo) e1 e'>> /\ 
      <<AT_STEP: at_step lo e' e''>> /\
      <<PRC_STEPS: rtc (@prc_step lo) e'' e2>>.


    (** ** Thread done *)
    (** A thread is done, iff. terminal + promise empty *)
    Definition is_done (e:t) : Prop :=
      <<TERMINAL: Language.is_terminal lang (state e)>> /\
      <<PROMISES: (Local.promises (local e)) = Memory.bot>>.

    (** ** Thread abort *)
    (** A thread abort, iff. the next thread-local state does not exist,
        or accessing the atomic location via non-atomic memory accesses,
        or accessing the non-atomic location via atomic memory accesses *)
    Definition is_abort (e1 :t) (lo: Ordering.LocOrdMap): Prop :=
      <<PROMISES: Local.promise_consistent (local e1)>> /\
      <<ABORT: ~((exists e st2, (Language.step lang) e (state e1) st2) \/ (is_done e1)) \/
               (exists st2 x o v, ((Language.step lang) (ProgramEvent.read x v o) (state e1) st2 
                     \/ (Language.step lang) (ProgramEvent.write x v o) (state e1) st2) 
                            /\ ~ Ordering.mem_ord_match o (lo x)) \/
                            (exists st2 x vr vw or ow, (Language.step lang) (ProgramEvent.update x vr vw or ow) (state e1) st2 /\ lo x = Ordering.nonatomic)>>.

    Inductive nprm_step (lo: Ordering.LocOrdMap) (e1 e2: t): Prop :=
    | nprm_step_program_step
        e
        (PROG: program_step e lo e1 e2)
        (TAU: ThreadEvent.get_machine_event e = MachineEvent.silent)
    | nprm_step_pf_step
        e
        (PF: promise_step true e e1 e2).

    Definition consistent_nprm (e:t) (lo: Ordering.LocOrdMap): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap (memory e) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        exists e2,
          <<STEPS: rtc (nprm_step lo) (mk (state e) (local e) sc1 mem1) e2>> /\
                   <<PROMISES: (Local.promises (local e2)) = Memory.bot>>.
    Definition not_rsv_ccl_scfence (e: ThreadEvent.t) :=
      match e with
      | ThreadEvent.syscall _ => false
      | ThreadEvent.fence _ Ordering.seqcst => false
      | ThreadEvent.promise _ _ _ _ Memory.op_kind_cancel => false
      | ThreadEvent.promise _ _ _ Message.reserve Memory.op_kind_add => false
      | _ => true
      end. 
    
    End Thread.
End Thread.
