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
Require Import NPThread.
Require Import Configuration.
Require Import MsgMapping.
Require Import DelaySet.
Require Import NPConfiguration.
Require Import ww_RF.

Require Import LibTactics.
Require Import ConfigInitLemmas.

Require Import np_to_ps_thread.
Require Import ps_to_np_thread.

Definition memory_concrete_le (lhs rhs: Memory.t): Prop :=
  forall loc to from val released
         (GET: Memory.get loc to lhs = Some (from, Message.concrete val released)),
    Memory.get loc to rhs = Some (from, Message.concrete val released).
Lemma memory_concrete_le_closed_timemap tm mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (TM: Memory.closed_timemap tm mem0)
  :
    Memory.closed_timemap tm mem1.
Proof.
  ii. hexploit (TM loc). i. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_closed_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_view vw mem0)
  :
    Memory.closed_view vw mem1.
Proof.
  inv VW. econs.
  - eapply memory_concrete_le_closed_timemap; eauto.
  - eapply memory_concrete_le_closed_timemap; eauto.
Qed.

Lemma memory_concrete_le_closed_opt_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_opt_view vw mem0)
  :
    Memory.closed_opt_view vw mem1.
Proof.
  inv VW; econs.
  eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_closed_msg msg mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (MSG: Memory.closed_message msg mem0)
  :
    Memory.closed_message msg mem1.
Proof.
  inv MSG; econs.
  eapply memory_concrete_le_closed_opt_view; eauto.
Qed.

Lemma memory_concrete_le_closed_tview vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: TView.closed vw mem0)
  :
    TView.closed vw mem1.
Proof.
  inv VW. econs.
  - i. eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_local_wf lc mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (PROM: Memory.le (Local.promises lc) mem1)
      (LOCAL: Local.wf lc mem0)
  :
    Local.wf lc mem1.
Proof.
  inv LOCAL. econs; eauto.
  eapply memory_concrete_le_closed_tview; eauto.
Qed.

Lemma closed_mem_implies_wf_msg_view
      loc to mem from val released
      (CLOSED_MEM: Memory.closed mem)
      (GET: Memory.get loc to mem = Some (from, Message.concrete val released)):
  View.opt_wf released.
Proof.
  inv CLOSED_MEM.
  eapply CLOSED in GET; eauto.
  destruct GET as (WF_MSG & MSG_TO & CLOSE_MSG).
  inv WF_MSG; eauto.
Qed.

Lemma closed_mem_implies_closed_msg
      mem loc to from val released
      (CLOSED_MEM: Memory.closed mem)
      (GET: Memory.get loc to mem = Some (from, Message.concrete val released)):
  Memory.closed_opt_view released mem.
Proof.
  inv CLOSED_MEM.
  eapply CLOSED in GET.
  destruct GET as (MSG_WF & MSG_TO & CLOSED_MSG).
  inv CLOSED_MSG; eauto.
Qed.

Lemma write_step_closed_mem
      lc1 sc1 mem1 loc from to val releasedr released ord lc2 sc2 mem2 kind lo
      (CLOSED_VIEW: Memory.closed_opt_view releasedr mem1)
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedr released ord lc2 sc2 mem2 kind lo)
      (LOCAL_WF: Local.wf lc1 mem1)
      (CLOSED_MEM: Memory.closed mem1):
  Memory.closed mem2.
Proof.
  inv STEP.
  inv WRITE.
  inv PROMISE.
  - (* memory add *)
    eapply Memory.add_closed; eauto.
    eapply Memory.closed_message_concrete;
      eapply TViewFacts.op_closed_released; eauto;
        inv LOCAL_WF; eauto.
  - (* memory split *)
    eapply Memory.split_closed; eauto.
    eapply Memory.closed_message_concrete;
      eapply TViewFacts.op_closed_released; eauto;
        inv LOCAL_WF; eauto.
  - (* memory lower *)
    eapply Memory.lower_closed; eauto.
    eapply Memory.closed_message_concrete;
      eapply TViewFacts.op_closed_released; eauto;
        inv LOCAL_WF; eauto.
  - (* memory cancel *)
    tryfalse.
Qed.

Lemma promise_step_closed_mem
      lc1 mem1 loc from to msg lc2 mem2 kind
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2  mem2 kind)
      (LOCAL_WF: Local.wf lc1 mem1)
      (CLOSED_MEM: Memory.closed mem1):
  Memory.closed mem2.
Proof.
  inv STEP.
  inv PROMISE.
  - (* memory add *)
    eapply Memory.add_closed; eauto.
  - (* memory split *)
    eapply Memory.split_closed; eauto.
  - (* memory lower *)
    eapply Memory.lower_closed; eauto.
  - (* memory cancel *)
    eapply Memory.cancel_closed; eauto.
Qed.

Lemma local_wf_promise
      tview promises mem from to msg promises' mem' kind loc
      (PROMISE: Memory.promise promises mem loc from to msg promises' mem' kind)
      (CLOSED_MEM: Memory.closed mem)
      (CLOSED: Memory.closed_message msg mem')
      (LOCAL_WF: Local.wf (Local.mk tview promises) mem):
  Local.wf (Local.mk tview promises') mem'.
Proof. 
  inv LOCAL_WF; simpls.
  econstructor; eauto; simpl.
  {
    (* TView closed *)
    eapply TView.promise_closed; eauto.
  }
  {
    (* Memory le *)
    eapply Memory.promise_le; eauto.
  }
  {
    (* Memory finite *)
    inv PROMISE.
    eapply Memory.add_finite; eauto.
    eapply Memory.split_finite; eauto.
    eapply Memory.lower_finite; eauto.
    eapply Memory.remove_finite; eauto.
  }
  {
    (* Memory bot_none *)
    inv PROMISE.
    eapply Memory.add_bot_none; eauto.
    eapply Memory.split_bot_none; eauto.
    eapply Memory.lower_bot_none; eauto.
    eapply Memory.remove_bot_none; eauto.
  }
Qed.

Lemma local_wf_promise2
      lc mem from to msg promises' mem' kind loc lc0
      (PROMISE: Memory.promise (Local.promises lc) mem loc from to msg promises' mem' kind)
      (CLOSED_MEM: Memory.closed mem)
      (CLOSED: Memory.closed_message msg mem')
      (LOCAL_DISJ: Local.disjoint lc0 lc)
      (LOCAL_WF: Local.wf lc0 mem):
  Local.wf lc0 mem'.
Proof.
  inv LOCAL_WF; econstructor; eauto.
  eapply TView.promise_closed; eauto.
  inv LOCAL_DISJ.
  exploit Memory.promise_disjoint; eauto.
  eapply Memory.disjoint_Symmetric; eauto.
  introv DISJ_LE; destruct DISJ_LE; eauto.
Qed.
  
Lemma local_wf_read
      lc mem lc' loc to val released ord lo
      (READ: Local.read_step lc mem loc to val released ord lc' lo)
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem):
  Local.wf lc' mem.
Proof.
  exploit Local.read_step_future; eauto. ii; des; eauto.
Qed.
  
Lemma local_wf_write
      lc sc mem loc from to val releasedr releasedw ord lc' sc' mem' kind lo
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw ord lc' sc' mem' kind lo)
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem):
  Local.wf lc' mem'.
Proof.
  inv LOCAL_WF.
  inv WRITE.
  inv WRITE0.
  lets LE: PROMISE.
  econstructor; simpl; eauto. 
  eapply TViewFacts.write_future0 in TVIEW_WF; eauto.
  destruct TVIEW_WF; eauto. 
  eapply TViewFacts.op_closed_tview; eauto.
  eapply Memory.promise_op; eauto.

  (* memory le *)
  {
    eapply Memory.promise_le in PROMISE; eauto. 
    eapply Memory.remove_future in REMOVE; eauto.
    destruct REMOVE; eauto.
    inv LE.
    eapply Memory.add_finite; eauto.
    eapply Memory.split_finite; eauto.
    eapply Memory.lower_finite; eauto.
    tryfalse.
  }
  (* memory finite *)
  {
    eapply Memory.remove_finite; eauto.
    inv PROMISE.
    eapply Memory.add_finite; eauto.
    eapply Memory.split_finite; eauto.
    eapply Memory.lower_finite; eauto.
    tryfalse.
  }
  (* bot_none *)
  {
    eapply Memory.remove_bot_none; eauto.
    inv PROMISE.
    eapply Memory.add_bot_none; eauto.
    eapply Memory.split_bot_none; eauto.
    eapply Memory.lower_bot_none; eauto.
    tryfalse.
  }
Qed.

Lemma local_wf_write2
      lc sc mem loc from to val releasedr releasedw ord lc' sc' mem' kind lo lc0
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw ord lc' sc' mem' kind lo)
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_DISJ: Local.disjoint lc0 lc)
      (LOCAL_WF: Local.wf lc0 mem):
  Local.wf lc0 mem'.
Proof.
  inv LOCAL_WF; econstructor; eauto.
  inv WRITE.
  inv WRITE0.
  eapply TView.promise_closed; eauto.
  inv WRITE.
  inv WRITE0.
  inv LOCAL_DISJ.
  eapply Memory.promise_disjoint; eauto.
  eapply Memory.disjoint_Symmetric; eauto.
Qed.
  
Lemma local_wf_upd
      lc mem loc tsr valr lc' lo sc tsw valw releasedr releasedw ordr ordw lc'' sc' mem' kind
      (READ: Local.read_step lc mem loc tsr valr releasedr ordr lc' lo)
      (WRITE: Local.write_step lc' sc mem loc tsr tsw valw releasedr releasedw ordw lc'' sc' mem' kind lo)
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem):
  Local.wf lc'' mem'.
Proof.
  exploit local_wf_read; eauto. ii.
  exploit local_wf_write; eauto.
Qed.

Lemma local_wf_upd2
      lc0 lc mem loc tsr valr lc' lo sc tsw valw releasedr releasedw ordr ordw lc'' sc' mem' kind
      (READ: Local.read_step lc mem loc tsr valr releasedr ordr lc' lo)
      (WRITE: Local.write_step lc' sc mem loc tsr tsw valw releasedr releasedw ordw lc'' sc' mem' kind lo)
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_DISJ: Local.disjoint lc0 lc)
      (LOCAL_WF: Local.wf lc0 mem):
  Local.wf lc0 mem'.
Proof.
  inv LOCAL_WF; econstructor; eauto.
  inv READ; inv WRITE; inv WRITE0; simpls.
  eapply TView.promise_closed; eauto.
  inv READ; inv WRITE; inv WRITE0; simpls.
  inv LOCAL_DISJ.
  eapply Memory.promise_disjoint; eauto.
  eapply Memory.disjoint_Symmetric; eauto.
Qed.
  
Lemma local_wf_fence
      tview promises mem ordr sc ordw
      (CLOSED_MEM: Memory.closed mem)
      (CLOSED_SC: Memory.closed_timemap sc mem)
      (LOCAL_WF: Local.wf (Local.mk tview promises) mem):
  Local.wf (Local.mk (TView.write_fence_tview (TView.read_fence_tview tview ordr) sc ordw) promises) mem.
Proof.
  inv LOCAL_WF; simpls; econstructor; eauto; simpls.
  eapply TViewFacts.write_fence_future with
      (tview := TView.read_fence_tview tview ordr) in CLOSED_SC; eauto.
  destruct CLOSED_SC as (TView_WF & TView_CLOSED & CLOSED_TIMEMAP); eauto.
  eapply TViewFacts.read_fence_future in TVIEW_CLOSED; eauto.
  destruct TVIEW_CLOSED; eauto.
  eapply TViewFacts.read_fence_future in TVIEW_CLOSED; eauto.
  destruct TVIEW_CLOSED; eauto.
  eapply TViewFacts.read_fence_future in TVIEW_CLOSED; eauto.
  destruct TVIEW_CLOSED as (TView_WF & TView_CLOSED).
  eapply TViewFacts.write_fence_future in TView_CLOSED; eauto.
  destruct TView_CLOSED as (?H1 & ?H2 & ?H3); eauto.
Qed.

Lemma local_wf_fence_not_seqcst
      tview promises mem ordr sc ordw
      (CLOSED_MEM: Memory.closed mem)
      (NOT_SEQCST: Ordering.le Ordering.seqcst ordw = false)
      (LOCAL_WF: Local.wf (Local.mk tview promises) mem):
  Local.wf (Local.mk (TView.write_fence_tview (TView.read_fence_tview tview ordr) sc ordw) promises) mem.
Proof.
  inv LOCAL_WF; simpls; econstructor; eauto; simpls.
  {
    (* TView wf *)
    inv TVIEW_WF.
    econstructor.
    intros.
    specialize (REL loc).
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    rewrite NOT_SEQCST; eauto.
    condtac; tryfalse; eauto.    
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    rewrite View.join_bot_r; eauto.
    intro.
    specialize (REL_CUR loc).
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    eapply View.View.le_PreOrder_obligation_1; eauto.
    eapply View.View.le_PreOrder_obligation_1; eauto.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    rewrite View.join_bot_r; eapply View.View.le_PreOrder_obligation_1; eauto.
    rewrite View.join_bot_r; eauto.
  }
  {
    (* TView.closed *)
    inv TVIEW_CLOSED.
    econstructor.
    intro.
    specialize (REL loc).
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    condtac; tryfalse; eauto.
    unfold TView.write_fence_tview, TView.read_fence_tview; simpl.
    condtac; tryfalse; eauto.
    rewrite View.join_bot_r; eauto.
  }
Qed.

Inductive no_scfence_nprm_step (lang : language) (lo : Ordering.LocOrdMap) (e1 e2 : Thread.t lang) : Prop :=
| no_scfence_nprm_step_intro1
    e (STEP: Thread.program_step e lo e1 e2)
    (NO_OUT: ThreadEvent.get_machine_event e = MachineEvent.silent)
    (NO_FENCE_SC: ~(exists ordr, e = ThreadEvent.fence ordr Ordering.seqcst)):
    no_scfence_nprm_step lang lo e1 e2
| no_scfence_nprm_step_intro2
    e (STEP: Thread.promise_step true e e1 e2):
    no_scfence_nprm_step lang lo e1 e2.

Lemma no_scfence_nprm_step_is_nprm_step
      lang lo e1 e2
      (NO_FENCE_SC_STEP: no_scfence_nprm_step lang lo e1 e2):
  Thread.nprm_step lo e1 e2.
Proof.
  inv NO_FENCE_SC_STEP; try solve [econstructor; eauto].
Qed.

Lemma no_scfence_nprm_steps_is_nprm_steps
      lang lo e1 e2
      (NO_FENCE_SC_STEP: rtc (no_scfence_nprm_step lang lo) e1 e2):
  rtc (Thread.nprm_step lo) e1 e2.
Proof.
  induction NO_FENCE_SC_STEP; eauto.
  eapply no_scfence_nprm_step_is_nprm_step in H.
  econstructor; eauto.
Qed.

Lemma Thread_na_step_is_no_scfence_nprm_step
      lang lo e e'
      (NA_STEP: @Thread.na_step lang lo e e'):
    no_scfence_nprm_step lang lo e e'.
Proof.
  inv NA_STEP; try solve [econs; eauto; ii; des; ss].
Qed.

Lemma Thread_na_steps_is_no_scfence_nprm_steps
      lang lo e e'
      (NA_STEPS: rtc (@Thread.na_step lang lo) e e'):
  rtc (no_scfence_nprm_step lang lo) e e'.
Proof.
  induction NA_STEPS; ii; eauto.
  eapply Thread_na_step_is_no_scfence_nprm_step in H.
  eapply Relation_Operators.rt1n_trans; [eapply H | eapply IHNA_STEPS | eauto..].
Qed.

Lemma no_scfence_nprm_step_sc_same
      lang lo e e'
      (NO_SCFENCE_STEP: no_scfence_nprm_step lang lo e e'):
  (Thread.sc e) = (Thread.sc e').
Proof.
  inv NO_SCFENCE_STEP.
  inv STEP; ss; eauto.
  inv LOCAL; ss; eauto.
  inv LOCAL0; ss; eauto.
  inv LOCAL2; ss; eauto.
  inv LOCAL0; ss; eauto.
  unfold TView.write_fence_sc.
  destruct ordw; ss; eauto.
  contradiction NO_FENCE_SC; eauto.
  inv STEP; eauto.
Qed.

Lemma no_scfence_nprm_steps_sc_same
      lang lo e e'
      (NO_SCFENCE_STEPS: rtc (no_scfence_nprm_step lang lo) e e'):
  (Thread.sc e) = (Thread.sc e').
Proof.
  induction NO_SCFENCE_STEPS; eauto.
  eapply no_scfence_nprm_step_sc_same in H.
  rewrite <- IHNO_SCFENCE_STEPS; eauto.
Qed.

Lemma pf_promise_step_is_no_scfence_nprm_step
      lang e e' lo
      (PF_PS: @Thread.pf_promise_step lang e e'):
  no_scfence_nprm_step lang lo e e'.
Proof.
  inv PF_PS.
  eapply no_scfence_nprm_step_intro2; eauto.
Qed.

Lemma pf_promise_steps_is_no_scfence_nprm_steps':
  forall n lang e e' lo
    (PF_PS_STEPS: rtcn (@Thread.pf_promise_step lang) n e e'),
  rtc (no_scfence_nprm_step lang lo) e e'.
Proof.
  induction n; ii; eauto.
  inv PF_PS_STEPS. econs; eauto.
  inv PF_PS_STEPS.
  eapply pf_promise_step_is_no_scfence_nprm_step in A12.
  eapply IHn in A23; eauto.
Qed.

Lemma pf_promise_steps_is_no_scfence_nprm_steps
      lang e e' lo
      (PF_PS_STEPS: rtc (@Thread.pf_promise_step lang) e e'):
  rtc (no_scfence_nprm_step lang lo) e e'.
Proof.
  eapply rtc_rtcn in PF_PS_STEPS.
  des.
  eapply pf_promise_steps_is_no_scfence_nprm_steps'; eauto.
Qed.

Lemma no_scfence_nprm_step_not_care_sc
      lang lo st lc sc mem st' lc' sc' mem' sc0
      (NO_SCFENCE_STEP: no_scfence_nprm_step lang lo
                                             (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')):
  no_scfence_nprm_step lang lo (Thread.mk lang st lc sc0 mem) (Thread.mk lang st' lc' sc0 mem').
Proof.
  inv NO_SCFENCE_STEP.
  - inv STEP. inv LOCAL; try solve [econs; eauto; econs; eauto].
    + inv LOCAL0.
      econs; eauto. econs; eauto.
      econs; eauto. econs; eauto.
      inv WRITABLE. econs; eauto.
    + inv LOCAL2.
      econs; eauto. econs; eauto.
      econs; eauto. econs; eauto.
      inv WRITABLE. econs; eauto.
    + inv LOCAL0.
      destruct ordw; ss;
        try solve [econs; eauto; econs; eauto; eauto].
      contradiction NO_FENCE_SC; eauto.
    + ss.
  - inv STEP.
    eapply no_scfence_nprm_step_intro2; eauto.
    econs; eauto.
Qed.

Lemma no_scfence_nprm_steps_not_care_sc':
  forall n lang lo st lc sc mem st' lc' sc' mem' sc0
    (NO_SCFENCE_STEPS: rtcn (no_scfence_nprm_step lang lo) n
                            (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
    rtc (no_scfence_nprm_step lang lo)
        (Thread.mk lang st lc sc0 mem) (Thread.mk lang st' lc' sc0 mem').
Proof.
  induction n; ii; eauto.
  inv NO_SCFENCE_STEPS; eauto.
  inv NO_SCFENCE_STEPS.
  destruct a2.
  eapply no_scfence_nprm_step_not_care_sc with (sc0 := sc0) in A12.
  eapply IHn in A23; eauto.
Qed.

Lemma no_scfence_nprm_steps_not_care_sc
      lang lo st lc sc mem st' lc' sc' mem' sc0
      (NO_SCFENCE_STEPS: rtc (no_scfence_nprm_step lang lo)
                              (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')):
  rtc (no_scfence_nprm_step lang lo)
      (Thread.mk lang st lc sc0 mem) (Thread.mk lang st' lc' sc0 mem').
Proof.
  eapply rtc_rtcn in NO_SCFENCE_STEPS; eauto.
  des; eauto.
  eapply no_scfence_nprm_steps_not_care_sc'; eauto.
Qed.
  
Lemma no_scfence_nprm_step_prsv_memory_closed
      lang lo e1 e2
      (STEP: no_scfence_nprm_step lang lo e1 e2)
      (CLOSED_MEM: Memory.closed (Thread.memory e1))
      (LOCAL_WF: Local.wf (Thread.local e1) (Thread.memory e1)):
  Memory.closed (Thread.memory e2).
Proof.
  inv STEP.
  - inv STEP0; simpls.
    inv LOCAL; eauto.
    {
      eapply write_step_closed_mem; eauto.
    }
    {
      exploit write_step_closed_mem.
      2: eapply LOCAL2.
      inv LOCAL1.
      eapply closed_mem_implies_closed_msg; eauto.
      eapply local_wf_read; eauto.
      eauto. eauto.
    }
  - inv STEP0; simpls.
    inv LOCAL.
    inv PROMISE; ss.
    eapply Memory.lower_closed; eauto.
    eapply Memory.cancel_closed; eauto.
Qed.

Lemma no_scfence_nprm_step_prsv_local_wf
      lang lo e1 e2
      (STEP: no_scfence_nprm_step lang lo e1 e2)
      (CLOSED_MEM: Memory.closed (Thread.memory e1))
      (LOCAL_WF: Local.wf (Thread.local e1) (Thread.memory e1)):
  Local.wf (Thread.local e2) (Thread.memory e2).
Proof.
  inv STEP.
  - inv STEP0; simpls.
    inv LOCAL; eauto.
    eapply local_wf_read; eauto.
    eapply local_wf_write; eauto.
    eapply local_wf_upd; eauto.
    {
      inv LOCAL0.
      assert(ordw <> Ordering.seqcst).
      {
        intro; subst.
        contradiction NO_FENCE_SC; eauto.
      }
      eapply local_wf_fence_not_seqcst; eauto.
      destruct ordw; simpls; tryfalse; eauto.
      destruct lc1; eauto.
    }
    {
      ss.
    }
  - inv STEP0; ss.
    inv LOCAL.
    eapply local_wf_promise; eauto.
    destruct lc1; eauto.
Qed.

Lemma no_scfence_nprm_steps_prsv_memory_closed:
  forall n lang lo e1 e2
    (STEPS: rtcn (no_scfence_nprm_step lang lo) n e1 e2)
    (CLOSED_MEM: Memory.closed (Thread.memory e1))
    (LOCAL_WF: Local.wf (Thread.local e1) (Thread.memory e1)),
  Memory.closed (Thread.memory e2).
Proof.
  induction n; intros.
  inv STEPS; eauto.
  inv STEPS.
  eapply IHn in A23; eauto.
  eapply no_scfence_nprm_step_prsv_memory_closed; eauto.
  eapply no_scfence_nprm_step_prsv_local_wf; eauto.
Qed.

Lemma no_scfence_nprm_steps_prsv_local_wf:
  forall n lang lo e1 e2
    (STEPS: rtcn (no_scfence_nprm_step lang lo) n e1 e2)
    (CLOSED_MEM: Memory.closed (Thread.memory e1))
    (LOCAL_WF: Local.wf (Thread.local e1) (Thread.memory e1)),
  Local.wf (Thread.local e2) (Thread.memory e2).
Proof.
  induction n; intros.
  inv STEPS; eauto.
  inv STEPS.
  eapply IHn in A23; eauto.
  eapply no_scfence_nprm_step_prsv_memory_closed; eauto.
  eapply no_scfence_nprm_step_prsv_local_wf; eauto.
Qed.

Lemma local_wf_prsv_cancel_steps:
  forall lang lo (e e': Thread.t lang)
    (CCLs: rtc (Thread.cancel_step lo) e e')
    (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e)),
    Local.wf (Thread.local e') (Thread.memory e').
Proof.
  intros. induction CCLs; eauto.
  eapply IHCCLs.
  clear - H LOCAL_WF. inv H. inv STEP; ss.
  inv LOCAL; ss. inv PROMISE.
  econs; eauto; ss.
  {
    inv LOCAL_WF; eauto.
  }
  {
    eapply TView.promise_closed; eauto.
    inv LOCAL_WF; eauto.
  }
  {
    eapply Memory.promise_le; eauto.
    inv LOCAL_WF; eauto.
  }
  {
    eapply Memory.op_finite; eauto.
    inv LOCAL_WF; eauto.
  }
  {
    eapply Memory.cancel_bot_none; eauto.
    inv LOCAL_WF; eauto.
  }
Qed.

Lemma local_wf_prsv_rsv_steps:
  forall lang lo (e e': Thread.t lang)
    (CCLs: rtc (Thread.reserve_step lo) e e')
    (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e)),
    Local.wf (Thread.local e') (Thread.memory e').
Proof.
  intros. induction CCLs; eauto.
  eapply IHCCLs; eauto.
  clear - H LOCAL_WF. inv H. inv STEP; ss.
  inv LOCAL_WF. inv LOCAL; ss.
  econs; eauto; ss.
  {
    eapply TView.promise_closed; eauto.
  }
  {
    eapply Memory.promise_le; eauto.
  }
  {
    inv PROMISE.
    eapply Memory.op_finite; eauto.
  }
  {
    inv PROMISE.
    eapply Memory.add_bot_none; eauto.
  }
Qed.

Lemma memory_closed_prsv_cancel_steps:
  forall lang lo (e e': Thread.t lang)
    (CCLs: rtc (Thread.cancel_step lo) e e')
    (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
    (CLOSED: Memory.closed (Thread.memory e)),
    Memory.closed (Thread.memory e').
Proof.
  intros. induction CCLs; eauto.
  exploit IHCCLs; eauto.
  eapply local_wf_prsv_cancel_steps. 2: eapply LOCAL_WF.
  eapply Operators_Properties.clos_rt1n_step; eauto.
  inv H. inv STEP; ss. inv LOCAL. inv PROMISE.
  eapply Memory.cancel_closed; eauto.
Qed.
  
Lemma memory_closed_prsv_rsv_steps:
  forall lang lo (e e': Thread.t lang)
    (CCLs: rtc (Thread.reserve_step lo) e e')
    (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
    (CLOSED: Memory.closed (Thread.memory e)),
    Memory.closed (Thread.memory e').
Proof.
  intros. induction CCLs; eauto.
  exploit IHCCLs; eauto.
  eapply local_wf_prsv_rsv_steps. 2: eapply LOCAL_WF.
  eapply Operators_Properties.clos_rt1n_step; eauto.
  inv H. inv STEP; ss. inv LOCAL. inv PROMISE.
  eapply Memory.add_closed; eauto.
Qed.
  
(** well-formed configuration initial *)
Lemma wf_config_init:
  forall lang fs (code: Language.syntax lang) ctid c
         (CONFIG_INIT: Configuration.init fs code ctid = Some c),
    Configuration.wf c.
Proof.
  intros.
  eapply config_init_ths_sc_mem in CONFIG_INIT.
  destruct CONFIG_INIT as (Hths_init & Hsc_init & Hmem_init).
  econstructor.
  {
    (* well-formed threads  *)
    econstructor.
    {
      intros.
      lets Hlang1: TH1.
      eapply thread_init_same_lang in Hlang1; eauto. subst.
      lets Hlang2: TH2.
      eapply thread_init_same_lang in Hlang2; eauto. subst.      
      eapply thread_init_lc_init in TH1; eauto. subst.
      eapply thread_init_lc_init in TH2; eauto. subst.
      econstructor; eauto.
      econstructor; eauto.
      intros.
      unfolds Local.init; simpls.
      rewrite Memory.bot_get in GET1; tryfalse.
    }
    {
      intros.
      lets Hlang0: TH.
      eapply thread_init_same_lang in Hlang0; eauto. subst.
      eapply thread_init_lc_init in TH; eauto. subst.
      rewrite Hmem_init.
      econstructor.
      {
        unfold Local.init; simpl.
        eapply TView.bot_wf; eauto.
      }
      {
        eapply TView.bot_closed; eauto.
      }
      {
        eapply Memory.bot_le; eauto.
      }
      {
        eapply Memory.bot_finite; eauto.
      }
      {
        eapply Memory.bot_bot_none; eauto.
      }
    }
  }
  {
    (* closed sc timemap *)
    rewrite Hsc_init, Hmem_init.
    eapply Memory.closed_timemap_bot; eauto.
  }
  {
    (* closed memory *)
    rewrite Hmem_init.
    eapply Memory.init_closed; eauto.
  }
Qed.
  
Ltac discuss_ths_upd :=
  do 3 (match goal with
        | [H: IdentMap.find ?tid1 (IdentMap.add ?tid2 _ _) = Some _ |- _] =>
          destruct (Configuration.tid_eq_dec tid1 tid2); subst; 
          [rewrite IdentMap.gss in H; inv H | rewrite IdentMap.gso in H; eauto]
        | [H: existT ?P ?x ?y = existT ?P ?x ?z |- _] =>
          eapply inj_pair2 in H; subst
        | _ => idtac
        end
       ); tryfalse.

Lemma wf_config_thread_step_prsv
      ths ctid tid sc mem lang st lc st' lc' sc' mem' lo
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
      (STEPS: Thread.all_step lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')):
  Configuration.wf
    (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) ctid sc' mem').
Proof.
  inv CONFIG_WF; simpls.
  inv STEPS. inv USTEP.
  inv STEP.
  - (* promise step *)
    inv STEP0.
    inv LOCAL.
    econstructor; simpls.
    {
      inv WF; simpls.
      econstructor; intros. 
      discuss_ths_upd.
      eapply DISJOINT with (st2 := st2) (lc2 := lc) in TID; eauto.
      inv TID.
      econstructor; simpl. 
      eapply Memory.disjoint_Symmetric in DISJOINT0.
      eapply Memory.promise_disjoint in DISJOINT0; eauto.
      destruct DISJOINT0; eauto.
      eapply Memory.disjoint_Symmetric; eauto.
      eapply THREADS in TH1.
      inv TH1; eauto.
      eapply DISJOINT with (st1 := st1) (lc1 := lc) in TID; eauto.
      inv TID.
      econstructor; simpl.
      eapply Memory.promise_disjoint in DISJOINT0; eauto.
      destruct DISJOINT0; eauto.
      eapply THREADS in TH2; eauto.
      inv TH2; eauto.
      discuss_ths_upd.
      eapply THREADS in TH; eauto.
      eapply local_wf_promise; eauto.
      destruct lc; eauto.
      lets TH0' : TH0.
      eapply THREADS in TH0; eauto.
      eapply local_wf_promise2; eauto.
    }
    {
      inv PROMISE.
      eapply Memory.add_closed_timemap; eauto.
      eapply Memory.split_closed_timemap; eauto.
      eapply Memory.lower_closed_timemap; eauto. 
      eapply Memory.cancel_closed_timemap; eauto.
    }
    {
      inv PROMISE.
      eapply Memory.add_closed; eauto.
      eapply Memory.split_closed; eauto.
      eapply Memory.lower_closed; eauto.
      eapply Memory.cancel_closed; eauto.
    }
  - (* program step *)
    inv STEP0.
    inv LOCAL.
    {
      (* silent step *)
      econstructor; eauto; simpl.
      inv WF.
      econstructor; intros; eauto.
      discuss_ths_upd.
      eapply DISJOINT in TID; eauto.
      discuss_ths_upd.
      eapply THREADS; eauto.
    }
    {
      (* read step *)
      econstructor; eauto; simpl.
      inv WF.
      econstructor; intros; eauto.
      discuss_ths_upd.
      eapply DISJOINT with (st2 := st) (lc2 := lc) in TID; eauto.
      inv TID.
      econstructor.
      inv LOCAL0; simpls; eauto. 
      eapply DISJOINT with (st1 := st) (lc1 := lc) (st2 := st2) (lc2 := lc2) in TID; eauto.
      inv TID.
      econstructor.
      inv LOCAL0; simpls; eauto.
      discuss_ths_upd.
      eapply THREADS in TH.
      eapply local_wf_read in LOCAL0; eauto.
    }
    {
      (* write step *)
      econstructor; eauto; simpl.
      (* - Threads.wf - *) 
      inv WF.
      econstructor; intros; eauto.
      (* - local disjoint - *)
      inv LOCAL0; subst; simpls.
      discuss_ths_upd.
      eapply DISJOINT with (st1 := st) (lc1 := lc) (st2 := st2) (lc2 := lc2) in TID; eauto.
      inv TID.
      econstructor; simpl.
      eapply Memory.write_disjoint in DISJOINT0; eauto.
      destruct DISJOINT0; eauto.
      eapply THREADS in TH2.
      inv TH2; eauto.
      eapply DISJOINT with (st1 := st1) (lc1 := lc1) (st2 := st) (lc2 := lc) in TID; eauto.
      inv TID.
      econstructor; simpl.
      eapply Memory.disjoint_Symmetric in DISJOINT0; eauto.
      eapply Memory.write_disjoint in DISJOINT0; eauto.
      eapply Memory.disjoint_Symmetric.
      destruct DISJOINT0; eauto.
      eapply THREADS in TH1.
      inv TH1; eauto.
      (* - local wf - *)
      discuss_ths_upd.
      eapply THREADS in TH.
      eapply local_wf_write; eauto.
      lets TH0' : TH0.
      eapply THREADS in TH0.
      eapply local_wf_write2; eauto.
      (* - closed timestamp - *)
      inv LOCAL0.
      inv WRITE.
      eapply Memory.promise_closed_timemap; eauto.
      (* - closed memory - *)
      Ltac solve_closed_message WF TH THREADS :=
        inv WF;
        eapply THREADS in TH;
        eapply Memory.closed_message_concrete;
        eapply TViewFacts.op_closed_released; eauto;      
        inv TH; eauto.
      
      inv LOCAL0.
      inv WRITE.
      inv PROMISE.
      (* - closed memory: add - *) 
      eapply Memory.add_closed; eauto.
      solve_closed_message WF TH THREADS.
      (* - closed memory: split - *)
      eapply Memory.split_closed; eauto.
      solve_closed_message WF TH THREADS.
      (* - closed memory: lower - *)
      eapply Memory.lower_closed; eauto.
      solve_closed_message WF TH THREADS.
      (* - closed memory: remove - *)
      tryfalse.
    }
    {
      (* update step *)
      econstructor; eauto; simpl.
      Ltac unfold_upd lc lc0 LOCAL1 LOCAL2 :=
        destruct lc, lc0; simpls;
        inv LOCAL1; simpls;
        inv LOCAL2; simpls.
      
      (* - Threads wf - *)
      inv WF.
      econstructor; intros.
      (* - local disjoint -  *)
      discuss_ths_upd.
      eapply DISJOINT with (st1 := st1) (lc1 := lc1) (st2 := st) (lc2 := lc) in TID; eauto.
      inv TID.
      econstructor.
      eapply Memory.disjoint_Symmetric in DISJOINT0.
      unfold_upd lc lc0 LOCAL1 LOCAL2.
      eapply Memory.write_disjoint in DISJOINT0; eauto.
      inv LC2.
      eapply Memory.disjoint_Symmetric.
      destruct DISJOINT0; eauto.
      eapply THREADS in TH1; inv TH1; eauto.
      eapply DISJOINT with (st1 := st) (lc1 := lc) (st2 := st2) (lc2 := lc0) in TID; eauto.
      unfold_upd lc lc0 LOCAL1 LOCAL2.
      inv TID; simpls.
      econstructor; simpl.
      eapply Memory.write_disjoint in DISJOINT0; eauto.
      destruct DISJOINT0; eauto.
      eapply THREADS in TH2; inv TH2; eauto.
      (* - local wf - *)
      discuss_ths_upd.
      eapply THREADS in TH.
      eapply local_wf_upd; eauto.
      lets TH0' : TH0.
      eapply THREADS in TH0.
      eapply local_wf_upd2; eauto.
      (* - closed timemap - *)
      inv LOCAL1.
      inv LOCAL2; simpls.
      inv WRITE.
      eapply Memory.promise_closed_timemap; eauto.
      (* - closed memory - *)
      inv LOCAL2.
      inv WRITE.
      inv PROMISE.
      
      Ltac solve_closed_message_upd WF TH THREADS GET :=
        solve_closed_message WF TH THREADS;
        [eapply TViewFacts.read_future in GET; eauto;
         [destruct GET; eauto | eapply closed_mem_implies_wf_msg_view; eauto] |
         eapply closed_mem_implies_closed_msg; eauto].
      (* - closed memory: add - *)  
      eapply Memory.add_closed; eauto.
      inv LOCAL1; inv READABLE; simpls. 
      solve_closed_message_upd WF TH THREADS GET.
      (* - closed memory: split - *)
      eapply Memory.split_closed; eauto.
      inv LOCAL1; inv READABLE; simpls. 
      solve_closed_message_upd WF TH THREADS GET.
      (* - closed memory: lower - *)
      eapply Memory.lower_closed; eauto.
      inv LOCAL1; inv READABLE; simpls. 
      solve_closed_message_upd WF TH THREADS GET.
      (* - closed memory: remove - *)
      tryfalse.
    }
    {
      (* fence *)
      inv LOCAL0; simpls.
      econstructor; simpls.
      (* Threads wf *)
      inv WF.
      econstructor; intros.
      discuss_ths_upd.
      eapply DISJOINT with (st1 := st1) (lc1 := lc1) (st2 := st) (lc2 := lc) in TID; eauto.
      inv TID.
      econstructor; simpl; eauto.
      eapply DISJOINT with (st1 := st) (lc1 := lc) (st2 := st2) (lc2 := lc2) in TID; eauto.
      inv TID.
      econstructor; eauto.
      discuss_ths_upd.
      eapply THREADS in TH.
      destruct lc; simpls; eapply local_wf_fence; eauto.
      (* closed timemap *)
      eapply TViewFacts.write_fence_future with
          (tview := TView.read_fence_tview (Local.tview lc) ordr) in SC; eauto.
      destruct SC as (TView_WF & TView_CLOSED & MEM_CLOSED_TIMEMAP); eauto.
      inv WF.
      eapply THREADS in TH.
      inv TH.
      exploit TViewFacts.read_fence_future; eauto.
      introv TView_WF_CLOSED.
      destruct TView_WF_CLOSED; eauto.
      inv WF.
      eapply THREADS in TH; eauto.
      inv TH.
      exploit TViewFacts.read_fence_future; eauto.
      introv TView_WF_CLOSED.
      destruct TView_WF_CLOSED; eauto.
      (* closed memory *)
      eauto.
    }
    {
      (* out put *)
      inv LOCAL0; simpls.
      econstructor; simpls.
      (* Threads wf *)
      inv WF.
      econstructor; intros.
      discuss_ths_upd.
      eapply DISJOINT with (st1 := st1) (lc1 := lc1) (st2 := st) (lc2 := lc) in TID; eauto.
      inv TID.
      econstructor; eauto.
      eapply DISJOINT with (st1 := st) (lc1 := lc) (st2 := st2) (lc2 := lc2) in TID; eauto.
      inv TID.
      econstructor; eauto.
      discuss_ths_upd.
      eapply THREADS in TH.
      destruct lc; simpls.
      eapply local_wf_fence; eauto.
      (* closed timemap *)
      eapply TViewFacts.write_fence_future with
          (tview := TView.read_fence_tview (Local.tview lc) Ordering.seqcst) in SC; eauto.
      destruct SC as (TVIEW_WF & TVIEW_CLOSED & CLOSED_TIMEMAP); eauto.
      inv WF.
      eapply THREADS in TH.
      inv TH.
      exploit TViewFacts.read_fence_future; eauto.
      introv TView_WF_CLOSED.
      destruct TView_WF_CLOSED; eauto.
      inv WF.
      eapply THREADS in TH.
      inv TH.
      exploit TViewFacts.read_fence_future; eauto.
      introv TView_WF_CLOSED.
      destruct TView_WF_CLOSED; eauto.
      (* closed memory *)
      eauto.
    }
Qed.

Lemma wf_config_thread_steps_prsv:
  forall n ths ctid tid sc mem lang st lc st' lc' sc' mem' lo
    (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
    (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
    (STEPS: rtcn (Thread.all_step lo) n (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
    Configuration.wf
      (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) ctid sc' mem').
Proof.
  induction n; ii; eauto.
  - inv STEPS; eauto.
    inv CONFIG_WF; econs; eauto; ss.
    rewrite IdentMap.gsident; eauto.
  - inv STEPS.
    destruct a2.
    eapply IHn with (ths := IdentMap.add tid (existT Language.state lang state, local) ths)
                    (tid := tid) (ctid := ctid) in A23; eauto.
    rewrite IdentMap.add_add_eq in A23; eauto.
    eapply wf_config_thread_step_prsv in A12; eauto.
    rewrite IdentMap.gss; eauto.
Qed.
    
Lemma wf_config_rtc_thread_steps_prsv:
  forall ths ctid tid sc mem lang st lc st' lc' sc' mem' lo
    (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
    (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
    (STEPS: rtc (Thread.all_step lo) (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
    Configuration.wf
      (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) ctid sc' mem').
Proof.
  ii. eapply rtc_rtcn in STEPS. des.
  eapply wf_config_thread_steps_prsv; eauto.
Qed.

Lemma wf_config_rtc_NPThread_tau_steps_prsv
      ths ctid tid sc mem lang st lc b st' lc' sc' mem' b' lo
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
      (STEPS: rtc (NPAuxThread.tau_step lang lo)
                  (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) b)
                  (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') b')):
  Configuration.wf
    (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) ctid sc' mem').
Proof.
  eapply NPThread_tau_steps_to_thread_all_steps in STEPS.
  eapply wf_config_rtc_thread_steps_prsv; eauto.
Qed.

Lemma wf_config_NPThread_out_step_prsv
      ths ctid tid sc mem lang st lc b st' lc' sc' mem' b' e lo
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
      (OUT_STEP: NPAuxThread.out_step lang lo e
                                      (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) b)
                                      (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') b')):
  Configuration.wf
    (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) ctid sc' mem').
Proof.
  eapply NPAuxThread_out_step_is_Thread_program_step in OUT_STEP; ss.
  eapply wf_config_thread_steps_prsv; eauto.
Qed.
  
Lemma wf_config_sw_prsv
      ths ctid ntid sc mem
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem)):
  Configuration.wf (Configuration.mk ths ntid sc mem).
Proof.
  inv CONFIG_WF; ss.
Qed.

Lemma wf_config_rm_prsv
      ths ctid tid ntid sc mem
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem)):
  Configuration.wf (Configuration.mk (IdentMap.remove tid ths) ntid sc mem).
Proof.
  inv CONFIG_WF; ss.
  econs; eauto; ss.
  inv WF. econs; eauto; ii.
  - eapply DISJOINT; eauto.
    rewrite IdentMap.grspec in TH1. des_ifH TH1; ss; eauto.
    rewrite IdentMap.grspec in TH2. des_ifH TH2; ss; eauto.
  - eapply THREADS; eauto.
    instantiate (3 := tid0). instantiate (2 := lang). instantiate (1 := st).
    rewrite IdentMap.grspec in TH. des_ifH TH; ss; eauto.
Qed.

Lemma wf_config_to_local_wf
      lang ths ctid sc mem tid st lc
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)):
  Local.wf lc mem.
Proof.
  inv CONFIG_WF; ss.
  inv WF.
  eauto.
Qed.
