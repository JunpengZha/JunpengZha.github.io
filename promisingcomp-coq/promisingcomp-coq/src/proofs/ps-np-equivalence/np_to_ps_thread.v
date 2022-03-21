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
Require Import Behavior.
Require Import NPConfiguration.
Require Import NPBehavior.

Require Import LibTactics.
Require Import Reordering.
Require Import LocalSim.
Require Import ps_to_np_thread.

Set Implicit Arguments.

Lemma na_step_to_thread_step
      lang lo e1 e2
      (NA_STEP: @Thread.na_step lang lo e1 e2):
  exists te, @Thread.step lang lo true te e1 e2 /\ ThreadEvent.is_na_step te.
Proof.
  inv NA_STEP.
  - (* read *)
    eexists. split.
    eapply Thread.step_program; eauto. ss.
  - (* write *)
    eexists. split.
    eapply Thread.step_program; eauto. ss.
  - (* tau *)
    eexists. split.
    eapply Thread.step_program; eauto. ss.
Qed.

Lemma at_step_to_thread_step
      lang lo e1 e2
      (AT_STEP: @Thread.at_step lang lo e1 e2):
  exists te, @Thread.step lang lo true te e1 e2 /\ ThreadEvent.is_at_or_out_step te /\
        (~ (exists e, te = ThreadEvent.syscall e)).
Proof.
  inv AT_STEP.
  des.
  inv AT_STEP0; eexists; split; [eapply Thread.step_program; eauto | eauto..]; ss.
  destruct o; ss; eauto; try solve [split; eauto; ii; des; ss].
  inv AT_STEP0; eexists; split; [eapply Thread.step_program; eauto | eauto..]; ss.
  destruct o; ss; eauto; try solve [split; eauto; ii; des; ss].
  inv AT_STEP0; eexists; split; [eapply Thread.step_program; eauto | eauto..]; ss.
  try solve [split; eauto; ii; des; ss].
  inv AT_STEP0; eexists; split; [eapply Thread.step_program; eauto | eauto..]; ss.
  try solve [split; eauto; ii; des; ss].
Qed. 

Lemma prc_step_to_thread_step
      lang lo e1 e2
      (PRC_STEP: @Thread.prc_step lang lo e1 e2):
  exists pf te, @Thread.step lang lo pf te e1 e2 /\
           (exists loc t, ThreadEvent.is_promising te = Some (loc, t)).
Proof.
  inv PRC_STEP.
  do 2 eexists.
  split.
  econs. eauto.
  ss.
  eauto.
Qed.

Lemma program_step_to_NPThread_tau_step
      lang lo e e' te b
      (STEP: @Thread.program_step lang te lo e e')
      (NOT_OUT: ~ (exists e, ThreadEvent.syscall e = te)):
  exists b', NPAuxThread.tau_step lang lo (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b') /\
        (ThreadEvent.is_na_step te -> b' = false) /\
        (ThreadEvent.is_at_or_out_step te -> b' = true).
Proof.
  destruct te; ss.
  - inv STEP. inv LOCAL.
  - exists false. split; eauto.
    unfold NPAuxThread.tau_step.
    left.
    econs; eauto.
    eapply Thread.na_tau_step_intro; eauto.
  - destruct ord; ss;
      try solve [exists true; split; eauto;
                   [unfold NPAuxThread.tau_step;
                    right; left;
                    econs; eauto;
                    econs; eauto; left; eauto;
                    econs; eauto | split; ii; ss; eauto]].
    + exists false. split; eauto.
      unfold NPAuxThread.tau_step.
      left.
      econs; eauto.
      eapply Thread.na_plain_read_step_intro; eauto.
  - destruct ord; ss;
      try solve [exists true; split; eauto;
                   [unfold NPAuxThread.tau_step;
                    right; left; econs; eauto;
                    econs; eauto; right; left; eauto;
                    econs; eauto | split; ii; ss; eauto]].
    + exists false. split; eauto;
      unfold NPAuxThread.tau_step.
      left.
      econs; eauto.
      eapply Thread.na_plain_write_step_intro; eauto.
  - exists true; split; eauto.
    unfold NPAuxThread.tau_step.
    right; left; econs; eauto.
    econs; eauto.
    right. right. left.
    econs; eauto.
    split; eauto; ii; des; ss.
  - exists true; split; eauto.
    unfold NPAuxThread.tau_step.
    right; left; econs; eauto.
    econs; eauto.
    right. right. right.
    econs; eauto.
    split; eauto; ii; des; ss.
  - contradiction NOT_OUT.
    eauto.
Qed. 

Lemma NPThread_tau_step_to_program_step
      lang lo e b e' b'
      (TAU_STEP: NPAuxThread.tau_step lang lo (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b')):
  exists te, (@Thread.program_step lang te lo e e' \/ (exists pf, @Thread.promise_step lang pf te e e')) /\
         ~ (exists e, ThreadEvent.syscall e = te).
Proof.
  unfold NPAuxThread.tau_step in *.
  des.
  - (* na step *)
    inv TAU_STEP; ss; subst.
    inv H; try solve [eexists; split; [left; eauto | ii; des; ss]].
  - (* at step *)
    inv TAU_STEP; ss; subst.
    inv H.
    des; inv AT_STEP; try solve [eexists; split; [left; eauto | ii; des; ss]].
  - (* prc step *)
    inv TAU_STEP; ss; subst.
    des; subst.
    inv H.
    eexists.
    split.
    right. eexists. eauto.
    ii; des; ss.
Qed.

Lemma NPThread_tau_step_to_thread_all_step
      lang lo e b e' b'
      (TAU_STEP: NPAuxThread.tau_step lang lo (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b')):
  @Thread.all_step lang lo e e'.
Proof.
  eapply NPThread_tau_step_to_program_step in TAU_STEP.
  des.
  econs. econs.
  eapply Thread.step_program; eauto.
  econs. econs.
  econs. eauto.
Qed.

Lemma NPThread_tau_steps_to_thread_all_steps
      lang lo e b e' b'
      (TAU_STEPS: rtc (NPAuxThread.tau_step lang lo) (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b')):
  rtc (@Thread.all_step lang lo) e e'.
Proof.
  eapply rtc_rtcn in TAU_STEPS. des.
  ginduction n; ii.
  - inv TAU_STEPS. eauto.
  - inv TAU_STEPS. destruct a2.
    eapply NPThread_tau_step_to_thread_all_step in A12.
    eapply IHn in A23; eauto.
Qed.

Lemma NPConfig_abort_to_Config_abort
      lo npc
      (NPCONFIG_ABORT: NPConfiguration.is_abort npc lo):
  Configuration.is_abort (NPConfiguration.cfg npc) lo.
Proof.
  destruct npc; ss.
  inv NPCONFIG_ABORT; ss. des; subst; ss.
  eapply NPAuxThread_tau_steps_2_Thread_tau_steps in H2; ss.
  econs; eauto.
  do 3 eexists.
  split; eauto.
Qed.

Lemma Thread_na_step_to_nprm_step
      lang lo e e'
      (NA_STEP: @Thread.na_step lang lo e e'):
  @Thread.nprm_step lang lo e e'.
Proof.
  inv NA_STEP; econs; eauto.
Qed.

Lemma Thread_na_steps_to_nprm_steps
      lang lo e e'
      (NA_STEPS: rtc (@Thread.na_step lang lo) e e'):
  rtc (@Thread.nprm_step lang lo) e e'.
Proof.
  induction NA_STEPS; eauto.
  eapply Thread_na_step_to_nprm_step in H.
  eapply Relation_Operators.rt1n_trans; eauto.
Qed. 

Lemma Thread_pf_promise_step_is_nprm_step
      lang lo e e'
      (PF_PROMISE_STEP: @Thread.pf_promise_step lang e e'):
  @Thread.nprm_step lang lo e e'.
Proof.
  inv PF_PROMISE_STEP.
  eapply Thread.nprm_step_pf_step; eauto.
Qed.

Lemma Thread_pf_promise_steps_is_nprm_steps
      lang lo e e'
      (PF_PROMISE_STEPS: rtc (@Thread.pf_promise_step lang) e e'):
  rtc (@Thread.nprm_step lang lo) e e'.
Proof.
  induction PF_PROMISE_STEPS; eauto.
  eapply Thread_pf_promise_step_is_nprm_step in H.
  eapply Relation_Operators.rt1n_trans; eauto.
Qed.

Lemma NPThread_all_step_to_Thread_all_step
      lang lo e1 b1 e2 b2
      (STEP: @NPAuxThread.all_step lang lo (NPAuxThread.mk lang e1 b1) (NPAuxThread.mk lang e2 b2)):
  @Thread.all_step lang lo e1 e2.
Proof.
  unfold NPAuxThread.all_step in STEP. des.
  eapply NPThread_tau_step_to_thread_all_step in STEP.
  eauto.
  eapply NPAuxThread_out_step_is_Thread_program_step in STEP. ss.
Qed.
  
Lemma NPThread_all_steps_to_Thread_all_steps':
  forall n lang lo e1 b1 e2 b2
    (STEPS: rtcn (@NPAuxThread.all_step lang lo) n (NPAuxThread.mk lang e1 b1) (NPAuxThread.mk lang e2 b2)),
  rtc (@Thread.all_step lang lo) e1 e2.
Proof.
  induction n; ii.
  inv STEPS. eauto.
  inv STEPS. destruct a2.
  eapply IHn in A23.
  eapply Relation_Operators.rt1n_trans. 2: eapply A23.
  eapply NPThread_all_step_to_Thread_all_step; eauto.
Qed.

Lemma NPThread_all_steps_to_Thread_all_steps
      lang lo e1 b1 e2 b2
      (STEPS: rtc (@NPAuxThread.all_step lang lo) (NPAuxThread.mk lang e1 b1) (NPAuxThread.mk lang e2 b2)):
  rtc (@Thread.all_step lang lo) e1 e2.
Proof.
  eapply rtc_rtcn in STEPS. des.
  eapply NPThread_all_steps_to_Thread_all_steps'; eauto.
Qed.

Lemma Thread_atmblk_step_is_tau_steps
      lang lo (e e': Thread.t lang)
      (ATMBLK_STEP: Thread.atmblk_step lo e e'):
  rtc (Thread.tau_step lo) e e'.
Proof.
  inv ATMBLK_STEP. des.
  eapply na_steps_is_tau_steps in NA_STEPS.
  eapply at_step_is_tau_step in AT_STEP.
  eapply prc_steps_is_tau_steps in PRC_STEPS.
  eapply rtc_compose. eapply NA_STEPS.
  eapply Relation_Operators.rt1n_trans; eauto.
Qed.

Lemma Thread_atmblk_steps_is_tau_steps:
  forall n lang lo (e e': Thread.t lang)
    (ATMBLK_STEPS: rtcn (Thread.atmblk_step lo) n e e'),
    rtc (Thread.tau_step lo) e e'.
Proof.
  induction n; ii.
  inv ATMBLK_STEPS. eauto.
  inv ATMBLK_STEPS.
  eapply IHn in A23.
  eapply Thread_atmblk_step_is_tau_steps in A12.
  eapply rtc_compose; eauto.
Qed.
