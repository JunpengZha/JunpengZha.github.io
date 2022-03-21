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

Set Implicit Arguments.

(** Below are some common auxiliary lemmas *)

Lemma reserve_step_is_allstep:
  forall lang e e' lo,
    @Thread.reserve_step lang lo e e' ->
    @Thread.all_step lang lo e e'.
Proof.
  ii.
  inv H. repeat (econstructor; eauto).
Qed.

Lemma reserve_steps_is_allsteps:
  forall n lang e e' lo,
    rtcn (@Thread.reserve_step lang lo) n e e' ->
    rtc (@Thread.all_step lang lo) e e'.
Proof.
  induction n; ii.
  inv H; eauto.
  inv H.
  eapply IHn in A23; eauto.
  eapply reserve_step_is_allstep in A12; eauto.
Qed.
  
Lemma cancel_step_is_allstep:
  forall lang e e' lo,
    @Thread.cancel_step lang lo e e' ->
    @Thread.all_step lang lo e e'.
Proof.
  ii.
  inv H. repeat (econstructor; eauto).
Qed.

Lemma cancel_steps_is_allsteps:
  forall n lang e e' lo,
    rtcn (@Thread.cancel_step lang lo) n e e' ->
    rtc (@Thread.all_step lang lo) e e'.
Proof.
  induction n; ii.
  inv H; eauto.
  inv H.
  eapply IHn in A23.
  eapply cancel_step_is_allstep in A12; eauto.
Qed.

Lemma promise_step_is_prc_step:
  forall lang e e1 e2 lo pf,
    @Thread.promise_step lang pf e e1 e2 -> @Thread.prc_step lang lo e1 e2.
Proof.
  intros.
  lets Htemp: H. inv Htemp.
  econstructor.
  econstructor; eauto.
Qed. 

Lemma thread_program_step_is_na_or_at_or_out_step:
  forall lang e lo e1 e2,
    @Thread.program_step lang e lo e1 e2 ->
    (@Thread.na_step lang lo e1 e2) \/ (@Thread.at_step lang lo e1 e2) \/
    (exists e', @Thread.out_step lang lo e' e1 e2 /\ e = ThreadEvent.syscall e').
Proof.
  Ltac solve_program_step := econstructor; eauto.
  Ltac solve_program_step2 H o' :=
    eapply H with (o := o'); try intro; tryfalse; try solve_program_step.
  Ltac solve_at_read_step o' :=
    try (right; left); econstructor; left;
    solve_program_step2 Thread.at_read_step_intro o'.
  Ltac solve_at_write_step o' :=
    try (right; left); econstructor; right; left;
    solve_program_step2 Thread.at_write_step_intro o'.
  
  intros. inv H. destruct e; simpls.
  - inv LOCAL.
  - left. eapply Thread.na_tau_step_intro. solve_program_step.
  - inv LOCAL. destruct ord.
    + left. eapply Thread.na_plain_read_step_intro. solve_program_step.
    + solve_at_read_step Ordering.relaxed.
    + solve_at_read_step Ordering.strong_relaxed.
    + solve_at_read_step Ordering.acqrel.
    + solve_at_read_step Ordering.seqcst.
  - inv LOCAL. destruct ord.
    + left. eapply Thread.na_plain_write_step_intro. solve_program_step.
    + solve_at_write_step Ordering.relaxed.
    + solve_at_write_step Ordering.strong_relaxed.
    + solve_at_write_step Ordering.acqrel.
    + solve_at_write_step Ordering.seqcst.
  - right; left. econstructor. right; right; left.
    econstructor. solve_program_step.
  - right; left. econstructor. do 3 right. econstructor.
    solve_program_step.
  - right; right. exists e. econstructor; eauto.
    econstructor. instantiate (1 := e).
    solve_program_step.
Qed.

Lemma thread_program_step_is_na_or_at_or_out_step_strong:
  forall lang e lo e1 e2,
    @Thread.program_step lang e lo e1 e2 ->
    (@Thread.na_step lang lo e1 e2 /\ ThreadEvent.is_na_step e) \/
    (@Thread.at_step lang lo e1 e2 /\ ThreadEvent.is_at_or_out_step e /\ ~ (exists e', e = ThreadEvent.syscall e')) \/
    (exists e', @Thread.out_step lang lo e' e1 e2 /\ e = ThreadEvent.syscall e').
Proof.
  intros. inv H. destruct e; simpls.
  - inv LOCAL.
  - left. split; eauto. eapply Thread.na_tau_step_intro. solve_program_step.
  - inv LOCAL. destruct ord; eauto.
    + left. split; eauto. eapply Thread.na_plain_read_step_intro. solve_program_step.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_read_step Ordering.relaxed.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_read_step Ordering.strong_relaxed.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_read_step Ordering.acqrel.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_read_step Ordering.seqcst.
  - inv LOCAL. destruct ord.
    + left. split; eauto. eapply Thread.na_plain_write_step_intro. solve_program_step.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_write_step Ordering.relaxed.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_write_step Ordering.strong_relaxed.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_write_step Ordering.acqrel.
    + right. left. split; eauto. 2: split; eauto; ii; des; ss.
      solve_at_write_step Ordering.seqcst.
  - right; left. split; eauto. 2: split; eauto; ii; des; ss.
    econstructor. right. right.
    solve_program_step. econs; eauto. econs; eauto.
  - right; left. split; eauto. 2: split; eauto; ii; des; ss.
    econstructor. do 3 right. econstructor.
    solve_program_step.
  - right; right. exists e. econstructor; eauto.
    econstructor. instantiate (1 := e).
    solve_program_step.
Qed.

Lemma thread_tau_step_is_na_or_atmblk_step:
  forall lang e lo e1 e2,
    @Thread.program_step lang e lo e1 e2 ->
    ThreadEvent.get_machine_event e = MachineEvent.silent ->
    (@Thread.na_step lang lo e1 e2) \/ (@Thread.atmblk_step lang lo e1 e2).
Proof.
  intros.
  eapply thread_program_step_is_na_or_at_or_out_step in H.
  destruct H; eauto.
  destruct H.
  - right. unfold Thread.atmblk_step.
    exists e1 e2. split; eauto.
  - destruct H. destruct H. substs.
    inv H0.
Qed.

Lemma thread_tau_step_is_na_or_at_or_prc
      lang lo (e1: Thread.t lang) e2 
      (PS_STEP: Thread.tau_step lo e1 e2):
  Thread.na_step lo e1 e2 \/ 
  Thread.at_step lo e1 e2 \/ 
  Thread.prc_step lo e1 e2.
Proof.
  unfolds Thread.tau_step. 
  inv PS_STEP. inv TSTEP. inv STEP.
  - right; right. 
    inv STEP0.
    eapply Thread.prc_step_intro; eauto.
    eapply Thread.promise_step_intro; eauto.
  - rewrite <- or_assoc. left. 
    eapply thread_program_step_is_na_or_at_or_out_step in STEP0; eauto.
    destruct STEP0 as [H | STEP0]; eauto.
    destruct STEP0 as [H | STEP0]; eauto.
    destruct STEP0 as (e' & Hout_step & Hout_evt); subst.
    tryfalse.
Qed.

Lemma np_na_step_is_tau_step:
  forall lang lo e e',
    @NPAuxThread.na_step lang lo e e' ->
    @NPAuxThread.tau_step lang lo e e'.
Proof.
  intros.
  unfold NPAuxThread.tau_step; eauto.
Qed.

Lemma np_na_steps_is_tau_steps:
  forall lang lo e e',
    rtc (@NPAuxThread.na_step lang lo) e e' ->
    rtc (@NPAuxThread.tau_step lang lo) e e'.
Proof.
  intros.
  induction H; eauto.
  eapply Relation_Operators.rt1n_trans; eauto.
  eapply np_na_step_is_tau_step; eauto.
Qed.

Lemma np_prc_step_is_tau_step:
  forall lang lo e e',
    @NPAuxThread.prc_step lang lo e e' ->
    @NPAuxThread.tau_step lang lo e e'.
Proof.
  intros.
  unfold NPAuxThread.tau_step; eauto.
Qed.

Lemma np_prc_steps_is_tau_steps:
  forall lang lo e e',
    rtc (@NPAuxThread.prc_step lang lo) e e' ->
    rtc (@NPAuxThread.tau_step lang lo) e e'.
Proof.
  intros.
  induction H; eauto.
  eapply Relation_Operators.rt1n_trans; eauto.
  eapply np_prc_step_is_tau_step; eauto.
Qed.

Lemma np_at_step_is_tau_step:
  forall lang lo e e',
    @NPAuxThread.at_step lang lo e e' ->
    @NPAuxThread.tau_step lang lo e e'.
Proof.
  intros.
  unfold NPAuxThread.tau_step; eauto.
Qed.
  
(** Lemmac B.2*) 
Lemma ps_split:
  forall n lang st lc sc mem st' lc' sc' mem' lo
         (THRD_STEPS: rtcn (@Thread.tau_step _ lo) n (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
  exists st0 lc0 sc0 mem0 st1 lc1 sc1 mem1,
    rtc (@Thread.prc_step _ lo) (Thread.mk lang st lc sc mem) (Thread.mk lang st0 lc0 sc0 mem0) /\
    rtc (@Thread.atmblk_step _ lo) (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk lang st1 lc1 sc1 mem1) /\
    rtc (@Thread.na_step _ lo) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st' lc' sc' mem').
Proof.
  induction n; intros.
  - inv THRD_STEPS.
    exists st' lc' sc' mem'; exists st' lc' sc' mem'; eauto.
  - inv THRD_STEPS.
    match goal with
    | H1: Thread.tau_step _ _ _,
          H2: rtcn _ _ _ _ |- _ => rename H1 into THRD_STEP; rename H2 into THRD_STEPS
    | _ => idtac
    end.
    unfold Thread.tau_step in THRD_STEP.
    destruct a2.
    eapply IHn in THRD_STEPS; eauto.
    destruct THRD_STEPS as (st0 & lc0 & sc1 & mem0 & st1 & lc1 & sc2 & mem1 & THRD_STEPS).
    destruct THRD_STEPS as (PRC_STEP & ATMBLK_STEP & NA_STEP).
    inv THRD_STEP. inv TSTEP. inv STEP.
    {
      (* promise step *)
      eapply promise_step_is_prc_step with (lo := lo) in STEP0.
      exists st0 lc0 sc1 mem0. exists st1 lc1 sc2 mem1.
      split; eauto.
    }
    {
      (* program step *) 
      eapply thread_tau_step_is_na_or_atmblk_step in STEP0; eauto.           
      destruct STEP0 as [FNA_STEP | FATM_BLK_STEP].
      {
        (* first na step *) 
        eapply Reordering.prc_steps_forward_na_step_same_thread in FNA_STEP. Focus 2. eauto.
        destruct FNA_STEP as (e0 & FPRC_STEPS & SNA_STEPS).
        clear - ATMBLK_STEP NA_STEP FPRC_STEPS SNA_STEPS.
        inv ATMBLK_STEP.
        {
          (* no atmblk step *)
          destruct e0.
          exists state local sc0 memory. exists state local sc0 memory.
          split; eauto. split; eauto.
          eapply rtc_compose; eauto.
        }
        {
          (* atmblk steps *)
          assert (H_ATMBLK_STEP : Thread.atmblk_step lo e0 y).
          {
            clear - SNA_STEPS H.
            unfolds Thread.atmblk_step.
            destruct H as (e' & e'' & Hna_steps & Hat_steps & Hprc_steps).
            do 2 eexists.
            split. eapply rtc_compose; eauto.
            split; eauto.
          }
          destruct e0, y. clear - FPRC_STEPS H0 H_ATMBLK_STEP NA_STEP.
          do 8 eexists. eauto.
        }
      }
      { 
        (* first atmblk step *)
        clear - PRC_STEP ATMBLK_STEP NA_STEP FATM_BLK_STEP EVENT.
        assert
          (Hatm_blk_step:
             Thread.atmblk_step lo
                                {| Thread.state := st; Thread.local := lc; Thread.sc := sc; Thread.memory := mem |}
                                {| Thread.state := st0; Thread.local := lc0; Thread.sc := sc1; Thread.memory := mem0 |}
          ).
        {
          clear - FATM_BLK_STEP PRC_STEP.
          unfolds Thread.atmblk_step.
          destruct FATM_BLK_STEP as (e' & e'' & Hna_step & Hat_step & Hprc_step).
          do 2 eexists.
          split; eauto. split; eauto.
          eapply rtc_compose; eauto.
        } 

        clear FATM_BLK_STEP.
        do 8 eexists. split; eauto.
      }
    }
Qed.

Lemma rtc_prc_p_to_np:
  forall n lang lo e e',
    rtcn (@Thread.prc_step lang lo) n e e' ->
    rtc (@NPAuxThread.prc_step lang lo) (NPAuxThread.mk lang e true) (NPAuxThread.mk lang e' true).
Proof.
  induction n; intros.
  - inv H; eauto.
  - inv H.
    eapply IHn in A23; eauto.
    eapply Relation_Operators.rt1n_trans with (NPAuxThread.mk lang a2 true); eauto.
    unfold NPAuxThread.prc_step; simpl; eauto.
Qed.

Lemma rtc_na_p_to_np:
  forall n lang lo e e' b,
    rtcn (@Thread.na_step lang lo) n e e' ->
    exists b', rtc (@NPAuxThread.na_step lang lo) (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b').
Proof.
  induction n; intros.
  - inv H; eauto.
  - inv H.
    eapply IHn with (b := false) in A23; eauto.
    destruct A23 as (b' & Hrtc_na_steps).
    exists b'.
    eapply Relation_Operators.rt1n_trans with (NPAuxThread.mk lang a2 false); eauto.
    unfold NPAuxThread.na_step; simpl; eauto.
Qed.

Lemma at_p_to_np:
  forall lang lo e e' b,
    @Thread.at_step lang lo e e' ->
    @NPAuxThread.at_step lang lo (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' true).
Proof.
  intros.
  unfold NPAuxThread.at_step; simpl; eauto.
Qed.
  
Lemma atmblk_p_to_np:
  forall lang lo e e',
    @Thread.atmblk_step lang lo e e' ->
    rtc (@NPAuxThread.tau_step lang lo) (NPAuxThread.mk lang e true) (NPAuxThread.mk lang e' true).
Proof.
  intros.
  inv H.
  destruct H0 as (e0 & Hna_steps & Hat_step & Hprc_steps).
  eapply rtc_rtcn in Hna_steps.
  destruct Hna_steps as (n1 & Hna_steps).
  eapply rtc_na_p_to_np with (b := true) in Hna_steps.
  destruct Hna_steps as (b' & Hrtc_na_steps).
  eapply at_p_to_np with (b := b') in Hat_step.
  eapply rtc_rtcn in Hprc_steps.
  destruct Hprc_steps as (n3 & Hprc_steps). 
  eapply rtc_prc_p_to_np in Hprc_steps.
  eapply np_na_steps_is_tau_steps in Hrtc_na_steps.
  eapply np_at_step_is_tau_step in Hat_step.
  eapply np_prc_steps_is_tau_steps in Hprc_steps.
  eapply rtc_compose. eapply Hrtc_na_steps.
  eapply Relation_Operators.rt1n_trans. eapply Hat_step.
  eapply Hprc_steps.
Qed.

Lemma atmblk_p_to_np_S
      lang lo e e'
      (ATMBLK_STEP: @Thread.atmblk_step lang lo e e'):
  exists n, rtcn (@NPAuxThread.tau_step lang lo) (S n) (NPAuxThread.mk lang e true) (NPAuxThread.mk lang e' true).
Proof.
  inv ATMBLK_STEP. des; subst; ss.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply rtc_na_p_to_np with (b := true) in NA_STEPS. des.
  eapply np_na_steps_is_tau_steps in NA_STEPS.
  eapply at_p_to_np with (b := b') in AT_STEP.
  eapply np_at_step_is_tau_step in AT_STEP.
  eapply rtc_rtcn in PRC_STEPS. des.
  eapply rtc_prc_p_to_np in PRC_STEPS.
  eapply np_prc_steps_is_tau_steps in PRC_STEPS.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply rtc_rtcn in PRC_STEPS. des.
  exploit rtcn_n1; [eapply NA_STEPS | eapply AT_STEP | eauto..].
  ii.
  exploit rtcn_add; [eapply x1 | eapply PRC_STEPS | eauto..].
Qed.
  
Lemma rtc_atmblk_p_to_np:
  forall n lang lo e e',
    rtcn (@Thread.atmblk_step lang lo) n e e' ->
    rtc (@NPAuxThread.tau_step lang lo) (NPAuxThread.mk lang e true) (NPAuxThread.mk lang e' true).
Proof.
  induction n; intros.
  - inv H; eauto.
  - inv H.
    eapply IHn in A23; eauto.
    eapply rtc_compose with (NPAuxThread.mk lang a2 true); eauto.
    eapply atmblk_p_to_np; eauto.
Qed.

Lemma cons_np_steps_from_p_steps_outatmblk:
  forall lang lo e e',
    rtc (@Thread.tau_step lang lo) e e' ->
    exists b, rtc (@NPAuxThread.tau_step lang lo) (NPAuxThread.mk lang e true) (NPAuxThread.mk lang e' b).
Proof.
  intros.
  destruct e, e'; simpls.
  eapply rtc_rtcn in H.
  destruct H as (n & H).
  eapply ps_split in H.
  destruct H as (st0 & lc0 & sc1 & mem0 & st1 & lc1 & sc2 & mem1 & Hrtc_prc & Hrtc_atmblk & Hrtc_na).
  eapply rtc_rtcn in Hrtc_prc.
  destruct Hrtc_prc as (n1 & Hrtc_prc).
  eapply rtc_prc_p_to_np in Hrtc_prc; simpls.
  eapply rtc_rtcn in Hrtc_atmblk.
  destruct Hrtc_atmblk as (n2 & Hrtc_atmblk).
  eapply rtc_atmblk_p_to_np in Hrtc_atmblk; simpls.
  eapply np_prc_steps_is_tau_steps in Hrtc_prc.
  eapply rtc_rtcn in Hrtc_na.
  destruct Hrtc_na as (n3 & Hrtc_na).
  eapply rtc_na_p_to_np with (b := true) in Hrtc_na.
  destruct Hrtc_na as (b' & Hrtc_na).
  eapply np_na_steps_is_tau_steps in Hrtc_na.
  exists b'.
  eapply rtc_compose.
  eapply Hrtc_prc.
  eapply rtc_compose.
  eapply Hrtc_atmblk.
  eauto.
Qed.

Lemma Thread_nprm_step_is_tau_step
      (lang: language) lo (e e': Thread.t lang)
      (NPRM_STEPS: rtc (Thread.nprm_step lo) e e'):
  rtc (Thread.tau_step lo) e e'.
Proof.
  induction NPRM_STEPS; intros; eauto.
  eapply Relation_Operators.rt1n_trans; [idtac | eapply IHNPRM_STEPS].
  inv H.
  econstructor.
  econstructor.
  eapply Thread.step_program; eauto.
  inv PROG.
  inv LOCAL; simpls; eauto; tryfalse.
  inv PF.
  econstructor.
  econstructor.
  econstructor; eauto.
  econstructor; eauto.
  simpl; eauto.
Qed.

Lemma na_step_is_tau_step:
  forall lang lo e e',
    @Thread.na_step lang lo e e' ->
    @Thread.tau_step lang lo e e'.
Proof.
  intros.
  inv H; try solve [econstructor; [econstructor; eapply Thread.step_program; eauto | simpl; eauto]].
Qed.

Lemma na_steps_is_tau_steps:
  forall lang lo e e',
    rtc (@Thread.na_step lang lo) e e' ->
    rtc (@Thread.tau_step lang lo) e e'.
Proof.
  intros.
  induction H; ss; eauto.
  eapply na_step_is_tau_step in H.
  eapply Relation_Operators.rt1n_trans; eauto.
Qed.

Lemma at_step_is_tau_step:
  forall lang lo e e',
    @Thread.at_step lang lo e e' ->
    @Thread.tau_step lang lo e e'.
Proof.
  intros.
  inv H.
  do 3 (destruct AT_STEP as [AT_STEP | AT_STEP];
        [inv AT_STEP; econstructor; [econstructor; eapply Thread.step_program; eauto | simpl; eauto] | idtac]).
  inv AT_STEP; econstructor; [econstructor; eapply Thread.step_program; eauto | simpl; eauto].
Qed.

Lemma prc_step_is_tau_step:
  forall lang lo e e',
    @Thread.prc_step lang lo e e' ->
    @Thread.tau_step lang lo e e'.
Proof.
  intros.
  inv H.
  econstructor; [econstructor; econstructor; eauto | simpl; eauto].
Qed.

Lemma prc_steps_is_tau_steps':
  forall n lang lo e e'
    (PRC_STEPS: rtcn (@Thread.prc_step lang lo) n e e'),
    rtcn (@Thread.tau_step lang lo) n e e'.
Proof.
  induction n; ii.
  inv PRC_STEPS. eauto.
  inv PRC_STEPS.
  eapply prc_step_is_tau_step in A12; eauto.
Qed.

Lemma prc_steps_is_tau_steps
  lang lo e e'
  (PRC_STEPS: rtc (@Thread.prc_step lang lo) e e'):
  rtc (@Thread.tau_step lang lo) e e'.
Proof.
  eapply rtc_rtcn in PRC_STEPS. des.
  eapply prc_steps_is_tau_steps' in PRC_STEPS.
  eapply rtcn_rtc in PRC_STEPS.
  eauto.
Qed.
  
Lemma out_step_is_all_step:
  forall lang lo e e' a,
    @Thread.out_step lang lo a e e' ->
    @Thread.all_step lang lo e e'.
Proof.
  intros.
  inv H.
  econstructor.
  econstructor; eapply Thread.step_program; eauto.
Qed.

Lemma NPAuxThread_tau_step_2_Thread_tau_step:
  forall lang lo th_npc th_npc',
    NPAuxThread.tau_step lang lo th_npc th_npc' ->
    @Thread.tau_step lang lo (NPAuxThread.state lang th_npc) (NPAuxThread.state lang th_npc').
Proof.
  intros. 
  unfold NPAuxThread.tau_step in H.
  destruct H.
  {
    (* na step *)
    inv H.
    eapply na_step_is_tau_step; eauto.
  }
  destruct H.
  {
    (* at step *)
    inv H.
    eapply at_step_is_tau_step; eauto.
  }
  {
    (* prc step *)
    inv H.
    eapply prc_step_is_tau_step; eauto.
  }
Qed.

Lemma NPAuxThread_tau_steps_2_Thread_tau_steps:
  forall lang lo th_npc th_npc',
    rtc (NPAuxThread.tau_step lang lo) th_npc th_npc' ->
    rtc (@Thread.tau_step lang lo) (NPAuxThread.state lang th_npc) (NPAuxThread.state lang th_npc').
Proof.
  intros.
  induction H; eauto.
  eapply Relation_Operators.rt1n_trans; eauto.
  eapply NPAuxThread_tau_step_2_Thread_tau_step; eauto.
Qed.

Lemma Thread_tau_step_is_all_step:
  forall lang lo e e',
    @Thread.tau_step lang lo e e' ->
    @Thread.all_step lang lo e e'.
Proof.
  intros.
  inv H.
  econstructor; eauto.
Qed.

Lemma Thread_tau_steps_is_all_steps:
  forall lang lo e e',
    rtc (@Thread.tau_step lang lo) e e' ->
    rtc (@Thread.all_step lang lo) e e'.
Proof.
  intros.
  induction H; simpls; eauto.
  eapply Relation_Operators.rt1n_trans; eauto.
  eapply Thread_tau_step_is_all_step; eauto.
Qed.

Lemma NPAuxThread_out_step_is_Thread_program_step:
  forall lang lo e th_npc th_npc',
    NPAuxThread.out_step lang lo e th_npc th_npc' ->
    @Thread.all_step lang lo (NPAuxThread.state lang th_npc) (NPAuxThread.state lang th_npc').
Proof.
  intros.
  inv H.
  eapply out_step_is_all_step; eauto.
Qed.

Lemma Thread_all_step_is_tau_or_out_step
      lang lo e e'
      (ALL_STEP: @Thread.all_step lang lo e e'):
  @Thread.tau_step lang lo e e' \/ (exists a, @Thread.out_step lang lo a e e').
Proof.
  inv ALL_STEP.
  inv USTEP.
  inv STEP.
  {
    left. 
    econstructor.
    econstructor.
    eapply Thread.step_promise; eauto.
    inv STEP0. simpl; eauto.
  }
  { 
    eapply thread_program_step_is_na_or_at_or_out_step in STEP0.
    destruct STEP0 as [STEP0 | STEP0]. 
    inv STEP0; try solve [left; econstructor; [econstructor; eapply Thread.step_program; eauto | eauto]].
    destruct STEP0 as [STEP0 | STEP0].
    inv STEP0.
    left.
    do 3 (destruct AT_STEP as
             [AT_STEP | AT_STEP]; [inv AT_STEP; econstructor;
                                   [econstructor; eapply Thread.step_program; eauto | eauto] | idtac]).
    inv AT_STEP; econstructor; [econstructor; eapply Thread.step_program; eauto | eauto].
    destruct STEP0 as (a & Hout_step & Hevent); subst.
    right; eauto.
  }
Qed.

Definition out_trans {lang: language} (lo: Ordering.LocOrdMap) (e e': Thread.t lang) :=
  exists e0 a, rtc (@Thread.tau_step lang lo) e e0 /\ @Thread.out_step lang lo a e0 e'.

Lemma Thread_all_steps_to_out_trans:
  forall n lang lo e e'
    (ALL_STEPS: rtcn (@Thread.all_step lang lo) n e e'),
    exists e0, rtc (@out_trans lang lo) e e0 /\ rtc (@Thread.tau_step lang lo) e0 e'.
Proof.
  induction n; intros; eauto.
  - inv ALL_STEPS.
    eauto.
  - inv ALL_STEPS.
    eapply Thread_all_step_is_tau_or_out_step in A12.
    eapply IHn in A23; eauto.
    destruct A23 as (e0 & Hout_trans & Htau_steps).
    destruct A12.
    {
      inv Hout_trans.
      {
        (* no out step *)
        exists e. split; eauto.
      }
      {
        exists e0. split; [idtac | eapply Htau_steps].
        assert (out_trans lo e y).
        {
          clear - H H0.
          inv H0.
          destruct H1 as (a & Htau_steps & Hout_step).
          econstructor.
          eexists.
          split.
          2: eapply Hout_step.
          eauto.
        }
        eapply Relation_Operators.rt1n_trans; [idtac | eapply H1].
        eauto.
      }
    }
    {
      destruct H as (a & Hout_step).
      exists e0.
      split; eauto.
      eapply Relation_Operators.rt1n_trans; [idtac | eapply Hout_trans].
      unfold out_trans.
      do 2 eexists.
      split; eauto.
    }
Qed. 

Lemma out_trans_to_np_configuration_step:
  forall lo lang st lc sc mem st' lc' sc' mem' tid ths
    (OUT_TRANS: @out_trans lang lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
  exists st0 lc0 sc0 mem0 e b,
    rtc (NPConfiguration.tau_step lo)
        (NPConfiguration.mk (Configuration.mk ths tid sc mem) true)
        (NPConfiguration.mk (Configuration.mk (IdentMap.add tid (existT _ lang st0, lc0) ths) tid sc0 mem0) b) /\
    NPConfiguration.step (MachineEvent.syscall e) lo
                         (NPConfiguration.mk
                            (Configuration.mk (IdentMap.add tid (existT _ lang st0, lc0) ths) tid sc0 mem0) b)
                         (NPConfiguration.mk
                            (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) tid sc' mem') true).
Proof.
  intros. 
  unfold out_trans in OUT_TRANS. 
  destruct OUT_TRANS as (e0 & a & TAU_STEPS & OUT_STEP). 
  assert (Hempty_prm: Local.promises lc' = Memory.bot /\ (Local.promises (Thread.local e0)) = Memory.bot).
  {
    clear - OUT_STEP.
    inv OUT_STEP.
    inv OUT.
    inv LOCAL.
    inv LOCAL0. simpls.
    eauto.
  }
  destruct Hempty_prm as (Hempty_prm & Hempty_prm2).
  eapply cons_np_steps_from_p_steps_outatmblk in TAU_STEPS; eauto.
  destruct TAU_STEPS as (b & NP_THRD_TAU_STEPS).
  eapply rtc_tail in NP_THRD_TAU_STEPS.
  destruct NP_THRD_TAU_STEPS as [NP_THRD_TAU_STEPS | NP_THRD_TAU_STEPS].
  {
    (* tau steps + out step *)
    destruct NP_THRD_TAU_STEPS as (e & TAU_STEPS & HTAU_STEP).
    destruct e; simpls.
    destruct e0; simpls.
    exists state0 local sc0 memory a b.
    split.
    {
      eapply Relation_Operators.rt1n_trans; eauto.
      econstructor.
      eapply NPConfiguration.step_tau with
          (thrd_conf1' := {| NPAuxThread.state := state; NPAuxThread.preempt := preempt |}); eauto; simpl.
      unfold NPAuxThread.consistent.
      unfold Thread.consistent_nprm; simpl; intros.
      eexists.
      split; eauto.
      intro.
      destruct H; tryfalse.
    }
    {
      eapply NPConfiguration.step_out; eauto; simpl.
      rewrite IdentMap.gss; eauto.
      econstructor; eauto.
      unfold NPAuxThread.consistent.
      unfold Thread.consistent_nprm; simpl; intros.
      eexists. split; eauto.
      rewrite IdentMap.add_add_eq; eauto.
    }
  }
  {
    (* only out step *)
    inv NP_THRD_TAU_STEPS. simpls.
    exists st lc sc mem a true.
    split.
    {
      rewrite IdentMap.gsident; eauto.
    }
    {
      eapply NPConfiguration.step_out; eauto; simpl.
      {
        rewrite IdentMap.gsident; eauto.
      }
      {
        unfold NPAuxThread.out_step; eauto.
      }
      {
        unfold NPAuxThread.consistent.
        unfold Thread.consistent_nprm; intros; simpls.
        eexists.
        split; eauto.
      }
      {
        rewrite IdentMap.add_add_eq; eauto.
      }
    }
  }
Qed.

Lemma NPConfig_tau_step_is_all_step:
  forall lo npc npc' 
    (TAU_STEP: (NPConfiguration.tau_step lo) npc npc'),
    (NPConfiguration.all_step lo) npc npc'.
Proof.
  intros.
  inv TAU_STEP.
  econstructor; eauto.
Qed.
  
Lemma NPConfig_tau_steps_is_all_steps:
  forall lo npc npc' 
    (TAU_STEPS: rtc (NPConfiguration.tau_step lo) npc npc'),
    rtc (NPConfiguration.all_step lo) npc npc'.
Proof.
  intros.
  induction TAU_STEPS; intros; eauto.
  eapply Relation_Operators.rt1n_trans; [eapply NPConfig_tau_step_is_all_step; eauto | eapply IHTAU_STEPS].
Qed.

Lemma multi_out_trans_to_np_configuration_steps:
  forall n lo lang st lc sc mem st' lc' sc' mem' tid ths
    (OUT_TRANS: rtcn (@out_trans lang lo) n (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk (Configuration.mk ths tid sc mem) true)
        (NPConfiguration.mk
           (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) tid sc' mem') true).
Proof.
  induction n; intros.
  -  inv OUT_TRANS; eauto.
     rewrite IdentMap.gsident; eauto.
  - inv OUT_TRANS.
    destruct a2. 
    eapply IHn with (ths := IdentMap.add tid (existT _ lang state, local) ths) (tid := tid) in A23; eauto. 
    2: rewrite IdentMap.gss; eauto.
    eapply out_trans_to_np_configuration_step in A12; eauto.
    destruct A12 as (st0 & lc0 & sc1 & mem0 & e & b & TAU_STEPS & OUT_STEP).
    eapply NPConfig_tau_steps_is_all_steps in TAU_STEPS.
    eapply rtc_compose; [eapply TAU_STEPS | idtac].
    eapply Relation_Operators.rt1n_trans.
    econstructor; eapply OUT_STEP.
    rewrite IdentMap.add_add_eq in A23; eauto.
Qed.

Lemma Thread_tau_steps_to_np_configuration_step:
  forall lo lang st lc sc mem st' lc' sc' mem' tid ths
    (TAU_STEPS: rtc (@Thread.tau_step lang lo) (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
    (CONSISTENT: Thread.consistent_nprm (Thread.mk lang st' lc' sc' mem') lo),
  exists b,
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk (Configuration.mk ths tid sc mem) true)
        (NPConfiguration.mk
           (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) tid sc' mem') b).
Proof.
  intros.
  eapply cons_np_steps_from_p_steps_outatmblk in TAU_STEPS.
  destruct TAU_STEPS as (b & TAU_STEPS).
  eapply rtc_tail in TAU_STEPS.
  destruct TAU_STEPS as [TAU_STEPS | TAU_STEPS].
  - destruct TAU_STEPS as (e & TAU_STEPS & TAU_STEP).
    exists b.
    eapply Relation_Operators.rt1n_trans; [idtac | eauto].
    destruct e.
    econstructor.
    eapply NPConfiguration.step_tau with
        (thrd_conf1' := {| NPAuxThread.state := state; NPAuxThread.preempt := preempt |}); eauto; simpl.
  - inv TAU_STEPS.
    rewrite IdentMap.gsident; eauto.
Qed.
    
Lemma thread_all_step_to_NPConfiguration_all_step_from_outAtmBlk:
  forall lo lang st lc sc mem st' lc' sc' mem' tid ths 
    (STEPS: rtc (@Thread.all_step lang lo)
                (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
    (CONSISTENT: NPAuxThread.consistent lang (Thread.mk lang st' lc' sc' mem') lo),
  exists b',
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk (Configuration.mk ths tid sc mem) true)
        (NPConfiguration.mk (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) tid sc' mem') b').
Proof.
  intros.
  eapply rtc_rtcn in STEPS.
  destruct STEPS as (n & STEPS).
  eapply Thread_all_steps_to_out_trans in STEPS.
  destruct STEPS as (e0 & Hout_trans & Htau_steps).
  destruct e0.
  eapply rtc_rtcn in Hout_trans.
  destruct Hout_trans as (n1 & Hout_trans).
  eapply multi_out_trans_to_np_configuration_steps in Hout_trans; eauto. 
  eapply Thread_tau_steps_to_np_configuration_step with
      (ths := IdentMap.add tid (existT Language.state lang state, local) ths) (tid := tid) in Htau_steps; eauto.
  destruct Htau_steps as (b & Htau_steps).
  exists b.
  eapply rtc_compose; [eapply Hout_trans | idtac].
  rewrite IdentMap.add_add_eq in Htau_steps; eauto.
  rewrite IdentMap.gss; eauto.
Qed.

Lemma NPThread_tau_step_is_NPThread_all_step
      lang lo e b e' b'
      (TAU_STEP: NPAuxThread.tau_step lang lo (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b')):
  NPAuxThread.all_step lang lo (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b').
Proof.
  econs; eauto.
Qed.

Lemma NPThread_tau_steps_is_NPThread_all_steps
      lang lo e b e' b'
      (TAU_STEPS: rtc (NPAuxThread.tau_step lang lo)
                      (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b')):
  rtc (NPAuxThread.all_step lang lo)
      (NPAuxThread.mk lang e b) (NPAuxThread.mk lang e' b').
Proof.
  induction TAU_STEPS; eauto.
  eapply NPThread_tau_step_is_NPThread_all_step in H; eauto.
  destruct x; ss. destruct y; ss.
  eapply Relation_Operators.rt1n_trans.
  eapply H. eapply IHTAU_STEPS.
Qed.
  
Lemma out_trans_to_NPThread_all_steps:
  forall lo lang st lc sc mem st' lc' sc' mem' 
    (OUT_TRANS: @out_trans lang lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
    rtc (NPAuxThread.all_step lang lo)
        (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) true)
        (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') true).
Proof.
  ii.
  inv OUT_TRANS. des. destruct x.
  eapply cons_np_steps_from_p_steps_outatmblk in H; eauto.
  des; ss.
  eapply NPThread_tau_steps_is_NPThread_all_steps in H.
  eapply rtc_n1. eapply H.
  unfold NPAuxThread.all_step. right.
  inv H0.
  exists e.
  econs; eauto. ss.
  econs. eauto.
Qed.

Lemma multi_out_trans_to_NPThread_steps:
  forall n lo lang st lc sc mem st' lc' sc' mem'
    (OUT_TRANS: rtcn (@out_trans lang lo) n (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
    rtc (NPAuxThread.all_step lang lo)
        (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) true)
        (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') true).
Proof.
  induction n; intros.
  -  inv OUT_TRANS; eauto.
  - inv OUT_TRANS.
    destruct a2.
    eapply IHn in A23; eauto.
    eapply out_trans_to_NPThread_all_steps in A12.
    eapply rtc_compose; [eapply A12 | eapply A23].
Qed.

Lemma thread_all_step_to_NPThread_all_steps_from_outAtmBlk:
  forall lo lang st lc sc mem st' lc' sc' mem'
    (STEPS: rtc (@Thread.all_step lang lo)
                (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')),
    exists b', rtc (NPAuxThread.all_step lang lo)
              (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) true)
              (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') b').
Proof.
  ii.
  eapply rtc_rtcn in STEPS. des.
  eapply Thread_all_steps_to_out_trans in STEPS. des.
  destruct e0.
  eapply rtc_rtcn in STEPS. des.
  eapply multi_out_trans_to_NPThread_steps in STEPS; eauto.
  eapply cons_np_steps_from_p_steps_outatmblk in STEPS0; eauto. des.
  eapply NPThread_tau_steps_is_NPThread_all_steps in STEPS0.
  eexists.
  eapply rtc_compose. eapply STEPS. eapply STEPS0.
Qed.

Lemma pf_promise_steps_to_np
      lang e e' lo
      (PF_PRM_STEP: rtc (@Thread.pf_promise_step lang) e e'):
  rtc (NPAuxThread.prc_step lang lo)
      (NPAuxThread.mk lang e true) (NPAuxThread.mk lang e' true).
Proof.
  induction PF_PRM_STEP; eauto.
  eapply Relation_Operators.rt1n_trans.
  2: eapply IHPF_PRM_STEP.
  inv H.
  inv PF_STEP.
  econs; eauto. econs; eauto; ss.
  econs; eauto.
Qed.
