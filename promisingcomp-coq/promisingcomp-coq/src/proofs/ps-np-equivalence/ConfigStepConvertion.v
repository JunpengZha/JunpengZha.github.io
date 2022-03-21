Require Import sflib.    

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.  
(* Require Import  *)
Require Import Language.

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration. 
Require Import Behavior.
Require Import NPThread.
Require Import NPConfiguration.
Require Import NPBehavior.

Require Import LibTactics.
Require Import Reordering. 
Require Import ps_to_np_thread.
Require Import np_to_ps_thread.
Require Import Omega.
Require Import FulfillStep.
Require Import WFConfig.
Require Import ConsistentProp.
Require Import ConsistentStableEnv.

Lemma NPConfig_steps_sw_tid:
  forall n lo c1 tid1 c2 b2 lang st lc
    (NP_ALL_STEPS: rtcn (NPConfiguration.all_step lo) n
                        (NPConfiguration.mk (Configuration.sw_tid c1 tid1) true)
                        (NPConfiguration.mk c2 b2))
    (TH: IdentMap.find (Configuration.tid c2) (Configuration.threads c2)
         = Some (existT _ lang st, lc))
    (WF_CONFIG: Configuration.wf c1),
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk c1 true) (NPConfiguration.mk c2 b2).
Proof.
  induction n; ii.
  - inv NP_ALL_STEPS; ss.
    eapply Operators_Properties.clos_rt1n_step.
    econs. eapply NPConfiguration.step_sw; eauto.
  - inv NP_ALL_STEPS. destruct a2.
    inv A12. destruct e.
    + assert (TH': exists lang st lc,
                 IdentMap.find tid1 (Configuration.threads c1)
                 = Some (existT _ lang st, lc)).
      {
        inv H; ss. eauto.
      }
      des.
      eapply rtcn_rtc in A23.
      eapply Relation_Operators.rt1n_trans.
      econs. eapply NPConfiguration.step_sw; eauto.
      ss.
      eapply Relation_Operators.rt1n_trans.
      econs. eapply H. eauto.
    + inv H; ss; inv NPC2.
      {
        eapply IHn; eauto.
      }
      {
        ss.
        eapply rtcn_rtc in A23.
        eapply Relation_Operators.rt1n_trans.
        econs. eapply NPConfiguration.step_sw; eauto.
        ss.
        eapply Relation_Operators.rt1n_trans.
        econs. eapply NPConfiguration.step_thread_term; eauto.
        ss. eauto. ss.
      }
    + assert (TH': exists lang st lc,
                 IdentMap.find tid1 (Configuration.threads c1)
                 = Some (existT _ lang st, lc)).
      {
        inv H; ss. eauto.
      }
      des.
      eapply rtcn_rtc in A23.
      eapply Relation_Operators.rt1n_trans.
      econs. eapply NPConfiguration.step_sw; eauto.
      ss.
      eapply Relation_Operators.rt1n_trans.
      econs. eapply H. eauto.
Qed.

Lemma Config_aux_na_step_to_NPConfig_step
      lo c b c'
      (NA_AUX_STEP: Configuration.aux_step AuxEvent.na lo c c')
      (WF_CONFIG: Configuration.wf c):
  NPConfiguration.step MachineEvent.silent lo
                       (NPConfiguration.mk c b) (NPConfiguration.mk c' false).
Proof.
  inv NA_AUX_STEP.
  destruct c, c'; ss. inv C2.
  exploit wf_config_rtc_thread_steps_prsv;
    [eapply WF_CONFIG | eapply TID1 | idtac ..].
  {
    eapply na_steps_is_tau_steps in STEPS.
    eapply Thread_tau_steps_is_all_steps in STEPS.
    eapply na_step_is_tau_step in STEP.
    eapply Thread_tau_step_is_all_step in STEP.
    eapply rtc_n1. eapply STEPS. eapply STEP.
  }
  introv WF_CONFIG'.
  eapply rtc_rtcn in STEPS. des.
  eapply rtc_na_p_to_np with (b := b) in STEPS. des.
  eapply np_na_steps_is_tau_steps in STEPS.
  econs; eauto.
  unfold NPAuxThread.tau_step.
  left. unfold NPAuxThread.na_step; ss.
  eapply Thread_consistent_to_consistent_nprm; eauto; ss.
  eapply wf_config_to_local_wf; eauto.
  instantiate (3 := tid).
  rewrite IdentMap.gss; eauto.
  inv WF_CONFIG'; ss.
Qed.

Lemma Configuration_aux_prc_step_to_NPConfig_step
      lo c c'
      (PRC_AUX_STEP: Configuration.aux_step AuxEvent.prc lo c c')
      (WF_CONFIG: Configuration.wf c):
  NPConfiguration.step MachineEvent.silent lo
                       (NPConfiguration.mk c true) (NPConfiguration.mk c' true).
Proof.
  inv PRC_AUX_STEP.
  destruct c, c'; ss. inv C2; ss.
  exploit wf_config_rtc_thread_steps_prsv;
    [eapply WF_CONFIG | eapply TID1 | idtac ..].
  {
    eapply prc_steps_is_tau_steps in STEPS.
    eapply Thread_tau_steps_is_all_steps in STEPS.
    eapply prc_step_is_tau_step in STEP.
    eapply Thread_tau_step_is_all_step in STEP.
    eapply rtc_n1. eapply STEPS. eapply STEP.
  }
  introv WF_CONFIG'.
  econs.
  ss.
  ss. eauto.
  ss. eapply rtc_rtcn in STEPS. des. eapply rtc_prc_p_to_np in STEPS.
  eapply np_prc_steps_is_tau_steps in STEPS. eapply STEPS.
  unfold NPAuxThread.tau_step. right. right.
  unfold NPAuxThread.prc_step. ss. split; eauto.
  instantiate (1 := NPAuxThread.mk lang (Thread.mk lang st2 lc2 sc0 memory0) true).
  ss. split; eauto. eauto.
  unfold NPAuxThread.consistent.
  eapply Thread_consistent_to_consistent_nprm; eauto; ss.
  eapply wf_config_to_local_wf; eauto.
  instantiate (3 := tid).
  rewrite IdentMap.gss; eauto.
  inv WF_CONFIG'; eauto.
  ss.
Qed.

Lemma Configuration_aux_output_step_to_NPConfig_step
      lo c c' e b
      (OUT_AUX_STEP: Configuration.aux_step (AuxEvent.out e) lo c c'):
  exists c0 b0,
    ((c = c0 /\ b = b0) \/
       NPConfiguration.step MachineEvent.silent lo
                            (NPConfiguration.mk c b) (NPConfiguration.mk c0 b0))
    /\ NPConfiguration.step (MachineEvent.syscall e) lo
                           (NPConfiguration.mk c0 b0) (NPConfiguration.mk c' true).
Proof.
  inv OUT_AUX_STEP.
  destruct c, c'; ss. inv C2; ss.
  eapply rtc_rtcn in STEPS. des.
  assert (PROM_EMPTY: Local.promises (Thread.local e1) = Memory.bot /\ Local.promises lc2 = Memory.bot).
  {
    clear - STEP_OUT.
    inv STEP_OUT. inv OUT; ss. inv LOCAL.
    inv LOCAL0; ss.
    exploit PROMISES; eauto.
  }
  des.
  destruct n.
  - inv STEPS.
    do 2 eexists. split. left. eauto.
    econs.
    eauto. ss. eauto.
    ss.
    instantiate (1 := NPAuxThread.mk lang (Thread.mk lang st2 lc2 sc0 memory0) true).
    econs. ss. ss. ss.
    unfold NPAuxThread.consistent; ss.
    unfold Thread.consistent_nprm; ss. ii.
    eexists. split; eauto. eauto. ss.
  - eapply rtcn_tail in STEPS. des.
    eapply rtc_na_p_to_np with (b := b) in STEPS. des.
    destruct e1; ss.
    do 2 eexists.
    
    split.
    right.
    econs.
    ss. ss. eauto. ss.
    eapply np_na_steps_is_tau_steps in STEPS. eapply STEPS.
    unfold NPAuxThread.tau_step. left.
    unfold NPAuxThread.na_step. ss.
    instantiate (1 := NPAuxThread.mk lang (Thread.mk lang state local sc1 memory1) false). ss.
    eauto.
    unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss.
    ii. eexists. split; eauto.
    ss.

    econs.
    ss.
    ss. rewrite IdentMap.gss; eauto.
    eauto. ss.
    instantiate (1 := NPAuxThread.mk lang (Thread.mk lang st2 lc2 sc0 memory0) true).
    unfold NPAuxThread.out_step; ss.
    ss. unfold NPAuxThread.consistent. ii; ss.
    eexists. split; eauto. eauto.
    ss. rewrite IdentMap.add_add_eq; eauto.
Qed.

Lemma Config_aux_atm_step_to_NPConfig_step
      lo c c'
      (CONFIG_AUX_ATM: Configuration.aux_step AuxEvent.atm lo c c')
      (WF_CONFIG: Configuration.wf c):
  NPConfiguration.tau_step lo (NPConfiguration.mk c true)
                           (NPConfiguration.mk c' true).
Proof.
  destruct c, c'; ss.
  inv CONFIG_AUX_ATM; ss. inv C2.

  exploit wf_config_rtc_thread_steps_prsv.
  eauto. eauto.
  eapply prc_steps_is_tau_steps in STEPS_PRC.
  eapply Thread_tau_steps_is_all_steps in STEPS_PRC.
  eapply rtc_rtcn in STEPS_ATM. des.
  eapply Thread_atmblk_steps_is_tau_steps in STEPS_ATM.
  eapply Thread_tau_steps_is_all_steps in STEPS_ATM.
  eapply Thread_atmblk_step_is_tau_steps in STEP_ATM.
  eapply Thread_tau_steps_is_all_steps in STEP_ATM.
  eapply rtc_compose. eapply STEPS_PRC.
  eapply rtc_compose. eapply STEPS_ATM. eapply STEP_ATM.
  introv WF_CONFIG'.
  
  eapply rtc_rtcn in STEPS_PRC. des.
  eapply rtc_prc_p_to_np in STEPS_PRC.
  eapply np_prc_steps_is_tau_steps in STEPS_PRC.
  eapply rtc_rtcn in STEPS_ATM. des.
  eapply rtc_atmblk_p_to_np in STEPS_ATM.
  eapply atmblk_p_to_np_S in STEP_ATM. des.
  eapply rtcn_tail in STEP_ATM. des. destruct a2.
  eapply rtcn_rtc in STEP_ATM.
  econs.
  eapply NPConfiguration.step_tau.
  ss. ss. eauto. ss.
  eapply rtc_compose. eapply STEPS_PRC.
  eapply rtc_compose. eapply STEPS_ATM. eapply STEP_ATM.
  eauto. eauto.
  unfold NPAuxThread.consistent.
  eapply Thread_consistent_to_consistent_nprm; eauto.
  ss. eapply wf_config_to_local_wf; eauto.
  instantiate (3 := tid). rewrite IdentMap.gss. eauto.
  ss. inv WF_CONFIG'; ss.
  eauto.
  ii; des; ss.
Qed.

Lemma Config_aux_tterm_to_NPConfig_step
      lo c c' b
      (TTERM: Configuration.aux_step AuxEvent.tterm lo c c'):
  NPConfiguration.step MachineEvent.switch lo
                       (NPConfiguration.mk c b) (NPConfiguration.mk c' true).
Proof.
  destruct c, c'; ss.
  inv TTERM; ss. inv C2.
  eapply NPConfiguration.step_thread_term; eauto.
Qed.

Lemma Config_aux_na_out_merge
      lo c c' c'' e
      (NA: Configuration.aux_step AuxEvent.na lo c c')
      (OUT: Configuration.aux_step (AuxEvent.out e) lo c' c''):
  Configuration.aux_step (AuxEvent.out e) lo c c''.
Proof.
  destruct c, c', c''; ss.
  inv NA; ss. inv C2. inv OUT; ss. inv C2.
  rewrite IdentMap.gss in TID0. inv TID0.
  eapply inj_pair2 in H1. subst.
  econs.
  eauto.
  ss. eauto.
  ss. eapply rtc_compose. 2: eapply STEPS0.
  eapply rtc_n1. eapply STEPS. eauto.
  ss. eauto.
  ss.
  ss.
  rewrite IdentMap.add_add_eq; eauto.
Qed.

Lemma thread_na_steps_atmblk_steps_merge
      lang (e e' e'': Thread.t lang) lo
      (NA_STEPS: rtc (Thread.na_step lo) e e')
      (ATM_STEP: Thread.atmblk_step lo e' e''):
  Thread.atmblk_step lo e e''.
Proof.
  inv ATM_STEP. des.
  exploit rtc_compose; [eapply NA_STEPS | eapply NA_STEPS0 | eauto..].
  ii.
  econs; eauto.
Qed.
  
Lemma Config_aux_na_atm_merge
      lo c c' c''
      (NA: Configuration.aux_step AuxEvent.na lo c c')
      (ATM: Configuration.aux_step AuxEvent.atm lo c' c''):
  Configuration.aux_step AuxEvent.atm lo c c''.
Proof.
  destruct c, c', c''; ss.
  inv NA; ss. inv C2. inv ATM; ss. inv C2.
  exploit rtc_n1; [eapply STEPS | eapply STEP | eauto..].
  introv NA_STEPS. clear STEPS STEP.
  rewrite IdentMap.gss in TID0. inv TID0.
  eapply inj_pair2 in H1. subst.
  exploit prc_steps_forward_na_steps_same_thread;
    [eapply NA_STEPS | eapply STEPS_PRC | eauto..].
  ii; des. clear STEPS_PRC NA_STEPS.
  eapply rtc_rtcn in STEPS_ATM. des.
  exploit rtcn_n1; eauto. ii.
  inv x2. 
  exploit thread_na_steps_atmblk_steps_merge; eauto.
  clear x1 A12. ii.
  exploit rtcn_cons; eauto.
  clear A23 x2. introv STEP_ATMBLK. 
  eapply rtcn_tail in STEP_ATMBLK. des.
  eapply rtcn_rtc in STEP_ATMBLK.
  econs.
  eauto.
  ss. eauto.
  ss. eauto.
  eapply STEP_ATMBLK.
  ss. eapply STEP_ATMBLK0.
  ss.
  ss. rewrite IdentMap.add_add_eq. eauto.
Qed.

Lemma Config_aux_na_merge
      lo c c' c''
      (NA1: Configuration.aux_step AuxEvent.na lo c c')
      (NA2: Configuration.aux_step AuxEvent.na lo c' c''):
  Configuration.aux_step AuxEvent.na lo c c''.
Proof.
  destruct c, c', c''; ss.
  inv NA1; ss. inv C2. inv NA2; ss. inv C2.
  rewrite IdentMap.gss in TID0. inv TID0.
  eapply inj_pair2 in H1. subst.
  econs.
  eauto.
  ss. eauto.
  ss. eapply rtc_compose. 2: eapply STEPS0.
  eapply rtc_n1. eapply STEPS. eauto.
  ss. eauto.
  ss.
  ss.
  rewrite IdentMap.add_add_eq; eauto.
Qed.
  
Lemma cons_na_abort
      c c' lo
      (AUX_NA_STEP: Configuration.aux_step AuxEvent.na lo c c')
      (ABORT: Configuration.is_abort c' lo):
  Configuration.is_abort c lo.
Proof.
  inv AUX_NA_STEP.
  destruct c, c'; ss. inv C2.
  inv ABORT; ss. des.
  rewrite IdentMap.gss in H. inv H.
  eapply inj_pair2 in H4. subst.
  eapply na_steps_is_tau_steps in STEPS.
  eapply na_step_is_tau_step in STEP.
  econs; eauto; ss.
  exists st1 lc1 e'.
  split; eauto. split; eauto.
  eapply rtc_compose.
  eapply STEPS.
  eapply Relation_Operators.rt1n_trans.
  eapply STEP. eapply H0.
Qed.

Lemma Config_abort_to_NPConfig_abort
      c lo
      (ABORT: Configuration.is_abort c lo):
  NPConfiguration.is_abort (NPConfiguration.mk c true) lo.
Proof.
  inv ABORT. des.
  eapply cons_np_steps_from_p_steps_outatmblk in H0; ss.
  des.
  econs; eauto; ss.
  exists st1 lc1. eexists. exists e' c b.
  split; eauto.
Qed.

Inductive Config_na_fulfill_step (lo: Ordering.LocOrdMap):
  Configuration.t -> Configuration.t -> Prop :=
| Config_na_fulfill_step_intro
    c tid lang st lc st' lc' st'' lc'' c'
    (TID: Configuration.tid c = tid)
    (TH: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc))
    (STEPS: rtc (@na_fulfill_step lang lo (Configuration.sc c) (Configuration.memory c)) (st, lc) (st', lc'))
    (STEP: na_fulfill_step lo (Configuration.sc c) (Configuration.memory c) (st', lc') (st'', lc''))
    (CONSISTENT: Thread.consistent (Thread.mk lang st'' lc'' (Configuration.sc c) (Configuration.memory c)) lo)
    (C2: c' = Configuration.mk (IdentMap.add tid (existT _ lang st'', lc'') (Configuration.threads c))
                               tid (Configuration.sc c) (Configuration.memory c)):
  Config_na_fulfill_step lo c c'.

Lemma Config_na_step_to_na_fulfill_step
      c c' lo
      (AUX_NA_STEP: Configuration.aux_step AuxEvent.na lo c c'):
  exists c0,
    (Configuration.aux_step AuxEvent.prc lo c c0 \/ c = c0)
    /\ Config_na_fulfill_step lo c0 c'.
Proof.
  inv AUX_NA_STEP.
  destruct c, c'; ss. inv C2.
  eapply rtc_rtcn in STEPS. des.
  destruct e1.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  introv STEPS'.
  eapply promises_forward_na_steps in STEPS'. des; subst.
  eapply rtc_rtcn in STEPS'. des.
  destruct n0; ss.
  - (* no previous prc step *)
    inv STEPS'.
    eexists. split. right. eauto.
    eapply rtcn_tail in STEPS'0. des. destruct a2.
    eapply rtcn_rtc in STEPS'0.
    econs.
    ss. ss. eauto.
    ss. eapply STEPS'0.
    ss. eapply STEPS'1.
    ss. ss.
  - (* has previous prc steps *)
    eapply rtcn_tail in STEPS'. des.
    destruct a2.
    exists (Configuration.mk (IdentMap.add tid (existT _ lang st1, lc0) threads)
                        tid sc0 memory0).
    split.
    left.
    econs.
    eauto.
    ss. eauto.
    ss. eapply rtcn_rtc in STEPS'. eapply STEPS'.
    ss. eapply STEPS'1.
    ss. eapply consistency_forward_na_steps with (n := S n); eauto.
    ss.
    eapply rtcn_tail in STEPS'0. des.
    eapply rtcn_rtc in STEPS'0. destruct a2.
    econs; eauto.
    ss. rewrite IdentMap.gss; eauto.
    ss. rewrite IdentMap.add_add_eq. eauto.
Qed.

Lemma Config_na_fulfill_step_to_Config_aux_na_step
      lo c c'
      (CONFIG_NA_FULFILL: Config_na_fulfill_step lo c c'):
  Configuration.aux_step AuxEvent.na lo c c'.
Proof.
  inv CONFIG_NA_FULFILL.
  eapply rtc_rtcn in STEPS. des.
  eapply na_fulfill_steps_to_na_steps in STEPS.
  eapply rtcn_rtc in STEPS.
  eapply na_fulfill_step_to_na_step in STEP.
  econs; eauto.
Qed.

Lemma Config_na_fulfill_step_sc_mem_unchange
      c c' lo
      (CONFIG_NA_FULFILL_STEP: Config_na_fulfill_step lo c c'):
  <<SC_UNCHANG: Configuration.sc c = Configuration.sc c'>> /\
  <<MEM_UNCHANG: Configuration.memory c = Configuration.memory c'>>.
Proof.
  inv CONFIG_NA_FULFILL_STEP; ss.
Qed.

Lemma Config_abort_stable
      c c' lo tid
      (ABORT: Configuration.is_abort (Configuration.sw_tid c' tid) lo)
      (SC_EQ: Configuration.sc c = Configuration.sc c')
      (MEM_EQ: Configuration.memory c = Configuration.memory c')
      (TH_EQ: IdentMap.find tid (Configuration.threads c) =
                IdentMap.find tid (Configuration.threads c')):
  Configuration.is_abort (Configuration.sw_tid c tid) lo.
Proof.
  inv ABORT. des.
  destruct c, c'; ss.
  unfold Configuration.sw_tid in *; ss. subst.
  econs; eauto; ss.
  rewrite <- TH_EQ in H.
  exists st1 lc1 e'.
  split; eauto.
Qed.

Lemma Config_na_fulfill_prc_reordering_in_same_thread
      lo c c0 c1
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c0)
      (PRC_STEP: Configuration.aux_step AuxEvent.prc lo c0 c1):
  exists c',
    Configuration.aux_step AuxEvent.prc lo c c'
    /\ Config_na_fulfill_step lo c' c1.
Proof.
  inv NA_FULFILL_STEP.
  destruct c; ss.
  inv PRC_STEP; ss.
  destruct c1; ss. inv C2.
  eapply rtc_rtcn in STEPS. des.
  eapply rtc_rtcn in STEPS0. des.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  clear STEPS STEP. introv NA_STEPS.
  exploit rtcn_n1; [eapply STEPS0 | eapply STEP0 | eauto..].
  clear STEPS0 STEP0. introv PRC_STEPS.
  rewrite IdentMap.gss in TID1.
  inv TID1. eapply inj_pair2 in H1. subst.
  exploit reorder_na_fulfill_steps_prc_steps; eauto.
  ii; des.
  clear NA_STEPS PRC_STEPS.
  lets CONSISTENT': CONSISTENT0.
  eapply consistency_forward_na_steps in CONSISTENT'; eauto.
  exists (Configuration.mk (IdentMap.add tid (existT _ lang0 st0, lc0) threads) tid sc0 memory0).
  eapply rtcn_tail in x0. des.
  eapply rtcn_tail in x1. des.

  destruct a0.
  split.
  econs.
  eauto.
  ss. eauto. ss. eapply rtcn_rtc in x0. eapply x0. ss. eapply x2.
  ss.
  ss.
  econs.
  eauto.
  ss. rewrite IdentMap.gss; eauto.
  ss. eapply rtcn_rtc in x1. eapply x1.
  ss. eapply x3.
  ss.
  ss.
  rewrite IdentMap.add_add_eq.
  rewrite IdentMap.add_add_eq.
  eauto.
Qed.

Lemma Config_na_prc_reordering_in_same_thread
      lo c c0 c1
      (NA_STEP: Configuration.aux_step AuxEvent.na lo c c0)
      (PRC_STEP: Configuration.aux_step AuxEvent.prc lo c0 c1):
  exists c',
    Configuration.aux_step AuxEvent.prc lo c c'
    /\ Config_na_fulfill_step lo c' c1.
Proof.
  inv NA_STEP.
  destruct c, c0; ss. inv C2.
  inv PRC_STEP; ss.
  destruct c1; ss. inv C2; ss.
  eapply rtc_rtcn in STEPS. des.
  eapply rtc_rtcn in STEPS0. des.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  clear STEPS STEP. introv NA_STEPS.
  exploit rtcn_n1; [eapply STEPS0 | eapply STEP0 | eauto..].
  clear STEPS0 STEP0. introv PRC_STEPS.
  eapply promises_forward_na_steps in NA_STEPS.
  des; subst.
  rewrite IdentMap.gss in TID0.
  inv TID0. eapply inj_pair2 in H1. subst.
  exploit reorder_na_fulfill_steps_prc_steps; eauto.
  ii; des.
  lets CONSISTENT': CONSISTENT0.
  eapply consistency_forward_na_steps in CONSISTENT'; eauto.
  rewrite IdentMap.add_add_eq.
  eapply rtcn_tail in x1. des. 
  clear - TID1 NA_STEPS x0 x1 x2 CONSISTENT' CONSISTENT0.
  eapply rtcn_tail in x0. des.
  eapply rtcn_rtc in x0.
  exists (Configuration.mk (IdentMap.add tid (existT _ lang0 st2, lc2) threads) tid sc1 memory1). 
  split.
  econs.
  eauto. ss. eauto. ss.
  eapply rtc_compose. eapply NA_STEPS. eapply x0.
  ss. eapply x3.
  ss. ss.
  destruct a2.
  econs.
  eauto.
  ss. rewrite IdentMap.gss; eauto.
  ss. eapply rtcn_rtc in x1. eapply x1.
  ss. eapply x2.
  ss.
  ss. rewrite IdentMap.add_add_eq; eauto.
Qed.

Lemma Memory_promise_memory_get
      prom mem loc0 from0 to0 msg prom' mem' kind
      loc to from val R
      (PROMISE: Memory.promise prom mem loc0 from0 to0 msg prom' mem' kind)
      (GET: Memory.get loc to mem = Some (from, Message.concrete val R)):
  exists from' R',
    Memory.get loc to mem' = Some (from', Message.concrete val R')
    /\ View.opt_le R' R.
Proof.
  inv PROMISE; eauto.
  exploit Memory.add_get1; eauto.
  ii. exists from R. split; eauto.
  eapply View.View.opt_le_PreOrder_obligation_1.
  des; subst.
  exploit Memory.split_get1; eauto.
  ii; des.
  exists f' R. split; eauto.
  eapply View.View.opt_le_PreOrder_obligation_1.
  des; subst.
  exploit Memory.lower_get1; [eapply MEM | eauto..].
  ii; des. inv MSG_LE.
  exists from released0. split; eauto.
  exploit Memory.remove_get1; [eapply MEM | eauto..].
  ii; des; subst.
  exploit Memory.remove_get0; [eapply MEM | eauto..].
  ii; des.
  rewrite GET in GET0. ss.
  exists from R.
  split; eauto.
  eapply View.View.opt_le_PreOrder_obligation_1.
Qed.
  
Lemma Thread_step_prsv_memory_get
      lang lo pf te
      st lc sc mem st' lc' sc' mem'
      loc to from val R
      (STEP: Thread.step lo pf te
                         (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (GET: Memory.get loc to mem = Some (from, Message.concrete val R)):
  exists from' R',
    Memory.get loc to mem' = Some (from', Message.concrete val R')
    /\ View.opt_le R' R.
Proof.
  inv STEP.
  - inv STEP0.
    inv LOCAL.
    eapply Memory_promise_memory_get; eauto.
  - inv STEP0. inv LOCAL; ss; eauto;
      try solve [do 2 eexists; split; eauto;
                 eapply View.View.opt_le_PreOrder_obligation_1].
    inv LOCAL0. inv WRITE.
    eapply Memory_promise_memory_get; eauto.
    inv LOCAL2. inv WRITE.
    eapply Memory_promise_memory_get; eauto.
Qed.

(** Single steps reordering in different threads **)
Lemma na_fulfill_step_thread_prog_step_reorering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2 te
      ths tid
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (PROG_STEP: Thread.program_step te lo
                                      (Thread.mk lang2 st2 lc2 sc mem)
                                      (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)):
  Thread.program_step te lo
                      (Thread.mk lang2 st2 lc2 sc mem)
                      (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  exploit wf_config_thread_step_prsv.
  eapply WF_CONFIG. eapply TH2.
  econs. econs. eapply Thread.step_program; eauto.
  introv WF_CONFIG'.

  assert (LOCAL_WF_TID1: Local.wf lc1 mem).
  {
    eapply wf_config_to_local_wf; eauto.
  }
  assert (LOCAL_WF_TID1': Local.wf lc1 mem').
  {
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := tid1).
    rewrite IdentMap.gso; eauto.
  }
  assert (MEM_GE_WEAK: 
           forall loc to from val R,
             Memory.get loc to mem = Some (from, Message.concrete val R) ->
             exists from' R',
               Memory.get loc to mem' = Some (from', Message.concrete val R')
               /\ View.opt_le R' R).
  {
    ii.
    eapply Thread_step_prsv_memory_get; eauto.
  }

  split; eauto.
  clear - NA_FULFILL_STEP LOCAL_WF_TID1 LOCAL_WF_TID1' MEM_GE_WEAK.
  inv NA_FULFILL_STEP.
  - (* write *)
    inv FULFILL.
    exploit Memory.remove_get0; eauto.
    ii; des.
    inv LOCAL_WF_TID1'.
    exploit PROMISES; eauto. ii.
    econs; eauto.
    unfold TView.write_tview in *; ss.
    econs; eauto.
    inv WRITABLE. econs; eauto.
  - (* read *)
    inv NA_READ.
    exploit MEM_GE_WEAK; eauto.
    ii; des.
    eapply na_fulfill_step_read; eauto.
    econs; eauto.
    inv READABLE.
    econs; eauto.
  - (* silent *)
    eapply na_fulfill_step_silent; eauto.
Qed.
    
Lemma na_fulfill_step_thread_step_reordering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2 pf te
      ths tid
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (STEP: Thread.step lo pf te
                         (Thread.mk lang2 st2 lc2 sc mem)
                         (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)):
  Thread.step lo pf te
              (Thread.mk lang2 st2 lc2 sc mem)
              (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  exploit wf_config_thread_step_prsv.
  eapply WF_CONFIG. eapply TH2.
  econs. econs. eapply STEP.
  introv WF_CONFIG'.

  assert (LOCAL_WF_TID1: Local.wf lc1 mem).
  {
    eapply wf_config_to_local_wf; eauto.
  }
  assert (LOCAL_WF_TID1': Local.wf lc1 mem').
  {
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := tid1).
    rewrite IdentMap.gso; eauto.
  }
  assert (MEM_GE_WEAK: 
           forall loc to from val R,
             Memory.get loc to mem = Some (from, Message.concrete val R) ->
             exists from' R',
               Memory.get loc to mem' = Some (from', Message.concrete val R')
               /\ View.opt_le R' R).
  {
    ii.
    eapply Thread_step_prsv_memory_get; eauto.
  }

  split; eauto.
  clear - NA_FULFILL_STEP LOCAL_WF_TID1 LOCAL_WF_TID1' MEM_GE_WEAK.
  inv NA_FULFILL_STEP.
  - (* write *)
    inv FULFILL.
    exploit Memory.remove_get0; eauto.
    ii; des.
    inv LOCAL_WF_TID1'.
    exploit PROMISES; eauto. ii.
    econs; eauto.
    unfold TView.write_tview in *; ss.
    econs; eauto.
    inv WRITABLE. econs; eauto.
  - (* read *)
    inv NA_READ.
    exploit MEM_GE_WEAK; eauto.
    ii; des.
    eapply na_fulfill_step_read; eauto.
    econs; eauto.
    inv READABLE.
    econs; eauto.
  - (* silent *)
    eapply na_fulfill_step_silent; eauto.
Qed.

Lemma na_fulfill_step_prc_step_reordering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2 
      ths tid
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (STEP: Thread.prc_step lo (Thread.mk lang2 st2 lc2 sc mem)
                             (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)):
  Thread.prc_step lo (Thread.mk lang2 st2 lc2 sc mem)
                  (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  inv STEP.
  assert (THRD_STEP: Thread.step lo pf (ThreadEvent.promise loc from to msg kind)
                                 (Thread.mk lang2 st2 lc2 sc mem)
                                 (Thread.mk lang2 st2' lc2' sc' mem')).
  {
    econs; eauto.
  }
  exploit na_fulfill_step_thread_step_reordering_in_diff_threads;
    [eapply TH1 | eapply NA_FULFILL_STEP |
      eapply TH2 | eapply THRD_STEP | eapply DIF_TID | eapply WF_CONFIG | eauto..].
  ii; des.
  inv x0; ss.
  split; eauto. econs; eauto.
  clear - STEP.
  inv STEP. inv LOCAL; ss.
Qed.

Lemma na_fulfill_step_na_step_reordering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2 
      ths tid
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (STEP: Thread.na_step lo (Thread.mk lang2 st2 lc2 sc mem)
                            (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)):
  Thread.na_step lo (Thread.mk lang2 st2 lc2 sc mem)
                 (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  inv STEP.
  - (* read *)
    assert (SC_MEM_EQ: sc = sc' /\ mem = mem').
    {
      inv STEP0. inv LOCAL. eauto.
    }
    des; subst.
    split; eauto.
    eapply Thread.na_plain_read_step_intro; eauto.
  - (* write *)
    assert (THRD_STEP: Thread.step lo true (ThreadEvent.write loc from to v R Ordering.plain)
                                   (Thread.mk lang2 st2 lc2 sc mem)
                                   (Thread.mk lang2 st2' lc2' sc' mem')).
    {
      eapply Thread.step_program; eauto.
    }
    exploit na_fulfill_step_thread_step_reordering_in_diff_threads;
    [eapply TH1 | eapply NA_FULFILL_STEP |
      eapply TH2 | eapply THRD_STEP | eapply DIF_TID | eapply WF_CONFIG | eauto..].
    ii; des.
    inv x0; ss. inv STEP; ss.
    split; eauto.
    eapply Thread.na_plain_write_step_intro; eauto.
  - (* silent *)
    assert (SC_MEM_EQ: sc = sc' /\ mem = mem').
    {
      inv STEP0. inv LOCAL. eauto.
    }
    des; subst.
    split; eauto.
    eapply Thread.na_tau_step_intro; eauto.
Qed. 

Lemma na_fulfill_step_output_step_reordering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2 e
      ths
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (STEP: Thread.out_step lo e (Thread.mk lang2 st2 lc2 sc mem)
                             (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2):
  Thread.out_step lo e (Thread.mk lang2 st2 lc2 sc mem)
                  (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  split; eauto.
  eapply na_fulfill_step_mem_ge; eauto.
  inv STEP. inv OUT; ss. inv LOCAL; ss.
Qed.

Lemma na_fulfill_step_at_step_reordering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2 
      ths tid
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (STEP: Thread.at_step lo (Thread.mk lang2 st2 lc2 sc mem)
                            (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)):
  Thread.at_step lo (Thread.mk lang2 st2 lc2 sc mem)
                 (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  inv STEP. des.    
  - inv AT_STEP.
    exploit na_fulfill_step_thread_prog_step_reorering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP | eapply TH2 | eapply STEP | eapply DIF_TID | eauto..].
    ii; des; eauto. split; eauto. econs; eauto.
    left. econs; eauto.
  - inv AT_STEP.
    exploit na_fulfill_step_thread_prog_step_reorering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP | eapply TH2 | eapply STEP | eapply DIF_TID | eauto..].
    ii; des; eauto. split; eauto. econs; eauto.
    right. left. econs; eauto.
  - inv AT_STEP.
    exploit na_fulfill_step_thread_prog_step_reorering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP | eapply TH2 | eapply STEP | eapply DIF_TID | eauto..].
    ii; des; eauto. split; eauto. econs; eauto.
    do 2 right. left. econs; eauto.
  - inv AT_STEP.
    exploit na_fulfill_step_thread_prog_step_reorering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP | eapply TH2 | eapply STEP | eapply DIF_TID | eauto..].
    ii; des; eauto. split; eauto. econs; eauto.
    do 3 right. econs; eauto.
Qed.
  
(** single step / multiply steps reordering in different threads **)
Lemma na_fulfill_step_prc_steps_reordering_in_diff_threads:
  forall n lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2
    ths tid
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (PRC_STEPS: rtcn (Thread.prc_step lo) n
                     (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    rtcn (Thread.prc_step lo) n
         (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem')
    /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  induction n; ii.
  - inv PRC_STEPS. split; eauto.
  - inv PRC_STEPS.
    destruct a2.
    
    exploit wf_config_thread_step_prsv.
    eapply WF_CONFIG.
    eauto.
    eapply prc_step_is_tau_step in A12.
    eapply Thread_tau_step_is_all_step in A12.
    eapply A12.
    introv WF_CONFIG'.

    exploit na_fulfill_step_prc_step_reordering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP |
        eapply TH2 | eapply A12 | eapply DIF_TID | eapply WF_CONFIG | eauto..].
    ii; des.
    exploit IHn; [| eapply x1 | | eapply A23 | eapply DIF_TID | eapply WF_CONFIG' | eauto..].
    rewrite IdentMap.gso; eauto.
    rewrite IdentMap.gss; eauto.
    ii; des.
    split; eauto.
Qed.

Lemma na_fulfill_step_na_steps_reordering_in_diff_threads:
  forall n lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2
    ths tid
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (NA_STEPS: rtcn (Thread.na_step lo) n
                    (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    rtcn (Thread.na_step lo) n
         (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem')
    /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  induction n; ii.
  - inv NA_STEPS. split; eauto.
  - inv NA_STEPS. destruct a2.

    exploit wf_config_thread_step_prsv.
    eapply WF_CONFIG.
    eauto.
    eapply na_step_is_tau_step in A12.
    eapply Thread_tau_step_is_all_step in A12.
    eapply A12.
    introv WF_CONFIG'.

    exploit na_fulfill_step_na_step_reordering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP |
        eapply TH2 | eapply A12 | eapply DIF_TID | eapply WF_CONFIG | eauto..].
    ii; des.
    exploit IHn; [| eapply x1 | | eapply A23 | eapply DIF_TID | eapply WF_CONFIG' | eauto..].
    rewrite IdentMap.gso; eauto.
    rewrite IdentMap.gss; eauto.
    ii; des.
    split; eauto.
Qed.

Lemma na_fulfill_step_atmblk_step_reordering_in_diff_threads
      lo sc mem sc' mem'
      lang1 st1 lc1 st1' lc1' tid1
      lang2 st2 lc2 st2' lc2' tid2
      ths tid
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (ATM_STEPS: Thread.atmblk_step lo (Thread.mk lang2 st2 lc2 sc mem)
                                     (Thread.mk lang2 st2' lc2' sc' mem'))
      (DIF_TID: tid1 <> tid2)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)):
  Thread.atmblk_step lo (Thread.mk lang2 st2 lc2 sc mem)
                     (Thread.mk lang2 st2' lc2' sc' mem')
  /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  split; eauto.
  inv ATM_STEPS. des; ss.
  destruct x, e''.
  assert (WF_CONFIG': Configuration.wf
                        (Configuration.mk
                           (IdentMap.add tid2 (existT _ lang2 state, local) ths) tid sc0 memory)).
  {
    eapply wf_config_rtc_thread_steps_prsv.
    eapply WF_CONFIG.
    eauto. eapply na_steps_is_tau_steps in NA_STEPS.
    eapply Thread_tau_steps_is_all_steps in NA_STEPS.
    eapply NA_STEPS.
  }
  assert (WF_CONFIG'': Configuration.wf
                         (Configuration.mk
                            (IdentMap.add tid2 (existT _ lang2 state0, local0) ths) tid sc1 memory0)).
  {
    eapply wf_config_thread_step_prsv in WF_CONFIG'.
    instantiate (6 := tid2) in WF_CONFIG'.
    rewrite IdentMap.add_add_eq in WF_CONFIG'. eauto.
    rewrite IdentMap.gss; eauto.
    eapply at_step_is_tau_step in AT_STEP.
    eapply Thread_tau_step_is_all_step in AT_STEP. eapply AT_STEP.
  }

  eapply rtc_rtcn in NA_STEPS. des.
  eapply rtc_rtcn in PRC_STEPS. des.

  exploit na_fulfill_step_na_steps_reordering_in_diff_threads;
    [| eapply NA_FULFILL_STEP | | eapply NA_STEPS | eapply DIF_TID | eapply WF_CONFIG | eauto..]; eauto.
  ii; des. clear NA_FULFILL_STEP NA_STEPS.
  
  exploit na_fulfill_step_at_step_reordering_in_diff_threads;
    [| eapply x1 | | eapply AT_STEP | eapply DIF_TID | eapply WF_CONFIG' | eauto..]; eauto.
  rewrite IdentMap.gso; eauto.
  rewrite IdentMap.gss; eauto.
  ii; des. clear x1 AT_STEP.

  exploit na_fulfill_step_prc_steps_reordering_in_diff_threads;
    [| eapply x3 | | eapply PRC_STEPS | eapply DIF_TID | eapply WF_CONFIG'' | eauto..]; eauto.
  rewrite IdentMap.gso; eauto.
  rewrite IdentMap.gss; eauto.

  ii; des; eauto.
Qed.
  
Lemma na_fulfill_step_atmblk_steps_reordering_in_diff_threads:
  forall n lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2
    ths tid
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (ATM_STEPS: rtcn (Thread.atmblk_step lo) n
                     (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    rtcn (Thread.atmblk_step lo) n
         (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem')
    /\ na_fulfill_step lo sc' mem' (st1, lc1) (st1', lc1').
Proof.
  induction n; ii.
  - inv ATM_STEPS.
    split; eauto.
  - inv ATM_STEPS.
    destruct a2.
    exploit na_fulfill_step_atmblk_step_reordering_in_diff_threads;
      [eapply TH1 | eapply NA_FULFILL_STEP | eapply TH2 | eapply A12 | eapply DIF_TID | eauto..].
    ii; des.
    clear NA_FULFILL_STEP A12.
 
    assert (WF_CONFIG': Configuration.wf
                          (Configuration.mk (IdentMap.add tid2 (existT _ lang2 state, local) ths) tid sc0 memory)).
    {
      clear - WF_CONFIG x0 TH1 TH2.
      inv x0; ss. des; ss.
      eapply wf_config_rtc_thread_steps_prsv.
      eapply WF_CONFIG. eauto.
      eapply na_steps_is_tau_steps in NA_STEPS.
      eapply Thread_tau_steps_is_all_steps in NA_STEPS.
      eapply at_step_is_tau_step in AT_STEP.
      eapply Thread_tau_step_is_all_step in AT_STEP.
      eapply prc_steps_is_tau_steps in PRC_STEPS.
      eapply Thread_tau_steps_is_all_steps in PRC_STEPS.
      eapply rtc_compose. eapply NA_STEPS.
      eapply Relation_Operators.rt1n_trans.
      eapply AT_STEP. eapply PRC_STEPS.
    }

    exploit IHn;
      [| eapply x1 | | eapply A23 | eapply DIF_TID | eapply WF_CONFIG' | eauto..].
    rewrite IdentMap.gso; eauto.
    rewrite IdentMap.gss; eauto.
    ii; des. clear A23 x1.
    split; eauto.
Qed.

(** multiply steps/ multiply steps reordering in different threads **)
Lemma na_fulfill_steps_prc_steps_reordering_in_diff_threads:
  forall n1 n2 lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2
    ths tid
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEPS: rtcn (na_fulfill_step lo sc mem) n1 (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (PRC_STEPS: rtcn (Thread.prc_step lo) n2
                     (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    rtcn (Thread.prc_step lo) n2
         (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem')
    /\ rtcn (na_fulfill_step lo sc' mem') n1 (st1, lc1) (st1', lc1').
Proof.
  induction n1; ii.
  - inv NA_FULFILL_STEPS. eauto.
  - inv NA_FULFILL_STEPS. destruct a2.
    exploit wf_config_thread_step_prsv.
    eapply WF_CONFIG. eapply TH1.
    eapply na_fulfill_step_to_na_step in A12.
    eapply na_step_is_tau_step in A12.
    eapply Thread_tau_step_is_all_step in A12.
    eapply A12.
    introv WF_CONFIG'.
    exploit IHn1; [ | eapply A23 | | eapply PRC_STEPS | eapply DIF_TID | eapply WF_CONFIG' | eauto..].
    rewrite IdentMap.gss; eauto.
    rewrite IdentMap.gso; eauto.
    ii; des.
    split; eauto.
    exploit na_fulfill_step_prc_steps_reordering_in_diff_threads;
      [eapply TH1 | eapply A12 | eapply TH2 | eapply x | eauto..].
    ii; des.
    eauto.
Qed.

Lemma na_fulfill_steps_na_steps_reordering_in_diff_threads:
  forall n1 n2 lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2
    ths tid
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEPS: rtcn (na_fulfill_step lo sc mem) n1 (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (NA_STEPS: rtcn (Thread.na_step lo) n2
                    (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    rtcn (Thread.na_step lo) n2
         (Thread.mk lang2 st2 lc2 sc mem) (Thread.mk lang2 st2' lc2' sc' mem')
    /\ rtcn (na_fulfill_step lo sc' mem') n1 (st1, lc1) (st1', lc1').
Proof.
  induction n1; ii.
  - inv NA_FULFILL_STEPS. eauto.
  - inv NA_FULFILL_STEPS. destruct a2.
    exploit wf_config_thread_step_prsv.
    eapply WF_CONFIG. eapply TH1.
    eapply na_fulfill_step_to_na_step in A12.
    eapply na_step_is_tau_step in A12.
    eapply Thread_tau_step_is_all_step in A12.
    eapply A12.
    introv WF_CONFIG'.
    exploit IHn1; [ | eapply A23 | | eapply NA_STEPS | eapply DIF_TID | eapply WF_CONFIG' | eauto..].
    rewrite IdentMap.gss; eauto.
    rewrite IdentMap.gso; eauto.
    ii; des.
    split; eauto.
    exploit na_fulfill_step_na_steps_reordering_in_diff_threads;
      [eapply TH1 | eapply A12 | eapply TH2 | eapply x | eauto..].
    ii; des.
    eauto.
Qed.

Lemma na_fulfill_steps_output_steps_reordering_in_diff_threads:
  forall n1 lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2 e
    ths
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEPS: rtcn (na_fulfill_step lo sc mem) n1 (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (OUT_STEPS: Thread.out_step lo e 
                                (Thread.mk lang2 st2 lc2 sc mem)
                                (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2),
    Thread.out_step lo e
                    (Thread.mk lang2 st2 lc2 sc mem)
                    (Thread.mk lang2 st2' lc2' sc' mem')
    /\ rtcn (na_fulfill_step lo sc' mem') n1 (st1, lc1) (st1', lc1').
Proof.
  induction n1; ii.
  - split; eauto.
    inv NA_FULFILL_STEPS. eauto.
  - split; eauto.
    inv NA_FULFILL_STEPS. destruct a2.
    exploit IHn1; [ | eapply A23 | | eapply OUT_STEPS | eapply DIF_TID | eauto..].
    instantiate (1 := IdentMap.add tid1 (existT _ lang1 s, t) ths).
    rewrite IdentMap.gss; eauto.
    rewrite IdentMap.gso; eauto.
    exploit na_fulfill_step_output_step_reordering_in_diff_threads;
      [eapply TH1 | eapply A12 | eapply TH2 | eapply OUT_STEPS | eauto..].
    ii; des.
    eauto.
Qed.

Lemma na_fulfill_steps_atmblk_steps_reordering_in_diff_threads:
  forall n1 n2 lo sc mem sc' mem'
    lang1 st1 lc1 st1' lc1' tid1
    lang2 st2 lc2 st2' lc2' tid2
    ths tid
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (NA_FULFILL_STEPS: rtcn (na_fulfill_step lo sc mem) n1 (st1, lc1) (st1', lc1'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (ATM_STEPS: rtcn (Thread.atmblk_step lo) n2
                     (Thread.mk lang2 st2 lc2 sc mem)
                     (Thread.mk lang2 st2' lc2' sc' mem'))
    (DIF_TID: tid1 <> tid2)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    rtcn (Thread.atmblk_step lo) n2
         (Thread.mk lang2 st2 lc2 sc mem)
         (Thread.mk lang2 st2' lc2' sc' mem')
    /\ rtcn (na_fulfill_step lo sc' mem') n1 (st1, lc1) (st1', lc1').
Proof.
  induction n1; ii.
  - inv NA_FULFILL_STEPS. split; eauto.
  - inv NA_FULFILL_STEPS. destruct a2.
    assert (WF_CONFIG': Configuration.wf
                          (Configuration.mk (IdentMap.add tid1 (existT _ lang1 s, t) ths) tid sc mem)).
    {
      eapply na_fulfill_step_to_na_step in A12.
      eapply na_step_is_tau_step in A12.
      eapply Thread_tau_step_is_all_step in A12.
      eapply wf_config_thread_step_prsv; eauto.
    }

    exploit IHn1;
      [| eapply A23 | | eapply ATM_STEPS | eapply DIF_TID | eapply WF_CONFIG' | eauto..].
    rewrite IdentMap.gss; eauto.
    rewrite IdentMap.gso; eauto.
    ii; des.

    exploit na_fulfill_step_atmblk_steps_reordering_in_diff_threads;
      [eapply TH1 | eapply A12 | eapply TH2 | eapply x | eapply DIF_TID | eauto..].
    ii; des.
    split; eauto.
Qed.
  
(** Configuration aux steps reordering **)
Lemma Config_na_fulfill_prc_reordering_in_diff_threads
      lo c c1 c2 tid1
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c1)
      (PRC_STEP: Configuration.aux_step AuxEvent.prc lo
                                        (Configuration.sw_tid c1 tid1) c2)
      (DIF_TID: tid1 <> Configuration.tid c1)
      (WF_CONFIG: Configuration.wf c):
  exists c' tid,
    Configuration.aux_step AuxEvent.prc lo (Configuration.sw_tid c tid1) c'
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c' tid)
                             (Configuration.sw_tid c2 tid)
    /\ Configuration.tid c = tid.
Proof.
  destruct c, c1, c2; ss.
  inv NA_FULFILL_STEP; ss. inv C2.
  unfold Configuration.sw_tid in *; ss.
  inv PRC_STEP; ss. inv C2.
  rewrite IdentMap.gso in TID1; eauto.
  eapply rtc_rtcn in STEPS. des.
  eapply rtc_rtcn in STEPS0. des.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  introv NA_STEPS. clear STEPS STEP.
  exploit rtcn_n1; [eapply STEPS0 | eapply STEP0 | eauto..].
  introv PRC_STEPS. clear STEPS0 STEP0.

  exploit wf_config_rtc_thread_steps_prsv.
  eapply WF_CONFIG.
  eapply TH.
  eapply na_fulfill_steps_to_na_steps in NA_STEPS.
  eapply rtcn_rtc in NA_STEPS.
  eapply na_steps_is_tau_steps in NA_STEPS.
  eapply Thread_tau_steps_is_all_steps in NA_STEPS.
  eapply NA_STEPS.
  introv WF_CONFIG'.

  assert (CONSISTENT': Thread.consistent (Thread.mk lang st'' lc'' sc1 memory1) lo).
  {
    eapply Thread_consistent_to_consistent_nprm in CONSISTENT; eauto; ss.
    eapply Thread_consistent_nprm_to_consistent.
    eapply rtcn_rtc in PRC_STEPS.
    eapply prc_steps_is_tau_steps in PRC_STEPS.
    eapply Thread_tau_steps_is_all_steps in PRC_STEPS.
    eapply promise_certified_envs_stable.
    eapply WF_CONFIG'.
    instantiate (4 := tid1).
    rewrite IdentMap.gso; eauto.
    eapply PRC_STEPS.
    instantiate (1 := tid).
    rewrite IdentMap.gss; eauto.
    eauto.
    eauto.
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := tid). rewrite IdentMap.gss; eauto.
    inv WF_CONFIG'; eauto.
  }

  exploit na_fulfill_steps_prc_steps_reordering_in_diff_threads;
    [ | eapply NA_STEPS | | eapply PRC_STEPS | | eapply WF_CONFIG | eauto..].
  eapply TH.
  eapply TID1.
  eauto.
  ii; des.

  exists (Configuration.mk (IdentMap.add tid1 (existT _ lang0 st2, lc2) threads)
                      tid1 sc1 memory1).
  exists tid.
  ss.
  eapply rtcn_tail in x0. des. destruct a2.
  eapply rtcn_tail in x1. des. destruct a2.

  split.
  econs.
  eauto.
  ss. eauto.
  ss. eapply rtcn_rtc in x0. eapply x0.
  ss. eapply x2.
  ss.
  ss.

  split; eauto.
  econs.
  eauto.
  ss. rewrite IdentMap.gso; eauto.
  ss. eapply rtcn_rtc in x1. eapply x1.
  ss. eapply x3.
  ss.
  ss.
  rewrite IdentMap.add_add; eauto.
Qed.
  
Lemma Config_na_prc_reordering_in_diff_threads
      lo c c0 tid0 c1
      (NA_STEP: Configuration.aux_step AuxEvent.na lo c c0)
      (PRC_STEP: Configuration.aux_step AuxEvent.prc lo
                                        (Configuration.sw_tid c0 tid0) c1)
      (DIF_TID: tid0 <> Configuration.tid c0)
      (WF_CONFIG: Configuration.wf c):
  exists c' c'' tid,
    (c = c' \/ Configuration.aux_step AuxEvent.prc lo c c')
    /\ Configuration.aux_step AuxEvent.prc lo
                             (Configuration.sw_tid c' tid0) c''
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c'' tid)
                             (Configuration.sw_tid c1 tid)
    /\ Configuration.tid c = tid.
Proof.
  eapply Config_na_step_to_na_fulfill_step in NA_STEP.
  des; subst.
  - exploit Config_na_fulfill_prc_reordering_in_diff_threads; eauto.
    {
      clear - WF_CONFIG NA_STEP.
      inv NA_STEP.
      destruct c, c2; ss. inv C2.
      exploit rtc_compose.
      eapply STEPS.
      eapply Operators_Properties.clos_rt1n_step. eapply STEP.
      introv PRC_STEPS.
      eapply prc_steps_is_tau_steps in PRC_STEPS.
      eapply Thread_tau_steps_is_all_steps in PRC_STEPS.
      eapply wf_config_rtc_thread_steps_prsv; eauto.
    }
    ii; des.
    exists c2 c' tid.
    split; eauto.
    split; eauto.
    subst. split; eauto.
    inv NA_STEP.
    destruct c, c2; ss. inv C2; eauto.
  - exploit Config_na_fulfill_prc_reordering_in_diff_threads; eauto.
    ii; des. subst.
    exists c2 c' (Configuration.tid c2).
    split; eauto.
Qed.

Lemma Config_na_fulfill_out_reordering_in_diff_threads
      lo c c1 c2 tid1 e
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c1)
      (OUT_STEP: Configuration.aux_step (AuxEvent.out e) lo
                                        (Configuration.sw_tid c1 tid1) c2)
      (DIF_TID: tid1 <> Configuration.tid c1)
      (WF_CONFIG: Configuration.wf c):
  exists c' tid,
    Configuration.aux_step (AuxEvent.out e) lo (Configuration.sw_tid c tid1) c'
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c' tid)
                             (Configuration.sw_tid c2 tid)
    /\ Configuration.tid c = tid.
Proof.
  destruct c, c1, c2; ss.
  inv NA_FULFILL_STEP; ss. inv C2.
  unfold Configuration.sw_tid in *; ss.
  inv OUT_STEP; ss. inv C2.
  rewrite IdentMap.gso in TID1; eauto.

  eapply rtc_rtcn in STEPS. des.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  introv NA_STEPS. clear STEPS STEP.

  exploit wf_config_rtc_thread_steps_prsv.
  eapply WF_CONFIG.
  eapply TH.
  eapply na_fulfill_steps_to_na_steps in NA_STEPS.
  eapply rtcn_rtc in NA_STEPS.
  eapply na_steps_is_tau_steps in NA_STEPS.
  eapply Thread_tau_steps_is_all_steps in NA_STEPS.
  eapply NA_STEPS.
  introv WF_CONFIG'.

  assert (CONSISTENT': Thread.consistent (Thread.mk lang st'' lc'' sc1 memory1) lo).
  {
    eapply Thread_consistent_to_consistent_nprm in CONSISTENT; eauto; ss.
    eapply Thread_consistent_nprm_to_consistent.
    eapply na_steps_is_tau_steps in STEPS0.
    eapply Thread_tau_steps_is_all_steps in STEPS0.
    eapply out_step_is_all_step in STEP_OUT.
    eapply promise_certified_envs_stable.
    eapply WF_CONFIG'.
    instantiate (4 := tid1).
    rewrite IdentMap.gso; eauto.
    eapply rtc_n1.
    eapply STEPS0. eapply STEP_OUT.
    instantiate (1 := tid).
    rewrite IdentMap.gss; eauto.
    eauto.
    eauto.
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := tid). rewrite IdentMap.gss; eauto.
    inv WF_CONFIG'; eauto.
  }

  eapply rtc_rtcn in STEPS0. des. destruct e1.
  exploit na_fulfill_steps_na_steps_reordering_in_diff_threads;
    [eapply TH | eapply NA_STEPS | eapply TID1 | eapply STEPS0 | eauto..].
  ii; des. clear x0. 
  exploit na_fulfill_steps_output_steps_reordering_in_diff_threads;
    [ | eapply x1 | | eapply STEP_OUT | idtac..].
  instantiate (1 := IdentMap.add tid1 (existT _ lang0 state, local) threads).
  instantiate (1 := tid). rewrite IdentMap.gso; eauto.
  instantiate (1 := tid1). rewrite IdentMap.gss; eauto.
  eauto.

  ii; des.
  exists (Configuration.mk (IdentMap.add tid1 (existT _ lang0 st2, lc2) threads) tid1 sc1 memory1); ss.
  exists tid.
  clear NA_STEPS x1. eapply rtcn_tail in x2. des. destruct a2.

  split.
  econs.
  eauto. eauto.
  ss. eapply rtcn_rtc in STEPS0. eapply STEPS0.
  ss. eapply x0.
  ss.
  ss.

  split; eauto.
  econs. eauto. ss. rewrite IdentMap.gso; eauto.
  ss. eapply rtcn_rtc in x2. eapply x2.
  ss. eapply x1.
  ss.

  ss. rewrite IdentMap.add_add; eauto.
Qed.

Lemma Config_na_fulfill_atm_reordering_in_diff_threads
      lo c c1 c2 tid1
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c1)
      (ATM_STEP: Configuration.aux_step AuxEvent.atm lo
                                        (Configuration.sw_tid c1 tid1) c2)
      (DIF_TID: tid1 <> Configuration.tid c1)
      (WF_CONFIG: Configuration.wf c):
  exists c' tid,
    Configuration.aux_step AuxEvent.atm lo (Configuration.sw_tid c tid1) c'
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c' tid)
                             (Configuration.sw_tid c2 tid)
    /\ Configuration.tid c = tid.
Proof.
  destruct c, c1, c2; ss.
  inv NA_FULFILL_STEP; ss. inv C2.
  unfold Configuration.sw_tid in *; ss.
  inv ATM_STEP; ss. inv C2.
  rewrite IdentMap.gso in TID1; eauto.

  eapply rtc_rtcn in STEPS. des.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  introv NA_STEPS. clear STEPS STEP.
  eapply rtc_rtcn in STEPS_ATM. des.
  exploit rtcn_n1; [eapply STEPS_ATM | eapply STEP_ATM | eauto..].
  introv ATM_STEPS. clear STEPS_ATM STEP_ATM.

  destruct e1; ss.
  assert (WF_CONFIG': 
           Configuration.wf (Configuration.mk
                               (IdentMap.add tid1 (existT _ lang0 state, local) threads) tid sc0 memory0)).
  {
    eapply wf_config_rtc_thread_steps_prsv.
    eapply WF_CONFIG. eauto.
    eapply prc_steps_is_tau_steps in STEPS_PRC.
    eapply Thread_tau_steps_is_all_steps in STEPS_PRC.
    eapply STEPS_PRC.
  }
  assert (WF_CONFIG'': 
           Configuration.wf (Configuration.mk
                               (IdentMap.add tid (existT _ lang st'', lc'') threads) tid sc memory)).
  {
    exploit wf_config_rtc_thread_steps_prsv.
    eapply WF_CONFIG.
    instantiate (4 := tid). eauto.
    eapply na_fulfill_steps_to_na_steps in NA_STEPS.
    eapply rtcn_rtc in NA_STEPS.
    eapply na_steps_is_tau_steps in NA_STEPS.
    eapply Thread_tau_steps_is_all_steps in NA_STEPS.
    eapply NA_STEPS. eauto.
  }

  assert (CONSISTENT': Thread.consistent (Thread.mk lang st'' lc'' sc1 memory1) lo).
  {
    eapply Thread_consistent_to_consistent_nprm in CONSISTENT; eauto; ss.
    eapply Thread_consistent_nprm_to_consistent.
    eapply promise_certified_envs_stable.
    eapply WF_CONFIG''.
    instantiate (4 := tid1). rewrite IdentMap.gso; eauto.
    eapply prc_steps_is_tau_steps in STEPS_PRC.
    eapply Thread_tau_steps_is_all_steps in STEPS_PRC.
    eapply Thread_atmblk_steps_is_tau_steps in ATM_STEPS.
    eapply Thread_tau_steps_is_all_steps in ATM_STEPS.
    eapply rtc_compose. eapply STEPS_PRC. eapply ATM_STEPS.
    instantiate (1 := tid). rewrite IdentMap.gss; eauto.
    eauto. eauto.
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := tid). rewrite IdentMap.gss; eauto.
    inv WF_CONFIG''; ss; eauto.
  }

  eapply rtc_rtcn in STEPS_PRC. des.
  exploit na_fulfill_steps_prc_steps_reordering_in_diff_threads;
    [eapply TH | eapply NA_STEPS | eapply TID1 | eapply STEPS_PRC | eauto..].
  ii; des. clear STEPS_PRC NA_STEPS.
  exploit na_fulfill_steps_atmblk_steps_reordering_in_diff_threads;
    [| eapply x1 | | eapply ATM_STEPS | | eapply WF_CONFIG' | eauto..].
  instantiate (1 := tid).
  rewrite IdentMap.gso; eauto.
  instantiate (1 := tid1). rewrite IdentMap.gss; eauto.
  eauto.

  ii; des. clear ATM_STEPS x1.
  eapply rtcn_tail in x2. des.
  eapply rtcn_tail in x3. des. destruct a0.
  exists (Configuration.mk (IdentMap.add tid1 (existT _ lang0 st2, lc2) threads)
                      tid1 sc1 memory1). ss.
  exists tid.
  split.
  {
    econs.
    eauto.
    ss. eauto.
    ss. eapply rtcn_rtc in x0. eapply x0.
    eapply rtcn_rtc in x2. eapply x2.
    ss. eapply x1.
    ss.
    ss.
  }
  split; eauto.
  {
    econs.
    eauto.
    ss. rewrite IdentMap.gso; eauto.
    ss. eapply rtcn_rtc in x3. eapply x3.
    ss. eapply x4.
    ss.
    ss.
    rewrite IdentMap.add_add; eauto.
  }
Qed.

Lemma Config_na_out_reordering_in_diff_threads
      lo c c0 tid0 c1 e
      (NA_STEP: Configuration.aux_step AuxEvent.na lo c c0)
      (OUT_STEP: Configuration.aux_step (AuxEvent.out e) lo
                                        (Configuration.sw_tid c0 tid0) c1)
      (DIF_TID: tid0 <> Configuration.tid c0)
      (WF_CONFIG: Configuration.wf c):
  exists c' c'' tid,
    (c = c' \/ Configuration.aux_step AuxEvent.prc lo c c')
    /\ Configuration.aux_step (AuxEvent.out e) lo
                             (Configuration.sw_tid c' tid0) c''
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c'' tid)
                             (Configuration.sw_tid c1 tid)
    /\ Configuration.tid c = tid.
Proof.
  eapply Config_na_step_to_na_fulfill_step in NA_STEP.
  des; subst.
  - exploit Config_na_fulfill_out_reordering_in_diff_threads; eauto.
    {
      clear - NA_STEP WF_CONFIG.
      inv NA_STEP. destruct c, c2; ss. inv C2.
      eapply wf_config_rtc_thread_steps_prsv.
      eapply WF_CONFIG.
      eauto.
      eapply prc_steps_is_tau_steps in STEPS.
      eapply Thread_tau_steps_is_all_steps in STEPS.
      eapply prc_step_is_tau_step in STEP.
      eapply Thread_tau_step_is_all_step in STEP.
      eapply rtc_n1. eapply STEPS. eapply STEP.
    }

    ii; des; subst. 
    exists c2 c' (Configuration.tid c).
    split; eauto.
    split; eauto.
    split; eauto.
    assert (TID_EQ: Configuration.tid c = Configuration.tid c2).
    {
      inv NA_STEP. destruct c, c2; ss. inv C2.
      eauto.
    }
    rewrite TID_EQ. eauto.
  - exploit Config_na_fulfill_out_reordering_in_diff_threads; eauto.
    ii; des; subst.
    exists c2 c' (Configuration.tid c2).
    split; eauto.
Qed.

Lemma Config_na_atm_reordering_in_diff_threads
      lo c c0 tid0 c1
      (NA_STEP: Configuration.aux_step AuxEvent.na lo c c0)
      (ATM_STEP: Configuration.aux_step AuxEvent.atm lo
                                        (Configuration.sw_tid c0 tid0) c1)
      (DIF_TID: tid0 <> Configuration.tid c0)
      (WF_CONFIG: Configuration.wf c):
  exists c' c'' tid,
    (c = c' \/ Configuration.aux_step AuxEvent.prc lo c c')
    /\ Configuration.aux_step AuxEvent.atm lo
                             (Configuration.sw_tid c' tid0) c''
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c'' tid)
                             (Configuration.sw_tid c1 tid)
    /\ Configuration.tid c = tid.
Proof.
  eapply Config_na_step_to_na_fulfill_step in NA_STEP.
  des; subst.
  - exploit Config_na_fulfill_atm_reordering_in_diff_threads; eauto.
    {
      clear - NA_STEP WF_CONFIG.
      destruct c, c2; ss. inv NA_STEP; ss. inv C2.
      eapply wf_config_rtc_thread_steps_prsv.
      eapply WF_CONFIG.
      eauto.
      eapply prc_steps_is_tau_steps in STEPS.
      eapply Thread_tau_steps_is_all_steps in STEPS.
      eapply prc_step_is_tau_step in STEP.
      eapply Thread_tau_step_is_all_step in STEP.
      eapply rtc_n1. eapply STEPS. eapply STEP.
    }

    ii; des; subst.
    exists c2 c' (Configuration.tid c).
    split; eauto.
    split; eauto.
    assert (TID_EQ: Configuration.tid c = Configuration.tid c2).
    {
      inv NA_STEP. destruct c, c2; ss. inv C2. eauto.
    }
    rewrite TID_EQ. split; eauto.
  - exploit Config_na_fulfill_atm_reordering_in_diff_threads; eauto.
    ii; des; subst.
    exists c2 c' (Configuration.tid c2).
    split; eauto.
Qed.

Lemma Config_abort_forwarding_na_fulfill_steps
      lo c c' tid'
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c')
      (ABORT: Configuration.is_abort (Configuration.sw_tid c' tid') lo):
  Configuration.is_abort (Configuration.sw_tid c tid') lo.
Proof.
  exploit Config_na_fulfill_step_sc_mem_unchange; eauto.
  ii; des.
  destruct c, c'; ss.
  unfold Configuration.sw_tid in *; ss; subst.
  inv ABORT; ss. des.
  inv NA_FULFILL_STEP; ss.
  inv C2.
  destruct (Loc.eq_dec tid tid'); subst; ss.
  {
    eapply rtc_rtcn in STEPS. des.
    eapply na_fulfill_steps_to_na_steps in STEPS.
    eapply na_fulfill_step_to_na_step in STEP.
    eapply rtcn_rtc in STEPS.
    exploit rtc_compose.
    eapply STEPS.
    eapply Operators_Properties.clos_rt1n_step. eauto.
    introv NA_STEPS. clear STEPS STEP.
    eapply na_steps_is_tau_steps in NA_STEPS.

    rewrite IdentMap.gss in H. inv H. eapply inj_pair2 in H4. subst.
    econs; ss.
    do 3 eexists.
    split; eauto.
    split. 2: eapply H1.
    eapply rtc_compose. eapply NA_STEPS. eapply H0.
  }
  {
    rewrite IdentMap.gso in H; eauto.
    econs; eauto; ss.
    do 3 eexists.
    split; eauto.
  }
Qed.

Lemma Config_na_fulfill_na_reordering_in_diff_threads
      lo c c1 c2 tid1
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c1)
      (NA_STEP: Configuration.aux_step AuxEvent.na lo
                                       (Configuration.sw_tid c1 tid1) c2)
      (DIF_TID: tid1 <> Configuration.tid c1)
      (WF_CONFIG: Configuration.wf c):
  exists c' tid,
    Configuration.aux_step AuxEvent.na lo (Configuration.sw_tid c tid1) c'
    /\ Config_na_fulfill_step lo (Configuration.sw_tid c' tid)
                             (Configuration.sw_tid c2 tid)
    /\ Configuration.tid c = tid.
Proof.
  destruct c, c1, c2; ss.
  unfold Configuration.sw_tid in *; ss.
  inv NA_FULFILL_STEP; ss. inv C2; ss.
  inv NA_STEP; ss. inv C2; ss.
  rewrite IdentMap.gso in TID1; ss.
  exists (Configuration.mk (IdentMap.add tid1 (existT _ lang0 st2, lc2) threads)
                      tid1 sc1 memory1). ss.
  exists tid.
  eapply rtc_rtcn in STEPS. des.
  eapply rtc_rtcn in STEPS0. des.
  exploit rtcn_n1; [eapply STEPS | eapply STEP | eauto..].
  clear STEPS STEP. introv NA_FULFILL_STEPS.
  exploit rtcn_n1; [eapply STEPS0 | eapply STEP0 | eauto..].
  clear STEPS0 STEP0. introv NA_STEPS.
  exploit na_fulfill_steps_na_steps_reordering_in_diff_threads;
    [eapply TH | eapply NA_FULFILL_STEPS | eapply TID1 | eapply NA_STEPS | eauto..].
  ii; des.

  exploit wf_config_rtc_thread_steps_prsv.
  eapply WF_CONFIG.
  eapply TH.
  eapply na_fulfill_steps_to_na_steps in NA_FULFILL_STEPS.
  eapply rtcn_rtc in NA_FULFILL_STEPS.
  eapply na_steps_is_tau_steps in NA_FULFILL_STEPS.
  eapply Thread_tau_steps_is_all_steps in NA_FULFILL_STEPS.
  eapply NA_FULFILL_STEPS.
  introv WF_CONFIG'.

  assert (CONSISTENT': Thread.consistent (Thread.mk lang st'' lc'' sc1 memory1) lo).
  {
    eapply Thread_consistent_to_consistent_nprm in CONSISTENT; eauto; ss.
    eapply Thread_consistent_nprm_to_consistent.
    eapply rtcn_rtc in NA_STEPS.
    eapply na_steps_is_tau_steps in NA_STEPS.
    eapply Thread_tau_steps_is_all_steps in NA_STEPS.
    eapply promise_certified_envs_stable.
    eapply WF_CONFIG'.
    instantiate (4 := tid1).
    rewrite IdentMap.gso; eauto.
    eapply NA_STEPS.
    instantiate (1 := tid).
    rewrite IdentMap.gss; eauto.
    eauto.
    eauto.
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := tid). rewrite IdentMap.gss; eauto.
    inv WF_CONFIG'; eauto.
  }

  eapply rtcn_tail in x0. des.
  eapply rtcn_tail in x1. des.

  split; eauto.
  econs.
  eauto. ss. eauto. ss. eapply rtcn_rtc in x0. eapply x0.
  ss. eapply x2.
  ss.
  ss.

  split; eauto.
  destruct a0.
  econs.
  eauto.
  ss. rewrite IdentMap.gso; eauto.
  ss. eapply rtcn_rtc in x1. eapply x1.
  ss. eapply x3. ss.
  ss.
  rewrite IdentMap.add_add; eauto.
Qed.

Lemma Config_na_tterm_reordering_in_diff_threads
      lo c c' c'' tid'
      (AUX_NA: Configuration.aux_step AuxEvent.na lo c c')
      (AUX_TTERM: Configuration.aux_step AuxEvent.tterm lo (Configuration.sw_tid c' tid') c'')
      (DIF_TID: tid' <> Configuration.tid c):
  exists c0,
    Configuration.aux_step AuxEvent.tterm lo (Configuration.sw_tid c tid') c0
    /\ Configuration.aux_step AuxEvent.na lo
                             (Configuration.sw_tid c0 (Configuration.tid c))
                             (Configuration.sw_tid c'' (Configuration.tid c)).
Proof.
  destruct c, c', c''; ss.
  inv AUX_NA; ss. inv C2.
  inv AUX_TTERM; ss. inv C2.
  rewrite IdentMap.gso in OLD_TID; eauto.
  unfold Configuration.sw_tid; ss.
  destruct (Loc.eq_dec tid'0 tid'); subst; ss.
  rewrite IdentMap.grs in NEW_TID_OK; eauto. ss.
  destruct (Loc.eq_dec tid'0 tid); subst.
  {  
    exists (Configuration.mk (IdentMap.remove tid' threads) tid sc memory). ss.
    rewrite IdentMap.gro in NEW_TID_OK; ss.
    rewrite IdentMap.gss in NEW_TID_OK; ss.
    inv NEW_TID_OK. eapply inj_pair2 in H1. subst.
    split.
    econs; eauto. 
    ss. rewrite IdentMap.gro; eauto.
    econs.
    eauto. ss. rewrite IdentMap.gro; eauto. 
    ss. eapply STEPS.
    ss. eapply STEP.
    ss. ss.
    rewrite IdentMap_remove_add_reorder. eauto.
    eauto.
  }
  { 
    exists (Configuration.mk (IdentMap.remove tid' threads) tid'0 sc memory). ss.
    rewrite IdentMap.gro in NEW_TID_OK; eauto.
    rewrite IdentMap.gso in NEW_TID_OK; eauto.
    split.
    econs; eauto.
    ss. rewrite IdentMap.gro; eauto.
    econs; eauto.
    ss. rewrite IdentMap.gro; eauto.
    ss. rewrite IdentMap_remove_add_reorder; eauto.
  }
Qed.
