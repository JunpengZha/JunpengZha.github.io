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
Require Import Omega.
Require Import FulfillStep.
Require Import WFConfig.
Require Import ConfigStepConvertion.

Set Implicit Arguments.

(** * Semantics equivalence proof *)

(** This file contains the semantics equivalence proof of
    the promising semantics 2.1 (PS2.1) and the non-preemptive semantics. *)

(** Theorem [sema_eq_ps_nps] in this file (Theorem 3.1 in paper) is the final theorem
    that shows the semantics equivalence between PS2.1 and the non-preemptive semantics. *)

(** Theorem [sema_eq_ps_nps] corresponds to the step 5 in Figure 3 (Our proof path)
    in our paper. *)

Definition aux_na_or_sw_step (lo: Ordering.LocOrdMap) (c1 c2:Configuration.t) : Prop:=
  Configuration.aux_step AuxEvent.na lo c1 c2 \/ Configuration.aux_step AuxEvent.sw lo c1 c2.

Lemma aux_na_or_sw_step_th_valid':
  forall n lo c c'
    (AUX_NA_SW: rtcn (aux_na_or_sw_step lo) n c c'),
    (exists tid, Configuration.aux_step AuxEvent.sw lo c (Configuration.sw_tid c tid)
            /\ rtc (aux_na_or_sw_step lo) (Configuration.sw_tid c tid) c')
    \/ c = c'.
Proof.
  induction n; ii.
  - inv AUX_NA_SW; eauto.
  - inv AUX_NA_SW.
    eapply IHn in A23; eauto. des; subst.
    + unfold aux_na_or_sw_step in A12. des.
      {
        lets NA_STEP: A12.
        destruct c, a2; ss. unfold Configuration.sw_tid in *; ss.
        inv NA_STEP; ss. inv C2; ss.
        left. exists tid0.
        split. econs; eauto.
        eapply Relation_Operators.rt1n_trans.
        left. eapply A12.
        eapply Relation_Operators.rt1n_trans.
        right. eapply A23. eauto.
      }
      {
        lets SW_STEP: A23.
        destruct a2; ss. unfold Configuration.sw_tid in *; ss.
        inv SW_STEP; ss. inv C2.
        left.
        exists tid'.
        destruct c; ss. inv A12; ss. inv C2; ss.
        split; eauto.
      }
    + unfold aux_na_or_sw_step in A12. des.
      {
        left.
        exists (Configuration.tid c).
        rewrite <- Configuration.sw_to_self.
        lets NA_STEP: A12.
        destruct c, c'; ss. inv NA_STEP; ss. inv C2.
        split.
        econs; eauto.
        eapply Relation_Operators.rt1n_trans.
        left. eauto. eauto.
      }
      {
        lets SW_STEP: A12.
        destruct c, c'; ss. unfold Configuration.sw_tid in *; ss.
        inv SW_STEP; ss. inv C2.
        left.
        exists tid'.
        split; eauto.
      }
Qed.

Lemma aux_na_or_sw_step_th_valid
      lo c c'
      (AUX_NA_SW: rtc (aux_na_or_sw_step lo) c c'):
  (exists tid, Configuration.aux_step AuxEvent.sw lo c (Configuration.sw_tid c tid)
          /\ rtc (aux_na_or_sw_step lo) (Configuration.sw_tid c tid) c')
  \/ c = c'.
Proof.
  eapply rtc_rtcn in AUX_NA_SW. des.
  eapply aux_na_or_sw_step_th_valid'; eauto.
Qed.

Inductive sw_procs:
  forall (lo:Ordering.LocOrdMap) (c c': Configuration.t) (behs: list VisibleEvent.t) (n: nat), Prop := 
| sw_procs_nil
    c c' lo 
    (AUX_SILENT_STEPS: rtc (@aux_na_or_sw_step lo) c c')
  :
  sw_procs lo c c' nil 0%nat
| sw_procs_done
    c c' lo
    (AUX_SILENT_STEPS: rtc (@aux_na_or_sw_step lo) c c')
    (DONE: Configuration.is_done c')
  :
  sw_procs lo c c' (VisibleEvent.done::nil) 0%nat
| sw_procs_abort
    c c' lo
    (AUX_SILENT_STEPS: rtc (@aux_na_or_sw_step lo) c c')
    (DONE: Configuration.is_abort c' lo)
  :
  sw_procs lo c c' (VisibleEvent.abort::nil) 0%nat
| sw_procs_out
    c c1 c2 c' lo e behs n
    (AUX_SILENT_STEPS: rtc (@aux_na_or_sw_step lo) c c1)
    (OUT_STEP: Configuration.aux_step (AuxEvent.out e) lo c1 c2)
    (SW_N: sw_procs lo c2 c' behs n)
  :
  sw_procs lo c c' ((VisibleEvent.out e)::behs) (S n)
| sw_procs_at 
    c c1 c2 c' lo behs n
    (AUX_SILENT_STEPS: rtc (@aux_na_or_sw_step lo) c c1)
    (AT_PRC_TTERM_STEP: Configuration.aux_step (AuxEvent.atm) lo c1 c2 \/ 
                          Configuration.aux_step (AuxEvent.prc) lo c1 c2 \/ 
                          Configuration.aux_step (AuxEvent.tterm) lo c1 c2)
    (SW_N: sw_procs lo c2 c' behs n)
  : 
  sw_procs lo c c' behs (S n)
.

Lemma sw_procs_merge
      lo c c' c'' behs n
      (AUX_NA_OR_SW_STEPS: rtc (aux_na_or_sw_step lo) c c')
      (SW_PROCS: sw_procs lo c' c'' behs n):
  sw_procs lo c c'' behs n.
Proof.
  inv SW_PROCS;
    try solve [exploit rtc_compose;
               [eapply AUX_NA_OR_SW_STEPS | eauto..];
               introv AUX_NA_OR_SW_STEPS';
               econs; eauto].
Qed.

Inductive NAStep: forall (lo: Ordering.LocOrdMap) (c c':Configuration.t) (n: nat), Prop :=
| na_zero
    lo c c0 c' tid
    (STEP: c = c0 \/
             Configuration.aux_step (AuxEvent.na) lo c c0)
    (SW_TID: Configuration.sw_tid c0 tid = c')
  :
  NAStep lo c c' 0%nat
| na_succ
    lo c c0 c' t0 n
    (STEP: Configuration.aux_step (AuxEvent.na) lo c c0)
    (DIFF_TID: Configuration.tid c0 <> t0)
    (NA: NAStep lo (Configuration.sw_tid c0 t0) c' n)
  :
  NAStep lo c c' (S n)    
.

Lemma NAStep_merge1
      lo c c' c'' n
      (AUX_NA: Configuration.aux_step AuxEvent.na lo c c')
      (NASTEP: NAStep lo c' c'' n):
  NAStep lo c c'' n.
Proof.
  inv NASTEP.
  des; ss; subst.
  econs; eauto.
  exploit Config_aux_na_merge; [eapply AUX_NA | eapply STEP | eauto..].
  ii.
  econs; eauto.
  exploit Config_aux_na_merge; [eapply AUX_NA | eapply STEP | eauto..].
  ii.
  econs; eauto.
Qed.

Lemma NAStep_merge2
      lo c c' c'' n tid'
      (AUX_NA: Configuration.aux_step AuxEvent.na lo c c')
      (NASTEP: NAStep lo (Configuration.sw_tid c' tid') c'' n):
  exists n', NAStep lo c c'' n'.
Proof.
  destruct (Loc.eq_dec (Configuration.tid c') tid'); subst.
  {
    rewrite <- Configuration.sw_to_self in NASTEP.
    exploit NAStep_merge1; eauto.
  }
  {
    exists (S n).
    econs; eauto.
  }
Qed.

Lemma NAStep_to_aux_na_or_sw_steps:
  forall n lo c c' lang st lc
    (NASTEP: NAStep lo c c' n)
    (TH: IdentMap.find (Configuration.tid c') (Configuration.threads c') = Some (existT _ lang st, lc)),
  exists tid' lang' st' lc',
    rtc (aux_na_or_sw_step lo) (Configuration.sw_tid c tid') c'
    /\ IdentMap.find tid' (Configuration.threads c) = Some (existT _ lang' st', lc').
Proof.
  induction n; ii.
  - inv NASTEP.
    des; subst; ss.
    exists tid lang st lc.
    split. eauto. eauto.
    assert (TH1: exists lang' st' lc',
               IdentMap.find (Configuration.tid c) (Configuration.threads c) = Some (existT _ lang' st', lc')).
    {
      destruct c, c1; ss. inv STEP; ss. inv C2; eauto.
    }
    des.
    exists (Configuration.tid c) lang' st' lc'.
    rewrite <- Configuration.sw_to_self.
    split.
    eapply Relation_Operators.rt1n_trans.
    left. eauto.
    eapply Operators_Properties.clos_rt1n_step.
    right. econs; eauto.
    eauto.
  - inv NASTEP.
    eapply IHn in NA; eauto.
    des; ss.
    rewrite Configuration.sw_tid_twice in NA.
    assert (TH1: exists lang' st' lc',
               IdentMap.find (Configuration.tid c) (Configuration.threads c) = Some (existT _ lang' st', lc')).
    {
      destruct c, c1; ss. inv STEP; ss. inv C2; eauto.
    }
    des.
    exists (Configuration.tid c) lang'0 st'0 lc'0.
    rewrite <- Configuration.sw_to_self.
    split.
    eapply Relation_Operators.rt1n_trans.
    left. eauto.
    eapply Relation_Operators.rt1n_trans.
    right.
    econs; eauto.
    destruct c'; ss.
    eauto.
Qed.
  
Inductive PRCStep: forall (lo: Ordering.LocOrdMap) (c c':Configuration.t) (n: nat), Prop :=
| prc_zero
    lo c c0 c' tid
    (STEP: c = c0 \/
             Configuration.aux_step (AuxEvent.prc) lo c c0)
    (SW_TID: Configuration.sw_tid c0 tid = c')
  :
  PRCStep lo c c' 0%nat
| prc_succ
    lo c c0 c' t0 n
    (STEP: Configuration.aux_step (AuxEvent.prc) lo c c0)
    (DIFF_TID: Configuration.tid c0 <> t0)
    (PRC: PRCStep lo (Configuration.sw_tid c0 t0) c' n)
  :
  PRCStep lo c c' (S n)    
. 

Lemma PRCStep_sw:
  forall n lo c c' tid'
    (PRC_STEP: PRCStep lo c c' n),
    PRCStep lo c (Configuration.sw_tid c' tid') n.
Proof.
  induction n; ii.
  - inv PRC_STEP. des; subst.
    econs; eauto.
    rewrite Configuration.sw_tid_twice; eauto.
    econs; eauto.
    rewrite Configuration.sw_tid_twice; eauto.
  - inv PRC_STEP.
    eapply IHn with (tid' := tid') in PRC.
    econs; eauto.
Qed.

Lemma PRCStep_to_NPConf_steps:
  forall n c c' lo lang st lc tid
    (PRC_STEPS: PRCStep lo c c' n)
    (TID_IN: IdentMap.find (Configuration.tid c')
                           (Configuration.threads c') = Some (existT _ lang st, lc))
    (WF_CONFIG: Configuration.wf c),
    rtc (NPConfiguration.tau_step lo)
        (NPConfiguration.mk (Configuration.sw_tid c tid) true)
        (NPConfiguration.mk c' true).
Proof.
  induction n; ii.
  - inv PRC_STEPS.
    des; subst.
    + destruct c1; ss.
      unfold Configuration.sw_tid in *; ss.
      eapply Operators_Properties.clos_rt1n_step.
      econs. 
      eapply NPConfiguration.step_sw; eauto.
      ii; des; ss.
    + destruct c, c1; ss.
      unfold Configuration.sw_tid in *; ss.
      assert (TID1_TH: exists lang st lc,
                 IdentMap.find tid1 threads = Some (existT _ lang st, lc)).
      {
        inv STEP; ss.
        inv C2.
        do 3 eexists.
        eauto.
      }
      des.
      eapply Relation_Operators.rt1n_trans.
      econs.
      eapply NPConfiguration.step_sw; eauto.
      ii; des; ss.

      ss.
      eapply Configuration_aux_prc_step_to_NPConfig_step in STEP; eauto.
      eapply Relation_Operators.rt1n_trans.
      econs. eapply STEP. ii; des; ss.
      eapply Relation_Operators.rt1n_trans.
      2: eauto.
      econs.
      eapply NPConfiguration.step_sw; eauto.
      ii; des; ss.
  - inv PRC_STEPS.
    eapply IHn with (tid := Configuration.tid c1) in PRC; eauto.
    rewrite Configuration.sw_tid_twice in PRC.
    rewrite <- Configuration.sw_to_self in PRC.
    assert (TH: exists lang st lc,
               IdentMap.find (Configuration.tid c) (Configuration.threads c) =
                 Some (existT _ lang st, lc)).
    {
      clear - STEP.
      inv STEP. destruct c, c1; ss. inv C2.
      eauto.
    }
    des.
    eapply Configuration_aux_prc_step_to_NPConfig_step in STEP; eauto.
    eapply Relation_Operators.rt1n_trans.
    econs.
    eapply NPConfiguration.step_sw; eauto.
    ii; des; ss.
    ss.
    destruct c; ss.
    eapply Relation_Operators.rt1n_trans.
    econs. eapply STEP. ii; des; ss.
    eapply PRC.
    clear - WF_CONFIG STEP.
    inv STEP. destruct c, c1; ss. inv C2.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv with (ctid := tid).
    eapply wf_config_rtc_thread_steps_prsv.
    eapply WF_CONFIG. eauto.
    eapply rtc_n1.
    eapply prc_steps_is_tau_steps in STEPS.
    eapply Thread_tau_steps_is_all_steps in STEPS. eapply STEPS.
    eapply prc_step_is_tau_step in STEP0.
    eapply Thread_tau_step_is_all_step in STEP0. eapply STEP0.
Qed.

Lemma wf_config_prc_step_prsv
      c c' lo
      (AUX_PRC: Configuration.aux_step AuxEvent.prc lo c c')
      (WF_CONFIG: Configuration.wf c):
  Configuration.wf c'.
Proof.
  destruct c, c'; ss.
  inv AUX_PRC; ss. inv C2.
  eapply wf_config_rtc_thread_steps_prsv.
  eapply WF_CONFIG.
  eauto.
  eapply prc_steps_is_tau_steps in STEPS.
  eapply Thread_tau_steps_is_all_steps in STEPS.
  eapply prc_step_is_tau_step in STEP.
  eapply Thread_tau_step_is_all_step in STEP.
  eapply rtc_n1. eapply STEPS. eapply STEP.
Qed.

Lemma Config_aux_prc_cons_NPConfig_steps:
  forall n lo c1 c2 tid2 c3 b3 lang st lc
    (AUX_PRC_STEP: Configuration.aux_step AuxEvent.prc lo c1 c2)
    (NP_ALL_STEPS: rtcn (NPConfiguration.all_step lo) n
                        (NPConfiguration.mk (Configuration.sw_tid c2 tid2) true)
                        (NPConfiguration.mk c3 b3))
    (TH: IdentMap.find (Configuration.tid c3) (Configuration.threads c3)
         = Some (existT _ lang st, lc))
    (WF_CONFIG: Configuration.wf c1),
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk c1 true) (NPConfiguration.mk c3 b3).
Proof.
  induction n; ii.
  - inv NP_ALL_STEPS; ss.
    eapply Configuration_aux_prc_step_to_NPConfig_step in AUX_PRC_STEP; eauto.
    eapply Relation_Operators.rt1n_trans.
    econs. eapply AUX_PRC_STEP.
    eapply Operators_Properties.clos_rt1n_step.
    econs. eapply NPConfiguration.step_sw; eauto.
  - inv NP_ALL_STEPS. destruct a2.
    inv A12. destruct e.
    + eapply rtcn_rtc in A23.
      assert (TH': exists lang st lc,
                 IdentMap.find tid2 (Configuration.threads c2) =
                   Some (existT _ lang st, lc)).
      {
        inv H; ss. inv NPC2. eauto.
      }
      des.
      eapply Configuration_aux_prc_step_to_NPConfig_step in AUX_PRC_STEP; eauto.
      
      eapply Relation_Operators.rt1n_trans.
      {
        econs. eapply AUX_PRC_STEP.
      }
      eapply Relation_Operators.rt1n_trans.
      {
        econs. eapply NPConfiguration.step_sw; eauto.
      }
      ss. destruct c2; ss. unfold Configuration.sw_tid in *; ss.
      eapply Relation_Operators.rt1n_trans.
      {
        econs. eapply H.
      }
      eapply A23.
    + inv H; ss.
      {
        inv NPC2.
        exploit IHn; [eapply AUX_PRC_STEP | idtac | eapply TH | eauto..].
        instantiate (1 := tid0).
        clear - A23. destruct c2; ss.
      }
      {
        inv NPC2; ss.
        eapply Configuration_aux_prc_step_to_NPConfig_step in AUX_PRC_STEP; eauto.
        
        eapply Relation_Operators.rt1n_trans.
        {
          econs. eapply AUX_PRC_STEP.
        }
        eapply Relation_Operators.rt1n_trans.
        {
          econs. eapply NPConfiguration.step_sw; eauto.
        }
        ss. destruct c2; ss. unfold Configuration.sw_tid in *; ss.
        eapply Relation_Operators.rt1n_trans.
        {
          econs. eapply NPConfiguration.step_thread_term; eauto.
          ss. eauto.
        }
        ss. eapply rtcn_rtc in A23. eapply A23.
      }
    + eapply rtcn_rtc in A23.
      assert (TH': exists lang st lc,
                 IdentMap.find tid2 (Configuration.threads c2) =
                   Some (existT _ lang st, lc)).
      {
        inv H; ss. inv NPC2. eauto.
      }
      des.
      eapply Configuration_aux_prc_step_to_NPConfig_step in AUX_PRC_STEP; eauto.
      eapply Relation_Operators.rt1n_trans.
      {
        econs. eapply AUX_PRC_STEP.
      }
      eapply Relation_Operators.rt1n_trans.
      {
        econs. eapply NPConfiguration.step_sw; eauto.
      }
      ss. destruct c2; ss. unfold Configuration.sw_tid in *; ss.
      eapply Relation_Operators.rt1n_trans.
      {
        econs. eapply H.
      }
      eapply A23.
Qed.
    
Lemma PRCStep_cons_NPConfig_steps:
  forall n lo c1 c2 c3 b3 lang st lc
    (PRC_STEPS: PRCStep lo c1 c2 n)
    (NP_ALL_STEPS: rtc (NPConfiguration.all_step lo)
                       (NPConfiguration.mk c2 true) (NPConfiguration.mk c3 b3))
    (TH: IdentMap.find (Configuration.tid c3) (Configuration.threads c3) = Some (existT _ lang st, lc))
    (WF_CONFIG: Configuration.wf c1),
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk c1 true) (NPConfiguration.mk c3 b3).
Proof.
  induction n; ii.
  - inv PRC_STEPS.
    des; subst; ss.
    + eapply rtc_rtcn in NP_ALL_STEPS. des.
      eapply NPConfig_steps_sw_tid; eauto.
    + eapply rtc_rtcn in NP_ALL_STEPS. des.
      eapply Config_aux_prc_cons_NPConfig_steps; eauto.
  - inv PRC_STEPS; ss.
    exploit IHn; [eapply PRC | eapply NP_ALL_STEPS | eauto..].
    eapply wf_config_prc_step_prsv in STEP; eauto.
    clear - STEP. destruct c0; ss.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
    introv ALL_STEPS.
    eapply rtc_rtcn in ALL_STEPS. des.
    eapply Config_aux_prc_cons_NPConfig_steps; eauto.
Qed.
   
Lemma wf_config_output_step_prsv
      c c' lo e
      (AUX_OUTPUT: Configuration.aux_step (AuxEvent.out e) lo c c')
      (WF_CONFIG: Configuration.wf c):
  Configuration.wf c'.
Proof.
  inv AUX_OUTPUT.
  destruct c, c'; ss. inv C2; ss.
  eapply na_steps_is_tau_steps in STEPS.
  eapply Thread_tau_steps_is_all_steps in STEPS.
  eapply out_step_is_all_step in STEP_OUT.
  eapply wf_config_rtc_thread_steps_prsv.
  eapply WF_CONFIG.
  eauto.
  eapply rtc_n1. eapply STEPS. eapply STEP_OUT.
Qed.

Lemma wf_config_prc_steps_prsv:
  forall n c c' lo
    (PRC_STEPS: PRCStep lo c c' n)
    (WF_CONFIG: Configuration.wf c),
    Configuration.wf c'.
Proof.
  induction n; ii.
  - inv PRC_STEPS; des; subst.
    destruct c1; ss.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
    exploit wf_config_prc_step_prsv; eauto.
    ii.
    destruct c1; ss.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
  - inv PRC_STEPS.
    exploit wf_config_prc_step_prsv; eauto.
    ii.
    exploit IHn; eauto.
    destruct c1; ss.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
Qed.

Lemma wf_config_ConfigAux_na_step
      lo c c'
      (AUX_NA: Configuration.aux_step AuxEvent.na lo c c')
      (WF_CONFIG: Configuration.wf c):
  Configuration.wf c'.
Proof.
  destruct c, c'; ss.
  inv AUX_NA; ss. inv C2.
  eapply na_steps_is_tau_steps in STEPS.
  eapply Thread_tau_steps_is_all_steps in STEPS.
  eapply na_step_is_tau_step in STEP.
  eapply Thread_tau_step_is_all_step in STEP.
  eapply wf_config_rtc_thread_steps_prsv.
  eapply WF_CONFIG.
  eauto.
  eapply rtc_n1; eauto.
Qed.

Lemma NP_silent_step_cons_NPConf_behav
      lo c c' tid n behs
      (NP_STEP: NPConfiguration.step MachineEvent.silent lo
                                     (NPConfiguration.mk c true)
                                     (NPConfiguration.mk c' true))
      (NP_BEHAV: NPconf_behaviors (NPConfiguration.mk (Configuration.sw_tid c' tid) true) lo n behs):
  exists n', NPconf_behaviors (NPConfiguration.mk c true) lo n' behs.
Proof.
  inv NP_BEHAV.
  {
    exists 1%nat.
    econs; eauto. econs; eauto.
  }
  {
    lets ABORT_STEP: IS_ABORT.
    inv ABORT_STEP; ss. des; subst; ss.
    exists 3%nat. 
    eapply behaviors_tau. left. eauto.
    eapply behaviors_tau. right. econs; eauto.
    ss. econs; eauto.
  }
  {
    lets DONE_STEP: IS_DONE.
    inv DONE_STEP; ss. des; subst; ss.
    exists 3%nat. 
    eapply behaviors_tau. left. eauto.
    eapply behaviors_tau. right. econs; eauto.
    ss. econs; eauto.
  }
  { 
    lets OUTPUT_STEP: STEP.
    inv STEP; ss. des; subst; ss.
    exists (S (S (S n0)))%nat. 
    eapply behaviors_tau. left. eauto.
    eapply behaviors_tau. right. econs; eauto.
    ss. econs; eauto.
  }
  {
    des.
    {
      lets SILENT_STEP: STEP.
      inv STEP; ss. des; subst; ss.
      exists (S (S (S n0)))%nat. 
      eapply behaviors_tau. left. eauto.
      eapply behaviors_tau. right. econs; eauto.
      ss. econs; eauto.
    }
    { 
      lets SWICH_STEP: STEP.
      inv STEP; ss. des; subst; ss.
      exists (S (S n0))%nat. 
      eapply behaviors_tau. left. eauto.
      eapply behaviors_tau. right. econs; eauto.
      ss.

      exists (S (S (S n0)))%nat.
      eapply behaviors_tau. left. eauto.
      eapply behaviors_tau. right. econs; eauto.
      ss. econs; eauto.
    }
  }
Qed.
  
Lemma PRC_steps_cons_NPConf_behav:
  forall n lo c c' n0 behs
    (PRC_STEPS: PRCStep lo c c' n)
    (NP_BEHAV: NPconf_behaviors (NPConfiguration.mk c' true) lo n0 behs)
    (WF_CONFIG: Configuration.wf c),
  exists n0', NPconf_behaviors (NPConfiguration.mk c true) lo n0' behs.
Proof.
  induction n; ii.
  - inv PRC_STEPS. 
    des; subst; ss.
    inv NP_BEHAV. 
    + exists 0%nat. econs; eauto.
    + lets ABORT_STEP: IS_ABORT.
      inv ABORT_STEP; ss. des; subst; ss.
      exists 2%nat.
      eapply behaviors_tau. right. econs; eauto.
      ss. econs; eauto.
    + lets DONE_STEP: IS_DONE.
      inv DONE_STEP; ss. des; subst; ss.
      exists 2%nat.
      eapply behaviors_tau. right. econs; eauto.
      ss. econs; eauto.
    + lets OUTPUT_STEP: STEP.
      inv OUTPUT_STEP; ss. des; subst; ss.
      exists (S (S n)).
      eapply behaviors_tau. right. econs; eauto.
      ss. econs; eauto.
    + des.
      {
        lets SILENT_STEP: STEP.
        inv SILENT_STEP; ss.
        exists (S (S n)).
        eapply behaviors_tau. right. econs; eauto.
        ss. econs; eauto.
      }
      {  
        inv STEP; ss.
        exists (S n). eapply behaviors_tau. right. econs; eauto. ss.
        exists (S (S n)).
        eapply behaviors_tau. right. econs; eauto. ss.
        eapply behaviors_tau. right.
        eapply NPConfiguration.step_thread_term; eauto.
        ss. eauto. ss.
      } 
    + eapply Configuration_aux_prc_step_to_NPConfig_step in STEP; eauto.
      eapply NP_silent_step_cons_NPConf_behav; eauto.
  - inv PRC_STEPS.
    exploit IHn; [eapply PRC | eapply NP_BEHAV | eauto..].
    {
      clear - WF_CONFIG STEP.
      eapply wf_config_prc_step_prsv in STEP; eauto.
      destruct c1; ss.
      unfold Configuration.sw_tid; ss.
      eapply wf_config_sw_prsv; eauto.
    }
    ii; des.
    eapply Configuration_aux_prc_step_to_NPConfig_step in STEP; eauto.
    eapply NP_silent_step_cons_NPConf_behav; eauto.
Qed.
      
Definition aux_any_step (lo: Ordering.LocOrdMap) (c1 c2:Configuration.t): Prop :=
  exists e, Configuration.aux_step e lo c1 c2.

Lemma prefix_tau_np_behav_construct:
  forall n npc npc' lo n0 b
    (TAU_STEPS: rtcn (NPConfiguration.tau_step lo) n npc npc')
    (CONT_BEHAV: NPconf_behaviors npc' lo n0 b), 
  exists n', NPconf_behaviors npc lo n' b.
Proof.
  induction n; intros.
  - inv TAU_STEPS. eauto.
  - inv TAU_STEPS.
    eapply IHn in A23; eauto.
    destruct A23.
    exists (S x). eapply behaviors_tau; eauto.
    inv A12. destruct e; ss; eauto.
    contradiction H1; eauto.
Qed.

(** PS to APS proof *)
Module PS_and_APS.
    Lemma aux_step_to_aux_any_step: 
      forall e lo c1 c2, 
      Configuration.aux_step e lo c1 c2
      -> aux_any_step lo c1 c2.
      Proof.
        intros.
        unfolds aux_any_step.
        exists e. eauto.
      Qed. 

    Lemma thread_full_tau_step_is_na_or_at_or_prc
      lang lo (e1: Thread.t lang) e2 
      (PS_STEP: Thread.tau_step lo e1 e2):
      Thread.na_step lo e1 e2 \/ 
      Thread.atmblk_step lo e1 e2 \/ 
      Thread.prc_step lo e1 e2.
    Proof.
      unfolds Thread.tau_step. 
      inv PS_STEP. inv TSTEP. inv STEP.
      - right; right. 
        inv STEP0.
        eapply Thread.prc_step_intro; eauto.
        eapply Thread.promise_step_intro; eauto.
      - rewrite <- or_assoc. left. 
        eapply thread_tau_step_is_na_or_atmblk_step in STEP0; eauto.
    Qed.

    Lemma out_step_start_consistency {lang:language}:
      forall (ts: Thread.t lang) ts' lo e
        (STEP: Thread.out_step lo e ts ts'),
        Thread.consistent ts lo.
    Proof.
      intros.
      inv STEP. inv OUT. inv LOCAL. inv LOCAL0.
      simpls.
      assert (seqsc_eq: Ordering.seqcst = Ordering.seqcst). {eauto. } apply PROMISES in seqsc_eq. 
      unfolds Thread.consistent. intros. eexists. 
      instantiate (1:= {|Thread.state := st1; Thread.local := lc1; Thread.sc := sc0; Thread.memory := mem1 |}). splits; eauto.  
    Qed.
    
    Lemma rtcn_tail:
      forall A R n 
      (a1 a3:A)
      (REL: rtcn R (S n) a1 a3),
      (exists a2, rtcn R n a1 a2 /\ R a2 a3).
    Proof.
      induction n.
      - intros. exists a1. splits; eauto.
        inv REL. inv A23; eauto. 
      - intros. inv REL.
        eapply IHn in A23.
        destruct A23 as (a2' & STEPS). 
        exists a2'. splits; destruct STEPS as (STEPS & FSTEP); eauto.
    Qed. 

    Lemma AuxThread_nonzero_na_step_is_prc_na_step:
      forall lo lang n ts1 ts2
        (NA_STEPS: rtcn (@Thread.na_step lang lo) (S n) ts1 ts2)
        (CONSISTENCY: Thread.consistent ts2 lo),
        exists ts',
        rtc (@Thread.prc_step lang lo) ts1 ts'/\ Thread.consistent ts' lo 
        /\ rtcn (@Thread.na_step lang lo) (S n) ts' ts2.
    Proof. 
        intros. 
        destruct ts1. destruct ts2. 
        eapply Reordering.promises_forward_na_steps in NA_STEPS.  
        destruct NA_STEPS as (lc' & PRC_STEPS & NA_STEPS).
        des; subst.
        pose proof (consistency_forward_na_steps NA_STEPS) as MID_CONSISTENCY.
        exists {| Thread.state := state; Thread.local := lc'; 
                  Thread.sc := sc0; Thread.memory := memory0 |}. 
        splits; eauto.
        eapply na_fulfill_steps_to_na_steps; eauto.
    Qed.

    Lemma AuxThread_aux_na_step_is_aux_tau_step:
    forall lo c c',
      Configuration.aux_step AuxEvent.na lo c c' 
      -> 
      Configuration.aux_tau_step lo c c'.
    Proof. 
      intros.
      eapply Configuration.aux_tau_step_intro in H; eauto.
      unfolds. intros. destruct H0 as (e0, contra). discriminate.
    Qed.

    Lemma AuxThread_aux_at_step_is_aux_tau_step:
    forall lo c c',
      Configuration.aux_step AuxEvent.atm lo c c' 
      -> 
      Configuration.aux_tau_step lo c c'.
    Proof. 
      intros.
      eapply Configuration.aux_tau_step_intro in H; eauto.
      unfolds. intros. destruct H0 as (e0, contra). discriminate.
    Qed.

    Lemma AuxThread_aux_prc_step_is_aux_tau_step:
    forall lo c c',
      Configuration.aux_step AuxEvent.prc lo c c' 
      -> 
      Configuration.aux_tau_step lo c c'.
    Proof. 
      intros.
      eapply Configuration.aux_tau_step_intro in H; eauto.
      unfolds. intros. destruct H0 as (e0, contra). discriminate.
    Qed.
    
    Lemma ps_to_aps
          lo c c'
          (PS_STEP: Configuration.tau_step lo c c'):
      rtc (Configuration.aux_tau_step lo) c c'.
    Proof.
      (* destruct PS_STEP. *)
      inv PS_STEP.
      inv WP_STEP.
      - (** tau step*)
        eapply rtc_n1 in STEP; eauto. 
        clear STEPS. rename STEP into TAU_STEPS. eapply rtc_rtcn in TAU_STEPS. 
        destruct TAU_STEPS as (n & TAU_STEPS).  
        eapply ps_split in TAU_STEPS. clear n.  (** it's ok to forget n>0 *)
        destruct TAU_STEPS as (st' & lc' & sc' & mem' & st'' & lc'' & sc'' & mem'' & PRC_STEPS & ATMBLK_STEPS & NA_STEPS).
        eapply rtc_rtcn in PRC_STEPS. destruct PRC_STEPS as (n1 & PRC_STEPS). 
        eapply rtc_rtcn in ATMBLK_STEPS. destruct ATMBLK_STEPS as (n2 & ATMBLK_STEPS). 
        eapply rtc_rtcn in NA_STEPS. destruct NA_STEPS as (n3 & NA_STEPS). 
        destruct n3. 
        * destruct n2.
          { 
            destruct n1.
            { (** n3 = 0 & n2 = 0 & n1 = 0*)
              inv PRC_STEPS. inv ATMBLK_STEPS. inv NA_STEPS. 
              (* destruct c. destruct c'. eauto. *)
              assert (
                c_c'_equal: c = c'
              ). {
                destruct c. destruct c'.  
                inv C2. simpls. subst.  
                eapply IdentMap.gsident in TID1. 
                rewrite <- TID1. 
                rewrite IdentMap.add_add_eq. eauto. (** subst *) 
               }
              rewrite c_c'_equal. eauto.
            }
            { (** n3 = 0 & n2 = 0 & n1 != 0*)
              inv ATMBLK_STEPS. inv NA_STEPS.
              eapply rtcn_tail in PRC_STEPS. destruct PRC_STEPS as (ts' & PRC_STEPS & PRC_STEP).
              eapply rtcn_rtc in PRC_STEPS.
              eapply Configuration.aux_step_prc in PRC_STEPS; eauto.
              eapply Configuration.aux_tau_step_intro in PRC_STEPS; eauto.
              unfolds. intros. destruct H as (e0, contra). discriminate.
            }
          }
          { (** n3 = 0 & n2 != 0 *)
            inv NA_STEPS.
            eapply rtcn_tail in ATMBLK_STEPS. destruct ATMBLK_STEPS as (ts'' & ATMBLK_STEPS & ATMBLK_STEP).
            eapply rtcn_rtc in ATMBLK_STEPS. eapply rtcn_rtc in PRC_STEPS.
            eapply Configuration.aux_step_at in ATMBLK_STEPS; eauto.
            eapply Configuration.aux_tau_step_intro in ATMBLK_STEPS; eauto.
            unfolds. intros. destruct H as (e0, contra). discriminate.
          }
        * (** n3 ~= 0 *)
          (** NA(CONSISTENT) -> PRC(CONSISTENT)+ NA(CONSISTENT) *)
          remember {| Thread.state := st''; Thread.local := lc'';
                      Thread.sc := sc''; Thread.memory := mem'' |} as ts''.
          remember {| Thread.state := st2; Thread.local := lc2;
                      Thread.sc := Configuration.sc c'; Thread.memory := Configuration.memory c'|} as ts2.
          eapply AuxThread_nonzero_na_step_is_prc_na_step in NA_STEPS; eauto.
          destruct NA_STEPS as (ts''' & PRC_STEPS2 & MID_CONSISTENCY & NA_STEPS).
          destruct n2. 
          { (** n3 ~= 0 & n2 = 0 & any n1 *)
            inv ATMBLK_STEPS. 
            eapply rtcn_rtc in PRC_STEPS.
            rewrite <- H1 in PRC_STEPS2.
            pose proof (rtc_compose PRC_STEPS PRC_STEPS2) as PRC_STEPS'; eauto.
            clear PRC_STEPS PRC_STEPS2.
            eapply rtc_rtcn in PRC_STEPS'. destruct PRC_STEPS' as (n' & PRC_STEPS).
            destruct n'. 
            { (** promises steps = 0*)
              inv PRC_STEPS. 
              eapply rtcn_tail in NA_STEPS. destruct NA_STEPS as (ts'''' & NA_STEPS & NA_STEP). 
              eapply rtcn_rtc in NA_STEPS. destruct ts''''.
              eapply Configuration.aux_step_na in NA_STEPS; eauto.
              eapply Configuration.aux_tau_step_intro in NA_STEPS; eauto.
              unfolds. intros. destruct H as (e0, contra). discriminate.
            }
            { (** promises steps ~= 0*)
              eapply rtcn_tail in PRC_STEPS. destruct PRC_STEPS as (ts'' & PRC_STEPS & PRC_STEP).
              eapply rtcn_rtc in PRC_STEPS.
              destruct ts'''.
              remember {|                
              Configuration.threads :=
                IdentMap.add (Configuration.tid c)
                  (existT Language.state lang state, local) (Configuration.threads c);
                  Configuration.tid := Configuration.tid c; Configuration.sc := sc; Configuration.memory := memory |} as c_mid.
              assert (sc_from_c_mid: Configuration.sc c_mid = sc). {subst. eauto. }
              assert (mem_from_c_mid: Configuration.memory c_mid = memory). {subst. eauto. }
              rewrite <- sc_from_c_mid in PRC_STEP.
              rewrite <- mem_from_c_mid in PRC_STEP.
              eapply Configuration.aux_step_prc in PRC_STEP ; eauto.
              2: {
                rewrite sc_from_c_mid. rewrite mem_from_c_mid. eauto.
              }
              2: {
                rewrite sc_from_c_mid. rewrite mem_from_c_mid. eauto.
              }
              clear PRC_STEPS.
              (** prc_step finished.*)
              (** start proof for na_step *)
              eapply rtcn_tail in NA_STEPS. destruct NA_STEPS as (ts'''' & NA_STEPS & NA_STEP).
              eapply rtcn_rtc in NA_STEPS.
              destruct ts''''.
              assert (conf_aux_na_step: Configuration.aux_step AuxEvent.na lo c_mid c'). 
              {
                eapply Configuration.aux_step_na with (st1 := state) (lc1 := local) in NA_STEP ; eauto.
                {
                  rewrite Heqc_mid. simpls. 
                  eapply IdentMap.gss.
                }
                {
                  rewrite sc_from_c_mid. rewrite mem_from_c_mid. eauto.
                }
                {
                  rewrite Heqc_mid. simpls. rewrite IdentMap.add_add_eq. eauto.  
                }
              }
              eapply AuxThread_aux_na_step_is_aux_tau_step in conf_aux_na_step.
              eapply AuxThread_aux_prc_step_is_aux_tau_step in PRC_STEP.
              eapply rtc_n1  with (a:=c) in PRC_STEP; eauto. 
              eapply rtc_n1 with (b:=c_mid) in conf_aux_na_step; eauto.
            }
          }
          { (** n3 ~= 0 & n2 ~= 0 & any n1 *)
            eapply rtcn_tail in ATMBLK_STEPS. destruct ATMBLK_STEPS as (ts1' & ATMBLK_STEPS & ATMBLK_STEP).
            unfold Thread.atmblk_step in ATMBLK_STEP. destruct ATMBLK_STEP as (ts2' & ts3' & NA_STEPS_AT & AT_STEPS_AT & PRC_STEPS_AT).
            eapply rtc_compose with (z:=ts''') in PRC_STEPS_AT; eauto.
            assert (NEW_ATMBLK_STEP: 
              Thread.atmblk_step lo  ts1' ts'''
            ).
              {
                unfold Thread.atmblk_step.
                exists ts2' ts3'. splits; eauto. 
              }
            clear NA_STEPS_AT AT_STEPS_AT PRC_STEPS_AT.
            eapply rtcn_rtc in ATMBLK_STEPS.
            eapply rtcn_rtc in PRC_STEPS. 
            destruct ts'''.
            remember {|                
              Configuration.threads :=
                IdentMap.add (Configuration.tid c)
                  (existT Language.state lang state, local) (Configuration.threads c);
                  Configuration.tid := Configuration.tid c; Configuration.sc := sc; Configuration.memory := memory |} as c_mid.
            assert (sc_from_c_mid: Configuration.sc c_mid = sc). {subst. eauto. }
            assert (mem_from_c_mid: Configuration.memory c_mid = memory). {subst. eauto. }
            (* assert (CONF_ATMBLK_STEP: Configuration.aux_step AuxEvent.atm lo ) *)
            rewrite <- sc_from_c_mid in NEW_ATMBLK_STEP. 
            rewrite <- mem_from_c_mid in NEW_ATMBLK_STEP. 
            eapply Configuration.aux_step_at in NEW_ATMBLK_STEP; eauto.
            2: {
              rewrite sc_from_c_mid. rewrite mem_from_c_mid. eauto. 
            }
            2: {
              rewrite sc_from_c_mid. rewrite mem_from_c_mid. eauto. 
            }
            eapply AuxThread_aux_at_step_is_aux_tau_step in NEW_ATMBLK_STEP.
            (** atmblk_step finished *)
            (** start proof for na_step *)
            eapply rtcn_tail in NA_STEPS. destruct NA_STEPS as (ts'''' & NA_STEPS & NA_STEP).
            eapply rtcn_rtc in NA_STEPS.
            destruct ts2.
            assert (conf_aux_na_step: Configuration.aux_step AuxEvent.na lo c_mid c'). 
              {
                rewrite <- sc_from_c_mid in NA_STEPS. 
                rewrite <- mem_from_c_mid in NA_STEPS. 
                eapply Configuration.aux_step_na with (st1 := state) (lc1 := local) in NA_STEPS ; eauto.
                {
                  rewrite Heqc_mid. simpls. 
                  eapply IdentMap.gss.
                }
                {
                  rewrite <- Heqts2. eauto.
                }
                {
                  rewrite <- Heqts2. eauto.
                }
                {
                  rewrite Heqc_mid. simpls. rewrite IdentMap.add_add_eq. eauto.  
                }
              }
              eapply AuxThread_aux_na_step_is_aux_tau_step in conf_aux_na_step.
              eapply rtc_n1  with (a:=c) in NEW_ATMBLK_STEP; eauto. 
              eapply rtc_n1 with (b:=c_mid) in conf_aux_na_step; eauto.
          }
      - (** out step *) 
        { 
          destruct TAU.
          exists e0. eauto.
        }
      - (** sw step *)
        {
          assert (sw_to_aux_sw: 
            Configuration.aux_step AuxEvent.sw lo
            c
            {|
              Configuration.threads := (Configuration.threads c);
              Configuration.tid := tid';
              Configuration.sc := (Configuration.sc c);
              Configuration.memory := (Configuration.memory c)
            |}
          ). {
            eauto.
          }
          eapply Configuration.aux_tau_step_intro in sw_to_aux_sw; eauto.
          eapply rtc_n1 in sw_to_aux_sw; eauto.
          unfolds. intros. destruct H as (e0, contra). discriminate.
        }
      - (** tterm *)
        { 
          assert (tterm_to_aux_tterm: 
            Configuration.aux_step AuxEvent.tterm lo c c'  
          ). {
            eauto.
          }
          eapply Configuration.aux_tau_step_intro in tterm_to_aux_tterm; eauto.
          eapply rtc_n1 in tterm_to_aux_tterm; eauto.
          unfolds. intros. destruct H as (e0, contra). discriminate.
        }
    Qed.

    Lemma ps_out_to_aps_tau_and_out:
    forall lo c c' e,
      Configuration.step (MachineEvent.syscall e) lo c c'
      ->
      (
        exists c1, 
        rtc (Configuration.aux_tau_step lo) c c1 
        /\ Configuration.aux_step (AuxEvent.out e) lo c1 c'  
      ).
    Proof.
      intros. inv H.
      pose proof (out_step_start_consistency STEP_OUT) as MID_CONSISTENT.
      eapply rtc_rtcn in STEPS. destruct STEPS as (n & STEPS).
      destruct n.
      - inv STEPS. eauto.
      - eapply rtcn_tail in STEPS.
        destruct STEPS as (ts0 & TAU_STEPS & TAU_STEP). 
        eapply rtcn_rtc in TAU_STEPS.
        destruct ts0. 
        remember {|
          Configuration.threads :=
            IdentMap.add (Configuration.tid c)
              (existT Language.state lang state, local) (Configuration.threads c);
          Configuration.tid := Configuration.tid c;
          Configuration.sc := sc;
          Configuration.memory := memory
          |} as c_mid.
          assert (MID_SC: Configuration.sc c_mid = sc). {subst. eauto. }
          assert (MID_MEM: Configuration.memory c_mid = memory). {subst. eauto. }
          rewrite <- MID_SC in TAU_STEP. 
          rewrite <- MID_MEM in TAU_STEP. 
        destruct e1.
        remember {|
          Configuration.threads :=
            IdentMap.add (Configuration.tid c)
              (existT Language.state lang state0, local0) (Configuration.threads c);
          Configuration.tid := Configuration.tid c;
          Configuration.sc := sc0;
          Configuration.memory := memory0
          |} as c_mid'.
          assert (MID'_SC: Configuration.sc c_mid' = sc0). {subst. eauto. }
          assert (MID'_MEM: Configuration.memory c_mid' = memory0). {subst. eauto. }
        eapply Configuration.step_tau with (c2 := c_mid') in TAU_STEPS; subst; eauto. simpls.
        remember {|
        Configuration.threads :=
          IdentMap.add (Configuration.tid c)
            (existT Language.state lang state0, local0) (Configuration.threads c);
        Configuration.tid := Configuration.tid c;
        Configuration.sc := sc0;
        Configuration.memory := memory0
        |} as c_mid'.
        assert (CONF_TAU_STEP: Configuration.tau_step lo c c_mid'). {
          eapply Configuration.tau_step_intro in TAU_STEPS; eauto. 
          intuition. destruct H as (e0 & CONTRA). discriminate.
        }
      eapply ps_to_aps in CONF_TAU_STEP.
      eapply Configuration.aux_step_out with (c1 := c_mid') (st1:=state0) (lc1 := local0) in STEP_OUT; subst; simpls; eauto. 
      * eapply IdentMap.gss.
      * rewrite IdentMap.add_add_eq. eauto.
    Qed.

    Lemma Config_aux_tau_step_to_aux_all_step
          lo c c'
          (CONFIG_AUX_TAU: Configuration.aux_tau_step lo c c'):
      Configuration.aux_all_step lo c c'.
    Proof.
      inv CONFIG_AUX_TAU.
      econs; eauto.
    Qed.

    Lemma Config_aux_tau_steps_to_aux_all_steps:
      forall n lo c c'
        (CONFIG_AUX_TAUS: rtcn (Configuration.aux_tau_step lo) n c c'),
        rtc (Configuration.aux_all_step lo) c c'.
    Proof.
      induction n; ii.
      - inv CONFIG_AUX_TAUS.
        econs; eauto.
      - inv CONFIG_AUX_TAUS.
        eapply Config_aux_tau_step_to_aux_all_step in A12.
        eapply IHn in A23.
        eapply Relation_Operators.rt1n_trans; eauto.
    Qed.

    Lemma Config_all_steps_aux_all_steps:
      forall n c c' lo
        (ALL_STEPS: rtcn (Configuration.all_step lo) n c c'),
        rtc (Configuration.aux_all_step lo) c c'.
    Proof.
      induction n; ii.
      - inv ALL_STEPS. eauto.
      - inv ALL_STEPS.
        eapply IHn in A23.
        inv A12. destruct e; ss.
        + exploit Configuration.tau_step_intro; eauto.
          ii; des; ss. ii.
          eapply ps_to_aps in x0.
          eapply rtc_rtcn in x0. des.
          eapply Config_aux_tau_steps_to_aux_all_steps in x0.
          eapply rtc_compose; eauto.
        + exploit Configuration.tau_step_intro; eauto.
          ii; des; ss. ii.
          eapply ps_to_aps in x0.
          eapply rtc_rtcn in x0. des.
          eapply Config_aux_tau_steps_to_aux_all_steps in x0.
          eapply rtc_compose; eauto.
        + eapply ps_out_to_aps_tau_and_out in WP_STEP.
          des.
          eapply rtc_rtcn in WP_STEP. des.
          eapply Config_aux_tau_steps_to_aux_all_steps in WP_STEP.
          eapply rtc_compose.
          eapply WP_STEP.
          eapply Relation_Operators.rt1n_trans.
          econs; eauto. eauto.
    Qed.

    Lemma conf_behavoirs_to_aux_conf_behaviors:
    forall n1 c lo behs,
      conf_behaviors c lo n1 behs -> (exists n2, aux_conf_behaviors c lo n2 behs).
    Proof.
      induction n1. 
        * intros. inv H; eauto.    
        * intros. 
          rename H into CONF_BEHS.
          inv CONF_BEHS; eauto.
          2: { (** tau step behaviors *)
            assert (TAU_STEP: Configuration.tau_step lo c c'). 
              { eapply Configuration.tau_step_intro in STEP; eauto. }
            eapply ps_to_aps in TAU_STEP. 
              eapply rtc_rtcn in TAU_STEP. 
              destruct TAU_STEP as (n2' & TAU_STEPS).
            eapply IHn1 in BEHS.
            destruct BEHS as (n2 & AUX_CONF_BEHS).
            eapply tau_steps_aux_behaviors' with (c2 := c') in AUX_CONF_BEHS; eauto. 
          }
          { (** out step behaviors *)
            eapply ps_out_to_aps_tau_and_out in STEP. 
              destruct STEP as (c1 & TAU_STEPS & OUT_STEP). 
              eapply rtc_rtcn in TAU_STEPS. 
                destruct TAU_STEPS as (n' & TAU_STEPS).
                destruct n'.
                {
                  inv TAU_STEPS. 
                  eapply IHn1 in BEHS. destruct BEHS as (n'' & AUX_CONF_BEHS).
                  eapply aux_behaviors_out with (behs := behs0) in OUT_STEP; eauto. 
                }
                {
                  eapply IHn1 in BEHS. destruct BEHS as (n'' & AUX_CONF_BEHS).
                  eapply aux_behaviors_out with (behs := behs0) in OUT_STEP; eauto. 
                  eapply tau_steps_aux_behaviors' with (c2 := c1) in OUT_STEP; eauto. 
                } 
          }
          Unshelve. exact 0. exact 0.
    Qed.

    Lemma atmblk_step_is_tau_steps:
      forall lang lo e e',
        @Thread.atmblk_step lang lo e e' ->
        rtc (@Thread.tau_step lang lo) e e'.
    Proof.
      intros.
      inv H. destruct H0 as (x' & NAS & AT & PRCS).
      pose proof na_step_is_tau_step.
      pose proof at_step_is_tau_step.
      pose proof prc_step_is_tau_step.
      eapply rtc_implies with (R2:= (Thread.tau_step lo)) in NAS; eauto. 
      eapply rtc_implies with (R2:= (Thread.tau_step lo)) in PRCS; eauto. 
      eapply at_step_is_tau_step in AT.
      eapply rtc_n1 with (a:=e) in AT; eauto.
      eapply rtc_compose with (z:=e') in AT; eauto.
    Qed.

    Lemma atmblk_steps_is_tau_steps':
      forall n lang lo e e',
        rtcn (@Thread.atmblk_step lang lo) n e e' ->
        rtc (@Thread.tau_step lang lo) e e'.
    Proof.
      induction n.
      - intros. inv H. eauto.
      - intros. inv H.
        eapply IHn in A23.
        eapply atmblk_step_is_tau_steps in A12.
        eapply rtc_compose with (z:=e') in A12; eauto.
    Qed.

    Lemma atmblk_steps_is_tau_steps:
      forall lang lo e e',
        rtc (@Thread.atmblk_step lang lo) e e' ->
        rtc (@Thread.tau_step lang lo) e e'.
    Proof.
      intros.
      eapply rtc_rtcn in H. destruct H as (n, ATMS).
      eapply atmblk_steps_is_tau_steps' in ATMS. eauto.
    Qed.

    Lemma aps_to_ps:
    forall lo c c',
        Configuration.aux_tau_step lo c c'
        -> rtc (Configuration.tau_step lo) c c'.
    Proof.
      intros.
      inv H.
      inv WP_STEP.
      - (** na step *) (** 几个step都是类似的 *)
        pose proof na_step_is_tau_step.
        eapply rtc_implies with (R2:= (Thread.tau_step lo)) in STEPS; eauto. 
        eapply na_step_is_tau_step in STEP.
        eapply Configuration.step_tau in STEPS; eauto.
        eapply Configuration.tau_step_intro in STEPS; eauto.
        intuition. destruct H0. discriminate.
      - (** prc step *) 
        pose proof prc_step_is_tau_step.
        eapply rtc_implies with (R2:= (Thread.tau_step lo)) in STEPS; eauto. 
        eapply prc_step_is_tau_step in STEP.
        eapply Configuration.step_tau in STEPS; eauto.
        eapply Configuration.tau_step_intro in STEPS; eauto.
        intuition. destruct H0. discriminate.
      - (** atmblk step *) 
        pose proof prc_step_is_tau_step.
        eapply atmblk_steps_is_tau_steps in STEPS_ATM.
        eapply atmblk_step_is_tau_steps in STEP_ATM.
        eapply rtc_implies with (R2:= (Thread.tau_step lo)) in STEPS_PRC; eauto. 
        eapply rtc_compose with (z:=e1') in STEPS_PRC; eauto.
        eapply rtc_compose with (z:={|
            Thread.state := st2;
            Thread.local := lc2;
            Thread.sc := Configuration.sc c';
            Thread.memory := Configuration.memory c'
          |}) in STEPS_PRC; eauto.
        eapply rtc_rtcn in STEPS_PRC. destruct STEPS_PRC as (n, STEPS).
        destruct n.
          * inv STEPS. destruct c. destruct c'. subst. simpls. rewrite H4. rewrite H5. 
            inv C2. rewrite -> IdentMap.gsident; eauto. 
          * 
            eapply rtcn_tail in STEPS. destruct STEPS as (ts' & STEPS & STEP).
            eapply rtcn_rtc in STEPS. 
            eapply Configuration.step_tau in STEPS; eauto.
            eapply Configuration.tau_step_intro in STEPS; eauto.
            intuition. destruct H0. discriminate.
      - (** out step *)
         destruct TAU. exists e0. reflexivity.
      - (** sw step *)
        {
          assert (aux_sw_to_sw: 
            Configuration.step MachineEvent.switch lo
            c
            {|
              Configuration.threads := (Configuration.threads c);
              Configuration.tid := tid';
              Configuration.sc := (Configuration.sc c);
              Configuration.memory := (Configuration.memory c)
            |}
          ). {
            eauto.
          }
          eapply Configuration.tau_step_intro in aux_sw_to_sw; eauto.
          eapply rtc_n1 in aux_sw_to_sw; eauto.
          unfolds. intros. destruct H as (e0, contra). discriminate.
        }
      - (** tterm *)
        { 
          assert (tterm: 
            Configuration.step MachineEvent.switch lo c c'  
          ). {
            eauto.
          }
          eapply Configuration.tau_step_intro in tterm; eauto.
          eapply rtc_n1 in tterm; eauto.
          unfolds. intros. destruct H as (e0, contra). discriminate.
        }
    Qed.

    Lemma aux_conf_behavoirs_to_conf_behaviors:
    forall n2 c lo behs,
      aux_conf_behaviors c lo n2 behs -> (exists n1, Behavior.conf_behaviors c lo n1 behs).
    Proof.
      induction n2.
      * intros. inv H; eauto.
      * intros. inv H; eauto.
        { (** out step *)
          rename STEP into AUX_CONF_STEP.
          inv AUX_CONF_STEP.
          assert (CONF_STEP: Configuration.step (MachineEvent.syscall e) lo c c'). 
          {
            eapply Configuration.step_out in STEP_OUT; eauto.
            pose proof na_step_is_tau_step.
            eapply rtc_implies with (R2:= (Thread.tau_step lo)) in STEPS; eauto. 
          } 
          eapply IHn2 in BEHS. destruct BEHS as (n1, BEHS).
          eapply Behavior.behaviors_out in CONF_STEP; eauto.
        }
        { (** tau step*)
          eapply IHn2 in BEHS. rename STEP into AUX_STEP.
          assert (TAU_STEP: Configuration.aux_tau_step lo c c'). 
              { eapply Configuration.aux_tau_step_intro in AUX_STEP; eauto. }
          eapply aps_to_ps in TAU_STEP.
          eapply rtc_rtcn in TAU_STEP. destruct TAU_STEP as (n, TAU_STEP).
          destruct BEHS as (n1, BEHS).
          eapply tau_steps_behaviors' in TAU_STEP; eauto.
        }
      Unshelve. exact 0. exact 0.
    Qed.

    Lemma conf_behaviors_eq_aux_conf_behaviors:
    forall c lo behs, 
    (exists n1, conf_behaviors c lo n1 behs) <-> (exists n2, aux_conf_behaviors c lo n2 behs).
    Proof.
      intros. splits.
      - intros. destruct H as (n1 & CONF_BEHS).
        eapply conf_behavoirs_to_aux_conf_behaviors; eauto.
      - intros. destruct H as (n2 & AUX_CONF_BEHS).
        eapply aux_conf_behavoirs_to_conf_behaviors; eauto.
    Qed. 
        
    (* Lemma B.3 *)
    Lemma sema_eq_ps_aps {lang:language}:
    forall (code: Language.syntax lang) lo fs behs ctid, 
        prog_behaviors fs code ctid lo behs 
        <-> aux_prog_behaviors fs code ctid lo behs.
    Proof.
      intros. splits.
      - intros. 
        unfolds prog_behaviors. destruct H as (n1 & c & INIT & BEHS).
        assert (exists n1, conf_behaviors c lo n1 behs); eauto.
        eapply conf_behaviors_eq_aux_conf_behaviors in H. 
        destruct H as (n2 & AUX_CONF_BEHS).
        unfolds aux_prog_behaviors. exists n2. exists c. splits; eauto.
      - intros. unfolds aux_prog_behaviors. destruct H as (n2 & c & INIT & BEHS).
        assert (exists n2, aux_conf_behaviors c lo n2 behs); eauto.
        eapply conf_behaviors_eq_aux_conf_behaviors in H.
        destruct H as (n1 & CONF_BEHS).
        unfolds prog_behaviors. exists n1. exists c. splits; eauto.
    Qed.
End PS_and_APS.

(** APS to NP proof *)
Module APS_and_NP.
  
  Lemma Config_aux_na_steps_merge
        c c' c'' lo
        (NA_STEP1: Configuration.aux_step AuxEvent.na lo c c')
        (NA_STEP2: Configuration.aux_step AuxEvent.na lo c' c''):
    Configuration.aux_step AuxEvent.na lo c c''.
  Proof.
    inv NA_STEP1; ss. inv NA_STEP2; ss.
    destruct c, c', c''; ss. inv C0. inv C2.
    rewrite IdentMap.add_add_eq.
    rewrite IdentMap.gss in TID0. inv TID0.
    eapply inj_pair2 in H1. subst.
    econs.
    eauto. 
    ss. eauto.
    ss. eapply rtc_compose.
    eapply rtc_n1. eapply STEPS. eapply STEP.
    eapply STEPS0.
    ss. eauto.
    ss. ss.
  Qed.

  Lemma Config_aux_prc_steps_merge
        c c' c'' lo
        (PRC_STEP1: Configuration.aux_step AuxEvent.prc lo c c')
        (PRC_STEP2: Configuration.aux_step AuxEvent.prc lo c' c''):
    Configuration.aux_step AuxEvent.prc lo c c''.
  Proof.
    inv PRC_STEP1; ss. inv PRC_STEP2; ss.
    destruct c, c', c''; ss. inv C0. inv C2.
    rewrite IdentMap.add_add_eq.
    rewrite IdentMap.gss in TID0. inv TID0.
    eapply inj_pair2 in H1. subst.
    econs.
    eauto. 
    ss. eauto.
    ss. eapply rtc_compose.
    eapply rtc_n1. eapply STEPS. eapply STEP.
    eapply STEPS0.
    ss. eauto.
    ss. ss.
  Qed.

  Lemma aux_prc_steps_compose
        lo c c' c'' tid' n
        (PRC_STEP: Configuration.aux_step AuxEvent.prc lo c c')
        (PRC_STEPS: PRCStep lo (Configuration.sw_tid c' tid') c'' n):
    exists n', PRCStep lo c c'' n'.
  Proof.
    inv PRC_STEPS.
    - des; subst.
      + exists 0%nat.
        rewrite Configuration.sw_tid_twice; eauto.
        econs; eauto.
      + destruct (Loc.eq_dec tid' (Configuration.tid c')); subst.
        {
          rewrite <- Configuration.sw_to_self in STEP.
          exists 0%nat. 
          exploit Config_aux_prc_steps_merge;
            [eapply PRC_STEP | eapply STEP | eauto..].
          ii.
          econs; eauto.
        }
        {
          exists 1%nat.
          econs; eauto.
          econs; eauto.
        }
    - destruct (Loc.eq_dec tid' (Configuration.tid c')); subst.
      {
        rewrite <- Configuration.sw_to_self in STEP.
        exploit Config_aux_prc_steps_merge; [eapply PRC_STEP | eapply STEP | eauto..].
        ii.
        exists (S n0).
        econs; eauto.
      }
      {
        exists (S (S n0)).
        econs; eauto.
        econs; eauto.
      }
  Qed.
      
  Lemma aetr_to_swprocs: 
    forall n c lo behs
      (AUX_CONF_BEH: aux_conf_behaviors c lo n behs),
    exists n' c', 
      sw_procs lo c c' behs n'.
  Proof.
    induction n; ii.
    - inv AUX_CONF_BEH.
      exists 0%nat c. econs; eauto.
    - inv AUX_CONF_BEH.
      + (* abort *)
        exists 0%nat c.
        econs; eauto.
      + (* done *)
        exists 0%nat c.
        econs; eauto.
      + (* output *)
        eapply IHn in BEHS; eauto. des.
        exists (S n') c'0.
        eapply sw_procs_out; eauto.
      + (* tau *)
        eapply IHn in BEHS; eauto. des.
        destruct npe; ss.
        {
          (* na step *)
          inv BEHS.

          (* cont na/sw steps *)
          exists 0%nat c'0. 
          eapply sw_procs_nil.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          econs; eauto.

          (* cont done step *)
          exists 0%nat c'0.
          eapply sw_procs_done; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          econs; eauto.

          (* cont abort step *)
          exists 0%nat c'0.
          eapply sw_procs_abort; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          econs; eauto.

          (* cont out step *)
          exists (S n0) c'0. 
          eapply sw_procs_out. 3: eapply SW_N. 2: eapply OUT_STEP.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          econs; eauto.

          (* cont at/prc/tterm step *)
          exists (S n0) c'0.
          eapply sw_procs_at.
          2: eauto. 2: eapply SW_N.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          econs; eauto.
        }
        {
          exists (S n') c'0.
          eapply sw_procs_at; eauto.
        }
        {
          exists (S n') c'0.
          eapply sw_procs_at; eauto.
        }
        {
          contradiction EVENT. eauto.
        }
        {
          (* sw step *)
          inv BEHS.

          (* cont na/sw steps *)
          exists 0%nat c'0. 
          eapply sw_procs_nil.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          right. eauto.

          (* cont done step *)
          exists 0%nat c'0.
          eapply sw_procs_done; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          right. eauto.

          (* cont abort step *)
          exists 0%nat c'0.
          eapply sw_procs_abort; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          right. eauto.

          (* cont out step *)
          exists (S n0) c'0. 
          eapply sw_procs_out. 3: eapply SW_N. 2: eapply OUT_STEP.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          right. eauto.

          (* cont at/prc/tterm step *)
          exists (S n0) c'0.
          eapply sw_procs_at.
          2: eauto. 2: eapply SW_N.
          eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
          right. eauto.
        }
        {
          exists (S n') c'0.
          eapply sw_procs_at; eauto.
        }
  Qed. 

  Lemma aux_na_or_sw_steps_to_na_aux_steps:
    forall n lo c c'
      (AUX_NA_OR_SW_STEPS: rtcn (aux_na_or_sw_step lo) n c c'),
    exists n' tid,
      NAStep lo (Configuration.sw_tid c tid) c' n'.
  Proof.
    induction n; ii.
    - inv AUX_NA_OR_SW_STEPS.
      exists 0%nat (Configuration.tid c'). destruct c'; ss.
      unfold Configuration.sw_tid; ss.
      econs; eauto.
      instantiate (1 := tid). ss.
    - inv AUX_NA_OR_SW_STEPS.
      eapply IHn in A23; eauto. des.
      inv A12.
      + (* na step *)
        destruct (Loc.eq_dec tid (Configuration.tid a2)); subst.
        {
          rewrite <- Configuration.sw_to_self in A23.
          inv A23.
          {
            des; subst.
            exists 0%nat (Configuration.tid c).
            rewrite <- Configuration.sw_to_self.
            econs; eauto. 
            exploit Config_aux_na_steps_merge;
              [eapply H | eapply STEP | eauto..].
            introv NA_STEP.
            exists 0%nat (Configuration.tid c).
            rewrite <- Configuration.sw_to_self; eauto.
            econs; eauto.
          }
          {
            exists (S n0)%nat (Configuration.tid c).
            rewrite <- Configuration.sw_to_self; eauto.
            exploit Config_aux_na_steps_merge;
              [eapply H | eapply STEP | eauto..].
            introv NA_STEP.
            econs; eauto.
          }
        }
        {
          exists (S n') (Configuration.tid c).
          rewrite <- Configuration.sw_to_self.
          econs; eauto.
        }
      + (* sw step *)
        inv H; ss.
        unfold Configuration.sw_tid in A23; ss.
        exists n' tid.
        destruct c; ss.
  Qed.

  Lemma reorder_na_fulfill_step_prc_steps:
    forall n c c0 c1 tid0 lo
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c0)
      (PRC_STEPS: PRCStep lo (Configuration.sw_tid c0 tid0) c1 n)
      (WF_CONFIG: Configuration.wf c),
    exists c' tid tid' n0,
      PRCStep lo (Configuration.sw_tid c tid) c' n0
      /\ Config_na_fulfill_step lo (Configuration.sw_tid c' tid')
                               (Configuration.sw_tid c1 tid')
      /\ Configuration.tid c = tid'.
  Proof.
    induction n; ii.
    - inv PRC_STEPS. des; subst.
      + exists c (Configuration.tid c) (Configuration.tid c) 0%nat.
        split.
        econs; eauto.
        rewrite <- Configuration.sw_to_self.
        rewrite <- Configuration.sw_to_self. eauto.
        rewrite <- Configuration.sw_to_self; eauto.
        rewrite Configuration.sw_tid_twice.
        rewrite Configuration.sw_tid_twice.
        split; eauto.
        assert (TID_EQ: Configuration.tid c = Configuration.tid c0).
        {
          inv NA_FULFILL_STEP. ss.
        }
        rewrite TID_EQ.
        rewrite <- Configuration.sw_to_self; eauto. 
      + destruct (Loc.eq_dec tid0 (Configuration.tid c0)); subst.
        {
          rewrite <- Configuration.sw_to_self in STEP.
          exploit Config_na_fulfill_prc_reordering_in_same_thread; eauto.
          ii; des.
          clear - x0 x1. 
          exists c' (Configuration.tid c) (Configuration.tid c) 0%nat.
          assert (TID_EQ1: Configuration.tid c = Configuration.tid c').
          {
            inv x0; eauto.
            destruct c, c'; ss. inv C2; eauto.
          }
          assert (TID_EQ2: Configuration.tid c' = Configuration.tid c3).
          {
            inv x1; eauto.
          }
          rewrite TID_EQ1. rewrite <- Configuration.sw_to_self.
          rewrite <- TID_EQ1. rewrite <- Configuration.sw_to_self.
          rewrite Configuration.sw_tid_twice.
          rewrite TID_EQ1. rewrite TID_EQ2.
          rewrite <- Configuration.sw_to_self.
          split; eauto.
          econs; eauto.
          instantiate (1 := Configuration.tid c').
          rewrite Configuration.sw_to_self; eauto.
        }
        {
          exploit Config_na_fulfill_prc_reordering_in_diff_threads; eauto.
          ii; des; subst.
          clear - WF_CONFIG n x0 x1.
          exists c' tid0 (Configuration.tid c) 0%nat.
          rewrite Configuration.sw_tid_twice.
          split; eauto.
          econs; eauto.
          instantiate (1 := Configuration.tid c').
          rewrite Configuration.sw_to_self; eauto.
        }
    - inv PRC_STEPS.
      destruct (Loc.eq_dec tid0 (Configuration.tid c0)); subst.
      {
        rewrite <- Configuration.sw_to_self in STEP.
        exploit Config_na_fulfill_prc_reordering_in_same_thread; eauto.
        ii; des.
        assert (WF_CONFIG': Configuration.wf c').
        {
          clear - x0 WF_CONFIG.
          inv x0. destruct c, c'; ss. inv C2.
          eapply prc_steps_is_tau_steps in STEPS.
          eapply prc_step_is_tau_step in STEP.
          eapply Thread_tau_steps_is_all_steps in STEPS.
          eapply Thread_tau_step_is_all_step in STEP.
          eapply wf_config_rtc_thread_steps_prsv.
          eapply WF_CONFIG.
          eauto.
          eapply rtc_compose.
          eapply STEPS.
          eapply Operators_Properties.clos_rt1n_step. eapply STEP.
        }

        exploit IHn; [eapply x1 | eapply PRC | eapply WF_CONFIG' | eauto..].
        ii; des. subst.
        assert (TID_EQ: Configuration.tid c = Configuration.tid c').
        {
          inv x0. destruct c, c'; ss.
          inv C2. eauto.
        }
        exists c'0 (Configuration.tid c) (Configuration.tid c').
        rewrite <- Configuration.sw_to_self.
        exploit aux_prc_steps_compose; [eapply x0 | eapply x | eauto..].
        ii; des.
        exists n'.
        split; eauto.
      }
      {
        exploit Config_na_fulfill_prc_reordering_in_diff_threads; eauto.
        ii; des; subst.

        assert (WF_CONFIG': Configuration.wf c').
        {
          clear - x0 WF_CONFIG.
          inv x0. destruct c, c'; ss. inv C2.
          eapply prc_steps_is_tau_steps in STEPS.
          eapply prc_step_is_tau_step in STEP.
          eapply Thread_tau_steps_is_all_steps in STEPS.
          eapply Thread_tau_step_is_all_step in STEP.
          eapply wf_config_rtc_thread_steps_prsv.
          eapply wf_config_sw_prsv; eauto.
          eauto.
          eapply rtc_compose.
          eapply STEPS.
          eapply Operators_Properties.clos_rt1n_step. eapply STEP.
        }

        exploit IHn; [eapply x1 | eapply PRC | eauto..].
        clear - WF_CONFIG'.
        destruct c, c'; ss.
        unfold Configuration.sw_tid; ss.
        eapply wf_config_sw_prsv; eauto.

        ii; des.
        rewrite Configuration.sw_tid_twice in x. subst; ss.
        exploit aux_prc_steps_compose; [eapply x0 | eapply x | eauto..].
        ii; des.
        exists c'0 tid0 (Configuration.tid c) n'.
        split; eauto.
      }
  Qed.
      
  Lemma reorder_na_step_prc_steps:
    forall n c c0 c1 tid0 lo
      (NA_STEP: Configuration.aux_step AuxEvent.na lo c c0)
      (PRC_STEPS: PRCStep lo (Configuration.sw_tid c0 tid0) c1 n)
      (WF_CONFIG: Configuration.wf c),
    exists c' tid n0 tid',
      PRCStep lo (Configuration.sw_tid c tid) c' n0
      /\ Config_na_fulfill_step lo (Configuration.sw_tid c' tid')
                               (Configuration.sw_tid c1 tid')
      /\ Configuration.tid c = tid'.
  Proof.
    ii.
    eapply Config_na_step_to_na_fulfill_step in NA_STEP.
    des.
    - exploit reorder_na_fulfill_step_prc_steps; eauto.
      {
        inv NA_STEP.
        destruct c, c2; ss. inv C2.
        eapply prc_steps_is_tau_steps in STEPS.
        eapply prc_step_is_tau_step in STEP.
        eapply Thread_tau_steps_is_all_steps in STEPS.
        eapply Thread_tau_step_is_all_step in STEP.
        eapply wf_config_rtc_thread_steps_prsv.
        eapply WF_CONFIG.
        eauto.
        eapply rtc_compose.
        eapply STEPS.
        eapply Operators_Properties.clos_rt1n_step. eapply STEP.
      }

      ii; des; subst.
      exploit aux_prc_steps_compose; eauto. ii; des.
      exists c' (Configuration.tid c) n' (Configuration.tid c2).
      rewrite <- Configuration.sw_to_self.
      split; eauto.
      split; eauto.
      inv NA_STEP.
      destruct c, c2; ss. inv C2; eauto.
    - subst.
      exploit reorder_na_fulfill_step_prc_steps; eauto.
      ii; des; subst.
      exists c' tid n0 (Configuration.tid c2).
      split; eauto.
  Qed.

  Lemma construct_done':
    forall n lo c c'
      (NA_STEPS: NAStep lo c c' n)
      (DONE: Configuration.is_done c'),
    exists tid',
      Configuration.aux_step AuxEvent.na lo (Configuration.sw_tid c tid') c'
      \/ (Configuration.sw_tid c tid') = c'.
  Proof.
    induction n; ii.
    - inv NA_STEPS. des; subst.
      + exists tid. eauto.
      + exists (Configuration.tid c).
        left. 
        rewrite <- Configuration.sw_to_self.
        assert (tid = Configuration.tid c1).
        {
          inv DONE; ss. des; subst.
          inv STEP; ss. destruct c, c1; ss. inv C2.
          destruct (Loc.eq_dec tid tid0); subst; eauto.
          clear - H1 n.
          eapply IdentMap.is_empty_2 in H1.
          eapply IdentMap.Empty_alt with (a := tid0) in H1.
          rewrite IdentMap.gro in H1; eauto.
          rewrite IdentMap.gss in H1; eauto. ss.
        }
        subst.
        rewrite <- Configuration.sw_to_self; eauto.
    - inv NA_STEPS.
      eapply IHn in NA; eauto. des.
      + clear - DONE STEP DIFF_TID NA.
        assert (tid' = Configuration.tid c1).
        {
          destruct c, c1, c'; ss. 
          unfold Configuration.sw_tid in *; ss.
          inv DONE; ss. des.
          inv STEP; ss. des.
          inv NA; ss. inv C0. inv C2.
          clear - H1.
          destruct (Loc.eq_dec tid' tid); subst; eauto.
          eapply IdentMap.is_empty_2 in H1.
          eapply IdentMap.Empty_alt with (a := tid) in H1.
          rewrite IdentMap.gro in H1; eauto.
          rewrite IdentMap.gso in H1; eauto.
          rewrite IdentMap.gss in H1; eauto. ss.
        }

        subst.
        assert (Configuration.tid c = Configuration.tid c1).
        {
          inv STEP. destruct c, c1; ss.
          inv C2; eauto.
        }
        destruct c, c1. ss.
        unfold Configuration.sw_tid in *; ss. subst.
        exists tid0.
        left.
        exploit Config_aux_na_steps_merge;
          [eapply STEP | eapply NA | eauto..].
      + subst.
        assert (Configuration.tid c1 = tid').
        {
          inv DONE. des; ss.
          inv STEP.
          destruct c, c1; ss.
          inv C2.
          destruct (Loc.eq_dec tid tid'); subst; eauto.
          eapply IdentMap.is_empty_2 in H1.
          eapply IdentMap.Empty_alt with (a := tid) in H1.
          rewrite IdentMap.gro in H1; eauto.
          rewrite IdentMap.gss in H1; eauto. ss.
        }

        subst.
        exists (Configuration.tid c).
        destruct c, c1; ss.
        unfold Configuration.sw_tid in *; ss.
        assert (tid = tid0).
        {
          inv STEP. ss. inv C2. eauto.
        }
        subst.
        left.
        eauto.
  Qed.

  Lemma construct_done
        lo c c'
        (AUX_NA_OR_SW_STEPS: rtc (aux_na_or_sw_step lo) c c')
        (DONE: Configuration.is_done c'):
    exists tid', 
      Configuration.aux_step AuxEvent.na lo (Configuration.sw_tid c tid') c'
      \/ (Configuration.sw_tid c tid') = c'.
  Proof.
    eapply rtc_rtcn in AUX_NA_OR_SW_STEPS. des.
    eapply aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEPS.
    des.
    exploit construct_done';
      [eapply AUX_NA_OR_SW_STEPS | eapply DONE | eauto..].
  Qed.

  Lemma sw_point_forwarding_abort':
    forall n lo c c'
      (NA_STEPS: NAStep lo c c' n)
      (ABORT: Configuration.is_abort c' lo)
      (WF_CONFIG: Configuration.wf c),
    exists c0 tid0 n0,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ Configuration.is_abort c0 lo.
  Proof.
    induction n; ii.
    - inv NA_STEPS.
      des; subst.
      + exists (Configuration.sw_tid c1 tid) tid 0%nat.
        split; eauto.
        econs; eauto.
        instantiate (1 := tid).
        unfold Configuration.sw_tid.
        destruct c1; ss.
      + destruct (Loc.eq_dec tid (Configuration.tid c1)); subst.
        {
          (* switch to the same thread *)
          rewrite <- Configuration.sw_to_self in ABORT.
          exploit cons_na_abort; eauto.
          introv CONFIG_ABORT.
          exists c (Configuration.tid c) 0%nat.
          split; eauto.
          econs; eauto.
          instantiate (1 := Configuration.tid c).
          rewrite Configuration.sw_to_self; eauto.
        }
        {
          (* switch to the different thread *)
          assert (NA_TID_UNCHANGE: Configuration.tid c = Configuration.tid c1).
          {
            inv STEP.
            destruct c, c1; ss. inv C2. eauto.
          }
          exploit Config_na_step_to_na_fulfill_step; eauto.
          ii; des.
          {
            exploit Config_na_fulfill_step_sc_mem_unchange; eauto.
            ii; des.
            exploit Config_abort_stable;
              [eapply ABORT | eapply SC_UNCHANG | eapply MEM_UNCHANG | eauto..].
            clear - n NA_TID_UNCHANGE x1.
            inv x1; ss.
            rewrite IdentMap.gso; eauto.

            introv ABORT'.
            assert (PRC_TID_UNCHANGE: Configuration.tid c0 = Configuration.tid c1).
            {
              inv x1. ss.
            }
            exists (Configuration.sw_tid c0 tid) (Configuration.tid c) 1%nat.
            split; eauto.
            rewrite <- Configuration.sw_to_self.
            econs; eauto.
            instantiate (1 := tid). rewrite PRC_TID_UNCHANGE. eauto.
            econs; eauto.
            instantiate (1 := tid).
            unfold Configuration.sw_tid.
            destruct c, c0; ss.
          }
          {
            subst.
            exploit Config_na_fulfill_step_sc_mem_unchange; eauto.
            ii; des.
            exploit Config_abort_stable; eauto.

            inv x1; ss.
            rewrite IdentMap.gso; eauto.

            introv ABORT'.
            exists (Configuration.sw_tid c0 tid) tid 0%nat.
            split; eauto.
            econs; eauto.
            instantiate (1 := tid).
            destruct c0; ss.
          }
        }
    - inv NA_STEPS.
      eapply IHn in NA; eauto. des.
      rewrite Configuration.sw_tid_twice in NA.
      exploit reorder_na_step_prc_steps; eauto.
      ii; des; subst.
      exploit Config_abort_forwarding_na_fulfill_steps.
      eapply x1.
      instantiate (1 := Configuration.tid c0).
      rewrite Configuration.sw_tid_twice.
      rewrite <- Configuration.sw_to_self; eauto.
      rewrite Configuration.sw_tid_twice.
      ii.
      exists (Configuration.sw_tid c'0 (Configuration.tid c0)) tid n1.
      split; eauto.
      eapply PRCStep_sw; eauto.

      clear - WF_CONFIG STEP.
      destruct c, c1. inv STEP; ss. inv C2; ss.
      unfold Configuration.sw_tid; ss.
      eapply na_steps_is_tau_steps in STEPS.
      eapply Thread_tau_steps_is_all_steps in STEPS.
      eapply na_step_is_tau_step in STEP0.
      eapply Thread_tau_step_is_all_step in STEP0.
      eapply wf_config_sw_prsv with (ctid := tid).
      eapply wf_config_rtc_thread_steps_prsv.
      eapply WF_CONFIG.
      eauto.
      eapply rtc_compose. eapply STEPS.
      eapply Operators_Properties.clos_rt1n_step; eauto.
  Qed.

  Lemma sw_point_forwarding_abort
        lo c c'
        (AUX_NA_OR_SW_STEP: rtc (aux_na_or_sw_step lo) c c')
        (ABORT: Configuration.is_abort c' lo)
        (WF_CONFIG: Configuration.wf c):
    exists c0 tid0 n0,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ Configuration.is_abort c0 lo.
  Proof.
    eapply rtc_rtcn in AUX_NA_OR_SW_STEP. des.
    eapply aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEP.
    des.
    exploit sw_point_forwarding_abort'; eauto.
    destruct c; ss.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
  Qed.

  Lemma sw_point_forwarding_out':
    forall n lo c c' c'' e
      (AUX_NA_OR_SW_STEP: NAStep lo c c' n)
      (OUT: Configuration.aux_step (AuxEvent.out e) lo c' c'')
      (WF_CONFIG: Configuration.wf c),
    exists c0 tid0 n0 c1,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ Configuration.aux_step (AuxEvent.out e) lo c0 c1
      /\ rtc (aux_na_or_sw_step lo) c1 c''
      /\ Configuration.tid c' = Configuration.tid c0.
  Proof.
    induction n; ii.
    - inv AUX_NA_OR_SW_STEP.
      des; subst; ss.
      + exists (Configuration.sw_tid c1 tid) tid 0%nat c''.
        split.
        econs; eauto.
        rewrite Configuration.sw_tid_twice; eauto.
        split; eauto.
      + destruct (Loc.eq_dec tid (Configuration.tid c1)); subst.
        {
          rewrite <- Configuration.sw_to_self in OUT.
          exploit Config_aux_na_out_merge; eauto. ii.
          exists c (Configuration.tid c) 0%nat c''.
          split.
          econs; eauto.
          rewrite Configuration.sw_tid_twice; eauto.
          instantiate (1 := Configuration.tid c).
          rewrite Configuration.sw_to_self; eauto.
          split; eauto.
          split; eauto.
          destruct c, c1; ss.
          inv STEP; ss. inv C2; eauto.
        }
        {
          exploit Config_na_out_reordering_in_diff_threads; eauto.
          ii; des; subst.
          {
            exists (Configuration.sw_tid c' tid) tid 0%nat c''0.
            split; eauto.
            econs; eauto.
            rewrite Configuration.sw_tid_twice; eauto.
            split; eauto.
            split.
            assert (TH: exists lang st lc,
                       IdentMap.find (Configuration.tid c'')
                                     (Configuration.threads c'') =
                         Some (existT _ lang st, lc)).
            {
              inv OUT. destruct c1, c''; ss.
              inv C2. rewrite IdentMap.gss; eauto.
            }
            des.
            eapply Config_na_fulfill_step_to_Config_aux_na_step in x2.
            assert (TH': exists lang st lc,
                       IdentMap.find (Configuration.tid c')
                                     (Configuration.threads c''0) =
                         Some (existT _ lang st, lc)).
            {
              clear - x2. destruct c''0, c'', c'; ss.
              unfold Configuration.sw_tid in *; ss.
              inv x2; ss. inv C2. eauto.
            }
            des.

            clear - x2 TH TH'. destruct c'', c', c''0; ss.
            unfold Configuration.sw_tid in *; ss.
            eapply Relation_Operators.rt1n_trans.
            right.
            econs. ss. eapply TH'. ss.
            eapply Relation_Operators.rt1n_trans.
            left. eapply x2.
            eapply Operators_Properties.clos_rt1n_step.
            right.
            econs. ss. eapply TH. ss.
            
            destruct c'; ss.
          }
          {
            eapply Config_na_fulfill_step_to_Config_aux_na_step in x2.
            exists (Configuration.sw_tid c' tid).
            exists (Configuration.tid c). rewrite <- Configuration.sw_to_self.
            exists 0%nat c''0.
            split; eauto.
            econs; eauto.
            split; eauto.
 
            assert (TH: exists lang st lc,
                       IdentMap.find (Configuration.tid c)
                                     (Configuration.threads c''0) =
                         Some (existT _ lang st, lc)).
            {
              inv x2. destruct c''0, c'', c; ss.
              inv C2. eauto.
            }
            des.
            assert (TH': exists lang st lc,
                       IdentMap.find (Configuration.tid c'')
                                     (Configuration.threads c'') =
                         Some (existT _ lang st, lc)).
            {
              inv OUT. destruct c''0, c'', c; ss.
              inv C2. rewrite IdentMap.gss; eauto.
            }
            des.

            split; eauto.
            eapply Relation_Operators.rt1n_trans.
            right.
            econs. eapply TH. ss.
            eapply Relation_Operators.rt1n_trans.
            left. eapply x2.
            eapply Operators_Properties.clos_rt1n_step.
            right.
            econs. ss. eapply TH'. destruct c''; ss.
          }
        }
    - inv AUX_NA_OR_SW_STEP.
      exploit IHn; [eapply NA | eapply OUT | eauto..].
      {
        clear - WF_CONFIG STEP.
        inv STEP. destruct c, c1; ss. inv C2.
        unfold Configuration.sw_tid in *; ss.
        eapply wf_config_rtc_thread_steps_prsv.
        eapply wf_config_sw_prsv; eauto.
        eauto.
        eapply na_steps_is_tau_steps in STEPS.
        eapply Thread_tau_steps_is_all_steps in STEPS.
        eapply na_step_is_tau_step in STEP0.
        eapply Thread_tau_step_is_all_step in STEP0.
        eapply rtc_n1; eauto.
      }

      ii; des. rewrite Configuration.sw_tid_twice in x.
      exploit reorder_na_step_prc_steps;
        [eapply STEP | eapply x | eapply WF_CONFIG | eauto..].
      ii; des; subst.

      assert (TH: exists lang st lc,
                 IdentMap.find (Configuration.tid c2) (Configuration.threads c2)
                 = Some (existT _ lang st, lc)).
      {
        clear - x0.
        inv x0; ss.
        destruct c0, c2; ss. inv C2.
        rewrite IdentMap.gss; eauto.
      } 
      des.
      clear - x4 x3 x0 x1 x2 WF_CONFIG TH.
      destruct (Loc.eq_dec (Configuration.tid c) (Configuration.tid c0)); subst.
      {
        rewrite e0 in x3. rewrite <- Configuration.sw_to_self in x3.
        eapply Config_na_fulfill_step_to_Config_aux_na_step in x3.
        exploit Config_aux_na_out_merge; eauto.
        introv OUT'.
        eapply PRCStep_sw with (tid' := Configuration.tid c0) in x4.
        exists (Configuration.sw_tid c'0 (Configuration.tid c0)).
        exists tid n1 c2.
        split; eauto.
      }
      {
        exploit Config_na_fulfill_out_reordering_in_diff_threads;
          [eapply x3 | idtac..].
        rewrite Configuration.sw_tid_twice.
        instantiate (2 := Configuration.tid c0).
        rewrite <- Configuration.sw_to_self; eauto.
        ss. eauto.
        exploit wf_config_prc_steps_prsv; eauto.
        {
          clear - WF_CONFIG.
          destruct c; ss.
          unfold Configuration.sw_tid; ss.
          eapply wf_config_sw_prsv; eauto.
        }
        {
          introv WF_CONFIG_TEMP.
          clear - WF_CONFIG_TEMP.
          destruct c'0; ss.
          unfold Configuration.sw_tid; ss.
          eapply wf_config_sw_prsv; eauto.
        }

        ii; des.
        rewrite Configuration.sw_tid_twice in x5.
        unfold Configuration.sw_tid in x7; ss; subst.
        eapply Config_na_fulfill_step_to_Config_aux_na_step in x6.
        eapply PRCStep_sw with (tid' := (Configuration.tid c0)) in x4.
        do 4 eexists.
        split. eapply x4.
        split. eapply x5.
        rewrite <- x2. split; eauto.
        clear - x6 TH x1.
        assert (TH': exists lang st lc,
                   IdentMap.find (Configuration.tid c)
                                 (Configuration.threads c'1)
                   = Some (existT _ lang st, lc)).
        {
          clear - x6.
          inv x6; ss.
          destruct c, c'1, c2; ss. inv C2. eauto.
        }
        des.
        destruct c'1, c2, c; ss.
        unfold Configuration.sw_tid in *; ss.
        eapply Relation_Operators.rt1n_trans.
        right.
        econs. eapply TH'. eauto.
        eapply Relation_Operators.rt1n_trans.
        left. ss. eapply x6.
        eapply Relation_Operators.rt1n_trans.
        right.
        econs. ss. eapply TH.
        ss. eapply x1.
      }
  Qed.
  
  Lemma sw_point_forwarding_out
        lo c c' c'' e
        (AUX_NA_OR_SW_STEP: rtc (aux_na_or_sw_step lo) c c')
        (OUT: Configuration.aux_step (AuxEvent.out e) lo c' c'')
        (WF_CONFIG: Configuration.wf c):
    exists c0 tid0 n0 c1,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ Configuration.aux_step (AuxEvent.out e) lo c0 c1
      /\ rtc (aux_na_or_sw_step lo) c1 c''
      /\ Configuration.tid c' = Configuration.tid c0.
  Proof.
    eapply rtc_rtcn in AUX_NA_OR_SW_STEP. des.
    eapply aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEP.
    des.
    exploit sw_point_forwarding_out'; eauto.
    clear - WF_CONFIG.
    destruct c; ss. unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
  Qed.
    
  Lemma sw_point_forwarding_atm':
    forall n lo c c' c''
      (AUX_NA_OR_SW_STEP: NAStep lo c c' n)
      (ATM: Configuration.aux_step AuxEvent.atm lo c' c'')
      (WF_CONFIG: Configuration.wf c),
    exists c0 tid0 n0 c1,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ Configuration.aux_step AuxEvent.atm lo c0 c1
      /\ rtc (aux_na_or_sw_step lo) c1 c''
      /\ Configuration.tid c' = Configuration.tid c0.
  Proof.
    induction n; ii.
    - inv AUX_NA_OR_SW_STEP.
      des; subst.
      + exists (Configuration.sw_tid c1 tid) tid 0%nat c''.
        split; eauto.
        econs; eauto.
        rewrite Configuration.sw_tid_twice; eauto.
      + destruct (Loc.eq_dec tid (Configuration.tid c1)); subst.
        {
          rewrite <- Configuration.sw_to_self in ATM.
          exploit Config_aux_na_atm_merge; eauto.
          ii.
          exists c (Configuration.tid c) 0%nat c''.
          split; eauto.
          econs; eauto. rewrite Configuration.sw_tid_twice; eauto.
          instantiate (1 := Configuration.tid c).
          rewrite Configuration.sw_to_self; eauto.
          split; eauto.
          split; eauto.
          ss.
          clear - STEP.
          destruct c, c1; ss.
          inv STEP; ss. inv C2; ss.
        }
        {
          exploit Config_na_atm_reordering_in_diff_threads; eauto.
          ii; des; subst.

          exists (Configuration.sw_tid c' tid) tid 0%nat c''0.
          split; eauto.
          econs; eauto. rewrite Configuration.sw_tid_twice; eauto.
          split; eauto. 
          assert (TH1: exists lang st lc,
                     IdentMap.find (Configuration.tid c') (Configuration.threads c''0) = Some (existT _ lang st, lc)).
          {
            clear - x2.
            destruct c''0, c'', c'; ss. unfold Configuration.sw_tid in *; ss.
            inv x2; ss. inv C2. eauto.
          }
          des.
          assert (TH2: exists lang st lc,
                     IdentMap.find (Configuration.tid c'') (Configuration.threads c'') = Some (existT _ lang st, lc)).
          {
            clear - ATM. destruct c1, c''; ss.
            unfold Configuration.sw_tid in *; ss.
            inv ATM; ss. inv C2. rewrite IdentMap.gss; eauto.
          }
          des.
          split.
          eapply Relation_Operators.rt1n_trans.
          right. econs; eauto.
          eapply Relation_Operators.rt1n_trans.
          left. eapply Config_na_fulfill_step_to_Config_aux_na_step in x2. eauto.
          eapply Relation_Operators.rt1n_trans.
          right.
          econs; eauto.
          destruct c''; ss. eauto.
          eauto.
 
          exists (Configuration.sw_tid c' tid) (Configuration.tid c).
          exists 0%nat c''0.
          rewrite <- Configuration.sw_to_self.
          split.
          econs; eauto.
          split; eauto.
          ss. split; eauto.
          assert (TH1: exists lang st lc,
                     IdentMap.find (Configuration.tid c) (Configuration.threads c''0) = Some (existT _ lang st, lc)).
          {
            clear - x2.
            destruct c''0, c'', c; ss. unfold Configuration.sw_tid in *; ss.
            inv x2; ss. inv C2. eauto.
          }
          des.
          assert (TH2: exists lang st lc,
                     IdentMap.find (Configuration.tid c'') (Configuration.threads c'') = Some (existT _ lang st, lc)).
          {
            clear - ATM. destruct c1, c''; ss.
            unfold Configuration.sw_tid in *; ss.
            inv ATM; ss. inv C2. rewrite IdentMap.gss; eauto.
          }
          des.

          eapply Relation_Operators.rt1n_trans.
          right. econs; eauto.
          eapply Relation_Operators.rt1n_trans.
          left. eapply Config_na_fulfill_step_to_Config_aux_na_step in x2. eauto.
          eapply Relation_Operators.rt1n_trans.
          right.
          econs; eauto.
          destruct c''; ss. eauto.
        }
    - inv AUX_NA_OR_SW_STEP.
      exploit IHn; eauto.
      {
        clear - WF_CONFIG STEP.
        destruct c, c1; ss. unfold Configuration.sw_tid in *; ss.
        inv STEP; ss. inv C2.
        eapply wf_config_sw_prsv with (ctid := tid); eauto.
        eapply wf_config_rtc_thread_steps_prsv; eauto.
        eapply na_steps_is_tau_steps in STEPS.
        eapply Thread_tau_steps_is_all_steps in STEPS.
        eapply na_step_is_tau_step in STEP0.
        eapply Thread_tau_step_is_all_step in STEP0.
        eapply rtc_n1; eauto.
      }

      ii; des.
      exploit reorder_na_step_prc_steps; eauto.
      ii; des; subst.
      destruct (Loc.eq_dec (Configuration.tid c) (Configuration.tid c0)).
      {
        rewrite e in x3. rewrite <- Configuration.sw_to_self in x3.
        eapply Config_na_fulfill_step_to_Config_aux_na_step in x3.
        exploit Config_aux_na_atm_merge; eauto. ii.
        exists (Configuration.sw_tid c'0 (Configuration.tid c0)) tid n1 c2.
        split; eauto.
        eapply PRCStep_sw; eauto.
      }
      {
        rewrite Configuration.sw_tid_twice in x.
        exploit Config_na_fulfill_atm_reordering_in_diff_threads; eauto.
        rewrite Configuration.sw_tid_twice.
        rewrite <- Configuration.sw_to_self. eauto.
        eapply wf_config_prc_steps_prsv in x4; eauto.
        clear - x4.
        destruct c'0, c; ss.
        unfold Configuration.sw_tid; ss.
        eapply wf_config_sw_prsv; eauto.
        clear - WF_CONFIG.
        destruct c; ss.
        unfold Configuration.sw_tid; ss.
        eapply wf_config_sw_prsv; eauto.

        ii; des; subst; ss.
        rewrite Configuration.sw_tid_twice in x6.
        exists (Configuration.sw_tid c'0 (Configuration.tid c0)) tid.
        exists n1 c'1.
        split; eauto.
        eapply PRCStep_sw; eauto.
        split; eauto. 
        clear - x5 x1 x0 x2.
        assert (TH1: exists lang st lc,
                   IdentMap.find (Configuration.tid c) (Configuration.threads c'1) = Some (existT _ lang st, lc)).
        {
          destruct c'1, c, c2; ss. unfold Configuration.sw_tid in *; ss.
          inv x5; ss. inv C2. eauto.
        }
        des. 
        assert (TH2: exists lang st lc,
                   IdentMap.find (Configuration.tid c2) (Configuration.threads c2) = Some (existT _ lang st, lc)).
        {
          destruct c', c''; ss.
          inv x0; ss. inv C2; ss. rewrite IdentMap.gss; eauto.
        }
        des.
        split.
        eapply Config_na_fulfill_step_to_Config_aux_na_step in x5.
        destruct c'1, c'', c2, c; ss.
        unfold Configuration.sw_tid in *; ss.
        eapply Relation_Operators.rt1n_trans.
        right. econs; eauto. ss.
        eapply Relation_Operators.rt1n_trans.
        left. eapply x5.
        eapply Relation_Operators.rt1n_trans.
        right. econs; eauto. ss.
        ss.
      }
  Qed.
  
  Lemma sw_point_forwarding_atm
        lo c c' c''
        (AUX_NA_OR_SW_STEP: rtc (aux_na_or_sw_step lo) c c')
        (OUT: Configuration.aux_step AuxEvent.atm lo c' c'')
        (WF_CONFIG: Configuration.wf c):
    exists c0 tid0 n0 c1,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ Configuration.aux_step AuxEvent.atm lo c0 c1
      /\ rtc (aux_na_or_sw_step lo) c1 c''
      /\ Configuration.tid c' = Configuration.tid c0.
  Proof.
    eapply rtc_rtcn in AUX_NA_OR_SW_STEP. des.
    eapply aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEP.
    des.
    exploit sw_point_forwarding_atm'; eauto.
    clear - WF_CONFIG.
    destruct c; ss. unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
  Qed.

  Lemma sw_point_forwarding_prc':
    forall n lo c c' c''
      (AUX_NA_OR_SW_STEP: NAStep lo c c' n)
      (ATM: Configuration.aux_step AuxEvent.prc lo c' c'')
      (WF_CONFIG: Configuration.wf c),
    exists c0 tid0 n0,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ rtc (aux_na_or_sw_step lo) c0 c''.
  Proof.
    induction n; ii.
    - inv AUX_NA_OR_SW_STEP. des; subst.
      + exists c'' tid 0%nat.
        split. econs; eauto.
        instantiate (1 := Configuration.tid c'').
        rewrite Configuration.sw_to_self; eauto. eauto.
      + destruct (Loc.eq_dec (Configuration.tid c1) tid); subst.
        {
          rewrite <- Configuration.sw_to_self in ATM.
          exploit Config_na_prc_reordering_in_same_thread; eauto.
          ii; des.
          exists c' (Configuration.tid c) 0%nat.
          rewrite <- Configuration.sw_to_self; eauto.
          split; eauto.
          econs; eauto.
          instantiate (1 := Configuration.tid c').
          rewrite Configuration.sw_to_self; eauto.
          eapply Operators_Properties.clos_rt1n_step.
          left.
          eapply Config_na_fulfill_step_to_Config_aux_na_step; eauto.
        }
        {
          exploit Config_na_prc_reordering_in_diff_threads; eauto.
          ii; des; subst.
          {
            eapply Config_na_fulfill_step_to_Config_aux_na_step in x2.
            assert (TH: exists lang st lc,
                       IdentMap.find (Configuration.tid c'') (Configuration.threads c'') =
                         Some (existT _ lang st, lc)).
            {
              clear - ATM.
              destruct c1, c''; ss. inv ATM; ss. inv C2; ss.
              rewrite IdentMap.gss; eauto.
            }
            des.
 
            exists (Configuration.sw_tid c''0 (Configuration.tid c')).
            exists tid 0%nat.
            split.
            econs; eauto.
            eapply Relation_Operators.rt1n_trans.
            left. eauto.
            eapply Relation_Operators.rt1n_trans.
            right.
            econs; eauto.
            destruct c''; ss. eauto.
          }
          {
            eapply Config_na_fulfill_step_to_Config_aux_na_step in x2.
            destruct (Loc.eq_dec (Configuration.tid c') tid); subst.
            {
              rewrite <- Configuration.sw_to_self in x1.
              exploit Config_aux_prc_steps_merge;
                [eapply x0 | eapply x1 | eauto..].
              ii. clear x0 x1.
              exists (Configuration.sw_tid c''0 (Configuration.tid c)).
              exists (Configuration.tid c) 0%nat.
              split; eauto.
              eapply PRCStep_sw.
              rewrite <- Configuration.sw_to_self.
              econs; eauto.
              instantiate (1 := Configuration.tid c''0).
              rewrite <- Configuration.sw_to_self; eauto.
              assert (TH: exists lang st lc,
                         IdentMap.find (Configuration.tid c'') (Configuration.threads c'') =
                           Some (existT _ lang st, lc)).
              {
                clear - ATM. destruct c1, c', c''; ss.
                inv ATM; ss. inv C2; ss.
                rewrite IdentMap.gss; eauto.
              }
              des.
              eapply Relation_Operators.rt1n_trans.
              left. eauto.
              eapply Relation_Operators.rt1n_trans.
              right. econs; eauto.
              destruct c''; ss. eauto.
            }
            {
              exists (Configuration.sw_tid c''0 (Configuration.tid c)).
              exists (Configuration.tid c) 1%nat.
              rewrite <- Configuration.sw_to_self.
              split.
              econs; eauto. econs; eauto.
              assert (TH: exists lang st lc,
                         IdentMap.find (Configuration.tid c'') (Configuration.threads c'')
                         = Some (existT _ lang st, lc)).
              {
                clear - ATM. destruct c1, c''; ss.
                inv ATM; ss. inv C2.
                rewrite IdentMap.gss; eauto.
              }
              des.
              eapply Relation_Operators.rt1n_trans.
              left. eauto.
              eapply Relation_Operators.rt1n_trans. 2: eauto.
              right. econs; eauto.
              destruct c''; ss.
            }
          }
        }
    - inv AUX_NA_OR_SW_STEP.
      exploit IHn; [eapply NA | eapply ATM | eauto..].
      {
        eapply wf_config_ConfigAux_na_step in STEP; eauto.
        destruct c1; ss.
        unfold Configuration.sw_tid; ss.
        eapply wf_config_sw_prsv; eauto.
      }
      ii; des.
      rewrite Configuration.sw_tid_twice in x.

      exploit reorder_na_step_prc_steps; eauto.
      ii; des; subst.
      eapply rtc_rtcn in x0; des.
      eapply aux_na_or_sw_steps_to_na_aux_steps in x0. des.
      eapply Config_na_fulfill_step_to_Config_aux_na_step in x1.

      exploit NAStep_merge2; [eapply x1 | eapply x0 | eauto..].
      ii; des.
      exists (Configuration.sw_tid c'0 (Configuration.tid c)).
      exists tid n1.
      split. eapply PRCStep_sw; eauto.
      assert (TH: exists lang st lc,
                 IdentMap.find (Configuration.tid c'') (Configuration.threads c'') = Some (existT _ lang st, lc)).
      {
        clear - ATM. destruct c', c''; ss.
        inv ATM; ss. inv C2; ss.
        rewrite IdentMap.gss; eauto.
      }
      des.
      exploit NAStep_to_aux_na_or_sw_steps;
        [eapply x4 | eapply TH | eauto..].
      ii; des; ss. rewrite Configuration.sw_tid_twice in x5.
      eapply Relation_Operators.rt1n_trans.
      right. econs; eauto.
      ss.
  Qed.
  
  Lemma sw_point_forwarding_prc
        lo c c' c''
        (AUX_NA_OR_SW_STEP: rtc (aux_na_or_sw_step lo) c c')
        (OUT: Configuration.aux_step AuxEvent.prc lo c' c'')
        (WF_CONFIG: Configuration.wf c):
    exists c0 tid0 n0,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ rtc (aux_na_or_sw_step lo) c0 c''.
  Proof.
    eapply rtc_rtcn in AUX_NA_OR_SW_STEP. des.
    eapply aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEP.
    des.
    exploit sw_point_forwarding_prc'; eauto.
    clear - WF_CONFIG.
    destruct c; ss. unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
  Qed.

  Lemma sw_point_forwarding_tterm':
    forall n lo c c' c''
      (AUX_NA_OR_SW_STEP: NAStep lo c c' n)
      (TTERM: Configuration.aux_step AuxEvent.tterm lo c' c'')
      (WF_CONFIG: Configuration.wf c),
    exists c0 tid0 c1 c2 n0,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ (c0 = c1 \/ Configuration.aux_step AuxEvent.na lo c0 c1)
      /\ Configuration.aux_step AuxEvent.tterm lo c1 c2
      /\ rtc (aux_na_or_sw_step lo) c2 c''.
  Proof.
    induction n; ii.
    - inv AUX_NA_OR_SW_STEP.
      des; subst.
      + exists (Configuration.sw_tid c1 tid) tid.
        exists (Configuration.sw_tid c1 tid) c'' 0%nat.
        split.
        econs; eauto.
        rewrite Configuration.sw_tid_twice; eauto.
        split; eauto.
      + destruct (Loc.eq_dec tid (Configuration.tid c1)); subst.
        {
          rewrite <- Configuration.sw_to_self in TTERM.
          exists c (Configuration.tid c).
          exists c1 c'' 0%nat.
          rewrite <- Configuration.sw_to_self; eauto.
          split. econs; eauto.
          instantiate (1 := Configuration.tid c).
          rewrite <- Configuration.sw_to_self; eauto.
          split; eauto.
        }
        {
          exploit Config_na_tterm_reordering_in_diff_threads; eauto.
          assert (TID_EQ: Configuration.tid c = Configuration.tid c1).
          {
            clear - STEP.
            destruct c, c1; ss. inv STEP; ss. inv C2; ss.
          }
          rewrite TID_EQ. eauto.

          ii; des.
          exists (Configuration.sw_tid c tid) tid.
          exists (Configuration.sw_tid c tid) c0 0%nat.
          split.
          econs; eauto. ss.
          split; eauto.
          split; eauto.
          assert (TH: exists lang st lc,
                     IdentMap.find (Configuration.tid c) (Configuration.threads c0) =
                       Some (existT _ lang st, lc)).
          {
            clear - x1. destruct c0, c, c''; ss.
            inv x1; ss. inv C2; ss. eauto.
          }
          des.
          assert (TH': exists lang st lc,
                     IdentMap.find (Configuration.tid c'') (Configuration.threads c'') =
                       Some (existT _ lang st, lc)).
          {
            clear - TTERM. destruct c1, c''; ss.
            unfold Configuration.sw_tid in *; ss.
            inv TTERM; ss. inv C2; ss. eauto.
          }
          des.

          eapply Relation_Operators.rt1n_trans.
          right. econs; eauto.
          eapply Relation_Operators.rt1n_trans.
          left. eauto.
          eapply Relation_Operators.rt1n_trans. 2: eauto.
          right. econs; eauto.
          destruct c''; ss.
        }
    - inv AUX_NA_OR_SW_STEP.
      exploit IHn; [eapply NA | eapply TTERM | eauto..].
      {
        eapply wf_config_ConfigAux_na_step in STEP; eauto.
        destruct c1; ss.
        unfold Configuration.sw_tid; ss.
        eapply wf_config_sw_prsv; eauto.
      }
      ii; des; subst.
      + rewrite Configuration.sw_tid_twice in x.
        exploit reorder_na_step_prc_steps; eauto.
        ii; des; subst; ss.
        eapply Config_na_fulfill_step_to_Config_aux_na_step in x0.
        destruct (Loc.eq_dec (Configuration.tid c) (Configuration.tid c2)).
        {
          rewrite e in x0. rewrite <- Configuration.sw_to_self in x0.
          exists (Configuration.sw_tid c'0 (Configuration.tid c2)) tid.
          exists c2 c3 n1.
          split. eapply PRCStep_sw; eauto.
          split; eauto.
        }
        {
          exploit Config_na_tterm_reordering_in_diff_threads; eauto.
          rewrite Configuration.sw_tid_twice.
          rewrite <- Configuration.sw_to_self. eauto.
          rewrite Configuration.sw_tid_twice. ss.
          ii; des.  
          exists (Configuration.sw_tid c'0 (Configuration.tid c2)) tid.
          exists (Configuration.sw_tid c'0 (Configuration.tid c2)).
          exists c0 n1.
          split. eapply PRCStep_sw; eauto.
          split; eauto.
          split; eauto. 
          clear - x4 x2 TTERM.
          exploit aux_na_or_sw_step_th_valid; eauto.
          ii; des; subst.
          {
            clear - x4 x0 x1.
            assert (TH1: exists lang st lc, 
                     IdentMap.find (Configuration.tid c) (Configuration.threads c0)
                     = Some (existT _ lang st, lc)).
            {
              clear - x4. destruct c, c0; ss.
              unfold Configuration.sw_tid in *; ss.
              inv x4; ss. inv C2; ss. eauto.
            }
            des.
            assert (TH2: exists lang st lc,
                       IdentMap.find tid (Configuration.threads c3)
                       = Some (existT _ lang st, lc)).
            {
              clear - x0. destruct c3; ss.
              unfold Configuration.sw_tid in *; ss.
              inv x0; ss. inv C2. eauto.
            }
            des.
            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            eapply Relation_Operators.rt1n_trans.
            left. eauto.
            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            destruct c3, c, c''; ss.
          }
          {
            assert (TH1: exists lang st lc,
                       IdentMap.find (Configuration.tid c'') (Configuration.threads c'')
                       = Some (existT _ lang st, lc)).
            {
              clear - TTERM. destruct c', c''; ss.
              inv TTERM; ss. inv C2.
              eauto.
            }
            des.
            assert (TH2: exists lang st lc,
                       IdentMap.find (Configuration.tid c) (Configuration.threads c0)
                       = Some (existT _ lang st, lc)).
            {
              clear - x4. destruct c0, c, c''; ss.
              unfold Configuration.sw_tid in *; ss.
              inv x4; ss. inv C2; ss. eauto.
            }
            des.

            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            eapply Relation_Operators.rt1n_trans.
            left. eauto.
            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            destruct c''; ss; eauto.
          }
        }
      + rewrite Configuration.sw_tid_twice in x.
        exploit reorder_na_step_prc_steps;
          [eapply STEP | eapply x | eauto..].
        ii; des; subst; ss.
        destruct (Loc.eq_dec (Configuration.tid c) (Configuration.tid c0)).
        {
          eapply Config_na_fulfill_step_to_Config_aux_na_step in x3.
          rewrite e in x3. rewrite <- Configuration.sw_to_self in x3.
          exploit Config_aux_na_merge; [eapply x3 | eapply x0 | eauto..].
          introv NA_STEP.
          exists (Configuration.sw_tid c'0 (Configuration.tid c0)) tid.
          exists c2 c3 n1.
          split.
          eapply PRCStep_sw; eauto.
          split. right. eauto.
          split; eauto.
        }
        {
          exploit Config_na_fulfill_na_reordering_in_diff_threads;
            [eapply x3 | eauto..].
          rewrite Configuration.sw_tid_twice.
          rewrite <- Configuration.sw_to_self; eauto.
          eapply wf_config_prc_steps_prsv in x4; eauto.
          clear - x4.
          destruct c'0, c; ss.
          unfold Configuration.sw_tid; ss.
          eapply wf_config_sw_prsv; eauto.
          clear - WF_CONFIG.
          destruct c; ss.
          unfold Configuration.sw_tid; ss.
          eapply wf_config_sw_prsv; eauto.

          ii; des; ss; subst.
          rewrite Configuration.sw_tid_twice in x6.
          clear x3.
          eapply Config_na_fulfill_step_to_Config_aux_na_step in x5.
          assert (TID_EQ: Configuration.tid c0 = Configuration.tid c2).
          {
            clear - x0. destruct c0, c2; ss.
            inv x0; ss. inv C2; ss.
          }
          exploit Config_na_tterm_reordering_in_diff_threads;
            [eapply x5 | eauto..].
          rewrite Configuration.sw_tid_twice.
          rewrite TID_EQ. rewrite <- Configuration.sw_to_self. eauto.
          rewrite Configuration.sw_tid_twice. ss.
          ii; des. clear x5.

          assert (TID_EQ': Configuration.tid c0 = Configuration.tid c'1).
          {
            clear - x6.
            destruct c'0, c0, c'1; ss.
            unfold Configuration.sw_tid in *; ss.
            inv x6; ss. inv C2; ss.
          }
          rewrite TID_EQ' in x7. rewrite <- Configuration.sw_to_self in x7; eauto.
          exists (Configuration.sw_tid c'0 (Configuration.tid c0)) tid.
          exists c'1 c4 n1.
          split; eauto.
          eapply PRCStep_sw; eauto.
          split; eauto.
          split; eauto.
          clear - x3 x2 TTERM.
          eapply aux_na_or_sw_step_th_valid in x2; eauto.
          assert (TH1: exists lang st lc,
                     IdentMap.find (Configuration.tid c) (Configuration.threads c4)
                     = Some (existT _ lang st, lc)).
          {
            clear - x3. destruct c3, c4, c; ss.
            unfold Configuration.sw_tid in *; ss.
            inv x3; ss. inv C2; ss. eauto.
          }
          des; subst.
          {
            assert (TH2: exists lang st lc,
                       IdentMap.find tid (Configuration.threads c3) = Some (existT _ lang st, lc)).
            {
              clear - x2. destruct c3; ss.
              unfold Configuration.sw_tid in *; ss.
              inv x2; ss. inv C2; ss. eauto.
            }
            des.
            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            eapply Relation_Operators.rt1n_trans.
            left. eauto.
            eapply Relation_Operators.rt1n_trans.
            right. eauto.
            destruct c3; ss.
          }
          {
            assert (TH2: exists lang st lc,
                       IdentMap.find (Configuration.tid c'') (Configuration.threads c'') = Some (existT _ lang st, lc)).
            {
              clear - TTERM.
              destruct c', c''; ss. inv TTERM; ss. inv C2; ss.
              eauto.
            }
            des.
            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            eapply Relation_Operators.rt1n_trans.
            left. eauto.
            eapply Relation_Operators.rt1n_trans.
            right. econs; eauto.
            destruct c''; ss. eauto.
          }
        }
  Qed.
        
  Lemma sw_point_forwarding_tterm
        lo c c' c''
        (AUX_NA_OR_SW_STEP: rtc (aux_na_or_sw_step lo) c c')
        (TTERM: Configuration.aux_step AuxEvent.tterm lo c' c'')
        (WF_CONFIG: Configuration.wf c):
    exists c0 tid0 c1 c2 n0,
      PRCStep lo (Configuration.sw_tid c tid0) c0 n0
      /\ (c0 = c1 \/ Configuration.aux_step AuxEvent.na lo c0 c1)
      /\ Configuration.aux_step AuxEvent.tterm lo c1 c2
      /\ rtc (aux_na_or_sw_step lo) c2 c''.
  Proof.
    eapply rtc_rtcn in AUX_NA_OR_SW_STEP. des.
    eapply aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEP.
    des.
    exploit sw_point_forwarding_tterm'; eauto.
    clear - WF_CONFIG.
    destruct c; ss.
    unfold Configuration.sw_tid; ss.
    eapply wf_config_sw_prsv; eauto.
  Qed.
    
  Lemma swprocs_to_npetr:
    forall n ths tid sc mem lo c' behs
      (SW_PROCS: sw_procs lo (Configuration.mk ths tid sc mem) c' behs n)
      (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem)),
    exists n',
      NPconf_behaviors (NPConfiguration.mk (Configuration.mk ths tid sc mem) true) lo n' behs.
  Proof.
    induction n; ii. 
    - inv SW_PROCS. 
      + (* nil *)
        exists 0%nat. eapply behaviors_nil.
      + (* done *)
        exploit construct_done; eauto.
        introv CONS_DONE. des.
        {
          (* Done after na steps *)
          unfold Configuration.sw_tid in CONS_DONE; ss.
          assert (TID'_EXT: exists lang st lc,
                     IdentMap.find tid' ths = Some (existT _ lang st, lc)).
          {
            inv CONS_DONE; ss.
            eauto.
          }
          des.
          eapply Config_aux_na_step_to_NPConfig_step
            with (b := true) in CONS_DONE; eauto.
          exists 3%nat. 
          eapply behaviors_tau.
          right.
          eapply NPConfiguration.step_sw; eauto.
          ss.
          eapply behaviors_tau.
          left. eauto.
          econs; eauto.
          eapply wf_config_sw_prsv; eauto.
        }
        {
          subst.
          unfold Configuration.sw_tid in *; ss.
          assert (TID'_EXT: exists lang st lc,
                     IdentMap.find tid' ths = Some (existT _ lang st, lc)).
          {
            inv DONE; ss.
            des. eauto.
          }
          des.

          exists 2%nat.
          eapply behaviors_tau.
          right.
          eapply NPConfiguration.step_sw; eauto.
          ss.
          econs; eauto.
        }
      + (* abort *)
        exploit sw_point_forwarding_abort; eauto.
        unfold Configuration.sw_tid; ss.
        ii; des.
        assert (TH0: exists lang0 st0 lc0,
                   IdentMap.find (Configuration.tid c0) (Configuration.threads c0)
                   = Some (existT _ lang0 st0, lc0)).
        {
          inv x1. des; eauto.
        }
        des.
        eapply PRCStep_to_NPConf_steps with (tid := tid) in x0; eauto.
        unfold Configuration.sw_tid in x0. ss.
        eapply rtc_rtcn in x0. des.
        eapply prefix_tau_np_behav_construct in x0.
        instantiate (1 := [VisibleEvent.abort]) in x0. des.
        exists n'. eauto. 
        instantiate (1 := 1%nat). econs; eauto.
        eapply Config_abort_to_NPConfig_abort; eauto.
        eapply wf_config_sw_prsv; eauto.
    - inv SW_PROCS.
      + (* output *)
        exploit sw_point_forwarding_out; eauto.
        ii; des. unfold Configuration.sw_tid in x0; ss.
        exploit sw_procs_merge; eauto. introv SW_N'.
        destruct c3; ss.
        exploit IHn; [eapply SW_N' | eauto..].
        {
          clear - WF_CONFIG x0 x1.
          eapply wf_config_sw_prsv with (ntid := tid0) in WF_CONFIG.
          eapply wf_config_prc_steps_prsv in x0; eauto.
          eapply wf_config_output_step_prsv; eauto.
        }

        ii; des.
        clear - x0 x1 x x3 WF_CONFIG.
        assert (TH: exists lang st lc,
                   IdentMap.find (Configuration.tid c0) (Configuration.threads c0)
                   = Some (existT _ lang st, lc)).
        {
          clear - x1.
          destruct c0; ss. inv x1; ss. inv C2.
          eauto.
        }
        des.
        exploit PRCStep_to_NPConf_steps; eauto.
        eapply wf_config_sw_prsv; eauto.

        ii; des.
        instantiate (1 := tid) in x4.
        unfold Configuration.sw_tid in *; ss. 
        eapply Configuration_aux_output_step_to_NPConfig_step with (b := true) in x1; eauto.
        des; ss; subst.
        {
          clear - x4 x2 x.
          exploit behaviors_out.
          eapply x2. eapply x. ii.
          eapply rtc_rtcn in x4. des.
          exploit prefix_tau_np_behav_construct; eauto.
        }
        {
          clear - x1 x2 x x4.
          exploit behaviors_out.
          eapply x2. eapply x. ii.
          exploit rtc_n1; [eapply x4 | eauto..].
          econs; eauto. ii; des; ss.
          ii.
          clear - x5 x3.
          eapply rtc_rtcn in x5. des.
          exploit prefix_tau_np_behav_construct;
            [eapply x5 | eapply x3 | eauto..].
        }
      + (* atm/prc/tterm step *) 
        destruct AT_PRC_TTERM_STEP as [AT_STEP | PRC_TTERM_STEP].
        {
          (* atm step *)
          exploit sw_point_forwarding_atm; eauto.
          ii; des. unfold Configuration.sw_tid in x0; ss.
          exploit sw_procs_merge; eauto. introv SW_N'.
          destruct c3; ss.
          exploit IHn; [eapply SW_N' | eauto..].
          {
            clear - WF_CONFIG x0 x1.
            eapply wf_config_sw_prsv with (ntid := tid0) in WF_CONFIG.
            eapply wf_config_prc_steps_prsv in x0; eauto.
            destruct c0; ss.
            inv x1; ss. inv C2.
            eapply prc_steps_is_tau_steps in STEPS_PRC.
            eapply PS_and_APS.atmblk_steps_is_tau_steps in STEPS_ATM.
            eapply PS_and_APS.atmblk_step_is_tau_steps in STEP_ATM.
            eapply Thread_tau_steps_is_all_steps in STEPS_PRC, STEPS_ATM, STEP_ATM.
            eapply wf_config_rtc_thread_steps_prsv.
            eauto. eauto.
            eapply rtc_compose. eapply STEPS_PRC.
            eapply rtc_compose. eapply STEPS_ATM. eapply STEP_ATM.
          }

          ii; des.
          clear - WF_CONFIG x0 x1 x.
          assert (TH: exists lang st lc,
                     IdentMap.find (Configuration.tid c0) (Configuration.threads c0)
                     = Some (existT _ lang st, lc)).
          {
            clear - x1.
            destruct c0; ss. inv x1; ss. inv C2.
            eauto.
          }
          des.
          assert (WF_CONFIG': Configuration.wf c0).
          {
            eapply wf_config_prc_steps_prsv; eauto.
            eapply wf_config_sw_prsv; eauto.
          }
          exploit PRCStep_to_NPConf_steps; eauto.
          eapply wf_config_sw_prsv; eauto.
          instantiate (1 := tid). unfold Configuration.sw_tid; ss.
          ii. clear x0 TH.
          eapply Config_aux_atm_step_to_NPConfig_step in x1; eauto.
          exploit rtc_n1; [eapply x3 | eapply x1 | eauto..].
          clear x1 x3. ii.
          eapply rtc_rtcn in x2. des.
          exploit prefix_tau_np_behav_construct; eauto.
        }
        destruct PRC_TTERM_STEP as [PRC_STEP | TTERM_STEP].
        {
          (* prc step *)
          exploit sw_point_forwarding_prc; eauto.
          unfold Configuration.sw_tid; ss. ii; des.
          exploit sw_procs_merge; eauto. introv SW_N'. clear x1.
          destruct c0.
          exploit IHn; [eapply SW_N' | eauto..].
          eapply wf_config_prc_steps_prsv; eauto.
          eapply wf_config_sw_prsv; eauto.

          ii; des.
          exploit PRC_steps_cons_NPConf_behav; [eapply x0 | eapply x | eauto..].
          {
            eapply wf_config_sw_prsv; eauto.
          }
          ii; des.
          eapply NPconf_behav_sw with (tid := tid) in x2; eauto.
        }
        {
          (* thread term step *)
          exploit sw_point_forwarding_tterm; eauto.
          unfold Configuration.sw_tid in *; ss.
          ii; des; subst.
          {
            exploit sw_procs_merge; eauto. introv SW_N'. clear x3 SW_N.
            destruct c4.
            eapply IHn in SW_N'; eauto. des.
            eapply Config_aux_tterm_to_NPConfig_step with (b := true) in x2.
            exploit behaviors_tau.
            right. eapply x2. eapply SW_N'.
            ii.
            exploit PRC_steps_cons_NPConf_behav;
              [eapply x0 | eapply x1 | eauto..].
            {
              eapply wf_config_sw_prsv; eauto.
            }

            ii; des.
            eapply NPconf_behav_sw with (tid := tid) in x3; eauto.
            eapply wf_config_prc_steps_prsv in x0; eauto.
            clear - x0 x2. destruct c3; ss.
            inv x2; ss. inv C2; ss.
            eapply wf_config_rm_prsv; eauto.
            eapply wf_config_sw_prsv; eauto.
          }
          {
            exploit sw_procs_merge; eauto. introv SW_N'. clear x3 SW_N.
            destruct c4.
            eapply IHn in SW_N'; eauto. des.
            eapply Config_aux_tterm_to_NPConfig_step with (b := false) in x2.
            eapply Config_aux_na_step_to_NPConfig_step with (b := true) in x1.
            exploit behaviors_tau.
            right. eapply x2. eapply SW_N'. ii.
            exploit behaviors_tau.
            left. eapply x1. eauto. ii.
            exploit PRC_steps_cons_NPConf_behav;
              [eapply x0 | eapply x4 | eauto..].
            {
              eapply wf_config_sw_prsv; eauto.
            }
            ii; des.
            eapply NPconf_behav_sw with (tid := tid) in x5; eauto.
            eapply wf_config_prc_steps_prsv in x0; eauto.
            eapply wf_config_sw_prsv; eauto.
            destruct c0, c3; ss.
            inv x2; ss. inv C2.
            eapply wf_config_prc_steps_prsv in x0; eauto.
            eapply wf_config_rm_prsv with (ctid := tid3); eauto.
            inv x1; ss. inv C2; ss.
            eapply na_steps_is_tau_steps in STEPS.
            eapply Thread_tau_steps_is_all_steps in STEPS.
            eapply na_step_is_tau_step in STEP.
            eapply Thread_tau_step_is_all_step in STEP.
            eapply wf_config_rtc_thread_steps_prsv.
            eauto.
            eauto.
            eapply rtc_n1. eapply STEPS. eapply STEP.
            eapply wf_config_sw_prsv; eauto.
          }
        }
  Qed.
  
  Lemma sema_implies_aps_np {lang:language}
        (code: Language.syntax lang) lo fs behs ctid
        (AUX_BEH: aux_prog_behaviors fs code ctid lo behs):
    NPprog_behaviors fs code ctid lo behs.
  Proof.
    unfold aux_prog_behaviors in AUX_BEH. des.
    exploit aetr_to_swprocs; eauto. ii; des.
    unfold NPprog_behaviors.
    exploit wf_config_init; eauto. introv WF_CONFIG_INIT.
    destruct c; ss.
    exploit swprocs_to_npetr; eauto.
    ii; des.
    assert (CTID: ctid = tid).
    {
      clear - AUX_BEH.
      unfold Configuration.init in AUX_BEH.
      destruct (Threads.init fs code); ss.
      inv AUX_BEH. eauto.
    }
    subst tid.

    exists n'0 (NPConfiguration.mk (Configuration.mk threads ctid sc memory) true).
    split; eauto.

    unfold NPConfiguration.init.
    rewrite AUX_BEH; eauto.
  Qed.
End APS_and_NP.

Lemma NPConfig_step_to_Config_step
      e lo npc npc'
      (NPCONFIG_STEP: NPConfiguration.step e lo npc npc'):
  Configuration.step e lo
                     (NPConfiguration.cfg npc) (NPConfiguration.cfg npc').
Proof.
  inv NPCONFIG_STEP; des; subst; ss.
  - eapply NPAuxThread_tau_steps_2_Thread_tau_steps in STEPS; ss.
    eapply NPAuxThread_tau_step_2_Thread_tau_step in STEP; ss.
    econs; eauto.
    ss.
    eapply ConsistentProp.Thread_consistent_nprm_to_consistent; eauto.
  - econs; eauto.
  - eapply Configuration.step_thread_term; eauto.
  - inv STEP; ss.
    econs; eauto.
    ss.
    eapply ConsistentProp.Thread_consistent_nprm_to_consistent; eauto.
Qed.

Lemma NPConfig_all_step_to_Config_all_step
      npc npc' lo
      (NP_ALL_STEP: NPConfiguration.all_step lo npc npc'):
  Configuration.all_step lo (NPConfiguration.cfg npc)
                         (NPConfiguration.cfg npc').
Proof.
  inv NP_ALL_STEP.
  eapply NPConfig_step_to_Config_step in H.
  econs; eauto.
Qed.

Lemma NPConfig_all_steps_to_Config_all_steps:
  forall n npc npc' lo
    (NP_ALL_STEP: rtcn (NPConfiguration.all_step lo) n npc npc'),
    rtc (Configuration.all_step lo) (NPConfiguration.cfg npc)
        (NPConfiguration.cfg npc').
Proof.
  induction n; ii.
  - inv NP_ALL_STEP. eauto.
  - inv NP_ALL_STEP.
    eapply NPConfig_all_step_to_Config_all_step in A12.
    eapply IHn in A23.
    eapply Relation_Operators.rt1n_trans; eauto.
Qed.

Lemma NPconf_behs_implies_conf_behs:
  forall n lo c b behs
    (NPCONF_BEHS: NPconf_behaviors (NPConfiguration.mk c b) lo n behs),
    conf_behaviors c lo n behs.
Proof.
  induction n; ii.
  - inv NPCONF_BEHS.
    econs; eauto.
  - inv NPCONF_BEHS.
    + econs; eauto.
      inv IS_ABORT; ss. des; subst; ss.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in H2; ss.
      econs; eauto.
      do 3 eexists.
      split; eauto.
    + inv IS_DONE; ss. des; ss.
      econs; eauto.
      econs; eauto.
    + destruct c'.
      eapply IHn in BEHS; eauto.
      eapply NPConfig_step_to_Config_step in STEP; ss.
      econs; eauto.
    + destruct c'.
      eapply IHn in BEHS; eauto.
      des.
      eapply NPConfig_step_to_Config_step in STEP; ss.
      econs; eauto. ii; des; ss.
      eapply NPConfig_step_to_Config_step in STEP; ss.
      econs; eauto. ii; des; ss.
Qed.

Lemma sema_implies_np_p {lang:language}
      (code: Language.syntax lang) lo fs behs ctid
      (NP_BEHS: NPprog_behaviors fs code ctid lo behs):
  prog_behaviors fs code ctid lo behs.
Proof.
  unfold NPprog_behaviors, prog_behaviors in *. des.
  unfold NPConfiguration.init in NP_BEHS.
  destruct (Configuration.init fs code ctid) eqn:INIT; ss.
  inv NP_BEHS.
  eapply NPconf_behs_implies_conf_behs in NP_BEHS0; eauto.
Qed.

(** ** Semantics equivalence *)
(** [prog_behaviors] collects the behaviors of the program in PS2.1.
    [NPprog_behaviors] collects the behaviors of the program in the non-preemptive semantics. *)
Theorem sema_eq_ps_nps {lang:language}
        (code: Language.syntax lang) lo fs ctid:
  evttr_equivalence fs ctid lo code code
                    prog_behaviors NPprog_behaviors.
Proof.
  unfold evttr_equivalence.
  split; ii.
  eapply PS_and_APS.sema_eq_ps_aps in H.
  eapply APS_and_NP.sema_implies_aps_np; eauto.
  eapply sema_implies_np_p; eauto.
Qed.

Lemma conf_behav_abort:
  forall n c lo behs
    (CONF_BEHAV: conf_behaviors c lo n (behs ++ (VisibleEvent.abort :: nil))),
    Configuration.abort_config lo c.
Proof.
  induction n; ii.
  inv CONF_BEHAV; ss. destruct behs; ss.
  inv CONF_BEHAV; try solve [destruct behs; ss; tryfalse].
  - destruct behs; ss.
    econs; eauto.
    inv H3; ss. destruct behs; ss.
  - destruct behs; ss.
    inv H3; ss. destruct behs; ss.
  - destruct behs; ss. inv H3; ss.
    eapply IHn in BEHS. inv BEHS.
    econs.
    eapply Relation_Operators.rt1n_trans. econs; eauto. eauto. eauto.
  - eapply IHn in BEHS.
    inv BEHS.
    econs.
    eapply Relation_Operators.rt1n_trans.
    econs; eauto.
    eauto. eauto.
Qed.

Lemma abort_conf_behav':
  forall n c c' lo
    (STEPS: rtcn (Configuration.all_step lo) n c c')
    (ABORT: Configuration.is_abort c' lo),
  exists behs n0,
    conf_behaviors c lo n0 (behs ++ (VisibleEvent.abort :: nil)).
Proof.
  induction n; ii.
  - inv STEPS.
    exists (@nil VisibleEvent.t) 1.
    ss. econs; eauto.
  - inv STEPS.
    inv A12.
    eapply IHn in A23; eauto. des.
    destruct e; ss.
    exists behs (S n0). econs; eauto.
    ii; des; ss.
    exists behs (S n0). econs; eauto.
    ii; des; ss. 
    exists ((VisibleEvent.out e) :: behs) (S n0).
    econs; eauto.
Qed.

Lemma abort_conf_behav
      lo c
      (ABORT: Configuration.abort_config lo c):
  exists behs n, conf_behaviors c lo n (behs ++ (VisibleEvent.abort :: nil)).
Proof.
  inv ABORT.
  eapply rtc_rtcn in STEPS. des.
  exploit abort_conf_behav'; eauto.
Qed.

Lemma safe_implies_not_abort_tr
      lang lo fs code ctid
      (SAFE: @Configuration.safe lang lo fs code ctid):
  ~ (exists behs, prog_behaviors fs code ctid lo (behs ++ (VisibleEvent.abort :: nil))).
Proof.
  ii; des.
  inv SAFE. des.
  unfold prog_behaviors in H. des.
  lets ABORT: H. eapply SAFR_EXEC in ABORT.
  contradiction ABORT.
  eapply conf_behav_abort; eauto.
Qed.

Lemma not_abort_tr_implies_safe
      lang lo fs code ctid
      (NOT_ABORT_TR: ~ (exists behs, @prog_behaviors lang fs code ctid lo (behs ++ (VisibleEvent.abort :: nil))))
  (*(INIT_SAFE: exists c, Configuration.init fs code ctid = Some c)*)
  :
  @Configuration.safe lang lo fs code ctid.
Proof.
  des.
  econs; eauto. ii.
  contradiction NOT_ABORT_TR.
  exploit abort_conf_behav; eauto.
  ii; des.
  exists behs. econs; eauto.
Qed.

Lemma conf_behav_abort_NP:
  forall n npc lo behs
    (CONF_BEHAV: NPconf_behaviors npc lo n (behs ++ (VisibleEvent.abort :: nil))),
    NPConfiguration.abort_config lo npc.
Proof.
  induction n; ii.
  inv CONF_BEHAV; ss. destruct behs; ss.
  inv CONF_BEHAV; try solve [destruct behs; ss; tryfalse].
  - destruct behs; ss.
    econs; eauto.
    inv H3; ss. destruct behs; ss.
  - destruct behs; ss.
    inv H3; ss. destruct behs; ss.
  - destruct behs; ss. inv H3; ss.
    eapply IHn in BEHS. inv BEHS.
    econs.
    eapply Relation_Operators.rt1n_trans. econs; eauto. eauto. eauto.
  - des.
    eapply IHn in BEHS.
    inv BEHS.
    econs.
    eapply Relation_Operators.rt1n_trans.
    econs; eauto.
    eauto. eauto.
    eapply IHn in BEHS.
    inv BEHS.
    econs.
    eapply Relation_Operators.rt1n_trans.
    econs; eauto.
    eauto. eauto.
Qed.

Lemma abort_conf_behav_NP':
  forall n npc npc' lo
    (STEPS: rtcn (NPConfiguration.all_step lo) n npc npc')
    (ABORT: NPConfiguration.is_abort npc' lo),
  exists behs n0,
    NPconf_behaviors npc lo n0 (behs ++ (VisibleEvent.abort :: nil)).
Proof.
  induction n; ii.
  - inv STEPS.
    exists (@nil VisibleEvent.t) 1.
    ss. econs; eauto.
  - inv STEPS.
    inv A12.
    eapply IHn in A23; eauto. des.
    destruct e; ss.
    exists behs (S n0). econs; eauto.
    ii; des; ss.
    exists behs (S n0). econs; eauto.
    ii; des; ss. 
    exists ((VisibleEvent.out e) :: behs) (S n0).
    econs; eauto.
Qed.

Lemma abort_conf_behav_NP
      lo npc
      (ABORT: NPConfiguration.abort_config lo npc):
  exists behs n, NPconf_behaviors npc lo n (behs ++ (VisibleEvent.abort :: nil)).
Proof.
  inv ABORT.
  eapply rtc_rtcn in STEPS. des.
  exploit abort_conf_behav_NP'; eauto.
Qed.

Lemma safe_implies_not_abort_tr_NP
      lang lo fs code ctid
      (SAFE: @NPConfiguration.safe lang lo fs code ctid):
  ~ (exists behs, NPprog_behaviors fs code ctid lo (behs ++ (VisibleEvent.abort :: nil))).
Proof.
  ii; des.
  inv SAFE. des.
  unfold NPprog_behaviors in H. des.
  lets ABORT: H. eapply SAFE_EXEC in ABORT.
  contradiction ABORT.
  eapply conf_behav_abort_NP; eauto.
Qed.

Lemma not_abort_tr_implies_safe_NP
      lang lo fs code ctid
      (NOT_ABORT_TR: ~ (exists behs, @NPprog_behaviors lang fs code ctid lo (behs ++ (VisibleEvent.abort :: nil)))):
  @NPConfiguration.safe lang lo fs code ctid.
Proof.
  econs; eauto. ii.
  contradiction NOT_ABORT_TR.
  exploit abort_conf_behav_NP; eauto.
  ii; des.
  exists behs. econs; eauto.
Qed.

Lemma config_safe_eq
      lang lo fs code ctid:
  @NPConfiguration.safe lang lo fs code ctid <->
  @Configuration.safe lang lo fs code ctid.
Proof.
  split; ii.
  {
    lets CONFIG_SAFE: H.
    eapply safe_implies_not_abort_tr_NP in CONFIG_SAFE.
    eapply not_abort_tr_implies_safe.
    ii. contradiction CONFIG_SAFE. des.
    eapply sema_eq_ps_nps in H0. eauto.
  }
  {
    lets CONFIG_SAFE: H.
    eapply safe_implies_not_abort_tr in CONFIG_SAFE.
    eapply not_abort_tr_implies_safe_NP.
    ii. contradiction CONFIG_SAFE. des.
    eapply sema_eq_ps_nps in H0.
    eauto.
  }
Qed.      


