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
Require Import SemaEq.
Require Import ww_RF.

(** * Write-write race freedom equivalence proof *)

(** This file contains the proof of the equivalence between
    the write-write race freedoms
    in the promising semantics and the non-preemptive semantics. *)

(** Theorem [ww_RF_eq] in this file is the theorem (Lemma 6.1 in our paper) to
    show the equivalence between the write-write race freeodoms
    in the promising semantics and the non-preemptive semantics. *)

(** Theorem [ww_RF_eq] corresponds to the step 1 in Figure 3 (Our proof path) in our paper. *)
  
Lemma ww_race_np_to_p {lang: language}
      (code: Language.syntax lang) lo fs ctid
      (NP_RACE: ww_race_np lo fs code ctid):
  ww_race_p lo fs code ctid.
Proof.
  inv NP_RACE.
  eapply rtc_rtcn in STEPS. des.
  eapply NPConfig_all_steps_to_Config_all_steps in STEPS; eauto.
  unfold NPConfiguration.init in *.
  destruct (Configuration.init fs code ctid) eqn:INIT; ss.
  inv NPLOAD; ss.
  econs; eauto.
Qed.

Lemma Config_ww_race_stable
      c c' lo tid
      (WW_RC: ww_race lo (Configuration.sw_tid c' tid))
      (SC_EQ: Configuration.sc c = Configuration.sc c')
      (MEM_EQ: Configuration.memory c = Configuration.memory c')
      (TH_EQ: IdentMap.find tid (Configuration.threads c) =
                IdentMap.find tid (Configuration.threads c')):
  ww_race lo (Configuration.sw_tid c tid).
Proof.
  inv WW_RC. des.
  destruct c, c'; ss.
  unfold Configuration.sw_tid in *; ss. subst.
  econs; eauto; ss.
  rewrite TH_EQ. eauto.
Qed.

Lemma Config_ww_race_forwarding_na_fulfill_steps
      lo c c' tid'
      (NA_FULFILL_STEP: Config_na_fulfill_step lo c c')
      (ABORT: ww_race lo (Configuration.sw_tid c' tid')):
  (tid' = Configuration.tid c')
  \/ (ww_race lo (Configuration.sw_tid c tid') /\ tid' <> Configuration.tid c').
Proof.
  exploit Config_na_fulfill_step_sc_mem_unchange; eauto.
  ii; des.
  destruct c, c'; ss.
  unfold Configuration.sw_tid in *; ss; subst.
  inv ABORT; ss. des. 
  destruct (Loc.eq_dec tid tid'); subst; ss.
  {
    left. inv NA_FULFILL_STEP; ss.
    inv C2; ss.
  }
  {
    inv NA_FULFILL_STEP; ss. inv C2; ss.
    right. split.
    econs; eauto.
    rewrite IdentMap.gso in CTID; eauto.
    eauto.
  }
Qed.

Lemma Config_aux_all_steps_to_sw_procs:
  forall n c c' lo 
    (CONFIG_STEPS: rtcn (Configuration.aux_all_step lo) n c c'),
  exists n' behs, 
    sw_procs lo c c' behs n'
    /\ prefix_behs behs.
Proof.
  induction n; ii.
  - inv CONFIG_STEPS.
    exists 0%nat (@nil VisibleEvent.t).
    split; eauto.
    econs; eauto. econs; eauto.
  - inv CONFIG_STEPS. 
    inv A12.
    eapply IHn in A23. des.
    destruct e; ss.
    + inv A23; try solve [inv A0].
      {
        exists 0%nat (@nil VisibleEvent.t).
        split. econs; eauto.
        eapply Relation_Operators.rt1n_trans.
        left. eauto.
        eapply AUX_SILENT_STEPS.
        econs; eauto.
      }
      {
        exists (S n0) ((VisibleEvent.out e) :: behs0).
        split; eauto.
        econs.
        eapply Relation_Operators.rt1n_trans.
        left. eauto. eapply AUX_SILENT_STEPS.
        eapply OUT_STEP. eauto.
      }
      {
        exists (S n0) behs. split; eauto.
        eapply sw_procs_at.
        2: eauto. 2: eapply SW_N.
        eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
        econs; eauto.
      }
    + exists (S n') behs. split; eauto.
      eapply sw_procs_at; eauto.
    + exists (S n') behs. split; eauto.
      eapply sw_procs_at; eauto.
    + exists (S n') ((VisibleEvent.out e)::behs).
      split; eauto.
      eapply sw_procs_out; eauto.
      econs; eauto.
    + inv A23; try solve [inv A0].
      {
        exists 0%nat (@nil VisibleEvent.t).
        split. econs; eauto.
        eapply Relation_Operators.rt1n_trans.
        right. eauto.
        eapply AUX_SILENT_STEPS.
        econs; eauto.
      }
      {
        exists (S n0) ((VisibleEvent.out e) :: behs0).
        split; eauto.
        econs.
        eapply Relation_Operators.rt1n_trans.
        right. eauto. eapply AUX_SILENT_STEPS.
        eapply OUT_STEP. eauto.
      }
      {
        exists (S n0) behs. split; eauto.
        eapply sw_procs_at.
        2: eauto. 2: eapply SW_N.
        eapply Relation_Operators.rt1n_trans. 2: eapply AUX_SILENT_STEPS.
        right; eauto.
      }
    + exists (S n') behs. split; eauto.
      eapply sw_procs_at; eauto.
Qed.

Lemma Config_all_steps_to_sw_procs:
  forall n c c' lo 
    (CONFIG_STEPS: rtcn (Configuration.all_step lo) n c c'),
  exists n' behs, 
    sw_procs lo c c' behs n'
    /\ prefix_behs behs.
Proof.
  ii.
  eapply PS_and_APS.Config_all_steps_aux_all_steps in CONFIG_STEPS.
  eapply rtc_rtcn in CONFIG_STEPS. des.
  eapply Config_aux_all_steps_to_sw_procs in CONFIG_STEPS.
  des.
  eauto.
Qed.

Lemma sw_point_forwarding_race':
  forall n lo c c'
    (NA_STEPS: NAStep lo c c' n)
    (WW_RC: ww_race lo c')
    (WF_CONFIG: Configuration.wf c),
  exists c0 tid0 n0 c1,
    PRCStep lo (Configuration.sw_tid c tid0) c0 n0
    /\ (c0 = c1 \/ Configuration.aux_step AuxEvent.na lo c0 c1)
    /\ ww_race lo c1.
Proof.
  induction n; ii.
  - inv NA_STEPS.
    des; subst.
    + exists (Configuration.sw_tid c1 tid) tid 0%nat.
      exists (Configuration.sw_tid c1 tid).
      split; eauto.
      econs; eauto.
      instantiate (1 := tid).
      unfold Configuration.sw_tid.
      destruct c1; ss.
    + destruct (Loc.eq_dec tid (Configuration.tid c1)); subst.
      {
        (* switch to the same thread *)
        rewrite <- Configuration.sw_to_self in WW_RC.
        exists c (Configuration.tid c) 0%nat c1.
        rewrite <- Configuration.sw_to_self.
        split; eauto.
        econs; eauto.
        instantiate (1 := Configuration.tid c).
        rewrite Configuration.sw_to_self; eauto.
      }
      {
        (* switch to the different thread *)
        exploit Config_na_step_to_na_fulfill_step; eauto.
        ii; des.
        {
          exploit Config_na_fulfill_step_sc_mem_unchange; eauto.
          ii; des.
          exploit Config_ww_race_stable;
            [eapply WW_RC | eapply SC_UNCHANG | eapply MEM_UNCHANG | eauto..].
          {
            clear - n x1.
            inv x1; ss.
            rewrite IdentMap.gso; eauto.
          }
          introv WW_RC'.

          assert (NA_TID_UNCHANGE: 
                   Configuration.tid c0 = Configuration.tid c1).
          {
            inv x1. ss.
          }

          exists (Configuration.sw_tid c0 tid) (Configuration.tid c) 0%nat.
          exists (Configuration.sw_tid c0 tid).
          split; eauto.
          rewrite <- Configuration.sw_to_self; eauto.
          econs; eauto.
        }
        {
          subst. clear STEP.
          exploit Config_na_fulfill_step_sc_mem_unchange; eauto.
          ii; des.
          exploit Config_ww_race_stable; eauto.

          inv x1; ss.
          rewrite IdentMap.gso; eauto.

          introv WW_RC'.
          exists (Configuration.sw_tid c0 tid) tid 0%nat.
          exists (Configuration.sw_tid c0 tid).
          split; eauto.
          econs; eauto.
          instantiate (1 := tid).
          destruct c0; ss.
        }
      }
  - inv NA_STEPS.
    eapply IHn in NA; eauto. des; subst.
    
    rewrite Configuration.sw_tid_twice in NA. 
    exploit APS_and_NP.reorder_na_step_prc_steps; eauto.
    ii; des; subst.
    exploit Config_ww_race_forwarding_na_fulfill_steps; eauto.
    instantiate (1 := Configuration.tid c2).
    rewrite Configuration.sw_tid_twice; eauto.
    rewrite <- Configuration.sw_to_self; eauto.
    rewrite Configuration.sw_tid_twice; eauto.
    ii; des; subst.
    {
      simpl in x2.
      rewrite <- x2 in x1.
      rewrite <- Configuration.sw_to_self in x1; eauto.
      exists (Configuration.sw_tid c'0 (Configuration.tid c2)).
      exists tid n1 c2.
      split; eauto.
      eapply PRCStep_sw; eauto.
      split; eauto.
      right.
      eapply Config_na_fulfill_step_to_Config_aux_na_step; eauto.
    }
    {
      exists (Configuration.sw_tid c'0 (Configuration.tid c2)).
      exists tid n1 (Configuration.sw_tid c'0 (Configuration.tid c2)).
      split; eauto.
      eapply PRCStep_sw; eauto.
    }

    rewrite Configuration.sw_tid_twice in NA.
    exploit APS_and_NP.reorder_na_step_prc_steps;
      [eapply STEP | eapply NA | eauto..].
    ii; des; subst.
    destruct (Loc.eq_dec (Configuration.tid c) (Configuration.tid c0)).
    {
      rewrite e in x1.
      rewrite <- Configuration.sw_to_self in x1; eauto.
      eapply Config_na_fulfill_step_to_Config_aux_na_step in x1;
        eauto.
      exploit Config_aux_na_merge; [eapply x1 | eapply NA0 | eauto..].
      ii.
      exists (Configuration.sw_tid c'0 (Configuration.tid c0)) tid.
      exists n1 c2.
      split; eauto.
      eapply PRCStep_sw; eauto.
    }
    {
      exploit Config_na_fulfill_na_reordering_in_diff_threads;
        [eapply x1 | eauto..].
      rewrite Configuration.sw_tid_twice.
      rewrite <- Configuration.sw_to_self; eauto.
      eapply wf_config_prc_steps_prsv in x0; eauto.
      clear - x0. destruct c'0; ss.
      unfold Configuration.sw_tid; ss.
      eapply wf_config_sw_prsv; eauto.
      destruct c; ss. clear - WF_CONFIG.
      unfold Configuration.sw_tid; ss.
      eapply wf_config_sw_prsv; eauto.
      
      rewrite Configuration.sw_tid_twice.
      ii; des; ss; subst.
      assert (TID_EQ1: Configuration.tid c0 = Configuration.tid c2).
      {
        clear - NA0. destruct c0, c2; ss.
        inv NA0; ss. inv C2; ss.
      }
      clear - WF_CONFIG x0 x2 x3 NA1 n2 TID_EQ1.
      exploit Config_ww_race_forwarding_na_fulfill_steps; eauto.
      instantiate (1 := Configuration.tid c2).
      rewrite Configuration.sw_tid_twice.
      rewrite <- Configuration.sw_to_self; eauto.
      rewrite Configuration.sw_tid_twice; eauto. ss.
      ii; des; subst; ss.

      rewrite <- x1 in n2. rewrite <- TID_EQ1 in n2. ss.

      exists (Configuration.sw_tid c'0 (Configuration.tid c0)).
      exists tid n1 (Configuration.sw_tid c'1 (Configuration.tid c2)).
      split; eauto.
      eapply PRCStep_sw; eauto.
      split; eauto.
      right.
      assert (TID_EQ2: Configuration.tid c'1 = Configuration.tid c0).
      {
        clear - x2. destruct c'0, c'1, c0; ss.
        unfold Configuration.sw_tid in *; ss.
        inv x2; ss. inv C2. eauto.
      }
      rewrite <- TID_EQ1. rewrite <- TID_EQ2.
      rewrite <- Configuration.sw_to_self; eauto.
      rewrite TID_EQ2. eauto.
    }    

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

Lemma sw_point_forwarding_race
      lo c c'
      (AUX_NA_OR_SW_STEP: rtc (aux_na_or_sw_step lo) c c')
      (WW_RC: ww_race lo c')
      (WF_CONFIG: Configuration.wf c):
  exists c0 tid0 n0 c1,
    PRCStep lo (Configuration.sw_tid c tid0) c0 n0
    /\ (c0 = c1 \/ Configuration.aux_step AuxEvent.na lo c0 c1)
    /\ ww_race lo c1.
Proof.
  eapply rtc_rtcn in AUX_NA_OR_SW_STEP. des.
  eapply APS_and_NP.aux_na_or_sw_steps_to_na_aux_steps in AUX_NA_OR_SW_STEP.
  des.
  exploit sw_point_forwarding_race'; eauto.
  destruct c; ss.
  unfold Configuration.sw_tid; ss.
  eapply wf_config_sw_prsv; eauto.
Qed.
  
Lemma swprocs_to_nprace:
  forall n ths tid sc mem lo c' behs
    (SW_PROCS: sw_procs lo (Configuration.mk ths tid sc mem) c' behs n)
    (WF_CONFIG: Configuration.wf (Configuration.mk ths tid sc mem))
    (PREFIX_BEHS: prefix_behs behs)
    (WWRC : ww_race lo c'),
  exists c0 b0,
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk (Configuration.mk ths tid sc mem) true)
        (NPConfiguration.mk c0 b0)
    /\ ww_race lo c0.
Proof.
  induction n; ii.
  - des.
    inv SW_PROCS; ss; try solve [inv PREFIX_BEHS; ss].
    exploit sw_point_forwarding_race; eauto. 
    unfold Configuration.sw_tid; ss. ii; des; subst; ss.
    {
      assert (TH': exists lang st lc, 
                 IdentMap.find (Configuration.tid c1)
                               (Configuration.threads c1) =
                   Some (existT _ lang st, lc)).
      {
        inv x2; eauto.
      }
      des.
      eapply PRCStep_to_NPConf_steps in x0; eauto.
      instantiate (1 := tid) in x0.
      unfold Configuration.sw_tid in x0; ss.
      eapply NPConfig_tau_steps_is_all_steps in x0.
      do 2 eexists.
      split. eapply x0. eauto.
      eapply wf_config_sw_prsv; eauto.
    }
    { 
      assert (TH': exists lang st lc, 
                 IdentMap.find (Configuration.tid c0)
                               (Configuration.threads c0) =
                   Some (existT _ lang st, lc)).
      {
        inv x1; eauto.
      } 
      des.
      assert (WF_CONFIG0: Configuration.wf c0).
      {
        eapply wf_config_prc_steps_prsv in x0; eauto.
        eapply wf_config_sw_prsv; eauto.
      }
      eapply PRCStep_to_NPConf_steps in x0; eauto.
      instantiate (1 := tid) in x0.
      unfold Configuration.sw_tid in x0; ss.
      eapply NPConfig_tau_steps_is_all_steps in x0. 
      eapply Config_aux_na_step_to_NPConfig_step in x1; eauto.
      instantiate (1 := true) in x1.
      exists c1 false.
      split; eauto.
      eapply rtc_n1. eapply x0. econs. eauto.
      eapply wf_config_sw_prsv; eauto.
    }
  - inv SW_PROCS; ss.
    + (* output *)
      exploit APS_and_NP.sw_point_forwarding_out; eauto.
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
      inv PREFIX_BEHS; eauto.

      ii; des. 
      clear - x0 x1 x x3 x4 WF_CONFIG.
      renames x4 to WW_RC.
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
        clear - x4 x2 x WW_RC.
        eapply NPConfig_tau_steps_is_all_steps in x4.
        exists c3 b0.
        split; eauto.
        eapply rtc_compose. eapply x4.
        eapply Relation_Operators.rt1n_trans.
        econs. eauto. eauto.
      }
      {
        clear - x1 x2 x x4 WW_RC.
        eapply NPConfig_tau_steps_is_all_steps in x4.
        exists c3 b0.
        split; eauto.
        eapply rtc_compose. eapply x4.
        eapply Relation_Operators.rt1n_trans.
        econs. eauto.
        eapply Relation_Operators.rt1n_trans.
        econs. eauto.
        eauto.
      }
    + (* atm/prc/tterm *)
      destruct AT_PRC_TTERM_STEP as [AT_STEP | PRC_TTERM_STEP].
      {
        (* atm step *)
        exploit APS_and_NP.sw_point_forwarding_atm; eauto.
        unfold Configuration.sw_tid; ss.
        ii; des.
        exploit sw_procs_merge; eauto. introv SW_N'.
        destruct c3; ss. clear x2.
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

        clear - WF_CONFIG x0 x1 x x2.
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
        eapply NPConfig_tau_steps_is_all_steps in x4.
        eapply NPConfig_tau_step_is_all_step in x1.
        exists c3 b0. 
        split; eauto.
        eapply rtc_compose. eapply x4.
        eapply Relation_Operators.rt1n_trans; eauto.
      }
      destruct PRC_TTERM_STEP as [PRC_STEP | TTERM_STEP].
      {
        (* prc step *)
        exploit APS_and_NP.sw_point_forwarding_prc; eauto.
        unfold Configuration.sw_tid; ss.
        ii; des.
        exploit sw_procs_merge; eauto. introv SW_N'.
        destruct c0. clear x1.
        exploit IHn; [eapply SW_N' | eauto..].
        {
          clear - WF_CONFIG x0.
          eapply wf_config_sw_prsv with (ntid := tid0) in WF_CONFIG.
          eapply wf_config_prc_steps_prsv in x0; eauto.
        }
        ii; des.

        assert (TH: exists lang st lc,
                   IdentMap.find (Configuration.tid c0) (Configuration.threads c0)
                   = Some (existT _ lang st, lc)).
        {
          clear - x1.
          destruct c0; ss. inv x1; ss. eauto.
        }
        des.
        exploit PRCStep_cons_NPConfig_steps; [eapply x0 | eapply x | eauto..].
        eapply wf_config_sw_prsv; eauto.
        introv ALL_STEPS'.
        eapply rtc_rtcn in ALL_STEPS'. des.
        exists c0 b0. split; eauto.
        eapply NPConfig_steps_sw_tid; eauto.
      }
      {
        (* thread term *)
        exploit APS_and_NP.sw_point_forwarding_tterm; eauto.
        unfold Configuration.sw_tid; ss.
        ii; des; subst.
        {
          exploit sw_procs_merge; eauto. introv SW_N'. clear x3 SW_N.
          destruct c4.
          exploit IHn; [eapply SW_N' | eauto..].
          {
            clear - WF_CONFIG x0 x2.
            eapply wf_config_sw_prsv with (ntid := tid0) in WF_CONFIG.
            eapply wf_config_prc_steps_prsv in x0; eauto.
            destruct c3; ss. inv x2; ss. inv C2.
            eapply wf_config_rm_prsv; eauto.
          }
          ii; des.

          clear - WF_CONFIG x0 x1 x x2.
          assert (TH: exists lang st lc,
                     IdentMap.find (Configuration.tid c3) (Configuration.threads c3)
                     = Some (existT _ lang st, lc)).
          {
            clear - x2.
            destruct c3; ss. inv x2; ss. inv C2.
            eauto.
          }
          des.
          assert (WF_CONFIG': Configuration.wf c3).
          {
            eapply wf_config_prc_steps_prsv; eauto.
            eapply wf_config_sw_prsv; eauto.
          }
          exploit PRCStep_to_NPConf_steps; eauto.
          eapply wf_config_sw_prsv; eauto.
          instantiate (1 := tid). unfold Configuration.sw_tid; ss.
          ii. clear x0 TH.
          eapply Config_aux_tterm_to_NPConfig_step with (b := true) in x2; eauto.
          eapply NPConfig_tau_steps_is_all_steps in x4.
          exists c0 b0. 
          split; eauto.
          eapply rtc_compose. eapply x4.
          eapply Relation_Operators.rt1n_trans; eauto.
          econs. eauto.
        }
        {
          exploit sw_procs_merge; eauto. introv SW_N'. clear x3 SW_N.
          destruct c4.
          exploit IHn; [eapply SW_N' | eauto..].
          { 
            clear - WF_CONFIG x0 x1 x2.
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
          ii; des.
          
          clear - WF_CONFIG x0 x1 x x2 x3.
          assert (TH: exists lang st lc,
                     IdentMap.find (Configuration.tid c0) (Configuration.threads c0)
                     = Some (existT _ lang st, lc)).
          {
            clear - x1.
            destruct c3; ss. inv x1; ss. inv C2.
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
          eapply Config_aux_tterm_to_NPConfig_step with (b := false) in x2; eauto.
          eapply Config_aux_na_step_to_NPConfig_step with (b := true) in x1; eauto.
          eapply NPConfig_tau_steps_is_all_steps in x5.
          exists c4 b0. 
          split; eauto.
          eapply rtc_compose. eapply x5. 
          eapply Relation_Operators.rt1n_trans.
          econs. eauto.
          eapply Relation_Operators.rt1n_trans.
          econs. eauto.
          eauto.
        }
      }
Qed.
  
Lemma ww_race_p_to_np {lang: language}
      (code: Language.syntax lang) lo fs ctid
      (NP_RACE: ww_race_p lo fs code ctid):
  ww_race_np lo fs code ctid.
Proof.
  inv NP_RACE; eauto.
  eapply rtc_rtcn in STEPS. des.
  eapply Config_all_steps_to_sw_procs in STEPS; eauto.
  des.
  destruct c.
  eapply swprocs_to_nprace in STEPS; eauto. des.
  econs.
  unfold NPConfiguration.init. rewrite LOAD. eauto.
  eapply STEPS.
  ss.
  eapply wf_config_init; eauto.
Qed.

(** ** Write-write race freedom equivalence *)
Theorem ww_RF_eq {lang: language}
        (code: Language.syntax lang) lo fs ctid:
  @ww_rf lang lo fs code ctid
  <-> @ww_rf_np lang lo fs code ctid.
Proof.
  split; ii.
  - unfold ww_rf in H.
    contradiction H.
    eapply ww_race_np_to_p; eauto.
  - unfold ww_rf_np in H.
    contradiction H.
    eapply ww_race_p_to_np; eauto.
Qed.
