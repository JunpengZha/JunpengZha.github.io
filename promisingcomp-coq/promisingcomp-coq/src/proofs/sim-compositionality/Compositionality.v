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

Require Import LocalSim.
Require Import GlobSim.
Require Import ww_RF.

Require Import LibTactics.
Require Import ConfigInitLemmas.
Require Import CompThreadSteps.
Require Import CompAuxDef.
Require Import WFConfig.

Require Import Reordering.
Require Import ps_to_np_thread.
Require Import np_to_ps_thread.

Require Import simPromiseCertified.
Require Import Mem_at_eq_lemmas.
Require Import ConsistentProp.

(** * Compositionality Proof *)

(** This file contains the proof of compositionality of our thread-local simulation.

    The theorem [compositionality] in this file shows the compositionality of our thread-local simulation.
    It says that,
    if each target thread has thread-local simulation with
    its corresponding source thread
    and the source program is safe and write-write race free,
    then the whole target program simulates the whole source program.

    The theorem [compositionality] is a part of proof in Lemma 6.2 in our paper and
    also shown as a part of proof of the step 3 in Figure 3 (Our proof path) in our paper.
 *)

Lemma compositionality_aux:
      forall (index: Type) (index_order: index -> index -> Prop)
        (I: Invariant) (lo: Ordering.LocOrdMap) (b b': bool) inj 
        (ths_tgt ths_src: Threads.t) (ctid: IdentMap.key)
        (sc_tgt sc_src: TimeMap.t) (mem_tgt mem_src: Memory.t)
        (WELL_FOUNDED_ORDER: well_founded index_order)
        (WELL_FORMED_INV: wf_I I)
        (READY_THRDS: 
           forall tid (READY_TID: tid <> ctid) lang st_tgt lc_tgt
             (READY_TGT_THD: IdentMap.find tid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
           exists st_src lc_src,
             IdentMap.find tid ths_src = Some (existT _ lang st_src, lc_src) /\ 
             @rely_local_sim_state index index_order lang I lo inj
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src) /\
             Local.promise_consistent lc_tgt)
        (CUR_THRD: 
           forall lang st_tgt lc_tgt  
             (CUR_TGT_THRD: IdentMap.find ctid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
           exists st_src lc_src dset,
             IdentMap.find ctid ths_src = Some (existT _ lang st_src, lc_src) /\
             @local_sim_state index index_order lang I lo inj dset b
                              (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                              (Thread.mk lang st_src lc_src sc_src mem_src) /\
             (b = true -> dset = dset_init) /\
             Local.promise_consistent lc_tgt)
        (COMPLETE_THRDS_MAP: 
           forall tid
             (IN_SRC_THRDS: IdentMap.mem tid ths_src = true),
             IdentMap.mem tid ths_tgt = true)
        (SAFE: ~(exists npc,
                    rtc (NPConfiguration.all_step lo)
                        (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) b') npc /\
                    Configuration.is_abort (NPConfiguration.cfg npc) lo))
        (WWRF: ~(exists npc,
                    rtc (NPConfiguration.all_step lo)
                        (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) b') npc /\
                    aux_ww_race lo (NPConfiguration.cfg npc)))
        (WF_CONFIG_TGT: Configuration.wf (Configuration.mk ths_tgt ctid sc_tgt mem_tgt))
        (WF_CONFIG_SRC: Configuration.wf (Configuration.mk ths_src ctid sc_src mem_src))
        (WF_ATM_BIT: b = true -> b' = true)
        (*(CTID_IN: IdentMap.mem ctid ths_tgt = true)*)
        (INV_OUT_ATM: b = true ->
                      (Mem_at_eq lo mem_tgt mem_src /\ I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)))
        (MONOTONIC_INJ: monotonic_inj inj),
        glob_sim_state lo (NPConfiguration.mk (Configuration.mk ths_tgt ctid sc_tgt mem_tgt) b)
                       (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) b').
Proof.
  cofix Hcofix; ii.
  econs; ss; ii.
  + (* tau step *)
    inv TGT_TAU; ss.
    assert(T_STEPS: rtc (NPAuxThread.tau_step lang lo)
                        (NPAuxThread.mk lang (Thread.mk lang st1 lc1 sc_tgt mem_tgt) b)
                        (NPAuxThread.mk lang (Thread.mk lang st2 lc2 sc2 m2) b0)).
    {
      eapply rtc_n1; [eapply STEPS | eapply STEP].
    }
    exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply T_STEPS | eauto..]; eauto.
    introv T_CONFIG_WF'.
    eapply rtc_rtcn in T_STEPS. des.
    exploit CUR_THRD; [eapply TID1 | eauto..]. ii; des.
    assert(TGT_PROM_CONS: Local.promise_consistent lc2).
    {
      eapply consistent_nprm_promise_consistent in CONSISTENT; eauto; ss.
      eapply wf_config_to_local_wf; eauto. 
      instantiate (3 := ctid). rewrite IdentMap.gss; eauto.
      inv T_CONFIG_WF'; eauto. inv T_CONFIG_WF'; eauto.
    }
    exploit sim_tau_steps; [eapply T_STEPS | eauto..]; ss.
    eapply wf_config_to_local_wf; eauto.
    inv WF_CONFIG_TGT; eauto.
    inv WF_CONFIG_TGT; eauto.
    ii; des.
    {
      (* not abort *)
      destruct e_src'.
      exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply S_STEPS | eauto..]; eauto.
      introv S_CONFIG_WF'.
      eapply rtc_rtcn in S_STEPS. destruct S_STEPS as (n0 & S_STEPS).
      destruct n0.
      {
        (* source takes zero step *)
        clear S_CONFIG_WF'. inv S_STEPS.
        eexists. split. eauto. 
        eapply Hcofix with (b' := b_src') (inj := inj'); eauto.
        {
          ii.
          erewrite IdentMap.gso in READY_TGT_THD; eauto.
          lets READY_SRC_THD: READY_TGT_THD.
          eapply READY_THRDS in READY_SRC_THD; eauto. des.
          do 2 eexists.
          split; eauto.
          split; eauto.
          eapply local_sim_rely_condition with (n_tgt := n) (n_src := 0) (lang2 := lang0); eauto.
          eapply wf_config_to_local_wf; eauto.
          eapply wf_config_to_local_wf; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). erewrite IdentMap.gso; eauto.
          eapply wf_config_to_local_wf; eauto.
          inv T_CONFIG_WF'; eauto.
          inv T_CONFIG_WF'; eauto.
        }
        {
          ii.
          rewrite IdentMap.gss in CUR_TGT_THRD. inv CUR_TGT_THRD.
          eapply inj_pair2 in H1. subst.
          do 3 eexists. split. eauto. split; eauto.
        }
        {
          ii. rewrite IdentMap.mem_find. 
          destruct (Loc.eq_dec tid ctid); subst.
          rewrite IdentMap.gss; eauto.
          rewrite IdentMap.gso; eauto.
          eapply COMPLETE_THRDS_MAP in IN_SRC_THRDS.
          rewrite IdentMap.mem_find in IN_SRC_THRDS. eauto.
        }
        {
          inv LOCAL_SIM_PSV; ss.
          contradiction SAFE. eexists. split. eauto. ss.
          econs; ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
          do 3 eexists. split. eauto.
          split.
          eapply NP_STEPS. eauto.
          clear - STEP_INV RELY_STEP.
          ii. exploit RELY_STEP; eauto. ii; des.
          inv STEP_INV. eauto.
        }
      }
      {
        (* source takes multiply steps *)
        exploit Behavior.rtcn_tail; [eapply S_STEPS | eauto..].
        introv S_STEPS_CONS.
        destruct S_STEPS_CONS as (npc & S_STEPS_CONS & S_STEP).
        destruct npc.
        assert(CONSISTENT_S: 
                 NPAuxThread.consistent lang (Thread.mk lang state local sc memory) lo).
        {
          eapply promise_certified_prsv; [ | eapply CONSISTENT | eauto..]; eauto.
          {
            clear - SAFE S_STEPS x.
            eapply rtcn_rtc in S_STEPS.
            introv S_ABORT. destruct S_ABORT as (e_src' & S_STEPS_TO_ABORT & S_ABORT).
            contradiction SAFE.
            eexists. split; eauto; ss.
            eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
            econs; ss.
            do 3 eexists.
            split. eapply x.
            split. eapply rtc_compose; [eapply S_STEPS | eapply S_STEPS_TO_ABORT].
            eauto.
          }
          {
            eapply aux_ww_race_to_thrd_ww_race; eauto; ss.
            eapply rtcn_rtc in S_STEPS.
            eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
          }
          {
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := ctid). erewrite IdentMap.gss; eauto.
          }
          {
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := ctid). erewrite IdentMap.gss; eauto.
          }
          {
            inv T_CONFIG_WF'; eauto.
          }
          {
            inv S_CONFIG_WF'; eauto.
          }
          {
            inv T_CONFIG_WF'; eauto.
          }
          {
            inv S_CONFIG_WF'; eauto.
          }
        }
        eexists. split.
        {
          eapply rtcn_rtc in S_STEPS_CONS.
          eapply Operators_Properties.clos_rt1n_step.
          eapply NPConfiguration.step_tau; ss; [ | eapply S_STEPS_CONS | eapply S_STEP | eauto..]; eauto.
        }
        eapply Hcofix; eauto.
        {
          ii.
          rewrite IdentMap.gso in READY_TGT_THD; eauto.
          rewrite IdentMap.gso; eauto.
          lets READY_SRC_THD: READY_TGT_THD.
          eapply READY_THRDS in READY_SRC_THD; eauto. des.
          do 2 eexists.
          split; eauto.
          split; eauto.
          eapply local_sim_rely_condition with (n_tgt := n) (n_src := (S n0)) (lang2 := lang0); eauto.
          eapply wf_config_to_local_wf; eauto.
          eapply wf_config_to_local_wf; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). erewrite IdentMap.gso; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). erewrite IdentMap.gso; eauto.
          inv T_CONFIG_WF'; eauto.
          inv T_CONFIG_WF'; eauto.          
        }
        {
          ii. rewrite IdentMap.gss in CUR_TGT_THRD.
          inv CUR_TGT_THRD.
          eapply inj_pair2 in H1. subst.
          do 3 eexists. split.
          rewrite IdentMap.gss; eauto.
          split; eauto. 
        }
        {
          ii. rewrite IdentMap.mem_find. 
          destruct (Loc.eq_dec tid ctid); subst.
          rewrite IdentMap.gss; eauto.
          rewrite IdentMap.gso; eauto.
          rewrite IdentMap.mem_find in IN_SRC_THRDS.
          rewrite IdentMap.gso in IN_SRC_THRDS; eauto.
          rewrite <- IdentMap.mem_find in IN_SRC_THRDS.
          eapply COMPLETE_THRDS_MAP in IN_SRC_THRDS.
          rewrite IdentMap.mem_find in IN_SRC_THRDS. eauto.
        }
        {
          clear - SAFE S_STEPS x CONSISTENT_S.
          eapply rtcn_rtc in S_STEPS. ii. des.
          contradiction SAFE.
          eapply rtc_rtcn in S_STEPS. des.
          destruct n.
          inv S_STEPS. 
          erewrite IdentMap.gsident in H; eauto.
          eapply Behavior.rtcn_tail in S_STEPS. des. destruct a2. destruct state0.
          eapply rtcn_rtc in S_STEPS.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs; eauto.
          eapply NPConfiguration.step_tau; ss; eauto.
          eapply H. eauto.
        }
        {
          ii; des. contradiction WWRF.
          clear - S_STEPS H H0 CONSISTENT_S x.
          eapply Behavior.rtcn_tail in S_STEPS. des. destruct a2. destruct state0.
          eapply rtcn_rtc in S_STEPS.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs; eauto.
          eapply NPConfiguration.step_tau; ss; eauto.
          eapply H. eauto.
        }
        {
          inv LOCAL_SIM_PSV; ss.
          contradiction SAFE.
          eapply rtcn_rtc in S_STEPS.
          eexists. split. eauto. ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
          econs; ss. do 3 eexists.
          split. eauto. split.
          eapply rtc_compose. eapply S_STEPS. eapply NP_STEPS. eauto.
          clear - STEP_INV RELY_STEP.
          ii. exploit RELY_STEP; eauto. ii; des.
          inv STEP_INV. eauto.
        }
      }
    }
    {
      (* abort *)
      clear - x SAFE S_STEPS ABORT.
      contradiction SAFE.
      eexists. split; eauto. ss.
      econs; ss.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
      do 3 eexists.
      split; eauto. 
    }
  + (* output step *)
    inv TGT_OUT; ss.
    exploit CUR_THRD; [eapply TID1 | eauto..]. ii; des.
    exploit sim_output_steps; [eapply STEP | eauto..]. ii; des.
    {
      (* not abort *)
      assert(CONSISTENT_S': Local.promises (Thread.local e_src0) = Memory.bot /\ 
                            Local.promises (Thread.local e_src') = Memory.bot).
      {
        clear - S_OUT. inv S_OUT; ss. inv H. inv OUT; ss.
        inv LOCAL; ss. inv LOCAL0; ss. exploit PROMISES; eauto.
      }
      destruct CONSISTENT_S' as (CONSISTENT_S' & CONSISTENT_S'').
      exploit wf_config_NPThread_out_step_prsv; [ | | eapply STEP | eauto..]; eauto.
      introv WF_CONFIG_TGT'. 
      destruct e_src0, e_src'.
      exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply S_STEPS | eauto..]; eauto.
      introv WF_CONFIG_SRC'.
      exploit wf_config_NPThread_out_step_prsv; [ | | eapply S_OUT | eauto..]; eauto.
      instantiate (1 := ctid). rewrite IdentMap.gss; eauto.
      introv WF_CONFIG_SRC''.
      erewrite IdentMap.add_add_eq in WF_CONFIG_SRC''; eauto.
      assert (T_PROM_CONS: Local.promise_consistent lc2).
      {
        inv STEP; ss. inv H; ss. inv OUT; ss.
        inv LOCAL; ss. inv LOCAL0; ss.
        exploit PROMISES; eauto. introv T_BOT.
        unfold Local.promise_consistent; ss.
        rewrite T_BOT; ss. ii. rewrite Memory.bot_get in PROMISE; ss.
      }
      eapply rtc_rtcn in S_STEPS. des. destruct n.
      {
        inv S_STEPS; ss. 
        do 2 eexists. split. eauto.
        split.
        econs; ss. eapply x. eapply S_OUT.
        ss. econs. split. eauto. ss.
        eapply Hcofix with (inj := inj'); eauto. 
        {
          ii.
          rewrite IdentMap.gso in READY_TGT_THD; eauto.
          rewrite IdentMap.gso; eauto. ss.
          exploit READY_THRDS; [eapply READY_TID | eapply READY_TGT_THD | eauto..]. ii; des. 
          do 2 eexists. split. eauto.
          split; eauto.
          eapply local_sim_out_rely_condition in x4; eauto.
          eapply wf_config_to_local_wf; eauto.
          eapply wf_config_to_local_wf; eauto. instantiate (3 := ctid). erewrite IdentMap.gss; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_TGT; eauto.
          ss. inv WF_CONFIG_SRC'.
          ss. inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC'; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). erewrite IdentMap.gso; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). erewrite IdentMap.gso; eauto.
          inv WF_CONFIG_TGT'; eauto.
          inv WF_CONFIG_TGT'; eauto.          
        }
        {
          ii. rewrite IdentMap.gss in CUR_TGT_THRD; eauto.
          inv CUR_TGT_THRD. eapply inj_pair2 in H1. subst.
          do 3 eexists. split. rewrite IdentMap.gss; eauto.
          split; eauto. 
        }
        {
          ii. rewrite IdentMap.mem_find. 
          destruct (Loc.eq_dec tid ctid); subst.
          rewrite IdentMap.gss; eauto.
          rewrite IdentMap.gso; eauto.
          rewrite IdentMap.mem_find in IN_SRC_THRDS.
          rewrite IdentMap.gso in IN_SRC_THRDS; eauto.
          rewrite <- IdentMap.mem_find in IN_SRC_THRDS.
          eapply COMPLETE_THRDS_MAP in IN_SRC_THRDS.
          rewrite IdentMap.mem_find in IN_SRC_THRDS. eauto.
        }
        {
          introv ABORT. destruct ABORT as (npc & TO_ABORT & ABORT).
          contradiction SAFE. exists npc.
          split. eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_out; ss; eauto.
          ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; ss.
          eexists. split; eauto.
          eauto. eauto.
        }
        {
          introv WW_RACE. destruct WW_RACE as (npc & TO_WW_RACE & WW_RACE).
          contradiction WWRF. exists npc.
          split. eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_out; ss; eauto.
          ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; ss.
          eexists. split; eauto.
          eauto. eauto.
        }
        { 
          inv LOCAL_SIM_PSV; ss.
          contradiction SAFE.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_out; eauto.
          ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
          eexists. split. eauto. ss.
          ss. eauto. ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
          econs; ss. do 3 eexists.
          erewrite IdentMap.gss; eauto.
          clear - STEP_INV RELY_STEP.
          ii. exploit RELY_STEP; eauto. ii; des.
          inv STEP_INV. eauto.
        }
        {
          inv LOCAL_SIM_PSV; ss.
          contradiction SAFE.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_out; eauto.
          ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
          eexists. split. eauto. ss.
          ss. eauto. ss. 
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
          econs; ss. do 3 eexists.
          erewrite IdentMap.gss; eauto.
          clear - WELL_FORMED_INV RELY_STEP.
          exploit RELY_STEP; eauto. intros. des. clear x0 RELY_STEP.
          unfold wf_I in WELL_FORMED_INV. eapply WELL_FORMED_INV in x; eauto; ss.
          inv x; eauto.
        }
      }
      {
        ss.
        exploit Behavior.rtcn_tail; [eapply S_STEPS | eauto..].
        introv S_STEPS_CONS.
        destruct S_STEPS_CONS as (npc & S_STEPS_CONS & S_STEP).
        eapply rtcn_rtc in S_STEPS_CONS.
        do 2 eexists. split.
        eapply Relation_Operators.rt1n_trans. 2: eauto.
        eapply NPConfiguration.step_tau; ss.
        2: eapply S_STEPS_CONS. 2: eapply S_STEP. eauto.
        unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; ss.
        eexists. split; eauto; ss.
        split.
        econs; ss; eauto. rewrite IdentMap.gss; eauto.
        ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; ss; eauto.
        eapply Hcofix with (inj := inj'); eauto.
        {
          ii. rewrite IdentMap.gso in READY_TGT_THD; eauto.
          rewrite IdentMap.add_add_eq; eauto.
          rewrite IdentMap.gso; eauto.
          exploit READY_THRDS; eauto. ii; des.
          do 2 eexists. split; eauto.
          split; eauto.
          eapply local_sim_out_rely_condition with (n_src := S n) in x4; eauto.
          eapply wf_config_to_local_wf; eauto.
          eapply wf_config_to_local_wf; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_SRC; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). rewrite IdentMap.gso; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (3 := tid). rewrite IdentMap.gso; eauto.
          inv WF_CONFIG_TGT'; eauto.
          inv WF_CONFIG_TGT'; eauto.
        }
        {
          ii. rewrite IdentMap.add_add_eq; eauto.
          try rewrite IdentMap.gss in *; eauto.
          inv CUR_TGT_THRD. eapply inj_pair2 in H1. subst.
          do 3 eexists. split; eauto.
        }
        {
          rewrite IdentMap.add_add_eq; eauto.
          ii. rewrite IdentMap.mem_find. 
          destruct (Loc.eq_dec tid ctid); subst.
          rewrite IdentMap.gss; eauto.
          rewrite IdentMap.gso; eauto.
          rewrite IdentMap.mem_find in IN_SRC_THRDS.
          rewrite IdentMap.gso in IN_SRC_THRDS; eauto.
          rewrite <- IdentMap.mem_find in IN_SRC_THRDS.
          eapply COMPLETE_THRDS_MAP in IN_SRC_THRDS.
          rewrite IdentMap.mem_find in IN_SRC_THRDS. eauto.
        }
        {
          introv ABORT. destruct ABORT as (npc' & TO_ABORT & ABORT).
          contradiction SAFE.
          exists npc'.
          split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_tau; eauto.
          unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; eauto.
          ss. eapply Relation_Operators.rt1n_trans. 2: eauto.
          econs. eapply NPConfiguration.step_out; ss; eauto; ss.
          rewrite IdentMap.gss; eauto.
          unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; eauto.
          eauto.
        }
        {
          introv WW_RACE. destruct WW_RACE as (npc' & TO_WW_RACE & WW_RACE).
          contradiction WWRF.
          exists npc'.
          split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_tau; eauto.
          unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; eauto.
          ss. eapply Relation_Operators.rt1n_trans. 2: eauto.
          econs. eapply NPConfiguration.step_out; ss; eauto; ss.
          rewrite IdentMap.gss; eauto.
          unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ii; eauto.
          eauto.
        }
        {
          rewrite IdentMap.add_add_eq; eauto.
        }
        {
          inv LOCAL_SIM_PSV; ss.
          contradiction SAFE.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_tau; eauto.
          unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss.
          ii. eexists. split. eauto. ss.
          ss. 
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_out; eauto.
          ss. rewrite IdentMap.gss; eauto.
          ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
          eexists. split. eauto. ss.
          ss. eauto. ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
          econs; ss. do 3 eexists.
          split. 
          erewrite IdentMap.gss; eauto.
          split; eauto.
          clear - STEP_INV RELY_STEP.
          ii. exploit RELY_STEP; eauto. ii; des.
          inv STEP_INV. eauto.
        }
        {
          inv LOCAL_SIM_PSV; ss.
          contradiction SAFE.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_tau; eauto.
          unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss.
          ii. eexists. split. eauto. ss.
          ss. 
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_out; eauto.
          ss. rewrite IdentMap.gss; eauto.
          ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
          eexists. split. eauto. ss.
          ss. eauto. ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
          econs; ss. do 3 eexists.
          split. 
          erewrite IdentMap.gss; eauto.
          split; eauto.
          clear - WELL_FORMED_INV RELY_STEP.
          exploit RELY_STEP; eauto. intros; des. clear RELY_STEP x0.
          unfold wf_I in WELL_FORMED_INV.
          eapply WELL_FORMED_INV in x; ss. inv x; eauto.
        }
      }
    }
    {
      (* abort *)
      clear - x SAFE S_STEPS ABORT.
      contradiction SAFE.
      eexists. split; eauto. ss.
      econs; ss.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
      do 3 eexists.
      split; eauto.
    }
  + (* switch *)
    destruct npc_tgt'. destruct cfg.
    destruct (Loc.eq_dec tid ctid).
    {
      (* switch to the same thread *)
      subst.
      inv TGT_SW; ss.
      {
        (* thread not term *)
        inv NPC2; ss.
        exploit CUR_THRD; eauto. ii; des.
        do 2 eexists.
        split. eauto.
        split.
        econs; ss; eauto.
        eapply Hcofix; eauto.
        {
          introv ABORT.
          destruct ABORT as (npc & TO_ABORT & ABORT).
          contradiction SAFE.
          eexists.
          split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_sw; ss; eauto.
          eauto. eauto.
        }
        {
          introv WW_RACE.
          destruct WW_RACE as (npc' & TO_WW_RACE & WW_RACE).
          contradiction WWRF.
          exists npc'.
          split.
          eapply Relation_Operators.rt1n_trans.
          econs. eapply NPConfiguration.step_sw; ss; eauto.
          eauto. eauto.
        }
      }
      {
        (* thread term: contradiction *)
        inv NPC2.
        rewrite IdentMap.grs in NEW_TID_OK. ss.
      }
    }
    {
      (* switch to another thread *)
      inv TGT_SW; ss; subst. 
      {
        (* thread not term *)
        inv NPC2; ss.
        exploit READY_THRDS; eauto. ii; des.
        assert(I_INV: I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src) /\
                      Mem_at_eq lo mem_tgt mem_src).
        {
          exploit INV_OUT_ATM; eauto. ii. des. split; eauto.
        }
        destruct I_INV as (I_INV & MEM_AT_EQ).
        exploit rely_local_sim_state_to_local_sim_state; eauto.
        eapply wf_config_to_local_wf; eauto.
        eapply wf_config_to_local_wf; eauto.
        inv WF_CONFIG_TGT; eauto.
        inv WF_CONFIG_TGT; eauto.
        introv NEW_TH_LOCAL_SIM.
        do 2 eexists.
        split. eauto.
        split.
        econs; eauto; ss.
        ss.
        eapply Hcofix; eauto. 
        { 
          ii.
          destruct (Loc.eq_dec tid ctid); subst.
          {
            exploit CUR_THRD; [eapply READY_TGT_THD | eauto..].
            ii; des. 
            do 2 eexists. split; eauto.
            exploit x4; eauto. ii; subst.
            split; eauto.
            eapply local_sim_state_to_rely_local_sim_state; eauto.
            instantiate (1 := ctid).
            introv ABORT. destruct ABORT as (npc' & TO_ABORT & ABORT).
            contradiction SAFE. clear SAFE.
            exploit WF_ATM_BIT; eauto. ii; subst.
            exists npc'.
            split. eauto.
            eapply NPConfig_abort_to_Config_abort; eauto.
          }
          {
            exploit READY_THRDS; eauto.
          }
        }
        {
          ii.
          exploit READY_THRDS; eauto. ii; des.
          exploit rely_local_sim_state_to_local_sim_state; eauto.
          eapply wf_config_to_local_wf; eauto.
          eapply wf_config_to_local_wf; eauto.
          inv WF_CONFIG_TGT; eauto.
          inv WF_CONFIG_TGT; eauto.
          ii; des.
          do 3 eexists.
          split. eauto.
          split. eauto.
          eauto.
        }
        {
          introv ABORT. destruct ABORT as (npc & TO_ABORT & ABORT).
          contradiction SAFE.
          exists npc.
          split.
          eapply Relation_Operators.rt1n_trans.
          econs.
          eapply NPConfiguration.step_sw; eauto.
          ss. eauto.
        }
        {
          introv WW_RACE. destruct WW_RACE as (npc & TO_WW_RACE & WW_RACE).
          contradiction WWRF.
          exists npc.
          split.
          eapply Relation_Operators.rt1n_trans.
          econs.
          eapply NPConfiguration.step_sw; eauto.
          ss. eauto.
        }
        {
          eapply wf_config_sw_prsv; eauto.
        }
        {
          eapply wf_config_sw_prsv; eauto.
        }
      }
      {
        (* thread term *) 
        inv NPC2; ss.
        exploit CUR_THRD; eauto. ii. des.
        inv x0; ss.
        {
          (* source will abort *)
          contradiction SAFE.
          eexists. split. eauto. ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS. ss.
          econs; ss.
          do 3 eexists.
          split. eauto.
          split. eapply NP_STEPS. eauto.
        }
        {
          (* source not abort *)
          clear THRD_STEP RELY_STEP THRD_ABORT.
          exploit THRD_DONE0; eauto. ii; des.
          rewrite IdentMap.gro in NEW_TID_OK; eauto.
          exploit READY_THRDS; eauto. ii; des.
          exploit na_steps_dset_to_NPThread_tau_steps; eauto.
          instantiate (1 := b'). introv Hprefix_tau_steps. des.
          eapply rtc_rtcn in Hprefix_tau_steps.
          destruct Hprefix_tau_steps as (n0 & Hprefix_tau_steps).
          destruct n0.
          {
            inv Hprefix_tau_steps; ss.
            do 2 eexists.
            split. eauto.
            split. 
            eapply NPConfiguration.step_thread_term; eauto; ss.
            instantiate (3 := tid2). rewrite IdentMap.gro; eauto.
            ss.
            eapply Hcofix with (inj := inj'); eauto.
            {
              ii.
              destruct (Loc.eq_dec tid ctid); subst.
              rewrite IdentMap.grs in READY_TGT_THD; ss.
              rewrite IdentMap.gro in READY_TGT_THD; eauto.
              rewrite IdentMap.gro; eauto.
              exploit READY_THRDS; eauto. ii; des.
              eapply local_sim_rely_condition with (n_tgt := 0) (n_src := 0) in x10; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_TGT; eauto.
            }
            {
              ii.
              try rewrite IdentMap.gro in *; eauto.
              exploit READY_THRDS; eauto. ii; des.              
              eapply local_sim_rely_condition with
                  (n_tgt := 0) (n_src := 0) (lc_tgt1 := lc1) (lc_src1 := lc_src) in x10; eauto.
              rewrite NEW_TID_OK in CUR_TGT_THRD.
              inv CUR_TGT_THRD. eapply inj_pair2 in H1. subst. 
              eapply rely_local_sim_state_to_local_sim_state in x10; eauto.
              do 3 eexists.
              split. eauto.
              split. eauto.
              eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv STEP_INV; ss.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_TGT; eauto.
            }
            {
              ii. rewrite IdentMap.mem_find in IN_SRC_THRDS.
              destruct (Loc.eq_dec tid ctid); subst.
              rewrite IdentMap.grs in IN_SRC_THRDS; ss.
              rewrite IdentMap.mem_find.
              try rewrite IdentMap.gro in *; eauto.
              try rewrite <- IdentMap.mem_find in *.
              eauto.
            }
            {
              introv ABORT. destruct ABORT as (npc & TO_ABORT & ABORT).
              contradiction SAFE.
              exists npc.
              split.
              eapply Relation_Operators.rt1n_trans.
              econs. eapply NPConfiguration.step_thread_term; eauto.
              ss. instantiate (3 := tid2). rewrite IdentMap.gro; eauto.
              ss. eauto.
            }
            {
              introv WW_RACE. destruct WW_RACE as (npc & TO_WW_RACE & WW_RACE).
              contradiction WWRF.
              exists npc.
              split.
              eapply Relation_Operators.rt1n_trans.
              econs. eapply NPConfiguration.step_thread_term; eauto.
              ss. instantiate (3 := tid2). rewrite IdentMap.gro; eauto.
              ss. eauto.
            }
            {
              eapply wf_config_rm_prsv; eauto.
            }
            {
              eapply wf_config_rm_prsv; eauto.
            }
            {
              ii. split; eauto.
              inv STEP_INV; eauto.
            }
            {
              clear - WELL_FORMED_INV x5.
              unfold wf_I in WELL_FORMED_INV.
              eapply WELL_FORMED_INV in x5; ss. inv x5; eauto.
            }
          }
          {
            exploit Behavior.rtcn_tail; [eapply Hprefix_tau_steps | eauto..].
            introv Hprefix_tau_steps'.
            destruct Hprefix_tau_steps' as (npc' & PREFIX_STEPS & PREFIX_STEP).
            destruct npc'. destruct state.
            eapply rtcn_rtc in PREFIX_STEPS.
            assert(CONSISTENT_T: Local.promises (Thread.local e_src) = Memory.bot).
            { 
              clear - x3. inv x3. eauto.
            }
            exploit rtcn_rtc; [eapply Hprefix_tau_steps | eauto..]. introv PROFIX_STEPS_TEMP.
            destruct e_src.
            exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply PROFIX_STEPS_TEMP | eauto..]; eauto.
            introv WF_CONFIG_SRC'.
            do 2 eexists.
            split. clear PROFIX_STEPS_TEMP.
            eapply Relation_Operators.rt1n_trans.
            eapply NPConfiguration.step_tau; eauto.
            unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
            eexists. split; eauto.
            ss. eauto.
            split.
            eapply NPConfiguration.step_thread_term; ss; eauto.
            rewrite IdentMap.gss; eauto.
            ss. instantiate (3 := tid2).
            rewrite IdentMap.gro; eauto.
            rewrite IdentMap.gso; eauto.
            eapply Hcofix with (inj := inj'); eauto.
            {
              ii.
              destruct (Loc.eq_dec tid ctid); subst.
              rewrite IdentMap.grs in READY_TGT_THD; ss.
              try rewrite IdentMap.gro in *; eauto.
              rewrite IdentMap.gso; eauto.
              exploit READY_THRDS; eauto. ii; des.
              clear PREFIX_STEPS PREFIX_STEP.
              eapply local_sim_rely_condition with (n_tgt := 0) (n_src := (S n0)) in x10; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              instantiate (3 := tid). rewrite IdentMap.gso; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_TGT; eauto.
            }
            {
              ss. clear PREFIX_STEPS PREFIX_STEP. ii.
              destruct (Loc.eq_dec tid2 ctid); subst.
              rewrite IdentMap.grs in CUR_TGT_THRD. ss.
              try rewrite IdentMap.gro in *; eauto.
              rewrite IdentMap.gso; eauto.
              exploit READY_THRDS; eauto. ii; des.
              eapply local_sim_rely_condition with (n_tgt := 0) (n_src := (S n0)) in x10; eauto.
              eapply rely_local_sim_state_to_local_sim_state in x10; eauto.
              do 3 eexists.
              split. eauto.
              split. eauto.
              eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              instantiate (3 := tid2). rewrite IdentMap.gso; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv STEP_INV; ss; eauto.
              clear - x0 ATOMIC_COVER.
              eapply na_steps_dset_to_Thread_na_steps in x0.
              eapply Mem_at_eq_na_steps_prsv with (m := mem_tgt) in x0; ss; eauto.
              eapply Mem_at_eq_reflexive; eauto.
              eapply Mem_at_eq_reflexive; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_SRC; eauto.
              eapply wf_config_to_local_wf; eauto.
              eapply wf_config_to_local_wf; eauto.
              instantiate (3 := tid2). rewrite IdentMap.gso; eauto.
              inv WF_CONFIG_TGT; eauto.
              inv WF_CONFIG_TGT; eauto.
            }
            {
              ii. try rewrite IdentMap.mem_find in *.
              destruct (Loc.eq_dec tid ctid); subst. 
              rewrite IdentMap.grs in IN_SRC_THRDS; eauto.
              try rewrite IdentMap.gro in *; eauto.
              rewrite IdentMap.gso in IN_SRC_THRDS; eauto.
              try rewrite <- IdentMap.mem_find in *.
              eauto.
            }
            {
              introv ABORT. destruct ABORT as (npc' & TO_ABORT & ABORT).
              contradiction SAFE. clear PROFIX_STEPS_TEMP.
              eexists npc'. split; eauto.
              eapply Relation_Operators.rt1n_trans.
              econs. eapply NPConfiguration.step_tau; eauto.
              unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
              eexists. split; eauto.
              ss. eapply Relation_Operators.rt1n_trans.
              econs. eapply NPConfiguration.step_thread_term; ss; eauto.
              rewrite IdentMap.gss; eauto.
              ss. instantiate (3 := tid2).
              rewrite IdentMap.gro; eauto.
              rewrite IdentMap.gso; eauto.
              eauto.
            }
            {
              introv WW_RACE. destruct WW_RACE as (npc' & TO_WW_RACE & WW_RACE).
              contradiction WWRF. clear PROFIX_STEPS_TEMP.
              exists npc'. split; eauto.
              eapply Relation_Operators.rt1n_trans.
              econs. eapply NPConfiguration.step_tau; eauto.
              unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
              eexists. split; eauto.
              ss. eapply Relation_Operators.rt1n_trans.
              econs. eapply NPConfiguration.step_thread_term; ss; eauto.
              rewrite IdentMap.gss; eauto.
              ss. instantiate (3 := tid2).
              rewrite IdentMap.gro; eauto.
              rewrite IdentMap.gso; eauto.
              eauto.
            }
            {
              eapply wf_config_rm_prsv; eauto.
            }
            {
              eapply wf_config_rm_prsv; eauto.
            }
            {
              ss. ii.
              split; eauto.
              inv STEP_INV.
              eapply na_steps_dset_to_Thread_na_steps in x0. 
              eapply Mem_at_eq_na_steps_prsv with (m := mem_tgt) in x0; eauto; ss.
              eapply Mem_at_eq_reflexive; eauto.
              eapply Mem_at_eq_reflexive; eauto.
            }
            { 
              clear - WELL_FORMED_INV x5; ss.
              unfold wf_I in WELL_FORMED_INV.
              eapply WELL_FORMED_INV in x5; ss. inv x5; eauto.
            }
          }
        }
      }
    }
  + (* program done *)
    inv TGT_DONE; ss. des.
    exploit CUR_THRD; eauto. ii. des.
    inv x1; ss.
    {
      (* source will abort *)
      contradiction SAFE.
      eexists. split. eauto. ss.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS. ss.
      econs; ss.
      do 3 eexists.
      split. eauto.
      split. eapply NP_STEPS. eauto.
    }
    {
      (* source not abort *)
      clear THRD_STEP RELY_STEP THRD_ABORT.
      exploit THRD_DONE; eauto. ii; des. clear THRD_DONE.
      exploit na_steps_dset_to_NPThread_tau_steps; eauto.
      instantiate (1 := b'). introv Hprefix_tau_steps. des. renames x to lang.
      eapply rtc_rtcn in Hprefix_tau_steps.
      destruct Hprefix_tau_steps as (n0 & Hprefix_tau_steps).
      assert(TO_DONE_S: IdentMap.is_empty (IdentMap.remove ctid ths_src) = true).
      {
        eapply IdentMap.is_empty_1.
        eapply IdentMap.is_empty_2 in H1.
        unfold IdentMap.Empty in *. ii.
        eapply IdentMap.find_1 in H2.
        destruct (Loc.eq_dec a ctid); subst.
        rewrite IdentMap.grs in H2; ss.
        rewrite IdentMap.gro in H2; eauto.
        assert(CONRT_SRC: IdentMap.mem a ths_src = true).
        {
          rewrite IdentMap.mem_find. rewrite H2; eauto.
        }
        exploit COMPLETE_THRDS_MAP; eauto. introv CONTR_TGT.
        rewrite IdentMap.mem_find in CONTR_TGT.
        destruct (IdentMap.find a ths_tgt) eqn: CONTR_TGT_TID; ss.
        specialize (H1 a p).
        contradiction H1.
        eapply IdentMap.find_2. rewrite IdentMap.gro; eauto.
      }
      assert(CONSISTENT_S: Local.promises (Thread.local e_src) = Memory.bot).
      {
        clear - x4. inv x4. eauto.
      }
      destruct n0.
      {
        inv Hprefix_tau_steps; ss.
        eexists. split. eauto.
        econs; eauto.
      }
      {
        exploit Behavior.rtcn_tail; eauto. ii; des.
        destruct e_src.
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        eapply rtcn_rtc in x7.
        eapply NPConfiguration.step_tau; eauto.
        unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss. ii.
        eexists. split. eauto. ss.
        ss. eauto.
        econs; eauto.
        ss.
        rewrite IdentMap.gss.
        do 2 eexists. split. eauto.
        split; eauto.
        eapply IdentMap.is_empty_2 in TO_DONE_S.
        eapply IdentMap.is_empty_1; eauto.
        unfold IdentMap.Empty in *. ii.
        specialize (TO_DONE_S a e). contradiction TO_DONE_S.
        eapply IdentMap.find_1 in H2.
        eapply IdentMap.find_2.
        destruct (Loc.eq_dec a ctid); subst.
        rewrite IdentMap.grs in H2; ss.
        rewrite IdentMap.gro in H2; eauto.
        rewrite IdentMap.gso in H2; eauto.
        rewrite IdentMap.gro; eauto. 
      }
    }
  + (* abort *) 
    inv TGT_ABORT; ss. des; subst; ss.
    exploit CUR_THRD; eauto. ii; des.
    eapply rtc_rtcn in H2; des.
    exploit sim_tau_steps; eauto; ss.
    eapply wf_config_to_local_wf; eauto.
    inv WF_CONFIG_TGT; eauto. inv WF_CONFIG_TGT; eauto.
    inv H3. des; eauto.
    ii; des.
    {
      inv LOCAL_SIM_PSV; ss.
      {
        (* source thread abort *)
        contradiction SAFE.
        eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
        eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
        eexists.
        split. eauto. ss.
        econs; ss.
        do 3 eexists.
        split. eapply x0.
        split. eapply rtc_compose. eapply S_STEPS. eapply NP_STEPS.
        eauto.
      }
      {
        (* target not promise consistent *)
        inv H3; ss.
      }
      {
        (* source thread not abort *)
        clear THRD_STEP RELY_STEP THRD_DONE.
        exploit THRD_ABORT; eauto. ii; des.
        eapply rtc_rtcn in x4. des.
        eapply rtc_na_p_to_np with (b := b_src') in x4; eauto. des.
        eapply np_na_steps_is_tau_steps in x4.
        eexists. split. eauto.
        econs; ss.
        do 6 eexists.
        split. eauto. ss.
        split. eapply x0.
        split. eauto.
        split.
        eapply rtc_compose. eapply S_STEPS. eapply x4.
        eauto.
      }
    }
    {
      contradiction SAFE.
      eexists. split. eauto. ss.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS. ss.
      econs; ss.
      do 3 eexists.
      split. eauto.
      split. eapply S_STEPS. eauto.
    }
    Unshelve.
    exact state.
    exact true.
    exact lang.
    exact st_src0.
    exact true.
    exact st_src0.
    exact true.
    exact lang.
    exact st_src.
    exact true.
    exact st_src.
    exact true.
    exact st_src.
    exact true.
    exact st_src.
    exact true.
Qed.
    
(** ** Compositionality *)
(** It depicts the following conclusion, if
    - [LOCAL_SIM]: local simulation holds;
    - [SAFE_NP_SRC]: source program is safe under the non-preemptive semantics;
    - [WW_RF_NP_SRC]: source progra is write-write race freedom;
    then the global simulation holds. *)
Theorem compositionality
        (lang: language) (index: Type) (index_order: index -> index -> Prop)
        (I: Invariant) (lo: Ordering.LocOrdMap)
        (code_t code_s: Language.syntax lang) (fs: list IdentMap.key) (ctid: IdentMap.key)
        (LOCAL_SIM: @local_sim index index_order lang I lo code_t code_s)
        (SAFE_NP_SRC: NPConfiguration.safe lo fs code_s ctid)
        (WW_RF_NP_SRC: ww_rf_np lo fs code_s ctid):
  glob_sim lang lo fs ctid code_t code_s.
Proof.
  intros.
  inv LOCAL_SIM.
  unfold glob_sim.
  introv TGT_INIT.

  (* destruct the target initial state *)
  unfolds NPConfiguration.init.
  destruct (Configuration.init fs code_t ctid) eqn:H_tgt_init; tryfalse.
  inv TGT_INIT. 
  renames t to c_tgt.

  (* construct the source initial state *)
  lets H_src_init : H_tgt_init.
  eapply cons_source_init_from_target_init_program in H_src_init; eauto.
  destruct H_src_init as (c_src & H_src_init & Htgt_2_src & Hsrc_2_tgt).
  rewrite H_src_init.
  eexists. split; eauto.

  (* construct global simulation *)
  destruct c_tgt, c_src; simpls.
  renames threads to ths_tgt, sc to sc_tgt, memory to mem_tgt.
  renames threads0 to ths_src, sc0 to sc_src, memory0 to mem_src.
  assert (Hctid: tid = ctid /\ tid0 = ctid).
  {
    clear - H_tgt_init H_src_init.
    unfolds Configuration.init.
    destruct (Threads.init fs code_t); tryfalse.
    inv H_tgt_init.
    destruct (Threads.init fs code_s); tryfalse.
    inv H_src_init; eauto.
  }
  destruct Hctid; subst.
  eapply config_init_ths_sc_mem in H_tgt_init; simpl in H_tgt_init.
  destruct H_tgt_init as (Hths_tgt_init & Hsc_tgt_init & Hmem_tgt_init); subst.
  eapply config_init_ths_sc_mem in H_src_init; simpl in H_src_init.
  destruct H_src_init as (Hths_src_init & Hsc_src_init & Hmem_src_init); subst.
  assert (NP_CONFIG_INIT: NPConfiguration.init fs code_s ctid =
                          Some (NPConfiguration.mk (Configuration.mk ths_src ctid TimeMap.bot Memory.init) true)).
  {
    clear - Hths_src_init.
    unfold NPConfiguration.init, Configuration.init; simpl.
    rewrite Hths_src_init; eauto.
  } 
  eapply compositionality_aux with (I := I) (inj := inj_init); eauto.
  {
    (* ready threads *)
    introv Hready_tid Hready_th.
    assert (lang0 = lang).
    {
      clear - Hths_tgt_init Hready_th.
      eapply thread_init_same_lang in Hths_tgt_init; eauto.
    }
    subst.
    eapply Htgt_2_src in Hready_th.
    destruct Hready_th as (st_src & lc_src & Hlc_tgt_init & Hlc_src_init & Hsrc_ready_th & Hlocal_sim_state); subst.
    do 2 eexists.
    split. eapply Hsrc_ready_th.
    split; eauto.
    eapply local_sim_state_to_rely_local_sim_state; eauto.
    instantiate (1 := ctid).
    clear - SAFE_NP_SRC NP_CONFIG_INIT.
    inv SAFE_NP_SRC. 
    eapply SAFE_EXEC in NP_CONFIG_INIT. ii. des.
    contradiction NP_CONFIG_INIT. econs; eauto.
    unfold Local.promise_consistent, Local.init; ii; ss.
    rewrite Memory.bot_get in PROMISE; eauto. ss.
    unfold Local.promise_consistent, Local.init; ii; ss.
    rewrite Memory.bot_get in PROMISE; eauto. ss.
  }
  {
    (* current thread *)
    introv Hcur_th.
    assert (lang0 = lang).
    {
      clear - Hths_tgt_init Hcur_th.
      eapply thread_init_same_lang in Hths_tgt_init; eauto.
    }
    subst.
    eapply Htgt_2_src in Hcur_th.
    destruct Hcur_th as(st_src & lc_src & Hlc_tgt_init & Hlc_src_init & Hsrc_cur_th & Hlocal_sim_state); subst.
    do 3 eexists.
    split; eauto. split; eauto.
    split; eauto.
    unfold Local.promise_consistent, Local.init; ii; ss.
    rewrite Memory.bot_get in PROMISE; eauto. ss.
  }
  {
    (* safe *) 
    eapply sound_np_abort; eauto. 
    clear - SAFE_NP_SRC NP_CONFIG_INIT.
    inv SAFE_NP_SRC.
    eapply SAFE_EXEC in NP_CONFIG_INIT; eauto.
    clear - NP_CONFIG_INIT.
    introv Hnp_abort.
    contradict NP_CONFIG_INIT.
    destruct Hnp_abort as (npc' & Hrtc_steps & Habort).
    econstructor; eauto.
  }
  {
    (* write-write race free *)
    eapply sound_np_aux_wwrf; eauto.
    eapply wf_config_init with (fs := fs) (code := code_s) (ctid := ctid); eauto.
    clear - NP_CONFIG_INIT.
    unfolds NPConfiguration.init; eauto.
    destruct (Configuration.init fs code_s ctid); tryfalse.
    inv NP_CONFIG_INIT; eauto.
    clear - WW_RF_NP_SRC NP_CONFIG_INIT.
    unfolds ww_rf_np.
    introv Haux_ww_race.
    contradict WW_RF_NP_SRC.
    destruct Haux_ww_race as (npc' & Hrtc & Haux_ww_race).
    econstructor.
    Focus 2. eapply Hrtc.
    eauto.
    eauto.
  }
  { 
    (* well-formed target configuraiton in initialization *)
    eapply wf_config_init with (fs := fs) (code := code_t) (ctid := ctid); eauto.
    unfold Configuration.init.
    rewrite Hths_tgt_init; eauto.
  }
  {
    (* well-formed source configuration in initialization *)
    eapply wf_config_init with (fs := fs) (code := code_s) (ctid := ctid); eauto.
    unfold Configuration.init.
    rewrite Hths_src_init; eauto.
  }
  {
    (* init Mem_at_eq I *)
    ii. split; eauto.
    eapply Mem_at_eq_init.
  }
  {
    (* monotonic inj *)
    unfold monotonic_inj. unfold inj_init; ss. ii.
    des_ifH INJ1; ss; subst. inv INJ1.
    des_ifH INJ2; ss; subst. inv INJ2.
    auto_solve_time_rel.
  }
Qed.
