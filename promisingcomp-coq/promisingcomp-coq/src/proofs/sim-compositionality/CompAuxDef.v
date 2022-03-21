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

Require Import ConsistentProp.
Require Import Reordering.
Require Import ps_to_np_thread.
Require Import np_to_ps_thread.
Require Import WFConfig.

(** auxiliary write-write race *) 
Inductive aux_ww_race: forall (lo: Ordering.LocOrdMap) (c: Configuration.t), Prop :=
| aux_ww_race_intro
    lang lo ths tid st lc sc mem st' lc' sc' mem' stw loc val val' e'' to from released
    (CTID: IdentMap.find tid ths = Some (existT _ lang st, lc))
    (STEPS: rtc (Thread.all_step lo) (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (WRITE: (Language.step lang) (ProgramEvent.write loc val Ordering.plain) st' stw)
    (RC_MSG: Memory.get loc to mem' = Some (from, Message.concrete val' released)
             /\ Memory.get loc to (Local.promises lc') = None)
    (WWRC: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (FULFILL: rtc (Thread.tau_step lo) (Thread.mk lang st' lc' sc' mem') e'' /\
              Local.promises (Thread.local e'') = Memory.bot)
  :
    aux_ww_race lo (Configuration.mk ths tid sc mem).

(** NP Safe to No thread execution abort *)
Section NP_Safe_to_No_ThreadAbort.
  Lemma P_abort_to_NP_abort_from_outAtmBlk:
    forall c lo 
      (ABORT: Configuration.is_abort c lo),
      NPConfiguration.is_abort (NPConfiguration.mk c true) lo.
  Proof.
    intros.
    inv ABORT.
    destruct H as (st & lc & e' & Hcur_th & Hrtc_steps & Habort).
    econstructor; simpl.
    instantiate (1 := x).
    eapply cons_np_steps_from_p_steps_outatmblk in Hrtc_steps.
    destruct Hrtc_steps as (b & Hrtc_steps).
    do 5 eexists. exists b.
    split; eauto.
  Qed.

  Lemma config_abort_cont:
    forall n lang lo st lc sc mem st' lc' sc' mem' tid ths
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
      (STEPS: rtcn (Thread.tau_step lo) n
                   (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (ABORT: Configuration.is_abort
                (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) tid sc' mem') lo),
      Configuration.is_abort (Configuration.mk ths tid sc mem) lo.
  Proof.
    induction n; intros.
    - inv STEPS; simpls.
      rewrite IdentMap.gsident in ABORT; eauto.
    - inv STEPS.
      destruct a2. 
      eapply IHn with (ths := IdentMap.add tid (existT _ lang state, local) ths) in A23; eauto.

      Focus 2.
      instantiate (1 := tid).
      rewrite IdentMap.gss; eauto.

      Focus 2.
      rewrite IdentMap.add_add_eq; eauto.
      clear - TH A12 A23.
      inv A23; simpls.
      destruct H as (st1 & lc1 & e' & TH' & Hsteps & Habort).
      rewrite IdentMap.gss in TH'.
      inv TH'.
      eapply inj_pair2 in H1; subst.
      econstructor; simpl.
      exists st lc e'.
      split; eauto.
  Qed.      

  Lemma sound_np_abort_cur_not_abort:
    forall n lo c b c' b'
      (STEPS: rtcn (NPConfiguration.all_step lo) n (NPConfiguration.mk c b) (NPConfiguration.mk c' b'))
      (NPABORT: Configuration.is_abort c' lo)
      (CUR_NOT_ABORT: ~Configuration.is_abort c lo),
    exists c' b',
      rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c b) (NPConfiguration.mk c' b') /\
      NPConfiguration.is_abort (NPConfiguration.mk c' b') lo.
  Proof.
    induction n; intros.
    - inv STEPS. tryfalse.
    - inv STEPS.
      destruct a2.
      inv A12.
      inv H; simpls; try inv NPC2; subst; simpls.
      {
        (* tau step *) 
        assert (Habort_cont: 
                  ~Configuration.is_abort
                   {|
                     Configuration.threads :=
                       IdentMap.add (Configuration.tid c) (existT Language.state lang st2, lc2)
                                    (Configuration.threads c);
                     Configuration.tid := Configuration.tid c;
                     Configuration.sc := sc2;
                     Configuration.memory := m2
                   |} lo
               ).
        {
          clear - CUR_NOT_ABORT STEPS STEP TID1.
          introv Habort.
          contradiction CUR_NOT_ABORT.
          eapply rtc_n1 with (R := NPAuxThread.tau_step lang lo) in STEPS; eauto.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in STEPS; simpls.
          eapply rtc_rtcn in STEPS.
          destruct STEPS.
          eapply config_abort_cont in Habort; eauto.
        }
        eapply IHn in Habort_cont; eauto.
        destruct Habort_cont as (c'' & b'' & Hsteps & Habort).
        exists c'' b''.
        split; eauto.
        eapply Relation_Operators.rt1n_trans.
        2: eapply Hsteps.
        clear - TID1 STEPS STEP CONSISTENT.
        econstructor.
        eapply NPConfiguration.step_tau; eauto.
      }
      {
        (* sw step *)
        destruct(classic (Configuration.is_abort
                            {|
                              Configuration.threads := Configuration.threads c;
                              Configuration.tid := tid2;
                              Configuration.sc := Configuration.sc c;
                              Configuration.memory := Configuration.memory c
                            |} lo)) as [Hnth_abort | Hnth_not_abort].
        {
          (* new thread will abort *)
          eapply P_abort_to_NP_abort_from_outAtmBlk in Hnth_abort.
          do 2 eexists.
          split.
          2: eauto.
          eapply Relation_Operators.rt1n_trans.
          econstructor.
          eapply NPConfiguration.step_sw with (tid2 := tid2); eauto.
          eauto.
        }
        {
          (* new thread will not abort *)
          eapply IHn in Hnth_not_abort; eauto.
          destruct Hnth_not_abort as (c'' & b'' & Hsteps & Habort).
          exists c'' b''.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_sw with (tid2 := tid2); eauto.
        }
      }
      {
        (* term step *)
        destruct(classic (Configuration.is_abort
                            {|
                              Configuration.threads :=
                                IdentMap.remove (Configuration.tid c) (Configuration.threads c);
                              Configuration.tid := tid2;
                              Configuration.sc := Configuration.sc c;
                              Configuration.memory := Configuration.memory c
                            |} lo)) as [Hnth_abort | Hnth_not_abort].
        {
          (* new thread will abort *)
          eapply P_abort_to_NP_abort_from_outAtmBlk in Hnth_abort.
          do 2 eexists.
          split.
          2: eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eauto.
          econstructor.
          eapply NPConfiguration.step_thread_term with (tid2 := tid2); eauto.
        }
        {
          (* new thread will not abort *)
          eapply IHn in Hnth_not_abort; eauto.
          destruct Hnth_not_abort as (c'' & b'' & Hsteps & Habort).
          exists c'' b''.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_thread_term with (tid2 := tid2); eauto.
        }
      }
      {
        (* out step *)
        destruct(classic (Configuration.is_abort
                            {|
                              Configuration.threads :=
                                IdentMap.add (Configuration.tid c) (existT Language.state lang st2, lc2)
                                             (Configuration.threads c);
                              Configuration.tid := Configuration.tid c;
                              Configuration.sc := sc2;
                              Configuration.memory := m2
                            |} lo)) as [Hout_abort | Hout_not_abort].
        {
          (* will abort after out step *)
          eapply P_abort_to_NP_abort_from_outAtmBlk in Hout_abort.
          do 2 eexists.
          split.
          2: eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eauto.
          econstructor.
          eapply NPConfiguration.step_out; eauto.
        }
        {
          (* will not abort after out step *)
          eapply IHn in Hout_not_abort; eauto.
          destruct Hout_not_abort as (c'' & b'' & Hsteps & Habort).
          exists c'' b''.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_out; eauto.
        }
      }
  Qed.
      
  Lemma sound_np_abort:
    forall lo c
           (NP_SAFE: ~(exists npc',
                          rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc' /\
                          NPConfiguration.is_abort npc' lo)),
      ~(exists npc',
           rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc' /\
           Configuration.is_abort (NPConfiguration.cfg npc') lo).
  Proof.
    intros.
    introv Haux_abort.
    contradiction NP_SAFE.
    destruct Haux_abort as (npc' & Hrtc_np_steps & Habort).
    eapply rtc_rtcn in Hrtc_np_steps.
    destruct Hrtc_np_steps as (n & Hrtc_np_steps).
    destruct (classic (Configuration.is_abort c lo)).
    {
      eexists.
      split; eauto.
      eapply P_abort_to_NP_abort_from_outAtmBlk; eauto.
    }
    {
      destruct npc'.
      eapply sound_np_abort_cur_not_abort in H; eauto.
      destruct H as (c' & b' & Hsteps & Habort').
      eexists.
      eauto.
    }
  Qed.
    
End NP_Safe_to_No_ThreadAbort.

(** NP write-write race free to aux write-write race free *)
Section NP_WW_RF_to_Aux_WW_RF.
  Lemma ww_race_dly_rsv_step:
    forall lang lo (e e': Thread.t lang) loc val val' from to st' R
      (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e) st')
      (RC_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val' R) /\ 
               Memory.get loc to (Local.promises (Thread.local e)) = None)
      (WWRC: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
      (RSV_CCL_STEPS: (Thread.reserve_step lo) e e'),
      Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e') st' /\
      Memory.get loc to (Thread.memory e') = Some (from, Message.concrete val' R) /\
      Memory.get loc to (Local.promises (Thread.local e')) = None /\
      Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to.
  Proof.
    intros.
    inv RSV_CCL_STEPS.
    inv STEP.
    {
      (* reserve step *)
      inv LOCAL. inv PROMISE. simpls.
      destruct RC_MSG as (RC_MSG_IN_MEM & RC_MSG_NOT_PRM).
      split; eauto.
      split.
      eapply Memory.add_get1; eauto.
      split; eauto.
      eapply Memory.add_msg_not_exits in MEM; eauto.
      eapply Memory.msg_add_disj_origin_prsv; eauto.
    }
  Qed.

  Lemma ww_race_dly_rsv_steps:
    forall n lang lo (e e': Thread.t lang) loc val val' from to st' R
      (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e) st')
      (RC_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val' R) /\ 
               Memory.get loc to (Local.promises (Thread.local e)) = None)
      (WWRC: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
      (RSV_CCL_STEPS: rtcn (Thread.reserve_step lo) n e e'),
      Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e') st' /\
      Memory.get loc to (Thread.memory e') = Some (from, Message.concrete val' R) /\
      Memory.get loc to (Local.promises (Thread.local e')) = None /\
      Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to.
  Proof.
    induction n; ii; ss.
    - inv RSV_CCL_STEPS; eauto.
      des; eauto.
    - inv RSV_CCL_STEPS.
      des.
      eapply ww_race_dly_rsv_step with (e' := a2) in WRITE; eauto.
      des.
      eapply IHn in A23; eauto.
  Qed.

  Lemma ww_race_dly_ccl_step:
    forall lang lo (e e': Thread.t lang) loc val val' from to st' R
      (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e) st')
      (RC_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val' R) /\ 
               Memory.get loc to (Local.promises (Thread.local e)) = None)
      (WWRC: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
      (RSV_CCL_STEPS: (Thread.cancel_step lo) e e'),
      Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e') st' /\
      Memory.get loc to (Thread.memory e') = Some (from, Message.concrete val' R) /\
      Memory.get loc to (Local.promises (Thread.local e')) = None /\
      Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to.
  Proof.
    intros.
    inv RSV_CCL_STEPS.
    inv STEP; ss.
    {
      (* cancel step *)
      inv LOCAL. inv PROMISE. simpls.
      destruct RC_MSG as (RC_MSG_IN_MEM & RC_MSG_NOT_PRM).
      split; eauto.
      split.
      eapply Memory.concrete_msg_remove_rsv_stable; eauto.
      split; eauto.
      erewrite Memory.remove_o; eauto.
      destruct (loc_ts_eq_dec (loc, to) (loc0, to0)); eauto.
    }
  Qed.

  Lemma ww_race_dly_ccl_steps:
    forall n lang lo (e e': Thread.t lang) loc val val' from to st' R
      (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e) st')
      (RC_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val' R) /\ 
               Memory.get loc to (Local.promises (Thread.local e)) = None)
      (WWRC: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
      (RSV_CCL_STEPS: rtcn (Thread.cancel_step lo) n e e'),
      Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e') st' /\
      Memory.get loc to (Thread.memory e') = Some (from, Message.concrete val' R) /\
      Memory.get loc to (Local.promises (Thread.local e')) = None /\
      Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to.
  Proof.
    induction n; ii; ss.
    - inv RSV_CCL_STEPS; eauto.
      des; eauto.
    - inv RSV_CCL_STEPS.
      des.
      eapply ww_race_dly_ccl_step with (e' := a2) in WRITE; eauto.
      des.
      eapply IHn in A23; eauto.
  Qed.
      
  Lemma ww_race_dly_rsv_or_ccl_steps
        n1 n2 lang lo (e e' e'': Thread.t lang) loc val val' from to st' R
        (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e) st')
        (RC_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val' R) /\ 
                 Memory.get loc to (Local.promises (Thread.local e)) = None)
        (WWRC: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
        (CCL_STEPS: rtcn (Thread.cancel_step lo) n1 e e')
        (RSV_STEPS: rtcn (Thread.reserve_step lo) n2 e' e''):
    Language.step lang (ProgramEvent.write loc val Ordering.plain) (Thread.state e'') st' /\
    Memory.get loc to (Thread.memory e'') = Some (from, Message.concrete val' R) /\
    Memory.get loc to (Local.promises (Thread.local e'')) = None /\
    Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e''))) loc) to.
  Proof.
    eapply ww_race_dly_ccl_steps in CCL_STEPS; eauto.
    des.
    eapply ww_race_dly_rsv_steps in RSV_STEPS; eauto.
  Qed.
  
  Lemma aux_wwrace_to_np_wwrace_from_outAtmBlk:
    forall c lo
      (AUX_WW_RACE: aux_ww_race lo c)
      (CONFIG_WF: Configuration.wf c),
    exists npc', rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc' /\
            ww_race lo (NPConfiguration.cfg npc').
  Proof.
    intros.
    inv AUX_WW_RACE.
    destruct FULFILL as (FULFILL_STEPS & IS_FULFILL).
    eapply rtc_rtcn in FULFILL_STEPS.
    destruct FULFILL_STEPS as (n & FULFILL_STEPS).
    eapply consistent_construct_from_fulfill in FULFILL_STEPS; eauto; ss.
    destruct FULFILL_STEPS as (e0 & e1& CCL_STEPS & RSV_STEPS & CONSISTENT).
    eapply rtc_rtcn in CCL_STEPS.
    destruct CCL_STEPS as (n1 & CCL_STEPS).
    eapply rtc_rtcn in RSV_STEPS.
    destruct RSV_STEPS as (n2 & RSV_STEPS).
    lets Hdly_ww_race : CCL_STEPS. 
    eapply ww_race_dly_rsv_or_ccl_steps with (val := val) (val' := val') in Hdly_ww_race; eauto.
    destruct Hdly_ww_race as (WRITE' & RC_MSG_IN_MEM & RC_MSG_NOT_PRM & RC_MSG').
    eapply cancel_steps_is_allsteps in CCL_STEPS.
    eapply reserve_steps_is_allsteps in RSV_STEPS.
    assert (Hto_wwrace_steps: rtc (Thread.all_step lo) (Thread.mk lang st lc sc mem) e1).
    {
      eapply rtc_compose; [eapply STEPS | eauto..].
      eapply rtc_compose; [eapply CCL_STEPS | eapply RSV_STEPS].
    }  
    destruct e1; simpls.
    lets CONFIG_WF': Hto_wwrace_steps.
    eapply wf_config_rtc_thread_steps_prsv in CONFIG_WF'; eauto.      
    eapply thread_all_step_to_NPConfiguration_all_step_from_outAtmBlk in Hto_wwrace_steps; eauto.
    2: eapply Thread_consistent_to_consistent_nprm; eauto; simpl.
    destruct Hto_wwrace_steps as (b' & Hto_wwrace_steps).
    eexists.
    split; eauto.
    simpl. 
    econstructor. 
    rewrite IdentMap.gss; eauto.
    eapply WRITE'.
    split; [eapply RC_MSG_IN_MEM | eapply RC_MSG_NOT_PRM]. 
    eauto.   
    inv CONFIG_WF'; simpls.
    inv WF.
    eapply THREADS with (tid0 := tid).
    rewrite IdentMap.gss; eauto. 
    inv CONFIG_WF'; simpls; eauto; ss.
    eapply Thread.rtc_all_step_future in STEPS; eauto; ss. des; eauto.
    inv CONFIG_WF; ss. inv WF.
    eapply THREADS; eauto.
    inv CONFIG_WF; ss. inv CONFIG_WF; eauto.
    eapply Thread.rtc_all_step_future in STEPS; eauto; ss. des; eauto.
    inv CONFIG_WF; ss. inv WF.
    eapply THREADS; eauto.
    inv CONFIG_WF; ss. inv CONFIG_WF; eauto.
  Qed.

  Lemma config_aux_wwrace_cont_rtc:
    forall lang lo st lc sc mem st' lc' sc' mem' tid ths
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc))
      (STEPS: rtc (Thread.all_step lo) 
                  (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (AUX_WW_RACE: aux_ww_race lo (Configuration.mk (IdentMap.add tid (existT _ lang st', lc') ths) tid sc' mem')),
      aux_ww_race lo (Configuration.mk ths tid sc mem).
  Proof.
    intros.
    inv AUX_WW_RACE.
    rewrite IdentMap.gss in CTID.
    inv CTID.
    eapply inj_pair2 in H1; subst.
    econstructor.
    eapply TH.
    eapply rtc_compose; [eapply STEPS | eapply STEPS0].
    eapply WRITE.
    eapply RC_MSG.
    eapply WWRC.
    eapply FULFILL.
  Qed.

  Lemma sound_aux_wwrace_cur_not_race:
    forall n lo c b c' b'
      (STEPS: rtcn (NPConfiguration.all_step lo) n (NPConfiguration.mk c b) (NPConfiguration.mk c' b'))
      (AUX_WWRACE: aux_ww_race lo c')
      (CUR_NOT_AUX_WWRACE: ~aux_ww_race lo c)
      (CONFIG_WF: Configuration.wf c),
    exists c' b',
      rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c b) (NPConfiguration.mk c' b') /\
      ww_race lo c'.
  Proof.
    induction n; intros.
    - inv STEPS; tryfalse.
    - inv STEPS.
      destruct a2.
      inv A12.
      inv H; simpls.
      {
        (* tau step *)
        inv NPC2.
        assert(Hcont_not_aux_race: 
                 ~aux_ww_race lo (
                    Configuration.mk (IdentMap.add (Configuration.tid c)
                                                   (existT _ lang st2, lc2) (Configuration.threads c))
                                     (Configuration.tid c) sc2 m2)).
        {
          introv Hcont_aux_ww_race.
          contradiction CUR_NOT_AUX_WWRACE.
          destruct c; simpls.
          eapply config_aux_wwrace_cont_rtc with (st' := st2) (lc' := lc2); eauto.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in STEPS; simpls.
          eapply NPAuxThread_tau_step_2_Thread_tau_step in STEP; simpls.
          eapply rtc_n1.
          eapply Thread_tau_steps_is_all_steps; eauto.
          eapply Thread_tau_step_is_all_step; eauto.
        }
        eapply IHn in A23; eauto.
        simpls.
        destruct A23 as (c'' & b'' & Hsteps & Hww_race).
        do 2 eexists.
        split.
        2: eapply Hww_race.
        eapply Relation_Operators.rt1n_trans.
        2: eapply Hsteps.
        econstructor.
        eapply NPConfiguration.step_tau; eauto.
        eapply NPAuxThread_tau_steps_2_Thread_tau_steps in STEPS; simpls.
        eapply NPAuxThread_tau_step_2_Thread_tau_step in STEP; simpls.
        eapply Thread_tau_steps_is_all_steps in STEPS.
        eapply Thread_tau_step_is_all_step in STEP.
        destruct c; simpls.
        eapply wf_config_rtc_thread_steps_prsv; [eapply CONFIG_WF | eapply TID1 | ..].
        eapply rtc_n1; [eapply STEPS | eapply STEP].
      }
      {
        (* sw step *)
        subst.
        inv NPC2.
        destruct c; simpls.
        destruct (classic (aux_ww_race lo (Configuration.mk threads tid2 sc memory))) as
            [Haux_ww_race_nth | Hnot_aux_ww_race_nth].
        {
          eapply aux_wwrace_to_np_wwrace_from_outAtmBlk in Haux_ww_race_nth.
          destruct Haux_ww_race_nth as (npc' & Hsteps & Hww_race).
          destruct npc'; simpls.
          exists cfg preempt.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_sw; eauto.
          eapply wf_config_sw_prsv; eauto.
        }
        {
          eapply IHn in Hnot_aux_ww_race_nth; eauto.
          destruct Hnot_aux_ww_race_nth as (c'' & b'' & Hsteps & Hww_race).
          exists c'' b''.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_sw; eauto.
          eapply wf_config_sw_prsv; eauto.
        }
      }
      {
        (* term step *)
        inv NPC2; simpls.
        destruct c; simpls.
        destruct (classic (aux_ww_race lo (Configuration.mk (IdentMap.remove tid threads) tid2 sc memory))) as
            [Haux_ww_race_nth | Hnot_aux_ww_race_nth].
        {
          eapply aux_wwrace_to_np_wwrace_from_outAtmBlk in Haux_ww_race_nth.
          destruct Haux_ww_race_nth as (npc' & Hsteps & Hww_race).
          destruct npc'; simpls.
          exists cfg preempt.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_thread_term; eauto.
          eapply wf_config_rm_prsv; eauto.
        }
        {
          eapply IHn in Hnot_aux_ww_race_nth; eauto.
          destruct Hnot_aux_ww_race_nth as (c'' & b'' & Hsteps & Hww_race).
          exists c'' b''.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          2: eapply Hsteps.
          econstructor.
          eapply NPConfiguration.step_thread_term; eauto.
          eapply wf_config_rm_prsv; eauto.
        }
      }
      {
        (* output step *)
        inv NPC2; simpls.
        assert(Hcont_not_aux_race: 
                 ~aux_ww_race lo (
                    Configuration.mk (IdentMap.add (Configuration.tid c)
                                                   (existT _ lang st2, lc2) (Configuration.threads c))
                                     (Configuration.tid c) sc2 m2)).
        {
          introv Hcon_aux_race.
          contradiction CUR_NOT_AUX_WWRACE.
          destruct c; simpls.
          eapply config_aux_wwrace_cont_rtc with (st' := st2) (lc' := lc2); eauto.
          eapply Operators_Properties.clos_rt1n_step.
          eapply NPAuxThread_out_step_is_Thread_program_step in STEP; eauto.
        }
        eapply IHn in Hcont_not_aux_race; eauto.
        destruct Hcont_not_aux_race as (c'' & b'' & Hsteps & Hww_race).
        exists c'' b''.
        split; eauto.
        eapply Relation_Operators.rt1n_trans.
        2: eapply Hsteps.
        econstructor.
        eapply NPConfiguration.step_out; eauto.
        eapply NPAuxThread_out_step_is_Thread_program_step in STEP; simpls.
        destruct c; simpls.
        eapply wf_config_thread_step_prsv; eauto.
      }
  Qed.
  
  Lemma sound_np_aux_wwrf:
    forall lo c
      (CONFIG_WF: Configuration.wf c)
      (NP_WW_RF: ~(exists npc',
                      rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc' /\
                      ww_race lo (NPConfiguration.cfg npc'))),
      ~(exists npc',
           rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc' /\
           aux_ww_race lo (NPConfiguration.cfg npc')).
  Proof.
    intros.
    introv AUX_WW_RACE.
    contradiction NP_WW_RF.
    destruct AUX_WW_RACE as (npc' & STEPS & AUX_WW_RACE).
    destruct (classic (aux_ww_race lo c)).
    {
      eapply aux_wwrace_to_np_wwrace_from_outAtmBlk; eauto.
    }
    { 
      destruct npc'; simpls.
      eapply rtc_rtcn in STEPS.
      destruct STEPS as (n & STEPS).
      eapply sound_aux_wwrace_cur_not_race with (b := true) in STEPS; eauto.
      destruct STEPS as (c'' & b'' & STEPS & Hww_race).
      exists (NPConfiguration.mk c'' b'').
      simpl.
      split; eauto.
    }
  Qed.

  Lemma sound_np_aux_wwrace
        lo c npc
        (CONFIG_WF: Configuration.wf c)
        (NP_WW_RACE: rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc /\
                     aux_ww_race lo (NPConfiguration.cfg npc)):
    exists npc',
      rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc' /\
      ww_race lo (NPConfiguration.cfg npc').
  Proof.
    des.
    destruct (classic (exists npc, rtc (NPConfiguration.all_step lo) (NPConfiguration.mk c true) npc /\
                              ww_race lo (NPConfiguration.cfg npc))); eauto.
    eapply sound_np_aux_wwrf in H; eauto.
    contradiction H; eauto.
  Qed.
End NP_WW_RF_to_Aux_WW_RF.

Inductive rely_local_sim_state {index: Type} {index_order: index -> index -> Prop} {lang: language}:
  Invariant -> Ordering.LocOrdMap -> Mapping -> Thread.t lang -> Thread.t lang -> Prop :=
| rely_local_sim_state_intro
    (I: Invariant) lo inj
    st_tgt lc_tgt sc_tgt mem_tgt
    st_src lc_src sc_src mem_src
    (RELY_LOCAL_SIM: 
       forall inj' sc_tgt' mem_tgt' sc_src' mem_src' 
         (RELY: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                     inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')
                     (Local.promises lc_tgt) (Local.promises lc_src) lo)
         (INV: I lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')),
         @local_sim_state index index_order lang
                          I lo inj' dset_init true
                          (Thread.mk lang st_tgt lc_tgt sc_tgt' mem_tgt')
                          (Thread.mk lang st_src lc_src sc_src' mem_src')
    ):
    rely_local_sim_state I lo inj
                         (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                         (Thread.mk lang st_src lc_src sc_src mem_src).

Lemma local_sim_state_to_rely_local_sim_state
      lang index index_order I lo inj ths_src ctid tid
      st_tgt lc_tgt sc_tgt mem_tgt
      st_src lc_src sc_src mem_src
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset_init true
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (ID: IdentMap.find tid ths_src = Some (existT _ lang st_src, lc_src))
      (NP_SAFE: ~(exists npc',
                     rtc (NPConfiguration.all_step lo)
                         (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) true) npc' /\
                     NPConfiguration.is_abort npc' lo))
      (T_PROM_CONS: Local.promise_consistent lc_tgt):
  @rely_local_sim_state index index_order lang I lo inj
                        (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                        (Thread.mk lang st_src lc_src sc_src mem_src).
Proof.
  inv LOCAL_SIM; ss.
  - (* abort *)
    contradiction NP_SAFE.
    eexists.
    split.
    eapply Relation_Operators.rt1n_trans.
    econs.
    (* switch to tid *)
    eapply NPConfiguration.step_sw; ss; eauto.
    eauto.
    unfold NPConfiguration.is_abort; ss.
    do 7 eexists.
    split. eauto.
    ss.
    split.
    eapply ID.
    split; eauto.
  - (* rely *)
    clear STEP_INV THRD_STEP THRD_DONE THRD_ABORT.
    exploit RELY_STEP; eauto. clear RELY_STEP. ii. des.
    econs. ii. eauto.
Qed.

Lemma rely_local_sim_state_to_local_sim_state
      lang index index_order I lo inj
      st_tgt lc_tgt sc_tgt mem_tgt
      st_src lc_src sc_src mem_src
      (R_LOCAL_SIM: @rely_local_sim_state index index_order lang I lo inj
                                          (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                          (Thread.mk lang st_src lc_src sc_src mem_src))
      (INV: I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
      (LOCAL_WF_S: Local.wf lc_src mem_src)
      (SC_CLOSED: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_CLOSED: Memory.closed mem_tgt)
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src):
  @local_sim_state index index_order lang I lo inj dset_init true
                  (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                  (Thread.mk lang st_src lc_src sc_src mem_src).
Proof.
  inv R_LOCAL_SIM.
  assert(RELY_ID: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                       inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                       (Local.promises lc_tgt) (Local.promises lc_src) lo).
  {
    econs; ss.
    econs; ss; eauto.
    unfold concrete_mem_incr. ii.
    exists f R. split.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    split. auto_solve_time_rel.
    split; eauto. ii. inv H0; ss.
    assert (Time.lt f f). auto_solve_time_rel.
    auto_solve_time_rel.
    
    unfold concrete_mem_incr. ii.
    exists f R. split.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    split. auto_solve_time_rel.
    split; eauto.
    ii. inv H0; ss.
    assert (Time.lt f f). auto_solve_time_rel.
    auto_solve_time_rel.
    
    eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
    eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
    inv LOCAL_WF_T; eauto.
    inv LOCAL_WF_S; eauto.
  }
  eapply RELY_LOCAL_SIM; eauto.
Qed.

Lemma concrete_covered_concrete_mem_incr_prsv
      loc ts mem mem'
      (CONCRETE_COVERED: concrete_covered loc ts mem)
      (CMEM_INCR: concrete_mem_incr mem mem'):
  concrete_covered loc ts mem'.
Proof.
  unfold concrete_mem_incr in *.
  inv CONCRETE_COVERED.
  exploit CMEM_INCR; eauto. ii; des.
  destruct (Time.le_lt_dec ts f').
  {
    eapply x2; eauto.
    inv ITV; ss.
  }
  {
    econs; eauto.
    econs; ss; eauto.
    inv ITV; ss.
  }
Qed.
  
Lemma concrete_mem_incr_transitivity
      mem mem' mem''
      (CMEM_INCR1: concrete_mem_incr mem mem')
      (CMEM_INCR2: concrete_mem_incr mem' mem''):
  concrete_mem_incr mem mem''.
Proof.
  unfold concrete_mem_incr in *. ii.
  exploit CMEM_INCR1; eauto. ii; des.
  exploit CMEM_INCR2; eauto. ii; des.
  exists f'0 R'0.
  split; eauto.
  split; eauto.
  auto_solve_time_rel.
  split; eauto.
  ii. 
  inv H0; ss.
  destruct (Time.le_lt_dec ts f').
  {
    specialize (x2 ts). exploit x2; eauto.
    econs; eauto. ii.
    eapply concrete_covered_concrete_mem_incr_prsv; eauto.
  }
  {
    eapply x6; eauto.
    econs; ss; eauto.
  }
Qed.
  
Lemma env_steps_transistivity
      S S' S'' p_tgt p_src
      (ENV_STEPS1: env_steps S S' p_tgt p_src)
      (ENV_STEPS2: env_steps S' S'' p_tgt p_src):
  env_steps S S'' p_tgt p_src.
Proof.
  inv ENV_STEPS1. inv ENV_STEPS2.
  econs; eauto.
  eapply concrete_mem_incr_transitivity; eauto.
  eapply concrete_mem_incr_transitivity; eauto.
Qed.

Lemma NPThread_step_implies_env_steps
      lang lo st lc sc mem b st' lc' sc' mem' b'
      (STEP: NPAuxThread.tau_step lang lo (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) b)
                                  (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') b')):
  concrete_mem_incr mem mem' /\ TimeMap.le sc sc'.
Proof.
  eapply NPThread_tau_step_to_program_step in STEP; eauto.
  des.
  - destruct te; ss; inv STEP.
    + inv LOCAL.
    + inv LOCAL. split; eauto.
      unfold concrete_mem_incr. ii; des.
      exists f R.
      split; eauto.
      eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      split; eauto.
      auto_solve_time_rel.
      split; eauto.
      ii. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel.
      auto_solve_time_rel.
      eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
    + inv LOCAL. split; eauto.
      unfold concrete_mem_incr. ii; des.
      exists f R.
      split; eauto.
      eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      split; eauto.
      auto_solve_time_rel.
      split; eauto.
      ii. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel.
      auto_solve_time_rel.
      eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
    + inv LOCAL. inv LOCAL0. inv WRITE. inv PROMISE; ss.
      {
        split; [ | eapply View.TimeMap.le_PreOrder_obligation_1; eauto].
        unfold concrete_mem_incr. ii.
        exploit Memory.add_get1; eauto. ii; des.
        exists f R.
        split; eauto.
        eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        split; eauto.
        auto_solve_time_rel.
        split; eauto.
        ii. inv H0; ss.
        assert (Time.lt f f). auto_solve_time_rel.
        auto_solve_time_rel.
      }
      {
        des; subst. inv RESERVE.
        split; [ | eapply View.TimeMap.le_PreOrder_obligation_1; eauto].
        unfold concrete_mem_incr. ii.
        exploit Memory.split_get1; eauto. ii; des.
        exists f' R.
        split; eauto.
        eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        split; eauto.
        split; eauto.
        ii.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          destruct (Time.eq_dec t ts3); subst.
          {
            exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
            rewrite H in GET0. inv GET0.
            rewrite GET3 in GET2. inv GET2.
            econs; eauto.
          }
          {
            assert (Memory.get loc0 t mem' = Some (f, Message.concrete val R)).
            erewrite Memory.split_o; eauto.
            des_if; ss; des; subst; ss; eauto.
            exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
            rewrite H in GET. ss.
            des_if; ss; des; subst; ss; eauto.
            rewrite GET2 in H1. inv H1. inv H0; ss.
            assert (Time.lt f f). auto_solve_time_rel.
            auto_solve_time_rel.
          }
        }
        {
          assert (Memory.get loc0 t mem' = Some (f, Message.concrete val R)).
          erewrite Memory.split_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          des_if; ss; des; subst; ss; eauto.
          des_if; ss; des; subst; ss; eauto.
          rewrite GET2 in H1. inv H1. inv H0; ss.
          assert (Time.lt f f). auto_solve_time_rel.
          auto_solve_time_rel.
        }
      }
      {
        des; subst.
        split; [ | eapply View.TimeMap.le_PreOrder_obligation_1; eauto].
        unfold concrete_mem_incr. ii.
        exploit Memory.lower_get1; [eapply MEM | eapply H | eauto..]. ii; des.
        inv MSG_LE.
        exists f released0.
        split; eauto.
        split; eauto.
        auto_solve_time_rel.
        split; eauto.
        ii. inv H0; ss.
        assert (Time.lt f f). auto_solve_time_rel.
        auto_solve_time_rel.
      }
    + inv LOCAL.
      inv LOCAL2. inv WRITE. inv PROMISE; ss.
      {
        split; [ | eapply View.TimeMap.le_PreOrder_obligation_1; eauto].
        unfold concrete_mem_incr. ii.
        exploit Memory.add_get1; eauto. ii; des.
        exists f R.
        split; eauto.
        eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        split; eauto.
        auto_solve_time_rel.
        split; eauto.
        ii. inv H0; ss.
        assert (Time.lt f f). auto_solve_time_rel.
        auto_solve_time_rel.
      }
      {
        des; subst. inv RESERVE.
        split; [ | eapply View.TimeMap.le_PreOrder_obligation_1; eauto].
        unfold concrete_mem_incr. ii.
        exploit Memory.split_get1; eauto. ii; des.
        exists f' R.
        split; eauto.
        eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        split; eauto.
        split; eauto.
        ii.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          destruct (Time.eq_dec t ts3); subst.
          {
            exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
            rewrite H in GET0. inv GET0.
            rewrite GET3 in GET2. inv GET2.
            econs; eauto.
          }
          {
            assert (Memory.get loc0 t mem' = Some (f, Message.concrete val R)).
            erewrite Memory.split_o; eauto.
            des_if; ss; des; subst; ss; eauto.
            exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
            rewrite H in GET. ss.
            des_if; ss; des; subst; ss; eauto.
            rewrite GET2 in H1. inv H1. inv H0; ss.
            assert (Time.lt f f). auto_solve_time_rel.
            auto_solve_time_rel.
          }
        }
        {
          assert (Memory.get loc0 t mem' = Some (f, Message.concrete val R)).
          erewrite Memory.split_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          des_if; ss; des; subst; ss; eauto.
          des_if; ss; des; subst; ss; eauto.
          rewrite GET2 in H1. inv H1. inv H0; ss.
          assert (Time.lt f f). auto_solve_time_rel.
          auto_solve_time_rel.
        }
      }
      {
        des; subst.
        split; [ | eapply View.TimeMap.le_PreOrder_obligation_1; eauto].
        unfold concrete_mem_incr. ii.
        exploit Memory.lower_get1; [eapply MEM | eapply H | eauto..]. ii; des.
        inv MSG_LE.
        exists f released0.
        split; eauto.
        split; eauto.
        auto_solve_time_rel.
        split; eauto.
        ii. inv H0; ss.
        assert (Time.lt f f). auto_solve_time_rel.
        auto_solve_time_rel.
      }
    + inv LOCAL.
      split.
      unfold concrete_mem_incr. ii.
      exists f R. split; eauto.
      eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      split; eauto. auto_solve_time_rel.
      split; eauto.
      ii. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel. auto_solve_time_rel.
      inv LOCAL0.
      unfold TView.read_fence_tview, TView.write_fence_sc; ss.
      des_if.
      eapply TimeMap.join_l.
      eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
    + contradiction STEP0; eauto.
  - inv STEP.
    split. 2: eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
    unfold concrete_mem_incr. ii. inv LOCAL. inv PROMISE.
    + exploit Memory.add_get1; eauto. ii; des.
      exists f R.
      split; eauto.
      eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      split; eauto.
      auto_solve_time_rel.
      split; eauto.
      ii. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel. auto_solve_time_rel.
    + exploit Memory.split_get1; eauto. ii; des. subst.
      exists f' R.
      split; eauto.
      eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      split; eauto. split; eauto.
      ii.
      destruct (Loc.eq_dec loc loc0); subst.
      {
        destruct (Time.eq_dec t ts3); subst.
        {
          exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
          rewrite H in GET0. inv GET0.
          rewrite GET3 in GET2. inv GET2.
          econs; eauto.
        }
        {
          assert (Memory.get loc0 t mem' = Some (f, Message.concrete val R)).
          erewrite Memory.split_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
          rewrite H in GET. ss.
          des_if; ss; des; subst; ss; eauto.
          rewrite GET2 in H1. inv H1. inv H0; ss.
          assert (Time.lt f f). auto_solve_time_rel.
          auto_solve_time_rel.
        }
      }
      {
        assert (Memory.get loc0 t mem' = Some (f, Message.concrete val R)).
        erewrite Memory.split_o; eauto.
        des_if; ss; des; subst; ss; eauto.
        des_if; ss; des; subst; ss; eauto.
        des_if; ss; des; subst; ss; eauto.
        rewrite GET2 in H1. inv H1. inv H0; ss.
        assert (Time.lt f f). auto_solve_time_rel.
        auto_solve_time_rel.
      }
    + des; subst.
      exploit Memory.lower_get1; [eapply MEM | eapply H | eauto..]. ii; des.
      inv MSG_LE.
      exists f released0.
      split; eauto.
      split; eauto.
      auto_solve_time_rel.
      split; eauto.
      ii. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel. auto_solve_time_rel.
    + exploit Memory.concrete_msg_remove_rsv_stable; eauto. ii.
      exists f R.
      split; eauto.
      eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      split; eauto.
      auto_solve_time_rel.
      split; eauto.
      ii. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel.
      auto_solve_time_rel.
Qed.

Lemma NPThread_steps_implies_env_steps
      lang lo n st lc sc mem b st' lc' sc' mem' b'
      (STEPS: rtcn (NPAuxThread.tau_step lang lo) n
                   (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) b)
                   (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') b')):
  concrete_mem_incr mem mem' /\ TimeMap.le sc sc'.
Proof.
  ginduction n; ss; ii.
  - inv STEPS. split; eauto. 
    econs. exists R. split; eauto.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    instantiate (1 := f).
    split. eapply Time.le_lteq; eauto.
    split; eauto.
    ii. inv H0; ss.
    assert (Time.lt f f). auto_solve_time_rel.
    auto_solve_time_rel.
    eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
  - inv STEPS. destruct a2. destruct state.
    exploit NPThread_step_implies_env_steps; [eapply A12 | eauto..].
    ii; des.
    exploit IHn; [eapply A23 | eauto..].
    ii. des.
    split; eauto.
    eapply concrete_mem_incr_transitivity; eauto.
Qed.

Lemma NPThread_out_step_implies_env_steps
      lang lo st lc sc mem b st' lc' sc' mem' b' e
      (STEPS: NPAuxThread.out_step lang lo e
                                   (NPAuxThread.mk lang (Thread.mk lang st lc sc mem) b)
                                   (NPAuxThread.mk lang (Thread.mk lang st' lc' sc' mem') b')):
  concrete_mem_incr mem mem' /\ TimeMap.le sc sc'.
Proof.
  inv STEPS; ss. inv H; ss.
  inv OUT; ss. inv LOCAL; ss. inv LOCAL0; ss.
  split.
  unfold concrete_mem_incr. ii.
  exists f R.
  split. eapply View.View.opt_le_PreOrder_obligation_1; eauto.
  split. auto_solve_time_rel.
  split; eauto.
  ii. inv H0; ss.
  assert (Time.lt f f). auto_solve_time_rel.
  auto_solve_time_rel.
  unfold TView.write_fence_sc, TView.read_fence_tview; ss.
  des_if.
  eapply TimeMap.join_l; eauto.
  eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
Qed.
  
Lemma local_sim_rely_condition
      lang lang2 lo inj I inj' index index_order
      n_tgt st_tgt1 lc_tgt1 sc_tgt mem_tgt b_tgt st_tgt1' lc_tgt1' sc_tgt' mem_tgt' b_tgt'
      n_src st_src1 lc_src1 sc_src mem_src b_src st_src1' lc_src1' sc_src' mem_src' b_src'
      st_tgt2 lc_tgt2 st_src2 lc_src2
      (T_STEPS: rtcn (NPAuxThread.tau_step lang lo) n_tgt
                     (NPAuxThread.mk lang (Thread.mk lang st_tgt1 lc_tgt1 sc_tgt mem_tgt) b_tgt)
                     (NPAuxThread.mk lang (Thread.mk lang st_tgt1' lc_tgt1' sc_tgt' mem_tgt') b_tgt'))
      (S_STEPS: rtcn (NPAuxThread.tau_step lang lo) n_src
                     (NPAuxThread.mk lang (Thread.mk lang st_src1 lc_src1 sc_src mem_src) b_src)
                     (NPAuxThread.mk lang (Thread.mk lang st_src1' lc_src1' sc_src' mem_src') b_src'))
      (LOCAL_SIM: @rely_local_sim_state index index_order lang2 I lo inj
                                        (Thread.mk lang2 st_tgt2 lc_tgt2 sc_tgt mem_tgt)
                                        (Thread.mk lang2 st_src2 lc_src2 sc_src mem_src))
      (INJ_INCR: incr_inj inj inj')
      (LOCAL_WF_T: Local.wf lc_tgt1 mem_tgt)
      (LOCAL_WF_S: Local.wf lc_src1 mem_src)
      (CLOSED_TM_T: Memory.closed_timemap sc_tgt mem_tgt)
      (CLOSED_TM_S: Memory.closed_timemap sc_src mem_src)
      (MEM_CLOSED_T: Memory.closed mem_tgt)
      (MEM_CLOSED_S: Memory.closed mem_src)
      (LOCAL_WF_T': Local.wf lc_tgt2 mem_tgt')
      (LOCAL_WF_S': Local.wf lc_src2 mem_src')
      (CLOSED_TM_T': Memory.closed_timemap sc_tgt' mem_tgt')
      (MEM_CLOSED_T': Memory.closed mem_tgt'):
  @rely_local_sim_state index index_order lang2 I lo inj'
                        (Thread.mk lang2 st_tgt2 lc_tgt2 sc_tgt' mem_tgt')
                        (Thread.mk lang2 st_src2 lc_src2 sc_src' mem_src').
Proof.
  inv LOCAL_SIM.
  econs; ss; ii.
  assert(RELY_CONS: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                         inj'0 (Build_Rss sc_tgt'0 mem_tgt'0 sc_src'0 mem_src'0)
                         (Local.promises lc_tgt2) (Local.promises lc_src2) lo).
  {
    inv RELY; ss.
    econs; eauto.
    eapply env_steps_transistivity; [ | eapply ENV_STEPS].
    exploit NPThread_steps_implies_env_steps; [eapply T_STEPS | eauto..]. ii; des.
    exploit NPThread_steps_implies_env_steps; [eapply S_STEPS | eauto..]. ii; des.
    inv ENV_STEPS; ss.
    econs; eauto; ss.
    inv LOCAL_WF_T'; eauto.
    inv LOCAL_WF_S'; eauto.
    eapply incr_inj_transitivity; eauto.
  }
  eapply RELY_LOCAL_SIM; eauto.
Qed.

Lemma local_sim_out_rely_condition
      lang lang2 lo inj I inj' index index_order
      st_tgt1 lc_tgt1 sc_tgt mem_tgt e b_tgt st_tgt1' lc_tgt1' sc_tgt' mem_tgt' b_tgt'
      st_src1 lc_src1 sc_src mem_src
      st_src0 lc_src0 sc_src0 mem_src0 b_src0
      e' b_src st_src1' lc_src1' sc_src' mem_src' b_src'
      st_tgt2 lc_tgt2 st_src2 lc_src2 n_src
      (T_STEP: NPAuxThread.out_step
                 lang lo e
                 (NPAuxThread.mk lang (Thread.mk lang st_tgt1 lc_tgt1 sc_tgt mem_tgt) b_tgt)
                 (NPAuxThread.mk lang (Thread.mk lang st_tgt1' lc_tgt1' sc_tgt' mem_tgt') b_tgt'))
      (S_STEPS: rtcn (NPAuxThread.tau_step lang lo) n_src
                     (NPAuxThread.mk lang (Thread.mk lang st_src1 lc_src1 sc_src mem_src) b_src)
                     (NPAuxThread.mk lang (Thread.mk lang st_src0 lc_src0 sc_src0 mem_src0) b_src0))
      (S_STEP: NPAuxThread.out_step
                 lang lo e'
                 (NPAuxThread.mk lang (Thread.mk lang st_src0 lc_src0 sc_src0 mem_src0) b_src0)
                 (NPAuxThread.mk lang (Thread.mk lang st_src1' lc_src1' sc_src' mem_src') b_src'))
      (LOCAL_SIM: @rely_local_sim_state index index_order lang2 I lo inj
                                        (Thread.mk lang2 st_tgt2 lc_tgt2 sc_tgt mem_tgt)
                                        (Thread.mk lang2 st_src2 lc_src2 sc_src mem_src))
      (INJ_INCR: incr_inj inj inj')
      (LOCAL_WF_T: Local.wf lc_tgt1 mem_tgt)
      (LOCAL_WF_S: Local.wf lc_src1 mem_src)
      (CLOSED_TM_T: Memory.closed_timemap sc_tgt mem_tgt)
      (CLOSED_TM_S: Memory.closed_timemap sc_src mem_src)
      (MEM_CLOSED_T: Memory.closed mem_tgt)
      (MEM_CLOSED_S: Memory.closed mem_src)
      (LOCAL_WF_T': Local.wf lc_tgt2 mem_tgt')
      (LOCAL_WF_S': Local.wf lc_src2 mem_src')
      (CLOSED_TM_T': Memory.closed_timemap sc_tgt' mem_tgt')
      (MEM_CLOSED_T': Memory.closed mem_tgt'):
  @rely_local_sim_state index index_order lang2 I lo inj'
                        (Thread.mk lang2 st_tgt2 lc_tgt2 sc_tgt' mem_tgt')
                        (Thread.mk lang2 st_src2 lc_src2 sc_src' mem_src').
Proof.
  inv LOCAL_SIM. econs; ii. 
  assert(RELY_CONS: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                         inj'0 (Build_Rss sc_tgt'0 mem_tgt'0 sc_src'0 mem_src'0)
                         (Local.promises lc_tgt2) (Local.promises lc_src2) lo).
  {
    inv RELY; ss.
    econs; eauto.
    eapply env_steps_transistivity; [ | eapply ENV_STEPS].
    exploit NPThread_out_step_implies_env_steps; [eapply T_STEP | eauto..]. ii; des.
    exploit NPThread_steps_implies_env_steps; [eapply S_STEPS | eauto..]. ii; des.
    exploit NPThread_out_step_implies_env_steps; [eapply S_STEP | eauto..]. ii; des.
    inv ENV_STEPS; ss.
    econs; eauto; ss.
    eapply concrete_mem_incr_transitivity; eauto.
    inv LOCAL_WF_T'; eauto.
    inv LOCAL_WF_S'; eauto.
    eapply incr_inj_transitivity; eauto.
  }
  eapply RELY_LOCAL_SIM; eauto.
Qed.

