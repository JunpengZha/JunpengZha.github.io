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
Require Import Configuration.
Require Import MsgMapping.
Require Import DelaySet.
Require Import NPConfiguration.

Require Import LocalSim.
Require Import GlobSim.
Require Import ww_RF.

Require Import LibTactics.

Lemma threads_add_preserve:
  forall fs lang (code_t code_s: Language.syntax lang) ths ths0 tid ths'
    (THRD_ADD_TGT: Threads.add_ths ths tid fs code_t = Some ths0)
    (ST_INIT_PRSV: forall fid st_tgt,
        Language.init lang code_t fid = Some st_tgt ->
        exists st_src, Language.init lang code_s fid = Some st_src),
  exists ths0', Threads.add_ths ths' tid fs code_s = Some ths0'.
Proof.
  induction fs; intros.
  - unfolds Threads.add_ths.
    inv THRD_ADD_TGT; eauto.
  - simpl in THRD_ADD_TGT.
    destruct (Threads.add_ths ths (Threads.tid_incr tid) fs code_t) eqn:Hthrd_add_ths; tryfalse.
    renames t to ths1, a to fid.
    unfold Threads.add_th in THRD_ADD_TGT.
    destruct (Language.init lang code_t fid) eqn:Hst_tgt_init; tryfalse.
    inv THRD_ADD_TGT.
    renames s to st_tgt.
    eapply ST_INIT_PRSV in Hst_tgt_init; eauto.
    destruct Hst_tgt_init as (st_src & Hst_src_init).
    simpl.
    eapply IHfs in Hthrd_add_ths; eauto.
    destruct Hthrd_add_ths as (ths0' & Hthrd_add_ths).
    rewrite Hthrd_add_ths.
    unfold Threads.add_th.
    rewrite Hst_src_init; eauto.
Qed.

(** construct source initial state from the target initial state *)
Lemma cons_source_init_from_target_init_program':
  forall fs (lang: language) (code_t code_s: Language.syntax lang)
    (index: Type) (index_order: index -> index -> Prop) ctid I inj lo ths_tgt ths_tgt' ths_src
    (THRD_INIT: forall fid st_tgt
                  (TGT_THRD_INIT: Language.init lang code_t fid = Some st_tgt),
        exists st_src, Language.init lang code_s fid = Some st_src /\
                  @local_sim_state index index_order lang I lo inj dset_init true
                                   (Thread.mk lang st_tgt Local.init TimeMap.bot Memory.init)
                                   (Thread.mk lang st_src Local.init TimeMap.bot Memory.init))
    (INIT_TGT_SRC: forall tid st_tgt lc_tgt
                     (IN_TGT_THRDS: IdentMap.find tid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
        exists st_src,
          lc_tgt = Local.init /\  
          IdentMap.find tid ths_src = Some (existT _ lang st_src, Local.init) /\
          @local_sim_state index index_order lang I lo inj dset_init true
                           (Thread.mk lang st_tgt Local.init TimeMap.bot Memory.init)
                           (Thread.mk lang st_src Local.init TimeMap.bot Memory.init))
    (INIT_SRC_TGT: forall tid
                     (IN_SRC_THRDS: IdentMap.mem tid ths_src = true),
        IdentMap.mem tid ths_tgt = true
    )
    (TGT_THRDS_INIT: Threads.add_ths ths_tgt ctid fs code_t = Some ths_tgt'), 
  exists ths_src',
    (* a source threads exists *)
    Threads.add_ths ths_src ctid fs code_s = Some ths_src' /\
    (* each target thread maps to a source thread and they can establish local sim *)
    (forall tid st_tgt lc_tgt
       (IN_TGT'_THRDS: IdentMap.find tid ths_tgt' = Some (existT _ lang st_tgt, lc_tgt)),
        exists st_src,
          lc_tgt = Local.init /\  
          IdentMap.find tid ths_src' = Some (existT _ lang st_src, Local.init) /\
          @local_sim_state index index_order lang I lo inj dset_init true
                           (Thread.mk lang st_tgt Local.init TimeMap.bot Memory.init)
                           (Thread.mk lang st_src Local.init TimeMap.bot Memory.init)) /\
    (* each source thread maps to a target thread *)
    (forall tid
       (IN_SRC'_THRDS: IdentMap.mem tid ths_src' = true),
        IdentMap.mem tid ths_tgt' = true).
Proof.
  induction fs; intros.
  - simpl in TGT_THRDS_INIT.
    inv TGT_THRDS_INIT; eauto.
    exists ths_src. simpl.
    split; eauto.
  - renames a to fid.
    simpl in TGT_THRDS_INIT.
    destruct (Threads.add_ths ths_tgt (Threads.tid_incr ctid) fs code_t) eqn:Hadd_tgt_ths.

    Focus 2. tryfalse.

    renames t to ths_tgt0.
    unfold Threads.add_th in TGT_THRDS_INIT.
    destruct (Language.init lang code_t fid) eqn:Hst_tgt_init.

    Focus 2. tryfalse.
    
    inv TGT_THRDS_INIT. renames s to st_tgt.
    lets Hadd_src_ths : Hadd_tgt_ths.
    eapply IHfs in Hadd_src_ths; eauto.
    destruct Hadd_src_ths as (ths_src' & H_add_src_ths & Htgt_2_src & Hsrc_2_tgt).
    simpl.
    lets Hst_src_init : Hst_tgt_init.
    eapply THRD_INIT in Hst_src_init; eauto.
    destruct Hst_src_init as (st_src & Hst_src_init & Hlocal_sim).
    rewrite H_add_src_ths.
    eexists. split.
    {
      unfold Threads.add_th.
      rewrite Hst_src_init; eauto.
    }
    split.
    {
      introv Htgt_th. 
      destruct (IdentSet.S'.eq_dec tid ctid); subst.
      {
        rewrite IdentMap.gss in Htgt_th.
        inv Htgt_th.
        eapply inj_pair2 in H0; subst.
        rewrite IdentMap.gss.
        exists st_src.
        split; eauto.
      }
      {
        rewrite IdentMap.gso in Htgt_th; eauto.
        lets Hsrc_th : Htgt_th.
        eapply Htgt_2_src in Hsrc_th; eauto.
        destruct Hsrc_th as (st_src0 & Hlc_tgt_init & Htid_src & Hlocal_sim2).
        exists st_src0.
        split; eauto.
        split; eauto.
        rewrite IdentMap.gso; eauto.
      }
    }
    {
      introv Hin_src_ths.
      destruct (IdentSet.S'.eq_dec tid ctid); subst.
      {
        rewrite IdentMap.Properties.F.add_eq_b; eauto.
      }
      {
        rewrite IdentMap.Facts.add_neq_b in Hin_src_ths; eauto.
        rewrite IdentMap.Facts.add_neq_b; eauto.
      }
    }
Qed. 

Lemma cons_source_init_from_target_init_program:
  forall fs (lang: language) (code_t code_s: Language.syntax lang)
    (index: Type) (index_order: index -> index -> Prop) ctid I inj lo c_tgt
    (THRD_INIT: forall fid st_tgt
                  (TGT_THRD_INIT: Language.init lang code_t fid = Some st_tgt),
        exists st_src, Language.init lang code_s fid = Some st_src /\
                  @local_sim_state index index_order lang I lo inj dset_init true
                                   (Thread.mk lang st_tgt Local.init TimeMap.bot Memory.init)
                                   (Thread.mk lang st_src Local.init TimeMap.bot Memory.init)) 
    (TGT_PROG_INIT: Configuration.init fs code_t ctid = Some c_tgt),
  exists c_src,
    (* a source initial configuration exists *)
    Configuration.init fs code_s ctid = Some c_src /\
    (* each target thread maps to a source thread and they can establish local sim *)
    (forall tid st_tgt lc_tgt
       (IN_TGT_THRDS: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)),
        exists st_src lc_src,
          lc_tgt = Local.init /\ lc_src = Local.init /\ 
          IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src) /\
          @local_sim_state index index_order lang I lo inj dset_init true
                           (Thread.mk lang st_tgt lc_tgt TimeMap.bot Memory.init)
                           (Thread.mk lang st_src lc_src TimeMap.bot Memory.init)) /\
    (* each source thread maps to a target thread *)
    (forall tid
       (IN_SRC_THRDS: IdentMap.mem tid (Configuration.threads c_src) = true),
        IdentMap.mem tid (Configuration.threads c_tgt) = true).
Proof.
  intros.
  unfold Configuration.init in TGT_PROG_INIT; subst; simpls.
  destruct (Threads.init fs code_t) eqn:Hadd_tgt_ths; tryfalse.
  inv TGT_PROG_INIT; simpl.
  renames t to tgt_ths.
  unfold Threads.init in Hadd_tgt_ths.
  eapply cons_source_init_from_target_init_program' in Hadd_tgt_ths; eauto.
  destruct Hadd_tgt_ths as (ths_src' & Hadd_src_ths & Htgt_2_src & Hsrc_2_tgt).

  unfold Configuration.init at 1.
  unfold Threads.init at 1.
  rewrite Hadd_src_ths; eauto.
  eexists. split; eauto.

  split.
  simpl.
  introv Hst_tgt_th.
  eapply Htgt_2_src in Hst_tgt_th; eauto.
  destruct Hst_tgt_th as (st_src & Hlc_tgt_init & Hst_src_th & Hlocal_sim); eauto.
  exists st_src Local.init.
  split; eauto.
  split; eauto.
  split; eauto.
  subst; eauto.

  simpl; eauto.

  introv Hcontr.
  rewrite IdentMap.Facts.empty_o in Hcontr; tryfalse.
Qed.

Lemma config_init_ths_sc_mem:
  forall lang fs (code: Language.syntax lang) ctid c,
    Configuration.init fs code ctid = Some c ->
    Threads.init fs code = Some (Configuration.threads c) /\
    Configuration.sc c = TimeMap.bot /\ Configuration.memory c = Memory.init.
Proof.
  intros.
  unfolds Configuration.init.
  destruct (Threads.init fs code) eqn:Hthrds_init; tryfalse.
  inv H; eauto.
Qed.

Lemma thread_add_same_lang':
  forall fs lang lang0 (code: Language.syntax lang) ths0 ths tid st lc ctid,
    Threads.add_ths ths0 ctid fs code = Some ths ->
    (forall tid lang1 st1 lc1,
        IdentMap.find tid ths0 = Some (existT _ lang1 st1, lc1) -> lang = lang1) ->
    IdentMap.find tid ths = Some (existT _ lang0 st, lc) ->
    lang = lang0.
Proof.
  induction fs; intros.
  - simpls. inv H. eauto.
  - renames a to fid.
    simpl in H.
    destruct (Threads.add_ths ths0 (Threads.tid_incr ctid) fs code) eqn:Hadd_ths; tryfalse.
    renames t to ths1.
    unfold Threads.add_th in H.
    destruct (Language.init lang code fid) eqn:Hst_init; tryfalse.
    inv H.
    destruct (Configuration.tid_eq_dec tid ctid); subst.
    {
      rewrite IdentMap.gss in H1.
      inv H1.
      eapply eq_sigT_fst in H3; eauto.
    }
    {
      rewrite IdentMap.gso in H1; eauto.
    }
Qed.
    
Lemma thread_init_same_lang:
  forall lang lang0 fs (code: Language.syntax lang) ths tid st lc,
    Threads.init fs code = Some ths ->
    IdentMap.find tid ths = Some (existT _ lang0 st, lc) ->
    lang = lang0.
Proof.
  intros.
  unfolds Threads.init.
  eapply thread_add_same_lang'; eauto.
  introv Hcontr.
  rewrite IdentMap.gempty in Hcontr; tryfalse.
Qed.

Lemma thread_init_lc_init':
  forall fs lang (code: Language.syntax lang) ths0 ths tid ctid st lc,
    Threads.add_ths ths0 ctid fs code = Some ths ->
    (forall tid lang1 st1 lc1,
        IdentMap.find tid ths0 = Some (existT _ lang1 st1, lc1) -> lc1 = Local.init) ->
    IdentMap.find tid ths = Some (existT _ lang st, lc) ->
    lc = Local.init.
Proof.  
  induction fs; intros.
  - simpls. inv H. eauto.
  - renames a to fid.
    simpl in H.
    destruct (Threads.add_ths ths0 (Threads.tid_incr ctid) fs code) eqn:Hadd_ths; tryfalse.
    renames t to ths_tgt.
    unfolds Threads.add_th.
    destruct (Language.init lang code fid) eqn:Hst_init; tryfalse.
    inv H.
    destruct (Configuration.tid_eq_dec tid ctid); subst.
    {
      rewrite IdentMap.gss in H1; eauto.
      inv H1; eauto.
    }
    {
      rewrite IdentMap.gso in H1; eauto.
    }
Qed.
    
Lemma thread_init_lc_init:
  forall lang fs (code: Language.syntax lang) ths tid st lc,
    Threads.init fs code = Some ths ->
    IdentMap.find tid ths = Some (existT _ lang st, lc) ->
    lc = Local.init.
Proof.
  intros.
  eapply thread_init_lc_init'; eauto.
  intros.
  rewrite IdentMap.gempty in H1; tryfalse.
Qed.
