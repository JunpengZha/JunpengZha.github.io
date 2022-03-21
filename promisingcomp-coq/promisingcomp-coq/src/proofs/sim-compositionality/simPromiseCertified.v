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
Require Import ww_RF.

Require Import LibTactics.
Require Import ConfigInitLemmas.
Require Import CompThreadSteps.
Require Import CompAuxDef.
Require Import WFConfig.

Require Import Reordering.
Require Import ps_to_np_thread.
Require Import np_to_ps_thread.
Require Import MsgMapping.
Require Import PromiseInjection.
Require Import ConsistentLemmas.
Require Import ConsistentProp.

Require Import MemoryProps.
Require Import Mem_at_eq_lemmas.
Require Import ps_to_np_thread.
Require Import np_to_ps_thread.

Require Import PromiseConsistent.
Require Import PromiseInjectionWeak.
Require Import promiseCertifiedAux.

Lemma memory_closed_addition_rsv
      mem mem'
      (MEM_CLOSED: Memory.closed mem)
      (MEM_LE: Memory.le mem mem')
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem' = Some (from, msg) ->
                            msg = Message.reserve):
  Memory.closed mem'.
Proof.
  inv MEM_CLOSED.
  econs; eauto. ii.
  destruct (Memory.get loc to mem) eqn:GET.
  destruct p.
  exploit MEM_LE; eauto. ii.
  rewrite MSG in x. inv x.
  eapply CLOSED in GET; eauto. des.
  split; eauto. split; eauto.
  eapply message_closed_rsv_concrete_prsv; eauto.
  exploit MORE_RESERVE; eauto. ii; subst.
  split; eauto. econs.
Qed.

Lemma aux_ww_race_to_thrd_ww_race
      lang lo pc st lc e'
      (AUX_WW_RACE: ~ aux_ww_race lo pc)
      (TH: IdentMap.find (Configuration.tid pc) (Configuration.threads pc) = Some (existT _ lang st, lc))
      (STEPS: rtc (@Thread.tau_step lang lo)
                  (@Thread.mk lang st lc (Configuration.sc pc) (Configuration.memory pc)) e')
      (CONFIG_WF: Configuration.wf pc):
  ~ @thrd_ww_race lang lo e'.
Proof.
  destruct pc; ss.
  ii.
  contradiction AUX_WW_RACE.
  inv H.
  assert (STEPS': rtc (Thread.all_step lo)
                      (Thread.mk lang st lc sc memory) (Thread.mk lang st' lc' sc' mem')).
  {
    eapply rtc_compose; [ | eapply STEPS0].
    eapply Thread_tau_steps_is_all_steps; eauto.
  }
  eapply wf_config_rtc_thread_steps_prsv in STEPS'; eauto.
  econs.
  eapply TH.
  eapply Thread_tau_steps_is_all_steps in STEPS.
  eapply rtc_compose; [eapply STEPS | eapply STEPS0].
  eauto.
  split. eauto. eauto.
  2: eauto.
  eapply wf_config_to_local_wf with (tid := tid) in STEPS'; eauto.
  rewrite IdentMap.gss; eauto.
Qed.
  
Lemma thrd_ww_race_cap_prsv':
  forall n lang lo st lc sc mem mem_c st' lc' sc' mem_c' stw loc val from to val' R' e_c'
    (STEPS_TO_RACE: rtcn (Thread.all_step lo) n
                         (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c'))
    (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) st' stw)
    (RACE_MSG: Memory.get loc to mem_c' = Some (from, Message.concrete val' R'))
    (NOT_PROM: Memory.get loc to (Local.promises lc') = None)
    (RACE: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (FULFILL: rtc (@Thread.tau_step lang lo) (Thread.mk lang st' lc' sc' mem_c') e_c')
    (BOT: Local.promises (Thread.local e_c') = Memory.bot)
    (MEM_LE: Memory.le mem mem_c)
    (MORE_RESERVE: 
       forall loc to from msg, Memory.get loc to mem = None ->
                          Memory.get loc to mem_c = Some (from, msg) ->
                          msg = Message.reserve)
    (PRM_LE: Memory.le (Local.promises lc) mem),
  exists mem' e',
    rtc (Thread.all_step lo)
        (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem') /\
    Memory.get loc to mem' = Some (from, Message.concrete val' R') /\
    rtc (@Thread.tau_step lang lo) (Thread.mk lang st' lc' sc' mem') e' /\
    Local.promises (Thread.local e') = Memory.bot.
Proof.
  induction n; ii.
  - inv STEPS_TO_RACE.
    eapply rtc_rtcn in FULFILL. des.
    exploit fulfill_cap; eauto. ii; des.
    do 2 eexists.
    split. eauto.
    split. eapply memory_additional_rsv_concrete_prsv; eauto.
    split. eapply x0. eauto.
  - inv STEPS_TO_RACE.
    destruct a2. 
    eapply all_step_cap_prsv in A12; eauto. des.
    eapply IHn in A23; eauto. des.
    do 2 eexists.
    split. eapply Relation_Operators.rt1n_trans; [eapply A12 | eapply A23].
    split. eauto. 
    split; eauto.
Qed.
    
Lemma thrd_ww_race_cap_prsv
      lang lo st lc sc mem mem_c
      (THRD_WW_RACE_CAP: @thrd_ww_race lang lo (Thread.mk lang st lc sc mem_c))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  @thrd_ww_race lang lo (Thread.mk lang st lc sc mem).
Proof.
  inv THRD_WW_RACE_CAP.
  eapply rtc_rtcn in STEPS. des.
  exploit thrd_ww_race_cap_prsv'; [eapply STEPS | eapply WRITE | eauto..]; eauto.
  ii; des.
  econs; eauto.
Qed.

(** local sim to promise certified preserving **)
Definition at_CAP_MEM (mem1 mem2: Memory.t) (lo: Ordering.LocOrdMap) : Memory.t :=
  fun loc => match (lo loc) with
           | Ordering.atomic => mem2 loc
           | Ordering.nonatomic => mem1 loc
           end.

Lemma at_CAP_MEM_mem_le
      mem mem1 mem2 lo
      (LE1: Memory.le mem mem1)
      (LE2: Memory.le mem mem2):
  Memory.le mem (at_CAP_MEM mem1 mem2 lo).
Proof.
  unfold Memory.le in *. ii.
  unfold Memory.get in *. unfold at_CAP_MEM.
  destruct (lo loc) eqn:Heqe; ss; eauto.
Qed.

Lemma Mem_at_eq_at_CAP_MEM
  lo mem mem0:
  Mem_at_eq lo mem (at_CAP_MEM mem0 mem lo).
Proof.
  unfold at_CAP_MEM.
  unfold Mem_at_eq. ii.
  unfold Mem_approxEq_loc.
  unfold Memory.get.
  split.
  - ii. split; ii. rewrite H; eauto.
    des. rewrite H in H0. eauto.
  - ii. split; ii.
    rewrite H. eauto.
    rewrite H in H0; eauto.
Qed.

Lemma Mem_at_eq_at_CAP_MEM2
      lo mem_tgt mem_src mem
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src):
  Mem_at_eq lo mem_tgt (at_CAP_MEM mem mem_src lo).
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii.
  unfold at_CAP_MEM.
  clear MEM_AT_EQ.
  unfold Mem_approxEq_loc in *.
  unfold Memory.get in *.
  rewrite H.
  eauto.
Qed.

Lemma memory_concrete_le_at_CAP_MEM
      mem mem1 mem2 lo
      (MEM_C_LE1: memory_concrete_le mem mem1)
      (MEM_C_LE2: memory_concrete_le mem mem2):
  memory_concrete_le mem (at_CAP_MEM mem1 mem2 lo).
Proof.
  unfold memory_concrete_le in *. ii.
  unfold Memory.get in *. unfold at_CAP_MEM.
  destruct (lo loc); eauto.
Qed.

Inductive rel_promises_TBOT {index: Type} (inj: Mapping) (pdset: @DelaySet index) (prm_src: Memory.t) :=
| rel_promises_intro
    (SOUND1: forall loc t i,
        dset_get loc t pdset = Some i ->
        (exists t' f' val' R',
            inj loc t = Some t' /\  Memory.get loc t' prm_src = Some (f', Message.concrete val' R')))
    (COMPLETE: forall loc f' t' val' R',
        Memory.get loc t' prm_src = Some (f', Message.concrete val' R') ->
        (exists t, inj loc t = Some t' /\ (exists i, dset_get loc t pdset = Some  i))). 

Definition finite_dset {index: Type} (dset: @DelaySet index)
           (ls: list (Loc.t * Time.t * index)) :=
  forall loc t i,
    dset_get loc t dset = Some i ->
    List.In (loc, t, i) ls.

Definition no_Dup_ls_dset {index: Type} (dset: @DelaySet index)
           (ls: list (Loc.t * Time.t * index)) :=
  forall loc t i,
    List.In (loc, t, i) ls ->
    dset_get loc t dset = Some i.

Definition no_Dup_ls {index: Type} (ls: list (Loc.t * Time.t * index)) :=
  forall loc t i j,
    List.In (loc, t, i) ls -> List.In (loc, t, j) ls ->
    i = j.
    
Lemma finite_promises_convert_to_list'
      promises index inj pdset
      (FINITE_MEM: Memory.finite promises)
      (REL_PROM_BOT: rel_promises_TBOT inj pdset promises)
      (MONOTONIC: monotonic_inj inj):
  exists ls, @finite_dset index pdset ls /\ @no_Dup_ls_dset index pdset ls.
Proof.
  unfold Memory.finite in *. des.
  generalize dependent promises.
  generalize dependent pdset.
  generalize dependent inj.
  generalize dependent index.
  induction dom; ii.
  - exists (@nil (Loc.t * Time.t * index)).
    split.
    {
      unfold finite_dset; ii.
      inv REL_PROM_BOT.
      eapply SOUND1 in H; eauto; des.
      eapply FINITE_MEM in H0; eauto.
    }
    {
      unfold no_Dup_ls_dset. ii. ss.
    }
  - destruct a. renames t to loc0.
    destruct (Memory.get loc0 t0 promises) eqn:H.
    {
      destruct p as (f0 & msg0).
      exploit Memory.remove_exists; [eapply H | eauto..]. ii; des.
      assert(forall loc from to msg,
                Memory.get loc to mem2 = Some (from, msg) ->
                List.In (loc, to) dom).
      {
        ii.
        erewrite Memory.remove_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss.
        eapply FINITE_MEM in H0; eauto.
        des; subst; eauto. inv H0; ss.
        eapply FINITE_MEM in H0; eauto.
        des; subst; eauto. inv H0; ss.
      }
      destruct msg0.
      {
        (* concrete message *)
        inv REL_PROM_BOT.
        exploit COMPLETE; [eapply H | eauto..]. ii; des.
        eapply IHdom with (pdset := dset_remove loc0 t pdset)
                          (inj := inj) in H0; eauto.
        des.
        exists ((loc0, t, i) :: ls).
        split.
        {
          unfold finite_dset in *. ii.
          destruct (dset_get loc t1 (dset_remove loc0 t pdset)) eqn:REMOVE_GET.
          {
            lets REMOVE_GET': REMOVE_GET.
            unfold dset_remove, dset_get in REMOVE_GET'.
            des_ifH REMOVE_GET'; ss.
            destruct (Loc.eq_dec t1 t); subst.
            rewrite DenseOrder.DOMap.grs in REMOVE_GET'; ss.
            rewrite DenseOrder.DOMap.gro in REMOVE_GET'; eauto.
            unfold dset_get in H2. rewrite H2 in REMOVE_GET'. inv REMOVE_GET'.
            eapply H0 in REMOVE_GET. eauto.
            unfold dset_get in H2; rewrite H2 in REMOVE_GET'. inv REMOVE_GET'.
            eapply H0 in REMOVE_GET; eauto.
          }
          {
            lets REMOVE_GET': REMOVE_GET.
            unfold dset_get, dset_remove in REMOVE_GET'.
            des_ifH REMOVE_GET'; ss; des; subst; ss.
            destruct (Loc.eq_dec t1 t); subst.
            rewrite x1 in H2. inv H2; eauto.
            rewrite DenseOrder.DOMap.gro in REMOVE_GET'; eauto.
            unfold dset_get in H2. rewrite H2 in REMOVE_GET'. inv REMOVE_GET'.
            unfold dset_get in H2. rewrite H2 in REMOVE_GET'. ss.
          }
        }
        {
          unfold no_Dup_ls_dset. ii; ss.
          des; subst; ss.
          inv H2; eauto. 
          unfold no_Dup_ls_dset in H1.
          eapply H1 in H2.
          clear - H2.
          unfold dset_get, dset_remove in *.
          des_ifH H2; subst; ss.
          destruct (Time.eq_dec t1 t); subst.
          rewrite DenseOrder.DOMap.grs in H2; ss.
          rewrite DenseOrder.DOMap.gro in H2; ss.
        }

        econs; ii.
        {
          lets REMOVE_GET: H1.
          unfold dset_get, dset_remove in REMOVE_GET.
          des_ifH REMOVE_GET.
          destruct (Loc.eq_dec t1 t); subst.
          rewrite DenseOrder.DOMap.grs in REMOVE_GET; ss.
          rewrite DenseOrder.DOMap.gro in REMOVE_GET; ss.
          unfold dset_get in *.
          eapply SOUND1 in REMOVE_GET; eauto. des.
          exists t' f' val' R'.
          split; eauto.
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          exploit monotonic_inj_implies_disj_mapping;
            [eapply MONOTONIC | eapply REMOVE_GET | eapply x | eapply n | eauto..]; ii; ss.
          unfold dset_get in *.
          eapply SOUND1 in REMOVE_GET; eauto. ii; des.
          exists t' f' val' R'.
          split; eauto.
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
        }
        {
          erewrite Memory.remove_o in H1; eauto.
          des_ifH H1; ss; des; subst; ss.
          exploit COMPLETE; [eapply H1 | eauto..]. ii; des.
          eexists. split; eauto.
          unfold dset_get, dset_remove.
          des_if; ss; des; subst; ss; eauto.
          exploit COMPLETE; [eapply H1 | eauto..]. ii; des.
          eexists. split; eauto.
          unfold dset_get, dset_remove; ss.
          des_if; ss; subst; ss; eauto.
          destruct (Loc.eq_dec t1 t); subst; eauto.
          rewrite x in x2. inv x2; ss.
          rewrite DenseOrder.DOMap.gro; eauto.
        }
      }
      {
        eapply IHdom; eauto.
        inv REL_PROM_BOT.
        econs; eauto; ii.
        eapply SOUND1 in H1; eauto. des.
        exists t' f' val' R'.
        split; eauto.
        erewrite Memory.remove_o; eauto.
        des_if; ss; des; subst; ss.
        rewrite H in H2; ss.
        eapply COMPLETE; eauto.
        erewrite Memory.remove_o in H1; eauto.
        des_ifH H1; ss; des; subst; ss; eauto.
      }
    }
    {
      assert(forall loc from to msg,
                Memory.get loc to promises = Some (from, msg) ->
                List.In (loc, to) dom).
      {
        ii. exploit FINITE_MEM; [eapply H0 | eauto..]. ii; ss.
        des; subst; ss. inv x.
        rewrite H in H0; ss.
      }
      eapply IHdom in H0; eauto.
    }
Qed.

Lemma finite_promises_convert_to_list
      promises index inj pdset
      (FINITE_MEM: Memory.finite promises)
      (REL_PROM_BOT: rel_promises_TBOT inj pdset promises)
      (MONOTONIC: monotonic_inj inj):
  exists ls, @finite_dset index pdset ls /\ @no_Dup_ls index ls.
Proof.
  exploit finite_promises_convert_to_list'; eauto.
  ii; des.
  eexists. split; eauto.
  unfold no_Dup_ls. ii.
  unfold no_Dup_ls_dset in x1.
  eapply x1 in H.
  eapply x1 in H0.
  rewrite H in H0. inv H0. eauto.
Qed.

Lemma dset_init_rel_promises_implies_only_reserve
      index inj (pdset: @DelaySet index) promises
      (REL_PROMISES_TBOT: rel_promises_TBOT inj pdset promises)
      (DSET_SUBSET: dset_subset pdset dset_init):
  <<RSV: forall loc to from msg,
      Memory.get loc to promises = Some (from, msg) ->
      msg = Message.reserve>>.
Proof.
  ii. destruct msg; eauto.
  inv REL_PROMISES_TBOT.
  exploit COMPLETE; eauto. ii; des.
  eapply DSET_SUBSET in x0.
  clear - x0. unfold dset_get, dset_init in *.
  rewrite DenseOrder.DOMap.gempty in x0; ss.
Qed.

Lemma only_reservations_fulfill
      lang lo st lc sc mem
      (ONLY_RSVs: forall loc to from msg,
          Memory.get loc to (Local.promises lc) = Some (from, msg) ->
          msg = Message.reserve)
      (MEM_FINITE: Memory.finite (Local.promises lc))
      (MEM_LE: Memory.le (Local.promises lc) mem):
  exists e_src',
    rtc (no_scfence_nprm_step lang lo) (Thread.mk lang st lc sc mem) e_src' /\
    Local.promises (Thread.local e_src') = Memory.bot.
Proof.
  unfold Memory.finite in MEM_FINITE. des.
  generalize dependent st.
  generalize dependent lc.
  generalize dependent sc.
  generalize dependent mem.
  induction dom; ss; ii.
  - destruct (classic (exists loc to from msg,
                          Memory.get loc to (Local.promises lc) = Some (from, msg))).
    {
      des. eapply MEM_FINITE in H; ss.
    }
    {
      assert(Local.promises lc = Memory.bot).
      {
        eapply Memory.ext; ii.
        rewrite Memory.bot_get.
        destruct (Memory.get loc ts (Local.promises lc)) eqn:Heqe; eauto.
        destruct p.
        contradiction H; eauto.
      }
      eexists. split; eauto.
    }
  - destruct a. rename t into loc0.
    destruct (Memory.get loc0 t0 (Local.promises lc)) eqn:GET.
    {
      destruct p.
      exploit ONLY_RSVs; [eapply GET | eauto..]. ii; subst.
      exploit Memory.remove_exists; [eapply GET | eauto..]. ii; des.
      exploit MEM_LE; [eapply GET | eauto..]. ii.
      exploit Memory.remove_exists; [eapply x | eauto..]. ii; des.
      assert(MEM_LE': 
              Memory.le (Local.promises (Local.mk (Local.tview lc) mem2)) mem0).
      {
        ss. eapply memory_remove_le_rsv_prsv.
        eapply MEM_LE. eapply x0. eapply x2.
      }
      eapply IHdom in MEM_LE'; eauto; ss.
      instantiate (1 := sc) in MEM_LE'.
      instantiate (1 := st) in MEM_LE'.
      destruct lc; ss. des.
      eexists. split.
      eapply Relation_Operators.rt1n_trans.
      eapply no_scfence_nprm_step_intro2; eauto.
      econs. econs; ss. eapply Memory.promise_cancel; eauto. ss.
      eapply MEM_LE'. eauto.
      ii.
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      ii.
      erewrite Memory.remove_o in GET0; eauto.
      des_ifH GET0; ss; des; subst; ss; eauto.
      exploit MEM_FINITE; [eapply GET0 | eauto..].
      ii; des; eauto.
      inv x1; ss.
      exploit MEM_FINITE; [eapply GET0 | eauto..].
      ii; des; eauto.
      inv x1; ss.
    }
    {
      eapply IHdom in MEM_LE; eauto.
      ii.
      exploit MEM_FINITE; [eapply GET0 | eauto..].
      ii; des; eauto.
      inv x. rewrite GET in GET0; ss.
    }
Qed.

Lemma write_not_abort_progress
      lang loc val st st' lc sc mem lo
      (NA_WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) st st')
      (ORD_MATCH: lo loc = Ordering.nonatomic)
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (BOT: Local.promises lc = Memory.bot):
  exists lc' mem' from to,
    Local.write_step lc sc mem loc from to val None None Ordering.plain lc' sc mem' Memory.op_kind_add lo.
Proof.
  assert (WRITE_ADD: exists mem',
             Memory.write (Local.promises lc) mem loc
                          (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem)) val
                          None (Local.promises lc) mem' Memory.op_kind_add).
  {
    eapply write_succeed_valid; eauto.
    inv LOCAL_WF; eauto.
    ii. inv COVER. inv ITV; ss.
    inv H; ss.
    exploit Memory.max_ts_spec; [eapply GET | eauto..]. ii; des.
    cut (Time.le t (Memory.max_ts loc mem)). ii.
    clear - FROM0 H. auto_solve_time_rel.
    clear - TO MAX. auto_solve_time_rel.
    ss. unfold TimeMap.bot; eauto.
    eapply Time.bot_spec; eauto.
    auto_solve_time_rel.
    ii. inv H. des.
    exploit Memory.max_ts_spec; [eapply GET | eauto..]. ii; des.
    exploit Memory.get_ts; [eapply GET | eauto..]. ii; des; subst.
    rewrite <- x1 in MAX.
    cut (Time.lt (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem))). ii.
    clear - MAX H.
    auto_solve_time_rel.
    auto_solve_time_rel.
    cut (Time.lt (Time.incr (Memory.max_ts loc mem)) (Memory.max_ts loc mem)).
    ii. clear - H.
    cut (Time.lt (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem))).
    ii. auto_solve_time_rel.
    ii. clear - x0. auto_solve_time_rel.
    auto_solve_time_rel.
    auto_solve_time_rel.
    econs; eauto.
  }
  des. eexists.
  exists mem' (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem)).
  econs; eauto.
  rewrite ORD_MATCH. ss.
  econs; eauto.
  inv LOCAL_WF.
  inv TVIEW_CLOSED.
  inv CUR.
  unfold Memory.closed_timemap in RLX.
  specialize (RLX loc). des.
  exploit Memory.max_ts_spec; [eapply RLX | eauto..]. ii; des.
  clear - MAX.
  cut (Time.lt (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem))). ii.
  auto_solve_time_rel.
  auto_solve_time_rel.
  ii; ss.
Qed.

Lemma state_in_not_abort_progress
      lang pe st st' lo lc mem sc
      (STATE_STEP: Language.step lang pe st st')
      (NA_STEP_T: state_in_step pe)
      (NOT_ABORT1: ~ (exists st' x o v,
                         (Language.step lang (ProgramEvent.read x v o) st st' \/
                          Language.step lang (ProgramEvent.write x v o) st st') /\
                         ~ Ordering.mem_ord_match o (lo x)))
      (NOT_ABORT2: ~ (exists st2 x vr vw or ow,
                         Language.step lang (ProgramEvent.update x vr vw or ow)
                                       st st2 /\ lo x = Ordering.nonatomic))
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (BOT: Local.promises lc = Memory.bot):
  (pe = ProgramEvent.silent) \/
  (exists releasedr loc to val lc' st2,
      Language.step lang (ProgramEvent.read loc val Ordering.plain) st st2 /\ 
      Local.read_step lc mem loc to val releasedr Ordering.plain lc' lo)
  \/
  (exists lc' mem' from to loc val st2,
      Language.step lang (ProgramEvent.write loc val Ordering.plain) st st2 /\
      Local.write_step lc sc mem loc from to val None None Ordering.plain lc' sc mem' Memory.op_kind_add lo).
Proof.
  destruct pe; ss; eauto.
  - (* non-atomic read *)
    right. left. destruct ord; ss.
    inv LOCAL_WF. inv TVIEW_CLOSED. inv CUR.
    unfold Memory.closed_timemap in PLN.
    specialize (PLN loc). des.
    assert (NA_LOC: lo loc = Ordering.nonatomic).
    {
      destruct (lo loc) eqn:TYPE_LOC; eauto.
      contradiction NOT_ABORT1.
      do 4 eexists. split. left. eauto.
      rewrite TYPE_LOC. ii; ss. des; ss.
    }
    exploit (Language.read_abitrary_1 lang); [eapply STATE_STEP | eauto..].
    instantiate (1 := val0).
    ii; des.
    {
      exists released loc (View.pln (TView.cur (Local.tview lc)) loc) val0. do 2 eexists.
      split. eapply x0.
      econs; eauto.
      rewrite NA_LOC. ss.
      econs; eauto.
      eapply Time.le_lteq; eauto.
      ii; ss.
    }
    {
      contradiction NOT_ABORT2.
      do 6 eexists.
      eauto.
    }
  - (* non atomic write *)
    destruct ord; ss.
    right. right.
    assert (NA_LOC: lo loc = Ordering.nonatomic).
    {
      destruct (lo loc) eqn:TYPE_LOC; eauto.
      contradiction NOT_ABORT1.
      do 4 eexists.
      split.
      right. eauto.
      rewrite TYPE_LOC. ii; ss. des; ss.
    }
    exploit write_not_abort_progress; eauto.
    instantiate (1 := sc). ii; des.
    exists lc' mem' from to loc val. exists st'.
    split; eauto.
Qed. 

Lemma state_in_not_abort_thread_step
      lang pe st st' lo lc mem sc
      (STATE_STEP: Language.step lang pe st st')
      (NA_STEP_T: state_in_step pe)
      (NOT_ABORT1: ~ (exists st' x o v,
                         (Language.step lang (ProgramEvent.read x v o) st st' \/
                          Language.step lang (ProgramEvent.write x v o) st st') /\
                         ~ Ordering.mem_ord_match o (lo x)))
      (NOT_ABORT2: ~ (exists st2 x vr vw or ow,
                         Language.step lang (ProgramEvent.update x vr vw or ow)
                                       st st2 /\ lo x = Ordering.nonatomic))
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (BOT: Local.promises lc = Memory.bot):
  exists te e', Thread.step lo true te (Thread.mk lang st lc sc mem) e' /\
           ThreadEvent.is_na_step te /\ (Local.promises lc) = (Local.promises (Thread.local e')).
Proof.
  exploit state_in_not_abort_progress; eauto. ii; des; subst.
  - do 2 eexists.
    split.
    eapply Thread.step_program.
    econs.
    Focus 2.
    eapply Local.step_silent. ss. eauto.
    eauto.
  - do 2 eexists.
    split.
    eapply Thread.step_program.
    econs.
    Focus 2.
    eapply Local.step_read. ss. eauto.
    ss. eauto.
    ss. split; eauto.
    inv x1; eauto.
  - do 2 eexists.
    split.
    eapply Thread.step_program.
    econs.
    Focus 2.
    eapply Local.step_write. ss. eauto.
    ss. eauto.
    split; eauto; ss.
    inv x1; ss. inv WRITE.
    inv PROMISE.
    eapply MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE].
Qed.
    
Fixpoint cons_ols {index: Type} (pdset: @DelaySet index) (ls: list (Loc.t * Time.t * index)) :=
  match ls with
  | nil => nil
  | (loc, to, i) :: ls' =>
    match dset_get loc to pdset with
    | None => None :: cons_ols pdset ls'
    | Some j => Some (loc, to, j) :: cons_ols pdset ls'
    end
  end.

Lemma na_steps_promises_fulfill':
  forall n lang e e' lo 
    (NA_STEPS: rtcn (@Thread.na_step lang lo) n e e'),
    (forall loc to from' val R,
        Memory.get loc to (Local.promises (Thread.local e')) = Some (from', Message.concrete val R) ->
        exists from, Memory.get loc to (Local.promises (Thread.local e)) = Some (from, Message.concrete val R)).
Proof.
  induction n; ii.
  - inv NA_STEPS; eauto.
  - inv NA_STEPS.
    eapply IHn in A23; eauto.
    clear - A12 A23.
    inv A12; eauto.
    + inv STEP; ss.
      inv LOCAL. inv LOCAL0; ss.
    + inv STEP; ss.
      inv LOCAL; ss.
      inv LOCAL0; ss.
      inv WRITE. des.
      inv PROMISE; ss.
      {
        (* add *)
        erewrite Memory.remove_o in A23; eauto.
        des_ifH A23; ss; eauto.
        erewrite Memory.add_o in A23; eauto.
        des_ifH A23; ss; eauto.
        des; subst; ss.
      }
      {
        (* split *)
        des; subst. inv RESERVE.
        erewrite Memory.remove_o in A23; eauto.
        des_ifH A23; ss; eauto.
        erewrite Memory.split_o in A23; eauto.
        des_ifH A23; ss; eauto.
        des; subst; ss; eauto.
        des_ifH A23; ss; eauto.
        des; subst; ss; eauto.
        inv A23.
        exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
        eauto.
      }
      {
        (* lower *)
        des; subst.
        erewrite Memory.remove_o in A23; eauto.
        des_ifH A23; eauto; ss.
        erewrite Memory.lower_o in A23; eauto.
        des_ifH A23; eauto; ss.
        des; subst; ss.
      }
    + des. inv STEP; ss. inv LOCAL. eauto.
Qed.
      
Lemma na_steps_promises_fulfill:
  forall lang e e' lo 
    (NA_STEPS: rtc (@Thread.na_step lang lo) e e'),
    (forall loc to from' val R,
        Memory.get loc to (Local.promises (Thread.local e')) = Some (from', Message.concrete val R) ->
        exists from, Memory.get loc to (Local.promises (Thread.local e)) = Some (from, Message.concrete val R)).
Proof.
  ii.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply na_steps_promises_fulfill'; eauto.
Qed.

Lemma pdset_less
      index (index_order: index -> index -> Prop) dset dset1 dset2 dset2' pdset pdset' te
      (DSET_SUBSET: dset_subset pdset dset)
      (DSET_UPD: dset_after_na_step te dset dset1)
      (DSET_SUBSET1: dset_subset dset2 dset1)
      (REDUCE_DSET: reduce_dset index_order dset2' dset2)
      (DSET_SUBSET': dset_subset pdset' dset2'):
  (forall loc to j,
      dset_get loc to pdset' = Some j ->
      dset_get loc to pdset = None \/
      (exists i, dset_get loc to pdset = Some i /\ index_order j i)).
Proof.
  ii.
  destruct (dset_get loc to pdset) eqn:DSET_GET; eauto.
  unfold dset_subset in *.
  exploit DSET_SUBSET; [eapply DSET_GET | eauto..]. ii.
  exploit DSET_SUBSET'; [eapply H | eauto..]. ii.
  inv REDUCE_DSET.
  exploit REDUCE; [eapply x0 | eauto..]. ii; des.
  right. eexists. split; eauto.
  inv DSET_UPD.
  - eapply DSET_SUBSET1 in x2.
    eapply dset_get_proper in x2. des.
    rewrite x in x2; ss.
    rewrite x in x2. inv x2; ss.
  - eapply DSET_SUBSET1 in x2.
    rewrite x in x2. inv x2. eauto.
Qed.

Lemma remove_none_empty_all_none:
  forall A ols (x: option A)
    (REMOVE_NONE: remove_none ols = nil)
    (LIST_IN: List.In x ols),
    x = None.
Proof.
  induction ols; ss. ii.
  destruct a; ss; eauto.
  des; eauto.
Qed.

Lemma remove_none_empty_implies_pdset_init:
  forall index ls (pdset: @DelaySet index)
    (REMOVE_NONE: remove_none (cons_ols pdset ls) = nil)
    (IN: forall loc t j, dset_get loc t pdset = Some j -> exists i, List.In (loc, t, i) ls),
    pdset = dset_init.
Proof.
  induction ls; ii; ss.
  - eapply functional_extensionality; eauto. ii.
    eapply DenseOrder.DOMap.eq_leibniz.
    unfold DenseOrder.DOMap.Equal. ii.
    unfold dset_init.
    rewrite DenseOrder.DOMap.gempty.
    destruct (DenseOrder.DOMap.find y (pdset x)) eqn:GET; eauto.
    eapply IN in GET. des. ss.
  - destruct a. destruct p.
    destruct (dset_get t t0 pdset) eqn:GET; ss.
    eapply IHls in REMOVE_NONE; eauto.
    ii.
    exploit IN; [eapply H | eauto..]. ii; des; eauto.
    inv x.
    rewrite GET in H. ss.
Qed.

Lemma lt_dset_cons_ols':
  forall index ls (pdset0: @DelaySet index) (index_order: index -> index -> Prop)
    (NO_DUP_DSET: no_Dup_ls ls)
    (PROM_LESS: forall loc t i j,
        List.In (loc, t, i) ls -> dset_get loc t pdset0 = Some j -> index_order j i)
    (NOT_NIL: ls <> nil),
    lt_dset index_order (cons_ols pdset0 ls) ls.
Proof.
  induction ls; ii; ss.
  destruct a. destruct p.
  destruct (dset_get t t0 pdset0) eqn:DSET_GET; ss; eauto.
  {
    lets PROM_LESS': PROM_LESS.
    specialize (PROM_LESS t t0 i i0).
    eapply PROM_LESS in DSET_GET; eauto.
    destruct ls.
    {
      ss.
      eapply lt_dset_some_nil; eauto.
    }
    {
      eapply lt_dset_some.
      eauto.
      eapply IHls; eauto.
      clear - NO_DUP_DSET.
      unfold no_Dup_ls in *. ii; ss.
      des; subst; ss.
      inv H0; eauto.
      specialize (NO_DUP_DSET loc t1 j i0).
      exploit NO_DUP_DSET; eauto.
      specialize (NO_DUP_DSET loc t1 i0 j).
      exploit NO_DUP_DSET; eauto.
      specialize (NO_DUP_DSET loc t1 i0 j).
      exploit NO_DUP_DSET; eauto.
      ii; ss.
    }
  }
  {
    destruct ls.
    ss. eapply lt_dset_none_nil.
    eapply lt_dset_none.
    eapply IHls; eauto.
    clear - NO_DUP_DSET.
    unfold no_Dup_ls in *; ii.
    ss. des; subst.
    inv H0. eauto.
    specialize (NO_DUP_DSET loc t1 j i0).
    exploit NO_DUP_DSET; eauto.
    specialize (NO_DUP_DSET loc t1 i0 j).
    exploit NO_DUP_DSET; eauto.
    specialize (NO_DUP_DSET loc t1 i0 j).
    exploit NO_DUP_DSET; eauto.
    ii; ss.
  }
Qed.
  
Lemma lt_dset_cons_ols:
  forall index ls (pdset pdset0: @DelaySet index) (index_order: index -> index -> Prop)
    (FINITE_DSET: finite_dset pdset ls)
    (NO_DUP_DSET: no_Dup_ls ls)
    (PROM_LESS: forall loc to j,
        dset_get loc to pdset0 = Some j ->
        (exists i, dset_get loc to pdset = Some i /\ index_order j i))
    (NOT_NIL: ls <> nil),
    lt_dset index_order (cons_ols pdset0 ls) ls.
Proof.
  ii.
  eapply lt_dset_cons_ols'; eauto.
  ii.
  exploit PROM_LESS; [eapply H0 | eauto..]. ii; des.
  unfold finite_dset in FINITE_DSET.
  exploit FINITE_DSET; [eapply x | eauto..]. ii.
  unfold no_Dup_ls in NO_DUP_DSET.
  exploit NO_DUP_DSET; [eapply H | eapply x1 | eauto..]. ii; subst.
  eauto.
Qed.

Lemma List_in_remove_none_cons_ols:
  forall index ls (pdset: @DelaySet index) loc to i
    (LIST_IN: List.In (loc, to, i) (remove_none (cons_ols pdset ls))),
    dset_get loc to pdset = Some i.
Proof.
  induction ls; ii; ss.
  destruct a. destruct p.
  destruct (dset_get t t0 pdset) eqn:GET; eauto.
  ss. des.
  inv LIST_IN; eauto.
  eauto.
Qed.

Lemma no_Dup_ls_remove_none_cons_ols
      index ls (pdset: @DelaySet index):
  no_Dup_ls (remove_none (cons_ols pdset ls)).
Proof.
  unfold no_Dup_ls. ii.
  eapply List_in_remove_none_cons_ols in H.
  eapply List_in_remove_none_cons_ols in H0.
  rewrite H in H0. inv H0; eauto.
Qed.

Lemma finite_dset_remove_none_cons_ols':
  forall index ls (pdset: @DelaySet index) loc to i
    (GET: dset_get loc to pdset = Some i),
    List.In (loc, to, i) (remove_none (cons_ols pdset ls)) \/ ~ (exists j, List.In (loc, to, j) ls).
Proof.
  induction ls; ii; ss.
  right. ii. des. ss.
  destruct a. destruct p.
  destruct (dset_get t t0 pdset) eqn:DSET_GET; ss.
  {
    exploit IHls; [eapply GET | eauto..]. ii; des.
    {
      left. right. eauto.
    }
    {
      destruct (Loc.eq_dec t loc); subst.
      destruct (Time.eq_dec to t0); subst.
      rewrite DSET_GET in GET. inv GET.
      left. eauto.
      right. ii. exploit x; eauto. des. inv H; ss.
      eauto.
      right.
      ii.
      contradiction x.
      des. inv H; ss. eauto.
    }
  }
  {
    exploit IHls; [eapply GET | eauto..]. ii; des; eauto.
    right. ii.
    contradiction x. des.
    inv H. rewrite GET in DSET_GET. ss.
    eauto.
  }
Qed.
  
Lemma finite_dset_remove_none_cons_ols
      index (pdset: @DelaySet index) ls
      (FINITE_DSET: forall loc to i,
          dset_get loc to pdset = Some i ->
          exists j, List.In (loc, to, j) ls):
  finite_dset pdset (remove_none (cons_ols pdset ls)).
Proof.
  unfold finite_dset. ii.
  exploit finite_dset_remove_none_cons_ols'; [eapply H | eauto..].
  instantiate (1 := ls).
  ii; des; eauto.
  contradiction x0; eauto.
Qed.
    
Lemma lsim_ensures_promise_fulfill_T_BOT'
      index (index_order: index -> index -> Prop) pdset dset ls lang I lo
      st_tgt lc_tgt sc_tgt mem_tgt
      st_src lc_src sc_src mem_src sc_srcc mem_srcc
      b inj
      (ACC_LT_DSET: Acc_lt_dset index_order ls)
      (REL_PROM_TBOT: rel_promises_TBOT inj pdset (Local.promises lc_src))
      (SUBSET: dset_subset pdset dset)
      (FINITE_DSET: finite_dset pdset ls)
      (NO_DUP_DSET: no_Dup_ls ls)
      (MONOTONIC_INJ: monotonic_inj inj)
      (WELL_FOUND: well_founded index_order)
      (T_BOT: Local.promises lc_tgt = Memory.bot)
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (SAFE_S: ~ (exists e_src', rtc (@Thread.tau_step lang lo)
                                (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                            Thread.is_abort e_src' lo))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem_src loc = mem_srcc loc)
      (LOCAL_WF_S: Local.wf lc_src mem_src)
      (MEM_CLOSED_S: Memory.closed mem_src)
      (MEM_LE_S: Memory.le mem_src mem_srcc)
      (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
      (MEM_CLOSED_T: Memory.closed mem_tgt):
  exists e_srcc',
    rtc (@Thread.nprm_step lang lo)
        (Thread.mk lang st_src lc_src sc_srcc mem_srcc) e_srcc' /\
      Local.promises (Thread.local e_srcc') = Memory.bot.
Proof.
  generalize dependent pdset.
  generalize dependent dset.
  generalize dependent st_tgt.
  generalize dependent lc_tgt.
  generalize dependent sc_tgt.
  generalize dependent mem_tgt.
  generalize dependent st_src.
  generalize dependent lc_src.
  generalize dependent sc_src.
  generalize dependent mem_src.
  generalize dependent mem_srcc.
  generalize dependent sc_srcc.
  generalize dependent b.
  induction ACC_LT_DSET; ii.
  assert(TGT_PROM_CONS: Local.promise_consistent lc_tgt).
  {
    unfold Local.promise_consistent. rewrite T_BOT. ii.
    rewrite Memory.bot_get in PROMISE. ss.
  }
  assert(NOT_ABORT_T: 
          ~ Thread.is_abort (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) lo).
  {
    introv NOT_ABORT_T.
    inv LOCAL_SIM; ss.
    contradiction SAFE_S.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
    eauto.
    clear THRD_STEP RELY_STEP THRD_DONE.
    exploit THRD_ABORT; eauto. ii; des.
    contradiction SAFE_S.
    eapply na_steps_is_tau_steps in x; eauto.
  }
  unfold Thread.is_abort in NOT_ABORT_T; ss.
  eapply not_and_or in NOT_ABORT_T.
  destruct NOT_ABORT_T as [NOT_ABORT_T | NOT_ABORT_T].
  {
    clear - T_BOT NOT_ABORT_T.
    contradiction NOT_ABORT_T.
    unfold Local.promise_consistent. ii.
    rewrite T_BOT in PROMISE.
    rewrite Memory.bot_get in PROMISE; ss.
  }
  eapply not_or_and in NOT_ABORT_T. des.
  eapply NNPP in NOT_ABORT_T. des.
  {
    (* target thread takes a step *)
    exploit state_in_or_out; eauto. instantiate (1 := e).
    introv AT_OR_NA_STEP.
    destruct AT_OR_NA_STEP as [AT_STEP_T | NA_STEP_T].
    {
      inv LOCAL_SIM; ss.
      contradiction SAFE_S.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; eauto.
      clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
      inv STEP_INV. 
      exploit DSET_EMP; eauto. ii; subst.
      assert(ONLY_RSVs: forall loc to from msg,
                Memory.get loc to (Local.promises lc_src) = Some (from, msg) ->
                msg = Message.reserve).
      {
        eapply dset_init_rel_promises_implies_only_reserve; eauto.
      }
      exploit only_reservations_fulfill; eauto.
      Focus 3. ii. des. eexists. split. 2: eapply x1.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.      
      inv LOCAL_WF_S; ss; eauto.
      inv LOCAL_WF_S; ss; eauto.      
      clear - MEM_LE_S PROMISES.
      unfold Memory.le in *; ii.
      eapply PROMISES in LHS. eauto.
    }
    {
      eapply not_or_and in NOT_ABORT_T0. des.
      exploit state_in_not_abort_thread_step; eauto.
      instantiate (1 := sc_tgt).
      introv TGT_THREAD_STEP.
      destruct TGT_THREAD_STEP as (te & e_tgt & TGT_THREAD_STEP & IS_NA_STEP & PROM_EQ).
      destruct e_tgt.
      renames state to st_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
      inv LOCAL_SIM; ss.
      (* abort *)
      contradiction SAFE_S.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      eexists.
      split. eapply NP_STEPS. eauto.
      (* not abort *)
      clear RELY_STEP THRD_DONE THRD_ABORT.
      assert (TGT_NA_STEP: @Thread.na_step lang lo
                                           (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                           (Thread.mk lang st_tgt' lc_tgt' sc_tgt' mem_tgt')).
      {
        clear - TGT_THREAD_STEP IS_NA_STEP.
        destruct te; ss.
        inv TGT_THREAD_STEP. inv STEP.
        eapply Thread.na_tau_step_intro; eauto.
        destruct ord; ss.
        inv TGT_THREAD_STEP. inv STEP.
        eapply Thread.na_plain_read_step_intro; eauto.
        destruct ord; ss.
        inv TGT_THREAD_STEP. inv STEP.
        eapply Thread.na_plain_write_step_intro; eauto.
      }
      assert (TGT_PROM_CONS': Local.promise_consistent lc_tgt').
      {
        unfold Local.promise_consistent.
        rewrite <- PROM_EQ. rewrite T_BOT.
        ii. rewrite Memory.bot_get in PROMISE; ss.
      }
      exploit THRD_STEP.
      eapply TGT_THREAD_STEP. 
      ii. clear THRD_STEP. des. clear x x1 x2.
      exploit x0; eauto. clear x0. ii; des.
      lets LOCAL_SIM_STATE': x2.
      inv LOCAL_SIM_STATE'; ss.
      contradiction SAFE_S.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      eapply na_steps_dset_to_NPThread_tau_steps in x0.
      instantiate (1 := true) in x0. des.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in x0; ss.
      exists e_src. split; eauto.
      eapply rtc_compose; [eapply x0 | eapply NP_STEPS].
      clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
      inv STEP_INV0. des.
      ss. rewrite <- PROM_EQ in REL_PROMISES0. rewrite T_BOT in REL_PROMISES0.
      assert(REL_PROM_TBOT': rel_promises_TBOT inj pdset0 (Local.promises lc_src0)).
      {
        clear - REL_PROMISES0. inv REL_PROMISES0.
        econs; eauto. ii.
        eapply COMPLETE in H; eauto. des; eauto.
        rewrite Memory.bot_get in H0; ss.
      }
      assert(LESS_PROMISES: forall loc from0 to val R,
                Memory.get loc to (Local.promises lc_src0) = Some (from0, Message.concrete val R) ->
                exists from, Memory.get loc to (Local.promises lc_src) = Some (from, Message.concrete val R)).
      {
        clear - x0.
        eapply na_steps_dset_to_Thread_na_steps in x0. ii.
        eapply na_steps_promises_fulfill in x0; ss; eauto.
      } 
      assert(PDSET_LESS: 
               forall loc to j,
                 dset_get loc to pdset0 = Some j ->
                 (dset_get loc to pdset = None \/ (exists i, dset_get loc to pdset = Some i /\ index_order j i))).
      {
        ii. eapply na_steps_dset_subset in x0.
        exploit pdset_less;
          [eapply SUBSET | eapply x | eapply x0 | eapply x1 | eapply REL_PROMISES | eauto..]; eauto.
      }
      assert(PDSET_LESS0: 
               forall loc to j,
                 dset_get loc to pdset0 = Some j -> exists i, dset_get loc to pdset = Some i /\ index_order j i).
      {
        clear - REL_PROM_TBOT REL_PROM_TBOT' LESS_PROMISES PDSET_LESS MONOTONIC_INJ. ii.
        exploit PDSET_LESS; [eapply H | eauto..]. ii; des; ss; eauto.
        inv REL_PROM_TBOT. inv REL_PROM_TBOT'.
        eapply SOUND0 in H. des.
        eapply LESS_PROMISES in H0. des.
        eapply COMPLETE in H0. des.
        destruct (Time.eq_dec to t); subst; eauto.
        rewrite H1 in x. ss.
        exploit monotonic_inj_implies_disj_mapping;
          [eapply MONOTONIC_INJ | eapply H | eapply H0 | eapply n | eauto..].
        ii; ss.
      }
      eapply na_steps_dset_to_Thread_na_steps in x0.
      lets NA_STEPS_S: x0.
      eapply na_steps_na_loc_same_prsv in x0; eauto.
      des.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto].
      ii.
      eapply no_scfence_nprm_steps_not_care_sc with (sc0 := sc_srcc) in x3.
      destruct (remove_none (cons_ols pdset0 ls)) eqn: REMOVE_NONE.
      {
        assert(PDSET_EMPTY: pdset0 = dset_init).
        {
          eapply remove_none_empty_implies_pdset_init; eauto.
          ii. clear - FINITE_DSET REL_PROM_TBOT REL_PROM_TBOT' H0 LESS_PROMISES MONOTONIC_INJ.
          inv REL_PROM_TBOT. inv REL_PROM_TBOT'.
          exploit SOUND0; [eapply H0 | eauto..]. ii; des.
          exploit LESS_PROMISES; [eapply x0 | eauto..]. ii; des.
          exploit COMPLETE; [eapply x1 | eauto..]. ii; des.
          destruct (Time.eq_dec t t0); subst.
          unfold finite_dset in FINITE_DSET.
          eapply FINITE_DSET in x3; eauto.
          exploit monotonic_inj_implies_disj_mapping;
            [eapply MONOTONIC_INJ | eapply x | eapply x2 | eauto..]. ii; ss.
        }
        subst.
        assert(ONLY_RSVs: forall loc to from msg,
                  Memory.get loc to (Local.promises lc_src0) = Some (from, msg) ->
                  msg = Message.reserve).
        {
          eapply dset_init_rel_promises_implies_only_reserve; eauto.
          unfold dset_subset. ii; eauto.
        }
        assert(LOCAL_WF_T': Local.wf lc_src0 mem_src0).
        {
          eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
          eapply rtc_rtcn in NA_STEPS_S. des.
          eapply no_scfence_nprm_steps_prsv_local_wf in NA_STEPS_S; eauto.
        }
        eapply only_reservations_fulfill in ONLY_RSVs.
        destruct ONLY_RSVs as (e_src' & NPRM_STEPS & T_BOT').
        instantiate (1 := mem_c') in NPRM_STEPS.
        instantiate (1 := sc_srcc) in NPRM_STEPS.
        instantiate (1 := st_src0) in NPRM_STEPS.
        instantiate (1 := lo) in NPRM_STEPS.           
        exists e_src'.
        split; eauto.
        eapply rtc_compose. 
        eapply no_scfence_nprm_steps_is_nprm_steps. eapply x3.
        eapply no_scfence_nprm_steps_is_nprm_steps. eapply NPRM_STEPS.
        inv LOCAL_WF_T'; eauto.
        inv LOCAL_WF_T'. ii.
        exploit PROMISES; eauto. ii.
        destruct (lo loc) eqn: AT_NA_LOC.
        eapply na_steps_atomic_loc_stable_rtc with (loc := loc) in NA_STEPS_S; eauto.
        eapply na_steps_atomic_loc_stable_rtc with (loc := loc) in NA_STEP_CAP; eauto.
        unfold Memory.get in *.
        rewrite <- NA_STEP_CAP. rewrite <- NA_STEPS_S in x0.
        eauto.
        unfold Memory.get in *.
        erewrite <- NA_SAME_PRSV; eauto.
      }
      {
        specialize (H (cons_ols pdset0 ls) (remove_none (cons_ols pdset0 ls))).
        exploit H.
        eapply lt_dset_cons_ols; eauto.
        ii. subst. ss.
        eauto.
        rewrite REMOVE_NONE. ii; ss.
        eapply no_Dup_ls_remove_none_cons_ols.
        eapply NA_SAME_PRSV.
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply rtc_rtcn in NA_STEPS_S. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in NA_STEPS_S; ss.
        ii.
        destruct (lo loc) eqn:NA_AT_LOC.
        eapply na_steps_atomic_loc_stable_rtc with (loc := loc) in NA_STEPS_S; eauto.
        eapply na_steps_atomic_loc_stable_rtc with (loc := loc) in NA_STEP_CAP; eauto.
        unfold Memory.get in *.
        rewrite <- NA_STEPS_S in LHS; eauto.
        rewrite <- NA_STEP_CAP. eauto.
        unfold Memory.get in *.
        rewrite <- NA_SAME_PRSV; eauto.
        instantiate (1 := lc_src0).
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply rtc_rtcn in NA_STEPS_S. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in NA_STEPS_S; eauto.
        instantiate (2 := st_src0).
        instantiate (1 := sc_src0).
        clear - SAFE_S NA_STEPS_S.
        ii; des.
        contradiction SAFE_S.
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply no_scfence_nprm_steps_is_nprm_steps in NA_STEPS_S.
        eapply Thread_nprm_step_is_tau_step in NA_STEPS_S.
        exists e_src'. split; eauto.
        eapply rtc_compose; [eapply NA_STEPS_S | eapply H].
        instantiate (1 := mem_tgt').
        eapply Thread_na_step_is_no_scfence_nprm_step in TGT_NA_STEP.
        eapply no_scfence_nprm_step_prsv_memory_closed in TGT_NA_STEP; ss.
        instantiate (1 := lc_tgt').
        rewrite <- PROM_EQ. eauto.
        eapply Thread_na_step_is_no_scfence_nprm_step in TGT_NA_STEP.
        eapply no_scfence_nprm_step_prsv_local_wf in TGT_NA_STEP; ss.
        eauto.
        instantiate (1 := pdset0). eauto.
        eauto.
        eapply finite_dset_remove_none_cons_ols; eauto.
        clear - PDSET_LESS0 FINITE_DSET.
        ii.
        unfold finite_dset in FINITE_DSET.
        eapply PDSET_LESS0 in H. des.
        eapply FINITE_DSET in H; eauto.
        instantiate (1 := sc_srcc). ii; des.
        exists e_srcc'.
        split; eauto.
        eapply no_scfence_nprm_steps_is_nprm_steps in x3.
        eapply rtc_compose; [eapply x3 | eapply x0].
      }
    }
  }
  {
    (* target thread is done *)
    inv LOCAL_SIM; ss.
    contradiction SAFE_S.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss. eauto.
    clear THRD_STEP RELY_STEP THRD_ABORT.
    exploit THRD_DONE; eauto. ii; des. inv x0.
    eapply na_steps_dset_to_Thread_na_steps in x.
    destruct e_src; ss.
    exploit na_steps_na_loc_same_prsv; [eapply x | eauto..]. ii; des.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply x | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S_CAP.
    eapply no_scfence_nprm_steps_not_care_sc with (sc0 := sc_srcc) in NO_SC_FENCE_NPRM_STEP_S_CAP.
    eexists. split.
    eapply no_scfence_nprm_steps_is_nprm_steps. eapply NO_SC_FENCE_NPRM_STEP_S_CAP.
    ss.
  }
Qed.
  
Lemma lsim_ensures_promise_fulfill_T_BOT
      index index_order dset lang I lo
      st_tgt lc_tgt sc_tgt mem_tgt
      st_src lc_src sc_src mem_src sc_srcc mem_srcc
      b inj
      (MONOTONIC_INJ: monotonic_inj inj)
      (WELL_FOUND: well_founded index_order)
      (T_BOT: Local.promises lc_tgt = Memory.bot)
      (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
      (MEM_CLOSED_T: Memory.closed mem_tgt)
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (SAFE_S: ~ (exists e_src', rtc (@Thread.tau_step lang lo)
                                (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                            Thread.is_abort e_src' lo))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem_src loc = mem_srcc loc)
      (LOCAL_WF_S: Local.wf lc_src mem_src)
      (MEM_CLOSED_S: Memory.closed mem_src)
      (MEM_LE_SRC: Memory.le mem_src mem_srcc):
  exists e_srcc',
    rtc (@Thread.nprm_step lang lo)
        (Thread.mk lang st_src lc_src sc_srcc mem_srcc) e_srcc' /\
    Local.promises (Thread.local e_srcc') = Memory.bot.
Proof.
  assert (TGT_PROM_CONS: Local.promise_consistent lc_tgt).
  {
    unfold Local.promise_consistent.
    rewrite T_BOT. ii. rewrite Memory.bot_get in PROMISE. ss.
  }
  inv LOCAL_SIM; ss.
  (* source abort *)
  contradiction SAFE_S.
  eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss. eauto.
  (* source not abort *)
  assert (PSET: exists pdset, dset_subset pdset dset /\ rel_promises_TBOT inj pdset (Local.promises lc_src)).
  {
    clear - STEP_INV T_BOT. inv STEP_INV. des.
    exists pdset. split; eauto.
    inv REL_PROMISES0. econs; eauto.
    ii.
    exploit COMPLETE; [eapply H | eauto..]. ii; des; eauto.
    rewrite T_BOT in x0.
    rewrite Memory.bot_get in x0; ss.
  }
  des.
  exploit finite_promises_convert_to_list; eauto.
  inv LOCAL_WF_S; eauto. ii; des.
  exploit well_founded_index_implies_Acc_lt_dset; eauto.
  instantiate (1 := ls). introv ACC_LT_DSET.
  eapply lsim_ensures_promise_fulfill_T_BOT'; eauto.
  eapply local_sim_state_step_intro; eauto.
Qed.
  
Lemma lsim_ensures_promise_fulfill:
      forall n lang index index_order I lo
        st_tgt lc_tgt sc_tgt mem_tgt sc_tgtc mem_tgtc e_tgt'
        st_src lc_src sc_src mem_src sc_srcc mem_srcc
        b dset inj
        (WELL_FOUND: well_founded index_order)
        (MONOTONIC_INJ: monotonic_inj inj)
        (WF_I: wf_I I)
        (FULFILL_TGT: rtcn (@Thread.nprm_step lang lo) n
                           (@Thread.mk lang st_tgt lc_tgt sc_tgtc mem_tgtc) e_tgt')
        (T_BOT: Local.promises (Thread.local e_tgt') = Memory.bot)
        (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
        (MEM_CLOSED_T: Memory.closed mem_tgt)
        (MEM_LE: Memory.le mem_tgt mem_tgtc)
        (MORE_RESERVE: 
           forall loc to from msg, Memory.get loc to mem_tgt = None ->
                              Memory.get loc to mem_tgtc = Some (from, msg) ->
                              msg = Message.reserve)
        (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                     (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                     (Thread.mk lang st_src lc_src sc_src mem_src))
        (SAFE_S: ~ (exists e_src', rtc (@Thread.tau_step lang lo)
                                  (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                              Thread.is_abort e_src' lo))
        (MEM_LE_SRC: Memory.le mem_src mem_srcc)
        (MORE_RESERVE_SRC: 
           forall loc to from msg, Memory.get loc to mem_src = None ->
                              Memory.get loc to mem_srcc = Some (from, msg) ->
                              msg = Message.reserve)
        (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem_src loc = mem_srcc loc)
        (AT_COVER: forall loc, lo loc = Ordering.atomic ->
                          (forall from to, Memory.get loc to mem_srcc = Some (from, Message.reserve) ->
                                      Memory.get loc to mem_tgtc = Some (from, Message.reserve)))
        (LOCAL_WF_S: Local.wf lc_src mem_src)
        (MEM_CLOSED_S: Memory.closed mem_src),
      exists e_srcc',
        rtc (@Thread.tau_step lang lo)
            (Thread.mk lang st_src lc_src sc_srcc mem_srcc) e_srcc' /\
        Local.promises (Thread.local e_srcc') = Memory.bot.
Proof.
  induction n; ii.
  - (* target has fulfill all its promises *)
    inv FULFILL_TGT; ss.
    exploit lsim_ensures_promise_fulfill_T_BOT; eauto. ii; des.
    eapply Thread_nprm_step_is_tau_step in x0.
    eexists. split; eauto.
  - (* target does not fulfill all its promises *)
    assert (LOCAL_WF_TGT_C: Local.wf lc_tgt mem_tgtc).
    {
      eapply memory_concrete_le_local_wf; eauto; ss.
      inv LOCAL_WF_T. clear - PROMISES MEM_LE.
      unfold Memory.le in *. ii.
      eapply PROMISES in LHS. eapply MEM_LE in LHS; eauto.
    }
    assert (CLOSED_TGT_C: Memory.closed mem_tgtc).
    {
      eapply memory_closed_addition_rsv with (mem := mem_tgt); eauto.
    }
    
    assert (TGT_PROMS_CONS: Local.promise_consistent lc_tgt).
    {
      eapply rtcn_rtc in FULFILL_TGT. 
      eapply nprm_steps_to_bot_promise_consistent in FULFILL_TGT; eauto. 
    }
    inv FULFILL_TGT. destruct a2.
    inv A12.
    + (* program step *)
      destruct (classic (exists ordr, e = ThreadEvent.fence ordr Ordering.seqcst)).
      {
        (* sc fence step *)
        clear LOCAL_WF_TGT_C CLOSED_TGT_C.
        des; subst. inv PROG. inv LOCAL. inv LOCAL0; ss.
        exploit PROMISES; eauto. ii.
        exploit lsim_ensures_promise_fulfill_T_BOT; eauto. ii; des.
        eapply Thread_nprm_step_is_tau_step in x1.
        eexists. split; eauto.
      }
      { 
        (* not sc fence step *)
        assert (LOCAL_WF_T': Local.wf local memory).
        {
          exploit no_scfence_nprm_step_prsv_local_wf.
          eapply no_scfence_nprm_step_intro1. eapply PROG. eauto. eauto.
          ss. ss. ss.
        }
        assert (MEM_CLOSED_T': Memory.closed memory).
        {
          exploit no_scfence_nprm_step_prsv_memory_closed.
          eapply no_scfence_nprm_step_intro1. eapply PROG. eauto. eauto.
          ss. ss. ss.
        }
        assert (PROM_CONS_T': Local.promise_consistent local).
        {
          eapply rtcn_rtc in A23. 
          eapply nprm_steps_to_bot_promise_consistent in A23; eauto.
        }
        exploit tgt_no_scfence_program_step_cap_sim;
          [eapply PROG | eapply TAU | eapply LOCAL_WF_T | eapply MEM_CLOSED_T | eapply H | eapply LOCAL_SIM | eauto..].
        instantiate (1 := sc_srcc). instantiate (2 := mem_srcc).
        ii; des.
        exploit x0; eauto. clear x0.
        ii; des.    
        eapply IHn with (st_src := st_src') (lc_src := lc_src')
                        (sc_src := sc_src) (mem_src := mem_src')
                        (inj := inj') (mem_tgt := mem_tgt') in A23; eauto.
        des. 
        exists e_srcc'. split; eauto.
        eapply Thread_nprm_step_is_tau_step in S_STEPS'.
        eapply Thread_nprm_step_is_tau_step in S_STEPS.
        eapply rtc_compose. eapply S_STEPS. eapply A23.
        clear - SAFE_S S_STEPS'.
        introv ABORT. destruct ABORT as (e_src' & ABORT). des.
        contradiction SAFE_S. 
        eapply Thread_nprm_step_is_tau_step in S_STEPS'.
        eexists. split.
        eapply rtc_compose; [eapply S_STEPS' | eapply ABORT | eauto..].
        eauto.
      }
    + (* promise free promise step *)
      assert (LOCAL_WF_T': Local.wf local memory).
      {
        exploit no_scfence_nprm_step_prsv_local_wf.
        eapply no_scfence_nprm_step_intro2. eapply PF. eauto. eauto. ss.
      }
      assert (MEM_CLOSED_T': Memory.closed memory).
      {
        exploit no_scfence_nprm_step_prsv_memory_closed.
        eapply no_scfence_nprm_step_intro2. eapply PF. eauto. eauto. eauto.
      }
      assert (PROM_CONS_T': Local.promise_consistent local).
      {
        eapply rtcn_rtc in A23. 
        eapply nprm_steps_to_bot_promise_consistent in A23; eauto.
      }
      exploit tgt_pf_promise_step_cap_sim;
        [eapply PF | eapply LOCAL_WF_T | eapply MEM_CLOSED_T | eapply LOCAL_SIM | eauto..]; eauto.
      ii; des.
      exploit x0; eauto.
      clear x0. instantiate (1 := sc_srcc). ii; des.
      eapply IHn with (st_src := st_src') (lc_src := lc_src')
                        (sc_src := sc_src) (mem_src := mem_src') in A23; eauto.
      des.
      exists e_srcc'. split; eauto.
      eapply Thread_nprm_step_is_tau_step in S_STEPS'.
      eapply Thread_nprm_step_is_tau_step in S_STEPS.
      eapply rtc_compose. eapply S_STEPS. eapply A23.
      clear - SAFE_S S_STEPS'.
      introv ABORT. destruct ABORT as (e_src' & ABORT). des.
      contradiction SAFE_S. 
      eapply Thread_nprm_step_is_tau_step in S_STEPS'.
      eexists. split.
      eapply rtc_compose; [eapply S_STEPS' | eapply ABORT | eauto..].
      eauto.
      Unshelve. exact lo.
      Unshelve. exact lo.
Qed.
      
Lemma fulfill_ww_race_free_implies_promise_certified
      lang lo st lc sc mem sc_c mem_c e' mem_cap
      (FULFILL: rtc (@Thread.nprm_step lang lo)
                    (Thread.mk lang st lc sc_c mem_c) e')
      (BOT: Local.promises (Thread.local e') = Memory.bot)
      (NO_WW_RACE: ~ @thrd_ww_race lang lo (@Thread.mk lang st lc sc mem_c))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc)
      (CAP_MEM: Memory.cap mem mem_cap)
      (AT_COVER: forall loc, lo loc = Ordering.atomic -> mem_cap loc = mem_c loc)
      (LOCAL_WF1: Local.wf lc mem)
      (LOCAL_WF2: Local.wf lc mem_c)
      (CLOSED_MEM1: Memory.closed mem)
      (CLOSED_MEM2: Memory.closed mem_c):
  Thread.consistent_nprm (Thread.mk lang st lc sc mem) lo. 
Proof.
  unfold Thread.consistent_nprm; ss. ii.
  exploit Memory.cap_inj; [eapply CAP_MEM | eapply CAP | eauto..]. ii. subst mem1.
  eapply rtc_rtcn in FULFILL. des.
  assert(PROMISE_CONSISTENT: Local.promise_consistent lc).
  {
    eapply promise_consistent_prsv_thread_nprm_step in FULFILL; eauto.
    unfold Local.promise_consistent. ii.
    rewrite BOT in PROMISE.
    rewrite Memory.bot_get in PROMISE. ss.
  }
  assert(WF_CONCRETE_PROM: forall loc from to val R,
            Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) ->
            Time.lt from to).
  {
    ii.
    unfold Local.promise_consistent in PROMISE_CONSISTENT.
    exploit PROMISE_CONSISTENT; eauto.
    introv LT.
    exploit Memory.get_ts; eauto. ii; des; subst.
    clear - LT. auto_solve_time_rel.
    eauto.
  }
  assert(LOCAL_WF_CAP: Local.wf lc mem_cap).
  {
    eapply Local.cap_wf; eauto.
  }
  assert(MEM_CLOSED_CAP: Memory.closed mem_cap).
  {
    eapply Memory.cap_closed; eauto.
  }
  destruct e'.
  eapply no_na_race_consistent_construction
    with (inj := spec_inj mem_c) (mem' := mem_cap) in FULFILL; eauto; ss. 
  {
    instantiate (1 := sc1) in FULFILL.
    destruct FULFILL as (st' & lc' & sc' & mem' & CAP_STEPS & CAP_BOT).
    exists (Thread.mk lang st' lc' sc' mem'). ss.
  } 
  {
    ii. unfold spec_inj in *.
    destruct (Memory.get loc t mem_c); ss. destruct p. destruct t1; ss.
    inv H0. eauto.
  }
  {
    ii.
    contradiction H0. clear H0.
    inv H1. inv ITV; ss.
    unfold Mem_at_eq in AT_COVER.
    assert (Memory.get loc to mem_c = Some (from, msg)).
    {
      unfold Memory.get in *.
      rewrite <- AT_COVER; eauto.
    }
    econs; eauto.
    econs; eauto.
  }
  {
    instantiate (2 := sc1).
    instantiate (1 := fun loc => Memory.max_ts loc mem_cap).
    ss. ii.
    unfold Memory.max_concrete_timemap in SC_MAX.
    specialize (SC_MAX loc).
    inv MEM_CLOSED_CAP. unfold Memory.inhabited in INHABITED.
    specialize (INHABITED loc).
    exploit Memory.max_concrete_ts_spec; eauto. ii; des.
    exploit Memory.cap_inv_concrete; [eapply CLOSED_MEM1 | eapply CAP | eapply GET | eauto..].
    ii.
    assert (GET_c: Memory.get loc (sc1 loc) mem_c = Some (from, Message.concrete val' released')).
    {
      unfold Memory.get in *.
      rewrite <- NA_SAME; eauto.
    }
    eexists.
    split.
    unfold spec_inj. rewrite GET_c. eauto.
    exploit Memory.max_ts_spec; [eapply GET | eauto..]. ii; des; eauto.
  }
  {
    econs; eauto.
    ii.
    exists t f R.
    split; eauto.
    unfold spec_inj. rewrite MSG; eauto.
    split. eapply spec_inj_optviewinj.
    destruct (lo loc) eqn: AT_NA_LOC.
    {
      (* atomic loc *)
      unfold Memory.get in *.
      rewrite AT_COVER; eauto.
    }
    {
      (* non-atomic loc *)
      assert (GET: Memory.get loc t mem = Some (f, Message.concrete val R)).
      {
        unfold Memory.get in *.
        rewrite NA_SAME; eauto.
      }
      inv CAP. eauto.
    }
    {
      ii.
      unfold spec_inj in INJ.
      destruct (Memory.get loc t mem_c) eqn:GET; ss.
      destruct p. destruct t1; eauto. ss.
    }
    {
      eapply spec_inj_monotonic.
    }
  }
  {
    eapply TViewInj_spec_inj_id; eauto.
  }
  {
    econs; eauto.
    ii.
    exists to released from.
    inv LOCAL_WF2.
    exploit PROMISES; eauto. introv GET_MEMC.
    split.
    unfold spec_inj. rewrite GET_MEMC. eauto.
    split; eauto.
    ii.
    exists to' released' from'.
    inv LOCAL_WF2.
    exploit PROMISES; eauto. introv GET_MEMC.
    split.
    unfold spec_inj. rewrite GET_MEMC. eauto.
    eauto.
  }
  {
    introv NA_LOC.
    eapply na_view_intro_le_max_ts; eauto.
    clear - SC_MAX LOCAL_WF_CAP.
    inv LOCAL_WF_CAP. inv TVIEW_CLOSED. inv ACQ.
    unfold Memory.closed_timemap in RLX.
    specialize (RLX loc). des.
    eapply max_concrete_timemap_get in RLX; eauto.
    ii.
    destruct msg; eauto.
    assert (GET_MEM: Memory.get loc ts mem = Some (from, Message.concrete val released)).
    {
      unfold Memory.get in *.
      rewrite <- NA_SAME in H0; eauto.
    }
    inv CAP_MEM.
    eapply SOUND in GET_MEM.
    eapply max_concrete_timemap_get in GET_MEM; eauto.
    clear - H GET_MEM. auto_solve_time_rel.
    ii.
    inv H0. inv ITV; ss.
    eapply Memory.max_ts_spec in GET; eauto. des.
    clear - H MAX TO.
    cut (Time.le ts' (Memory.max_ts loc mem_cap)).
    ii. clear - H H0. auto_solve_time_rel.
    auto_solve_time_rel.
  }
  {
    ii.
    unfold Memory.max_concrete_timemap in SC_MAX.
    specialize (SC_MAX loc). 
    inv MEM_CLOSED_CAP. unfold Memory.inhabited in INHABITED.
    specialize (INHABITED loc).
    exploit Memory.max_concrete_ts_spec; [ | eapply INHABITED | eauto..]. eauto.
    ii; des.
    eapply Memory.cap_inv_concrete in GET.
    3: eapply CAP. 2: eauto.
    unfold Memory.get in *.
    erewrite <- NA_SAME; eauto.
  }
  {
    ii.
    inv LOCAL_WF1.
    eapply PROMISES in H0.
    inv CAP_MEM.
    eapply SOUND in H0.
    eapply max_concrete_timemap_get in H0; eauto.
  }
Qed.
  
Lemma promise_certified_prsv
      lang index index_order I lo inj dset b
      st_tgt lc_tgt sc_tgt mem_tgt st_src lc_src sc_src mem_src
      (WELL_FOUND: well_founded index_order)
      (CONSISTENT_T: NPAuxThread.consistent lang (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) lo)
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (SAFE: ~ (exists e_src', rtc (@Thread.tau_step lang lo)
                              (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                          Thread.is_abort e_src' lo))
      (NO_WW_RACE: ~ @thrd_ww_race lang lo (@Thread.mk lang st_src lc_src sc_src mem_src))
      (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
      (LOCAL_WF_S: Local.wf lc_src mem_src)
      (CLOSED_SC_T: Memory.closed_timemap sc_tgt mem_tgt)
      (CLOSED_SC_S: Memory.closed_timemap sc_src mem_src)
      (CLOSED_MEM_T: Memory.closed mem_tgt)
      (CLOSED_MEM_S: Memory.closed mem_src)
      (WF_I: wf_I I)
      (MONOTONIC_INJ': monotonic_inj inj):
  <<CONSISTENT_S: NPAuxThread.consistent lang (Thread.mk lang st_src lc_src sc_src mem_src) lo>>.
Proof.
  unfold NPAuxThread.consistent in *.
  unfold Thread.consistent_nprm in CONSISTENT_T; ss. ii.
  exploit Memory.cap_exists; [eapply CLOSED_MEM_T | eauto..].
  introv CAP_TGT. destruct CAP_TGT as (mem_tgt_cap & CAP_TGT). 
  exploit Memory.max_concrete_timemap_exists; eauto.
  instantiate (1 := mem_tgt_cap).
  eapply Memory.cap_closed in CAP_TGT; eauto.
  inv CAP_TGT; eauto.
  introv MAX_CONCRETE_TM_TGT. destruct MAX_CONCRETE_TM_TGT as (max_tm_tgt & MAX_CONCRETE_TM_TGT).
  exploit CONSISTENT_T; eauto.
  clear CONSISTENT_T. introv CONSISTENT_T. destruct CONSISTENT_T as (e_tgt & FULFILL_TGT & BOT_TGT).
  lets FULFILL_SRC: FULFILL_TGT.
  eapply rtc_rtcn in FULFILL_SRC. des. ss.
  assert (TGT_PROM_CONS: Local.promise_consistent lc_tgt).
  {
    eapply promise_consistent_prsv_thread_nprm_step in FULFILL_SRC; eauto; ss.
    eapply Memory.cap_closed; eauto.
    eapply Local.cap_wf; eauto.
    unfold Local.promise_consistent.
    rewrite BOT_TGT. ii. rewrite Memory.bot_get in PROMISE; ss.
  }
  eapply lsim_ensures_promise_fulfill with
      (sc_srcc := sc1) (mem_srcc := at_CAP_MEM mem_src mem1 lo) in FULFILL_SRC; eauto; ss.
  {
    destruct FULFILL_SRC as (e_srcc' & FULFILL_SRC & BOT_SRC).
    assert(LOCAL_WF_MEM_AT_CAP: Local.wf lc_src (at_CAP_MEM mem_src mem1 lo)).
    {
      eapply memory_concrete_le_local_wf; eauto.
      unfold memory_concrete_le. unfold at_CAP_MEM.
      clear - CAP. inv CAP. clear - SOUND. unfold Memory.le in *.
      unfold Memory.get in *. ii.
      destruct (lo loc); eauto.
      clear - LOCAL_WF_S CAP.
      inv LOCAL_WF_S. inv CAP.
      clear - SOUND PROMISES.
      unfold Memory.le in *. unfold Memory.get in *. ii.
      unfold at_CAP_MEM. destruct (lo loc); eauto.
    }
    assert(CLOSED_MEM_AT_CAP: Memory.closed (at_CAP_MEM mem_src mem1 lo)).
    {
      eapply memory_closed_additional_rsv; eauto.
      eapply at_CAP_MEM_mem_le; eauto.
      eapply Memory.Memory.le_PreOrder_obligation_1; eauto.
      inv CAP; eauto.
      ii. 
      unfold at_CAP_MEM in *. unfold Memory.get in *.
      destruct (lo loc); ss.
      destruct msg; eauto.
      exploit Memory.cap_inv; eauto. ii; des; ss.
      unfold Memory.get in x0.
      rewrite H in x0; ss.
      destruct msg; eauto. rewrite H in H0; ss.
    }
    eapply rtc_rtcn in FULFILL_SRC. des.
    eapply tau_steps_fulfill_implies_nprm_steps_fulfill in FULFILL_SRC; eauto; ss. des.
    eapply fulfill_ww_race_free_implies_promise_certified in FULFILL_SRC; eauto.
    {
      clear LOCAL_WF_MEM_AT_CAP CLOSED_MEM_AT_CAP.
      introv THRD_WW_RACE_CAP.
      contradiction NO_WW_RACE.
      eapply thrd_ww_race_cap_prsv; eauto.
      eapply at_CAP_MEM_mem_le; eauto.
      eapply Memory.Memory.le_PreOrder_obligation_1; eauto.
      inv CAP; eauto.
      ii. unfold Memory.get in H0, H. unfold at_CAP_MEM in H0.
      destruct (lo loc) eqn:Heqe; eauto; ss. 
      exploit Memory.cap_inv; eauto. ii; des; eauto.
      unfold Memory.get in x0. rewrite H in x0; ss.
      rewrite H in H0. ss.
      inv LOCAL_WF_S; eauto.
    } 
    {
      ii. unfold at_CAP_MEM. rewrite H; eauto.
    }
    {
      ii.
      unfold at_CAP_MEM. rewrite H. eauto.
    }
  }
  {
    inv CAP_TGT; eauto.
  }
  {
    ii. exploit Memory.cap_inv; [ | eapply CAP_TGT | eapply H0 | eauto..]; eauto.
    ii; des; subst; ss.
    rewrite H in x0; ss.
  }
  {
    unfold Memory.le, at_CAP_MEM. ii.
    unfold Memory.get in *.
    destruct (lo loc); eauto.
    inv CAP; eauto.
  }
  {
    ii.
    unfold Memory.get, at_CAP_MEM in *. destruct (lo loc); eauto.
    destruct msg; eauto. 
    exploit Memory.cap_inv; [ | eapply CAP | eauto..]; eauto. ii; des; ss.
    unfold Memory.get in x0.
    rewrite H in x0. ss.
    rewrite H in H0; ss.
  } 
  {
    ii.
    unfold at_CAP_MEM. rewrite H; eauto.
  }
  {
    assert(Mem_at_eq lo mem_tgt_cap (at_CAP_MEM mem_src mem1 lo)).
    {
      inv LOCAL_SIM; ss.
      contradiction SAFE.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; eauto.
      clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
      inv STEP_INV.
      eapply Mem_at_eq_at_CAP_MEM2; eauto.
      eapply Mem_at_eq_cap; eauto.
    }
    ii.
    unfold at_CAP_MEM in *; ss.
    unfold Memory.get in *.
    rewrite H0 in H1; ss.
    unfold Mem_at_eq in *.
    exploit H; eauto. ii. unfold Mem_approxEq_loc in x. des.
    specialize (x0 from to). des.
    unfold Memory.get in x1. rewrite H0 in x1. eauto.
  }
Qed.      
