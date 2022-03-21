Require Import sflib.   
Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Coqlib.
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
Require Import WFConfig.
Require Import PromiseConsistent.
Require Import CompAuxDef.
Require Import LocalSim.
Require Import ConfigInitLemmas.
Require Import Mem_at_eq_lemmas.

Require Import Reordering.
Require Import np_to_ps_thread.
Require Import ps_to_np_thread.
Require Import ConsistentProp.
Require Import CompThreadSteps.
Require Import ConsistentStableEnv.
Require Import simPromiseCertified.

(** * Write-write race freedom preservation proof  *)

(** This file contains the proof of the write-write race freedom preservation. *)

(** The theorem [ww_RF_preservation] in this file shows
    the write-write race freedom preservation of our thread-local simulation.
    It says that,
    if each target thread has thread-local simulation with
    its corresponding source thread
    and the source program is safe and write-write race free,
    then the whole target program is write-write race free.

    The theorem [ww_RF_preservation] is a part of proof in Lemma 6.2 in our paper and
    also shown as a part of proof of the step 3 in Figure 3 (Our proof path) in our paper.
*)

Lemma na_write_on_atomic_loc_is_abort
      lang st lc sc mem lo st' val loc
      (NA_WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) st st')
      (AT_LOC: lo loc = Ordering.atomic)
      (PROM_CONS: Local.promise_consistent lc):
  Thread.is_abort (Thread.mk lang st lc sc mem) lo.
Proof.
  econs; eauto.
  right; ss. left.
  do 4 eexists.
  split; eauto.
  ii.
  rewrite AT_LOC in H. ss.
  des; ss.
Qed. 

Lemma pf_promise_step_tview_unchange
      lang (e e': Thread.t lang)
      (PF: @Thread.pf_promise_step lang e e'):
  Local.tview (Thread.local e) = Local.tview (Thread.local e').
Proof.
  inv PF. inv PF_STEP; ss.
  inv LOCAL; ss; eauto.
Qed.

Lemma pf_promise_steps_tview_unchange
      lang (e e': Thread.t lang)
      (PF: rtc (@Thread.pf_promise_step lang) e e'):
  Local.tview (Thread.local e) = Local.tview (Thread.local e').
Proof.
  induction PF; ss; eauto.
  eapply pf_promise_step_tview_unchange in H.
  rewrite <- IHPF. rewrite H. eauto.
Qed.
  
Lemma not_abort_implies_thread_safe
  ths ctid sc mem lang st lc lo
  (SAFE: ~ (exists npc, rtc (NPConfiguration.all_step lo)
                       (NPConfiguration.mk (Configuration.mk ths ctid sc mem) true) npc /\
                   Configuration.is_abort (NPConfiguration.cfg npc) lo))
  (TH: IdentMap.find ctid ths = Some (existT _ lang st, lc)):
  (~ exists e, rtc (@Thread.all_step lang lo)
              (Thread.mk lang st lc sc mem) e /\ Thread.is_abort e lo).
Proof.
  ii. des.
  eapply rtc_rtcn in H. des.
  eapply Thread_all_steps_to_out_trans in H; eauto.
  des.
  eapply rtc_rtcn in H. des. destruct e0.
  eapply multi_out_trans_to_np_configuration_steps in H; eauto.
  contradiction SAFE.
  eexists.
  split.
  eapply H. ss.
  econs; ss.
  do 3 eexists.
  split.
  rewrite IdentMap.gss. eauto.
  split. eapply H1. eauto.
Qed.

Lemma Memory_promise_not_prm_msg_prsv
      prom mem loc from to msg prom' mem' kind
      loc0 to0 from0 val0 released0
      (PROMISE: Memory.promise prom mem loc from to msg prom' mem' kind)
      (MEM_GET: Memory.get loc0 to0 mem' = Some (from0, Message.concrete val0 released0))
      (PROM_GET: Memory.get loc0 to0 prom' = None):
  Memory.get loc0 to0 mem = Some (from0, Message.concrete val0 released0) /\
  Memory.get loc0 to0 prom = None.
Proof.
  inv PROMISE; ss.
  {
    (* promise add *)
    erewrite Memory.add_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.add_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.add_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
  }
  {
    (* promise split *)
    des; subst; ss.
    erewrite Memory.split_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
  }
  {
    (* promise lower *)
    des; subst.
    erewrite Memory.lower_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
  }
  {
    (* promise cancel *)
    erewrite Memory.remove_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
  }
Qed.

Lemma Memory_promise_not_prm_msg_stable
      prom mem loc from to msg prom' mem' kind
      loc0 to0 from0 val0 released0
      (PROMISE: Memory.promise prom mem loc from to msg prom' mem' kind)
      (MEM_GET: Memory.get loc0 to0 mem = Some (from0, Message.concrete val0 released0))
      (PROM_GET: Memory.get loc0 to0 prom = None):
  Memory.get loc0 to0 mem' = Some (from0, Message.concrete val0 released0) /\
  Memory.get loc0 to0 prom' = None.
Proof.
  inv PROMISE; ss.
  {
    (* promise add *)
    exploit Memory.add_get1; eauto. ii.
    split; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; eauto. des; subst.
    exploit Memory.add_get0; eauto. ii; des.
    rewrite MEM_GET in GET. ss.
  }
  {
    (* promise split *)
    des; subst.
    split.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
    rewrite MEM_GET in GET. ss.
    des_if; ss; des; subst; ss.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET0. ss.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
    rewrite MEM_GET in GET. ss.
    des_if; ss; des; subst; ss.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET0. ss.
  }
  {
    (* promise lower *)
    des; subst.
    split.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET. ss.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET. ss.
  }
  {
    (* promise cancel *)
    split.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.remove_get0; eauto. ii; des.
    rewrite PROM_GET in GET. ss.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  }
Qed.

Lemma race_message_in_starting_mem':
  forall n lang st lc sc mem st' lc' sc' mem' lo loc to from val released
    (STEPS: rtcn (@Thread.all_step lang lo) n
                 (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MSG: Memory.get loc to mem' = Some (from, Message.concrete val released))
    (NOT_PROM: Memory.get loc to (Local.promises lc') = None)
    (RACE: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (LOCAL_WF: Local.wf lc mem)
    (SC_CLOSED: Memory.closed_timemap sc mem)
    (CLOSED_MEM: Memory.closed mem),
    Memory.get loc to mem = Some (from, Message.concrete val released) /\
    Memory.get loc to (Local.promises lc) = None /\
    Time.lt (View.rlx (TView.cur (Local.tview lc)) loc) to.
Proof.
  induction n; ii.
  - inv STEPS. eauto.
  - inv STEPS. destruct a2.
    inv A12. inv USTEP.
    exploit Thread.step_future; eauto; ss. ii; des.
    eapply IHn in A23; eauto. des.
    inv STEP.
    + inv STEP0. inv LOCAL. ss.
      exploit Memory_promise_not_prm_msg_prsv; [eapply PROMISE | eapply A23 | eapply A0 | eauto..].
      ii; des; eauto.
    + inv STEP0. inv LOCAL; ss; eauto.
      {
        (* read *)
        inv LOCAL0; ss; eauto.
        split; eauto. split; eauto.
        eapply Time_lt_join in A1. des.
        eapply Time_lt_join in A1. des. eauto.
      }
      {
        (* write *)
        inv LOCAL0; ss. inv WRITE; ss. 
        assert ((loc0, to0) <> (loc, to)).
        {
          ii. inv H.
          clear - A1.
          eapply Time_lt_join in A1. des.
          unfold TimeMap.singleton in A0; ss.
          rewrite Loc_add_eq in A0.
          auto_solve_time_rel.
        }
        erewrite Memory.remove_o in A0; eauto.
        des_ifH A0; ss. contradiction H; eauto. des; subst. eauto.
        exploit Memory_promise_not_prm_msg_prsv; [eapply PROMISE | eapply A23 | eapply A0 | eauto..].
        introv MEM_PROM_GET. destruct MEM_PROM_GET.
        split; eauto. split; eauto.
        eapply Time_lt_join in A1. des; eauto.
      }
      {
        (* update *)
        inv LOCAL1.
        inv READABLE.
        inv LOCAL2; ss. inv WRITABLE. inv WRITE.
        assert ((loc0, tsw) <> (loc, to)).
        {
          ii; subst. inv H.
          eapply Time_lt_join in A1. des.
          unfold TimeMap.singleton in A2.
          rewrite Loc_add_eq in A2.
          auto_solve_time_rel.
        }
        erewrite Memory.remove_o in A0; eauto.
        des_ifH A0; ss. contradiction H. des; subst; ss; eauto.
        exploit Memory_promise_not_prm_msg_prsv; [eapply PROMISE | eapply A23 | eapply A0 | eauto..].
        introv MEM_PROM_GET. destruct MEM_PROM_GET.
        split; eauto. split; eauto.
        eapply Time_lt_join in A1. destruct A1.
        eapply Time_lt_join in H2. destruct H2.
        eapply Time_lt_join in H2. destruct H2.
        eauto.
      }
      {
        (* fence *) 
        inv LOCAL0; ss.
        split; eauto. split; eauto. 
        destruct (Ordering.le Ordering.seqcst ordw) eqn:ORDER.
        {
          ss. 
          unfold TView.write_fence_sc in A1.
          unfold TView.read_fence_tview in A1; ss.
          des_ifH A1; ss; des; subst; ss.
          des_ifH A1; ss; des; subst; ss; eauto.
          eapply Time_lt_join in A1. des.
          inv LOCAL_WF. inv TVIEW_WF. inv CUR_ACQ.
          unfold TimeMap.le in RLX. specialize (RLX loc).
          cut (Time.lt (View.rlx (TView.cur (Local.tview lc)) loc) to).
          ii.
          inv CUR.
          unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc).
          auto_solve_time_rel.
          auto_solve_time_rel.
          
          eapply Time_lt_join in A1; des; eauto.
        }
        des_ifH A1; ss; eauto.
        inv LOCAL_WF. inv TVIEW_WF. inv CUR_ACQ.
        unfold TimeMap.le in RLX.
        specialize (RLX loc).
        auto_solve_time_rel.
      }
      {
        (* out put *)
        inv LOCAL0; ss. split; eauto. split; eauto.
        assert (ORDER_LE: Ordering.le Ordering.seqcst Ordering.seqcst).
        eauto.
        rewrite ORDER_LE in A1. ss.
        unfold TView.write_fence_sc, TView.read_fence_tview in A1; ss.
        des_ifH A1; ss.
        eapply Time_lt_join in A1. des.
        des_ifH A2; ss; eauto.
        inv LOCAL_WF. inv TVIEW_WF. inv CUR_ACQ.
        unfold TimeMap.le in RLX. 
        specialize (RLX loc).
        cut (Time.lt (View.rlx (TView.acq (Local.tview lc)) loc) to). ii.
        auto_solve_time_rel. eauto.
      }
Qed.

Lemma race_message_in_starting_mem
    lang st lc sc mem st' lc' sc' mem' lo loc to from val released
    (STEPS: rtc (@Thread.all_step lang lo)
                (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MSG: Memory.get loc to mem' = Some (from, Message.concrete val released))
    (NOT_PROM: Memory.get loc to (Local.promises lc') = None)
    (RACE: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (LOCAL_WF: Local.wf lc mem)
    (SC_CLOSED: Memory.closed_timemap sc mem)
    (CLOSED_MEM: Memory.closed mem):
    Memory.get loc to mem = Some (from, Message.concrete val released) /\
    Memory.get loc to (Local.promises lc) = None.
Proof.
  eapply rtc_rtcn in STEPS. des.
  eapply race_message_in_starting_mem' in STEPS; eauto.
  des; eauto.
Qed.

Lemma race_message_stable':
  forall n lang st lc sc mem st' lc' sc' mem' lo loc from to val released
    (STEPS: rtcn (@Thread.all_step lang lo) n
                 (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MSG: Memory.get loc to mem = Some (from, Message.concrete val released))
    (NOT_PROM: Memory.get loc to (Local.promises lc) = None),
    Memory.get loc to mem' = Some (from, Message.concrete val released) /\
    Memory.get loc to (Local.promises lc') = None.
Proof.
  induction n; ii.
  - inv STEPS. eauto.
  - inv STEPS.
    inv A12. inv USTEP. inv STEP; ss.
    + inv STEP0. inv LOCAL; ss.
      exploit Memory_promise_not_prm_msg_stable;
        [eapply PROMISE | eapply MSG | eapply NOT_PROM | eauto..].
      ii; des.
      eapply IHn in A23; eauto.
    + inv STEP0. inv LOCAL; eauto.
      {
        (* read *)
        inv LOCAL0; ss. eauto.
      }
      {
        (* write *)
        inv LOCAL0. inv WRITE.
        eapply Memory_promise_not_prm_msg_stable in PROMISE; eauto. des.
        assert ((loc, to) <> (loc0, to0)).
        {
          ii. inv H.
          exploit Memory.remove_get0; [eapply REMOVE | eauto..]. ii; des.
          rewrite PROMISE0 in GET. ss.
        }

        eapply IHn in A23; eauto.
        ss. erewrite Memory.remove_o; eauto.
        des_if; eauto.
      }
      {
        (* update *)
        inv LOCAL1. inv LOCAL2; ss. inv WRITE.
        eapply Memory_promise_not_prm_msg_stable with (loc0 := loc) (to0 := to) in PROMISE; eauto. des.
        assert ((loc, to) <> (loc0, tsw)).
        {
          ii. inv H.
          exploit Memory.remove_get0; [eapply REMOVE | eauto..]. ii; des.
          rewrite PROMISE0 in GET0. ss.
        }

        eapply IHn in A23; eauto.
        ss. erewrite Memory.remove_o; eauto.
        des_if; eauto.
      }
      {
        (* fence *)
        inv LOCAL0.
        eapply IHn in A23; eauto.
      }
      {
        (* out put *)
        eapply IHn in A23; eauto.
        inv LOCAL0; eauto.
      }
Qed.

Lemma race_message_stable
  lang st lc sc mem st' lc' sc' mem' lo loc from to val released
  (STEPS: rtc (@Thread.all_step lang lo) 
               (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
  (MSG: Memory.get loc to mem = Some (from, Message.concrete val released))
  (NOT_PROM: Memory.get loc to (Local.promises lc) = None):
  Memory.get loc to mem' = Some (from, Message.concrete val released) /\
  Memory.get loc to (Local.promises lc') = None.
Proof.
  eapply rtc_rtcn in STEPS. des.
  eapply race_message_stable'; eauto.
Qed.

Lemma na_steps_dset_race_or_not':
  forall n lo lang (e e': Thread.t lang) loc from to val R index (dset dset': @DelaySet index) i t 
    (NA_STEPS_DSET: rtcn (na_step_dset lo) n (e, dset) (e', dset'))
    (RACE_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val R))
    (NOT_PROM: Memory.get loc to (Local.promises (Thread.local e)) = None)
    (LT: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
    (IN_DSET: dset_get loc t dset = Some i),
  <<RACE: exists e0 e1 f' t' v,
    rtc (Thread.na_step lo) e e0 /\
    Thread.program_step (ThreadEvent.write loc f' t' v None Ordering.plain) lo e0 e1 /\
    Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e0))) loc) to /\
    rtc (Thread.na_step lo) e1 e' >> \/
  <<NOT_RACE: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to /\
              dset_get loc t dset' = Some i>>.
Proof.
  induction n; ii.
  - inv NA_STEPS_DSET. eauto.
  - inv NA_STEPS_DSET. destruct a2. 
    renames t0 to e0, d to dset0.
    inv A12.
    + (* silent step *)
      eapply IHn in A23; eauto.
      des.
      {
        left.
        exists e1 e2 f' t' v.
        split; eauto.
        eapply Relation_Operators.rt1n_trans. 2: eauto.
        eapply Thread.na_tau_step_intro; eauto.
      }
      {
        right; eauto.
      }

      inv STEP; ss. inv LOCAL; ss. eauto.
      inv STEP; ss. inv LOCAL; ss.
      inv STEP; ss. inv LOCAL; ss.
    + (* read step *)
      eapply IHn in A23; eauto.
      des.
      {
        left.
        exists e1 e2 f' t' v0.
        split; eauto.
        eapply Relation_Operators.rt1n_trans. 2: eauto.
        eapply Thread.na_plain_read_step_intro; eauto.
      }
      {
        right.
        split; eauto.
      }

      inv STEP; ss. inv LOCAL; ss. eauto.
      inv STEP; ss. inv LOCAL; ss. inv LOCAL0; ss.
      erewrite <- RLX; eauto.
    + (* write step *)
      destruct (Loc.eq_dec loc loc0); subst.
      {
        (* race in the current step *)
        left.
        exists e e0 from0 to0 v.
        assert (R0 = None).
        {
          inv STEP; ss. inv LOCAL; ss. inv LOCAL0; ss.
        }
        subst R0.
        split; eauto.
        split; eauto.
        split; eauto.
        eapply na_steps_dset_to_Thread_na_steps' in A23. eauto.
      }
      {
        (* race not in the current step *)  
        assert (DSET0: dset_get loc t dset0 = Some i).
        {
          clear - DSET_REMOVE IN_DSET n0. des; subst; eauto.
          unfold dset_get, dset_remove in *; ss. des_if; subst; ss.
        } 
        clear DSET_REMOVE. destruct e, e0; ss. 
        exploit race_message_stable; [ | eapply RACE_MSG | eapply NOT_PROM | eauto..].
        {      
          eapply Relation_Operators.rt1n_trans. 2: eauto.
          econs. econs. eapply Thread.step_program. eauto.
        }
        ii; des.
        eapply IHn with (loc := loc) (to := to) (i := i) in A23; eauto.

        des; ss.
        {
          left.
          exists e0 e1 f' t' v0.
          split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eauto.
          eapply Thread.na_plain_write_step_intro; eauto.
        }
        {
          right. eauto.
        }

        ss.
        inv STEP; ss. inv LOCAL; ss. inv LOCAL0; ss.
        unfold TimeMap.join; ss.
        unfold TimeMap.singleton.
        rewrite Loc_add_neq; eauto.
        unfold LocFun.init; ss.
        rewrite Time_join_bot; eauto.
      }
Qed.

Lemma na_steps_dset_race_or_not
      lo lang (e e': Thread.t lang) loc from to val R index (dset dset': @DelaySet index) i t
      (NA_STEPS_DSET: rtc (na_step_dset lo) (e, dset) (e', dset'))
      (RACE_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val R))
      (NOT_PROM: Memory.get loc to (Local.promises (Thread.local e)) = None)
      (LT: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
      (IN_DSET: dset_get loc t dset = Some i):
  <<RACE: exists e0 e1 f' t' v,
    rtc (Thread.na_step lo) e e0 /\
    Thread.program_step (ThreadEvent.write loc f' t' v None Ordering.plain) lo e0 e1 /\
    Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e0))) loc) to /\
    rtc (Thread.na_step lo) e1 e' >> \/
  <<NOT_RACE: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to /\
              dset_get loc t dset' = Some i>>.
Proof.
  eapply rtc_rtcn in NA_STEPS_DSET. des.
  eapply na_steps_dset_race_or_not'; eauto.
Qed.

(** Move above lemmas to another file*)
Lemma source_ww_race_construction1:
  forall lang st_tgt lc_tgt sc_tgt mem_tgt 
    index index_order 
    st_src lc_src sc_src mem_src lo loc to' b dset inj I
    from' val' R' i t
    (T_BOT: Local.promises lc_tgt = Memory.bot)
    (INDSET: dset_get loc t dset = Some i)
    (ACC: Acc index_order i)
    (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_src lc_src sc_src mem_src))
    (RACE_MSG_S: Memory.get loc to' mem_src = Some (from', Message.concrete val' R'))
    (NOT_PROM_S: Memory.get loc to' (Local.promises lc_src) = None)
    (RACE_S: Time.lt (View.rlx (TView.cur (Local.tview lc_src)) loc) to')
    (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                        Thread.is_abort e_src' lo))
    (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
    (MEM_CLOSED: Memory.closed mem_tgt)
    (LOCAL_WF_S: Local.wf lc_src mem_src)
    (MEM_CLOSED: Memory.closed mem_src)
    (MONOTONIC_INJ: monotonic_inj inj)
    (WELL_FOUNDED: well_founded index_order),
  exists st_src' lc_src' sc_src' mem_src' e_src' stw_src' val0,
    <<PRE_S: rtc (Thread.nprm_step lo) (Thread.mk lang st_src lc_src sc_src mem_src)
                 (Thread.mk lang st_src' lc_src' sc_src' mem_src')>> /\
    <<WRITE_S: Language.step lang (ProgramEvent.write loc val0 Ordering.plain) st_src' stw_src'>> /\ 
    <<RACE_MSG_S': Memory.get loc to' mem_src' = Some (from', Message.concrete val' R')>> /\
    <<NOT_PROM_S': Memory.get loc to' (Local.promises lc_src') = None>> /\
    <<VIEW_S': Time.lt (View.rlx (TView.cur (Local.tview lc_src')) loc) to'>> /\
    <<FULFILL_S: rtc (Thread.nprm_step lo)
                     (Thread.mk lang st_src' lc_src' sc_src' mem_src') e_src'>> /\ 
    <<BOT_S: Local.promises (Thread.local e_src') = Memory.bot>>.
Proof.
  ii.
  generalize dependent st_tgt.
  generalize dependent lc_tgt.
  generalize dependent sc_tgt.
  generalize dependent mem_tgt.
  generalize dependent st_src.
  generalize dependent lc_src.
  generalize dependent sc_src.
  generalize dependent mem_src.
  generalize dependent dset.
  generalize dependent inj.
  generalize dependent b.
  induction ACC; ii.

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
    contradiction SAFE.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
    eapply Thread_tau_steps_is_all_steps in NP_STEPS. eauto.
    clear THRD_STEP RELY_STEP THRD_DONE.
    exploit THRD_ABORT; eauto. ii; des.
    contradiction SAFE.
    eapply na_steps_is_tau_steps in H1; eauto.
    eapply Thread_tau_steps_is_all_steps in H1; eauto.
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
      (* target thread takes an atomic step *)
      inv LOCAL_SIM; ss.

      (* source thread abort *)
      contradiction SAFE.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      eapply Thread_tau_steps_is_all_steps in NP_STEPS. eauto.

      (* source thread not abort *)
      clear THRD_STEP RELY_STEP THRD_ABORT THRD_DONE.
      inv STEP_INV. exploit DSET_EMP; eauto. ii; subst.
      unfold dset_get, dset_init in INDSET.
      rewrite DenseOrder.DOMap.gempty in INDSET. ss.
    }
    {
      (* target thread takes a non-atomic step *)
      eapply not_or_and in NOT_ABORT_T0. des.
      exploit state_in_not_abort_thread_step; eauto.
      instantiate (1 := sc_tgt).
      introv TGT_THREAD_STEP.
      destruct TGT_THREAD_STEP as (te & e_tgt & TGT_THREAD_STEP & IS_NA_STEP & PROM_EQ).
      destruct e_tgt.
      renames state to st_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
      inv LOCAL_SIM; ss.

      (* source abort *)
      contradiction SAFE.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      eapply Thread_tau_steps_is_all_steps in NP_STEPS.
      exists e_src. split; eauto.

      (* source thread not abort *)
      clear RELY_STEP THRD_DONE THRD_ABORT.
      exploit THRD_STEP; eauto. clear THRD_STEP.
      ii; des.
      clear H1 H3 H4.
      exploit H2; eauto. clear H2. ii; des.
      exploit na_steps_dset_to_Thread_na_steps; [eapply H2 | eauto..].
      introv NA_STEPS_S.
      destruct e_src'.
      assert (LOCAL_WF_S': Local.wf local memory).
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply rtc_rtcn in NA_STEPS_S. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in NA_STEPS_S; eauto.
      }
      assert (MEM_CLOSED_S': Memory.closed memory).
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply rtc_rtcn in NA_STEPS_S. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in NA_STEPS_S; eauto.
      }
      eapply Thread_na_steps_to_nprm_steps in NA_STEPS_S.
      lets S_PROM_FULFILL: H4.
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
      assert (LOCAL_WF_T': Local.wf lc_tgt' mem_tgt').
      {
        eapply Thread_na_step_is_no_scfence_nprm_step in TGT_NA_STEP.
        eapply no_scfence_nprm_step_prsv_local_wf in TGT_NA_STEP; ss.
      }
      assert (MEM_CLOSED_T': Memory.closed mem_tgt').
      {
        eapply Thread_na_step_is_no_scfence_nprm_step in TGT_NA_STEP.
        eapply no_scfence_nprm_step_prsv_memory_closed in TGT_NA_STEP; ss.
      }

      exploit na_steps_dset_race_or_not; [eapply H2 | eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..]; ss.
      {
        instantiate (1 := x). instantiate (1 := t).
        clear - INDSET H1. inv H1; eauto.
        eapply dset_get_add1; eauto.
      }
      
      ii; des.
      {
        (* source generate race in current steps *)
        destruct e0, e1; ss. inv RACE0; ss.
        eapply lsim_ensures_promise_fulfill_T_BOT in S_PROM_FULFILL; eauto.
        instantiate (1 := sc) in S_PROM_FULFILL. des.
        exists state0 local0 sc0 memory0. exists e_srcc' state1 v.
        exploit race_message_stable; [| eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..]. 
        eapply Thread_na_steps_to_nprm_steps in RACE.
        eapply Thread_nprm_step_is_tau_step in RACE.
        eapply Thread_tau_steps_is_all_steps in RACE.
        eapply RACE.
        
        introv RACE_MSG_S'.
        destruct RACE_MSG_S' as (RACE_MSG_S' & NOT_PROM_S').

        split; eauto.
        {
          eapply Thread_na_steps_to_nprm_steps; eauto.
        }
        split; eauto. split; eauto. split; eauto. split; eauto.
        split; eauto.
        eapply Thread_na_steps_to_nprm_steps in RACE2.
        eapply Relation_Operators.rt1n_trans.
        econs. econs; eauto. eauto. eauto.
        eapply rtc_compose; eauto.
        rewrite <- PROM_EQ; eauto.

        introv ABORT_S. destruct ABORT_S as (e_src & PSTEPS & ABORT_S).
        contradiction SAFE.
        exists e_src; eauto.
        eapply Thread_tau_steps_is_all_steps in PSTEPS.
        split; eauto.
        eapply Thread_nprm_step_is_tau_step in NA_STEPS_S.
        eapply Thread_tau_steps_is_all_steps in NA_STEPS_S.
        eapply rtc_compose; eauto.

        unfold Memory.le. ii; eauto.
      }
      {
        (* source not generate race in current steps *)
        exploit dset_after_na_step_origin_prsv; eauto.
        introv DSET_GET.
        
        exploit dset_reduce; eauto. ii; des.
        exploit race_message_stable; [| eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..]. 
        eapply Thread_nprm_step_is_tau_step in NA_STEPS_S.
        eapply Thread_tau_steps_is_all_steps in NA_STEPS_S.
        eapply NA_STEPS_S.

        introv RACE_MSG_S'. destruct RACE_MSG_S' as (RACE_MSG_S' & NOT_PROM_S').

        exploit H0.
        eauto. eauto. eauto.
        eapply RACE_MSG_S'. eauto.
        eapply NOT_PROM_S'. eauto. eauto.

        introv ABORT_S.
        destruct ABORT_S as (e_src' & PSTEPS & ABORT_S).
        contradiction SAFE.
        exists e_src'. split; eauto.
        eapply Thread_nprm_step_is_tau_step in NA_STEPS_S.
        eapply Thread_tau_steps_is_all_steps in NA_STEPS_S.
        eapply rtc_compose; eauto.

        4: eapply H4.
        eauto. rewrite <- PROM_EQ; eauto. eauto.

        ii; des.
        exists st_src' lc_src' sc_src' mem_src'. exists e_src' stw_src' val0.
        split.
        eapply rtc_compose; eauto.
        split; eauto.
      } 
    }
  }
  {
    (* target thread done *)
    inv LOCAL_SIM; ss.

    (* source abort *)
    contradiction SAFE.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
    eapply Thread_tau_steps_is_all_steps in NP_STEPS. eauto.

    (* source not abort *)
    exploit THRD_DONE; eauto. ii; des.
    exploit na_steps_dset_race_or_not; [eapply H1 | eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..]; ss.
    ii; des.
    {
      (* source generates race *)
      destruct e0, e1; ss. inv RACE0; ss.
      exploit race_message_stable; [| eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..].
      eapply Thread_na_steps_to_nprm_steps in RACE.
      eapply Thread_nprm_step_is_tau_step in RACE.
      eapply Thread_tau_steps_is_all_steps in RACE.
      eapply RACE.
      introv RACE_MSG_S'. destruct RACE_MSG_S' as (RACE_MSG_S' & NOT_PROM_S').
      exists state local sc memory. exists e_src state0 v.
      split.
      {
        eapply Thread_na_steps_to_nprm_steps in RACE.
        eauto.
      }
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split.
      {
        eapply Relation_Operators.rt1n_trans.
        econs; eauto. econs; eauto. eauto. eauto.
        eapply Thread_na_steps_to_nprm_steps in RACE2. eauto.
      }
      {
        inv H2. eauto.
      }
    }
    {
      (* source not generate race *)
      rewrite dset_gempty in NOT_RACE0. ss.
    }
  }
Qed. 
  
Lemma source_ww_race_construction2':
  forall n lang st_tgt lc_tgt sc_tgt mem_tgt e_tgt'
    index index_order 
    st_src lc_src sc_src mem_src lo loc to' b dset inj I
    from' val' R' t i
    (FULFILL: rtcn (no_scfence_nprm_step lang lo) n (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) e_tgt')
    (BOT: Local.promises (Thread.local e_tgt') = Memory.bot)
    (INDSET: dset_get loc t dset = Some i)
    (ACC: Acc index_order i)
    (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_src lc_src sc_src mem_src))
    (RACE_MSG_S: Memory.get loc to' mem_src = Some (from', Message.concrete val' R'))
    (NOT_PROM_S: Memory.get loc to' (Local.promises lc_src) = None)
    (RACE_S: Time.lt (View.rlx (TView.cur (Local.tview lc_src)) loc) to')
    (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                        Thread.is_abort e_src' lo))
    (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
    (MEM_CLOSED: Memory.closed mem_tgt)
    (LOCAL_WF_S: Local.wf lc_src mem_src)
    (MEM_CLOSED: Memory.closed mem_src)
    (MONOTONIC_INJ: monotonic_inj inj)
    (WELL_FOUNDED: well_founded index_order)
    (WF_I: wf_I I),
  exists st_src' lc_src' sc_src' mem_src' e_src' stw_src' val0,
    <<PRE_S: rtc (Thread.nprm_step lo) (Thread.mk lang st_src lc_src sc_src mem_src)
                 (Thread.mk lang st_src' lc_src' sc_src' mem_src')>> /\
    <<WRITE_S: Language.step lang (ProgramEvent.write loc val0 Ordering.plain) st_src' stw_src'>> /\ 
    <<RACE_MSG_S': Memory.get loc to' mem_src' = Some (from', Message.concrete val' R')>> /\
    <<NOT_PROM_S': Memory.get loc to' (Local.promises lc_src') = None>> /\
    <<VIEW_S': Time.lt (View.rlx (TView.cur (Local.tview lc_src')) loc) to'>> /\
    <<FULFILL_S: rtc (Thread.nprm_step lo)
                     (Thread.mk lang st_src' lc_src' sc_src' mem_src') e_src'>> /\ 
    <<BOT_S: Local.promises (Thread.local e_src') = Memory.bot>>.
Proof.
  induction n; ii.
  - inv FULFILL; ss.
    eapply source_ww_race_construction1; eauto.
  - assert (TGT_PROM_CONS: Local.promise_consistent lc_tgt).
    {
      eapply rtcn_rtc in FULFILL.
      eapply no_scfence_steps_to_bot_promise_consistent in FULFILL; eauto.
    }
    inv FULFILL.
    destruct a2; ss.
    assert (TGT_PROM_CONS': Local.promise_consistent local).
    {
      eapply rtcn_rtc in A23.
      eapply no_scfence_steps_to_bot_promise_consistent in A23; eauto; ss.
      eapply no_scfence_nprm_step_prsv_local_wf in A12; eauto.
      eapply no_scfence_nprm_step_prsv_memory_closed in A12; eauto.
    }
    assert (LOCAL_WF_T': Local.wf local memory).
    {
      eapply no_scfence_nprm_step_prsv_local_wf in A12; eauto.
    }
    assert (MEM_CLOSED': Memory.closed memory).
    {
      eapply no_scfence_nprm_step_prsv_memory_closed in A12; eauto.
    }
    inv A12.
    + (* program step *)
      exploit state_in_or_out. instantiate (1 := ThreadEvent.get_program_event e).
      introv AT_OR_NA_STEP.
      destruct AT_OR_NA_STEP as [AT_STEP | NA_STEP].
      {
        (* atomic step *)
        inv LOCAL_SIM; ss.
        contradiction SAFE.
        eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS; eauto.

        clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
        inv STEP_INV. inv STEP. exploit DSET_EMP; eauto. ii; subst.
        clear - INDSET.
        unfold dset_get, dset_init in INDSET.
        rewrite DenseOrder.DOMap.gempty in INDSET. ss.
      }
      {
        (* non-atomic step *)
        exploit state_in_step_implies_threadEvt_is_na_step; eauto.
        introv IS_NA_STEP.
        inv LOCAL_SIM; ss.

        (* source abort *)
        contradiction SAFE.
        eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
        exists e_src. split; eauto.

        (* source not abort *)
        clear THRD_ABORT THRD_DONE RELY_STEP.
        exploit THRD_STEP; eauto. clear THRD_STEP.
        ii; des. clear H H1 H2.
        exploit H0; eauto. ii; des.
        exploit na_steps_dset_to_Thread_na_steps; [eapply H1 | eauto..].
        introv NA_STEPS_S.
        destruct e_src'.
        assert (LOCAL_WF_S': Local.wf local0 memory0).
        {
          eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
          eapply rtc_rtcn in NA_STEPS_S. des.
          eapply no_scfence_nprm_steps_prsv_local_wf in NA_STEPS_S; eauto.
        }
        assert (MEM_CLOSED_S': Memory.closed memory0).
        {
          eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
          eapply rtc_rtcn in NA_STEPS_S. des.
          eapply no_scfence_nprm_steps_prsv_memory_closed in NA_STEPS_S; eauto.
        }

        exploit na_steps_dset_race_or_not; [eapply H1 | eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..].
        {
          instantiate (1 := i). instantiate (1 := t).
          clear - INDSET H. inv H; eauto.
          eapply dset_get_add1; eauto.
        }
        ii; des.
        {
          (* source current steps generate race *)
          eapply rtcn_rtc in A23.
          eapply no_scfence_nprm_steps_is_nprm_steps in A23; eauto.
          eapply rtc_rtcn in A23. des.
          
          exploit lsim_ensures_promise_fulfill;
            [eapply WELL_FOUNDED | eapply MONOTONIC_INJ | eapply WF_I |
              eapply A23 | eapply BOT | eauto..].
          {
            unfold Memory.le. ii; eauto.
          }
          {
            introv GET_NONE GET_MSG.
            rewrite GET_MSG in GET_NONE. ss.
          }
          {
            introv ABORT_S. destruct ABORT_S as (e_src' & PSTEPS & ABORT_S).
            contradiction SAFE.
            eapply na_steps_is_tau_steps in NA_STEPS_S.
            eapply Thread_tau_steps_is_all_steps in NA_STEPS_S.
            eapply Thread_tau_steps_is_all_steps in PSTEPS.
            exists e_src'. split; eauto.
            eapply rtc_compose; [eapply NA_STEPS_S | eapply PSTEPS].
          }
          {
            instantiate (1 := memory0).
            unfold Memory.le. ii; eauto.
          }
          {
            introv GET_NONE GET_MSG.
            rewrite GET_NONE in GET_MSG. ss.
          }

          instantiate (1 := sc0).
          introv TEMP. exploit TEMP; eauto.
          inv H3; ss.
          contradiction SAFE.
          eapply na_steps_is_tau_steps in NA_STEPS_S.
          eapply Thread_tau_steps_is_all_steps in NA_STEPS_S.
          eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
          exists e_src. split; eauto.
          eapply rtc_compose; eauto.

          clear - STEP_INV0. inv STEP_INV0.
          unfold Mem_at_eq in ATOMIC_COVER. ii.
          exploit ATOMIC_COVER; eauto.
          introv MEM_APPROX_EQ.
          unfold Mem_approxEq_loc in MEM_APPROX_EQ. des.
          eapply MEM_APPROX_EQ0; eauto.

          introv FULFILL_S. destruct FULFILL_S as (e_src' & FULFILL_S & BOT_S).
          eapply rtc_rtcn in FULFILL_S. des.
          eapply tau_steps_fulfill_implies_nprm_steps_fulfill in FULFILL_S; eauto; ss. des.
          inv RACE0; ss.
          eapply Thread_na_steps_to_nprm_steps in RACE.
          eapply Thread_na_steps_to_nprm_steps in RACE2.
          exists st1 lc1 sc1 mem1 e2. exists st2 v.
          split; eauto. split; eauto. 
          eapply Thread_nprm_step_is_tau_step in RACE.
          eapply Thread_tau_steps_is_all_steps in RACE.
          exploit race_message_stable; [eapply RACE | eauto..]. ii; des.
          split; eauto. split; eauto. split; eauto.
          split; eauto.
          eapply Relation_Operators.rt1n_trans.
          econs. econs; eauto. ss. eauto. eauto.
          eapply rtc_compose; eauto.
        }
        {
          (* source thread will not generate race *)
          ss.
          exploit dset_reduce; [ | eauto..]; eauto; ss. 
          introv IN_DSET2'.
          destruct IN_DSET2' as (j & IN_DSET2' & INDEX_DEC).
          exploit race_message_stable; [ | eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..].
          eapply na_steps_is_tau_steps in NA_STEPS_S.
          eapply Thread_tau_steps_is_all_steps; eauto.
          introv RACE_MSG_S'.
          destruct RACE_MSG_S' as (RACE_MSG_S' & NOT_PROM_S').
          eapply IHn in H3; eauto; ss.
          ii; des.
          exists st_src' lc_src' sc_src' mem_src'. exists e_src' stw_src' val0.
          eapply Thread_na_steps_to_nprm_steps in NA_STEPS_S.
          split. eapply rtc_compose; [eapply NA_STEPS_S | eapply PRE_S].
          split; eauto.

          introv ABORT_S. destruct ABORT_S as (e_src' & PSTEPS & ABORT_S).
          contradiction SAFE.
          exists e_src'. split; eauto.
          eapply na_steps_is_tau_steps in NA_STEPS_S.
          eapply Thread_tau_steps_is_all_steps in NA_STEPS_S; eauto.
          eapply rtc_compose; eauto.
        }
      }
    + (* pf promise step *)
      inv LOCAL_SIM; ss.

      (* source abort *)
      contradiction SAFE.
      eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
      exists e_src. split; eauto.

      (* source not abort *)
      clear RELY_STEP THRD_DONE THRD_ABORT.
      exploit THRD_STEP; eauto.
      ii; des. clear THRD_STEP H H0 H1.
      exploit H2; eauto.
      clear - STEP. inv STEP. inv LOCAL; ss; eauto.
      ii; des. clear H2.
      lets TVIEW_UNCHANGE: H.
      eapply pf_promise_steps_tview_unchange in TVIEW_UNCHANGE; ss.
      destruct e_src'; ss.
      exploit race_message_stable; [| eapply RACE_MSG_S | eapply NOT_PROM_S | eauto.. ].
      eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
      eapply no_scfence_nprm_steps_is_nprm_steps in H.
      eapply Thread_nprm_step_is_tau_step in H.
      eapply Thread_tau_steps_is_all_steps in H.
      eapply H.
      introv RACE_MSG_S'.
      destruct RACE_MSG_S' as (RACE_MSG_S' & NOT_PROM_S'). 
      eapply IHn in H0; eauto.
      {
        des.
        exists st_src' lc_src' sc_src' mem_src'. exists e_src' stw_src' val0.
        split.
        eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
        eapply no_scfence_nprm_steps_is_nprm_steps in H.
        eapply rtc_compose; eauto.
        split; eauto.
      }
      {
        rewrite <- TVIEW_UNCHANGE; eauto.
      }
      {
        introv ABORT_S.
        contradiction SAFE.
        destruct ABORT_S as (e_src' & PSTEPS & ABORT_S).
        exists e_src'. split; eauto.
        eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
        eapply no_scfence_nprm_steps_is_nprm_steps in H.
        eapply Thread_nprm_step_is_tau_step in H.
        eapply Thread_tau_steps_is_all_steps in H.
        eapply rtc_compose; eauto.
      }
      {
        eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
        eapply rtc_rtcn in H. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in H; eauto.
      }
      {
        eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
        eapply rtc_rtcn in H. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in H; eauto.
      }
Qed.
      
Lemma source_ww_race_construction2:
  forall n lang st_tgt lc_tgt sc_tgt mem_tgt e_tgt'
    index index_order 
    st_src lc_src sc_src mem_src lo loc to' b dset inj I
    from' val' R' t i
    (FULFILL: rtcn (Thread.nprm_step lo) n (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) e_tgt')
    (BOT: Local.promises (Thread.local e_tgt') = Memory.bot)
    (INDSET: dset_get loc t dset = Some i)
    (ACC: Acc index_order i)
    (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_src lc_src sc_src mem_src))
    (RACE_MSG_S: Memory.get loc to' mem_src = Some (from', Message.concrete val' R'))
    (NOT_PROM_S: Memory.get loc to' (Local.promises lc_src) = None)
    (RACE_S: Time.lt (View.rlx (TView.cur (Local.tview lc_src)) loc) to')
    (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                        Thread.is_abort e_src' lo))
    (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
    (MEM_CLOSED: Memory.closed mem_tgt)
    (LOCAL_WF_S: Local.wf lc_src mem_src)
    (MEM_CLOSED: Memory.closed mem_src)
    (MONOTONIC_INJ: monotonic_inj inj)
    (WELL_FOUNDED: well_founded index_order)
    (WF_I: wf_I I),
  exists st_src' lc_src' sc_src' mem_src' e_src' stw_src' val0,
    <<PRE_S: rtc (Thread.nprm_step lo) (Thread.mk lang st_src lc_src sc_src mem_src)
                 (Thread.mk lang st_src' lc_src' sc_src' mem_src')>> /\
    <<WRITE_S: Language.step lang (ProgramEvent.write loc val0 Ordering.plain) st_src' stw_src'>> /\ 
    <<RACE_MSG_S': Memory.get loc to' mem_src' = Some (from', Message.concrete val' R')>> /\
    <<NOT_PROM_S': Memory.get loc to' (Local.promises lc_src') = None>> /\
    <<VIEW_S': Time.lt (View.rlx (TView.cur (Local.tview lc_src')) loc) to'>> /\
    <<FULFILL_S: rtc (Thread.nprm_step lo)
                     (Thread.mk lang st_src' lc_src' sc_src' mem_src') e_src'>> /\ 
    <<BOT_S: Local.promises (Thread.local e_src') = Memory.bot>>.
Proof.
  ii.
  eapply nprm_steps_fulfill_implies_no_scfence_nprm_step_fulfill in FULFILL; eauto.
  des.
  eapply rtc_rtcn in FULFILL. des.
  eapply source_ww_race_construction2' in FULFILL; eauto.
Qed.
  
Lemma source_ww_race_construction:
  forall n lang st_tgt lc_tgt sc_tgt mem_tgt e_tgt'
    index index_order 
    st_src lc_src sc_src mem_src lo loc val to' b dset inj stw_tgt I
    from' val' R'
    (TGT_WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) st_tgt stw_tgt)
    (FULFILL: rtcn (Thread.nprm_step lo) n (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) e_tgt')
    (BOT: Local.promises (Thread.local e_tgt') = Memory.bot)
    (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_src lc_src sc_src mem_src))
    (RACE_MSG_S: Memory.get loc to' mem_src = Some (from', Message.concrete val' R'))
    (NOT_PROM_S: Memory.get loc to' (Local.promises lc_src) = None)
    (RACE_S: Time.lt (View.rlx (TView.cur (Local.tview lc_src)) loc) to')
    (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                        Thread.is_abort e_src' lo))
    (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
    (MEM_CLOSED: Memory.closed mem_tgt)
    (LOCAL_WF_S: Local.wf lc_src mem_src)
    (MEM_CLOSED: Memory.closed mem_src)
    (MONOTONIC_INJ: monotonic_inj inj)
    (WELL_FOUNDED: well_founded index_order)
    (WF_I: wf_I I),
  exists st_src' lc_src' sc_src' mem_src' e_src' stw_src' val0,
    <<PRE_S: rtc (Thread.nprm_step lo) (Thread.mk lang st_src lc_src sc_src mem_src)
                 (Thread.mk lang st_src' lc_src' sc_src' mem_src')>> /\
    <<WRITE_S: Language.step lang (ProgramEvent.write loc val0 Ordering.plain) st_src' stw_src'>> /\ 
    <<RACE_MSG_S': Memory.get loc to' mem_src' = Some (from', Message.concrete val' R')>> /\
    <<NOT_PROM_S': Memory.get loc to' (Local.promises lc_src') = None>> /\
    <<VIEW_S': Time.lt (View.rlx (TView.cur (Local.tview lc_src')) loc) to'>> /\
    <<FULFILL_S: rtc (Thread.nprm_step lo)
                     (Thread.mk lang st_src' lc_src' sc_src' mem_src') e_src'>> /\ 
    <<BOT_S: Local.promises (Thread.local e_src') = Memory.bot>>.
Proof.
  induction n; ii.
  - (* target has fulfilled all its promises *)
    inv FULFILL; ss.
    assert (TGT_PROM_CONS: Local.promise_consistent lc_tgt).
    {
      unfold Local.promise_consistent.
      rewrite BOT. ii. rewrite Memory.bot_get in PROMISE. ss.
    }
    lets PROGRESS: TGT_WRITE.
    eapply write_not_abort_progress with (lo := lo) (sc := sc_tgt) (lc := lc_tgt) in PROGRESS; eauto.
    des.
    inv LOCAL_SIM; ss.

    (* source abort *)
    contradiction SAFE.
    eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
    exists e_src. split; eauto.

    (* source not abort *)
    clear RELY_STEP THRD_DONE THRD_ABORT.
    exploit THRD_STEP.
    eapply Thread.step_program.
    econs. 
    instantiate (2 := ThreadEvent.write loc from to val None Ordering.plain). ss. eauto.
    eapply Local.step_write; eauto.
    ii. des. clear H H1 H2 THRD_STEP. ss.
    exploit H0; eauto. clear H0. ii; des.

    assert (DSET_ADD: exists i, dset_get loc to dset1 = Some i).
    {
      inv H; ss. inv NA_WRITE.
      eapply dset_get_gss.
    }
    des.
    exploit na_steps_dset_race_or_not; [eapply H0 | eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..].
    ii; des.
    {
      (* current source steps will generate race *)
      assert (TGT_LC_BOT': Local.promises lc' = Memory.bot).
      {
        clear - BOT PROGRESS.
        inv PROGRESS; ss. inv WRITE. inv PROMISE.
        exploit MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
        ii; subst; eauto.
      }

      exploit na_steps_dset_to_Thread_na_steps; [eapply H0 | eauto..].
      introv NA_STEPS_S.
      
      destruct e_src'.
      exploit lsim_ensures_promise_fulfill_T_BOT;
        [eapply MONOTONIC_INJ | eapply WELL_FOUNDED | eapply TGT_LC_BOT' | | | eapply H2 | eauto..]. 
      {
        eapply local_wf_write; eauto.
      }
      {
        eapply write_step_closed_mem; eauto.
      }
      {
        ii; des.
        contradiction SAFE.
        exists e_src'.
        split; eauto. 
        eapply Thread_tau_steps_is_all_steps in H3. 
        eapply rtc_compose; [ | eapply H3 | eauto..].
        eapply na_steps_is_tau_steps in NA_STEPS_S.
        eapply Thread_tau_steps_is_all_steps; eauto.
      }
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply rtc_rtcn in NA_STEPS_S. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in NA_STEPS_S; eauto.
      }
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in NA_STEPS_S.
        eapply rtc_rtcn in NA_STEPS_S. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in NA_STEPS_S; eauto.
      } 
      {
        unfold Memory.le; ii; eauto.
      }

      instantiate (1 := sc). ii; des.
      lets RACE_WRITE: RACE0.
      inv RACE_WRITE; ss.
      exists st1 lc1 sc1 mem1. exists e_srcc' st2 v. 
      split.
      {
        eapply Thread_na_steps_to_nprm_steps in RACE. eapply RACE.
      }
      split; eauto.
      eapply na_steps_is_tau_steps in RACE.
      eapply Thread_tau_steps_is_all_steps in RACE.
      exploit race_message_stable; [eapply RACE | eauto..]. ii; des.
      split; eauto. split; eauto. split; eauto.
      split; eauto.
      eapply Relation_Operators.rt1n_trans.
      econs. econs; eauto. ss; eauto. ss. eauto.
      eapply Thread_na_steps_to_nprm_steps in RACE2.
      eapply rtc_compose; [eapply RACE2 | eauto..].
    }
    {
      (* current source steps will not generate race *)
      eapply na_steps_dset_to_Thread_na_steps in H0.
      destruct e_src'; ss.
      assert (RACE_MSG_PRSV: Memory.get loc to' memory = Some (from', Message.concrete val' R') /\
                             Memory.get loc to' (Local.promises local) = None).
      {
        eapply race_message_stable; [| eapply RACE_MSG_S | eapply NOT_PROM_S].
        eapply na_steps_is_tau_steps in H0.
        eapply Thread_tau_steps_is_all_steps in H0. eapply H0.
      }
      des.

      eapply H1 in NOT_RACE0. des; ss.
      lets WF_INDEX: WELL_FOUNDED.
      unfold well_founded in WF_INDEX. specialize (WF_INDEX i).  
      eapply source_ww_race_construction1 in H2; eauto.
      des.

      exists st_src' lc_src' sc_src' mem_src'. exists e_src' stw_src' val0.
      split.
      {
        eapply Thread_na_steps_to_nprm_steps in H0.
        eapply rtc_compose; [eapply H0 | eapply PRE_S].
      }
      split; eauto.
      {
        clear - BOT PROGRESS.
        inv PROGRESS; ss. inv WRITE; ss. inv PROMISE.
        exploit MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
        ii; subst; eauto.
      }
      {
        introv ABORT. destruct ABORT as (e_src' & PSTEP_S & ABORT_S).
        contradiction SAFE.
        exists e_src'. split; eauto.
        eapply na_steps_is_tau_steps in H0.
        eapply Thread_tau_steps_is_all_steps in H0.
        eapply rtc_compose; [eapply H0 | eapply PSTEP_S].
      }
      {
        eapply local_wf_write; eauto.
      } 
      {
        eapply write_step_closed_mem; eauto.
      }
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in H0.
        eapply rtc_rtcn in H0; des.
        eapply no_scfence_nprm_steps_prsv_local_wf in H0; eauto.
      }
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in H0.
        eapply rtc_rtcn in H0; des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in H0; eauto.
      }
    }

    destruct (lo loc) eqn: AT_OR_NA_LOC; eauto.
    contradiction SAFE. 
    eapply na_write_on_atomic_loc_is_abort in PROGRESS; eauto.
    inv LOCAL_SIM; ss.
    {
      eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS; eauto.
    }
    {
      exploit THRD_ABORT; eauto. ii; des.
      eapply na_steps_is_tau_steps in H.
      eapply Thread_tau_steps_is_all_steps in H.
      eauto.
    }
  - assert (TGT_PROM_CONS: Local.promise_consistent lc_tgt).
    {
      eapply rtcn_rtc in FULFILL.
      eapply nprm_steps_to_bot_promise_consistent in FULFILL; eauto.
    }
    inv FULFILL. inv A12.
    + destruct a2. inv PROG.
      exploit (Language.deterministic lang); [eapply TGT_WRITE | eapply STATE | eauto..]. 
      ii; des; subst; ss. 
      destruct e; ss. inv H. clear STATE.
      inv LOCAL_SIM; ss.

      (* current source thread abort *)
      contradiction SAFE.
      eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS; eauto.

      (* current source thread not abort *)
      clear RELY_STEP THRD_DONE THRD_ABORT.
      exploit THRD_STEP.
      eapply Thread.step_program. econs; eauto.
      ss; eauto.
      clear THRD_STEP. ii; des.
      clear H H1 H2. exploit H0; eauto. ss.
      clear H0. ii; des.

      destruct e_src'; ss.
      assert (LOCAL_WF_S': Local.wf local0 memory0).
      {
        eapply na_steps_dset_to_Thread_na_steps in H0.
        eapply Thread_na_steps_is_no_scfence_nprm_steps in H0.
        eapply rtc_rtcn in H0; des.
        eapply no_scfence_nprm_steps_prsv_local_wf in H0; eauto.
      }
      assert (CLOSED_S': Memory.closed memory0).
      {
        eapply na_steps_dset_to_Thread_na_steps in H0.
        eapply Thread_na_steps_is_no_scfence_nprm_steps in H0.
        eapply rtc_rtcn in H0; des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in H0; eauto.
      }

      assert (DSET_ADD: exists i, dset_get loc0 to dset1 = Some i).
      {
        inv H; ss. inv NA_WRITE.
        eapply dset_get_gss.
      }
      des.
      exploit na_steps_dset_race_or_not; [eapply H0 | eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..]; ss.
      ii; des; ss.
      {
        (* current source steps will generate race *)
        lets RACE_WRITE_S: RACE0.
        inv RACE_WRITE_S; ss.

        (* promise fulfill *)
        eapply lsim_ensures_promise_fulfill
          with (n := n) (e_tgt' := e_tgt') (mem_tgtc := memory) (mem_srcc := memory0) (sc_srcc := sc0) in H2; eauto.

        des. eapply rtc_rtcn in H2; des.
        eapply tau_steps_fulfill_implies_nprm_steps_fulfill in H2; eauto; ss.
        des.
        exists st1 lc1 sc1 mem1. exists e0 st2 v.
        split.
        {
          eapply Thread_na_steps_to_nprm_steps in RACE. eapply RACE.
        }
        split; eauto. 
        eapply na_steps_is_tau_steps in RACE.
        eapply Thread_tau_steps_is_all_steps in RACE.
        exploit race_message_stable; [eapply RACE | eauto..]. ii; des.
        split; eauto. split; eauto. split; eauto.
        split; eauto.
        eapply Relation_Operators.rt1n_trans.
        econs. econs; eauto. ss; eauto. ss. 
        eapply Thread_na_steps_to_nprm_steps in RACE2.
        eapply rtc_compose; [eapply RACE2 | eauto..].

        inv LOCAL; ss.
        eapply local_wf_write; eauto.

        inv LOCAL; ss.
        eapply write_step_closed_mem; eauto.

        unfold Memory.le. ii; eauto.

        introv GET_NONE GET_MSG. rewrite GET_NONE in GET_MSG; ss.

        (* source thread not abort *)
        introv ABORT_S. destruct ABORT_S as (e_src' & PSTEPS_S & ABORT_S).
        contradiction SAFE.
        exists e_src'. split; eauto.
        eapply na_steps_dset_to_Thread_na_steps in H0.
        eapply na_steps_is_tau_steps in H0.
        eapply Thread_tau_steps_is_all_steps in H0.
        eapply Thread_tau_steps_is_all_steps in PSTEPS_S.
        eapply rtc_compose; [eapply H0 | eapply PSTEPS_S].

        unfold Memory.le. ii; eauto.
        
        introv GET_NONE GET_MSG.
        rewrite GET_NONE in GET_MSG. ss.

        assert (TGT_PROM_CONS': Local.promise_consistent local).
        {
          inv LOCAL.
          eapply rtcn_rtc in A23.
          eapply nprm_steps_to_bot_promise_consistent in A23; eauto; ss.
          eapply local_wf_write; eauto.
          eapply write_step_closed_mem; eauto.
        }
        inv H2; ss.
        contradiction SAFE.
        eapply na_steps_dset_to_Thread_na_steps in H0.
        eapply na_steps_is_tau_steps in H0.
        eapply Thread_tau_steps_is_all_steps in H0. 
        eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
        exists e_src. split; eauto. eapply rtc_compose; [eapply H0 | eapply NP_STEPS].
        clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
        inv STEP_INV0. ii.
        unfold Mem_at_eq in ATOMIC_COVER.
        eapply ATOMIC_COVER in H2. unfold Mem_approxEq_loc in H2. des.
        eapply H4 in H3. eauto.
      }
      {
        (* source current steps will not generate race *)
        eapply H1 in NOT_RACE0. des.
        eapply na_steps_dset_to_Thread_na_steps in H0.
        exploit race_message_stable; [| eapply RACE_MSG_S | eapply NOT_PROM_S | eauto..].
        eapply na_steps_is_tau_steps in H0.
        eapply Thread_tau_steps_is_all_steps in H0. eapply H0.
        introv RACE_MSG_S'. des.

        eapply source_ww_race_construction2 with (n := n) (e_tgt' := e_tgt') in H2; eauto.
        {
          des.
          exists st_src' lc_src' sc_src' mem_src'. exists e_src' stw_src' val1.
          split; eauto.
          {
            eapply Thread_na_steps_to_nprm_steps in H0.
            eapply rtc_compose; eauto.
          }
          split; eauto.
        }
        {
          introv ABORT_S. destruct ABORT_S as (e_src' & PSTEPS_S & ABORT_S).
          contradiction SAFE.
          exists e_src'; eauto.
          eapply na_steps_is_tau_steps in H0.
          eapply Thread_tau_steps_is_all_steps in H0.
          split; eauto.
          eapply rtc_compose; eauto.
        }
        {
          inv LOCAL.
          eapply local_wf_write; eauto.
        }
        {
          inv LOCAL.
          eapply write_step_closed_mem; eauto.
        }
      }
    + destruct a2.
      inv LOCAL_SIM; ss.

      (* source thread abort *)
      contradiction SAFE.
      eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS; eauto.

      (* source thread will not abort *)
      clear RELY_STEP THRD_DONE THRD_ABORT.
      exploit THRD_STEP.
      econs. eauto. clear THRD_STEP.
      ii; des. clear H H0 H1.
      exploit H2; eauto. inv PF. ss. eauto. clear H2.
      ii; des.
      destruct e_src'.
      assert (RACE_MSG_PRSV: Memory.get loc to' memory0 = Some (from', Message.concrete val' R') /\
                             Memory.get loc to' (Local.promises local0) = None).
      {
        eapply race_message_stable; [ | eapply RACE_MSG_S | eapply NOT_PROM_S].
        eapply Thread_pf_promise_steps_is_nprm_steps with (lo := lo) in H.
        eapply Thread_nprm_step_is_tau_step in H.
        eapply Thread_tau_steps_is_all_steps in H. eapply H.
      }
      des.
      assert (st_tgt = state).
      {
        inv PF. eauto.
      }
      subst state.
      eapply IHn in H0; eauto.
      {
        des.
        exists st_src' lc_src' sc_src' mem_src'. exists e_src' stw_src' val0.
        split; eauto.
        eapply Thread_pf_promise_steps_is_nprm_steps with (lo := lo) in H.
        eapply rtc_compose; eauto.
        split; eauto.
      }
      {
        eapply pf_promise_steps_tview_unchange in H; ss.
        rewrite <- H; eauto.
      }
      {
        introv ABORT_S. des.
        contradiction SAFE.
        eapply Thread_pf_promise_steps_is_nprm_steps with (lo := lo) in H.
        eapply Thread_nprm_step_is_tau_step in H.
        eapply Thread_tau_steps_is_all_steps in H.
        exists e_src'. split; eauto.
        eapply rtc_compose; eauto.
      }
      inv PF.
      exploit Local.promise_step_future; eauto. ii; des; eauto.
      inv PF.
      exploit Local.promise_step_future; eauto. ii; des; eauto.
      eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
      eapply rtc_rtcn in H; des.
      eapply no_scfence_nprm_steps_prsv_local_wf in H; eauto.
      eapply pf_promise_steps_is_no_scfence_nprm_steps with (lo := lo) in H.
      eapply rtc_rtcn in H; des.
      eapply no_scfence_nprm_steps_prsv_memory_closed in H; eauto.
Qed.
      
Lemma ww_rf_preservation_aux_cur_race
      (index: Type) (index_order: index -> index -> Prop)
      (I: Invariant) (lo: Ordering.LocOrdMap) inj
      (ths_tgt ths_src: Threads.t) (sc_tgt sc_src: TimeMap.t) (mem_tgt mem_src: Memory.t)
      (ctid: IdentMap.key)
      (WELL_FOUNDED_ORDER: well_founded index_order)
      (WELL_FORMED_INV: wf_I I)
      (AUX_WW_RACE: aux_ww_race lo (Configuration.mk ths_tgt ctid sc_tgt mem_tgt))
      (LOCAL_SIM: 
         forall lang st_tgt lc_tgt,
           IdentMap.find ctid ths_tgt = Some (existT _ lang st_tgt, lc_tgt) ->
           exists st_src lc_src,
             IdentMap.find ctid ths_src = Some (existT _ lang st_src, lc_src) /\
             @local_sim_state index index_order lang I lo inj dset_init true
                              (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                              (Thread.mk lang st_src lc_src sc_src mem_src) /\
             <<TGT_PROM_CONS: Local.promise_consistent lc_tgt>>)
      (SAFE: ~ (exists npc,
                   rtc (NPConfiguration.all_step lo)
                       (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) true) npc /\
                   Configuration.is_abort (NPConfiguration.cfg npc) lo))
      (MONOTONIC_INJ: monotonic_inj inj)
      (WF_CONFIG_TGT: Configuration.wf (Configuration.mk ths_tgt ctid sc_tgt mem_tgt))
      (WF_CONFIG_SRC: Configuration.wf (Configuration.mk ths_src ctid sc_src mem_src))
  :
    aux_ww_race lo (Configuration.mk ths_src ctid sc_src mem_src).
Proof.
  inv AUX_WW_RACE.
  exploit LOCAL_SIM; [eapply CTID | eauto..].
  ii; des.
  eapply thread_all_step_to_NPThread_all_steps_from_outAtmBlk in STEPS. des.
  eapply rtc_rtcn in FULFILL. des.
  eapply tau_steps_fulfill_implies_nprm_steps_fulfill in FULFILL; eauto. des. 
  eapply not_abort_implies_thread_safe with (st := st_src) (lc := lc_src) in SAFE; eauto.

  (* sim holds when target race *) 
  exploit sim_all_steps; [eapply STEPS | eapply H0 | eauto..].

  eapply wf_config_to_local_wf; eauto.
  ss. inv WF_CONFIG_TGT; ss; eauto.
  ss. inv WF_CONFIG_TGT; ss; eauto.
  ss.
  eapply nprm_steps_to_bot_promise_consistent in FULFILL; eauto.
  ss. 

  ss.
  eapply NPThread_all_steps_to_Thread_all_steps in STEPS.
  exploit wf_config_rtc_thread_steps_prsv; [| eapply CTID | eapply STEPS | eauto..]. eauto.
  ii. inv H1; ss. inv WF.
  eapply THREADS with (tid := ctid); eauto.
  rewrite IdentMap.gss; eauto.

  ss.
  eapply NPThread_all_steps_to_Thread_all_steps in STEPS.
  exploit wf_config_rtc_thread_steps_prsv; [| eapply CTID | eapply STEPS | eauto..]. eauto.
  ii. inv H1; ss.
  
  ii; des.
  (* race message exists at last switch point *)
  exploit race_message_in_starting_mem; [ | eapply RC_MSG | eapply RC_MSG0 | eapply WWRC | eauto..].
  {
    eapply NPThread_all_steps_to_Thread_all_steps in STEPS. eauto.
  }
  {
    clear - CTID WF_CONFIG_TGT.
    inv WF_CONFIG_TGT; ss. inv WF.
    eapply THREADS in CTID; eauto.
  }
  {
    inv WF_CONFIG_TGT; eauto.
  }
  {
    inv WF_CONFIG_TGT; eauto.
  }
  introv RACE_POINT.
  destruct RACE_POINT as (MEM_RACE_MSG0 & NOT_IN_PROM0).

  (* find source race msg *)
  inv H0; ss.
  contradiction SAFE.
  eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
  exists e_src. split; eauto.
  clear THRD_STEP THRD_DONE THRD_ABORT.
  exploit RELY_STEP; eauto. clear RELY_STEP. ii; des. clear H1.
  unfold wf_I in WELL_FORMED_INV.
  eapply WELL_FORMED_INV in H0. ss. inv H0.
  exploit SOUND; [eapply MEM_RACE_MSG0 | eauto..]. ii; des.
  assert (NOT_IN_S_PROM0: Memory.get loc t' (Local.promises lc_src) = None).
  {
    destruct (Memory.get loc t' (Local.promises lc_src)) eqn:GET_S_PROM; eauto.
    destruct p.
    inv STEP_INV. des.
    inv WF_CONFIG_SRC; ss.
    inv WF.
    eapply THREADS in H; eauto. inv H.
    exploit PROMISES; [eapply GET_S_PROM | eauto..]. ii.
    rewrite H1 in H. inv H.
    inv REL_PROMISES0.
    eapply COMPLETE0 in GET_S_PROM; des.

    clear - GET_S_PROM0 REL_PROMISES.
    unfold dset_subset in REL_PROMISES.
    exploit REL_PROMISES; eauto.
    unfold dset_get, dset_init; ss.
    rewrite DenseOrder.DOMap.gempty; eauto. ii; ss.

    exploit monotonic_inj_implies_injective;
      [eapply MONOTONIC_INJ | eapply H0 | eapply GET_S_PROM | eauto..].
    ii. subst.
    rewrite NOT_IN_PROM0 in GET_S_PROM0. ss.
  }
  
  (* source race msg in target race point *) 
  ii; des. destruct e_src'.
  exploit race_message_stable;
    [ | eapply H1 | eapply NOT_IN_S_PROM0 | eauto..].
  { 
    eapply NPThread_all_steps_to_Thread_all_steps in S_STEPS.
    eapply S_STEPS.
  }
  ii; des.
  renames memory to mem_src', local to lc_src'.

  eapply NPThread_all_steps_to_Thread_all_steps in STEPS.
  exploit wf_config_rtc_thread_steps_prsv; [| eapply CTID | eapply STEPS | eauto..]. eauto.
  introv WF_CONFIG_TGT'.
  eapply NPThread_all_steps_to_Thread_all_steps in S_STEPS.
  exploit wf_config_rtc_thread_steps_prsv; [| eapply H | eapply S_STEPS | eauto..]. eauto.
  introv WF_CONFIG_SRC'.
  assert (TGT_PROM_CONS': Local.promise_consistent lc').
  {
    eapply nprm_steps_to_bot_promise_consistent in FULFILL; eauto; ss.
    eapply wf_config_to_local_wf; eauto.
    instantiate (3 := ctid). rewrite IdentMap.gss; eauto.
    inv WF_CONFIG_TGT'; eauto.
  }

  (* in target race point, source has a race message *)
  lets LOCAL_SIM_PSV': LOCAL_SIM_PSV.
  inv LOCAL_SIM_PSV; ss.
  contradiction SAFE.
  eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
  exists e_src.
  split; eauto.
  eapply rtc_compose. eapply S_STEPS. eapply NP_STEPS.
  clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
  inv STEP_INV0.
  assert (INJ: inj' loc to = Some t').
  {
    eapply INJ_INCR; eauto.
  } 
  exploit VIEW_LE; eauto.
  introv RACE_S.

  (* aux ww-race *) 
  eapply rtc_rtcn in FULFILL. des.
  exploit source_ww_race_construction;
    [eapply WRITE | eapply FULFILL | eapply FULFILL1 | eapply LOCAL_SIM_PSV' |
     eapply H2 | eapply H3 | eapply RACE_S | eauto..].
  {
    clear - S_STEPS SAFE.
    introv WW_RACE_S.
    contradiction SAFE. des.
    exists e_src'.
    split; eauto.
    eapply rtc_compose.
    eapply S_STEPS. eapply WW_RACE_S.
  }
  {
    inv WF_CONFIG_TGT'; ss. inv WF.
    eapply THREADS; eauto.
    instantiate (3 := ctid).
    rewrite IdentMap.gss; eauto.
  }
  {
    inv WF_CONFIG_TGT'; eauto.
  }
  ii. exploit H4; eauto.
  {
    inv WF_CONFIG_SRC'; ss.
    inv WF.
    eapply THREADS with (tid := ctid).
    rewrite IdentMap.gss; eauto.
  }
  {
    inv WF_CONFIG_SRC'; eauto.
  }
  clear H4.
  ii; des.
  eapply Thread_nprm_step_is_tau_step in PRE_S.
  eapply Thread_nprm_step_is_tau_step in FULFILL_S.
  eapply Thread_tau_steps_is_all_steps in PRE_S.
  econs.
  {
    eauto.
  }
  {
    eapply rtc_compose.
    eapply S_STEPS. eapply PRE_S.
  }
  {
    eapply WRITE_S.
  }
  {
    eauto.
  }
  {
    eauto.
  }
  split. eapply FULFILL_S. eauto.

  ss.
  eapply NPThread_all_steps_to_Thread_all_steps in STEPS.
  exploit wf_config_rtc_thread_steps_prsv; [| eapply CTID | eapply STEPS | eauto..]. eauto.
  ii. inv H1; ss. inv WF.
  eapply THREADS with (tid := ctid); eauto.
  rewrite IdentMap.gss; eauto.

  ss.
  eapply NPThread_all_steps_to_Thread_all_steps in STEPS.
  exploit wf_config_rtc_thread_steps_prsv; [| eapply CTID | eapply STEPS | eauto..]. eauto.
  ii. inv H1; ss.
Qed.

(** current thread will not abort *) 
Lemma ww_rf_preservation_aux_cur_not_race:
  forall n (index: Type) (index_order: index -> index -> Prop)
    (I: Invariant) (lo: Ordering.LocOrdMap) inj
    (ths_tgt ths_src: Threads.t) (sc_tgt sc_src: TimeMap.t) (mem_tgt mem_src: Memory.t)
    (ctid: IdentMap.key) npc_tgt b_tgt b_src
    (WELL_FOUNDED_ORDER: well_founded index_order)
    (WELL_FORMED_INV: wf_I I)
    (T_STEPS: rtcn (NPConfiguration.all_step lo) n
                   (NPConfiguration.mk (Configuration.mk ths_tgt ctid sc_tgt mem_tgt) b_tgt) npc_tgt)
    (WW_RACE: ww_race lo (NPConfiguration.cfg npc_tgt))
    (CUR_NOT_RACE: ~ (aux_ww_race lo (Configuration.mk ths_tgt ctid sc_tgt mem_tgt)))
    (READY_THRDS: 
         forall tid (READY_TID: tid <> ctid) lang st_tgt lc_tgt
           (READY_TGT_THD: IdentMap.find tid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
         exists st_src lc_src,
           IdentMap.find tid ths_src = Some (existT _ lang st_src, lc_src) /\ 
           @rely_local_sim_state index index_order lang I lo inj
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_src lc_src sc_src mem_src) /\
           <<R_TGT_PROM_CONS: Local.promise_consistent lc_tgt>>)
      (CUR_THRD: 
         forall lang st_tgt lc_tgt  
           (CUR_TGT_THRD: IdentMap.find ctid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
         exists st_src lc_src dset,
           IdentMap.find ctid ths_src = Some (existT _ lang st_src, lc_src) /\
           @local_sim_state index index_order lang I lo inj dset b_tgt
                            (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                            (Thread.mk lang st_src lc_src sc_src mem_src) /\
           (b_tgt = true -> dset = dset_init) /\
           <<C_TGT_PROM_CONS: Local.promise_consistent lc_tgt>>)
      (CONSISTENTS: NPConfiguration.consistent
                      (NPConfiguration.mk (Configuration.mk ths_tgt ctid sc_tgt mem_tgt) b_tgt) lo)
      (WWRF: ~(exists npc,
                    rtc (NPConfiguration.all_step lo)
                        (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) b_src) npc /\
                    aux_ww_race lo (NPConfiguration.cfg npc)))
      (SAFE: ~(exists npc,
                  rtc (NPConfiguration.all_step lo)
                      (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) b_src) npc /\
                  Configuration.is_abort (NPConfiguration.cfg npc) lo))
      (WF_CONFIG_TGT: Configuration.wf (Configuration.mk ths_tgt ctid sc_tgt mem_tgt))
      (WF_CONFIG_SRC: Configuration.wf (Configuration.mk ths_src ctid sc_src mem_src))
      (WF_ATM_BIT: b_tgt = true -> b_src = true)
      (INV_OUT_ATM: b_tgt = true ->
                    (Mem_at_eq lo mem_tgt mem_src /\ I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)))
      (MONOTONIC_INJ: monotonic_inj inj),
  exists npc_src,
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) b_src) npc_src /\
    ww_race lo (NPConfiguration.cfg npc_src).
Proof.
  induction n; ii.
  - inv T_STEPS; ss.
    clear - WW_RACE CUR_NOT_RACE CONSISTENTS WF_CONFIG_TGT.
    inv WW_RACE.
    contradiction CUR_NOT_RACE. clear CUR_NOT_RACE.
    unfold NPConfiguration.consistent in CONSISTENTS; ss.
    unfold Threads.consistent_nprm in CONSISTENTS.
    lets T_CONSISTENT: CTID.
    eapply CONSISTENTS in T_CONSISTENT.
    eapply Thread_nprm_implies_fulfill in T_CONSISTENT; eauto.
    {
      des.
      econs. eapply CTID.
      eauto. eauto. eauto. eauto.
      split.
      eapply Thread_nprm_step_is_tau_step in T_CONSISTENT.
      eapply T_CONSISTENT. eauto.
    }
    {
      inv WF_CONFIG_TGT; ss.
      inv WF. eauto.
    }
    {
      inv WF_CONFIG_TGT; eauto.
    }
  - inv T_STEPS. inv A12.
    lets CONSISTENTS': H.
    eapply threads_consistent_stable in CONSISTENTS'; eauto. 
    inv H; ss.
    + (* tau step *)
      assert(T_STEPS: rtc (NPAuxThread.tau_step lang lo)
                        (NPAuxThread.mk lang (Thread.mk lang st1 lc1 sc_tgt mem_tgt) b_tgt)
                        (NPAuxThread.mk lang (Thread.mk lang st2 lc2 sc2 m2) b)).
      {
        eapply rtc_n1; [eapply STEPS | eapply STEP].
      }
      
      exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply T_STEPS | eauto..]; eauto.
      introv T_CONFIG_WF'.
      exploit CUR_THRD; [eapply TID1 | eauto..]. ii; des.
      assert (PROM_CONS_T: Local.promise_consistent lc2).
      {
        unfold NPAuxThread.consistent in CONSISTENT.
        eapply consistent_nprm_promise_consistent in CONSISTENT; ss; eauto.
        eapply wf_config_to_local_wf; eauto.
        instantiate (3 := ctid). rewrite IdentMap.gss; eauto.
        inv T_CONFIG_WF'; ss; eauto.
        inv T_CONFIG_WF'; ss; eauto.
      }
      
      exploit sim_tau_steps_aux; [eapply T_STEPS | eauto..]; ss.
      eapply wf_config_to_local_wf; eauto.
      inv WF_CONFIG_TGT; eauto.
      inv WF_CONFIG_TGT; eauto.      
      {
        (* abort *)
        introv S_ABORT. des.
        contradiction SAFE.
        eexists. split; eauto. ss.
        econs; ss. 
        eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_ABORT; ss.
        do 3 eexists.
        split; eauto. 
      }

      ii; des.
      destruct e_src'.
      exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply S_STEPS | eauto..]; eauto.
      introv S_CONFIG_WF'.
      eapply rtc_rtcn in S_STEPS. destruct S_STEPS as (n0 & S_STEPS).
      destruct n0.
      {
        (* source takes zero step *)
        inv S_STEPS; ss.
        eapply IHn with (ths_src := IdentMap.add ctid (existT _ lang state, local) ths_src)
                        (sc_tgt := sc2) (mem_tgt := m2)
                        (sc_src := sc) (mem_src := memory) (b_src := b_src') in A23; eauto.
        {
          destruct A23 as (npc_src & PSTEPS_SRC & WW_RACE_S).
          exists npc_src. split; eauto.
          erewrite IdentMap.gsident in PSTEPS_SRC; eauto.
        }
        {
          eapply NPThread_tau_steps_to_thread_all_steps in T_STEPS.
          introv AUX_WW_RACE.
          contradiction CUR_NOT_RACE.
          inv AUX_WW_RACE.
          rewrite IdentMap.gss in CTID. inv CTID.
          eapply inj_pair2 in H4. subst.
          econs.
          eapply TID1.
          eapply rtc_compose. eapply T_STEPS. eapply STEPS0.
          eauto. eauto. eauto. eauto.
        }
        {
          ii.
          rewrite IdentMap.gso in READY_TGT_THD; eauto.
          rewrite IdentMap.gso; eauto.
          exploit READY_THRDS; [eapply READY_TID | eapply READY_TGT_THD | eauto..].
          ii; des.
          do 2 eexists. split. eauto. split; eauto.
          eapply rtc_rtcn in T_STEPS. des.
          eapply local_sim_rely_condition with (n_tgt := n0) (n_src := 0) (lang2 := lang0); eauto.
          eapply wf_config_to_local_wf; eauto.
          eapply wf_config_to_local_wf; eauto.
          instantiate (4 := ctid). rewrite IdentMap.gss; eauto.
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
          rewrite IdentMap.gss; eauto.
          ii. inv CUR_TGT_THRD. eapply inj_pair2 in H4. subst.
          do 3 eexists.
          split.
          rewrite IdentMap.gss; eauto.
          split. eauto. eauto.
        }
        {
          erewrite IdentMap.gsident; eauto.
        }
        {
          erewrite IdentMap.gsident; eauto.
        }
        {
          ii; subst.
          eapply out_atmblk_I_inj_hold in LOCAL_SIM_PSV; eauto.
          des; eauto.
          contradiction SAFE.
          eexists. split. eauto. ss.
          econs; ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in LOCAL_SIM_PSV; ss.
          exists state local e_src'.
          split; eauto.
        }
      }
      {
        (* source takes multiply steps *)
        exploit Behavior.rtcn_tail; [eapply S_STEPS | eauto..].
        introv S_STEPS_CONS.
        destruct S_STEPS_CONS as (npc & S_STEPS_CONS & S_STEP).
        destruct npc.
        destruct (classic (@thrd_ww_race lang lo (Thread.mk lang state local sc memory))) as
            [THRD_WW_RACE | THRD_NOT_WW_RACE].

        (* source thread ww race *) 
        assert (AUX_WW_RACE_S: aux_ww_race lo (Configuration.mk ths_src ctid sc_src mem_src)).
        {
          inv THRD_WW_RACE.
          eapply rtcn_rtc in S_STEPS.
          eapply NPThread_tau_steps_to_thread_all_steps in S_STEPS.
          assert (rtc (Thread.all_step lo)
                      (Thread.mk lang st_src lc_src sc_src mem_src)
                      (Thread.mk lang st' lc' sc' mem')).
          {
            eapply rtc_compose; [eapply S_STEPS | eapply STEPS0].
          }
          lets WF_CONFIG_T_TEMP: H2.
          eapply wf_config_rtc_thread_steps_prsv in WF_CONFIG_T_TEMP; eauto.
          eapply wf_config_to_local_wf with (tid := ctid) in WF_CONFIG_T_TEMP; eauto.
          Focus 2. rewrite IdentMap.gss; eauto.
          econs. eauto.
          eapply H2.
          eauto. eauto.
          eauto. split; eauto.
        }
        contradiction WWRF.
        eexists. split. eauto. ss.
        
        (* source thread not ww race *)
        assert(CONSISTENT_S: 
                 NPAuxThread.consistent lang (Thread.mk lang state local sc memory) lo).
        {
          eapply promise_certified_prsv; [ | eapply CONSISTENT | eauto..]; eauto;
            try solve [inv T_CONFIG_WF'; eauto];
            try solve [inv S_CONFIG_WF'; eauto].
          {
            clear - SAFE S_STEPS H.
            eapply rtcn_rtc in S_STEPS.
            introv S_ABORT. destruct S_ABORT as (e_src' & S_STEPS_TO_ABORT & S_ABORT).
            contradiction SAFE.
            eexists. split; eauto; ss.
            eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
            econs; ss.
            do 3 eexists.
            split. eapply H.
            split. eapply rtc_compose; [eapply S_STEPS | eapply S_STEPS_TO_ABORT].
            eauto.
          }
          {
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := ctid). erewrite IdentMap.gss; eauto.
          }
          {
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := ctid). erewrite IdentMap.gss; eauto.
          }
        }

        eapply IHn with (ths_src := IdentMap.add ctid (existT _ lang state, local) ths_src)
                        (sc_tgt := sc2) (mem_tgt := m2)
                        (sc_src := sc) (mem_src := memory) (b_src := b_src') in A23; eauto.
        {
          destruct A23 as (npc_src & PSTEPS_SRC & WW_RACE_S).
          exists npc_src. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply PSTEPS_SRC.
          econs.
          eapply NPConfiguration.step_tau; ss.
          eauto.
          eapply rtcn_rtc in S_STEPS_CONS.
          eapply S_STEPS_CONS. eapply S_STEP.
          eauto.
        }
        {
          eapply NPThread_tau_steps_to_thread_all_steps in T_STEPS.
          introv AUX_WW_RACE.
          contradiction CUR_NOT_RACE.
          inv AUX_WW_RACE.
          rewrite IdentMap.gss in CTID. inv CTID.
          eapply inj_pair2 in H4. subst.
          econs.
          eapply TID1.
          eapply rtc_compose. eapply T_STEPS. eapply STEPS0.
          eauto. eauto. eauto. eauto.
        }
        {
          ii.
          rewrite IdentMap.gso in READY_TGT_THD; eauto.
          rewrite IdentMap.gso; eauto.
          exploit READY_THRDS; [eapply READY_TID | eapply READY_TGT_THD | eauto..].
          ii; des.
          do 2 eexists. split. eauto. split; eauto.
          eapply rtc_rtcn in T_STEPS. des.
          eapply local_sim_rely_condition with (n_tgt := n1) (n_src := S n0) (lang2 := lang0); eauto.
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
          rewrite IdentMap.gss; eauto.
          ii. inv CUR_TGT_THRD. eapply inj_pair2 in H4. subst.
          do 3 eexists.
          split.
          rewrite IdentMap.gss; eauto.
          split. eauto. eauto.
        }
        {
          introv AUX_WW_RACE_S.
          destruct AUX_WW_RACE_S as (npc_src' & PSTEPS_S & AUX_WW_RACE_S).
          contradiction WWRF.
          exists npc_src'. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
          econs.
          eapply NPConfiguration.step_tau; ss.
          eauto. eapply rtcn_rtc in S_STEPS_CONS. eapply S_STEPS_CONS. eauto. eauto.
        }
        {
          introv ABORT_S.
          destruct ABORT_S as (npc_src' & PSTEPS_S & ABORT_S).
          contradiction SAFE.
          exists npc_src'. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
          econs.
          eapply NPConfiguration.step_tau; ss.
          eauto. eapply rtcn_rtc in S_STEPS_CONS. eapply S_STEPS_CONS. eauto. eauto.
        }
        {
          ii; subst b.
          eapply out_atmblk_I_inj_hold in LOCAL_SIM_PSV; eauto.
          des; eauto.
          contradiction SAFE.
          eexists.
          split.
          eapply Operators_Properties.clos_rt1n_step.
          econs.
          eapply NPConfiguration.step_tau; ss.
          eauto. eapply rtcn_rtc in S_STEPS_CONS. eapply S_STEPS_CONS. eauto. eauto.
          ss.
          econs; ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in LOCAL_SIM_PSV; ss.
          exists state local e_src'.
          split; eauto.
          rewrite IdentMap.gss; eauto.
        }
      }
    + (* switch *)
      subst b_tgt.
      destruct (Loc.eq_dec ctid tid2); subst.
      (* switch to the same thread *)
      eauto.

      (* switch to the different thread *)
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
      exploit WF_ATM_BIT; eauto. ii; subst b_src.

      (* discuss whether the new thread will generate ww race *) 
      destruct (classic (aux_ww_race lo (Configuration.mk ths_tgt tid2 sc_tgt mem_tgt)))
               as [TID2_WW_RACE | TID2_NOT_WW_RACE].
      {
        (* new thread will generate ww race  *)
        eapply ww_rf_preservation_aux_cur_race with
            (ths_src := ths_src) (ctid := tid2) (sc_src := sc_src) (mem_src := mem_src)
          in TID2_WW_RACE; eauto.
        eapply aux_wwrace_to_np_wwrace_from_outAtmBlk in TID2_WW_RACE; eauto. des.
        exists npc'. split; eauto.
        eapply Relation_Operators.rt1n_trans.
        2: eapply TID2_WW_RACE.
        econs.
        eapply NPConfiguration.step_sw with (tid2 := tid2); eauto.
        eapply wf_config_sw_prsv; eauto.
        introv TH_TID2.
        rewrite TID2 in TH_TID2.
        inv TH_TID2. eapply inj_pair2 in H3. subst.
        eauto.

        introv ABORT_S.
        destruct ABORT_S as (npc_src' & PSTEPS_S & ABORT_S).
        contradiction SAFE.
        exists npc_src'. split; eauto.
        eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
        econs.
        eapply NPConfiguration.step_sw; ss.
        eauto.
        eapply wf_config_sw_prsv; eauto.
        eapply wf_config_sw_prsv; eauto.
      }
      {
        eapply IHn with (ths_src := ths_src) (sc_src := sc_src)
                        (mem_src := mem_src) (b_src := true) in A23; eauto.
        {
          destruct A23 as (npc_src & PSTEPS_SRC & WW_RACE_S).
          exists npc_src. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply PSTEPS_SRC.
          econs.
          eapply NPConfiguration.step_sw with (tid2 := tid2); eauto; ss.
        }
        {
          ii.
          destruct (Loc.eq_dec tid ctid); subst; eauto.
          (* origin thread *)
          exploit CUR_THRD; [eapply READY_TGT_THD | eauto..]. ii; des.
          exploit H3; eauto. ii; subst.
          exists st_src0 lc_src0.
          split. eauto. split; eauto.
          eapply local_sim_state_to_rely_local_sim_state; eauto.
          instantiate (1 := ctid).
          introv ABORT. destruct ABORT as (npc' & TO_ABORT & ABORT).
          contradiction SAFE. clear SAFE.
          exists npc'.
          split. eauto.
          eapply NPConfig_abort_to_Config_abort; eauto.
        }
        {
          ii.
          rewrite TID2 in CUR_TGT_THRD. inv CUR_TGT_THRD.
          eapply inj_pair2 in H3. subst st2.
          exists st_src lc_src (@dset_init index).
          split; eauto.
        }
        {
          introv AUX_WW_RACE_S.
          destruct AUX_WW_RACE_S as (npc_src' & PSTEPS_S & AUX_WW_RACE_S).
          contradiction WWRF.
          exists npc_src'. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
          econs.
          eapply NPConfiguration.step_sw; ss.
          eauto.
        }
        {
          introv ABORT_S.
          destruct ABORT_S as (npc_src' & PSTEPS_S & ABORT_S).
          contradiction SAFE.
          exists npc_src'. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
          econs.
          eapply NPConfiguration.step_sw; ss; eauto.
        }
        eapply wf_config_sw_prsv; eauto.
        eapply wf_config_sw_prsv; eauto.
      }
    + (* thread term *)
      exploit CUR_THRD; [eapply OLD_TID | eauto..].
      ii; des.
      inv H0; ss.
      (* current source thread will abort *)
      contradiction SAFE.
      eexists. split; eauto; ss.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      econs; eauto; ss.
      exists st_src lc_src e_src.
      split; eauto.

      (* current source thread will not abort *)
      clear THRD_STEP RELY_STEP THRD_ABORT.
      exploit THRD_DONE0; eauto. ii; des.
      assert (NEW_TID_NOT_DONE: tid2 <> ctid).
      {
        ii; subst.
        rewrite IdentMap.grs in NEW_TID_OK; ss.
      }
      rewrite IdentMap.gro in NEW_TID_OK; eauto.
      exploit READY_THRDS; eauto. ii; des.
      exploit na_steps_dset_to_NPThread_tau_steps; eauto.
      instantiate (1 := b_src). introv Hprefix_tau_steps. des.
      eapply rtc_rtcn in Hprefix_tau_steps.
      destruct Hprefix_tau_steps as (n0 & Hprefix_tau_steps).
      destruct n0.
      {
        (* source takes zero prefix step *)
        inv Hprefix_tau_steps. ss.
        (* discuss whether the new thread will generate ww race *)
        destruct (classic (aux_ww_race lo (Configuration.mk (IdentMap.remove ctid ths_tgt) tid2 sc_tgt mem_tgt)))
          as [TID2_WW_RACE | TID2_NOT_WW_RACE].
        (* new thread will generate race *)
        eapply ww_rf_preservation_aux_cur_race with
            (ths_src := IdentMap.remove ctid ths_src) (ctid := tid2) (sc_src := sc_src) (mem_src := mem_src)
            (inj := inj')
          in TID2_WW_RACE; eauto.
        {
          eapply aux_wwrace_to_np_wwrace_from_outAtmBlk in TID2_WW_RACE; eauto.
          des.
          exists npc'. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply TID2_WW_RACE].
          econs.
          eapply NPConfiguration.step_thread_term; ss.
          eauto. eauto.
          rewrite IdentMap.gro; eauto.
          eapply wf_config_rm_prsv; eauto.
        } 
        { 
          repeat (rewrite IdentMap.gro; eauto).
          introv TID2_T.
          exploit READY_THRDS; eauto. ii; des. 
          eapply local_sim_rely_condition with
              (n_tgt := 0) (n_src := 0) (lc_tgt1 := lc1) (lc_src1 := lc_src) in H8; eauto.
          rewrite H5 in H7. inv H7. eapply inj_pair2 in H11. subst.
          eapply rely_local_sim_state_to_local_sim_state in H8; eauto.
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
          clear - WELL_FORMED_INV H4.
          unfold wf_I in WELL_FORMED_INV.
          eapply WELL_FORMED_INV in H4; ss. inv H4; eauto.
        }
        eapply wf_config_rm_prsv; eauto.
        eapply wf_config_rm_prsv; eauto. 

        (* new thread will not generate race *)
        eapply local_sim_rely_condition with
            (n_tgt := 0) (n_src := 0) (lc_tgt1 := lc1) (lc_src1 := lc_src)
          in H6; eauto.
        eapply rely_local_sim_state_to_local_sim_state in H6; eauto.
        eapply IHn with (ths_src := IdentMap.remove ctid ths_src) (sc_src := sc_src)
                        (mem_src := mem_src) (b_src := true) (inj := inj') in A23; eauto.
        {
          destruct A23 as (npc_src & PSTEPS_SRC & WW_RACE_S).
          exists npc_src. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply PSTEPS_SRC.
          econs. 
          eapply NPConfiguration.step_thread_term with (tid2 := tid2); eauto; ss.          
          rewrite IdentMap.gro; eauto.
        } 
        { 
          ii.
          assert (NOT_ORIGIN_TID: tid <> ctid).
          {
            ii; subst.
            rewrite IdentMap.grs in READY_TGT_THD. ss.
          }
          rewrite IdentMap.gro in READY_TGT_THD; eauto.
          rewrite IdentMap.gro; eauto.
          lets READY_TGT_THD_ORIGN: READY_TGT_THD.
          eapply READY_THRDS in READY_TGT_THD; eauto. des.
          eapply local_sim_rely_condition with
              (n_tgt := 0) (n_src := 0) (lc_tgt1 := lc1) (lc_src1 := lc_src)
              (inj' := inj') in READY_TGT_THD0; eauto.
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
          assert (NOT_ORIGIN_TID: tid2 <> ctid).
          {
            ii; subst.
            rewrite IdentMap.grs in CUR_TGT_THRD. ss.
          }
          rewrite IdentMap.gro in CUR_TGT_THRD; eauto.
          rewrite IdentMap.gro; eauto.
          rewrite NEW_TID_OK in CUR_TGT_THRD.
          inv CUR_TGT_THRD. eapply inj_pair2 in H9; eauto. subst.
          do 3 eexists. split; eauto.
        }
        {
          introv AUX_WW_RACE_S.
          destruct AUX_WW_RACE_S as (npc_src' & PSTEPS_S & AUX_WW_RACE_S).
          contradiction WWRF.
          exists npc_src'. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
          econs.
          eapply NPConfiguration.step_thread_term; ss.
          eauto. eauto. rewrite IdentMap.gro; eauto.
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
        eapply wf_config_rm_prsv; eauto.
        eapply wf_config_rm_prsv; eauto.
        {
          ii.
          split; eauto. inv STEP_INV; eauto.
        }
        unfold wf_I in *. eapply WELL_FORMED_INV in H4; ss. inv H4; eauto.
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
        (* source thread will take multiply prefix steps *)
        exploit Behavior.rtcn_tail; [eapply Hprefix_tau_steps | eauto..].
        introv Hprefix_tau_steps'.
        destruct Hprefix_tau_steps' as (npc' & PREFIX_STEPS & PREFIX_STEP).
        destruct npc'. destruct state.
        eapply rtcn_rtc in PREFIX_STEPS.
        assert(CONSISTENT_T: Local.promises (Thread.local e_src) = Memory.bot).
        {
          clear - H2. inv H2. eauto.
        }
        exploit rtcn_rtc; [eapply Hprefix_tau_steps | eauto..]. introv PROFIX_STEPS_TEMP.
        destruct e_src; ss.
        exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply PROFIX_STEPS_TEMP | eauto..]; eauto.
        introv WF_CONFIG_SRC'.
        eapply local_sim_rely_condition with (n_tgt := 0) (n_src := (S n0)) in H6; eauto.
        eapply rely_local_sim_state_to_local_sim_state in H6; eauto.

        (* discuss whether the new thread will generate ww race *)
        destruct (classic (aux_ww_race lo (Configuration.mk (IdentMap.remove ctid ths_tgt) tid2 sc_tgt mem_tgt)))
          as [TID2_WW_RACE | TID2_NOT_WW_RACE].
        (* new thread will generate race *)
        eapply ww_rf_preservation_aux_cur_race with
            (ths_src := IdentMap.remove ctid (IdentMap.add ctid (existT Language.state lang state0, local0) ths_src))
            (ctid := tid2) (sc_src := sc0) (mem_src := memory0) (inj := inj')
          in TID2_WW_RACE; eauto.
        {
          eapply aux_wwrace_to_np_wwrace_from_outAtmBlk in TID2_WW_RACE; eauto.
          des.
          exists npc'. split; eauto.
          eapply Relation_Operators.rt1n_trans.
          econs. 
          eapply NPConfiguration.step_tau. ss.
          ss. eauto. eauto.
          ss. eapply PREFIX_STEPS. eapply PREFIX_STEP. eauto.
          econs; ss. split; eauto.
          eauto.
          ss.
          eapply Relation_Operators.rt1n_trans; [ | eapply TID2_WW_RACE].
          econs.
          eapply NPConfiguration.step_thread_term; ss.
          rewrite IdentMap.gss; eauto. eauto.
          rewrite IdentMap.gro; eauto. rewrite IdentMap.gso; eauto.
          eapply wf_config_rm_prsv; eauto.
        }
        {
          ii. 
          rewrite IdentMap.gro in H7; eauto.
          rewrite IdentMap.gro; eauto. rewrite IdentMap.gso; eauto.
          rewrite NEW_TID_OK in H7. inv H7. eapply inj_pair2 in H10. subst.
          do 2 eexists.
          split; eauto.
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
          unfold wf_I in *.
          eapply WELL_FORMED_INV in H4. inv H4; eauto.
        }
        eapply wf_config_rm_prsv; eauto.
        eapply wf_config_rm_prsv; eauto.

        (* new thread will not generate race *)
        assert (MEM_AT_EQ: Mem_at_eq lo mem_tgt memory0).
        {
          eapply out_atmblk_I_inj_hold in H6; eauto.
          des; eauto.
          contradiction SAFE.
          eexists.
          split.
          eapply Relation_Operators.rt1n_trans.
          clear PROFIX_STEPS_TEMP.
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
          ss. econs; ss.
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in H6; ss.
          do 3 eexists.
          split.
          rewrite IdentMap.gro; eauto. rewrite IdentMap.gso; eauto.
          split. eapply H6. eauto.
        }
        eapply IHn with (ths_src := IdentMap.remove ctid (IdentMap.add ctid (existT _ lang state0, local0) ths_src))
                        (sc_src := sc0)
                        (mem_src := memory0) (b_src := true) (inj := inj') in A23; eauto.
        {
          destruct A23 as (npc_src & PSTEPS_SRC & WW_RACE_S).
          exists npc_src. split; eauto.
          eapply Relation_Operators.rt1n_trans.
          econs. 
          eapply NPConfiguration.step_tau. ss.
          ss. eauto. eauto.
          ss. eapply PREFIX_STEPS. eapply PREFIX_STEP. eauto.
          econs; ss. split; eauto.
          eauto.
          ss.
          eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_SRC].
          econs.
          eapply NPConfiguration.step_thread_term; ss.
          rewrite IdentMap.gss; eauto. eauto.
          rewrite IdentMap.gro; eauto. rewrite IdentMap.gso; eauto.
        }
        {
          ii.
          assert (READY_TGT_NOT_DONE: tid <> ctid).
          {
            ii; subst.
            rewrite IdentMap.grs in READY_TGT_THD. ss.
          }
          rewrite IdentMap.gro in READY_TGT_THD; eauto.
          rewrite IdentMap.gro; eauto. rewrite IdentMap.gso; eauto.
          exploit READY_THRDS; [ | eapply READY_TGT_THD | eauto..]; eauto.
          ii; des.
          eapply local_sim_rely_condition with (n_tgt := 0) (n_src := (S n0)) in H8; eauto.
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
          ii.
          rewrite IdentMap.gro in CUR_TGT_THRD; eauto.
          rewrite NEW_TID_OK in CUR_TGT_THRD. inv CUR_TGT_THRD. eapply inj_pair2 in H9. subst.
          do 3 eexists. split; eauto.
          rewrite IdentMap.gro; eauto.
          rewrite IdentMap.gso; eauto.
        } 
        {
          introv AUX_WW_RACE_S. destruct AUX_WW_RACE_S as (npc' & PSTEPS_S & AUX_WW_RACE_S).
          contradiction WWRF. clear PROFIX_STEPS_TEMP.
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
        eapply wf_config_rm_prsv; eauto.
        eapply wf_config_rm_prsv; eauto.

        unfold wf_I in *. eapply WELL_FORMED_INV in H4; eauto. inv H4; eauto.
        eapply wf_config_to_local_wf; eauto.
        eapply wf_config_to_local_wf; eauto.
        instantiate (3 := tid2). rewrite IdentMap.gso; eauto.
        inv WF_CONFIG_TGT; eauto.
        inv WF_CONFIG_TGT; eauto.
        { 
          inv STEP_INV.
          eapply na_steps_dset_to_Thread_na_steps in H0; eauto.
          eapply Mem_at_eq_na_steps_prsv with (m := mem_tgt) in H0; eauto; ss.
          eapply Mem_at_eq_reflexive; eauto.
          eapply Mem_at_eq_reflexive; eauto.
        }
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
    + (* output *)
      exploit CUR_THRD; [eapply TID1 | eauto..]. ii; des.
      exploit sim_output_steps; [eapply STEP | eauto..]. ii; des.
      {
        (* not abort *)
        destruct e_src'.
        exploit wf_config_NPThread_out_step_prsv; [ | | eapply STEP | eauto..]; eauto.
        introv T_CONFIG_WF'.
        destruct e_src0.
        exploit wf_config_rtc_NPThread_tau_steps_prsv; [ | | eapply S_STEPS | eauto..]; eauto.
        introv S_CONFIG_WF'.
        exploit wf_config_NPThread_out_step_prsv; [ | | eapply S_OUT | eauto..]; eauto.
        instantiate (1 := ctid).
        rewrite IdentMap.gss; eauto.
        introv S_CONFIG_WF''.
        assert (PROM_BOT: Local.promises local = Memory.bot /\ Local.promises local0 = Memory.bot).
        {
          clear - S_OUT. inv S_OUT; ss. inv H.
          inv OUT. inv LOCAL. inv LOCAL0; ss.
          exploit PROMISES; eauto.
        }
        destruct PROM_BOT as (PROM_BOT & PROM_BOT').

        assert (TGT_PROM_CONS': Local.promise_consistent lc2).
        {
          inv STEP; ss. inv H2; ss. inv OUT; ss. inv LOCAL; ss.
          inv LOCAL0; ss. exploit PROMISES; eauto. ii; ss.
          rewrite H2 in PROMISE. rewrite Memory.bot_get in PROMISE. ss.
        }
        eapply rtc_rtcn in S_STEPS. des.
        destruct n0.
        {
          (* source thread takes zero steps *)
          inv S_STEPS.
          exploit out_atmblk_I_inj_hold; eauto.
          ii; des.
          Focus 2.
          contradiction SAFE.
          eexists. split.
          eapply Relation_Operators.rt1n_trans; [ | eauto].
          econs.
          eapply NPConfiguration.step_out; eauto.
          ss. unfold NPAuxThread.consistent; ss; eauto.
          unfold Thread.consistent_nprm; ss; eauto.
          ss. econs; ss.
          exists state local e_src'.
          split; eauto. rewrite IdentMap.gss; eauto.
          split; eauto. 
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in H2; eauto.
          
          eapply IHn with (ths_src := IdentMap.add ctid (existT _ lang state, local) ths_src)
                          (sc_tgt := sc2) (mem_tgt := m2)
                          (sc_src := sc) (mem_src := memory) (b_src := true) (inj := inj') in A23; eauto.
          {
            destruct A23 as (npc_src & PSTEPS_S & WW_RACE_S).
            exists npc_src. split; eauto.
            eapply Relation_Operators.rt1n_trans; [ | eapply PSTEPS_S].
            econs.
            eapply NPConfiguration.step_out; eauto.
            ss.
            econs; eauto.
          }
          {
            introv AUX_WW_RACE_T.
            contradiction CUR_NOT_RACE.
            inv STEP; ss.
            inv AUX_WW_RACE_T.
            rewrite IdentMap.gss in CTID. inv CTID. eapply inj_pair2 in H9. subst.
            econs.
            instantiate (2 := st1). instantiate (1 := lc1). eauto.
            eapply Relation_Operators.rt1n_trans; [ | eapply STEPS].
            eapply out_step_is_all_step; eauto.
            eauto. eauto. eauto. eauto.
          } 
          {
            ii.
            rewrite IdentMap.gso in READY_TGT_THD; eauto.
            rewrite IdentMap.gso; eauto.
            exploit READY_THRDS; [ | eapply READY_TGT_THD | eauto..]; eauto.
            ii; des.
            do 2 eexists.
            split; eauto. split; eauto.
            eapply local_sim_out_rely_condition with (n_src := 0); eauto.
            eapply wf_config_to_local_wf; eauto.
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := ctid). rewrite IdentMap.gss; eauto.
            inv WF_CONFIG_TGT; eauto.
            inv S_CONFIG_WF'; eauto.
            inv WF_CONFIG_TGT; eauto.
            inv S_CONFIG_WF'; eauto.
            eapply wf_config_to_local_wf; eauto. 
            instantiate (3 := tid). rewrite IdentMap.gso; eauto.
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := tid).
            rewrite IdentMap.gso; eauto. rewrite IdentMap.gso; eauto.
            inv T_CONFIG_WF'; eauto.
            inv T_CONFIG_WF'; eauto.
          }
          {
            ii.
            rewrite IdentMap.gss in CUR_TGT_THRD; eauto.
            inv CUR_TGT_THRD. eapply inj_pair2 in H7. subst.
            rewrite IdentMap.gss; eauto.
            do 3 eexists. split; eauto.
          }
          {
            introv AUX_WW_RACE_S.
            destruct AUX_WW_RACE_S as (npc_src & PSTEPS_S & AUX_WW_RACE_S).
            contradiction WWRF.
            exists npc_src. split; eauto.
            econs.
            econs.
            eapply NPConfiguration.step_out; eauto.
            ss. unfold NPAuxThread.consistent; ii; ss; eauto.
            ss.
          }
          {
            introv ABORT_S.
            destruct ABORT_S as (npc_src & PSTEPS_S & ABORT_S).
            contradiction SAFE.
            exists npc_src. split; eauto.
            econs.
            econs.
            eapply NPConfiguration.step_out; eauto.
            ss. unfold NPAuxThread.consistent; ii; ss; eauto.
            ss.
          }
          {
            rewrite IdentMap.add_add_eq in S_CONFIG_WF''; eauto.
          } 
        }
        {
          (* source thread takes multiply steps *)
          exploit Behavior.rtcn_tail; [eapply S_STEPS | eauto..].
          introv Hprefix_tau_steps'.
          destruct Hprefix_tau_steps' as (npc' & PREFIX_STEPS & PREFIX_STEP).
          destruct npc'. destruct state1.
          eapply rtcn_rtc in PREFIX_STEPS.
          
          exploit out_atmblk_I_inj_hold; eauto.
          ii; des.
          Focus 2.
          contradiction SAFE.
          eexists. split.
          eapply Relation_Operators.rt1n_trans.
          econs.
          eapply NPConfiguration.step_tau; eauto.
          unfold NPAuxThread.consistent.
          unfold Thread.consistent_nprm; ss. ii; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eauto].
          ss.
          econs.
          eapply NPConfiguration.step_out; eauto.
          ss. rewrite IdentMap.gss; eauto.
          ss. unfold NPAuxThread.consistent; ss; eauto.
          unfold Thread.consistent_nprm; ss; eauto.
          ss. econs; ss.
          exists state local e_src'.
          split; eauto. rewrite IdentMap.gss; eauto.
          split; eauto. 
          eapply NPAuxThread_tau_steps_2_Thread_tau_steps in H2; eauto.
          
          eapply IHn with (ths_src := IdentMap.add ctid (existT _ lang state, local) ths_src)
                          (sc_tgt := sc2) (mem_tgt := m2)
                          (sc_src := sc) (mem_src := memory) (b_src := true) (inj := inj') in A23; eauto. 
          {
            destruct A23 as (npc_src & PSTEPS_S & WW_RACE_S).
            exists npc_src. split; eauto.
            eapply Relation_Operators.rt1n_trans.
            econs.
            eapply NPConfiguration.step_tau; eauto.
            unfold NPAuxThread.consistent.
            unfold Thread.consistent_nprm; eauto.
            ss.
            eapply Relation_Operators.rt1n_trans.
            econs.
            eapply NPConfiguration.step_out; eauto.
            ss. rewrite IdentMap.gss; eauto.
            ss. unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; ss.
            ii. eauto.
            ss; eauto.
            rewrite IdentMap.add_add_eq; eauto.
          }
          {
            introv AUX_WW_RACE_T.
            contradiction CUR_NOT_RACE.
            inv AUX_WW_RACE_T.
            rewrite IdentMap.gss in CTID. inv CTID. eapply inj_pair2 in H7. subst.
            inv STEP; ss.
            econs. eauto.
            eapply Relation_Operators.rt1n_trans; [ | eapply STEPS | eauto..].
            eapply out_step_is_all_step; eauto.
            eauto. eauto. eauto. eauto.
          } 
          {
            ii.
            rewrite IdentMap.gso in READY_TGT_THD; eauto.
            rewrite IdentMap.gso; eauto.
            exploit READY_THRDS; [| eapply READY_TGT_THD | eauto..]; eauto.
            ii; des.
            do 2 eexists.
            split; eauto. split; eauto.
            eapply local_sim_out_rely_condition with (n_src := S n0); eauto.
            eapply wf_config_to_local_wf; eauto.
            eapply wf_config_to_local_wf; eauto.
            inv WF_CONFIG_TGT; eauto.
            inv WF_CONFIG_SRC; eauto.
            inv WF_CONFIG_TGT; eauto.
            inv WF_CONFIG_SRC; eauto.
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := tid). rewrite IdentMap.gso; eauto.
            eapply wf_config_to_local_wf; eauto.
            instantiate (3 := tid). rewrite IdentMap.gso; eauto. rewrite IdentMap.gso; eauto.
            inv T_CONFIG_WF'; eauto.
            inv T_CONFIG_WF'; eauto.
          }
          {
            ii.
            rewrite IdentMap.gss in CUR_TGT_THRD; eauto.
            inv CUR_TGT_THRD. eapply inj_pair2 in H7. subst.
            do 3 eexists.
            split; eauto.
            rewrite IdentMap.gss; eauto.
          }
          {
            introv AUX_WW_RACE_S.
            destruct AUX_WW_RACE_S as (npc_src & PSTEPS_S & AUX_WW_RACE_S).
            contradiction WWRF.
            exists npc_src. split; eauto.
            econs.
            econs.
            eapply NPConfiguration.step_tau; eauto.
            unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; eauto.
            ss.
            econs. econs.
            eapply NPConfiguration.step_out; eauto.
            ss. rewrite IdentMap.gss; eauto.
            ss. unfold NPAuxThread.consistent; ii; ss; eauto.
            ss. rewrite IdentMap.add_add_eq; eauto.
          }
          {
            introv ABORT_S.
            destruct ABORT_S as (npc_src & PSTEPS_S & ABORT_S).
            contradiction SAFE.
            exists npc_src. split; eauto.
            econs.
            econs.
            eapply NPConfiguration.step_tau; eauto.
            unfold NPAuxThread.consistent. unfold Thread.consistent_nprm; eauto.
            ss.
            econs. econs.
            eapply NPConfiguration.step_out; eauto.
            ss. rewrite IdentMap.gss; eauto.
            ss. unfold NPAuxThread.consistent; ii; ss; eauto.
            ss. rewrite IdentMap.add_add_eq; eauto.
          }
          {
            rewrite IdentMap.add_add_eq in S_CONFIG_WF''; eauto.
          }
        }
      }
      {
        contradiction SAFE.
        eexists. split; eauto; ss.
        econs; ss.
        eapply NPAuxThread_tau_steps_2_Thread_tau_steps in S_STEPS; ss.
        do 3 eexists.
        split; eauto.
      }
      Unshelve.
      exact st2.
      exact true.
      exact lang0.
      exact st_tgt.
      exact true.
      exact st_tgt.
      exact true.
      exact lang.
      exact st_src0.
      exact true.
      exact st_src0.
      exact true.
      exact lang0.
      exact st_tgt.
      exact true.
      exact st_tgt.
      exact true.
      exact state.
      exact true.
      exact state.
      exact true.
Qed.

(** ww-race preservation proof *)
Lemma ww_RF_preservation_aux
      (index: Type) (index_order: index -> index -> Prop)
      (I: Invariant) (lo: Ordering.LocOrdMap) inj
      (ths_tgt ths_src: Threads.t) (ctid: IdentMap.key)
      (sc_tgt sc_src: TimeMap.t) (mem_tgt mem_src: Memory.t) npc_tgt
      (WELL_FOUNDED_ORDER: well_founded index_order)
      (WELL_FORMED_INV: wf_I I)
      (T_STEPS: rtc (NPConfiguration.all_step lo)
                    (NPConfiguration.mk (Configuration.mk ths_tgt ctid sc_tgt mem_tgt) true) npc_tgt)
      (WW_RACE: ww_race lo (NPConfiguration.cfg npc_tgt))
      (READY_THRDS: 
         forall tid (READY_TID: tid <> ctid) lang st_tgt lc_tgt
           (READY_TGT_THD: IdentMap.find tid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
         exists st_src lc_src,
           IdentMap.find tid ths_src = Some (existT _ lang st_src, lc_src) /\ 
           @rely_local_sim_state index index_order lang I lo inj
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_src lc_src sc_src mem_src) /\
           <<R_PROM_CONS_T: Local.promise_consistent lc_tgt>>)
      (CUR_THRD: 
         forall lang st_tgt lc_tgt  
           (CUR_TGT_THRD: IdentMap.find ctid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)),
         exists st_src lc_src,
           IdentMap.find ctid ths_src = Some (existT _ lang st_src, lc_src) /\
           @local_sim_state index index_order lang I lo inj dset_init true
                            (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                            (Thread.mk lang st_src lc_src sc_src mem_src) /\
           <<C_PROM_CONS_T: Local.promise_consistent lc_tgt>>)
      (CONSISTENTS: NPConfiguration.consistent
                      (NPConfiguration.mk (Configuration.mk ths_tgt ctid sc_tgt mem_tgt) true) lo)
      (SAFE: ~(exists npc,
                  rtc (NPConfiguration.all_step lo)
                      (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) true) npc /\
                  Configuration.is_abort (NPConfiguration.cfg npc) lo))
      (WWRF: ~(exists npc,
                    rtc (NPConfiguration.all_step lo)
                        (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) true) npc /\
                    aux_ww_race lo (NPConfiguration.cfg npc)))
      (WF_CONFIG_TGT: Configuration.wf (Configuration.mk ths_tgt ctid sc_tgt mem_tgt))
      (WF_CONFIG_SRC: Configuration.wf (Configuration.mk ths_src ctid sc_src mem_src))
      (INV_OUT_ATM: Mem_at_eq lo mem_tgt mem_src /\ I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (MONOTONIC_INJ: monotonic_inj inj):
  exists npc_src,
    rtc (NPConfiguration.all_step lo)
        (NPConfiguration.mk (Configuration.mk ths_src ctid sc_src mem_src) true) npc_src /\
    ww_race lo (NPConfiguration.cfg npc_src).
Proof.
  destruct (classic (aux_ww_race lo (Configuration.mk ths_tgt ctid sc_tgt mem_tgt))) as
      [CUR_WILL_RACE | CUR_WILL_NOT_RACE].
  {
    (* current thread will race *)
    eapply ww_rf_preservation_aux_cur_race in CUR_WILL_RACE; eauto.
    eapply sound_np_aux_wwrace. eauto.
    split. eauto. ss.
  }
  {
    (* current thread will not abort *)
    eapply rtc_rtcn in T_STEPS. des.
    eapply ww_rf_preservation_aux_cur_not_race; eauto.
    introv CTH.
    eapply CUR_THRD in CTH; eauto. des.
    do 3 eexists.
    split; eauto.
  }
Qed.

(** ** Write-write race freedom preservation *)
(** It depicts that, if
    - [LOCAL_SIM]: local simulation holds;
    - [SAFE_NP_SRC]: source program is safe;
    - [WW_RF_NP_SRC]: source program is write-write race free;
    then the target program is write-write race free. *)
Lemma ww_RF_preservation
      (lang: language) (index: Type) (index_order: index -> index -> Prop)
      (I: Invariant) (lo: Ordering.LocOrdMap)
      (code_t code_s: Language.syntax lang) (fs: list IdentMap.key) (ctid: IdentMap.key)
      (LOCAL_SIM: @local_sim index index_order lang I lo code_t code_s)
      (SAFE_NP_SRC: NPConfiguration.safe lo fs code_s ctid)
      (WW_RF_NP_SRC: ww_rf_np lo fs code_s ctid):
  ww_rf_np lo fs code_t ctid.
Proof.
  inv LOCAL_SIM.
  unfold ww_rf_np. introv ww_Race_np_tgt.
  unfold ww_rf_np in WW_RF_NP_SRC.
  contradiction WW_RF_NP_SRC.
  inv ww_Race_np_tgt.

  (* destruct the target initial state *)
  unfolds NPConfiguration.init.
  destruct (Configuration.init fs code_t ctid) eqn:H_tgt_init; tryfalse.
  inv NPLOAD. 
  renames t to c_tgt.

  (* construct the source initial state *)
  lets H_src_init : H_tgt_init.
  eapply cons_source_init_from_target_init_program in H_src_init; eauto.
  destruct H_src_init as (c_src & H_src_init & Htgt_2_src & Hsrc_2_tgt).

  (* construct ww_race in source *)
  destruct c_tgt; ss. destruct c_src; ss.
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
  
  eapply ww_RF_preservation_aux in STEPS; eauto.
  instantiate (3 := ths_src) in STEPS.
  instantiate (2 := TimeMap.bot) in STEPS.
  instantiate (1 := Memory.init) in STEPS.
  des.
  econs; eauto.

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
  split.
  eapply local_sim_state_to_rely_local_sim_state; eauto.
  instantiate (1 := ctid).
  clear - SAFE_NP_SRC NP_CONFIG_INIT.
  inv SAFE_NP_SRC.
  eapply SAFE_EXEC in NP_CONFIG_INIT. ii. des.
  contradiction NP_CONFIG_INIT. econs; eauto.
  unfold Local.promise_consistent, Local.init. ii; ss.
  rewrite Memory.bot_get in PROMISE. ss.
  unfold Local.promise_consistent, Local.init. ii; ss.
  rewrite Memory.bot_get in PROMISE. ss.

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
  do 2 eexists.
  split; eauto.
  split; eauto.
  unfold Local.promise_consistent, Local.init. ii; ss.
  rewrite Memory.bot_get in PROMISE. ss.

  (* consistent *)
  unfold NPConfiguration.consistent; ss.
  unfold Threads.consistent_nprm. intros.
  assert (lang0 = lang).
  {
    clear - Hths_tgt_init TH.
    eapply thread_init_same_lang in Hths_tgt_init; eauto.
  }
  subst.
  eapply thread_init_lc_init with (fs := fs) (code := code_t) in TH; eauto.
  subst.
  unfold Thread.consistent_nprm; ss. ii.
  eexists. split. eauto. ss.

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

  (* Source aux safe *)
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

  (* well-formed target configuraiton in initialization *)
  eapply wf_config_init with (fs := fs) (code := code_t) (ctid := ctid); eauto.
  unfold Configuration.init.
  rewrite Hths_tgt_init; eauto.

  (* well-formed source configuraiton in initialization *)
  eapply wf_config_init with (fs := fs) (code := code_s) (ctid := ctid); eauto.
  unfold Configuration.init.
  rewrite Hths_src_init; eauto.

  split. eapply Mem_at_eq_init. eauto.
  unfold monotonic_inj. ii. unfold inj_init in *.
  des_ifH INJ1; ss. subst. inv INJ1.
  des_ifH INJ2; ss. subst. inv INJ2.
  auto_solve_time_rel.
Qed. 
