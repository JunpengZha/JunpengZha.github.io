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

Require Import LibTactics.
Require Import ps_to_np_thread.
Require Import WFConfig.
Require Import PromiseConsistent.
Require Import MemoryReorder.
Require Import ReorderPromise.
Require Import ReorderReserve.
Require Import ReorderCancel.
Require Import ConsistentLemmas.
Require Import PromiseInjection.
Require Import ConsistentProp.
Require Import MemoryProps.

Require Import np_to_ps_thread.
Require Import ps_to_np_thread.

Lemma memory_add_disj_loc_same
      mem loc from to msg mem' loc0
      (ADD: Memory.add mem loc from to msg mem')
      (DISJ_LOC: loc <> loc0):
  mem loc0 = mem' loc0.
Proof.
  eapply Cell.ext. ii.
  inv ADD.
  rewrite Loc_add_neq; eauto.
Qed. 

Lemma memory_split_disj_loc_same
      mem loc from to ts msg msg' mem' loc0
      (SPLIT: Memory.split mem loc from to ts msg msg' mem')
      (DISJ_LOC: loc <> loc0):
  mem loc0 = mem' loc0.
Proof.
  eapply Cell.ext. ii.
  inv SPLIT.
  rewrite Loc_add_neq; eauto.
Qed.

Lemma memory_remove_disj_loc_same
      mem loc from to msg mem' loc0
      (REMOVE: Memory.remove mem loc from to msg mem')
      (DISJ_LOC: loc <> loc0):
  mem loc0 = mem' loc0.
Proof.
  eapply Cell.ext. ii.
  inv REMOVE.
  rewrite Loc_add_neq; eauto.
Qed.
  
Lemma thread_consistent_nprm_stable_mem_add
      lang st lc sc mem lo loc from to msg sc' mem'
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang st lc sc mem) lo)
      (ADD: Memory.add mem loc from to msg mem')
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (LOCAL_WF': Local.wf lc mem')
      (MEM_CLOSED': Memory.closed mem'):
  Thread.consistent_nprm (@Thread.mk lang st lc sc' mem') lo. 
Proof.
  unfold Thread.consistent_nprm in *; ss. ii.
  exploit Memory.cap_exists; [eapply MEM_CLOSED | eauto..]. ii; des.
  exploit Memory.cap_closed; [eapply CAP0 | eapply MEM_CLOSED | eauto..]. ii.
  exploit Memory.max_concrete_timemap_exists; eauto.
  inv H. eauto. ii; des.
  exploit CONSISTENT; [eapply CAP0 | eapply H0 | eauto..].
  ii; des. destruct e2; ss.
  eapply rtc_rtcn in STEPS. des. 
  eapply additional_msg_consistent_construction with
      (inj := (spec_inj mem))
      (max_ts := Memory.max_ts loc mem2)
      (max_ts' := Time.join (Memory.max_ts loc mem2) (Memory.max_ts loc mem1))
      (mem' := mem1) in STEPS; eauto.
  {
    (* fulfill *)
    destruct STEPS as (st0' & lc0' & sc0' & mem0' & FULFILL_STEPS & BOT).
    eexists.
    split. eapply FULFILL_STEPS. ss.
  }
  {
    (* local wf *)
    eapply Local.cap_wf; eauto.
  }
  {
    (* local wf *)
    eapply Local.cap_wf; eauto.
  }
  {
    (* memory closed *)
    eapply Memory.cap_closed; eauto.
  }
  {
    (* id injection *)
    instantiate (1 := loc). ii.
    unfold spec_inj in *. destruct (Memory.get loc0 t mem) eqn:GET; ss; eauto.
    destruct p; ss. destruct t1; ss.
    inv H2; eauto.
  }
  {
    (* id injection *)
    ii. unfold spec_inj in *.
    destruct (Memory.get loc t mem) eqn:GET; ss; eauto.
    destruct p; ss. destruct t1; ss.
    inv H2; eauto.
  }
  {
    (* Time le *)
    eapply Time.join_l.
  }
  {
    (* mem injection *)
    econs; eauto.
    {
      ii.
      eapply Memory.cap_inv_concrete with (mem1 := mem) in MSG; eauto.
      exists t f R.
      split. unfold spec_inj. rewrite MSG; ss.
      split. eapply spec_inj_optviewinj.
      inv CAP.
      eapply SOUND.
      erewrite Memory.add_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.add_get0; eauto. ii; des.
      rewrite MSG in GET. ss.
    }
    {
      ii. unfold spec_inj in *.
      destruct (Memory.get loc0 t mem) eqn:GET; ss.
      destruct p. destruct t1; ss. inv INJ.
      exists val t0 released.
      inv CAP0. eapply SOUND; eauto.
    }
    eapply spec_inj_monotonic; eauto.
  }
  {
    (* TViewInj *)
    eapply TViewInj_spec_inj_id; eauto.
  }
  {
    (* Promise injection *)
    eapply spec_inj_implies_promises_inj; eauto.
    inv LOCAL_WF; eauto.
  }
  {
    (* disj loc cover *)
    introv DISJ_LOC NOT_COVER COVER.
    assert (mem loc0 = mem' loc0).
    {
      eapply memory_add_disj_loc_same; eauto.
    }
    exploit Memory.cap_slice_inj;
      [eapply MEM_CLOSED | eapply MEM_CLOSED' | eapply H1 | eapply CAP0 | eapply CAP | eauto..].
    ii.
    contradiction NOT_COVER.
    inv COVER.
    econs; eauto.
    unfold Memory.get in *.
    rewrite H2; eauto.
  }
  {
    (* Cover *)
    ii.
    exploit MemoryProps.memory_cap_covered; [eapply CAP0 | eapply MEM_CLOSED | eauto..].
    instantiate (2 := loc). instantiate (1 := ts). ii.
    des.
    destruct (Time.eq_dec ts Time.bot); subst.
    {
      inv H3. inv ITV; ss. auto_solve_time_rel.
    }
    {
      erewrite <- Memory.cap_max_ts in H4; eauto.
      exploit H4; eauto.
      econs; eauto; ss.
      exploit Time.bot_spec; eauto.
      instantiate (1 := ts). ii.
      eapply Time.le_lteq in H6. des; eauto.
      subst. ss.
    }
  }
  {
    (* spec view *)
    eapply spec_view_intro_le_max_ts; eauto.
    {
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..]; ss.
      instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
      cut(Time.le (View.rlx (TView.acq (Local.tview lc)) loc) (Memory.max_ts loc mem)).
      ii. eapply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt; [eapply H1 | idtac ..].
      eapply Time.incr_spec.
      clear - LOCAL_WF MEM_CLOSED.
      inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
      inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
      specialize (RLX loc). des.
      eapply Memory.max_ts_spec in RLX; des; ss.
    }
    {
      eapply Cover.gt_max_not_covered.
    }
    {
      ii.
      eapply Time.Time_lt_join in H1. des.
      eapply Cover.gt_max_not_covered in H3. ss.
    }
  }
  {
    (* MAX reserve *)
    clear - CAP0 MEM_CLOSED. 
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..].
    instantiate (1 := loc). ii.
    inv CAP0.
    specialize (BACK loc).
    rewrite H; eauto.
  }
  {
    (* promise less *)
    clear - LOCAL_WF MEM_CLOSED CAP0.
    inv LOCAL_WF; ss; ii.
    eapply PROMISES in H.
    eapply Memory.max_ts_spec in H; eauto; des.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..].
    instantiate (1 := loc). ii.
    rewrite H.
    cut(Time.lt (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem))); ii.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
Qed.

Lemma thread_consistent_nprm_stable_mem_split
      lang st lc sc mem lo loc from to ts msg1 msg2 sc' mem'
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang st lc sc mem) lo)
      (SPLIT: Memory.split mem loc from to ts msg1 msg2 mem')
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (LOCAL_WF': Local.wf lc mem')
      (MEM_CLOSED': Memory.closed mem'):
  Thread.consistent_nprm (@Thread.mk lang st lc sc' mem') lo. 
Proof.
  unfold Thread.consistent_nprm in *; ss. ii.
  exploit Memory.cap_exists; [eapply MEM_CLOSED | eauto..]. ii; des.
  exploit Memory.cap_closed; [eapply CAP0 | eapply MEM_CLOSED | eauto..]. ii.
  exploit Memory.max_concrete_timemap_exists; eauto.
  inv H. eauto. ii; des.
  exploit CONSISTENT; [eapply CAP0 | eapply H0 | eauto..].
  ii; des. destruct e2; ss.
  eapply rtc_rtcn in STEPS. des. 
  eapply additional_msg_consistent_construction with
      (inj := (spec_inj mem))
      (max_ts := Memory.max_ts loc mem2)
      (max_ts' := Time.join (Memory.max_ts loc mem2) (Memory.max_ts loc mem1))
      (mem' := mem1) in STEPS; eauto.
  {
    (* fulfill *)
    destruct STEPS as (st0' & lc0' & sc0' & mem0' & FULFILL_STEPS & BOT).
    eexists.
    split. eapply FULFILL_STEPS. ss.
  }
  {
    (* local wf *)
    eapply Local.cap_wf; eauto.
  }
  {
    (* local wf *)
    eapply Local.cap_wf; eauto.
  }
  {
    (* memory closed *)
    eapply Memory.cap_closed; eauto.
  }
  {
    (* id injection *)
    instantiate (1 := loc). ii.
    unfold spec_inj in *. destruct (Memory.get loc0 t mem) eqn:GET; ss; eauto.
    destruct p; ss. destruct t1; ss.
    inv H2; eauto.
  }
  {
    (* id injection *)
    ii. unfold spec_inj in *.
    destruct (Memory.get loc t mem) eqn:GET; ss; eauto.
    destruct p; ss. destruct t1; ss.
    inv H2; eauto.
  }
  {
    (* Time le *)
    eapply Time.join_l.
  }
  {
    (* mem injection *)
    econs; eauto.
    {
      ii.
      eapply Memory.cap_inv_concrete with (mem1 := mem) in MSG; eauto.
      destruct (Loc.eq_dec loc loc0); subst.
      {
        destruct (Time.eq_dec t ts); subst.
        {
          exists ts to R.
          split. unfold spec_inj. rewrite MSG; ss.
          split. eapply spec_inj_optviewinj; eauto.
          inv CAP. eapply SOUND.
          erewrite Memory.split_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
          rewrite MSG in GET. ss.
          des_if; ss; des; subst; ss; eauto.
          exploit Memory.split_get0; [eapply SPLIT | eauto..].
          ii. des.
          rewrite MSG in GET0. inv GET0.
          eauto.
        }
        {
          exists t f R.
          split. unfold spec_inj. rewrite MSG; ss.
          split. eapply spec_inj_optviewinj; eauto.
          inv CAP. eapply SOUND.
          erewrite Memory.split_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
          rewrite MSG in GET. ss.
          des_if; ss; des; subst; ss; eauto.
        }
      }
      {
        exists t f R.
        split. unfold spec_inj. rewrite MSG; ss.
        split. eapply spec_inj_optviewinj; eauto.
        inv CAP. eapply SOUND.
        erewrite Memory.split_o; eauto.
        des_if; ss; des; subst; ss; eauto.
        exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
        des_if; ss; des; subst; ss; eauto.
        des_if; ss; des; subst; ss; eauto.
      }
    }
    {
      ii. unfold spec_inj in *.
      destruct (Memory.get loc0 t mem) eqn:GET; ss.
      destruct p. destruct t1; ss. inv INJ.
      exists val t0 released.
      inv CAP0. eapply SOUND; eauto.
    }
    eapply spec_inj_monotonic; eauto.
  }
  {
    (* TViewInj *)
    eapply TViewInj_spec_inj_id; eauto.
  }
  {
    (* Promise injection *)
    eapply spec_inj_implies_promises_inj; eauto.
    inv LOCAL_WF; eauto.
  }
  {
    (* disj loc cover *)
    introv DISJ_LOC NOT_COVER COVER.
    assert (mem loc0 = mem' loc0).
    {
      eapply memory_split_disj_loc_same; eauto.
    }
    exploit Memory.cap_slice_inj;
      [eapply MEM_CLOSED | eapply MEM_CLOSED' | eapply H1 | eapply CAP0 | eapply CAP | eauto..].
    ii.
    contradiction NOT_COVER.
    inv COVER.
    econs; eauto.
    unfold Memory.get in *.
    rewrite H2; eauto.
  }
  {
    (* Cover *)
    ii.
    exploit MemoryProps.memory_cap_covered; [eapply CAP0 | eapply MEM_CLOSED | eauto..].
    instantiate (2 := loc). instantiate (1 := ts0). ii.
    des.
    destruct (Time.eq_dec ts0 Time.bot); subst.
    {
      inv H3. inv ITV; ss. auto_solve_time_rel.
    }
    {
      erewrite <- Memory.cap_max_ts in H4; eauto.
      exploit H4; eauto.
      econs; eauto; ss.
      exploit Time.bot_spec; eauto.
      instantiate (1 := ts0). ii.
      eapply Time.le_lteq in H6. des; eauto.
      subst. ss.
    }
  }
  {
    (* spec view *)
    eapply spec_view_intro_le_max_ts; eauto.
    {
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..]; ss.
      instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
      cut(Time.le (View.rlx (TView.acq (Local.tview lc)) loc) (Memory.max_ts loc mem)).
      ii. eapply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt; [eapply H1 | idtac ..].
      eapply Time.incr_spec.
      clear - LOCAL_WF MEM_CLOSED.
      inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
      inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
      specialize (RLX loc). des.
      eapply Memory.max_ts_spec in RLX; des; ss.
    }
    {
      eapply Cover.gt_max_not_covered.
    }
    {
      ii.
      eapply Time.Time_lt_join in H1. des.
      eapply Cover.gt_max_not_covered in H3. ss.
    }
  }
  {
    (* MAX reserve *)
    clear - CAP0 MEM_CLOSED. 
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..].
    instantiate (1 := loc). ii.
    inv CAP0.
    specialize (BACK loc).
    rewrite H; eauto.
  }
  {
    (* promise less *)
    clear - LOCAL_WF MEM_CLOSED CAP0.
    inv LOCAL_WF; ss; ii.
    eapply PROMISES in H.
    eapply Memory.max_ts_spec in H; eauto; des.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..].
    instantiate (1 := loc). ii.
    rewrite H.
    cut(Time.lt (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem))); ii.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
Qed.

Lemma thread_consistent_nprm_stable_mem_cancel
      lang st lc sc mem lo loc from to sc' mem'
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang st lc sc mem) lo)
      (CANCEL: Memory.remove mem loc from to Message.reserve mem')
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (LOCAL_WF': Local.wf lc mem')
      (MEM_CLOSED': Memory.closed mem'):
  Thread.consistent_nprm (@Thread.mk lang st lc sc' mem') lo.
Proof.
  unfold Thread.consistent_nprm in *; ss. ii.
  exploit Memory.cap_exists; [eapply MEM_CLOSED | eauto..]. ii; des.
  exploit Memory.cap_closed; [eapply CAP0 | eapply MEM_CLOSED | eauto..]. ii.
  exploit Memory.max_concrete_timemap_exists; eauto.
  inv H. eauto. ii; des.
  exploit CONSISTENT; [eapply CAP0 | eapply H0 | eauto..].
  ii; des. destruct e2; ss.
  eapply rtc_rtcn in STEPS. des. 
  eapply additional_msg_consistent_construction with
      (inj := (spec_inj mem))
      (max_ts := Memory.max_ts loc mem2)
      (max_ts' := Time.join (Memory.max_ts loc mem2) (Memory.max_ts loc mem1))
      (mem' := mem1) in STEPS; eauto.
  {
    (* fulfill *)
    destruct STEPS as (st0' & lc0' & sc0' & mem0' & FULFILL_STEPS & BOT).
    eexists.
    split. eapply FULFILL_STEPS. ss.
  }
  {
    (* local wf *)
    eapply Local.cap_wf; eauto.
  }
  {
    (* local wf *)
    eapply Local.cap_wf; eauto.
  }
  {
    (* memory closed *)
    eapply Memory.cap_closed; eauto.
  }
  {
    (* id injection *)
    instantiate (1 := loc). ii.
    unfold spec_inj in *. destruct (Memory.get loc0 t mem) eqn:GET; ss; eauto.
    destruct p; ss. destruct t1; ss.
    inv H2; eauto.
  }
  {
    (* id injection *)
    ii. unfold spec_inj in *.
    destruct (Memory.get loc t mem) eqn:GET; ss; eauto.
    destruct p; ss. destruct t1; ss.
    inv H2; eauto.
  }
  {
    (* Time le *)
    eapply Time.join_l.
  }
  {
    (* mem injection *)
    econs; eauto.
    {
      ii.
      eapply Memory.cap_inv_concrete with (mem1 := mem) in MSG; eauto.
      exists t f R.
      split. unfold spec_inj. rewrite MSG; eauto.
      split. eapply spec_inj_optviewinj.
      inv CAP.
      eapply SOUND.
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      exploit Memory.remove_get0; eauto. ii; des.
      rewrite MSG in GET. ss.
    }
    {
      ii. unfold spec_inj in *.
      destruct (Memory.get loc0 t mem) eqn:GET; ss.
      destruct p. destruct t1; ss. inv INJ.
      exists val t0 released.
      inv CAP0. eapply SOUND; eauto.
    }
    eapply spec_inj_monotonic; eauto.
  }
  {
    (* TViewInj *)
    eapply TViewInj_spec_inj_id; eauto.
  }
  {
    (* Promise injection *)
    eapply spec_inj_implies_promises_inj; eauto.
    inv LOCAL_WF; eauto.
  }
  {
    (* disj loc cover *)
    introv DISJ_LOC NOT_COVER COVER.
    assert (mem loc0 = mem' loc0).
    {
      eapply memory_remove_disj_loc_same; eauto.
    }
    exploit Memory.cap_slice_inj;
      [eapply MEM_CLOSED | eapply MEM_CLOSED' | eapply H1 | eapply CAP0 | eapply CAP | eauto..].
    ii.
    contradiction NOT_COVER.
    inv COVER.
    econs; eauto.
    unfold Memory.get in *.
    rewrite H2; eauto.
  }
  {
    (* Cover *)
    ii.
    exploit MemoryProps.memory_cap_covered; [eapply CAP0 | eapply MEM_CLOSED | eauto..].
    instantiate (2 := loc). instantiate (1 := ts). ii.
    des.
    destruct (Time.eq_dec ts Time.bot); subst.
    {
      inv H3. inv ITV; ss. auto_solve_time_rel.
    }
    {
      erewrite <- Memory.cap_max_ts in H4; eauto.
      exploit H4; eauto.
      econs; eauto; ss.
      exploit Time.bot_spec; eauto.
      instantiate (1 := ts). ii.
      eapply Time.le_lteq in H6. des; eauto.
      subst. ss.
    }
  }
  {
    (* spec view *)
    eapply spec_view_intro_le_max_ts; eauto.
    {
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..]; ss.
      instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
      cut(Time.le (View.rlx (TView.acq (Local.tview lc)) loc) (Memory.max_ts loc mem)).
      ii. eapply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt; [eapply H1 | idtac ..].
      eapply Time.incr_spec.
      clear - LOCAL_WF MEM_CLOSED.
      inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
      inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
      specialize (RLX loc). des.
      eapply Memory.max_ts_spec in RLX; des; ss.
    }
    {
      eapply Cover.gt_max_not_covered.
    }
    {
      ii.
      eapply Time.Time_lt_join in H1. des.
      eapply Cover.gt_max_not_covered in H3. ss.
    }
  }
  {
    (* MAX reserve *)
    clear - CAP0 MEM_CLOSED. 
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..].
    instantiate (1 := loc). ii.
    inv CAP0.
    specialize (BACK loc).
    rewrite H; eauto.
  }
  {
    (* promise less *)
    clear - LOCAL_WF MEM_CLOSED CAP0.
    inv LOCAL_WF; ss; ii.
    eapply PROMISES in H.
    eapply Memory.max_ts_spec in H; eauto; des.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED | eapply CAP0 | eauto..].
    instantiate (1 := loc). ii.
    rewrite H.
    cut(Time.lt (Memory.max_ts loc mem) (Time.incr (Memory.max_ts loc mem))); ii.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
Qed.

Inductive mem_id_le: Memory.t -> Memory.t -> Prop :=
| Mem_id_le_intro
    mem mem'
    (SOUND: forall loc to val from released,
        Memory.get loc to mem = Some (from, Message.concrete val released) ->
        exists released',
          Memory.get loc to mem' = Some (from, Message.concrete val released') /\
          View.opt_le released released')
    (COMPLETE: forall loc to val from released',
        Memory.get loc to mem' = Some (from, Message.concrete val released') ->
        exists released, Memory.get loc to mem = Some (from, Message.concrete val released))
    (SOUND_RSV: forall loc to from,
        Memory.get loc to mem = Some (from, Message.reserve) ->
        Memory.get loc to mem' = Some (from, Message.reserve))
    (COMPLETE_RSV: forall loc to from,
        Memory.get loc to mem' = Some (from, Message.reserve) ->
        Memory.get loc to mem = Some (from, Message.reserve)):
    mem_id_le mem mem'.

Lemma mem_id_le_bot
      prom prom'
      (MEM_LE: mem_id_le prom prom')
      (BOT: prom' = Memory.bot):
  prom = Memory.bot.
Proof.
  destruct (classic (exists loc from to msg, Memory.get loc to prom = Some (from, msg))).
  {
    des.
    inv MEM_LE.
    destruct msg.
    eapply SOUND in H; eauto.
    des. rewrite Memory.bot_get in H. ss.
    eapply SOUND_RSV in H; eauto.
    rewrite Memory.bot_get in H. ss.
  }
  {
    eapply Memory.ext. ii.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts prom) eqn:GET; eauto.
    destruct p.
    contradiction H; eauto.
  }
Qed.

Lemma mem_id_le_identity
      prom:
  mem_id_le prom prom.
Proof.
  econs; ii; eauto.
  eexists. split; eauto.
  eapply View.View.opt_le_PreOrder_obligation_1.
Qed.

Lemma memory_nonsynch_loc_mem_le
      prom prom' loc
      (MEM_SYNC_LOC: Memory.nonsynch_loc loc prom')
      (MEM_ID_LE: mem_id_le prom prom'):
  Memory.nonsynch_loc loc prom.
Proof.
  unfold Memory.nonsynch_loc in *. ii.
  destruct msg; ss.
  inv MEM_ID_LE.
  exploit SOUND; [eapply GET | eauto..]. ii; des.
  exploit MEM_SYNC_LOC; [eapply H | eauto..]. ss. ii; subst.
  inv H0. eauto.
Qed.

Lemma memory_nonsynch_mem_le
      prom prom'
      (MEM_SYNC: Memory.nonsynch prom')
      (MEM_ID_LE: mem_id_le prom prom'):
  Memory.nonsynch prom.
Proof.
  unfold Memory.nonsynch in *. ii.
  specialize (MEM_SYNC loc).
  unfold Memory.nonsynch_loc in *.
  destruct msg; ss.
  inv MEM_ID_LE.
  exploit SOUND; eauto. ii; des.
  exploit MEM_SYNC; eauto.
  ii; ss. subst.
  inv H0; eauto.
Qed.

Lemma mem_id_le_add_prsv
      mem1 loc from to val R1 mem1'
      mem2 R2 mem2'
      (MEM_ID_LE: mem_id_le mem1 mem2)
      (ADD1: Memory.add mem1 loc from to (Message.concrete val R1) mem1')
      (ADD2: Memory.add mem2 loc from to (Message.concrete val R2) mem2')
      (VIEW_OPT_LE: View.opt_le R1 R2):
  mem_id_le mem1' mem2'.
Proof.
  inv MEM_ID_LE.
  econs; eauto; ii.
  - erewrite Memory.add_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H; eauto.
    exploit Memory.add_get0; [eapply ADD2 | eauto..]. ii; des.
    eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.add_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H; eauto.
    exploit Memory.add_get0; [eapply ADD1 | eauto..]. ii; des; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.add_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.add_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma mem_id_le_split_prsv
      mem1 loc from to ts val R1 val' R1' mem1'
      mem2 R2 R2' mem2'
      (MEM_ID_LE: mem_id_le mem1 mem2)
      (SPLIT1: Memory.split mem1 loc from to ts
                            (Message.concrete val R1) (Message.concrete val' R1') mem1')
      (SPLIT2: Memory.split mem2 loc from to ts
                            (Message.concrete val R2) (Message.concrete val' R2') mem2')
      (VIEW_OPT_LE: View.opt_le R1 R2):
  mem_id_le mem1' mem2'.
Proof.
  inv MEM_ID_LE.
  econs; eauto; ii.
  - erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H.
    exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
    exploit Memory.split_get0; [eapply SPLIT1 | eauto..].
    des_ifH H; ss; des; subst; ss.
    exploit SOUND; eauto. ii; des.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit SOUND; eauto. ii; des.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H.
    exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
    exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
    exploit SOUND; [eapply GET4 | eauto..]. ii; des.
    rewrite GET0 in H. inv H.
    eexists. split; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H.
    exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H.
    exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma mem_id_le_lower_prsv
      mem1 loc from to val R1 val' R1' mem1'
      mem2 R2 R2' mem2'
      (MEM_ID_LE: mem_id_le mem1 mem2)
      (LOWER1: Memory.lower mem1 loc from to
                            (Message.concrete val R1) (Message.concrete val' R1') mem1')
      (LOWER2: Memory.lower mem2 loc from to
                            (Message.concrete val R2) (Message.concrete val' R2') mem2')
      (VIEW_OPT_LE: View.opt_le R1' R2'):
  mem_id_le mem1' mem2'.
Proof.
  inv MEM_ID_LE.
  econs; eauto; ii.
  - erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H.
    exploit Memory.lower_get0; eauto. ii; des.
    exploit COMPLETE; eauto. ii; des.
    exploit SOUND; eauto. ii; des.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    inv H.
    exploit Memory.lower_get0; [eapply LOWER1 | eauto..]. ii; des; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply LOWER2 | eauto..]. ii; des; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply LOWER1 | eauto..]. ii; des; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma mem_id_le_remove_prsv
      mem1 loc from to msg1 mem1'
      mem2 msg2 mem2'
      (MEM_ID_LE: mem_id_le mem1 mem2)
      (SPLIT1: Memory.remove mem1 loc from to msg1 mem1')
      (SPLIT2: Memory.remove mem2 loc from to msg2 mem2'):
  mem_id_le mem1' mem2'.
Proof.
  inv MEM_ID_LE.
  econs; eauto; ii.
  - erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.
    
Lemma Local_read_tview_le_prsv
      lc1 mem loc to val released ord lc2 lo lc1' mem'
      (READ: Local.read_step lc1 mem loc to val released ord lc2 lo)
      (MEM_LE: mem_id_le mem' mem)
      (PROM_LE: mem_id_le (Local.promises lc1') (Local.promises lc1))
      (TVIEW_LE: TView.le (Local.tview lc1') (Local.tview lc1))
      (LOCAL_WF: Local.wf lc1 mem)
      (MEM_CLOSED: Memory.closed mem)
      (LOCAL_WF': Local.wf lc1' mem')
      (MEM_CLOSED': Memory.closed mem'):
  exists lc2' released',
    <<LE_READ: Local.read_step lc1' mem' loc to val released' ord lc2' lo>> /\
    <<PROM_LE': mem_id_le (Local.promises lc2') (Local.promises lc2)>> /\
    <<TVIEW_LE': TView.le (Local.tview lc2') (Local.tview lc2)>> /\
    <<OPT_VIEW_LE': View.opt_le released' released>>.
Proof.
  inv READ; ss.
  assert (exists released', Memory.get loc to mem' = Some (from, Message.concrete val released') /\
                       View.opt_le released' released).
  {
    clear - MEM_LE GET.
    inv MEM_LE. exploit COMPLETE; eauto. ii; des.
    exploit SOUND; eauto. ii; des.
    rewrite GET in H0. inv H0.
    eexists. split; eauto.
  }
  des.
  do 2 eexists.
  split.
  {
    econs; eauto.
    inv READABLE. econs.
    clear - PLN TVIEW_LE.
    inv TVIEW_LE. inv CUR.
    unfold TimeMap.le in PLN0. specialize (PLN0 loc).
    auto_solve_time_rel.
    ii.
    exploit RLX; eauto. ii.
    inv TVIEW_LE. inv CUR.
    unfold TimeMap.le in RLX0.
    specialize (RLX0 loc).
    auto_solve_time_rel.
  }
  ss. split; eauto.
  split; eauto.
  eapply MemoryProps.read_tview_mon; eauto.
  destruct ord; ss.
Qed.

Lemma Local_write_tview_le_prsv
      lc1 sc1 mem1 loc from to val releasedr released ord lc2 sc2 mem2 lo kind
      lc1' sc1' mem1' releasedr'
      (WRITE: Local.write_step lc1 sc1 mem1 loc from to val releasedr released ord lc2 sc2 mem2 kind lo)
      (MEM_LE: mem_id_le mem1' mem1)
      (PROM_LE: (Local.promises lc1') = (Local.promises lc1))
      (TVIEW_LE: TView.le (Local.tview lc1') (Local.tview lc1))
      (REL_LE: View.opt_le releasedr' releasedr)
      (VIEW_WF: View.opt_wf releasedr)
      (VIEW_WF': View.opt_wf releasedr')
      (LOCAL_WF: Local.wf lc1 mem1)
      (MEM_CLOSED: Memory.closed mem1)
      (LOCAL_WF': Local.wf lc1' mem1')
      (MEM_CLOSED': Memory.closed mem1'):
  exists lc2' mem2' released' kind',
    <<LE_WRITE: Local.write_step lc1' sc1' mem1' loc from to val releasedr' released' ord lc2' sc1' mem2' kind' lo>> /\
    <<MEM_LE': mem_id_le mem2' mem2>> /\
    <<PROM_LE': (Local.promises lc2') = (Local.promises lc2)>> /\
    <<TVIEW_LE': TView.le (Local.tview lc2') (Local.tview lc2)>>.
Proof.
  inv WRITE; ss. inv WRITE0; ss. inv PROMISE; ss.
  - (* add *)
    exploit MemoryProps.add_succeed_wf; eauto.
    ii; des.
    exploit MemoryProps.write_succeed_valid; [ | | | eapply TO1 | idtac..]. 
    {
      inv LOCAL_WF'; eauto.
    }
    { 
      instantiate (1 := loc). ii.
      eapply MemoryProps.memory_add_cover_disjoint with (mem0 := mem1) (mem1 := mem2) in H; eauto.
      contradiction H. 
      inv COVER. 
      inv MEM_LE.
      destruct msg.
      exploit SOUND; [eapply GET | eauto..]. ii; des.
      econs; eauto. 
      exploit SOUND_RSV; eauto. ii.
      econs; eauto.
    }
    {
      inv WRITABLE.
      instantiate (1 := TView.write_released (Local.tview lc1') sc1' loc to releasedr' ord).
      inv TS.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eauto..].
      inv LOCAL_WF. eauto.
      instantiate (2 := ord). instantiate (1 := ord). destruct ord; ss.
      instantiate (3 := sc1). instantiate (2 := loc). instantiate (1 := to).
      instantiate (1 := sc1').
      ii. inv H. ss. unfold TimeMap.bot. eapply Time.bot_spec.
      ss. rewrite <- H2 in TS1. ss.
      unfold View.le in LE. inv LE. unfold TimeMap.le in RLX.
      specialize (RLX loc).
      auto_solve_time_rel.
    }
    {
      ii.
      clear - MEM_LE ATTACH H.
      inv H. des.
      inv MEM_LE.
      destruct msg.
      exploit SOUND; eauto. ii; des.
      eapply ATTACH in H; eauto.
      exploit SOUND_RSV; eauto.
    }
    {
      instantiate (1 := val).
      inv MSG_WF.
      econs.
      inv LOCAL_WF'.
      exploit TViewFacts.write_future0; [eapply TVIEW_WF | eapply VIEW_WF' | eauto..].
      ii; des; eauto.
    }
    ii; des.
    exploit MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
    ii; subst.
    do 4 eexists.
    split. 
    {
      econs; eauto.
      inv WRITABLE. econs.
      inv TVIEW_LE. inv CUR. unfold TimeMap.le in RLX.
      specialize (RLX loc).
      auto_solve_time_rel.
      introv ORDER.
      eapply memory_nonsynch_loc_mem_le; eauto.
      rewrite PROM_LE. eapply mem_id_le_identity.
    }
    ss.
    split.
    {
      inv WRITE. inv PROMISE.
      eapply mem_id_le_add_prsv with (mem1 := mem1') (mem2 := mem1); eauto.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eauto..].
      inv LOCAL_WF; eauto.
      destruct ord; ss.
    }
    split.
    rewrite PROM_LE. eauto.
    eapply MemoryProps.write_tview_mon_same_ord'; eauto.
  - (* split *)
    des; subst; ss. inv RESERVE. 
    assert (GET': Memory.get loc ts3 (Local.promises lc1') = Some (from, Message.concrete val' released')).
    {
      exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
      rewrite PROM_LE; eauto.
    }
    des.
    assert (MSG_WF': Message.wf (Message.concrete val'0 (TView.write_released
                                                           (Local.tview lc1') sc1' loc to releasedr' ord))).
    {
      econs.
      exploit TViewFacts.write_future0; [ | eapply VIEW_WF' | eauto..].
      inv LOCAL_WF'. eauto.
      ii; des; eauto.
    }
    exploit MemoryProps.split_succeed_wf; [eapply PROMISES | eauto..].
    ii; des. clear GET2.
    assert (MEM_GET': Memory.get loc ts3 mem1' = Some (from, Message.concrete val' released')).
    {
      inv LOCAL_WF'. eauto.
    }
    exploit Memory.split_exists; [eapply GET' | eapply TS12 | eapply TS23 | eapply MSG_WF' | eauto..].
    introv PROM_SPLIT'. destruct PROM_SPLIT' as (prom1' & PROM_SPLIT').
    exploit Memory.split_exists; [eapply MEM_GET' | eapply TS12 | eapply TS23 | eapply MSG_WF' | eauto..].
    introv MEM_SPLIT'. destruct MEM_SPLIT' as (mem2' & MEM_SPLIT').
    exploit Memory.split_get0; [eapply PROM_SPLIT' | eauto..]. ii; des.
    exploit Memory.remove_exists; [eapply GET1 | eauto..].
    introv PROM_REMOVE'. destruct PROM_REMOVE' as (prom2' & PROM_REMOVE').
    do 4 eexists.
    split.
    {
      econs; eauto.
      inv WRITABLE. econs.
      inv TVIEW_LE. inv CUR. unfold TimeMap.le in RLX.
      specialize (RLX loc).
      auto_solve_time_rel. 

      econs. eapply Memory.promise_split.
      eauto. eauto.
      econs. inv TS. 
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eauto..].
      inv LOCAL_WF. eauto.
      instantiate (2 := ord). instantiate (1 := ord). destruct ord; ss.
      instantiate (3 := sc1). instantiate (2 := loc). instantiate (1 := to).
      instantiate (1 := sc1').
      ii. inv H. ss. unfold TimeMap.bot. eapply Time.bot_spec.
      ss. rewrite <- H2 in TS0. ss.
      unfold View.le in LE. inv LE. unfold TimeMap.le in RLX.
      specialize (RLX loc).
      clear - TS0 RLX.
      auto_solve_time_rel.
      eauto. eauto. eauto.
      introv ORDER. eapply memory_nonsynch_loc_mem_le; eauto.
      rewrite PROM_LE; eauto.
      eapply mem_id_le_identity; eauto.
    }
    ss.
    split.
    {
      eapply mem_id_le_split_prsv with (mem1 := mem1') (mem2 := mem1); eauto.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eauto..].
      inv LOCAL_WF; eauto.
      destruct ord; ss.
    }
    split.
    {
      eapply Memory.ext. ii.
      destruct (Memory.get loc0 ts prom2') eqn: GET_prom2';
        destruct (Memory.get loc0 ts promises2) eqn: GET_promises2; eauto.
      {
        destruct p. destruct p0.
        exploit MemoryReorder.split_remove_the_split_msg_stable_rvs;
          [eapply PROM_SPLIT' | eapply PROM_REMOVE' | eapply GET_prom2' | eauto..].
        ii; des; subst.
        {
          exploit MemoryReorder.split_remove_the_split_msg_stable_rvs;
            [eapply PROMISES | eapply REMOVE | eapply GET_promises2 | eauto..].
          ii; des; subst. eauto.
          erewrite Memory.remove_o in GET_promises2; eauto.
          des_ifH GET_promises2; ss; des; subst; ss; eauto.
          erewrite Memory.split_o in GET_promises2; eauto.
          des_ifH GET_promises2; ss; des; subst; ss; eauto.
          des_ifH GET_promises2; ss; des; subst; ss; eauto.
        }
        {
          exploit MemoryReorder.split_remove_the_split_msg_stable_rvs;
          [eapply PROMISES | eapply REMOVE | eapply GET_promises2 | eauto..].
          ii; des; subst.
          erewrite Memory.remove_o in GET_prom2'; eauto.
          des_ifH GET_prom2'; ss; des; subst; ss; eauto.
          erewrite Memory.split_o in GET_prom2'; eauto.
          des_ifH GET_prom2'; ss; des; subst; ss; eauto.
          des_ifH GET_prom2'; ss; des; subst; ss; eauto.
          rewrite PROM_LE in H. rewrite H in H0. inv H0; eauto.
        }
      }
      {
        destruct p.
        exploit MemoryReorder.split_remove_the_split_msg_stable_rvs;
          [eapply PROM_SPLIT' | eapply PROM_REMOVE' | eapply GET_prom2' | eauto..].
        ii; des; subst. 
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        auto_solve_time_rel.
        exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
        rewrite GET_promises2 in GET6. ss.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        exploit Memory.split_get0; [eapply PROM_SPLIT' | eauto..]. ii; des.
        rewrite H in GET3. ss.
        erewrite Memory.split_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        erewrite Memory.split_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
        rewrite PROM_LE in H. rewrite H in GET_promises2. ss.
      }
      {
        destruct p.
        exploit MemoryReorder.split_remove_the_split_msg_stable_rvs;
          [eapply PROMISES | eapply REMOVE | eapply GET_promises2 | eauto..].
        ii; des; subst.
        erewrite Memory.remove_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss; eauto.
        exploit Memory.split_get0; [eapply PROM_SPLIT' | eauto..]. ii; des.
        rewrite GET_prom2' in GET6. ss.
        erewrite Memory.remove_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
        rewrite H in GET3. ss.
        erewrite Memory.split_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        erewrite Memory.split_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        des_ifH GET_prom2'; ss; des; subst; ss; eauto.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
        rewrite PROM_LE in GET_prom2'. rewrite H in GET_prom2'. ss.
      }
    }
    eapply MemoryProps.write_tview_mon_same_ord'; eauto.
  - (* lower *)
    des; subst; ss.
    assert (GET': Memory.get loc to (Local.promises lc1') = Some (from, Message.concrete val0 released)).
    { 
      exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
      rewrite PROM_LE; eauto.
    }
    assert (MEM_GET': Memory.get loc to mem1' = Some (from, Message.concrete val0 released)).
    {
      inv LOCAL_WF'. eauto.
    }
    assert (MSG_WF': Message.wf (Message.concrete val (TView.write_released
                                                         (Local.tview lc1') sc1' loc to releasedr' ord))).
    {
      econs.
      exploit TViewFacts.write_future0; [ | eapply VIEW_WF' | eauto..].
      inv LOCAL_WF'. eauto.
      ii; des; eauto.
    }
    exploit MemoryProps.lower_succeed_wf; [eapply PROMISES | eauto..]. ii; des.
    clear GET. inv MSG_LE.
    exploit Memory.lower_exists; [eapply GET' | eapply TS0 | eapply MSG_WF' | eauto..].
    {
      econs; eauto.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eapply VIEW_WF | eauto..].
      inv LOCAL_WF. eauto.
      destruct ord; ss.
    }
    introv PROM_LOWER'. destruct PROM_LOWER' as (prom1' & PROM_LOWER').
    exploit Memory.lower_exists; [eapply MEM_GET' | eapply TS0 | eapply MSG_WF' | eauto..].
    {
      econs; eauto.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eapply VIEW_WF | eauto..].
      inv LOCAL_WF. eauto.
      destruct ord; ss.
    }
    introv MEM_LOWER'. destruct MEM_LOWER' as (mem2' & MEM_LOWER').
    exploit Memory.lower_get0; [eapply PROM_LOWER' | eauto..]. ii; des.
    exploit Memory.remove_exists; [eapply GET0 | eauto..].
    introv PROM_REMOVE'. destruct PROM_REMOVE' as (prom2' & PROM_REMOVE').
    do 4 eexists.
    split.
    {
      econs; eauto.
      inv WRITABLE. econs.
      inv TVIEW_LE. inv CUR. unfold TimeMap.le in RLX.
      specialize (RLX loc).
      auto_solve_time_rel.

      econs. eapply Memory.promise_lower; eauto.
      inv TS. econs.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eauto..].
      inv LOCAL_WF. eauto.
      instantiate (2 := ord). instantiate (1 := ord). destruct ord; ss.
      instantiate (3 := sc1). instantiate (2 := loc). instantiate (1 := to).
      instantiate (1 := sc1').
      ii. inv H. ss. unfold TimeMap.bot. eapply Time.bot_spec.
      ss. rewrite <- H2 in TS1. ss.
      unfold View.le in LE. inv LE. unfold TimeMap.le in RLX.
      specialize (RLX loc).
      clear - TS1 RLX.
      auto_solve_time_rel.
      eauto.
      introv ORDER. eapply memory_nonsynch_loc_mem_le; eauto.
      rewrite PROM_LE; eauto.
      eapply mem_id_le_identity; eauto.
    }
    split.
    {
      eapply mem_id_le_lower_prsv; eauto.
      exploit TViewFacts.write_released_mon'; [eapply TVIEW_LE | | eapply REL_LE | eauto..].
      inv LOCAL_WF; eauto.
      destruct ord; ss.
    }
    ss. split.
    {
      eapply Memory.ext. ii.
      exploit MemoryProps.lower_remove_remove; [eapply PROMISES | eapply REMOVE | eauto..]. ii.
      exploit MemoryProps.lower_remove_remove; [eapply PROM_LOWER' | eapply PROM_REMOVE' | eauto..]. ii.
      destruct (Memory.get loc0 ts prom2') eqn: GET_prom2';
        destruct (Memory.get loc0 ts promises2) eqn: GET_promises2; eauto.
      {
        destruct p, p0.
        erewrite Memory.remove_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
      }
      {
        destruct p.
        erewrite Memory.remove_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
      }
      {
        destruct p.
        erewrite Memory.remove_o in GET_promises2; eauto.
        des_ifH GET_promises2; ss; des; subst; ss.
        erewrite Memory.remove_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        erewrite Memory.remove_o in GET_prom2'; eauto.
        des_ifH GET_prom2'; ss; des; subst; ss.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
        rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. eauto.
      }
    }
    eapply MemoryProps.write_tview_mon_same_ord'; eauto.
Qed.

Lemma Local_fence_tview_le_prsv
      lc1 sc1 ordr ordw lc2 sc2 lc1' sc1'
      (FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (NOT_SC: ordw <> Ordering.seqcst)
      (TVIEW_WF: TView.wf (Local.tview lc1))
      (TVIEW_LE: TView.le (Local.tview lc1') (Local.tview lc1))
      (MEM_ID_LE: mem_id_le (Local.promises lc1') (Local.promises lc1)):
  exists lc2',
    <<FENCE_LE: Local.fence_step lc1' sc1' ordr ordw lc2' sc1'>> /\
    <<TVIEW_LE': TView.le (Local.tview lc2') (Local.tview lc2)>>.
Proof.
  inv FENCE; ss.
  eexists.
  split.
  econs; eauto; ss.
  introv ORDER.
  eapply memory_nonsynch_mem_le; eauto.
  destruct ordw; ss.
  ss.
  eapply write_fence_tview_mon_same_ord_not_scfence; eauto.
  eapply TViewFacts.read_fence_tview_mon; eauto.
  destruct ordr; ss.
Qed.

Lemma lower_to_none_tview_le_prsv
      lc1 mem1 loc from to val val0 released lc2 mem2
      lc1'  mem1' 
      (LOWER: Local.promise_step lc1 mem1 loc from to (Message.concrete val None)
                                 lc2 mem2 (Memory.op_kind_lower (Message.concrete val0 released)))
      (MEM_LE: mem_id_le mem1' mem1)
      (PROM_LE: (Local.promises lc1') = (Local.promises lc1))
      (LOCAL_WF: Local.wf lc1 mem1)
      (LOCAL_WF': Local.wf lc1' mem1'):
  exists lc2' mem2',
    <<LE_WRITE: Local.promise_step lc1' mem1' loc from to (Message.concrete val None)
                                 lc2' mem2' (Memory.op_kind_lower (Message.concrete val0 released))>> /\
    <<MEM_LE': mem_id_le mem2' mem2>> /\
    <<PROM_LE': (Local.promises lc2') = (Local.promises lc2)>>.
Proof.
  inv LOWER. inv PROMISE.
  des; subst. inv RESERVE.
  exploit MemoryProps.lower_succeed_wf; [eapply PROMISES | eauto..].
  ii; des. inv MSG_LE.
  exploit MemoryProps.lower_succeed_wf; [eapply MEM | eauto..].
  ii; des.
  assert (GET_PROM': Memory.get loc to (Local.promises lc1') =
                     Some (from, Message.concrete val1 released0)).
  {
    rewrite PROM_LE; eauto.
  }
  exploit Memory.lower_exists; [eapply GET_PROM' | eauto..].
  introv PROM_LOWER. destruct PROM_LOWER as (prom2' & PROM_LOWER).
  assert (GET_MEM': Memory.get loc to mem1' =
                    Some (from, Message.concrete val1 released0)).
  {
    inv LOCAL_WF'; eauto.
  }
  exploit Memory.lower_exists; [eapply GET_MEM' | eauto..].
  introv MEM_LOWER. destruct MEM_LOWER as (mem2' & MEM_LOWER).
  do 2 eexists.
  split.
  {
    econs.
    eapply Memory.promise_lower; eauto.
    econs. econs. eauto.
  }
  split.
  eapply mem_id_le_lower_prsv; eauto.
  ss.
  eapply Memory.ext. ii.
  destruct (Memory.get loc0 ts prom2') eqn:GET_prom2';
    destruct (Memory.get loc0 ts promises2) eqn:GET_promises2; eauto.
  {
    destruct p, p0.
    erewrite Memory.lower_o in GET_prom2'; eauto.
    des_ifH GET_prom2'; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    inv GET_prom2'. inv GET_promises2. eauto.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
  }
  {
    destruct p.
    erewrite Memory.lower_o in GET_prom2'; eauto.
    des_ifH GET_prom2'; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. 
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. 
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
  }
  {
    destruct p.
    erewrite Memory.lower_o in GET_prom2'; eauto.
    des_ifH GET_prom2'; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. 
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
    erewrite Memory.lower_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. 
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
  }
Qed.

Lemma cancel_tview_le_prsv
      lc1 mem1 loc from to msg lc2 mem2
      lc1'  mem1' 
      (CANCEL: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel)
      (MEM_LE: mem_id_le mem1' mem1)
      (PROM_LE: (Local.promises lc1') = (Local.promises lc1))
      (LOCAL_WF: Local.wf lc1 mem1)
      (LOCAL_WF': Local.wf lc1' mem1'):
  exists lc2' mem2',
    <<LE_WRITE: Local.promise_step lc1' mem1' loc from to msg lc2' mem2' Memory.op_kind_cancel>> /\
    <<MEM_LE': mem_id_le mem2' mem2>> /\
    <<PROM_LE': (Local.promises lc2') = (Local.promises lc2)>>.
Proof.
  inv CANCEL. inv PROMISE.
  exploit Memory.remove_get0; [eapply PROMISES | eauto..]. ii; des.
  exploit Memory.remove_get0; [eapply MEM | eauto..]. ii; des.
  inv LOCAL_WF.
  exploit PROMISES0; eauto. ii.
  assert (Memory.get loc to (Local.promises lc1') = Some (from, Message.reserve)).
  {
    rewrite PROM_LE; eauto.
  }
  inv LOCAL_WF'.
  exploit PROMISES1; eauto. ii.
  exploit Memory.remove_exists; [eapply H0 | eauto..].
  introv PROM_REMOVE. destruct PROM_REMOVE as (prom2' & PROM_REMOVE).
  exploit Memory.remove_exists; [eapply H1 | eauto..].
  introv MEM_REMOVE. destruct MEM_REMOVE as (mem2' & MEM_REMOVE).
  do 2 eexists.
  split.
  econs; eauto.
  split.
  eapply mem_id_le_remove_prsv; eauto.
  ss.
  eapply Memory.ext. ii.
  destruct (Memory.get loc0 ts prom2') eqn: GET_prom2';
    destruct (Memory.get loc0 ts promises2) eqn: GET_promises2; eauto.
  {
    destruct p, p0.
    erewrite Memory.remove_o in GET_prom2'; eauto.
    des_ifH GET_prom2'; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. eauto.
  }
  {
    destruct p.
    erewrite Memory.remove_o in GET_prom2'; eauto.
    des_ifH GET_prom2'; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. 
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
  }
  {
    destruct p.
    erewrite Memory.remove_o in GET_prom2'; eauto.
    des_ifH GET_prom2'; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2. 
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
    erewrite Memory.remove_o in GET_promises2; eauto.
    des_ifH GET_promises2; ss; des; subst; ss; eauto.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
    rewrite PROM_LE in GET_prom2'. rewrite GET_prom2' in GET_promises2. inv GET_promises2.
  }
Qed.

Lemma thread_consistent_nprm_stable_mem_lower':
  forall lang n st lc sc mem lc' sc' mem' lo e
    (STEPS: rtcn (@Thread.nprm_step lang lo) n (Thread.mk lang st lc sc mem) e)
    (BOT: Local.promises (Thread.local e) = Memory.bot)
    (MEM_LE: mem_id_le mem' mem)
    (PROM_LE: (Local.promises lc') = (Local.promises lc))
    (TVIEW_LE: TView.le (Local.tview lc') (Local.tview lc))
    (LOCAL_WF: Local.wf lc mem)
    (MEM_CLOSED: Memory.closed mem)
    (LOCAL_WF': Local.wf lc' mem')
    (MEM_CLOSED': Memory.closed mem'),
  exists e',
    rtc (@Thread.nprm_step lang lo) (Thread.mk lang st lc' sc' mem') e' /\
    Local.promises (Thread.local e') = Memory.bot.
Proof.
  induction n; ii.
  inv STEPS; ss.
  exploit mem_id_le_bot; [ | eapply BOT | eauto..]; ss.
  rewrite PROM_LE.
  eapply mem_id_le_identity.
  inv STEPS. destruct a2.
  inv A12.
  - (* program step *)
    inv PROG. inv LOCAL; ss.
    + (* silent *)
      eapply IHn in A23; eauto.
      des.
      exists e'. split; eauto.
      eapply Relation_Operators.rt1n_trans. 2: eapply A23.
      eapply Thread.nprm_step_program_step.
      econs.
      Focus 2. eapply Local.step_silent; eauto.
      ss. ss.
    + (* read *)
      exploit Local_read_tview_le_prsv; eauto.
      rewrite PROM_LE. eapply mem_id_le_identity. ii; des.
      eapply IHn with (mem' := mem') (lc' := lc2') (sc' := sc') in A23; eauto. des.
      exists e'. split; eauto.
      eapply Relation_Operators.rt1n_trans. 2: eapply A23.
      eapply Thread.nprm_step_program_step.
      econs.
      Focus 2. eapply Local.step_read; eauto.
      ss. ss.
      inv LOCAL0; ss. inv LE_READ; ss.
      eapply local_wf_read; eauto.
      eapply local_wf_read; eauto.
    + (* write *)
      exploit Local_write_tview_le_prsv; eauto.
      instantiate (1 := sc'). ii; des.
      eapply IHn with (lc' := lc2') (sc' := sc') (mem' := mem2') in A23; eauto.
      des.
      exists e'. split; eauto.
      eapply Relation_Operators.rt1n_trans. 2: eapply A23.
      eapply Thread.nprm_step_program_step.
      econs.
      Focus 2. eapply Local.step_write; eauto.
      eauto. eauto.
      eapply local_wf_write; eauto.
      eapply write_step_closed_mem; eauto.
      eapply local_wf_write; eauto.
      eapply write_step_closed_mem; eauto.
    + (* update *)
      exploit Local_read_tview_le_prsv; eauto.
      rewrite PROM_LE. eapply mem_id_le_identity. ii; des.
      assert (PROM_EQ: Local.promises lc2' = Local.promises lc2).
      {
        inv LOCAL1; ss. inv LE_READ; ss.
      }
      exploit Local_write_tview_le_prsv; eauto.
      { 
        inv LOCAL1; ss.
        eapply closed_mem_implies_wf_msg_view; [eapply MEM_CLOSED | eauto..].
      }
      {
        inv LE_READ; ss.
        eapply closed_mem_implies_wf_msg_view; [eapply MEM_CLOSED' | eauto..].
      }
      {
        eapply local_wf_read; eauto.
      }
      {
        eapply local_wf_read; eauto.
      }
      instantiate (1 := sc').
      ii; des.
      eapply IHn with (lc' := lc2'0) (sc' := sc') (mem' := mem2') in A23; eauto.
      des.
      exists e'. split; eauto.
      eapply Relation_Operators.rt1n_trans. 2: eapply A23.
      eapply Thread.nprm_step_program_step.
      econs.
      Focus 2. eapply Local.step_update; eauto.
      eauto. eauto.
      eapply local_wf_write; eauto.
      eapply local_wf_read; eauto. 
      eapply write_step_closed_mem; [ | eapply LOCAL2 | eauto..].
      inv LOCAL1; ss. eapply closed_mem_implies_closed_msg; eauto.
      eapply local_wf_read; eauto.
      eapply local_wf_write; eauto.
      eapply local_wf_read; eauto.
      eapply write_step_closed_mem; [ | eapply LE_WRITE | eauto..].
      inv LE_READ; ss. eapply closed_mem_implies_closed_msg; eauto.
      eapply local_wf_read; eauto.
    + (* fence *)
      assert (SC_FENCE_OR_NOT_SC: ordw = Ordering.seqcst \/ ordw <> Ordering.seqcst).
      {
        destruct ordw; ss; eauto;
          try solve [right; ii; ss].
      }
      destruct SC_FENCE_OR_NOT_SC as [SC_FENCE | NOT_SC_FENCE].
      {
        subst.
        inv LOCAL0; ss.
        exploit PROMISES; eauto. ii.
        assert (Local.promises lc' = Memory.bot).
        {
          exploit mem_id_le_bot; [ | eapply H | eauto..].
          rewrite PROM_LE.
          eapply mem_id_le_identity.
        }
        eexists.
        split. eauto.
        ss.
      }
      {
        exploit Local_fence_tview_le_prsv; eauto.
        inv LOCAL_WF; eauto.
        rewrite PROM_LE. eapply mem_id_le_identity.
        instantiate (1 := sc').
        ii; des.
        eapply IHn with (lc' := lc2') in A23; eauto.
        des.
        exists e'.
        split; eauto.
        eapply Relation_Operators.rt1n_trans. 2: eapply A23.
        eapply Thread.nprm_step_program_step.
        econs.
        Focus 2. eapply Local.step_fence; eauto.
        eauto. eauto.
        inv LOCAL0; ss. inv FENCE_LE; ss.
        eapply Local_wf_fence_not_sc; eauto.
        eapply Local_wf_fence_not_sc; eauto.
      }
  - (* lower to none or cancel *)
    inv PF. destruct kind; ss.
    + (* lower to none *)
      destruct msg1; ss. destruct msg; ss.
      destruct released0; ss.
      exploit lower_to_none_tview_le_prsv; eauto. ii; des.
      eapply IHn with (lc' := lc2') (sc' := sc') (mem' := mem2') in A23; eauto.
      des.
      exists e'. split; eauto.
      eapply Relation_Operators.rt1n_trans. 2: eapply A23. 
      eapply Thread.nprm_step_pf_step.
      econs. eauto. eauto.
      inv LOCAL; ss. inv LE_WRITE; ss.
      inv LOCAL. eapply local_wf_promise in PROMISE; eauto. destruct lc; eauto.
      eapply promise_step_closed_mem; eauto.
      inv LE_WRITE. eapply local_wf_promise in PROMISE; eauto. destruct lc'; eauto.
      eapply promise_step_closed_mem; eauto.
    + (* cancel *)
      exploit cancel_tview_le_prsv; eauto. ii; des.
      eapply IHn with (lc' := lc2') (sc' := sc') (mem' := mem2') in A23; eauto.
      des.
      exists e'. split; eauto.
      eapply Relation_Operators.rt1n_trans. 2: eapply A23. 
      eapply Thread.nprm_step_pf_step.
      econs. eauto. eauto.
      inv LOCAL; ss. inv LE_WRITE; ss.
      inv LOCAL. eapply local_wf_promise in PROMISE; eauto. destruct lc; eauto.
      eapply promise_step_closed_mem; eauto.
      inv LE_WRITE. eapply local_wf_promise in PROMISE; eauto. destruct lc'; eauto.
      eapply promise_step_closed_mem; eauto.
Qed.

Lemma thread_consistent_nprm_stable_mem_lower
      lang st lc sc mem lo loc from to sc' mem' msg val released
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang st lc sc mem) lo)
      (LOWER: Memory.lower mem loc from to (Message.concrete val released) msg mem')
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem)
      (LOCAL_WF': Local.wf lc mem')
      (MEM_CLOSED': Memory.closed mem'):
  Thread.consistent_nprm (@Thread.mk lang st lc sc' mem') lo.
Proof.
  unfold Thread.consistent_nprm in *; ss. ii.
  exploit Memory.cap_exists; [eapply MEM_CLOSED | eauto..]. ii; des.
  exploit Memory.cap_closed; [eapply CAP0 | eapply MEM_CLOSED | eauto..]. ii.
  exploit Memory.max_concrete_timemap_exists; eauto.
  inv H. eauto. ii; des.
  exploit CONSISTENT; [eapply CAP0 | eapply H0 | eauto..].
  ii; des. destruct e2; ss.
  eapply rtc_rtcn in STEPS. des.
  eapply thread_consistent_nprm_stable_mem_lower'; eauto.
  {
    clear - LOWER CAP CAP0 MEM_CLOSED' MEM_CLOSED.
    econs; eauto; ii; eauto.
    eapply Memory.cap_inv_concrete in H; eauto.
    erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto. inv H.
    exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
    inv CAP0.
    inv MSG_LE.
    eexists. split; eauto.
    inv CAP0.
    eexists. split; eauto.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    inv CAP0.
    eexists. split; eauto.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    eapply Memory.cap_inv_concrete with (mem1 := mem) in H; eauto.
    eapply Memory.lower_get1 in H; eauto. des. inv MSG_LE.
    inv CAP. eauto. 
    eapply Memory.cap_inv in H; eauto. des.
    {
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto. inv H.
      exploit Memory.lower_get0; eauto. ii; des.
      inv MSG_LE.
      inv CAP0. eauto.
      inv CAP0. eauto.
    }
    {
      inv CAP0. 
      assert (Memory.adjacent loc0 from1 from0 to0 to2 mem).
      {
        inv H0.
        erewrite Memory.lower_o in GET1; eauto.
        des_ifH GET1; ss; des; subst; ss; eauto. inv GET1.
        erewrite Memory.lower_o in GET2; eauto.
        des_ifH GET2; ss; des; subst; ss; eauto. inv GET2.
        auto_solve_time_rel.
        exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
        econs; eauto. ii.
        destruct (Memory.get loc ts mem) eqn:GET'; eauto.
        destruct p.
        exploit EMPTY; eauto. ii.
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss; eauto.
        rewrite GET' in H0. ss.
        erewrite Memory.lower_o in GET2; eauto.
        des_ifH GET2; ss; des; subst; ss; eauto.
        econs; eauto.
        ii.
        destruct (Memory.get loc0 ts mem) eqn:GET'; eauto. destruct p.
        exploit EMPTY; eauto. ii.
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss; eauto.
        rewrite GET' in H0. ss.
        rewrite GET' in H0. ss.
        econs; eauto. ii.
        exploit EMPTY; eauto. ii. 
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss; eauto.
        erewrite Memory.lower_o in GET2; eauto.
        des_ifH GET2; ss; des; subst; ss; eauto.
        inv GET2.
        exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
        econs; eauto.
        ii. exploit EMPTY; eauto. ii.
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss; eauto.
        econs; eauto.
        ii. exploit EMPTY; eauto. ii.
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss; eauto.
        econs; eauto. ii. exploit EMPTY; eauto. ii.
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss; eauto.
      }
      eauto.
    }
    {
      subst.
      exploit Memory.mem_lower_max_ts_eq; [eapply LOWER | eapply MEM_CLOSED | eapply MEM_CLOSED' | eauto..].
      instantiate (1 := loc0). ii.
      rewrite <- H0.
      inv CAP0. eauto.
    } 

    eapply Memory.cap_inv with (mem1 := mem) in H; eauto. des.
    {
      assert (Memory.get loc0 to0 mem' = Some (from0, Message.reserve)).
      {
        erewrite Memory.lower_o; eauto.
        des_if; ss; des; subst; ss; eauto.
        exploit Memory.lower_get0; eauto. ii; des.
        rewrite H in GET. ss.
      }
      inv CAP. eauto.
    }
    {
      assert (Memory.adjacent loc0 from1 from0 to0 to2 mem').
      {
        inv H0.
        assert (exists m1', Memory.get loc0 from0 mem' = Some (from1, m1')).
        {
          erewrite Memory.lower_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          exploit Memory.lower_get0; eauto. ii; des.
          rewrite GET1 in GET. inv GET. eauto.
        }
        des. 
        assert (exists m2', Memory.get loc0 to2 mem' = Some (to0, m2')).
        {
          eapply Memory.lower_get1 in GET2; eauto. des; eauto.
        }
        des.
        econs; eauto.
        ii.
        exploit EMPTY; eauto. ii.
        erewrite Memory.lower_o; eauto.
        des_if; ss; des; subst; ss; eauto.
        exploit Memory.lower_get0; eauto. ii; des.
        rewrite H4 in GET. ss.
      }
      inv CAP. eauto.
    }
    {
      subst.
      exploit Memory.mem_lower_max_ts_eq; [eapply LOWER | eapply MEM_CLOSED | eapply MEM_CLOSED' | eauto..].
      instantiate (1 := loc0). ii.
      rewrite H0.
      inv CAP. eauto.
    }
  }
  {
    eapply TView.TView.le_PreOrder_obligation_1; eauto.
  }
  {
    eapply Local.cap_wf; eauto.
  }
  {
    eapply Local.cap_wf; eauto.
  }
  {
    eapply Memory.cap_closed; eauto.
  }
Qed.

Lemma thread_consistent_nprm_stable_sc_fence
      lang st lc sc mem lo sc' 
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang st lc sc mem) lo)
      (MEM_CLOSED: Memory.closed mem):
  Thread.consistent_nprm (@Thread.mk lang st lc sc' mem) lo.
Proof.
  unfold Thread.consistent_nprm in *; ss.
Qed.

Lemma promise_certified_env_stable
      ths ctid tid1 tid2 sc mem lang1 lang2 st1 lc1 st1' lc1' sc' mem' lo st2 lc2
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (STEP: Thread.all_step lo (Thread.mk lang1 st1 lc1 sc mem) (Thread.mk lang1 st1' lc1' sc' mem'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (DISJ_TH: tid1 <> tid2)
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang2 st2 lc2 sc mem) lo):
  Thread.consistent_nprm (@Thread.mk lang2 st2 lc2 sc' mem') lo.
Proof.
  exploit wf_config_thread_step_prsv; [eapply CONFIG_WF | eapply TH1 | eapply STEP | eauto..].
  introv CONFIG_WF'.
  assert (LOCAL_WF: Local.wf lc2 mem).
  {
    inv CONFIG_WF; ss. inv WF.
    exploit THREADS; [eapply TH2 | eauto..].
  }
  assert (LOCAL_WF': Local.wf lc2 mem').
  {
    inv CONFIG_WF'; ss.
    inv WF; ss.
    eapply THREADS; eauto.
    instantiate (3 := tid2). rewrite IdentMap.gso; eauto.
  }
  assert (MEM_CLOSED: Memory.closed mem).
  {
    inv CONFIG_WF; eauto.
  }
  assert (MEM_CLOSED': Memory.closed mem').
  {
    inv CONFIG_WF'; eauto.
  }
  inv STEP. inv USTEP. inv STEP.
  - inv STEP0. inv LOCAL. inv PROMISE.
    + eapply thread_consistent_nprm_stable_mem_add; eauto.
    + des; subst.
      eapply thread_consistent_nprm_stable_mem_split; eauto.
    + des; subst.
      eapply thread_consistent_nprm_stable_mem_lower; eauto.
    + eapply thread_consistent_nprm_stable_mem_cancel; eauto.
  - inv STEP0. inv LOCAL; eauto.
    + inv LOCAL0; ss. inv WRITE. inv PROMISE; ss.
      eapply thread_consistent_nprm_stable_mem_add; eauto.
      des; subst; ss. inv RESERVE.
      eapply thread_consistent_nprm_stable_mem_split; eauto.
      des; subst; ss.
      eapply thread_consistent_nprm_stable_mem_lower; eauto.
    + inv LOCAL2; ss. inv WRITE. inv PROMISE; ss.
      eapply thread_consistent_nprm_stable_mem_add; eauto.
      des; subst; ss. inv RESERVE.
      eapply thread_consistent_nprm_stable_mem_split; eauto.
      des; subst; ss.
      eapply thread_consistent_nprm_stable_mem_lower; eauto.
Qed.

Lemma promise_certified_envs_stable':
  forall n ths ctid tid1 tid2 sc mem lang1 lang2 st1 lc1 st1' lc1' sc' mem' lo st2 lc2
    (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
    (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
    (STEPS: rtcn (Thread.all_step lo) n (Thread.mk lang1 st1 lc1 sc mem) (Thread.mk lang1 st1' lc1' sc' mem'))
    (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
    (DISJ_TH: tid1 <> tid2)
    (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang2 st2 lc2 sc mem) lo),
    Thread.consistent_nprm (@Thread.mk lang2 st2 lc2 sc' mem') lo.
Proof.
  induction n. intros.
  inv STEPS; eauto.
  intros.
  inv STEPS. destruct a2.
  exploit wf_config_thread_step_prsv; [ | | eapply A12 | eauto..]; eauto.
  intros.
  eapply IHn in A23; eauto.
  rewrite IdentMap.gss; eauto.
  rewrite IdentMap.gso; eauto. 
  eapply promise_certified_env_stable; [ | | eapply A12 | eauto..]; eauto.
Qed.

Lemma promise_certified_envs_stable
      ths ctid tid1 tid2 sc mem lang1 lang2 st1 lc1 st1' lc1' sc' mem' lo st2 lc2
      (CONFIG_WF: Configuration.wf (Configuration.mk ths ctid sc mem))
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
      (STEPS: rtc (Thread.all_step lo) (Thread.mk lang1 st1 lc1 sc mem) (Thread.mk lang1 st1' lc1' sc' mem'))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2))
      (DISJ_TH: tid1 <> tid2)
      (CONSISTENT: Thread.consistent_nprm (@Thread.mk lang2 st2 lc2 sc mem) lo):
  Thread.consistent_nprm (@Thread.mk lang2 st2 lc2 sc' mem') lo.
Proof.
  eapply rtc_rtcn in STEPS.
  des. 
  eapply promise_certified_envs_stable' in STEPS; eauto.
Qed.

Lemma threads_consistent_stable
      npc npc' lo pe
      (CONFIG_WF: Configuration.wf (NPConfiguration.cfg npc))
      (STEP: NPConfiguration.step pe lo npc npc')
      (THS_CONSISTENT: NPConfiguration.consistent npc lo):
  NPConfiguration.consistent npc' lo.
Proof.
  inv STEP; ss.
  - destruct thrd_conf1'.
    eapply NPThread_tau_steps_to_thread_all_steps in STEPS.
    eapply NPThread_tau_step_to_thread_all_step in STEP0; eauto.
    exploit rtc_n1; [eapply STEPS | eapply STEP0 | eauto..].
    introv ALL_STEPS.
    unfold NPConfiguration.consistent in *; ss.
    unfold Threads.consistent_nprm in *; ss.
    intros.
    destruct (Loc.eq_dec tid (Configuration.tid (NPConfiguration.cfg npc))); subst.
    {
      rewrite IdentMap.gss in TH. inv TH.
      eapply inj_pair2 in H1. subst.
      unfold NPAuxThread.consistent in CONSISTENT.
      eauto.
    }
    {
      rewrite IdentMap.gso in TH; eauto.
      lets CONSISTENT': TH.
      eapply THS_CONSISTENT in CONSISTENT'.
      destruct npc; ss. destruct cfg; ss.
      eapply promise_certified_envs_stable;
        [eapply CONFIG_WF | eapply TID1 | eapply ALL_STEPS | eapply TH | eauto..].
    }
  - destruct npc; ss. destruct cfg; ss.
    unfold NPConfiguration.consistent in *; ss.
    unfold Threads.consistent_nprm in *; ss. intros.
    destruct (Loc.eq_dec tid0 tid); subst.
    rewrite IdentMap.grs in TH. ss.
    rewrite IdentMap.gro in TH; eauto.
  - destruct npc; ss. destruct cfg; ss.
    eapply NPAuxThread_out_step_is_Thread_program_step in STEP0; ss.
    unfold NPConfiguration.consistent in *; ss.
    unfold Threads.consistent_nprm in *; ss. intros.
    destruct (Loc.eq_dec tid0 tid); subst.
    {
      rewrite IdentMap.gss in TH; eauto.
      inv TH. eapply inj_pair2 in H1. subst.
      eauto.
    }
    {
      rewrite IdentMap.gso in TH; eauto.
      lets CONSISTENT': TH.
      eapply THS_CONSISTENT in CONSISTENT'.
      eapply promise_certified_env_stable with (lang2 := lang0).
      eapply CONFIG_WF. eapply TID1. eapply STEP0.
      eapply TH. eauto. eauto.
    }
Qed.
