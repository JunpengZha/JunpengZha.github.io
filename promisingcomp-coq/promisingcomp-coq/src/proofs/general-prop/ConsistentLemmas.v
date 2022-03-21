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
Require Import Cover.
Require Import ps_to_np_thread.
Require Import PromiseInjection.
Require Import WFConfig.
Require Import PromiseConsistent.
Require Import MemoryReorder.
Require Import ReorderPromise.
Require Import ReorderReserve.
Require Import ReorderCancel. 

Lemma time_le_singleton_prsv
      to to' loc loc0
      (LE: loc = loc0 -> Time.le to to'):
  Time.le (TimeMap.singleton loc to loc0) to'.
Proof.
  unfold TimeMap.singleton.
  destruct(Loc.eq_dec loc0 loc); subst.
  {
    cut(LocFun.find loc (LocFun.add loc to (LocFun.init Time.bot)) = to). ii.
    exploit LE; eauto. ii.
    unfold LocFun.find in H.
    rewrite H; eauto.
    rewrite LocFun.add_spec_eq; eauto.
  }
  {
    cut(LocFun.find loc0 (LocFun.add loc to (LocFun.init Time.bot)) = Time.bot). ii.
    unfold LocFun.find in *.
    rewrite H; eauto.
    eapply Time.bot_spec; eauto.
    rewrite LocFun.add_spec_neq; eauto.
  }
Qed.

Lemma no_msg_implies_mem_bot
      mem loc
      (NO_MSG: ~ (exists f msg ts, Memory.get loc ts mem = Some (f, msg))):
  mem loc = Cell.bot.
Proof.
  eapply Cell.ext; eauto. ii.
  unfold Memory.get in *.
  destruct (Cell.get ts (mem loc)) eqn:Heqe; ss; eauto.
  contradiction NO_MSG. destruct p. eauto.
  rewrite Cell.bot_get; eauto.
Qed.

Lemma ITV_NEXT_NOTCOVER
      loc to mem from msg to0
      (GET: Memory.get loc to mem = Some (from, msg))
      (LT: Time.lt to0 from)
      (IS_NEXT: forall ts', Time.lt to0 ts' -> Time.lt ts' to -> Memory.get loc ts' mem = None):
  forall ts, Interval.mem (to0, from) ts -> ~ Cover.covered loc ts mem.
Proof.
  ii. inv H0. inv H; inv ITV; ss.
  assert(WF_MSG_ITV: Time.lt from to).
  {
    exploit Memory.get_ts; [eapply GET | eauto..]. 
    ii; des; subst; eauto. auto_solve_time_rel.
  }
  exploit Memory.get_disjoint; [eapply GET | eapply GET0 | eauto..]. ii; des; subst.
  - cut(Time.lt ts ts).
    i. auto_solve_time_rel.
    clear - TO FROM0. auto_solve_time_rel.
  - exploit Interval.disjoint_spec; eauto; auto_solve_time_rel. 
    cut(Time.lt to0 to). i.
    auto_solve_time_rel. 
    ii; des.
    { 
      destruct(Time.le_lt_dec to1 to0).
      {
        clear - FROM TO0 l.
        cut(Time.lt to0 to1). i.
        clear - l H. auto_solve_time_rel.
        auto_solve_time_rel.
      }
      { 
        eapply IS_NEXT in l; eauto.
        rewrite GET0 in l; ss.
        clear - H1 WF_MSG_ITV. auto_solve_time_rel.
      }
    }
    {
      clear - TO WF_MSG_ITV H1 FROM0.
      cut(Time.lt ts to). ii.
      cut(Time.le to ts). ii.
      auto_solve_time_rel.
      clear - FROM0 H1.
      eapply Time.le_lteq; left.
      auto_solve_time_rel.
      auto_solve_time_rel.
    }
    auto_solve_time_rel.
Qed.

Lemma Local_wf_fence_not_sc
      lc sc ordr ordw lc' sc' mem
      (LOCAL_WF: Local.wf lc mem)
      (FENCE_STEP: Local.fence_step lc sc ordr ordw lc' sc')
      (NOT_SC_FENCE: ordw <> Ordering.seqcst):
  Local.wf lc' mem.
Proof.
  destruct lc, lc'; ss.
  inv FENCE_STEP; ss. inv LC2.
  inv LOCAL_WF; ss.
  destruct tview; ss.
  econs; eauto; ss.
  {
    inv TVIEW_WF.
    rewrite write_fence_tview_not_sc; eauto.
    econs; eauto; ss.
    ii. des_if; eauto. des_if; eauto.
    des_if; eauto.
    ii. des_if; eauto. des_if; eauto. viewtac. viewtac.
    des_if; ss. specialize (REL_CUR loc).
    eapply View.View.le_PreOrder_obligation_2; eauto.
    des_if; ss. viewtac.
  }
  {
    inv TVIEW_CLOSED; ss.
    rewrite write_fence_tview_not_sc; eauto.
    econs; eauto; ss.
    ii. des_if; eauto. des_if; eauto.
    des_if; eauto.
  }
Qed.

Lemma write_step_reserve_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo ts f loc0
      (WRITE1: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (RESERVE: Memory.get loc0 ts mem = Some (f, Message.reserve)):
  Memory.get loc0 ts mem' = Some (f, Message.reserve).
Proof.
  inv WRITE1. inv WRITE. inv PROMISE; ss.
  - eapply Memory.add_get1; eauto.
  - des; subst. inv RESERVE0.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; eauto. ii; des.
    rewrite RESERVE in GET; ss.
    des_if; ss; des; subst; ss.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; eauto. ii; des.
    rewrite RESERVE in GET0. ss.
  - des; subst.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
    rewrite RESERVE in GET. ss.
Qed.

Lemma write_step_disj_promise_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0
      (WRITE1: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (DISJ_LOC: loc <> loc0):
  forall to from msg,
    (Memory.get loc0 to (Local.promises lc) = Some (from, msg) <->
     Memory.get loc0 to (Local.promises lc') = Some (from, msg)).
Proof.
  ii.
  inv WRITE1; ss. inv WRITE. inv PROMISE; ss.
  - (* add *)
    split; ii.
    {
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.add_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.add_o; eauto.
      des_if; ss; des; subst; ss; eauto.
    }
    {
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
    }
  - (* split *)
    des; subst. inv RESERVE.
    split; ii.
    {
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
    }
    {
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
    }
  - (* lower *)
    des; subst. 
    split; ii.
    {
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss; eauto.
    }
    {
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
    }
Qed.
  
Lemma write_step_itv_msg_false
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo t f msg
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (LT1: Time.lt from t)
      (LT2: Time.lt t to)
      (GET: Memory.get loc t mem = Some (f, msg)):
  False.
Proof.
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  - eapply MemoryProps.memory_add_cover_disjoint in MEM; eauto.
    contradiction MEM. instantiate (1 := t).
    exploit Memory.get_ts; eauto. ii; des; subst.
    auto_solve_time_rel.
    econs; eauto. econs; ss; eauto. clear. auto_solve_time_rel.
    econs; eauto; ss. eapply Time.le_lteq; eauto.
  - des; subst. inv RESERVE.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
    exploit Memory.get_disjoint; [eapply GET1 | eapply GET | eauto..]. ii; des; subst.
    {
      exploit MemoryProps.split_succeed_wf; [eapply MEM | eauto..]. ii; des.
      clear - LT2 TS23. auto_solve_time_rel. ii. auto_solve_time_rel.
    }
    {
      exploit MemoryProps.split_succeed_wf; [eapply MEM | eauto..]. ii; des.
      unfold Interval.disjoint in H.
      specialize (H t). eapply H; eauto.
      econs; ss; eauto. clear - LT2 TS23.
      eapply Time.le_lteq. left. auto_solve_time_rel.
      econs; ss; eauto.
      exploit Memory.get_ts; [eapply GET | eauto..]. ii; des; subst; ss.
      clear - LT1. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }
  - des; subst.
    exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
    exploit Memory.get_disjoint; [eapply GET0 | eapply GET | eauto..]. ii; des; subst.
    auto_solve_time_rel.
    unfold Interval.disjoint in H. specialize (H t).
    eapply H; eauto.
    econs; ss; eauto.
    eapply Time.le_lteq; eauto.
    econs; ss; eauto.
    exploit Memory.get_ts; [eapply GET | eauto..]. ii; des; subst; ss.
    clear - LT1. auto_solve_time_rel.
    eapply Time.le_lteq; eauto.
Qed.

Lemma write_step_promise_lt_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0 max_ts to' from' msg'
      (WRITE1: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (PRM_LE: forall ts from msg, Memory.get loc0 ts (Local.promises lc) = Some (from, msg) -> Time.lt ts max_ts)
      (RESERVE: Memory.get loc0 to' (Local.promises lc') = Some (from', msg')):
  Time.lt to' max_ts.
Proof.
  inv WRITE1; ss. inv WRITE. inv PROMISE; ss.
  - exploit MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..]. ii; subst.
    eauto.
  - des; subst. inv RESERVE. inv RESERVE0.
    clear - PRM_LE REMOVE PROMISES H0.
    erewrite Memory.remove_o in H0; eauto. des_ifH H0; ss; des; subst; ss.
    erewrite Memory.split_o in H0; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in H0; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    inv H0.
    exploit Memory.split_get0; eauto. ii; des; eauto.
  - des; subst.
    erewrite Memory.remove_o in RESERVE; eauto.
    des_ifH RESERVE; ss; des; subst; ss.
    erewrite Memory.lower_o in RESERVE; eauto.
    des_ifH RESERVE; ss; subst; des; ss; eauto.
    erewrite Memory.lower_o in RESERVE; eauto.
    des_ifH RESERVE; ss; subst; des; ss; eauto.
Qed.

Lemma closed_timemap_le_max
      tm mem max_ts loc
      (CLOSED: Memory.closed_timemap tm mem)
      (NOCOVER: forall ts, Time.lt max_ts ts -> ~ Cover.covered loc ts mem):
  Time.le (tm loc) max_ts.
Proof.
  unfold Memory.closed_timemap in *.
  specialize (CLOSED loc). des.
  destruct (Time.le_lt_dec (tm loc) max_ts); eauto.
  exploit Memory.get_ts; eauto. ii; des; subst.
  rewrite H0 in l. eapply Time_lt_bot_false in l; ss.
  exploit NOCOVER; eauto; ii; ss.
  econs; eauto.
  econs; eauto; ss.
  eapply Time.le_lteq; eauto.
Qed.

Lemma write_max_add
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (MAX_WRITE: Time.lt (Memory.max_ts loc mem) to):
  Time.le (Memory.max_ts loc mem) from /\ kind = Memory.op_kind_add.
Proof.
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  - (* add *)
    destruct (classic (exists f msg ts, Memory.get loc ts mem = Some (f, msg))).
    {
      des.
      exploit Memory.max_ts_spec; eauto. ii; des.
      exploit Memory.add_get0; eauto. ii; des.
      lets GET': GET.
      eapply Memory.add_get1 in GET'; eauto.
      destruct (Time.le_lt_dec (Memory.max_ts loc mem) from); eauto.
      assert(forall t : Time.t, Interval.mem (from, to) t -> ~ covered loc t mem).
      {
        eapply MemoryProps.memory_add_cover_disjoint; eauto.
      }
      specialize (H0 (Memory.max_ts loc mem)).
      false. eapply H0; eauto.
      econs; ss; eauto. clear - MAX_WRITE. auto_solve_time_rel.
      econs; eauto. econs; ss; eauto.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      clear - l H2. rewrite H2 in l. auto_solve_time_rel.
      clear. auto_solve_time_rel.
    }
    {
      exploit no_msg_implies_mem_bot; eauto. ii.
      unfold Memory.max_ts. rewrite H0.
      unfold Cell.max_ts, Cell.bot. ss. unfold DenseOrder.DOMap.max_key, Cell.Raw.bot; ss.
      split; eauto.
      eapply Time.bot_spec.
    }
  - (* split *)
    des; subst; ss. inv RESERVE.
    exploit MemoryProps.split_succeed_wf; eauto. ii; des.
    exploit Memory.max_ts_spec; eauto. ii; des.
    cut(Time.lt to (Memory.max_ts loc mem)). ii.
    clear - MAX_WRITE H. auto_solve_time_rel. ii. auto_solve_time_rel.
    clear - TS23 MAX. auto_solve_time_rel.
  - (* lower *)
    des; subst.
    exploit MemoryProps.lower_succeed_wf; [eapply MEM | eauto..]. ii; des.
    exploit Memory.max_ts_spec; eauto. ii; des.
    clear - MAX_WRITE MAX. auto_solve_time_rel.
Qed.

Lemma write_not_cover_prsv
      lc1 sc1 mem1 loc from to val releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 val' releasedr2 released2 lc2' sc2' mem2' kind2 max_ts
      (NOT_COVER: forall t, ~ Cover.covered loc t mem1 -> Time.le t max_ts -> ~ Cover.covered loc t mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from to val' releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (LE: Time.le to max_ts)
      (KIND_MATCH: kind_match kind1 kind2):
  forall t, ~ Cover.covered loc t mem1' -> Time.le t max_ts -> ~ Cover.covered loc t mem2'.
Proof.
  inv WRITE1. inv WRITE. inv PROMISE; ss.
  - (* add *)
    destruct kind2; ss.
    inv WRITE2. inv WRITE. inv PROMISE.
    eapply add_not_cover_prsv; eauto.
  - (* split *)
    des; subst; ss. inv RESERVE.
    destruct kind2; ss. destruct msg3; ss. des; subst.
    inv WRITE2. inv WRITE. inv PROMISE. des; ss. inv RESERVE. inv RESERVEORIGINAL.
    ii. contradiction H.
    eapply split_covered with (mem1 := mem1); eauto.
    eapply split_covered with (mem1 := mem2) in H1; eauto.
    eapply NOT_COVER in H1; eauto; ss.
    ii. contradiction H.
    eapply split_covered with (mem1 := mem1); eauto.
  - (* lower *)
    des; subst. destruct kind2; ss. destruct msg1; ss; subst.
    ii.
    eapply NOT_COVER; eauto.
    ii. contradiction H.
    eapply lower_covered with (mem1 := mem1); eauto.
    inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
    eapply lower_covered with (mem2 := mem2'); eauto.
Qed.

Lemma write_not_cover_prsv_write_max
      lc1 sc1 mem1 loc from to val releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from' to' val' releasedr2 released2 lc2' sc2' mem2' kind2 max_ts
      (NOT_COVER: forall t, ~ Cover.covered loc t mem1 -> Time.le t max_ts -> ~ Cover.covered loc t mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from' to' val' releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (LE: Time.le max_ts from')
      (KIND_MATCH: kind_match kind1 kind2):
  forall t, ~ Cover.covered loc t mem1' -> Time.le t max_ts -> ~ Cover.covered loc t mem2'.
Proof.
  inv WRITE1. inv WRITE. inv PROMISE; ss.
  - (* add *)
    destruct kind2; ss.
    ii. exploit NOT_COVER; eauto. ii. contradiction H.
    eapply add_covered with (mem2 := mem1'); eauto.
    inv WRITE2. inv WRITE. inv PROMISE.
    exploit MemoryProps.add_succeed_wf; [eapply MEM0 | eauto..]. ii; des.
    inv H1. inv ITV; ss.
    erewrite Memory.add_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss. inv GET.
    clear - LE H0 FROM.
    cut (Time.le t from0). ii.
    auto_solve_time_rel. ii; auto_solve_time_rel.
    econs; ss; eauto.
    econs; ss; eauto.
  - (* split *)
    des. subst. inv RESERVE.
    destruct kind2; ss. destruct msg3; ss. des; subst.
    inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss.
    inv RESERVE. inv RESERVEORIGINAL.
    ii.
    eapply NOT_COVER in H0; eauto. 
    contradiction H0. eapply split_covered with (mem2 := mem2'); eauto.
    ii. contradiction H. eapply split_covered with (mem1 := mem1); eauto.
  - (* lower *)
    des. subst. destruct kind2; ss. destruct msg1; ss; subst.
    inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
    ii.
    eapply NOT_COVER in H0; eauto.
    contradiction H0. eapply lower_covered with (mem2 := mem2'); eauto.
    ii. contradiction H. eapply lower_covered with (mem1 := mem1); eauto.
Qed.

Lemma write_not_cover_prsv_write
      lc1 sc1 mem1 loc from to val releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 val' releasedr2 released2 lc2' sc2' mem2' kind2
      (NOT_COVER: forall t, ~ Cover.covered loc t mem1 -> ~ Cover.covered loc t mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from to val' releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (KIND_MATCH: kind_match kind1 kind2):
  forall t, ~ Cover.covered loc t mem1' -> ~ Cover.covered loc t mem2'.
Proof.
  inv WRITE1. inv WRITE. inv PROMISE; ss.
  - (* add *)
    destruct kind2; ss.
    ii. exploit NOT_COVER; eauto. instantiate (1 := t). ii. contradiction H.
    eapply add_covered with (mem2 := mem1'); eauto.
    inv H0. inv ITV; ss.
    inv WRITE2. inv WRITE. inv PROMISE.
    erewrite Memory.add_o in GET; eauto.
    des_ifH GET; des; ss; subst; ss. inv GET.
    clear - MEM H FROM TO.
    exploit Memory.add_get0; eauto. ii; des.
    contradiction H.
    econs; eauto. econs; ss; auto.
    exploit Memory.get_ts; eauto. ii; des; subst. auto_solve_time_rel.
    econs; eauto. econs; ss; eauto.
  - (* split *)
    des; subst. inv RESERVE.
    destruct kind2; ss. destruct msg3; ss. des; subst.
    inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss.
    inv RESERVE. inv RESERVEORIGINAL.
    ii.
    eapply NOT_COVER; eauto. 
    ii. contradiction H. eapply split_covered with (mem2 := mem1'); eauto.
    eapply split_covered with (mem2 := mem2'); eauto.
  - (* lower *)
    des. subst. destruct kind2; ss. destruct msg1; ss; subst.
    inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
    ii.
    eapply NOT_COVER; eauto.
    ii. contradiction H. eapply lower_covered with (mem2 := mem1'); eauto.
    eapply lower_covered with (mem2 := mem2'); eauto.
Qed.
    
Lemma identity_inj_incr
      inj loc to
      (MON: monotonic_inj inj)
      (NEW: inj loc to = None)
      (ID: forall ts ts', inj loc ts = Some ts' -> ts = ts'):
  exists inj',
    <<NEW_INJ: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj loc1 to1)>> /\
    <<MON: monotonic_inj inj'>>.
Proof.
  eexists. split. ss.
  unfold monotonic_inj in *. ii.
  des_ifH INJ1.
  {
    inv INJ1; ss; des; subst.
    des_ifH INJ2; ss; des; subst.
    inv INJ2. auto_solve_time_rel.
    eapply ID in INJ2; eauto. subst; eauto.
    eapply ID in INJ2; eauto; subst; eauto.
  }
  {
    ss.
    des_ifH INJ2; ss; des; subst; ss; try solve [eapply MON; eauto].
    inv INJ2. eapply ID in INJ1; eauto. subst; eauto.
  }
Qed.

Lemma GT_inj_incr
      inj loc to to'
      (MON: monotonic_inj inj)
      (GT_INJ: forall ts ts', inj loc ts = Some ts' -> (Time.lt ts to /\ Time.lt ts' to')):
  exists inj',
    <<NEW_INJ: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)>> /\
    <<MON: monotonic_inj inj'>>.
Proof.
  eexists. split.
  instantiate (1 := fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)).
  eauto.
  unfold monotonic_inj in *; ii.
  des_ifH INJ1; ss; des; subst; ss.
  {
    inv INJ1.
    des_ifH INJ2; des; ss; subst; ss.
    inv INJ2. auto_solve_time_rel.
    exploit GT_INJ; eauto. ii; des.
    auto_solve_time_rel. ii. auto_solve_time_rel.
  }
  des_ifH INJ2; des; ss; subst; ss; eauto.
  des_ifH INJ2; des; ss; subst; ss; eauto.
  inv INJ2.
  exploit GT_INJ; eauto. ii; des. auto.
Qed.

Lemma injection_read_step
      inj mem mem' lc loc to val released ord lc1 lo lc'
      (LOCAL_WF: Local.wf lc mem)
      (INJ: MsgInj inj mem mem')
      (READ: Local.read_step lc mem loc to val released ord lc1 lo)
      (TVIEWINJ: TViewInj inj (Local.tview lc) (Local.tview lc')):
  exists lc1' released' to',
    <<INJ_READ: Local.read_step lc' mem' loc to' val released' ord lc1' lo>> /\
    <<INJ_MSG: inj loc to = Some to'>> /\ <<INJ_VIEW: opt_ViewInj inj released released'>>.
Proof.
  inv READ.
  assert(INJ_MSG: exists to' from' released',
            Memory.get loc to' mem' = Some (from', Message.concrete val released') /\
            inj loc to = Some to' /\ opt_ViewInj inj released released').
  {
    clear - INJ GET. inv INJ.
    eapply SOUND in GET; eauto. des.
    exists t' f' R'. eauto.
  }
  destruct INJ_MSG as (to' & from' & released' & INJ_GET & INJ_MSG & INJ_VIEW).
  inv READABLE.
  assert(CUR_VIEW_LOC_INJ: inj loc (View.pln (TView.cur (Local.tview lc)) loc) =
                           Some (View.pln (TView.cur (Local.tview lc')) loc) /\
                           inj loc (View.rlx (TView.cur (Local.tview lc)) loc) =
                           Some (View.rlx (TView.cur (Local.tview lc')) loc)).
  {
    exploit TViewInj_sound_cur_acq; eauto.
    inv LOCAL_WF; eauto.
    ii. des; eauto.
  }
  destruct CUR_VIEW_LOC_INJ as (CUR_PLN_VIEW_LOC_INJ & CUR_RLX_VIEW_LOC_INJ).
  assert(READABLE_INJ: TView.readable (TView.cur (Local.tview lc')) loc to' released' ord).
  {
    econs; eauto.
    eapply Time_le_monotonic_inj; eauto. inv INJ; eauto.
    ii. eapply RLX in H.
    eapply Time_le_monotonic_inj; eauto. inv INJ; eauto.
  }
  do 3 eexists.
  split; eauto.
Qed.

Lemma Local_write_lt_max_ts_reserve
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo max_ts
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (LE: Time.le to max_ts)
      (MAX_RESERVE: exists from, Memory.get loc max_ts mem = Some (from, Message.reserve)):
  Time.lt to max_ts.
Proof.
  des. eapply Time.le_lteq in LE. des; eauto; subst.
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  - eapply Memory.add_get0 in MEM; eauto; des.
    rewrite MAX_RESERVE in GET; ss.
  - des; subst. inv RESERVE.
    eapply Memory.split_get0 in MEM; eauto; des.
    rewrite MAX_RESERVE in GET; ss.
  - des; subst.
    eapply Memory.lower_get0 in MEM; eauto; des.
    rewrite MAX_RESERVE in GET; ss.
Qed.

Lemma Local_write_add_lt_max_ts_reserve
      lc sc mem loc from to val releasedr released ord lc' sc' mem' lo max_ts
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' Memory.op_kind_add lo)
      (LE: Time.le to max_ts)
      (MAX_RESERVE: exists from msg, Memory.get loc max_ts mem = Some (from, msg)):
  Time.lt to max_ts.
Proof.
  des. inv WRITE. inv WRITE0. inv PROMISE.
  eapply Time.le_lteq in LE; des; eauto. subst.
  exploit Memory.add_get0; [eapply MEM | eauto..]; ii; des.
  rewrite MAX_RESERVE in GET; inv GET.
Qed.

Lemma injection_write_step_id_loc0
      inj mem mem' lc sc mem1 lc1 sc1 loc from to val releasedr releasedr' releasedw kind lo ord 
      max_ts lc' sc'
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw ord lc1 sc1 mem1 kind lo)
      (LE_MAX: Time.le to max_ts)
      (NO_GT_MAX: forall ts from val R,
          Memory.get loc ts mem = Some (from, Message.concrete val R) -> Time.le ts max_ts)
      (LOC_COVER: forall ts, ~ Cover.covered loc ts mem -> Time.le ts max_ts -> ~ Cover.covered loc ts mem')
      (MAX_RESERVE: exists from msg, Memory.get loc max_ts mem = Some (from, msg))
      (MEM_INJ: MsgInj inj mem mem')
      (LOCAL_WF: Local.wf lc mem)
      (LOCAL_WF': Local.wf lc' mem')
      (CLOSED_MEM: Memory.closed mem)
      (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
      (CLOSED_VIEW: Memory.closed_opt_view releasedr mem)
      (VIEW_INJ: opt_ViewInj inj releasedr releasedr')
      (INJ_LOC0: forall t t', inj loc t = Some t' -> Time.le t max_ts -> t = t')
      (PRM_EQ: promise_inj inj (Local.promises lc) (Local.promises lc')):
  exists lc1' releasedw' mem1' inj' kind',
    <<INJ_WRITE: Local.write_step lc' sc' mem' loc from to val releasedr' releasedw' ord lc1' sc' mem1' kind' lo>> /\
    <<KIND: kind_match kind kind'>> /\
    <<INJ_MSG: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj loc1 to1)>> /\
    <<INJ_INCR: incr_inj inj inj'>> /\ <<MON_INJ: monotonic_inj inj' >> /\
    <<INJ_VIEW: opt_ViewInj inj' releasedw releasedw'>> /\ 
    <<INJ_COMPLETE: forall loc to to', inj' loc to = Some to' ->
                                  exists val f R, Memory.get loc to mem1 = Some (f, Message.concrete val R)>> /\
    <<SPLIT_INJ: forall t val R, kind = Memory.op_kind_split t (Message.concrete val R) ->
                         exists t' val' R', kind' = Memory.op_kind_split t' (Message.concrete val' R') /\
                                       inj loc t = Some t'>>.
Proof.
  destruct lc, lc1. 
  destruct MAX_RESERVE as (from''' & msg''' & MAX_RESERVE).
  exploit MemoryProps.write_msg_wf; eauto.
  ii; des.
  assert(CLOSED_RELEASEDR: closed_opt_viewinj inj releasedr).
  {
    eapply closed_optview_msginj_implies_closed_viewInj; eauto. 
  }
  assert(CLOSED_TVIEWINJ: closed_tviewInj inj tview).
  {
    clear - LOCAL_WF MEM_INJ.
    eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
    inv LOCAL_WF; eauto.
  } 
  destruct kind.
  { 
    (* add *)
    assert(LT_MAX: Time.lt to max_ts).
    {
      eapply Local_write_add_lt_max_ts_reserve; eauto.
    }
    inv WRITE. inv LC2. ss.
    assert(ADD_NOT_COVER: forall ts, Interval.mem (from, to) ts -> ~ Cover.covered loc ts mem).
    {
      inv WRITE0. inv PROMISE.
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    } 
    exploit Memory.write_get2; eauto. ii. des.
    lets GET_MEM': GET_MEM. 
    eapply Memory.next_exists with (ts := to) in GET_MEM'; eauto.
    des.
    assert(NXT_ORIGN: Memory.get loc to0 mem = Some (from0, msg)).
    {
      clear MAX_RESERVE.
      inv WRITE0. inv PROMISE. 
      erewrite Memory.add_o in GET_MEM'; eauto. 
      des_ifH GET_MEM'; eauto; ss; des; subst; ss.
      clear - GET_MEM'0. auto_solve_time_rel.
    } 
    assert(WF_ITV_MSG': Time.lt from0 to0).
    {
      auto_solve_time_rel.
    } 
    assert(WF_NEXT: forall ts, Time.lt to ts -> Time.lt ts to0 -> Memory.get loc ts mem = None).
    {
      ii.
      exploit GET_MEM'1; [eapply H | eapply H0 | eauto..].
      ii.
      inv WRITE0. inv PROMISE.
      erewrite Memory.add_o in H1; eauto.
      des_ifH H1; des; ss; eauto.
    }
    assert(LE_MAX': Time.le to0 max_ts).
    {
      destruct (Time.le_lt_dec to0 max_ts); eauto.
      clear - LE_MAX WRITE0 WF_NEXT l MAX_RESERVE.
      eapply Time.le_lteq in LE_MAX. des; subst; eauto.
      specialize (WF_NEXT max_ts).
      exploit WF_NEXT; eauto. introv Hcontr. rewrite MAX_RESERVE in Hcontr. ss.
      inv WRITE0. inv PROMISE.
      exploit Memory.add_get0; [eapply MEM | eauto..]. ii; des.
      rewrite MAX_RESERVE in GET; ss.
    }
    assert(NEXT_NOT_ATTACH: Time.lt to from0).
    {
      destruct(Time.le_lt_dec from0 to); eauto.
      eapply Time.le_lteq in l; des; subst. 
      clear - GET_MEM GET_MEM' l GET_MEM'0 FROMTO. 
      exploit Memory.get_disjoint; [eapply GET_MEM | eapply GET_MEM' | eauto..]; eauto.
      ii; des; subst. 
      auto_solve_time_rel.
      unfold Interval.disjoint in *.
      specialize (H to). exploit H; eauto; ii; ss.
      econs; eauto; ss. clear. auto_solve_time_rel.
      econs; ss; eauto. clear - GET_MEM'0. auto_solve_time_rel.
      inv WRITE0. inv PROMISE.
      erewrite Memory.add_o in GET_MEM'; eauto.
      des_ifH GET_MEM'; ss; des; subst; ss; eauto.
      eapply ATTACH in GET_MEM'; eauto; ss.
    }
    assert(IS_NEXT: forall ts, Interval.mem (to, from0) ts -> ~ Cover.covered loc ts mem).
    {
      clear - ADD_NOT_COVER GET_MEM'1 NEXT_NOT_ATTACH WF_ITV_MSG' GET_MEM' NXT_ORIGN WRITE0.
      eapply ITV_NEXT_NOTCOVER; eauto.
      inv WRITE0. inv PROMISE; ss.
      ii.
      exploit GET_MEM'1; [eapply H | eapply H0 | eauto..]. ii.
      erewrite Memory.add_o in H1; eauto.
      des_ifH H1; ss; eauto.
    }
    assert(PRE_ADD_NOT_COVER: forall ts, Interval.mem (from, from0) ts -> ~ Cover.covered loc ts mem).
    { 
      clear - ADD_NOT_COVER NEXT_NOT_ATTACH IS_NEXT FROMTO. ii.
      destruct(Time.le_lt_dec ts to).
      {
        eapply ADD_NOT_COVER; eauto.
        inv H; ss.
      }
      {
        eapply IS_NEXT; eauto.
        inv H; ss.
      }
    }
    assert(PRE_ADD_NOT_COVER': forall ts, Interval.mem (from, from0) ts -> ~ Cover.covered loc ts mem').
    {  
      clear - LOC_COVER WF_ITV_MSG' LE_MAX' PRE_ADD_NOT_COVER. 
      introv ITV. lets ITV': ITV. eapply PRE_ADD_NOT_COVER in ITV.
      inv ITV'; ss. 
      cut(Time.le ts max_ts). intro; eauto.
      eapply Time.le_lteq. left.
      cut(Time.lt ts to0). i. auto_solve_time_rel.
      auto_solve_time_rel.
    } 
    exploit identity_inj_incr.
    inv MEM_INJ; eauto.
    instantiate (2 := loc); instantiate (1 := to).
    clear - MEM_INJ WRITE0.
    inv WRITE0. inv PROMISE. eapply Memory.add_get0 in MEM; eauto. des.
    eapply MsgInj_not_in_dom; eauto.
    clear - MEM_INJ INJ_LOC0 NO_GT_MAX.
    ii. eapply INJ_LOC0; eauto.
    inv MEM_INJ. eapply COMPLETE in H; des.
    eapply NO_GT_MAX in H; eauto.
    introv NEW_INJ. destruct NEW_INJ as (inj' & NEW_INJ' & MON_NEWINJ).
    assert(INCR_INJ: incr_inj inj inj').
    {
      rewrite NEW_INJ'. unfold incr_inj. ii.
      des_if; subst; ss; des; ss; subst; eauto.
      clear - WRITE0 MEM_INJ H.
      inv WRITE0. inv PROMISE. eapply Memory.add_get0 in MEM; eauto. des.
      inv MEM_INJ.
      eapply COMPLETE in H. des. rewrite H in GET. inv GET.
    }
    assert(WRITE': exists mem1', Memory.write (Local.promises lc') mem' loc from to val
                                         (TView.write_released (Local.tview lc') sc' loc to releasedr' ord)
                                         (Local.promises lc') mem1' Memory.op_kind_add).
    {
      exploit MemoryProps.write_succeed_valid.
      Focus 7. ii; des; eauto.
      {
        clear - LOCAL_WF' PRM_EQ. subst. inv LOCAL_WF'; eauto.
      }
      {
        clear - FROMTO NEXT_NOT_ATTACH PRE_ADD_NOT_COVER'. ii.
        exploit PRE_ADD_NOT_COVER'; eauto. inv H; ss.
        econs; ss. eapply Time.le_lteq. left. auto_solve_time_rel.
      }
      { 
        eapply TLE_write_prs with (inj := inj'); eauto.
        rewrite NEW_INJ'. des_if; eauto. ss; subst; ss. destruct o; ss.
        eapply incr_inj_opt_ViewInj; eauto.
        eapply incr_inj_TViewInj; eauto.
        eapply incr_inj_closed_tviewInj; eauto.
        eapply incr_inj_closed_opt_ViewInj; eauto.
      } 
      eauto.  
      clear - NEXT_NOT_ATTACH PRE_ADD_NOT_COVER' FROMTO. introv ATTACH.
      unfold MemoryProps.attatched_time in *. des.
      destruct(Time.le_lt_dec to' from0); eauto.
      eapply PRE_ADD_NOT_COVER' with (ts := to'); eauto.
      econs; eauto; ss. clear - GET FROMTO.
      eapply Memory.get_ts in GET; des; subst. auto_solve_time_rel. auto_solve_time_rel.
      econs; eauto. econs; ss; eauto. eapply Memory.get_ts in GET; des; subst; eauto; try auto_solve_time_rel.
      clear. auto_solve_time_rel. 
      eapply PRE_ADD_NOT_COVER' with (ts := from0); eauto.
      econs; ss; eauto. clear - FROMTO NEXT_NOT_ATTACH. auto_solve_time_rel.
      clear. auto_solve_time_rel.
      econs; ss; eauto. econs; eauto; ss. clear - l; auto_solve_time_rel.   
      clear - MSGWF VIEW_INJ MEM_INJ TVIEW_INJ CLOSED_TVIEWINJ NEW_INJ' MON_NEWINJ INCR_INJ CLOSED_RELEASEDR.
      inv MSGWF. econs.  
      eapply View_opt_wf_inj with (inj := inj'); eauto.
      eapply incr_inj_TViewInj; eauto. 
      eapply incr_inj_opt_ViewInj; eauto. 
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      rewrite NEW_INJ'. des_if; eauto. ss; tryfalse. des; tryfalse.
    }
    destruct WRITE' as (mem1' & WRITE').
    do 2 eexists. exists mem1' inj' Memory.op_kind_add.
    split; subst.
    econs; eauto.
    clear - LE_MAX INJ_LOC0 WRITABLE TVIEW_INJ NEW_INJ' INCR_INJ MON_NEWINJ CLOSED_TVIEWINJ.
    inv WRITABLE. econs. 
    eapply writable_inj with (inj := inj'); eauto.
    eapply incr_inj_TViewInj; eauto. eapply incr_inj_closed_tviewInj; eauto.
    rewrite NEW_INJ'. des_if; eauto; ss; des; ss.
    clear - RELEASE LOCAL_WF LOCAL_WF' MEM_INJ PRM_EQ.
    introv ORDER. eapply RELEASE in ORDER.
    inv LOCAL_WF. inv LOCAL_WF'. ss.
    eapply mem_nonsynch_loc_msgInj in ORDER; eauto.
    split; eauto.
    split; eauto.
    split; eauto. 
    split; eauto.
    split. 
    {
      eapply opt_ViewInj_write_released_inj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      rewrite NEW_INJ'. des_if; eauto; des; subst; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }
 
    split; try solve [ii; ss].
    introv INJ'. rewrite NEW_INJ' in INJ'.
    des_ifH INJ'; eauto; des; ss; subst. inv INJ'. eauto.
    clear - MEM_INJ INJ' WRITE0 o.
    inv WRITE0. inv PROMISE.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; try solve [inv MEM_INJ; eapply COMPLETE; eauto].
    clear - MEM_INJ INJ' WRITE0 o.
    inv WRITE0. inv PROMISE.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; try solve [inv MEM_INJ; eapply COMPLETE; eauto].
    eapply Memory.max_ts_spec in GET_MEM'; des.
    eapply Time.le_lteq in MAX; eauto; des; eauto; subst.
    clear - LT_MAX WRITE0 MAX_RESERVE.
    inv WRITE0. inv PROMISE; ss.
    eapply Memory.add_get1 in MAX_RESERVE; eauto.
    eapply Memory.max_ts_spec in MAX_RESERVE; eauto; des.
    clear - LT_MAX MAX. auto_solve_time_rel.
  }
  { 
    (* split *) 
    inv WRITE. inv LC2. ss.
    assert(LT_MAX_TO: Time.lt to ts3).
    {
      clear - WRITE0. inv WRITE0. inv PROMISE. des; subst.
      inv RESERVE.
      exploit MemoryProps.split_succeed_wf; eauto. ii; des; eauto.
    }
    subst.
    destruct lc' as (tview' & promises'); ss.
    exploit identity_inj_incr.
    inv MEM_INJ; eauto.
    instantiate (2 := loc); instantiate (1 := to).
    clear - MEM_INJ WRITE0.
    inv WRITE0. inv PROMISE. des; subst. inv RESERVE.
    eapply Memory.split_get0 in MEM; eauto. des.
    eapply MsgInj_not_in_dom; eauto. 
    clear - MEM_INJ INJ_LOC0 LT_MAX_TO NO_GT_MAX.
    ii. eapply INJ_LOC0; eauto.
    inv MEM_INJ. eapply COMPLETE in H; des.
    eapply NO_GT_MAX in H; eauto.
    introv NEW_INJ. destruct NEW_INJ as (inj' & NEW_INJ' & MON_NEWINJ).
    assert(INCR_INJ: incr_inj inj inj').
    {
      rewrite NEW_INJ'. unfold incr_inj. ii.
      des_if; subst; ss; des; ss; subst; eauto.
      clear - WRITE0 MEM_INJ H.
      inv WRITE0. inv PROMISE. des; subst. inv RESERVE.
      eapply Memory.split_get0 in MEM; eauto. des.
      inv MEM_INJ.
      eapply COMPLETE in H. des. rewrite H in GET. inv GET.
    }
    assert(MSG_WF: Message.wf (Message.concrete val (TView.write_released tview' sc loc to releasedr' ord))).
    {
      inv MSGWF.
      econs; eauto.
      eapply View_opt_wf_inj with (inj := inj'); eauto.
      eapply incr_inj_TViewInj; eauto. 
      eapply incr_inj_opt_ViewInj; eauto. 
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      rewrite NEW_INJ'. des_if; eauto. ss; tryfalse. des; tryfalse.
    }
    assert(LT_TS3: Time.le ts3 max_ts).
    {
      clear - NO_GT_MAX WRITE0.
      inv WRITE0. inv PROMISE. des; subst. inv RESERVE.
      exploit Memory.split_get0; eauto. ii; des; eauto.
    } 
    assert(GET_PROMISE': exists val3 R3,
              Memory.get loc ts3 promises' = Some (from, Message.concrete val3 R3)).
    {
      clear - NO_GT_MAX WRITE0 INJ_LOC0 PRM_EQ LT_TS3.
      inv WRITE0. inv PROMISE. des; subst. inv RESERVE.
      exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des; eauto.
      inv PRM_EQ.
      exploit SOUND; eauto. ii; des.
      exploit INJ_LOC0; eauto; ii; subst. eauto.
    }
    destruct GET_PROMISE' as (val3 & R3 & GET_PROMISE').
    assert(WRITE1: exists mem1' promises2',
              Memory.write promises' mem' loc from to val
                           (TView.write_released tview' sc' loc to releasedr' ord)
                           promises2' mem1' (Memory.op_kind_split ts3 (Message.concrete val3 R3))).
    { 
      inv WRITE0. inv PROMISE; des; inv RESERVE. 
      lets GET_TS3_MEM': GET_PROMISE'.
      inv LOCAL_WF'; ss. eapply PROMISES0 in GET_TS3_MEM'.
      exploit Memory.split_exists; [eapply GET_TS3_MEM' | eauto..].
      introv MEM_SPLIT. destruct MEM_SPLIT as (mem2 & MEM_SPLIT).
      exploit Memory.split_exists; [eapply GET_PROMISE' | eauto..].
      introv PROMISES_SPLIT. destruct PROMISES_SPLIT as (promises0' & PROMISES_SPLIT).
      exploit Memory.split_get0; [eapply PROMISES_SPLIT | eauto..]. ii; des.
      exploit Memory.remove_exists; [eapply GET1 | eauto..].
      introv PROM_REMOVE. destruct PROM_REMOVE as (promises2' & PROM_REMOVE).
      exists mem2 promises2'.
      econs; eauto. 
      econs; eauto.
      econs.
      eapply TLE_write_prs with
          (inj :=
             fun (loc1 : Loc.t) (to1 : Time.t) =>
               if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else inj loc1 to1); eauto.
      des_if; eauto; ss; des; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }
    destruct WRITE1 as (mem1' & promises1' & WRITE1).
    do 4 eexists. exists (Memory.op_kind_split ts3 (Message.concrete val3 R3)). split.
    { 
      econs; eauto; ss.
      econs. inv WRITABLE. 
      eapply writable_inj with (inj := inj'); eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      rewrite NEW_INJ'. des_if; eauto; des; ss.
      introv ORDER. eapply RELEASE in ORDER.
      inv LOCAL_WF; inv LOCAL_WF'; ss.
      eapply mem_nonsynch_loc_msgInj; eauto.
    }
    split.
    {
      inv WRITE0. inv PROMISE; des; subst. inv RESERVE.
      eapply Memory.split_get0 in PROMISES; eauto; des.
      inv PRM_EQ.
      exploit SOUND; eauto; ii. des.
      exploit INJ_LOC0; eauto; ii; subst.
      rewrite GET_PROMISE' in H0. inv H0. eauto.
    }
    split; eauto.
    split; eauto.
    split; eauto.
    split. 
    {
      ss. eapply opt_ViewInj_write_released_inj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      rewrite NEW_INJ'. des_if; eauto; des; subst; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }

    split. introv INJ'.
    rewrite NEW_INJ' in INJ'.
    des_ifH INJ'; ss; des; subst; ss.
    inv INJ'.
    clear - WRITE0. inv WRITE0. inv PROMISE; des; ss; subst; ss. inv RESERVE.
    eapply Memory.split_get0 in MEM; eauto; des; eauto.
    clear - MEM_INJ INJ' WRITE0.
    inv MEM_INJ. exploit COMPLETE; eauto; ii; des.
    inv WRITE0. inv PROMISE. des; ss; subst; ss. inv RESERVE.
    eapply Memory.split_get1 in MEM; eauto; des; eauto.
    clear - MEM_INJ INJ' WRITE0.
    inv MEM_INJ. exploit COMPLETE; eauto; ii; des.
    inv WRITE0. inv PROMISE. des; ss; subst; ss. inv RESERVE.
    eapply Memory.split_get1 in MEM; eauto; des; eauto.

    ii. inv H. do 3 eexists. split; eauto.
    clear - INJ_LOC0 LT_TS3 WRITE0 MEM_INJ.
    inv WRITE0. inv PROMISE. des; subst. inv RESERVE. inv RESERVEORIGINAL.
    exploit Memory.split_get0; [eapply MEM | eauto..]; ii; des.
    inv MEM_INJ. exploit SOUND; eauto. ii; des.
    exploit INJ_LOC0; eauto. ii; subst; eauto.
  }
  {
    (* lower *)
    inv WRITE. inv LC2. ss.
    destruct lc' as (tview' & promises'); ss.
    assert(GET_PROMISE: exists R1, 
              Memory.get loc to promises = Some (from, msg1) /\
              msg1 = Message.concrete val R1).
    {
      clear - WRITE0. inv WRITE0. inv PROMISE. des; subst.
      eapply Memory.lower_get0 in PROMISES; eauto; des; eauto.
      inv MSG_LE; eauto.
    }
    destruct GET_PROMISE as (R1 & GET_PROMISE & MSG1). subst.
    assert(ID_INJ: inj loc to = Some to).
    {
      clear - LE_MAX INJ_LOC0 GET_PROMISE MEM_INJ LOCAL_WF.
      inv LOCAL_WF; ss.
      eapply PROMISES in GET_PROMISE.
      inv MEM_INJ. eapply SOUND in GET_PROMISE; eauto; des.
      exploit INJ_LOC0; eauto.
      auto_solve_time_rel.
      ii; subst; eauto.
    }
    assert(MSG_WF: Message.wf (Message.concrete val (TView.write_released tview' sc loc to releasedr' ord))).
    {
      inv MSGWF.
      econs; eauto.
      eapply View_opt_wf_inj with (inj := inj); eauto.
      inv MEM_INJ; eauto.
    }  
    assert(GET_PROMISE': exists R1', Memory.get loc to promises' = Some (from, Message.concrete val R1')
                                /\ opt_ViewInj inj R1 R1').
    { 
      clear - ID_INJ GET_PROMISE PRM_EQ MEM_INJ LOCAL_WF LOCAL_WF'.
      inv PRM_EQ. inv MEM_INJ.
      exploit SOUND; eauto. ii; des.
      inv LOCAL_WF; ss. exploit PROMISES; eauto; ii.
      inv LOCAL_WF'; ss. exploit PROMISES0; eauto; ii.
      exploit SOUND0; eauto; ii; des.
      rewrite ID_INJ in H, H3; inv H; inv H3.
      rewrite H2 in H5; inv H5. eauto.
    }
    destruct GET_PROMISE' as (R1' & GET_PROMISE' & OPT_RELEASED_INJ).
    assert(VIEW_LE: View.opt_le (TView.write_released tview' sc loc to releasedr' ord) R1').
    {
      inv WRITE0. inv PROMISE; des. inv RESERVE.
      exploit Memory.lower_get0; eauto; ii; des. inv MSG_LE.
      eapply view_opt_le_inj; eauto. 
      eapply opt_ViewInj_write_released_inj; eauto.
      inv MEM_INJ; eauto.
      eapply closed_opt_viewInj_write_released; eauto.
      eapply closed_optview_msginj_implies_closed_viewInj; eauto.
      clear - CLOSED_MEM GET.
      inv CLOSED_MEM.
      eapply CLOSED in GET; des. inv MSG_CLOSED; eauto.
      inv MEM_INJ; eauto.
    }
    assert(WRITE1: exists mem1' promises2',
              Memory.write promises' mem' loc from to val
                           (TView.write_released tview' sc' loc to releasedr' ord)
                           promises2' mem1' (Memory.op_kind_lower (Message.concrete val R1'))).
    {
      inv WRITE0. inv PROMISE; des. inv RESERVE.
      lets GET_MEM': GET_PROMISE'.
      inv LOCAL_WF'; ss. eapply PROMISES0 in GET_MEM'.
      exploit Memory.lower_exists; eauto.
      introv MEM_LOWER'. destruct MEM_LOWER' as (mem2' & MEM_LOWER').
      exploit Memory.lower_exists; [eapply GET_PROMISE' | eauto..].
      introv PROM_LOWER'. destruct PROM_LOWER' as (promises2' & PROM_LOWER').
      exploit Memory.lower_get0; [eapply PROM_LOWER' | eauto..]. ii; des.
      exploit Memory.remove_exists; eauto.
      introv PROM_REMOVE'. destruct PROM_REMOVE' as (promises1' & PROM_REMOVE').
      do 2 eexists.
      econs; eauto.
      econs; eauto.
      econs.
      eapply TLE_write_prs with (inj := inj); eauto.
      inv MEM_INJ; eauto.
    }
    destruct WRITE1 as (mem1' & promises1' & WRITE1).
    do 5 eexists.
    split.
    {
      econs; eauto; ss.
      econs. inv WRITABLE.
      eapply writable_inj with (inj := inj); eauto.
      inv MEM_INJ; eauto.
      introv ORDER. eapply RELEASE in ORDER.
      inv LOCAL_WF; inv LOCAL_WF'; ss.
      eapply mem_nonsynch_loc_msgInj; eauto.
    }
    split; eauto.
    split.
    {
      instantiate (1 := inj).
      eapply functional_extensionality. ii.
      eapply functional_extensionality. ii.
      des_if; eauto; ss; des; subst; eauto.
    }
    split.
    {
      unfold incr_inj; ii; eauto.
    }
    split.
    {
      inv MEM_INJ; eauto.
    }
    split.
    {
      ss.
      eapply opt_ViewInj_write_released_inj; eauto.
      inv MEM_INJ; eauto.
    }
    split; try solve [ii; ss].
    { 
      clear - MEM_INJ WRITE0. ii. inv MEM_INJ; eauto.
      eapply COMPLETE in H; eauto; des.
      inv WRITE0. inv PROMISE. des. inv RESERVE.
      exploit Memory.lower_get1; eauto. ii; des; eauto. inv MSG_LE; eauto.
    }
  }
  {
    (* cancel *)
    clear - WRITE. inv WRITE; ss. inv LC2.
    inv WRITE0. inv PROMISE; ss.
  }
Qed.

Lemma injection_write_step_id_loc0_GT
      inj mem mem' lc sc mem1 lc1 sc1 loc from to val releasedr releasedr' releasedw kind lo ord 
      max_ts lc' sc' from' to'
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw ord lc1 sc1 mem1 kind lo)
      (GT_MAX: Time.lt max_ts to)
      (NO_GT_TO: forall ts from val released,
          Memory.get loc ts mem = Some (from, Message.concrete val released) -> Time.lt ts to)
      (MEM_INJ: MsgInj inj mem mem')
      (LOCAL_WF: Local.wf lc mem)
      (LOCAL_WF': Local.wf lc' mem')
      (CLOSED_MEM: Memory.closed mem)
      (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
      (CLOSED_VIEW: Memory.closed_opt_view releasedr mem)
      (VIEW_INJ: opt_ViewInj inj releasedr releasedr')
      (PRM_EQ: promise_inj inj (Local.promises lc) (Local.promises lc'))
      (FROM'_GE: forall ts from msg, Memory.get loc ts mem' = Some (from, msg) -> Time.le ts from')
      (FROM'_TO': Time.lt from' to'):
  exists lc1' releasedw' mem1' inj',
    <<INJ_WRITE: Local.write_step lc' sc' mem' loc from' to' val releasedr' releasedw' ord lc1' sc' mem1' kind lo>> /\
    <<INJ_MSG: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)>> /\
    <<INJ_INCR: incr_inj inj inj'>> /\ <<MON_INJ: monotonic_inj inj' >> /\
    <<INJ_VIEW: opt_ViewInj inj' releasedw releasedw'>> /\ 
    <<INJ_COMPLETE: forall loc to to', inj' loc to = Some to' ->
                                  exists val f R, Memory.get loc to mem1 = Some (f, Message.concrete val R)>> /\
    <<KIND: kind = Memory.op_kind_add>>. 
Proof.
  destruct lc, lc1; ss.
  inv WRITE. inv LC2. ss.
  exploit MemoryProps.write_msg_wf; eauto. ii; des.
  assert(CLOSED_RELEASEDR: closed_opt_viewinj inj releasedr).
  {
    eapply closed_optview_msginj_implies_closed_viewInj; eauto. 
  }
  assert(CLOSED_TVIEWINJ: closed_tviewInj inj tview).
  {
    clear - LOCAL_WF MEM_INJ.
    eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
    inv LOCAL_WF; eauto.
  } 
  destruct kind.
  {
    (* add *)
    exploit GT_inj_incr. inv MEM_INJ; eauto.
    instantiate (1 := to'). instantiate (1 := to). instantiate (1 := loc).
    introv INJ.
    split.
    {
      inv MEM_INJ.
      exploit COMPLETE; eauto. ii; des. eauto.
    }
    {
      inv MEM_INJ.
      exploit COMPLETE; eauto. ii; des.
      exploit SOUND; eauto. ii; des.
      rewrite INJ in H0; inv H0.
      eapply FROM'_GE in H2.
      auto_solve_time_rel.
    }

    introv NEW_INJ.
    destruct NEW_INJ as (inj' & NEW_INJ & MON_NEW_INJ).
    assert(INCR_INJ: incr_inj inj inj').
    {
      rewrite NEW_INJ. unfold incr_inj. ii.
      des_if; subst; ss; des; ss; subst; eauto.
      clear - WRITE0 MEM_INJ H.
      inv WRITE0. inv PROMISE. eapply Memory.add_get0 in MEM; eauto. des.
      inv MEM_INJ.
      eapply COMPLETE in H. des. rewrite H in GET. inv GET.
    }
    assert(WRITE': exists mem1',
              Memory.write (Local.promises lc') mem' loc from' to' val
                           (TView.write_released (Local.tview lc') sc' loc to' releasedr' ord)
                           (Local.promises lc') mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      inv LOCAL_WF'; eauto.
      ii. inv COVER. inv ITV; ss. inv H; ss.
      eapply FROM'_GE in GET.
      clear - GET FROM0 TO.
      cut(Time.lt from' to0). ii. clear - GET H. auto_solve_time_rel.
      auto_solve_time_rel.

      eapply TLE_write_prs with (inj := inj'); eauto.
      rewrite NEW_INJ. des_if; eauto. ss; subst; ss. destruct o; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.

      ii. inv H. des.
      exploit MemoryProps.memory_get_ts_le; eauto. ii.
      eapply FROM'_GE in GET.
      cut(Time.lt from' x). ii. clear - GET H0. auto_solve_time_rel.
      auto_solve_time_rel.

      clear - MSGWF VIEW_INJ MEM_INJ TVIEW_INJ CLOSED_TVIEWINJ NEW_INJ MON_NEW_INJ INCR_INJ CLOSED_RELEASEDR.
      inv MSGWF. econs.
      eapply View_opt_wf_inj with (inj := inj'); eauto.
      eapply incr_inj_TViewInj; eauto. 
      eapply incr_inj_opt_ViewInj; eauto. 
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      rewrite NEW_INJ. des_if; eauto. ss; tryfalse. des; tryfalse.
    }
    assert(PROM_WRITE_EQ: promises = promises2).
    {
      clear - WRITE0. inv WRITE0. inv PROMISE.
      eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    }
    subst.
    destruct WRITE' as (mem1' & WRITE').

    do 4 eexists.
    split.
    {
      econs; eauto.
      econs. inv WRITABLE.
      eapply writable_inj with (inj := inj'); eauto.
      eapply incr_inj_TViewInj; eauto. eapply incr_inj_closed_tviewInj; eauto.
      rewrite NEW_INJ. des_if; eauto; ss; des; ss.
      clear - RELEASE LOCAL_WF LOCAL_WF' MEM_INJ PRM_EQ.
      introv ORDER. eapply RELEASE in ORDER.
      inv LOCAL_WF. inv LOCAL_WF'. ss.
      eapply mem_nonsynch_loc_msgInj in ORDER; eauto.
    }
    split. eauto.
    split; eauto.
    split; eauto.
    split.
    {
      eapply opt_ViewInj_write_released_inj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      rewrite NEW_INJ. des_if; eauto; des; subst; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }
    split; eauto.
    {
      introv INJ'. rewrite NEW_INJ in INJ'.
      des_ifH INJ'; ss; des; subst; ss.
      inv INJ'.
      clear - WRITE0. inv WRITE0. inv PROMISE. exploit Memory.add_get0; eauto. ii; des; eauto.
      inv MEM_INJ. exploit COMPLETE; eauto. ii; des.
      clear - WRITE0 H. inv WRITE0. inv PROMISE. exploit Memory.add_get1; eauto.
      inv MEM_INJ. exploit COMPLETE; eauto. ii; des.
      clear - WRITE0 H. inv WRITE0. inv PROMISE. exploit Memory.add_get1; eauto.
    }
  }
  {
    (* split *)
    inv WRITE0. inv PROMISE. des; ss; subst; ss. inv RESERVE.
    exploit MemoryProps.split_succeed_wf; eauto. ii; des.
    eapply NO_GT_TO in GET2.
    clear - GET2 TS23. auto_solve_time_rel. ii. auto_solve_time_rel.
  }
  {
    (* lower *)
    inv WRITE0. inv PROMISE. des; ss; subst; ss.
    exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
    eapply NO_GT_TO in GET.
    auto_solve_time_rel.
  }
  {
    (* cancel *)
    inv WRITE0. inv PROMISE. ss.
  }
Qed.

Lemma injection_write_step_id
      inj mem mem' lc sc mem1 lc1 sc1 loc from to val releasedr releasedr' releasedw kind lo ord lc' sc'
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw ord lc1 sc1 mem1 kind lo)
      (LOC_COVER: forall ts, ~ Cover.covered loc ts mem -> ~ Cover.covered loc ts mem')
      (MEM_INJ: MsgInj inj mem mem')
      (LOCAL_WF: Local.wf lc mem)
      (LOCAL_WF': Local.wf lc' mem')
      (CLOSED_MEM: Memory.closed mem)
      (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
      (CLOSED_VIEW: Memory.closed_opt_view releasedr mem)
      (VIEW_INJ: opt_ViewInj inj releasedr releasedr')
      (INJ_LOC0: forall t t', inj loc t = Some t' -> t = t')
      (PRM_EQ: promise_inj inj (Local.promises lc) (Local.promises lc')):
  exists lc1' releasedw' mem1' inj' kind',
    <<INJ_WRITE: Local.write_step lc' sc' mem' loc from to val releasedr' releasedw' ord lc1' sc' mem1' kind' lo>> /\
    <<KIND: kind_match kind kind'>> /\
    <<INJ_MSG: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj loc1 to1)>> /\
    <<INJ_INCR: incr_inj inj inj'>> /\ <<MON_INJ: monotonic_inj inj' >> /\
    <<INJ_VIEW: opt_ViewInj inj' releasedw releasedw'>> /\ 
    <<INJ_COMPLETE: forall loc to to', inj' loc to = Some to' ->
                                  exists val f R, Memory.get loc to mem1 = Some (f, Message.concrete val R)>> /\
    <<SPLIT_INJ: forall t val R, kind = Memory.op_kind_split t (Message.concrete val R) ->
                         exists t' val' R', kind' = Memory.op_kind_split t' (Message.concrete val' R') /\
                                       inj loc t = Some t'>>.
Proof.
  destruct (Time.le_lt_dec to (Memory.max_ts loc mem)) as [LE_MAX | GT_MAX].
  {
    lets TEMP: WRITE.
    destruct (classic (exists f' ts' msg', Memory.get loc ts' mem = Some (f', msg'))).
    {
      eapply injection_write_step_id_loc0 with (lc' := lc') (mem' := mem') in TEMP; eauto.
      ii. exploit Memory.max_ts_spec; eauto. ii; des; eauto.
      des. exploit Memory.max_ts_spec; eauto. ii; des; eauto.
    }
    {
      destruct lc, lc1. 
      exploit MemoryProps.write_msg_wf; eauto. ii; des.
      assert(CLOSED_RELEASEDR: closed_opt_viewinj inj releasedr).
      {
        eapply closed_optview_msginj_implies_closed_viewInj; eauto. 
      }
      assert(CLOSED_TVIEWINJ: closed_tviewInj inj tview).
      {
        clear - LOCAL_WF MEM_INJ.
        eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
        inv LOCAL_WF; eauto.
      } 
      destruct kind.
      {
        (* add *)
        inv WRITE. inv LC2. ss.
        exploit identity_inj_incr.
        inv MEM_INJ; eauto.
        instantiate (2 := loc); instantiate (1 := to).
        clear - MEM_INJ WRITE0.
        inv WRITE0. inv PROMISE. eapply Memory.add_get0 in MEM; eauto. des.
        eapply MsgInj_not_in_dom; eauto. eauto.
        introv NEW_INJ. destruct NEW_INJ as (inj' & NEW_INJ' & MON_NEWINJ).
        assert(INCR_INJ: incr_inj inj inj').
        {
          rewrite NEW_INJ'. unfold incr_inj. ii.
          des_if; subst; ss; des; ss; subst; eauto.
          clear - WRITE0 MEM_INJ H0.
          inv WRITE0. inv PROMISE. eapply Memory.add_get0 in MEM; eauto. des.
          inv MEM_INJ.
          eapply COMPLETE in H0. des. rewrite H0 in GET. inv GET.
        }
        assert(WRITE': exists mem1', Memory.write (Local.promises lc') mem' loc from to val
                                             (TView.write_released (Local.tview lc') sc' loc to releasedr' ord)
                                             (Local.promises lc') mem1' Memory.op_kind_add).
        {
          exploit MemoryProps.write_succeed_valid.
          {
            inv LOCAL_WF'. eapply PROMISES.
          }
          {
            instantiate (3 := loc). instantiate (2 := from). instantiate (1 := to).
            ii. eapply LOC_COVER in COVER; eauto. ii. inv H1. contradiction H; eauto.
          }
          {
            instantiate (1 := TView.write_released (Local.tview lc') sc' loc to releasedr' ord).
            eapply TLE_write_prs with (inj := inj'); eauto.
            rewrite NEW_INJ'. des_if; eauto. ss; subst; ss. destruct o; ss.
            eapply incr_inj_opt_ViewInj; eauto.
            eapply incr_inj_TViewInj; eauto.
            eapply incr_inj_closed_tviewInj; eauto.
            eapply incr_inj_closed_opt_ViewInj; eauto.
          }
          eauto.
          {
            ii. inv H0. des.
            exploit Memory.get_ts; eauto. ii; des; subst.
            auto_solve_time_rel.
            eapply LOC_COVER with (ts := x); eauto.
            ii. inv H1. contradiction H; eauto.
            econs; eauto. econs; ss; eauto. clear. auto_solve_time_rel.
          }
          {
            instantiate (1 := val).
            inv MSGWF. econs.
            eapply View_opt_wf_inj with (inj := inj'); eauto.
            eapply incr_inj_TViewInj; eauto. 
            eapply incr_inj_opt_ViewInj; eauto. 
            eapply incr_inj_closed_tviewInj; eauto.
            eapply incr_inj_closed_opt_ViewInj; eauto.
            rewrite NEW_INJ'. des_if; eauto. ss; tryfalse. des; tryfalse.
          }
          ii; eauto.
        }
        destruct WRITE' as (mem1' & WRITE').
        do 2 eexists. exists mem1' inj' Memory.op_kind_add.
        split; subst.
        econs; eauto.
        clear - LE_MAX INJ_LOC0 WRITABLE TVIEW_INJ NEW_INJ' INCR_INJ MON_NEWINJ CLOSED_TVIEWINJ.
        inv WRITABLE. econs. 
        eapply writable_inj with (inj := inj'); eauto.
        eapply incr_inj_TViewInj; eauto. eapply incr_inj_closed_tviewInj; eauto.
        rewrite NEW_INJ'. des_if; eauto; ss; des; ss.
        clear - RELEASE LOCAL_WF LOCAL_WF' MEM_INJ PRM_EQ.
        introv ORDER. eapply RELEASE in ORDER.
        inv LOCAL_WF. inv LOCAL_WF'. ss.
        eapply mem_nonsynch_loc_msgInj in ORDER; eauto.
        split; eauto.
        split; eauto.
        split; eauto. 
        split; eauto.
        split. 
        {
          eapply opt_ViewInj_write_released_inj; eauto.
          eapply incr_inj_TViewInj; eauto.
          eapply incr_inj_closed_tviewInj; eauto.
          rewrite NEW_INJ'. des_if; eauto; des; subst; ss.
          eapply incr_inj_opt_ViewInj; eauto.
          eapply incr_inj_closed_opt_ViewInj; eauto.
        }
        
        split; try solve [ii; ss]. 
        {
          introv INJ'. rewrite NEW_INJ' in INJ'.
          des_ifH INJ'; eauto; des; ss; subst. inv INJ'.
          eapply Memory.write_get2 in WRITE0; des; eauto.
          inv MEM_INJ.
          eapply COMPLETE in INJ'; eauto. des.
          inv WRITE0. inv PROMISE.
          erewrite Memory.add_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          inv MEM_INJ.
          eapply COMPLETE in INJ'; eauto. des.
          inv WRITE0. inv PROMISE.
          erewrite Memory.add_o; eauto.
          des_if; ss; des; subst; ss; eauto.
        }
      }
      {
        (* split *)
        clear - H WRITE.
        inv WRITE. inv LC2; ss. inv WRITE0. inv PROMISE; ss. des; subst; ss.
        inv RESERVE.
        exploit Memory.split_get0; eauto. ii; des.
        contradiction H; eauto.
      }
      {
        (* lower *)
        clear - H WRITE.
        inv WRITE. inv LC2; ss. inv WRITE0. inv PROMISE; ss. des; subst; ss.
        exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
        contradiction H; eauto.
      }
      {
        (* cancel *) 
        inv WRITE. inv LC2; ss. inv WRITE0. inv PROMISE. ss.
      }
    }
  }
  {
    lets TEMP: WRITE.
    eapply injection_write_step_id_loc0_GT with (from' := from) (to' := to)
                                                (max_ts := Memory.max_ts loc mem) (sc' := sc') in TEMP; eauto.
    des. subst kind.
    do 4 eexists. exists Memory.op_kind_add.
    split; eauto.
    split; eauto. ss; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    ii; ss.
    {
      ii.
      exploit Memory.max_ts_spec; eauto. ii; des.
      auto_solve_time_rel.
    }
    {
      ii. exploit Memory.get_ts; eauto. ii; des; subst; ss.
      eapply Time.bot_spec.
      destruct(classic (covered loc ts mem)).
      {
        inv H1. inv ITV; ss. 
        exploit Memory.get_ts; eauto. ii; des; subst; ss.
        cut(Time.lt Time.bot Time.bot). ii. clear - H1; auto_solve_time_rel.
        auto_solve_time_rel.
        exploit write_max_add; [eapply WRITE | eauto..]. ii; des. subst kind.
        exploit Memory.max_ts_spec; [eapply GET | eauto..]. ii; des.
        clear - TO H2 MAX.
        cut(Time.le ts (Memory.max_ts loc mem)). ii.
        clear - H2 H. auto_solve_time_rel.
        clear - TO MAX. auto_solve_time_rel.
      }
      {
        eapply LOC_COVER in H1.
        contradiction H1. econs; eauto.
        exploit Memory.get_ts; eauto. ii; des; subst; ss.
        auto_solve_time_rel.
        econs; ss. auto_solve_time_rel.
      }
    }
    {
      inv WRITE. eapply MemoryFacts.MemoryFacts.write_time_lt; eauto.
    }
  }
Qed.

Lemma injection_fecne_step
      inj mem mem' lc1 sc1 ordr ordw lc2 sc2 lc1' sc1'
      (LOCAL_FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (MEM_INJ: MsgInj inj mem mem')
      (TVIEW_INJ: TViewInj inj (Local.tview lc1) (Local.tview lc1'))
      (PRM_EQ: promise_inj inj (Local.promises lc1) (Local.promises lc1'))
      (LOCAL_WF: Local.wf lc1 mem)
      (LOCAL_WF': Local.wf lc1' mem')
      (NOT_SC_FENCE: ordw <> Ordering.seqcst):
  exists lc2' sc2',
    <<INJ_FENCE: Local.fence_step lc1' sc1' ordr ordw lc2' sc2'>> /\
    <<TVIEW_INJ': TViewInj inj (Local.tview lc2) (Local.tview lc2')>> /\
    <<PRM_EQ': promise_inj inj (Local.promises lc2) (Local.promises lc2')>>.
Proof.
  inv LOCAL_FENCE.
  do 2 eexists.
  split.
  {
    econs; eauto. introv ORDER. 
    inv LOCAL_WF. inv LOCAL_WF'.
    eapply mem_nonsynch_msgInj with (promises := Local.promises lc1); eauto.
    ii. eapply PROMISES in H. eapply promise_inj_bot; eauto.
  }
  ss. split; eauto.
  {
    eapply TView_inj_fence_prsv; eauto. 
    eapply read_fence_tview_prsv; eauto.
  }
Qed.

Lemma injection_fecne_sc_step
      inj mem mem' lc1 sc1 ordr lc2 sc2 lc1' sc1'
      (LOCAL_FENCE_SC: Local.fence_step lc1 sc1 ordr Ordering.seqcst lc2 sc2)
      (MEM_INJ: MsgInj inj mem mem')
      (TVIEW_INJ: TViewInj inj (Local.tview lc1) (Local.tview lc1'))
      (PRM_EQ: promise_inj inj (Local.promises lc1) (Local.promises lc1'))
      (LOCAL_WF: Local.wf lc1 mem)
      (LOCAL_WF': Local.wf lc1' mem'):
  exists lc2' sc2',
    <<INJ_FENCE: Local.fence_step lc1' sc1' ordr Ordering.seqcst lc2' sc2'>> /\
    <<BOT: Local.promises lc2' = Memory.bot>>.
Proof.
  inv LOCAL_FENCE_SC.
  exploit PROMISES; eauto. ii.
  do 2 eexists. split.
  econs; eauto.
  introv ORDER. eapply RELEASE in ORDER.
  inv LOCAL_WF; inv LOCAL_WF'.
  eapply mem_nonsynch_msgInj with (promises := Local.promises lc1); eauto.
  ii. eapply promise_inj_bot; eauto.
  ss.
  eapply promise_inj_bot; eauto.
Qed.

Lemma injection_lower_to_none
      inj lc1 mem1 loc from to val' lc2 mem2 val released lc1' mem1'
      (LOCAL_PROMISE: Local.promise_step lc1 mem1 loc from to (Message.concrete val' None) lc2 mem2
                                         (Memory.op_kind_lower (Message.concrete val released)))
      (MEM_INJ: MsgInj inj mem1 mem1')
      (PROM_EQ: promise_inj inj (Local.promises lc1) (Local.promises lc1'))
      (INJ_ID: inj loc to = Some to)
      (LOCAL_WF: Local.wf lc1 mem1)
      (LOCAL_WF': Local.wf lc1' mem1')
      (CLOSED_MEM: Memory.closed mem1):
  exists lc2' mem2' released',
    <<INJ_PROMISE': Local.promise_step lc1' mem1' loc from to (Message.concrete val' None) lc2' mem2'
                                       (Memory.op_kind_lower (Message.concrete val released'))>> /\
    <<MEM_INJ': MsgInj inj mem2 mem2'>> /\
    <<PROM_EQ': promise_inj inj (Local.promises lc2) (Local.promises lc2')>> /\
    <<TVIEW_EQ1: Local.tview lc1 = Local.tview lc2>> /\
    <<TVIEW_EQ2: Local.tview lc1' = Local.tview lc2'>>.
Proof.
  inv LOCAL_PROMISE; ss. inv PROMISE. des; subst; ss.
  inv RESERVE.
  exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
  assert(GET'_LOWER: exists released0', Memory.get loc to (Local.promises lc1') =
                                   Some (from, Message.concrete val0 released0')).
  {
    inv PROM_EQ.
    exploit SOUND; [eapply GET | eauto..]. ii; des.
    rewrite INJ_ID in H. inv H. eauto.
  }
  assert(LT: Time.lt from to).
  {
    exploit MemoryProps.lower_succeed_wf; eauto. ii; des; eauto.
  }
  des.
  assert(exists promises2', Memory.lower (Local.promises lc1') loc from to (Message.concrete val0 released0')
                                    (Message.concrete val' None) promises2').
  {
    eapply Memory.lower_exists; eauto.
    econs; eauto.
    inv MSG_LE.
    econs; eauto.
  }
  des.
  assert(exists mem2', Memory.lower mem1' loc from to (Message.concrete val0 released0')
                               (Message.concrete val' None) mem2').
  {
    eapply Memory.lower_exists_le; eauto.
    inv LOCAL_WF'; eauto.
  }
  des.
  do 3 eexists.
  split.
  {
    econs. econs.
    eapply H. eapply H0.
    inv TS. econs; eauto.
    eauto.
    eauto.
    eauto.
  }
  ss. split.
  {
    lets MEM_INJ': MEM_INJ.
    eapply lower_msgInj_stable_concrete with (inj' := inj) in MEM_INJ'; eauto.
    econs; eauto.
    unfold incr_inj; ii; eauto.
    inv MEM_INJ; eauto.
    ii. inv MEM_INJ.
    eapply COMPLETE in H1; eauto. des.
    eapply Memory.lower_get1 in H1; eauto. des; eauto. inv MSG_LE0. eauto.
  }
  split.
  {
    eapply promise_inj_lower in PROM_EQ; eauto.
  }
  eauto.
Qed.

Lemma injection_cancel
      inj lc1 mem1 loc from to lc2 mem2 msg lc1' mem1'
      (LOCAL_PROMISE: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel)
      (MEM_INJ: MsgInj inj mem1 mem1')
      (PROM_EQ: promise_inj inj (Local.promises lc1) (Local.promises lc1'))
      (LOCAL_WF': Local.wf lc1' mem1'):
  exists lc2' mem2',
    <<INJ_PROMISE': Local.promise_step lc1' mem1' loc from to msg lc2' mem2' Memory.op_kind_cancel>> /\
    <<MEM_INJ': MsgInj inj mem2 mem2'>> /\
    <<PROM_EQ': promise_inj inj (Local.promises lc2) (Local.promises lc2')>> /\
    <<TVIEW_EQ1: Local.tview lc1 = Local.tview lc2>> /\
    <<TVIEW_EQ2: Local.tview lc1' = Local.tview lc2'>>.
Proof.
  inv LOCAL_PROMISE; ss. inv PROMISE.
  exploit Memory.remove_get0; eauto. ii; des.
  assert(GET'_RESERVE: Memory.get loc to (Local.promises lc1') = Some (from, Message.reserve)).
  {
    inv PROM_EQ. eauto.
  }
  exploit Memory.remove_exists; eauto. ii; des.
  exploit Memory.remove_exists_le; [ | eapply H | eauto..]; eauto.
  inv LOCAL_WF'; eauto.
  ii; des.
  do 2 eexists.
  split; ss.
  {
    econs; eauto.
  }
  split; ss.
  {
    eapply cancel_msg_stable; eauto.
  }
  split.
  {
    eapply promise_inj_remove_reseve; eauto.
  }
  eauto.
Qed.

Hint Resolve local_wf_read local_wf_write write_step_closed_mem: local_wf.
  
Inductive spec_view (loc0: Loc.t): TView.t -> TView.t -> Time.t -> Time.t -> Memory.t -> Memory.t -> Prop :=
| spec_view_intro_le_max_ts
    tview tview' max_ts max_ts' mem mem'
    (LE_MAX_TS: Time.le ((View.rlx (TView.acq tview)) loc0) max_ts)
    (GT_MAX_NOCOVER: forall ts, Time.lt max_ts ts -> ~ (Cover.covered loc0 ts mem))
    (GT_MAX_NOCOVER': forall ts', Time.lt max_ts' ts' -> ~ (Cover.covered loc0 ts' mem')):
    spec_view loc0 tview tview' max_ts max_ts' mem mem'
| spec_view_intro_gt_max_ts
    tview tview' max_ts max_ts' mem mem'
    (GT_MAX_TS: Time.lt max_ts ((View.pln (TView.cur tview)) loc0))
    (GT_MAX_TS': Time.lt max_ts' ((View.pln (TView.cur tview')) loc0))
    (MAX_MSG: forall ts, Time.lt ((View.pln (TView.cur tview)) loc0) ts ->
                    ~ (Cover.covered loc0 ts mem))
    (MAX_MSG: forall ts', Time.lt ((View.pln (TView.cur tview')) loc0) ts' ->
                    ~ (Cover.covered loc0 ts' mem')):
    spec_view loc0 tview tview' max_ts max_ts' mem mem'.

Lemma spec_view_read_prsv
      loc0 tview tview' max_ts max_ts' mem mem' inj released released' loc to to' ord from msg
      (MEM_INJ: MsgInj inj mem mem')
      (SPEC_VIEW: spec_view loc0 tview tview' max_ts max_ts' mem mem')
      (TVIEW_WF: TView.wf tview)
      (OPT_VIEWINJ: opt_ViewInj inj released released')
      (CLOSED_OPT_VIEW: Memory.closed_opt_view released mem)
      (GET: Memory.get loc to mem = Some (from, msg))
      (READ: Time.le ((View.pln (TView.cur tview)) loc) to)
      (INJ_MSG: inj loc to = Some to'):
  spec_view loc0 (TView.read_tview tview loc to released ord)
            (TView.read_tview tview' loc to' released' ord) max_ts max_ts' mem mem'.
Proof.
  inv SPEC_VIEW.
  - assert(LE: loc = loc0 -> Time.le to max_ts).
    {
      ii. destruct(Time.le_lt_dec to max_ts); subst; eauto.
      exploit GT_MAX_NOCOVER; eauto; ii; ss.
      exploit Memory.get_ts; eauto. ii.
      des; subst; ss; eauto.
      exploit Time_lt_bot_false; eauto; ii; ss.
      econs; eauto.
      econs; eauto.
      ss. eapply Time.le_lteq; eauto.
    }
    eapply spec_view_intro_le_max_ts; eauto.
    unfold TView.read_tview; ss. des_if.
    {
      unfold View.singleton_ur_if. destruct released; ss.
      {
        viewtac.
        eapply time_le_singleton_prsv; eauto.
        inv CLOSED_OPT_VIEW. inv CLOSED.
        eapply closed_timemap_le_max; eauto.
      }
      {
        viewtac.
        eapply time_le_singleton_prsv; eauto.
      }
    }
    {
      viewtac.
      eapply time_le_singleton_prsv; eauto.
    }
  - eapply spec_view_intro_gt_max_ts; eauto.
    {
      clear - GT_MAX_TS.
      unfold TView.read_tview; eauto; ss. unfold View.singleton_ur_if.
      des_if.
      {
        destruct released; ss.
        {
          des_if.
          {
            unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
          }
          {
            unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
          }
        }
        {
          des_if. 
          unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
          unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
        }
      }
      {
        unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
      }
    }
    {
      clear - GT_MAX_TS'.
      unfold TView.read_tview; eauto; ss. unfold View.singleton_ur_if.
      des_if.
      {
        destruct released'; ss.
        {
          des_if.
          {
            unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
          }
          {
            unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
          }
        }
        {
          des_if. 
          unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
          unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
        }
      }
      {
        unfold TimeMap.join. do 2 (eapply Time.lt_join_l); eauto.
      }
    }
    {
      ii.
      unfold TView.read_tview in H; ss.
      unfold TimeMap.join in H.
      eapply Time_lt_join in H. des.
      eapply Time_lt_join in H. des.
      eapply MAX_MSG; eauto.
    }
    {
      ii.
      unfold TView.read_tview in H; ss.
      unfold TimeMap.join in H.
      eapply Time_lt_join in H. des.
      eapply Time_lt_join in H. des.
      eapply MAX_MSG0; eauto.
    }
Qed.

Lemma spec_view_read_gt_max_ts
      lc1 mem1 loc to1 val1 released1 ord1 lc1' lo
      lc2 mem2 to2 val2 released2 ord2 lc2' max_ts1 max_ts2
      (SPEC_VIEW: spec_view loc (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (LOCAL_READ1: Local.read_step lc1 mem1 loc to1 val1 released1 ord1 lc1' lo)
      (LOCAL_READ2: Local.read_step lc2 mem2 loc to2 val2 released2 ord2 lc2' lo)
      (LT_MAX: Time.lt max_ts1 to1):
  Time.lt max_ts2 to2 /\ Time.le (Memory.max_ts loc mem2) to2 /\ Time.le (Memory.max_ts loc mem1) to1.
Proof.
  inv LOCAL_READ1. inv LOCAL_READ2.
  inv SPEC_VIEW.
  - exploit GT_MAX_NOCOVER; [eapply LT_MAX | eauto..]; ii; ss.
    exploit Memory.get_ts; [eapply GET | eauto..]. ii; des; subst; ss.
    auto_solve_time_rel.
    econs; eauto. econs; ss; eauto. eapply Time.le_lteq; eauto.
  - inv READABLE. inv READABLE0.
    split.
    {
      clear - GT_MAX_TS' PLN0.
      auto_solve_time_rel.
    }
    split.
    {
      exploit Memory.max_ts_spec; [eapply GET0 | eauto..]. ii; des.
      destruct (Time.le_lt_dec (Memory.max_ts loc mem2) to2); eauto. 
      clear - PLN0 l GET1 MAX_MSG0.
      eapply Time.le_lteq in PLN0; des; eauto.
      cut(Time.lt (View.pln (TView.cur (Local.tview lc2)) loc) (Memory.max_ts loc mem2)). ii.
      eapply MAX_MSG0 in H; eauto.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      rewrite H1 in l. clear - l. auto_solve_time_rel.
      contradiction H. econs; ss; eauto. econs; ss.
      eapply Time.le_lteq; eauto.
      auto_solve_time_rel.
      subst.
      exploit MAX_MSG0; eauto; ii; ss.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      rewrite H0 in l. auto_solve_time_rel.
      econs; eauto. econs; ss; eauto.
      eapply Time.le_lteq; eauto.
    }
    {
      exploit Memory.max_ts_spec; [eapply GET | eauto..]. ii; des.
      destruct (Time.le_lt_dec (Memory.max_ts loc mem1) to1); eauto. 
      clear - PLN l GET1 MAX_MSG.
      eapply Time.le_lteq in PLN; des; eauto.
      cut(Time.lt (View.pln (TView.cur (Local.tview lc1)) loc) (Memory.max_ts loc mem1)). ii.
      eapply MAX_MSG in H; eauto.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      rewrite H1 in l. clear - l. auto_solve_time_rel.
      contradiction H. econs; ss; eauto. econs; ss.
      eapply Time.le_lteq; eauto.
      auto_solve_time_rel.
      subst.
      exploit MAX_MSG; eauto; ii; ss.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      rewrite H0 in l. auto_solve_time_rel.
      econs; eauto. econs; ss; eauto.
      eapply Time.le_lteq; eauto.
    }
Qed.

Lemma spec_view_write_prsv_loc_write_le_max
      lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 val2 releasedr2 released2 lc2' sc2' mem2' kind2
      max_ts1 max_ts2
      (LOCAL_WF: Local.wf lc1 mem1)
      (SPEC_VIEW: spec_view loc (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val2 releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (LE1: Time.le to1 max_ts1)
      (LE2: Time.le to2 max_ts2):
  spec_view loc (Local.tview lc1') (Local.tview lc2') max_ts1 max_ts2 mem1' mem2'.
Proof.
  inv SPEC_VIEW.
  - inv WRITE1; ss. inv WRITE2; ss.
    eapply spec_view_intro_le_max_ts.
    {
      clear - LE_MAX_TS LE1.
      unfold TView.write_tview; ss.
      unfold TimeMap.singleton.
      eapply Time.join_spec; eauto.
      rewrite Loc_add_eq; eauto.
    }
    {
      eapply write_le_not_cover_prs; eauto.
    }
    {
      eapply write_le_not_cover_prs; eauto.
    }
  - inv WRITE1. ss. inv WRITABLE.
    clear - LOCAL_WF LE1 GT_MAX_TS TS.
    inv LOCAL_WF. inv TVIEW_WF.
    cut(Time.le (View.pln (TView.cur (Local.tview lc1)) loc) (View.rlx (TView.cur (Local.tview lc1)) loc)).
    ii.
    clear - LE1 GT_MAX_TS TS H.
    cut(Time.lt (View.pln (TView.cur (Local.tview lc1)) loc) to1). ii.
    cut(Time.lt max_ts1 to1). ii.
    clear - LE1 H1. auto_solve_time_rel.
    clear - GT_MAX_TS H0. auto_solve_time_rel.
    clear - H TS. auto_solve_time_rel.
    inv CUR. inv CUR_ACQ. unfold TimeMap.le in PLN_RLX. eauto.
Qed. 

Lemma spec_view_write_prsv_loc_write_gt_max
      lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 val2 releasedr2 released2 lc2' sc2' mem2' kind2
      max_ts1 max_ts2
      (LOCAL_WF: Local.wf lc1 mem1)
      (LOCAL_WF': Local.wf lc2 mem2)
      (SPEC_VIEW: spec_view loc (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val2 releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (LE1: Time.lt max_ts1 to1)
      (LE2: Time.lt max_ts2 to2):
  spec_view loc (Local.tview lc1') (Local.tview lc2') max_ts1 max_ts2 mem1' mem2'.
Proof.
  inv SPEC_VIEW.
  - inv WRITE1; ss. inv WRITE2; ss.
    eapply spec_view_intro_gt_max_ts.
    unfold TView.write_tview; ss.
    {
      unfold TimeMap.join. rewrite Time.join_comm.
      eapply lt_join_l. unfold TimeMap.singleton. rewrite Loc_add_eq. eauto.
    }
    {
      clear - LE2. unfold TView.write_tview; ss.
      unfold TimeMap.join, TimeMap.singleton; ss.
      rewrite Loc_add_eq.
      rewrite Time.join_comm. eapply lt_join_l; eauto.
    }
    {
      ii. unfold TView.write_tview in H; ss.
      unfold TimeMap.join in H. eapply Time_lt_join in H. des.
      unfold TimeMap.singleton in H1. rewrite Loc_add_eq in H1.
      exploit write_gt_not_cover_prs'; [eapply WRITE | eauto..]. ii.
      eapply GT_MAX_NOCOVER with (ts := ts0); eauto.
      clear - LE1 H2. auto_solve_time_rel.
    }
    {
      ii. unfold TView.write_tview in H; ss. unfold TimeMap.join, TimeMap.singleton in H.
      rewrite Loc_add_eq in H.
      eapply Time_lt_join in H. des. clear H.
      exploit write_gt_not_cover_prs'; [eapply WRITE0 | eauto..]. ii.
      eapply GT_MAX_NOCOVER' with (ts' := ts); eauto.
      clear - LE2 H. auto_solve_time_rel.
    }
  - inv WRITE1; ss. inv WRITE2; ss.
    eapply spec_view_intro_gt_max_ts.
    {
      unfold TView.write_tview; ss. unfold TimeMap.join, TimeMap.singleton. rewrite Loc_add_eq.
      eapply lt_join_l; eauto.
    }
    {
      clear - GT_MAX_TS'. unfold TView.write_tview; ss.
      unfold TimeMap.join, TimeMap.singleton. rewrite Loc_add_eq.
      eapply lt_join_l; eauto.
    }
    {
      ii. unfold TView.write_tview in H; ss. unfold TimeMap.join, TimeMap.singleton in H.
      rewrite Loc_add_eq in H. 
      eapply Time_lt_join in H. des.
      exploit write_gt_not_cover_prs'; [eapply WRITE | eauto..]. ii.
      eapply MAX_MSG with (ts := ts0); eauto.
      clear - LOCAL_WF WRITABLE H2. inv WRITABLE.
      inv LOCAL_WF. clear TVIEW_CLOSED PROMISES FINITE BOT.
      inv TVIEW_WF. inv CUR. unfold TimeMap.le in PLN_RLX.
      specialize (PLN_RLX loc).
      cut(Time.lt (View.pln (TView.cur (Local.tview lc1)) loc) to1). ii.
      clear - H2 H. auto_solve_time_rel.
      clear - PLN_RLX TS. auto_solve_time_rel.
    }
    {
      ii. unfold TView.write_tview in H; ss. unfold TimeMap.join, TimeMap.singleton in H.
      rewrite Loc_add_eq in H.
      eapply Time_lt_join in H. des.
      exploit write_gt_not_cover_prs'; [eapply WRITE0 | eauto..]. ii.
      eapply MAX_MSG0 with (ts' := ts); eauto.
      clear - LOCAL_WF' WRITABLE0 H2. inv WRITABLE0.
      inv LOCAL_WF'. clear TVIEW_CLOSED PROMISES FINITE BOT.
      inv TVIEW_WF. inv CUR. unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc).
      clear - H2 TS PLN_RLX.
      cut (Time.lt (View.pln (TView.cur (Local.tview lc2)) loc) to2). ii.
      auto_solve_time_rel.
      auto_solve_time_rel.
    }
Qed.
    
Lemma spec_view_write_le_max_ts
      loc max_ts max_ts1 mem mem1
      lc lc' lc1 sc from to val releasedr released ord sc' mem' kind lo
      ts from0 msg0
      (LOCAL_WF: Local.wf lc mem)
      (SPEC_VIEW: spec_view loc (Local.tview lc) (Local.tview lc1) max_ts max_ts1 mem mem1)
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (LE: Time.le to max_ts)
      (GET: Memory.get loc ts mem = Some (from0, msg0)):
  Time.le ts max_ts.
Proof.
  inv SPEC_VIEW.
  - destruct (Time.le_lt_dec ts max_ts); eauto.
    lets LT: l.
    eapply GT_MAX_NOCOVER in l.
    contradiction l.
    econs; eauto.
    exploit Memory.get_ts; eauto; ii; des; subst.
    auto_solve_time_rel.
    econs; ss; eauto.
    auto_solve_time_rel.
  - inv WRITE. inv WRITABLE.
    inv LOCAL_WF. inv TVIEW_WF. inv CUR.
    cut(Time.lt max_ts to). ii.
    auto_solve_time_rel.
    cut(Time.lt max_ts (View.rlx (TView.cur (Local.tview lc)) loc)). ii.
    clear - H TS. 
    auto_solve_time_rel.
    unfold TimeMap.le in *. specialize (PLN_RLX loc).
    clear - GT_MAX_TS PLN_RLX.
    auto_solve_time_rel.
Qed.

Lemma spec_view_write_gt_max_implies_max_write
      lc lc0 max_ts max_ts0 sc mem loc from to val releasedr released ord
      lc' sc' mem' kind lo ts f msg mem0
      (LOCAL_WF: Local.wf lc mem)
      (SPEC_VIEW: spec_view loc (Local.tview lc) (Local.tview lc0) max_ts max_ts0 mem mem0)
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (LT: Time.lt max_ts to)
      (GET: Memory.get loc ts mem = Some (f, msg)):
  Time.lt ts to.
Proof.
  inv SPEC_VIEW.
  - assert(LE_MAX_TS': Time.le ts max_ts).
    {
      destruct (Time.le_lt_dec ts max_ts); eauto.
      exploit MemoryProps.memory_get_ts_strong; eauto. ii; des; subst.
      auto_solve_time_rel.
      exploit GT_MAX_NOCOVER; eauto; ii; ss.
      clear - GET TS. econs; ss; eauto. econs; ss. auto_solve_time_rel.
    }
    auto_solve_time_rel.
  - assert(Time.lt (View.pln (TView.cur (Local.tview lc)) loc) to).
    {
      inv WRITE. inv WRITABLE.
      clear - LOCAL_WF TS.
      inv LOCAL_WF. inv TVIEW_WF. inv CUR.
      clear - TS PLN_RLX. unfold TimeMap.le in *.
      specialize (PLN_RLX loc).
      auto_solve_time_rel.
    }
    destruct(Time.le_lt_dec to ts); eauto.
    assert(Time.lt (View.pln (TView.cur (Local.tview lc)) loc) to).
    auto_solve_time_rel.
    exploit MemoryProps.memory_get_ts_strong; eauto. ii; des; subst.
    clear - LT l. cut (Time.lt max_ts Time.bot). ii. auto_solve_time_rel.
    auto_solve_time_rel.
    assert(Time.lt (View.pln (TView.cur (Local.tview lc)) loc) ts).
    {
      auto_solve_time_rel.
    }
    exploit MAX_MSG; [eapply H1 | eauto..]; ii; ss.
    econs; eauto.
    econs; ss; eauto.
    clear. auto_solve_time_rel.
Qed.

Lemma spec_view_write_prsv_loc_write_disj
      lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 val2 releasedr2 released2 lc2' sc2' mem2' kind2 max_ts1 max_ts2 loc0
      (SPEC_VIEW: spec_view loc0 (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val2 releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (DISJ_LOC: loc <> loc0):
  spec_view loc0 (Local.tview lc1') (Local.tview lc2') max_ts1 max_ts2 mem1' mem2'.
Proof.
  inv WRITE1. inv WRITE2. ss.
  inv SPEC_VIEW.
  - eapply spec_view_intro_le_max_ts; eauto.
    {
      clear - LE_MAX_TS DISJ_LOC.
      unfold TView.write_tview; ss.
      unfold TimeMap.join, TimeMap.singleton; ss.
      rewrite Loc_add_neq; eauto. ss. unfold LocFun.init.
      eapply Time.join_spec; eauto.
      eapply Time.bot_spec.
    }
    {
      ii. eapply GT_MAX_NOCOVER in H; eauto. contradiction H.
      eapply write_disj_cover_prsv with (mem := mem1) (mem' := mem1'); eauto.
    }
    {
      ii. eapply GT_MAX_NOCOVER' in H; eauto. contradiction H.
      eapply write_disj_cover_prsv with (mem := mem2) (mem' := mem2'); eauto.
    }
  - eapply spec_view_intro_gt_max_ts; eauto.
    {
      clear - GT_MAX_TS DISJ_LOC.
      unfold TView.write_tview; ss.
      unfold TimeMap.join, TimeMap.singleton; ss.
      rewrite Loc_add_neq; eauto. ss. unfold LocFun.init.
      eapply lt_join_l; eauto.
    }
    {
      clear - GT_MAX_TS'.
      eapply lt_join_l; eauto.
    }
    {
      ii. unfold TView.write_tview in H; ss.
      unfold TimeMap.join, TimeMap.singleton in H; ss.
      rewrite Loc_add_neq in H; eauto. unfold LocFun.init in H.
      eapply Time_lt_join in H; des.
      eapply MAX_MSG in H; eauto. contradiction H.
      eapply write_disj_cover_prsv with (mem := mem1) (mem' := mem1'); eauto.
    }
    {
      ii. unfold TView.write_tview in H; ss.
      unfold TimeMap.join, TimeMap.singleton in H; ss.
      rewrite Loc_add_neq in H; eauto. unfold LocFun.init in H.
      eapply Time_lt_join in H; des.
      eapply MAX_MSG0 in H; eauto. contradiction H.
      eapply write_disj_cover_prsv with (mem := mem2) (mem' := mem2'); eauto.
    }
Qed.

Lemma spec_view_fence_step_prsv
      loc max_ts max_ts' mem mem' ordr ordw
      lc1 sc1 lc2 sc2
      lc1' sc1' lc2' sc2'
      (SPEC_VIEW: spec_view loc (Local.tview lc1) (Local.tview lc1') max_ts max_ts' mem mem')
      (FENCE_STEP1: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (FENCE_STEP2: Local.fence_step lc1' sc1' ordr ordw lc2' sc2')
      (NOT_SC_FENCE: ordw <> Ordering.seqcst)
      (LOCAL_WF1: Local.wf lc1 mem)
      (LOCAL_WF2: Local.wf lc1' mem'):
  spec_view loc (Local.tview lc2) (Local.tview lc2') max_ts max_ts' mem mem'.
Proof.
  inv FENCE_STEP1; ss. inv FENCE_STEP2; ss.
  inv SPEC_VIEW.
  - eapply spec_view_intro_le_max_ts; eauto.
    clear - LOCAL_WF1 LE_MAX_TS NOT_SC_FENCE. inv LOCAL_WF1.
    clear TVIEW_CLOSED PROMISES FINITE BOT.
    erewrite write_fence_tview_not_sc; eauto.
  - erewrite write_fence_tview_not_sc; eauto.
    erewrite write_fence_tview_not_sc; eauto.
    eapply spec_view_intro_gt_max_ts; eauto; ss.
    {
      des_if; eauto.
      clear - LOCAL_WF1 GT_MAX_TS. inv LOCAL_WF1. inv TVIEW_WF.
      inv CUR_ACQ. unfold TimeMap.le in PLN.
      specialize (PLN loc).
      clear - GT_MAX_TS PLN.
      auto_solve_time_rel.
    }
    {
      des_if; eauto.
      clear - LOCAL_WF2 GT_MAX_TS'. inv LOCAL_WF2. inv TVIEW_WF.
      inv CUR_ACQ. unfold TimeMap.le in PLN.
      specialize (PLN loc).
      clear - GT_MAX_TS' PLN.
      auto_solve_time_rel.
    }
    {
      des_if; eauto. introv LT.
      eapply MAX_MSG; eauto.
      inv LOCAL_WF1. inv TVIEW_WF.
      inv CUR_ACQ. unfold TimeMap.le in PLN.
      specialize (PLN loc).
      clear - LT PLN. auto_solve_time_rel.
    }
    {
      des_if; eauto. introv LT.
      eapply MAX_MSG0; eauto.
      inv LOCAL_WF2. inv TVIEW_WF.
      inv CUR_ACQ. unfold TimeMap.le in PLN.
      specialize (PLN loc).
      clear - LT PLN. auto_solve_time_rel.
    }
Qed.

Lemma spec_view_lower_none_step_prsv
      loc0 max_ts max_ts'
      lc1 mem1 loc from to val' lc2 mem2 val released
      lc1' mem1' lc2' mem2' released'
      (SPEC_VIEW: spec_view loc0 (Local.tview lc1) (Local.tview lc1') max_ts max_ts' mem1 mem1')
      (LOCAL_PROMISE: Local.promise_step lc1 mem1 loc from to (Message.concrete val' None) lc2 mem2
                                         (Memory.op_kind_lower (Message.concrete val released)))
      (LOCAL_PROMISE': Local.promise_step lc1' mem1' loc from to (Message.concrete val' None) lc2' mem2'
                                          (Memory.op_kind_lower (Message.concrete val released'))):
  spec_view loc0 (Local.tview lc2) (Local.tview lc2') max_ts max_ts' mem2 mem2'.
Proof.
  inv LOCAL_PROMISE. inv PROMISE. des; ss. inv RESERVE.
  inv LOCAL_PROMISE'. inv PROMISE. des; ss. inv RESERVE.
  inv SPEC_VIEW.
  - eapply spec_view_intro_le_max_ts; eauto.
    ii. exploit GT_MAX_NOCOVER; eauto.
    eapply lower_covered with (mem1 := mem1) (mem2 := mem2); eauto.
    ii. exploit GT_MAX_NOCOVER'; eauto.
    eapply lower_covered with (mem1 := mem1') (mem2 := mem2'); eauto.
  - eapply spec_view_intro_gt_max_ts; eauto.
    ii. exploit MAX_MSG; eauto.
    eapply lower_covered with (mem1 := mem1) (mem2 := mem2); eauto.
    ii. exploit MAX_MSG0; eauto.
    eapply lower_covered with (mem1 := mem1') (mem2 := mem2'); eauto.
Qed.

Lemma spec_view_cancel_step_prsv
      loc0 max_ts max_ts'
      lc1 mem1 loc from to msg lc2 mem2
      lc1' mem1' lc2' mem2' 
      (SPEC_VIEW: spec_view loc0 (Local.tview lc1) (Local.tview lc1') max_ts max_ts' mem1 mem1')
      (CANCEL: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel)
      (CANCEL': Local.promise_step lc1' mem1' loc from to msg lc2' mem2' Memory.op_kind_cancel):
  spec_view loc0 (Local.tview lc2) (Local.tview lc2') max_ts max_ts' mem2 mem2'.
Proof.
  inv CANCEL; ss. inv PROMISE.
  inv CANCEL'; ss. inv PROMISE.
  inv SPEC_VIEW.
  - econs; eauto. ii.
    eapply GT_MAX_NOCOVER; eauto.
    eapply remove_covered with (mem2 := mem2) in H0; eauto. des; eauto.
    ii. eapply GT_MAX_NOCOVER'; eauto.
    eapply remove_covered with (mem2 := mem2') in H0; eauto. des; eauto.
  - eapply spec_view_intro_gt_max_ts; eauto.
    ii.
    eapply MAX_MSG; eauto.
    eapply remove_covered with (mem2 := mem2) in H0; eauto. des; eauto.
    ii.
    eapply MAX_MSG0; eauto.
    eapply remove_covered with (mem2 := mem2') in H0; eauto. des; eauto.
Qed.
  
Lemma additional_msg_consistent_construction:
  forall n lang loc0 (inj: Mapping) (max_ts max_ts': Time.t)
    st lc sc mem lc' sc' mem' st0 lc0 sc0 mem0 lo
    (WF_LOCAL: Local.wf lc mem)
    (WF_LOCAL': Local.wf lc' mem')
    (CLOSED_MEM: Memory.closed mem)
    (CLOSED_MEM': Memory.closed mem')
    (OTHER_ID: forall loc t t', loc <> loc0 -> inj loc t = Some t' -> t = t')
    (LOC0_INJ: forall t t', Time.le t max_ts -> inj loc0 t = Some t' -> t = t')
    (MAX_TS: Time.le max_ts max_ts')
    (MEM_INJ: MsgInj inj mem mem')
    (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
    (PRM_EQ: promise_inj inj (Local.promises lc) (Local.promises lc'))
    (OTHER_NOTCOVER: forall loc ts,
        loc <> loc0 -> ~ (Cover.covered loc ts mem) -> ~ (Cover.covered loc ts mem'))
    (LOC0_NOTCOVER1: forall ts,
        ~ (Cover.covered loc0 ts mem) -> Time.le ts max_ts -> ~ (Cover.covered loc0 ts mem'))
    (SPEC_VIEW: spec_view loc0 (Local.tview lc) (Local.tview lc') max_ts max_ts' mem mem')
    (MAX_RESERVE: exists from, Memory.get loc0 max_ts mem = Some (from, Message.reserve))
    (PRM_LESS: forall to from msg,
        Memory.get loc0 to (Local.promises lc) = Some (from, msg) -> Time.lt to max_ts)
    (STEPS: rtcn (Thread.nprm_step lo) n (Thread.mk lang st lc sc mem)
                 (Thread.mk lang st0 lc0 sc0 mem0))
    (FULFILL: Local.promises lc0 = Memory.bot),
  exists st0' lc0' sc0' mem0',
    rtc (Thread.nprm_step lo) (Thread.mk lang st lc' sc' mem') (Thread.mk lang st0' lc0' sc0' mem0') /\
    Local.promises lc0' = Memory.bot.
Proof.
  induction n; ii.
  - inv STEPS. do 4 eexists. split; eauto. eapply promise_inj_bot; eauto.
  - inv STEPS.
    inv A12.
    inv PROG.
    inv LOCAL.
    + (* silent *)
      eapply IHn in A23; eauto.
      des.
      do 4 eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs; eauto. ss. eauto. eauto.
    + (* read *)
      lets INJ_READ: LOCAL0. 
      eapply injection_read_step in INJ_READ; eauto.
      destruct INJ_READ as (lc1' & released' & to' & INJ_READ & INJ_MSG & INJ_VIEW).
      assert(PROM_EQ: Local.promises lc = Local.promises lc2).
      {
        clear - LOCAL0. inv LOCAL0. destruct lc; ss.
      }
      assert(PROM_EQ': Local.promises lc' = Local.promises lc1').
      { 
        clear - INJ_READ. inv INJ_READ. destruct lc'; ss. 
      } 
      eapply IHn with (lc' := lc1') in A23; eauto with local_wf. 
      destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS' & FULFILL').
      do 4 eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. instantiate (2 := ThreadEvent.read loc to' val released' ord). ss. eauto.
      econs; eauto. ss; eauto. eauto. eauto.
      {
        (* TViewInj preserve *)
        inv LOCAL0. inv INJ_READ. ss.
        eapply TView_inj_read_prsv; eauto.
        inv MEM_INJ; eauto.
        eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
        inv WF_LOCAL; eauto.
        eapply wf_msginj_implies_closed_view in GET; eauto.
        unfold closed_opt_viewinj.
        des; subst; ss.
      }
      {
        (* Local promises eq *)
        rewrite <- PROM_EQ; rewrite <- PROM_EQ'; eauto.
      }
      {
        (* spec view *)
        inv LOCAL0; ss.
        inv INJ_READ; ss.
        eapply spec_view_read_prsv; eauto.
        inv WF_LOCAL; eauto.
        eapply closed_mem_implies_closed_msg; eauto.
        inv READABLE; eauto.
      }
      {
        (* promise less max *)
        rewrite <- PROM_EQ; eauto.
      }
    + (* write *)
      destruct (Loc.eq_dec loc loc0); subst.
      {
        (* same location *)
        destruct(Time.le_lt_dec to max_ts) as [LE_WRITE | GT_WRITE].
        {
          assert(LT_MAX: Time.lt to max_ts).
          {
            eapply Local_write_lt_max_ts_reserve; eauto.
          }
          exploit injection_write_step_id_loc0; eauto.
          ii. eapply spec_view_write_le_max_ts; [eapply WF_LOCAL | eapply SPEC_VIEW | eauto..].
          des; eauto.
          instantiate (1 := None). econs.
          instantiate (1 := sc).
          introv WRITE'. des. 
          assert(Promise_inj: promise_inj inj' (Local.promises lc2) (Local.promises lc1')).
          {
            exploit write_step_promise_inj_stable; [eapply LOCAL0 | eapply INJ_WRITE | eapply PRM_EQ | eauto..].
            rewrite INJ_MSG.
            des_if; ss; des; subst; ss; eauto. introv SPLIT_INJ'.
            exploit SPLIT_INJ'; eauto. ii; subst.
            exploit SPLIT_INJ; eauto. ii; des. do 3 eexists. split; eauto.
          }
          assert(MEM_INJ': MsgInj inj' mem2 mem1').
          {
            eapply write_step_msgInj_stable; eauto.
            rewrite INJ_MSG. des_if; des; ss; subst; ss.
            introv INJ'. eapply INJ_COMPLETE in INJ'. des.
            do 3 eexists. eauto.
          } 
          eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                          (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
          {
            (* fulfill *) 
            destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
            exists st0'. do 3 eexists. split; eauto.
            eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
            econs. econs. 
            instantiate (1 := ThreadEvent.write loc0 from to val releasedw' ord).
            ss; eauto.
            econs. instantiate (1 := kind'). inv INJ_WRITE; subst. econs; eauto.
            ss. inv WRITABLE. econs; eauto.
            ss; eauto.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem; eauto.
          }
          ii. rewrite INJ_MSG in H0. des_ifH H0; des; ss; subst; ss; eauto.
          ii. rewrite INJ_MSG in H0. des_ifH H0; des; ss; subst; ss; eauto. inv H0; eauto.
          {
            (* TViewInj *)
            inv LOCAL0; ss. inv INJ_WRITE; ss.
            eapply TView_inj_write_prsv; eauto.
            eapply incr_inj_TViewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL; eauto.
            eapply incr_inj_closed_tviewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL; eauto.
            des_if; ss; des; ss; eauto.
          }
          {
            (* OTHER NOT COVER *)
            ii. contradiction H0. eapply write_disj_cover_prsv with (mem := mem') in H1; eauto.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
            eapply OTHER_NOTCOVER in H; eauto. contradiction H; eauto.
            ii. contradiction H0.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
          }
          {
            (* LOC0 NOT Cover *)
            eapply write_not_cover_prsv; eauto.
          }
          {
            (* Spec view *)
            eapply spec_view_write_prsv_loc_write_le_max with (lc1 := lc) (lc2 := lc'); eauto.
            clear - LE_WRITE MAX_TS. auto_solve_time_rel.
          }
          {
            (* Reserve *)
            des. exploit write_step_reserve_prsv; [eapply LOCAL0 | eauto..].
          }
          {
            (* promise less *) 
            ii. eapply write_step_promise_lt_prsv; [eapply LOCAL0 | eauto..].
          }
        }
        {
          assert(WRITE_MAX: forall ts from0 msg, Memory.get loc0 ts mem = Some (from0, msg) -> Time.lt ts to).
          {
            ii.
            eapply spec_view_write_gt_max_implies_max_write; [eapply WF_LOCAL | eapply SPEC_VIEW | eauto..].
          }
          exploit injection_write_step_id_loc0_GT; [eapply LOCAL0 | eauto..].
          instantiate (1 := None). ss.
          instantiate (1 := Time.join max_ts' (Memory.max_ts loc0 mem')).
          ii. exploit Memory.max_ts_spec; eauto. ii; des; eauto.
          cut(Time.le (Memory.max_ts loc0 mem') (Time.join max_ts' (Memory.max_ts loc0 mem'))). ii.
          auto_solve_time_rel.
          eapply Time.join_r.
          instantiate (1 := Time.incr (Time.join max_ts' (Memory.max_ts loc0 mem'))). ii.
          exploit H. auto_solve_time_rel. clear H.
          instantiate (1 := sc'). ii. des. subst kind.
          assert(Promise_inj: promise_inj inj' (Local.promises lc2) (Local.promises lc1')).
          {
            exploit write_step_promise_inj_stable; [eapply LOCAL0 | eapply INJ_WRITE | eapply PRM_EQ | eauto..].
            rewrite INJ_MSG.
            des_if; ss; des; subst; ss; eauto. ss.
            introv SPLIT_INJ'.
            exploit SPLIT_INJ'; eauto. ii; subst; ss.
          }
          assert(MEM_INJ': MsgInj inj' mem2 mem1').
          {
            eapply write_step_msgInj_stable; eauto. ss.
            rewrite INJ_MSG. des_if; des; ss; subst; ss.
            introv INJ'. eapply INJ_COMPLETE in INJ'. des.
            do 3 eexists. eauto.
          }
          eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                          (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
          {
            (* fulfill *)
            destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
            exists st0'. do 3 eexists. split; eauto.
            eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
            econs. econs. 
            instantiate
              (1 := ThreadEvent.write loc0 (Time.join max_ts' (Memory.max_ts loc0 mem'))
                                      (Time.incr (Time.join max_ts' (Memory.max_ts loc0 mem'))) val releasedw' ord).
            ss; eauto.
            econs. instantiate (1 := Memory.op_kind_add). inv INJ_WRITE; subst. econs; eauto.
            ss. 
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem; eauto.
          }
          ii. rewrite INJ_MSG in H0. des_ifH H0; des; ss; subst; ss; eauto.
          ii. rewrite INJ_MSG in H0. des_ifH H0; des; ss; subst; ss; eauto. inv H0; eauto. auto_solve_time_rel.
          {
            (* TViewInj *)
            inv LOCAL0; ss. inv INJ_WRITE; ss.
            eapply TView_inj_write_prsv; eauto.
            eapply incr_inj_TViewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL; eauto.
            eapply incr_inj_closed_tviewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL; eauto.
            des_if; ss; des; ss; eauto.
          }
          {
            (* OTHER NOT COVER *)
            ii. contradiction H0. eapply write_disj_cover_prsv with (mem := mem') in H1; eauto.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
            eapply OTHER_NOTCOVER in H; eauto. contradiction H; eauto.
            ii. contradiction H0.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
          }
          {
            (* LOC0 NOT Cover *) 
            eapply write_not_cover_prsv_write_max; eauto.
            cut(Time.le max_ts' (Time.join max_ts' (Memory.max_ts loc0 mem'))). ii.
            auto_solve_time_rel. eapply Time.join_l. ss.
          }
          {
            (* Spec view *)
            eapply spec_view_write_prsv_loc_write_gt_max with (lc1 := lc) (lc2 := lc'); eauto.
            cut(Time.le max_ts' (Time.join max_ts' (Memory.max_ts loc0 mem'))). ii.
            cut(Time.lt (Time.join max_ts' (Memory.max_ts loc0 mem'))
                        (Time.incr (Time.join max_ts' (Memory.max_ts loc0 mem')))). ii.
            auto_solve_time_rel. auto_solve_time_rel.
            eapply Time.join_l.
          }
          {
            (* Reserve *)
            des. exploit write_step_reserve_prsv; [eapply LOCAL0 | eauto..].
          }
          {
            (* promise less *) 
            ii. eapply write_step_promise_lt_prsv; [eapply LOCAL0 | eauto..].
          }
        }
      }
      {
        (* not same location *) 
        exploit injection_write_step_id;
        [eapply LOCAL0 | | eapply MEM_INJ | eapply WF_LOCAL | eapply WF_LOCAL' | eauto..].
        {
          clear - OTHER_NOTCOVER n0. ii. eapply OTHER_NOTCOVER; eauto.
        }
        {
          instantiate (1 := None). econs.
        }
        instantiate (1 := sc'). ii. des.
        assert(Promise_inj: promise_inj inj' (Local.promises lc2) (Local.promises lc1')).
        {
          exploit write_step_promise_inj_stable; [eapply LOCAL0 | eapply INJ_WRITE | eapply PRM_EQ | eauto..].
          rewrite INJ_MSG.
          des_if; ss; des; subst; ss; eauto. introv SPLIT_INJ'.
          exploit SPLIT_INJ'; eauto. ii; subst.
          exploit SPLIT_INJ; eauto. ii; des. do 3 eexists. split; eauto.
        }
        assert(MEM_INJ': MsgInj inj' mem2 mem1').
        {
          eapply write_step_msgInj_stable; eauto.
          rewrite INJ_MSG. des_if; des; ss; subst; ss.
          introv INJ'. eapply INJ_COMPLETE in INJ'. des.
          do 3 eexists. eauto.
        } 
        eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                        (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
        {
          (* Fulfill *)
          destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
          exists st0'. do 3 eexists. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
          econs. econs.
          instantiate (1 := ThreadEvent.write loc from to val releasedw' ord). ss; eauto.
          econs; eauto. ss; eauto.
        }
        {
          (* Local wf *)
          eapply local_wf_write; eauto.
        }
        {
          (* Local wf *)
          eapply local_wf_write; eauto.
        }
        {
          (* Memory closed *)
          eapply write_step_closed_mem; eauto.
        }
        {
          (* Memory closed *)
          eapply write_step_closed_mem; eauto.
        }
        {
          (* Other Inj *)
          introv OTHER_LOC INJ'.
          rewrite INJ_MSG in INJ'. des_ifH INJ'; ss; des; subst. inv INJ'; eauto.
          eauto. eauto.
        }
        {
          (* LOC Inj *)
          introv MAX_LE INJ'. rewrite INJ_MSG in INJ'.
          des_ifH INJ'; ss; des; subst; ss; eauto.
        }
        {
          (* TViewInj *)
          inv LOCAL0; ss. inv INJ_WRITE; ss.
          eapply TView_inj_write_prsv; eauto.
          eapply incr_inj_TViewInj; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL; eauto.
          eapply incr_inj_closed_tviewInj; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL; eauto.
          des_if; ss; des; ss; eauto.
        }
        {
          (* Other Cover *)
          introv OTHER_LOC.
          destruct(Loc.eq_dec loc1 loc); subst.  
          eapply write_not_cover_prsv_write; [| eapply LOCAL0 | eapply INJ_WRITE | eauto..]; eauto.
          ii.
          eapply OTHER_NOTCOVER with (ts := ts) in OTHER_LOC; eauto. 
          contradiction OTHER_LOC; eauto.
          eapply write_disj_cover_prsv with (mem := mem') (mem' := mem1') in H0; eauto.
          ii. contradiction H.
          eapply write_disj_cover_prsv with (mem := mem) (mem' := mem2); eauto.
        }
        {
          (* LOC0 Cover *)
          ii. contradiction H.
          eapply LOC0_NOTCOVER1 in H0; eauto.
          contradiction H0.
          eapply write_disj_cover_prsv with (mem := mem') (mem' := mem1'); eauto.
          ii. contradiction H.
          eapply write_disj_cover_prsv with (mem := mem) (mem' := mem2); eauto.
        }
        {
          (* spec view *)
          eapply spec_view_write_prsv_loc_write_disj; eauto.
        }
        {
          (* Reserve *)
          des. exploit write_step_reserve_prsv; [eapply LOCAL0 | eapply MAX_RESERVE | eauto..].
        }
        {
          (* promise less *) 
          ii. eapply write_step_promise_lt_prsv; [eapply LOCAL0 | eauto..].
        }
      }
    + (* update *)
      assert(WRITE_ITV: Time.lt tsr tsw).
      {
        destruct lc3, lc2.
        exploit MemoryProps.write_msg_wf; eauto. ii; des; eauto.
      }
      destruct(Loc.eq_dec loc loc0); subst.
      {
        (* same location *)
        destruct(Time.le_lt_dec tsw max_ts) as [LE_WRITE | GT_WRITE].
        {
          assert(LT_MAX: Time.lt tsw max_ts).
          {
            eapply Local_write_lt_max_ts_reserve; eauto.
          }
          (* construct read *)
          lets INJ_READ: LOCAL1. 
          eapply injection_read_step in INJ_READ; eauto.
          destruct INJ_READ as (lc3' & releasedr' & tsr' & INJ_READ & INJ_MSG & INJ_VIEW).
          assert(PROM_EQ: Local.promises lc = Local.promises lc3).
          {
            clear - LOCAL1. inv LOCAL1. destruct lc; ss.
          }
          assert(PROM_EQ': Local.promises lc' = Local.promises lc3').
          { 
            clear - INJ_READ. inv INJ_READ. destruct lc'; ss. 
          }
          assert(SPEC_VIEW': spec_view loc0 (Local.tview lc3) (Local.tview lc3') max_ts max_ts' mem mem').
          {
            destruct lc, lc3. inv LOCAL1. inv LC2; ss.
            destruct lc', lc3'. inv INJ_READ. inv LC2; ss.
            eapply spec_view_read_prsv; eauto.
            inv WF_LOCAL; eauto.
            eapply closed_mem_implies_closed_msg; eauto.
            inv READABLE; eauto.
          }
          assert(WF_LOCAL3: Local.wf lc3 mem).
          {
            eapply local_wf_read; eauto.
          }
          assert(WF_LOCAL3': Local.wf lc3' mem').
          {
            eapply local_wf_read; eauto.
          }
          assert(READ_SAME_MSG: tsr = tsr').
          { 
            clear - MEM_INJ LOC0_INJ WRITE_ITV LE_WRITE LOCAL1 INJ_MSG.
            inv LOCAL1. inv MEM_INJ.
            exploit SOUND; eauto. ii; des.
            rewrite INJ_MSG in H; inv H.
            eapply LOC0_INJ in INJ_MSG; eauto.
            clear - WRITE_ITV LE_WRITE.
            eapply Time.le_lteq. left. auto_solve_time_rel.
          }
          subst tsr'.
          assert(TVIEW_INJ_READ: TViewInj inj (Local.tview lc3) (Local.tview lc3')).
          {
            inv LOCAL1. inv INJ_READ. ss.
            eapply TView_inj_read_prsv; eauto.
            inv MEM_INJ; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv WF_LOCAL; eauto.
            eapply wf_msginj_implies_closed_view in GET; eauto.
            unfold closed_opt_viewinj.
            des; subst; ss.
          }
          assert(CLOSED_READ: Memory.closed_opt_view releasedr mem).
          {
            inv LOCAL1; ss.
            eapply closed_mem_implies_closed_msg; eauto.
          }
          assert(Promise_inj0: promise_inj inj (Local.promises lc3) (Local.promises lc3')).
          {
            rewrite <- PROM_EQ. rewrite <- PROM_EQ'. eauto.
          }
          (* construct write *) 
          exploit injection_write_step_id_loc0; eauto; try solve [des; eauto]. 
          ii. eapply spec_view_write_le_max_ts; [eapply WF_LOCAL3 | eapply SPEC_VIEW' | eauto..].
          instantiate (1 := sc').
          ii; des.
          assert(Promise_inj: promise_inj inj' (Local.promises lc2) (Local.promises lc1')).
          {
            exploit write_step_promise_inj_stable; [eapply LOCAL2 | eapply INJ_WRITE | eauto..].
            rewrite INJ_MSG0.
            des_if; ss; des; subst; ss; eauto. introv SPLIT_INJ'.
            exploit SPLIT_INJ'; eauto. ii; subst.
            exploit SPLIT_INJ; eauto. ii; des. do 3 eexists. split; eauto.
          }
          assert(MEM_INJ': MsgInj inj' mem2 mem1').
          {
            eapply write_step_msgInj_stable; eauto.
            rewrite INJ_MSG0. des_if; des; ss; subst; ss.
            introv INJ'. eapply INJ_COMPLETE in INJ'. des.
            do 3 eexists. eauto.
          }
          eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                          (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
          {
            (* fulfill *)
            destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
            exists st0'. do 3 eexists. split; eauto.
            eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
            econs. econs.
            instantiate (1 := ThreadEvent.update loc0 tsr tsw valr valw releasedr' releasedw' ordr ordw).
            ss; eauto.
            econs; eauto.
            ss; eauto.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem with (releasedr := releasedr); eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem with (releasedr := releasedr'); eauto.
            inv INJ_READ; ss. eapply closed_mem_implies_closed_msg; eauto.
          }
          ii. rewrite INJ_MSG0 in H0. des_ifH H0; des; ss; subst; ss; eauto.
          ii. rewrite INJ_MSG0 in H0. des_ifH H0; des; ss; subst; ss; eauto. inv H0; eauto.
          {
            (* TViewInj *)
            inv LOCAL2; ss. inv INJ_WRITE; ss.
            eapply TView_inj_write_prsv; eauto.
            eapply incr_inj_TViewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL3; eauto.
            eapply incr_inj_closed_tviewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL3; eauto.
            des_if; ss; des; ss; eauto.
          }
          {
            (* OTHER NOT COVER *)
            ii. contradiction H0. eapply write_disj_cover_prsv with (mem := mem') in H1; eauto.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
            eapply OTHER_NOTCOVER in H; eauto. contradiction H; eauto.
            ii. contradiction H0.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
          }
          {
            (* LOC0 NOT Cover *)
            eapply write_not_cover_prsv; eauto.
          }
          {
            (* Spec view *)
            eapply spec_view_write_prsv_loc_write_le_max with (lc1 := lc3) (lc2 := lc3'); eauto.
            clear - LE_WRITE MAX_TS. auto_solve_time_rel.
          }
          {
            (* Reserve *)
            des. exploit write_step_reserve_prsv; [eapply LOCAL2 | eauto..].
          }
          {
            (* promise less *)
            ii. eapply write_step_promise_lt_prsv; [eapply LOCAL2 | eauto..].
            ii. rewrite <- PROM_EQ in H0; eauto.
          }
        }
        {
          assert(READ_GT: Time.lt max_ts tsr).
          {
            destruct(Time.le_lt_dec tsr max_ts) as [TSR_LE_MAX | TSR_GT_MAX]; eauto.
            eapply Time.le_lteq in TSR_LE_MAX. des.
            exploit write_step_itv_msg_false; [eapply LOCAL2 | eapply TSR_LE_MAX | eapply GT_WRITE | eauto..].
            ii; ss.
            subst.
            inv LOCAL1. des. rewrite MAX_RESERVE in GET; ss.
          }
          (* construct read *) 
          lets INJ_READ: LOCAL1. 
          eapply injection_read_step in INJ_READ; eauto.
          destruct INJ_READ as (lc3' & releasedr' & tsr' & INJ_READ & INJ_MSG & INJ_VIEW).
          assert(PROM_EQ: Local.promises lc = Local.promises lc3).
          {
            clear - LOCAL1. inv LOCAL1. destruct lc; ss.
          }
          assert(PROM_EQ': Local.promises lc' = Local.promises lc3').
          { 
            clear - INJ_READ. inv INJ_READ. destruct lc'; ss. 
          }
          assert(SPEC_VIEW': spec_view loc0 (Local.tview lc3) (Local.tview lc3') max_ts max_ts' mem mem').
          {
            destruct lc, lc3. inv LOCAL1. inv LC2; ss.
            destruct lc', lc3'. inv INJ_READ. inv LC2; ss.
            eapply spec_view_read_prsv; eauto.
            inv WF_LOCAL; eauto.
            eapply closed_mem_implies_closed_msg; eauto.
            inv READABLE; eauto.
          }
          assert(WF_LOCAL3: Local.wf lc3 mem).
          {
            eapply local_wf_read; eauto.
          }
          assert(WF_LOCAL3': Local.wf lc3' mem').
          {
            eapply local_wf_read; eauto.
          } 
          assert(LT_MAX_TS': Time.lt max_ts' tsr' /\ Time.le (Memory.max_ts loc0 mem') tsr'
                /\ Time.le (Memory.max_ts loc0 mem) tsr).
          {
            eapply spec_view_read_gt_max_ts; [eapply SPEC_VIEW | eauto..].
          }
          destruct LT_MAX_TS' as (LT_MAX_TS' & GT_MAX_TS_READ' & GT_MAX_TS_READ).
          assert(TVIEW_INJ_READ: TViewInj inj (Local.tview lc3) (Local.tview lc3')).
          {
            inv LOCAL1. inv INJ_READ. ss.
            eapply TView_inj_read_prsv; eauto.
            inv MEM_INJ; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv WF_LOCAL; eauto.
            eapply wf_msginj_implies_closed_view in GET; eauto.
            unfold closed_opt_viewinj.
            des; subst; ss.
          }
          assert(CLOSED_READ: Memory.closed_opt_view releasedr mem).
          {
            inv LOCAL1; ss.
            eapply closed_mem_implies_closed_msg; eauto.
          }
          assert(CLOSED_READ': Memory.closed_opt_view releasedr' mem').
          {
            inv INJ_READ; ss.
            eapply closed_mem_implies_closed_msg; eauto.
          }
          assert(Promise_inj0: promise_inj inj (Local.promises lc3) (Local.promises lc3')).
          {
            rewrite <- PROM_EQ. rewrite <- PROM_EQ'. eauto.
          }
          (* construct write *)
          exploit injection_write_step_id_loc0_GT; [eapply LOCAL2 | eauto..].
          {
            ii. exploit Memory.max_ts_spec; eauto. ii; des.
            clear - GT_MAX_TS_READ WRITE_ITV MAX.
            cut(Time.le ts tsr). ii. clear GT_MAX_TS_READ MAX. auto_solve_time_rel.
            clear WRITE_ITV. auto_solve_time_rel.
          }
          {
            ii. instantiate (1 := tsr').
            exploit Memory.max_ts_spec; [eapply H | eauto..]. ii; des.
            clear - MAX GT_MAX_TS_READ'.
            auto_solve_time_rel.
          }
          instantiate (1 := Time.incr tsr'). instantiate (1 := sc').
          introv TEMP. exploit TEMP. clear. auto_solve_time_rel.
          clear TEMP. ii; des. subst kind.
          assert(Promise_inj: promise_inj inj' (Local.promises lc2) (Local.promises lc1')).
          {
            exploit write_step_promise_inj_stable; [eapply LOCAL2 | eapply INJ_WRITE | eapply Promise_inj0 | eauto..].
            rewrite INJ_MSG0.
            des_if; ss; des; subst; ss; eauto. ss.
            introv SPLIT_INJ'.
            exploit SPLIT_INJ'; eauto. ii; subst; ss.
          }
          assert(MEM_INJ': MsgInj inj' mem2 mem1').
          {
            eapply write_step_msgInj_stable; eauto. ss.
            rewrite INJ_MSG0. des_if; des; ss; subst; ss.
            introv INJ'. eapply INJ_COMPLETE in INJ'. des.
            do 3 eexists. eauto.
          }
          eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                          (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
          {
            (* fulfill *)
            destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
            exists st0'. do 3 eexists. split; eauto.
            eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
            econs. econs. 
            instantiate (1 := ThreadEvent.update loc0 tsr' (Time.incr tsr') valr valw releasedr' releasedw' ordr ordw).
            ss; eauto.
            econs; eauto. ss.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem; [ | eapply LOCAL2 | eauto..]; eauto.
          }
          {
            (* Memory closed *)
            eapply write_step_closed_mem; [ | eapply INJ_WRITE | eauto..]; eauto.
          }
          ii. rewrite INJ_MSG0 in H0. des_ifH H0; des; ss; subst; ss; eauto.
          ii. rewrite INJ_MSG0 in H0. des_ifH H0; des; ss; subst; ss; eauto. inv H0; eauto. auto_solve_time_rel.
          {
            (* TViewInj *)
            inv LOCAL2; ss. inv INJ_WRITE; ss.
            eapply TView_inj_write_prsv; eauto.
            eapply incr_inj_TViewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL3; eauto.
            eapply incr_inj_closed_tviewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL3; eauto.
            des_if; ss; des; ss; eauto.
          }
          {
            (* OTHER NOT COVER *)
            ii. contradiction H0. eapply write_disj_cover_prsv with (mem := mem') in H1; eauto.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
            eapply OTHER_NOTCOVER in H; eauto. contradiction H; eauto.
            ii. contradiction H0.
            eapply write_disj_cover_prsv with (mem := mem); eauto.
          }
          {
            (* LOC0 NOT Cover *) 
            eapply write_not_cover_prsv_write_max; eauto.
            clear - MAX_TS LT_MAX_TS'.
            eapply Time.le_lteq. left. auto_solve_time_rel.
            ss.
          }
          {
            (* Spec view *)
            eapply spec_view_write_prsv_loc_write_gt_max with (lc1 := lc3) (lc2 := lc3'); eauto.
            clear - LT_MAX_TS'.
            cut(Time.lt tsr' (Time.incr tsr')). ii.
            auto_solve_time_rel.
            auto_solve_time_rel.
          }
          {
            (* Reserve *)
            des. exploit write_step_reserve_prsv; [eapply LOCAL2 | eauto..].
          }
          {
            (* promise less *) 
            ii. eapply write_step_promise_lt_prsv; [eapply LOCAL2 | eauto..].
            introv GET_PROM. rewrite <- PROM_EQ in GET_PROM; eauto.
          }
        }
      }
      {
        (* not same location *)
        (* construct read *) 
        lets INJ_READ: LOCAL1. 
        eapply injection_read_step in INJ_READ; eauto.
        destruct INJ_READ as (lc3' & releasedr' & tsr' & INJ_READ & INJ_MSG & INJ_VIEW).
        assert(PROM_EQ: Local.promises lc = Local.promises lc3).
        {
          clear - LOCAL1. inv LOCAL1. destruct lc; ss.
        }
        assert(PROM_EQ': Local.promises lc' = Local.promises lc3').
        { 
          clear - INJ_READ. inv INJ_READ. destruct lc'; ss. 
        }
        assert(SPEC_VIEW': spec_view loc0 (Local.tview lc3) (Local.tview lc3') max_ts max_ts' mem mem').
        {
          destruct lc, lc3. inv LOCAL1. inv LC2; ss.
          destruct lc', lc3'. inv INJ_READ. inv LC2; ss.
          eapply spec_view_read_prsv; eauto.
          inv WF_LOCAL; eauto.
          eapply closed_mem_implies_closed_msg; eauto.
          inv READABLE; eauto.
        }
        assert(WF_LOCAL3: Local.wf lc3 mem).
        {
          eapply local_wf_read; eauto.
        }
        assert(WF_LOCAL3': Local.wf lc3' mem').
        {
          eapply local_wf_read; eauto.
        } 
        assert(TVIEW_INJ_READ: TViewInj inj (Local.tview lc3) (Local.tview lc3')).
        {
          inv LOCAL1. inv INJ_READ. ss.
          eapply TView_inj_read_prsv; eauto.
          inv MEM_INJ; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv WF_LOCAL; eauto.
          eapply wf_msginj_implies_closed_view in GET; eauto.
          unfold closed_opt_viewinj.
          des; subst; ss.
        }
        assert(CLOSED_READ: Memory.closed_opt_view releasedr mem).
        {
          inv LOCAL1; ss.
          eapply closed_mem_implies_closed_msg; eauto.
        }
        assert(CLOSED_READ': Memory.closed_opt_view releasedr' mem').
        {
          inv INJ_READ; ss.
          eapply closed_mem_implies_closed_msg; eauto.
        }
        assert(Promise_inj0: promise_inj inj (Local.promises lc3) (Local.promises lc3')).
        {
          rewrite <- PROM_EQ. rewrite <- PROM_EQ'. eauto.
        }
        assert(tsr = tsr').
        {
          exploit OTHER_ID; eauto.
        }
        subst tsr'.
        (* construct write *)
        exploit injection_write_step_id;
        [eapply LOCAL2 | | eapply MEM_INJ | eapply WF_LOCAL3 | eapply WF_LOCAL3' | eauto..].
        {
          clear - OTHER_NOTCOVER n0. ii. eapply OTHER_NOTCOVER; eauto.
        }
        instantiate (1 := sc'). ii. des.
        assert(Promise_inj: promise_inj inj' (Local.promises lc2) (Local.promises lc1')).
        {
          exploit write_step_promise_inj_stable; [eapply LOCAL2 | eapply INJ_WRITE | eapply Promise_inj0 | eauto..].
          rewrite INJ_MSG0.
          des_if; ss; des; subst; ss; eauto. introv SPLIT_INJ'.
          exploit SPLIT_INJ'; eauto. ii; subst.
          exploit SPLIT_INJ; eauto. ii; des. do 3 eexists. split; eauto.
        }
        assert(MEM_INJ': MsgInj inj' mem2 mem1').
        {
          eapply write_step_msgInj_stable; eauto.
          rewrite INJ_MSG0. des_if; des; ss; subst; ss.
          introv INJ'. eapply INJ_COMPLETE in INJ'. des.
          do 3 eexists. eauto.
        } 
        eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                        (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
        {
          (* Fulfill *)
          destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
          exists st0'. do 3 eexists. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
          econs. econs.
          instantiate (1 := ThreadEvent.update loc tsr tsw valr valw releasedr' releasedw' ordr ordw). ss; eauto.
          econs; eauto. ss; eauto.
        }
        {
          (* Local wf *)
          eapply local_wf_write; eauto.
        }
        {
          (* Local wf *)
          eapply local_wf_write; eauto.
        }
        {
          (* Memory closed *)
          eapply write_step_closed_mem with (mem1 := mem); eauto.
        }
        {
          (* Memory closed *)
          eapply write_step_closed_mem with (mem1 := mem'); eauto.
        }
        {
          (* Other Inj *)
          introv OTHER_LOC INJ'.
          rewrite INJ_MSG0 in INJ'. des_ifH INJ'; ss; des; subst. inv INJ'; eauto.
          eauto. eauto.
        }
        {
          (* LOC Inj *)
          introv MAX_LE INJ'. rewrite INJ_MSG0 in INJ'.
          des_ifH INJ'; ss; des; subst; ss; eauto.
        }
        {
          (* TViewInj *)
          inv LOCAL2; ss. inv INJ_WRITE; ss.
          eapply TView_inj_write_prsv; eauto.
          eapply incr_inj_TViewInj; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL3; eauto.
          eapply incr_inj_closed_tviewInj; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto. inv WF_LOCAL3; eauto.
          des_if; ss; des; ss; eauto.
        }
        {
          (* Other Cover *)
          introv OTHER_LOC.
          destruct(Loc.eq_dec loc1 loc); subst.  
          eapply write_not_cover_prsv_write; [| eapply LOCAL2 | eapply INJ_WRITE | eauto..]; eauto.
          ii.
          eapply OTHER_NOTCOVER with (ts := ts) in OTHER_LOC; eauto. 
          contradiction OTHER_LOC; eauto.
          eapply write_disj_cover_prsv with (mem := mem') (mem' := mem1') in H0; eauto.
          ii. contradiction H.
          eapply write_disj_cover_prsv with (mem := mem) (mem' := mem2); eauto.
        }
        {
          (* LOC0 Cover *)
          ii. contradiction H.
          eapply LOC0_NOTCOVER1 in H0; eauto.
          contradiction H0.
          eapply write_disj_cover_prsv with (mem := mem') (mem' := mem1'); eauto.
          ii. contradiction H.
          eapply write_disj_cover_prsv with (mem := mem) (mem' := mem2); eauto.
        }
        {
          (* spec view *)
          eapply spec_view_write_prsv_loc_write_disj; eauto.
        }
        {
          (* Reserve *)
          des. exploit write_step_reserve_prsv; [eapply LOCAL2 | eapply MAX_RESERVE | eauto..].
        }
        {
          (* promise less *) 
          ii. eapply write_step_promise_lt_prsv; [eapply LOCAL2 | eauto..].
          ii. rewrite <- PROM_EQ in H0. eauto.
        }
      }
    + (* fence *)
      destruct (classic (ordw = Ordering.seqcst)).
      {
        subst ordw.
        exploit injection_fecne_sc_step; eauto. instantiate (1 := sc').
        ii; des.
        exists st2. do 3 eexists.
        split. eapply Operators_Properties.clos_rt1n_step; eauto.
        econs. econs. instantiate (1 := ThreadEvent.fence ordr Ordering.seqcst).
        eauto. econs; eauto. ss. eauto.
      }
      {
        exploit injection_fecne_step; eauto. instantiate (1 := sc').
        ii; des. 
        eapply IHn with (sc' := sc2') (lc' := lc2') (mem' := mem')
                        (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
        {
          (* Fulfill *)
          destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
          exists st0'. do 3 eexists. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
          econs. econs.
          instantiate (1 := ThreadEvent.fence ordr ordw). ss; eauto.
          econs; eauto. ss; eauto.
        }
        {
          (* Local wf *)
          eapply Local_wf_fence_not_sc; eauto.
        }
        {
          (* Local wf *)
          eapply Local_wf_fence_not_sc; eauto.
        }
        {
          (* Spec view *)
          eapply spec_view_fence_step_prsv; eauto.
        }
        {
          (* Promise le *)
          ii. inv LOCAL0; ss. eauto.
        }
      }
    + ss.
    + inv PF. destruct kind; ss.
      {
        (* lower to none *)
        destruct msg1; ss.
        destruct msg; ss. destruct released0; ss.
        exploit injection_lower_to_none; eauto.
        {
          clear - LOCAL PRM_LESS OTHER_ID LOC0_INJ PRM_EQ.
          inv LOCAL. inv PROMISE. des; ss. inv RESERVE.
          exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
          destruct (Loc.eq_dec loc loc0); subst.
          {
            exploit PRM_LESS; [eapply GET | eauto..]. ii.
            inv PRM_EQ. eapply SOUND in GET; eauto. des.
            exploit LOC0_INJ; eauto.
            eapply Time.le_lteq; eauto. ii; subst. eauto.
          }
          {
            inv PRM_EQ. eapply SOUND in GET; eauto. des.
            exploit OTHER_ID; eauto. ii; subst; eauto.
          }
        }
        ii; des.
        eapply IHn with (sc' := sc') (lc' := lc2') (mem' := mem2')
                        (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
        {
          (* Fulfill *)
          destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
          exists st0'. do 3 eexists. split; eauto. 
          eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
          eapply Thread.nprm_step_pf_step. 
          econs. eapply INJ_PROMISE'. ss.
        }
        {
          (* Local wf *)
          inv LOCAL. destruct lc; ss. eapply local_wf_promise; eauto.
        }
        {
          (* Local wf *)
          inv INJ_PROMISE'. destruct lc'; ss. eapply local_wf_promise; eauto.
        } 
        {
          (* Memory closed *)
          eapply promise_step_closed_mem; eauto.
        }
        {
          (* Memory closed *)
          eapply promise_step_closed_mem; eauto.
        }
        {
          (* TView Inj *)
          rewrite <- TVIEW_EQ1. rewrite <- TVIEW_EQ2. eauto.
        }
        {
          (* OTHER NOT COVER *)
          introv OTHER_LOC NOT_COVER1 NOT_COVER2. contradiction NOT_COVER1.
          inv LOCAL. inv PROMISE. des; subst. inv RESERVE.
          inv INJ_PROMISE'. inv PROMISE. des; subst. inv RESERVE.
          eapply lower_covered with (mem1 := mem); eauto.
          eapply lower_covered with (mem1 := mem') in NOT_COVER2; eauto.
          exploit OTHER_NOTCOVER; eauto. ii.
          contradiction NOT_COVER1.
          eapply lower_covered with (mem1 := mem); eauto. ii; ss.
        }
        {
          (* LOC0 NOT COVER *)
          ii. exploit LOC0_NOTCOVER1; eauto.
          ii. contradiction H.
          inv LOCAL. inv PROMISE. des; subst. inv RESERVE.
          eapply lower_covered with (mem1 := mem); eauto.
          inv INJ_PROMISE'. inv PROMISE. des; subst. inv RESERVE.
          eapply lower_covered with (mem1 := mem') (mem2 := mem2'); eauto.
        }
        {
          (* Spec view *)
          eapply spec_view_lower_none_step_prsv; eauto.
        }
        {
          (* MAX Resereve *)
          des. inv LOCAL. inv PROMISE. des. inv RESERVE.
          erewrite Memory.lower_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          clear - MAX_RESERVE MEM.
          exploit Memory.lower_get0; eauto. ii; des.
          rewrite MAX_RESERVE in GET. inv GET.
        }
        {
          (* Promise lt *)
          introv PROM_GET.
          inv LOCAL; ss. inv PROMISE. des. inv RESERVE.
          erewrite Memory.lower_o in PROM_GET; eauto.
          des_ifH PROM_GET; ss; des; subst; ss; eauto.
          inv PROM_GET.
          exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
          eauto.
        }
      }
      {
        (* Cancel *)
        exploit injection_cancel; eauto. ii; des.
        eapply IHn with (sc' := sc') (lc' := lc2') (mem' := mem2')
                        (loc0 := loc0) (max_ts := max_ts) in A23; eauto.
        {
          (* Fulfill *)
          destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
          exists st0'. do 3 eexists. split; eauto. 
          eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
          eapply Thread.nprm_step_pf_step. 
          econs. eapply INJ_PROMISE'. ss.
        }
        {
          (* Local wf *)
          inv LOCAL. destruct lc; ss. eapply local_wf_promise; eauto.
        }
        {
          (* Local wf *)
          inv INJ_PROMISE'. destruct lc'; ss. eapply local_wf_promise; eauto.
        } 
        {
          (* Memory closed *)
          eapply promise_step_closed_mem; eauto.
        }
        {
          (* Memory closed *)
          eapply promise_step_closed_mem; eauto.
        }
        {
          (* TView Inj *)
          rewrite <- TVIEW_EQ1. rewrite <- TVIEW_EQ2. eauto.
        }
        {
          (* Other not cover *)
          introv OTHER_LOC. 
          assert(~ covered loc1 ts mem -> ~ covered loc1 ts mem').
          {            
            eapply OTHER_NOTCOVER; eauto.
          }
          introv NOT_COVER.
          eapply cancel_not_cover_prsv with (mem2 := mem2) (mem2' := mem2') in H; eauto.
        }
        {
          (* LOC0 not cover *)
          introv NOT_COVER LE_MAX_TS.
          assert(~ covered loc0 ts mem -> ~ covered loc0 ts mem').
          {
            introv NOT_COVER_MEM.
            eapply LOC0_NOTCOVER1 in LE_MAX_TS; eauto.
          }
          eapply cancel_not_cover_prsv with (mem2 := mem2) (mem2' := mem2') in H; eauto.
        }
        {
          (* Spec view *)
          eapply spec_view_cancel_step_prsv with (mem1 := mem) (mem1' := mem'); eauto.
        }
        {
          (* MAX reserve *)
          exists from0. inv LOCAL; ss. inv PROMISE.
          erewrite Memory.remove_o; eauto. des_if; eauto; ss.
          des; subst.
          clear - MAX_RESERVE MEM PROMISES WF_LOCAL PRM_LESS.
          exploit Memory.remove_get0; [eapply PROMISES | eauto..]. ii; des.
          eapply PRM_LESS in GET. auto_solve_time_rel.
        }
        {
          (* PROM LE *)
          ii. inv LOCAL; ss. inv PROMISE.
          erewrite Memory.remove_o in H; eauto.
          des_ifH H; ss. eauto.
        }
      }
Qed.
