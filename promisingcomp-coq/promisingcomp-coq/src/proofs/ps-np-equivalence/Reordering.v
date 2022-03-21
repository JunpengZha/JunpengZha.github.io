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
Require Import Behavior.
Require Import NPConfiguration.
Require Import NPBehavior.
Require Import MemoryReorder.

Require Import LibTactics.
Require Import FulfillStep.

Set Implicit Arguments.

Lemma rtc_compose:
  forall A R (x y z : A),
    rtc R x y -> rtc R y z ->
    rtc R x z.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma rtcn_n1:
  forall n A R (x y z: A),
    rtcn R n x y -> R y z ->
    rtcn R (S n) x z.
Proof.
  induction n; ii.
  inv H. econs; eauto.
  inv H.
  exploit IHn; [eapply A23 | eapply H0 | eauto..].
Qed.

Lemma rtcn_add:
  forall n1 n2 A R (a1 a2 a3: A)
    (RTC1: rtcn R n1 a1 a2)
    (RTC2: rtcn R n2 a2 a3),
    rtcn R (n1+n2)%nat a1 a3.
Proof.
  induction n1; ii; eauto.
  inv RTC1. ss.
  inv RTC1.
  exploit IHn1; eauto. ii.
  clear - A12 x.
  econs; eauto.
Qed.

Lemma IdentMap_remove_add_reorder
      V k1 k2 (v: V) m
      (NEQ: k1 <> k2):
  IdentMap.remove k1 (IdentMap.add k2 v m) = IdentMap.add k2 v (IdentMap.remove k1 m).
Proof.
  eapply IdentMap.eq_leibniz; eauto.
  unfold IdentMap.Equal. ii.
  destruct (Loc.eq_dec y k1); subst.
  rewrite IdentMap.grs; eauto.
  rewrite IdentMap.gso; eauto.
  rewrite IdentMap.grs; eauto.
  rewrite IdentMap.gro; eauto.
  destruct (Loc.eq_dec y k2); subst.
  rewrite IdentMap.gss; eauto.
  rewrite IdentMap.gss; eauto.
  rewrite IdentMap.gso; eauto.
  rewrite IdentMap.gso; eauto.
  rewrite IdentMap.gro; eauto.
Qed.
  
(** Reordering *)
Lemma PRC_step_state_sc_unchange':
  forall n lang st lc sc mem st' lc' sc' mem' lo
    (PRC_STEPS: rtcn (@Thread.prc_step lang lo) n
                     (Thread.mk lang st lc sc mem)
                     (Thread.mk lang st' lc' sc' mem')),
    st = st' /\ sc = sc'.
Proof.
  induction n; ii.
  inv PRC_STEPS; ss.
  inv PRC_STEPS; ss. destruct a2.
  eapply IHn in A23; eauto. des; subst.
  inv A12. inv PRC. eauto.
Qed.

Lemma PRC_step_state_sc_unchange
      lang st lc sc mem st' lc' sc' mem' lo
      (PRC_STEPS: rtc (@Thread.prc_step lang lo)
                      (Thread.mk lang st lc sc mem)
                      (Thread.mk lang st' lc' sc' mem')):
  st = st' /\ sc = sc'.
Proof.
  eapply rtc_rtcn in PRC_STEPS. des.
  eapply PRC_step_state_sc_unchange'; eauto.
Qed.

Inductive na_fulfill_step {lang: language}
          (lo: Ordering.LocOrdMap) (sc: TimeMap.t) (mem: Memory.t):
  (Language.state lang * Local.t) ->
  (Language.state lang * Local.t) -> Prop :=
| na_fulfill_step_write
    st lc loc from to val st' lc' 
    (NA_WRITE_STATE: Language.step lang (ProgramEvent.write loc val Ordering.plain) st st')
    (FULFILL: fulfill_step lc sc loc from to val None None Ordering.plain lc' sc)
    (GET_MEM: Memory.get loc to mem = Some (from, Message.concrete val None))
    (ORD_MATCH: Ordering.mem_ord_match Ordering.plain (lo loc)):
  na_fulfill_step lo sc mem (st, lc) (st', lc')
| na_fulfill_step_read
    st lc loc to val st' lc' released
    (NA_READ_STATE: Language.step lang (ProgramEvent.read loc val Ordering.plain) st st')
    (NA_READ: Local.read_step lc mem loc to val released Ordering.plain lc' lo):
  na_fulfill_step lo sc mem (st, lc) (st', lc')
| na_fulfill_step_silent
    st lc st'
    (NA_SILENT_STATE: Language.step lang ProgramEvent.silent st st'):
  na_fulfill_step lo sc mem (st, lc) (st', lc).

Lemma na_step_to_na_fulfill_step
      lang st lc sc mem st' lc' sc' mem' lo
      (NA_STEP: Thread.na_step lo (Thread.mk lang st lc sc mem)
                               (Thread.mk lang st' lc' sc' mem')):
  exists lc0,
    rtc (Thread.prc_step lo)
        (Thread.mk lang st lc sc mem) (Thread.mk lang st lc0 sc mem')
    /\ na_fulfill_step lo sc mem' (st, lc0) (st', lc')
    /\ sc = sc'.
Proof. 
  inv NA_STEP; inv STEP; ss; inv LOCAL; ss.
  - (* read *)
    exists lc. split; eauto. split; eauto.
    eapply na_fulfill_step_read; eauto.
  - (* write *)
    exploit write_promise_fulfill_na_write; eauto.
    ii; des; subst.
    eexists.
    split.
    eapply Operators_Properties.clos_rt1n_step.
    econs. econs; eauto.
    assert (sc = sc').
    {
      inv STEP2; ss.
    }
    subst sc'.
    split; eauto.
    assert (WRITE_RELEASE_NONE: 
             TView.write_released (Local.tview lc) sc loc to None
                                  Ordering.plain = None).
    {
      unfold TView.write_released. 
      assert (ORD: Ordering.le Ordering.relaxed Ordering.plain = false).
      eauto.
      rewrite ORD. eauto.
    }
    rewrite WRITE_RELEASE_NONE in STEP2.
    eapply na_fulfill_step_write; eauto.

    (* promise step message in mem *)
    inv STEP1.
    eapply Memory.promise_get2 in PROMISE; eauto.
    des. rewrite WRITE_RELEASE_NONE in GET_MEM; eauto.
    inv PROMISE; ss.

    (* na location match *)
    inv LOCAL0; eauto.
  - (* silent *)
    exists lc'.
    split; eauto. split; eauto.
    eapply na_fulfill_step_silent; eauto.
Qed.

Lemma na_fulfill_step_mem_ge
      lang lo sc mem st lc st' lc' mem' sc'
      (NA_FULFILL_STEP: @na_fulfill_step lang lo sc mem (st, lc) (st', lc'))
      (MEM_LE: Memory.le mem mem'):
  @na_fulfill_step lang lo sc' mem' (st, lc) (st', lc').
Proof.
  inv NA_FULFILL_STEP; try solve [econs; eauto].
  eapply na_fulfill_step_write; eauto.
  inv FULFILL. destruct lc; ss.
  unfold TView.write_tview. ss.
  assert (ORD_LE: Ordering.le Ordering.acqrel Ordering.plain = false).
  {
    eauto.
  }
  rewrite ORD_LE.
  econs; eauto. ss.
  inv WRITABLE. econs; eauto.
  inv NA_READ.
  eapply na_fulfill_step_read; eauto.
Qed. 

Lemma na_fulfill_step_to_na_step
      lang st lc sc mem st' lc' lo
      (NA_FULFILL_STEP: @na_fulfill_step lang lo sc mem (st, lc) (st', lc')):
  @Thread.na_step lang lo (Thread.mk lang st lc sc mem)
                  (Thread.mk lang st' lc' sc mem).
Proof.
  inv NA_FULFILL_STEP.
  - (* write *)
    exploit fulfill_step_to_local_write_step; eauto.
    {
      assert (ORD_LE: Ordering.le Ordering.strong_relaxed Ordering.plain = false).
      eauto.
      rewrite ORD_LE. ii; ss.
    }
    {
      inv FULFILL; eauto.
    }
    {
      econs; eauto. ss.
      unfold TimeMap.bot.
      eapply Time.bot_spec.
    }

    ii; des.
    eapply Thread.na_plain_write_step_intro; eauto.
    econs; eauto.
  - (* read *)
    eapply Thread.na_plain_read_step_intro; eauto.
    econs; eauto.
  - (* silent *)
    eapply Thread.na_tau_step_intro; eauto.
    econs; eauto.
Qed.

Lemma na_fulfill_steps_to_na_steps:
  forall n (lang: language) st lc sc mem st' lc' lo
    (THRD_NA_STEPS: rtcn (@na_fulfill_step lang lo sc mem) n (st, lc) (st', lc')),
    rtcn (@Thread.na_step lang lo) n
         (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc mem).
Proof.
  induction n; ii; eauto.
  - inv THRD_NA_STEPS. eauto.
  - inv THRD_NA_STEPS. destruct a2.
    eapply IHn in A23; eauto.
    eapply na_fulfill_step_to_na_step in A12.
    eauto.
Qed.

Lemma reorder_fulfill_step_promise_step
      lc sc loc0 from0 to0 val releasedm released lc' sc' ord
      mem loc from to msg lc'' mem'' kind val0 R0
      (FULFILL: fulfill_step lc sc loc0 from0 to0 val releasedm released ord lc' sc')
      (PROMISE: Local.promise_step lc' mem loc from to msg lc'' mem'' kind)
      (GET_MEM: Memory.get loc0 to0 mem = Some (from0, Message.concrete val0 R0)):
  exists lc1,
    Local.promise_step lc mem loc from to msg lc1 mem'' kind
    /\ fulfill_step lc1 sc loc0 from0 to0 val releasedm released ord lc'' sc
    /\ Memory.get loc0 to0 mem'' = Some (from0, Message.concrete val0 R0).
Proof.
  inv FULFILL; ss. 
  inv PROMISE; ss.
  inv PROMISE0; ss.
  - (* add *)
    exploit MemoryReorder.remove_add_disj; eauto.
    exploit Memory.add_msg_not_exits; eauto. ii; des; subst; ss; eauto.
    right.
    split; eauto.
    clear - GET_MEM TIME MEM.
    destruct (Time.le_lt_dec to from0); eauto.
    destruct (Time.le_lt_dec to0 from); eauto.
    exploit Memory.add_get0; eauto. ii; des.
    exploit Memory.add_get1; eauto. ii.
    exploit Memory.get_disjoint; [eapply GET0 | eapply x0 | eauto..].
    ii; des; subst.
    rewrite GET_MEM in GET; ss.
    unfold Interval.disjoint in x1.
    assert (LT: Time.lt from to).
    {
      inv MEM. inv ADD; eauto.
    }
    destruct (Time.le_lt_dec to to0).
    {
      specialize (x1 to).
      exploit x1; eauto.
      econs; eauto; ss. eapply Time.le_lteq; eauto.
      econs; eauto; ss.
      ii; ss.
    }
    {
      specialize (x1 to0).
      exploit x1; eauto.
      econs; eauto; ss. eapply Time.le_lteq; eauto.
      econs; eauto; ss. eapply Time.le_lteq; eauto.
      ii; ss.
    }

    ii; des. renames mem1' to promises'.
    eexists.
    split.
    econs; eauto.
    split.
    destruct lc; ss.
    eapply Memory.add_get1; eauto.
  - (* split *)
    des; subst; ss.
    exploit MemoryReorder.remove_split_aux; eauto.
    ii; des. renames mem1' to promises1'.
    eexists.
    split.
    econs; eauto. econs; eauto.
    split.
    destruct lc; ss.
    erewrite Memory.split_o; eauto.
    des_if; ss; eauto.
    des; subst; ss.
    exploit Memory.split_get0; [eapply MEM | eauto..].
    ii; des.
    rewrite GET_MEM in GET; ss.
    des_if; ss; eauto.
    destruct a; subst.
    des; ss.
    exploit Memory.remove_get0; [eapply REMOVE | eauto..].
    ii; des.
    exploit Memory.split_get0; [eapply PROMISES | eauto..].
    ii; des.
    rewrite GET0 in GET2. ss.
  - (* lower *)
    des; subst; ss.
    exploit MemoryReorder.remove_lower_aux; eauto.
    ii; des. renames mem1' to promises1'.
    eexists.
    split.
    econs; eauto.
    split.
    destruct lc; ss.
    erewrite Memory.lower_o; eauto.
    des_if; ss.
    des; subst; ss.
    exploit Memory.remove_get0; [eapply REMOVE | eauto..].
    ii; des.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..].
    ii; des.
    rewrite GET0 in GET1. ss.
  - (* cancel *)
    exploit MemoryReorder.remove_remove;
      [eapply REMOVE | eapply PROMISES | eauto..].
    ii; des.
    eexists.
    split.
    econs; eauto.
    split.
    destruct lc; ss.
    erewrite Memory.remove_o; eauto.
    des_if; ss; eauto.
    des; subst.
    exploit Memory.remove_get0; [eapply MEM | eauto..].
    ii; des.
    rewrite GET_MEM in GET. ss.
Qed.

Lemma reorder_na_read_step_promise_step
      mem lc loc to val released lc' lo kind msg lc'' mem''
      loc0 from0 to0 
      (READ: Local.read_step lc mem loc to val released Ordering.plain lc' lo)
      (PROM: Local.promise_step lc' mem loc0 from0 to0 msg lc'' mem'' kind):
  exists lc1 released1,
    Local.promise_step lc mem loc0 from0 to0 msg lc1 mem'' kind
    /\ Local.read_step lc1 mem'' loc to val released1 Ordering.plain lc'' lo.
Proof.
  inv READ.
  inv PROM; ss. inv PROMISE; ss.
  - (* add *)
    exploit Memory.add_get1; eauto. ii; des.
    do 2 eexists.
    split.
    econs; eauto.
    econs; eauto.
  - (* split *)
    des; subst; ss.
    exploit Memory.split_get1; eauto. ii; des.
    do 2 eexists.
    split.
    econs; eauto.
    econs; eauto.
    econs; eauto.
  - (* lower *)
    des; subst; ss. 
    exploit Memory.lower_get1; [eapply MEM | eauto..].
    ii; des. inv MSG_LE.
    do 2 eexists.
    split; eauto.
    econs; eauto.
    ss.
    inv READABLE.
    econs; eauto.
  - (* cancel *)
    assert (MEM_GET: Memory.get loc to mem'' = Some (from, Message.concrete val released)).
    {
      erewrite Memory.remove_o; eauto.
      des_if; ss; eauto.
      des; subst.
      exploit Memory.remove_get0; [eapply MEM | eauto..]. 
      ii; des.
      rewrite GET in GET0. ss.
    }
    do 2 eexists.
    split; eauto.
Qed.

Lemma reorder_na_fulfill_step_prc_step
      lang lo st lc sc mem st' lc' sc' mem' st0 lc0
      (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st, lc) (st0, lc0))
      (PRC_STEP: Thread.prc_step lo
                                 (Thread.mk lang st0 lc0 sc mem)
                                 (Thread.mk lang st' lc' sc' mem')):
  exists st1 lc1,
    Thread.prc_step lo (Thread.mk lang st lc sc mem)
                    (Thread.mk lang st1 lc1 sc' mem')
    /\ na_fulfill_step lo sc' mem' (st1, lc1) (st', lc').
Proof.
  inv PRC_STEP. inv PRC; ss.
  inv NA_FULFILL_STEP; ss.
  - (* write *)
    exploit reorder_fulfill_step_promise_step; eauto.
    ii; des.
    do 2 eexists.
    split. 
    econs. econs; eauto.
    eapply na_fulfill_step_write; eauto.
  - (* read *)
    exploit reorder_na_read_step_promise_step; eauto.
    ii; des.
    do 2 eexists.
    split.
    econs. econs; eauto.
    eapply na_fulfill_step_read; eauto.
  - (* silent *)
    do 2 eexists.
    split.
    econs; eauto.
    econs; eauto.
    eapply na_fulfill_step_silent; eauto.
Qed.

Lemma reorder_na_fulfill_step_prc_steps':
  forall n lang lo st lc sc mem st' lc' sc' mem' st0 lc0
    (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st, lc) (st0, lc0))
    (PRC_STEPS: rtcn (Thread.prc_step lo) n
                     (Thread.mk lang st0 lc0 sc mem) (Thread.mk lang st' lc' sc' mem')),
  exists st1 lc1,
    rtcn (Thread.prc_step lo) n
         (Thread.mk lang st lc sc mem) (Thread.mk lang st1 lc1 sc' mem')
    /\ na_fulfill_step lo sc' mem' (st1, lc1) (st', lc').
Proof.
  induction n; ii.
  - inv PRC_STEPS; ss.
    exists st lc. split; eauto.
  - inv PRC_STEPS. destruct a2.
    exploit reorder_na_fulfill_step_prc_step; eauto.
    ii; des.
    eapply IHn in A23; eauto.
    des.
    exists st2 lc2.
    split; eauto.
Qed.

Lemma reorder_na_fulfill_step_prc_steps:
  forall n lang lo st lc sc mem st' lc' sc' mem' st0 lc0
    (NA_FULFILL_STEP: na_fulfill_step lo sc mem (st, lc) (st0, lc0))
    (PRC_STEPS: rtcn (Thread.prc_step lo) n
                     (Thread.mk lang st0 lc0 sc mem) (Thread.mk lang st' lc' sc' mem')),
  exists st1 lc1,
    rtc (Thread.prc_step lo)
        (Thread.mk lang st lc sc mem) (Thread.mk lang st1 lc1 sc' mem')
    /\ na_fulfill_step lo sc' mem' (st1, lc1) (st', lc').
Proof.
  ii. eapply reorder_na_fulfill_step_prc_steps' in PRC_STEPS; eauto.
  des.
  eapply rtcn_rtc in PRC_STEPS. eauto.
Qed.

Lemma reorder_na_fulfill_steps_prc_steps:
  forall n1 n2 lang lo st lc sc mem st' lc' sc' mem' st0 lc0
    (NA_FULFILL_STEPS: rtcn (na_fulfill_step lo sc mem) n1 (st, lc) (st0, lc0))
    (PRC_STEPS: rtcn (Thread.prc_step lo) n2
                     (Thread.mk lang st0 lc0 sc mem) (Thread.mk lang st' lc' sc' mem')),
  exists st1 lc1,
    rtcn (Thread.prc_step lo) n2
         (Thread.mk lang st lc sc mem) (Thread.mk lang st1 lc1 sc' mem')
    /\ rtcn (na_fulfill_step lo sc' mem') n1 (st1, lc1) (st', lc').
Proof.
  induction n1; ii.
  - inv NA_FULFILL_STEPS.
    exists st' lc'. split; eauto.
  - inv NA_FULFILL_STEPS. destruct a2.
    exploit IHn1; eauto. ii; des.
    exploit reorder_na_fulfill_step_prc_steps'; eauto.
    ii; des.
    exists st2 lc2.
    split; eauto.
Qed.

Lemma promises_forward_na_step:
  forall n (lang: language) st lc sc mem st' lc' sc' mem' lo
    st'' lc'' sc'' mem''
    (NA_STEP: Thread.na_step lo (Thread.mk lang st lc sc mem)
                             (Thread.mk lang st' lc' sc' mem'))
    (PRC_STEPS: rtcn (Thread.prc_step lo) n
                     (Thread.mk lang st' lc' sc' mem')
                     (Thread.mk lang st'' lc'' sc'' mem'')),
  exists lc0,
    rtc (Thread.prc_step lo)
        (Thread.mk lang st lc sc mem) (Thread.mk lang st lc0 sc mem'')
    /\ @na_fulfill_step lang lo sc mem'' (st, lc0) (st'', lc'')
    /\ sc = sc''.
Proof.
  ii.
  eapply na_step_to_na_fulfill_step in NA_STEP; eauto.
  des. subst.
  exploit reorder_na_fulfill_step_prc_steps; eauto.
  ii; des.
  exploit PRC_step_state_sc_unchange; [eapply x0 | eauto..].
  ii; des; subst.
  exists lc1.
  split; eauto.
  eapply rtc_compose; eauto.
Qed.

(** Lemma B.18 *)
Lemma promises_forward_na_steps:
  forall n (lang: language) st lc sc mem st' lc' sc' mem' lo
    (THRD_NA_STEPS: rtcn (@Thread.na_step _ lo) n
                         (Thread.mk lang st lc sc mem)
                         (Thread.mk lang st' lc' sc' mem')),
  exists lc0,
    rtc (@Thread.prc_step _ lo)
        (Thread.mk lang st lc sc mem) (Thread.mk lang st lc0 sc mem')
    /\ rtcn (@na_fulfill_step lang lo sc mem') n (st, lc0) (st', lc')
    /\ sc = sc'.
Proof.
  induction n; ii.
  - inv THRD_NA_STEPS.
    exists lc'.
    split; eauto.
  - inv THRD_NA_STEPS. destruct a2.
    eapply IHn in A23; eauto. des. subst sc0.
    eapply rtc_rtcn in A23. des. 
    exploit promises_forward_na_step; eauto.
    ii; des. subst.
    clear - x1 x0 A0 A23.
    assert (RTC_SN: rtcn (na_fulfill_step lo sc' mem') (S n)
                         (st, lc1) (st', lc')).
    {
      econs; eauto.
    }
    exists lc1.
    split; eauto.
Qed.

Lemma consistency_forward_na_step
      (lang: language) st lc sc mem st' lc' lo
      (THRD_NA_STEPS: @na_fulfill_step lang lo sc mem (st, lc) (st', lc'))
      (CONSISTENT: Thread.consistent (Thread.mk lang st' lc' sc mem) lo):
    Thread.consistent (Thread.mk lang st lc sc mem) lo.
Proof.
  unfold Thread.consistent; ss.
  ii.
  unfold Thread.consistent in CONSISTENT; ss.
  exploit CONSISTENT; eauto. ii; des.
  eapply na_fulfill_step_mem_ge with
    (sc' := sc1) (mem' := mem1) in THRD_NA_STEPS; eauto.
  eapply na_fulfill_step_to_na_step in THRD_NA_STEPS.
  exists e2. split; eauto.
  clear - THRD_NA_STEPS STEPS.
  eapply Relation_Operators.rt1n_trans; [ | eapply STEPS | eauto..].
  clear - THRD_NA_STEPS.

  inv THRD_NA_STEPS.
  econs. econs. eapply Thread.step_program; eauto. eauto.
  econs. econs. eapply Thread.step_program; eauto. eauto.
  econs. econs. eapply Thread.step_program; eauto. eauto.
  inv CAP; eauto.
Qed.
  
Lemma consistency_forward_na_steps:
  forall n (lang: language) st lc sc mem st' lc' lo
    (THRD_NA_STEPS: rtcn (@na_fulfill_step lang lo sc mem) n (st, lc) (st', lc'))
    (CONSISTENT: Thread.consistent (Thread.mk lang st' lc' sc mem) lo),
    Thread.consistent (Thread.mk lang st lc sc mem) lo.
Proof.
  induction n; intros; ss.
  - inv THRD_NA_STEPS. eauto.
  - inv THRD_NA_STEPS. destruct a2.
    eapply IHn in A23; eauto.
    eapply consistency_forward_na_step; eauto.
Qed.

Lemma prc_steps_forward_na_step_same_thread:
  forall (lang: language) e e' e'' (lo: Ordering.LocOrdMap)
    (THRD_NA_STEP: @Thread.na_step lang lo e e')
    (THRD_PRC_STEPS: rtc (@Thread.prc_step lang lo) e' e''),
  exists e0,
    rtc (@Thread.prc_step lang lo) e e0
    /\ rtc (@Thread.na_step lang lo) e0 e''.
Proof.
  ii.
  eapply rtc_rtcn in THRD_PRC_STEPS. des.
  destruct e, e', e''.
  exploit promises_forward_na_step; eauto.
  ii; des. subst sc1.
  eapply na_fulfill_step_to_na_step in x1.
  eexists.
  split; eauto.
Qed.

Lemma prc_steps_forward_na_steps_same_thread':
  forall n (lang: language) e e' e'' (lo: Ordering.LocOrdMap)
    (THRD_NA_STEPS: rtcn (@Thread.na_step lang lo) n e e')
    (THRD_PRC_STEPS: rtc (@Thread.prc_step lang lo) e' e''),
  exists e0,
    rtc (@Thread.prc_step lang lo) e e0
    /\ rtc (@Thread.na_step lang lo) e0 e''.
Proof.
  induction n; ii.
  - inv THRD_NA_STEPS.
    exists e''. split; eauto.
  - inv THRD_NA_STEPS.
    exploit IHn; eauto.
    ii; des.
    exploit prc_steps_forward_na_step_same_thread; eauto.
    ii; des.
    exists e1. split; eauto.
    eapply rtc_compose; eauto.
Qed.

Lemma prc_steps_forward_na_steps_same_thread:
  forall (lang: language) e e' e'' (lo: Ordering.LocOrdMap)
    (THRD_NA_STEPS: rtc (@Thread.na_step lang lo) e e')
    (THRD_PRC_STEPS: rtc (@Thread.prc_step lang lo) e' e''),
  exists e0,
    rtc (@Thread.prc_step lang lo) e e0
    /\ rtc (@Thread.na_step lang lo) e0 e''.
Proof.
  ii.
  eapply rtc_rtcn in THRD_NA_STEPS. des.
  eapply prc_steps_forward_na_steps_same_thread'; eauto.
Qed.
