Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.
Require Import ReorderPromise.
Require Import MemoryReorder.
Require Import MemoryFacts.
Require Import WFConfig.
Require Import MemoryProps.

Set Implicit Arguments.

Lemma reserve_sc_nochange
      lang (e e': Thread.t lang) lo
      (RSVs: rtc (Thread.reserve_step lo) e e'):
  (Thread.sc e) = (Thread.sc e') /\ (Thread.state e) = (Thread.state e').
Proof.
  induction RSVs; ii; eauto.
  inv H. inv STEP; ss.
Qed.
  
Lemma reorder_reserve_promise
      prom0 mem0
      prom1 mem1
      prom2 mem2
      loc1 from1 to1
      loc2 from2 to2 msg2 kind2
      (STEP1: Memory.promise prom0 mem0 loc1 from1 to1 Message.reserve prom1 mem1 Memory.op_kind_add)
      (STEP2: Memory.promise prom1 mem1 loc2 from2 to2 msg2 prom2 mem2 kind2):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg2 = Message.reserve /\ kind2 = Memory.op_kind_cancel /\
   prom0 = prom2 /\ mem0 = mem2) \/
  (exists prom1' mem1',
      <<STEP1: Memory.promise prom0 mem0 loc2 from2 to2 msg2 prom1' mem1' kind2>> /\
      <<STEP2: Memory.promise prom1' mem1' loc1 from1 to1 Message.reserve prom2 mem2 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2; ss.
  - (* reserve/add *)
    exploit MemoryReorder.add_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
    exploit MemoryReorder.add_add; try exact MEM; try exact MEM0; eauto. i. des.
    right. esplits.
    + econs; eauto; try congr.
      i. exploit Memory.add_get1; try exact MEM; eauto.
    + econs; eauto. ss.
  - (* reserve/split *)
    exploit MemoryReorder.add_split; try exact PROMISES; try exact PROMISES0; eauto. i.
    des; clarify.
    + exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
      right. esplits.
      * econs 2; eauto.
      * econs; eauto. ss.
  - (* reserve/lower *)
    des. subst.
    exploit MemoryReorder.add_lower; try exact PROMISES; try exact PROMISES0; eauto. i.
    des; clarify.
    + exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
      right. esplits.
      * econs; eauto.
      * econs; eauto. ss.
  - (* reserve/cancel *)
    destruct (classic ((loc1, to1) = (loc2, to2))).
    + inv H.
      exploit MemoryReorder.add_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.add_remove_same; try exact MEM0; eauto. i. des. subst.
      left. splits; auto.
    + exploit MemoryReorder.add_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_remove; try exact MEM0; eauto. i. des.
      right. esplits; eauto. econs; eauto. ss.
Qed.

Lemma reorder_promise_reserve_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg2 = Message.reserve /\ kind2 = Memory.op_kind_cancel /\
   lc0 = lc2 /\ mem0 = mem2) \/
  (exists lc1' mem1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2>> /\
      <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit reorder_reserve_promise; eauto. i. des; subst.
  { left. splits; auto. destruct lc0; auto. }
  right. esplits.
  { econs; eauto. inv STEP2.
    
    
    eapply memory_concrete_le_closed_msg; try apply CLOSED0.
    ii. erewrite (@Memory.add_o mem2 mem1') in GET; eauto. des_ifs. }
  { econs; eauto. }
Qed.

Lemma add_non_synch_loc loc0 prom0 loc1 from to msg prom1
      (NONSYNCH: Memory.nonsynch_loc loc0 prom1)
      (ADD: Memory.add prom0 loc1 from to msg prom1)
  :
    Memory.nonsynch_loc loc0 prom0.
Proof.
  ii. eapply Memory.add_get1 in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma reserve_non_synch_loc loc0 prom0 loc1 from to prom1
      (NONSYNCH: Memory.nonsynch_loc loc0 prom0)
      (RSV: Memory.add prom0 loc1 from to Message.reserve prom1)
  :
    Memory.nonsynch_loc loc0 prom1.
Proof.
  ii. erewrite Memory.add_o in GET; eauto.
  destruct (loc_ts_eq_dec (loc0, t) (loc1, to)).
  inv GET; ss; des; subst.
  ss.
  exploit NONSYNCH; eauto.
Qed.

Lemma add_non_synch prom0 loc from to msg prom1
      (NONSYNCH: Memory.nonsynch prom1)
      (ADD: Memory.add prom0 loc from to msg prom1)
  :
    Memory.nonsynch prom0.
Proof.
  ii. eapply Memory.add_get1 in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma reserve_non_synch prom0 loc from to prom1
      (NONSYNCH: Memory.nonsynch prom0)
      (RSV: Memory.add prom0 loc from to Message.reserve prom1)
  :
    Memory.nonsynch prom1.
Proof.
  ii. erewrite Memory.add_o in GET; eauto.
  des_ifs; ss.
  exploit NONSYNCH; eauto.
Qed.

Lemma reorder_reserve_fence
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1
      ord1 ord2 sc0 sc1
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.fence_step lc1 sc0 ord1 ord2 lc2 sc1)
  :
    exists lc1',
      (<<STEP1: Local.fence_step lc0 sc0 ord1 ord2 lc1' sc1>>) /\
      (<<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 Message.reserve lc2 mem1 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss. esplits.
  - econs; eauto.
    + inv PROMISE. i. eapply add_non_synch; eauto.
    + i. ss. subst. erewrite PROMISES in *; auto.
      inv PROMISE. eapply Memory.add_get0 in PROMISES0. des.
      erewrite Memory.bot_get in *. ss.
  - econs; eauto.
Qed.

Lemma reorder_reserve_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1
      loc2 to2 val2 released2 ord2 lo
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2 lo)
  :
    exists lc1',
      (<<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1' lo>>) /\
      (<<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 Message.reserve lc2 mem1 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. esplits; eauto.
  { econs; eauto. inv PROMISE.
    erewrite Memory.add_o in GET; eauto. des_ifs. eauto. }
  { econs; eauto. }
Qed.

Lemma reorder_reserve_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2 lo
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2 lo)
  :
    exists lc1' mem1',
      (<<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2 lo>>) /\
      (<<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss. inv WRITE.
  exploit reorder_reserve_promise.
  { eapply PROMISE. }
  { eapply PROMISE0. }
  i. des; clarify.
  i. des; clarify.
  assert (LOCTS: (loc1, to1) <> (loc2, to2)).
  { ii. clarify. inv PROMISE.
    eapply Memory.add_get0 in MEM. des. inv PROMISE0; ss.
    { eapply Memory.add_get0 in MEM. des. clarify. }
    { des. subst. eapply Memory.split_get0 in MEM. des. clarify. }
    { des. subst. eapply Memory.lower_get0 in MEM. des. clarify. }
  }
  exploit MemoryReorder.add_remove; eauto.
  { inv STEP2. eauto. }
  i. des. esplits.
  { econs; eauto. i. inv PROMISE. eapply add_non_synch_loc; eauto. }
  { econs; eauto. ss. inv STEP2. econs; eauto. }
Qed.

Lemma reorder_promise_add_reserve
      lc1 mem1 loc1 from1 to1 val released
      lc2 mem2 loc2 from2 to2 lc3 mem3
      (PRM_ADD: Local.promise_step lc1 mem1 loc1 from1 to1 (Message.concrete val released) lc2 mem2 Memory.op_kind_add)
      (RSV: Local.promise_step lc2 mem2 loc2 from2 to2 Message.reserve lc3 mem3 Memory.op_kind_add):
  (exists lc' mem',
      Local.promise_step lc1 mem1 loc2 from2 to2 Message.reserve lc' mem' Memory.op_kind_add /\
      Local.promise_step lc' mem' loc1 from1 to1 (Message.concrete val released) lc3 mem3 Memory.op_kind_add) \/
  (loc1 = loc2 /\ to1 = from2).
Proof.
  inv PRM_ADD; inv RSV; ss.
  inv PROMISE; inv PROMISE0; ss.
  exploit MemoryReorder.add_add; [eapply PROMISES | eapply PROMISES0 | eauto..].
  ii. des.
  exploit MemoryReorder.add_add; [eapply MEM | eapply MEM0 | eauto..].
  ii; des.
  destruct (classic (to1 = from2)); subst.
  {
    destruct (classic (loc1 = loc2)); subst.
    {
      (* attach implies not reorder *)
      eauto.
    }
    {
      (* not attach implies reorder *)
      left.
      do 2 eexists.
      split.
      econstructor. econstructor; eauto.
      ii; ss.
      ss.
      ss.
      econstructor; eauto.
      econstructor; eauto.
      ii.
      inv MSG. 
      clear - ATTACH ADD0 GET H.
      exploit ATTACH; eauto.
      instantiate (2 := to'); instantiate (1 := msg').
      erewrite Memory.add_o in GET; eauto.
      destruct (loc_ts_eq_dec (loc1, to') (loc2, to2)); subst; ss.
      des; ss.
      eapply Memory.add_closed_message with (mem1 := mem2); eauto.
    }
  }
  {
    (* not attach implies reorder *)
    destruct (classic (loc1 = loc2)); subst.
    {
      left.
      do 2 eexists.
      split.
      econstructor. econstructor; eauto.
      ii; ss.
      ss.
      ss.
      econstructor; eauto.
      econstructor; eauto.
      ii.
      inv MSG.
      clear - ATTACH ADD0 GET H.
      destruct (classic (to' = to2)); subst.
      {
        eapply Memory.add_get0 in ADD0; des.
        rewrite GET1 in GET; inv GET; ss.
      }
      {
        exploit ATTACH; eauto.
        instantiate (2 := to'); instantiate (1 := msg').
        erewrite Memory.add_o in GET; eauto.
        destruct (loc_ts_eq_dec (loc2, to') (loc2, to2)); subst; ss.
        des; subst; ss.
      }
      eapply Memory.add_closed_message with (mem1 := mem2); eauto.
    }
    {
      left.
      do 2 eexists.
      split.
      econstructor. econstructor; eauto.
      ii; ss.
      ss.
      ss.
      econstructor; eauto.
      econstructor; eauto.
      ii.
      inv MSG.
      clear - ATTACH ADD0 GET H.
      exploit ATTACH; eauto.
      instantiate (2 := to'); instantiate (1 := msg').
      erewrite Memory.add_o in GET; eauto.
      destruct (loc_ts_eq_dec (loc1, to') (loc2, to2)); subst; ss.
      inv GET.
      des; subst; ss.
      eapply Memory.add_closed_message with (mem1 := mem2); eauto.
    }
  }
Qed.

Lemma reorder_promise_add_reserve_step_attached
      lc1 mem1 loc from ts val released lc2 mem2
      to lc3 mem3 loc' from' to' lc4 mem4 
      (PROMISE: Local.promise_step lc1 mem1 loc from ts (Message.concrete val released) lc2 mem2 Memory.op_kind_add)
      (RSV_ATTACH: Local.promise_step lc2 mem2 loc ts to Message.reserve lc3 mem3 Memory.op_kind_add)
      (RSV: Local.promise_step lc3 mem3 loc' from' to' Message.reserve lc4 mem4 Memory.op_kind_add):
  exists lc' mem' lc'' mem'',
    Local.promise_step lc1 mem1 loc' from' to' Message.reserve lc' mem' Memory.op_kind_add /\
    Local.promise_step lc' mem' loc from ts (Message.concrete val released) lc'' mem'' Memory.op_kind_add /\
    Local.promise_step lc'' mem'' loc ts to Message.reserve lc4 mem4 Memory.op_kind_add.
Proof.
  exploit reorder_promise_reserve_promise; [eapply RSV_ATTACH | eapply RSV | eauto..]. ii.
  des; ss.
  exploit reorder_promise_add_reserve; [eapply PROMISE | eapply STEP1 | eauto..]. ii.
  des; ss.
  do 4 eexists; eauto.
  subst.
  clear - RSV_ATTACH RSV.
  inv RSV_ATTACH; inv RSV.
  inv PROMISE; inv PROMISE0.
  clear - MEM MEM0.
  destruct (loc_ts_eq_dec (loc', to) (loc', to')); ss.
  {
    des; ss.
    exploit MemoryReorder.add_add; [eapply MEM | eapply MEM0 | eauto..].
    ii; des.
    subst.
    contradiction LOCTS; eauto.
  }
  {
    des; ss.
    assert(LT1: Time.lt from' to).
    {
      clear - MEM.
      inv MEM.
      inv ADD; eauto.
    }
    assert(LT2: Time.lt from' to').
    {
      clear - MEM0.
      inv MEM0.
      inv ADD; eauto.
    }
    eapply Memory.add_get0 in MEM; des.
    inv MEM0.
    inv ADD.
    unfold Memory.get in GET0.
    unfold Cell.get in GET0.
    eapply DISJOINT in GET0; eauto.
    clear - GET0 LT1 LT2.
    unfold Interval.disjoint in *.
    destruct(Time.le_lt_dec to' to).
    {
      specialize (GET0 to').
      exploit GET0; ss.
      econstructor; ss; eauto.
      eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
    }
    {
      specialize (GET0 to).
      exploit GET0; ss.
      econstructor; ss; eauto.
      eapply Time.le_lteq; eauto.
      econstructor; ss.
      eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
    }
  }
Qed.
  
Lemma reorder_promise_add_reservations_attached:
  forall n lang lc1 mem1 loc from ts val released lc2 mem2
    to lc3 mem3 st sc e'' lo
    (PROMISE: Local.promise_step lc1 mem1 loc from ts (Message.concrete val released) lc2 mem2 Memory.op_kind_add)
    (RSV_ATTACH: Local.promise_step lc2 mem2 loc ts to Message.reserve lc3 mem3 Memory.op_kind_add)
    (RSVs: rtcn (Thread.reserve_step lo) n (Thread.mk lang st lc3 sc mem3) e''),
  exists lc' mem' lc'' mem''  lc4 mem4,
    rtc (Thread.reserve_step lo) (Thread.mk lang st lc1 sc mem1) (Thread.mk lang st lc' sc mem') /\
    Local.promise_step lc' mem' loc from ts (Message.concrete val released) lc'' mem'' Memory.op_kind_add /\
    Local.promise_step lc'' mem'' loc ts to Message.reserve lc4 mem4 Memory.op_kind_add /\
    e'' = Thread.mk lang st lc4 sc mem4.
Proof.
  induction n; ii.
  - inv RSVs; eauto.
    do 6 eexists; eauto.
  - inv RSVs.
    inv A12.
    inv STEP.
    exploit reorder_promise_add_reserve_step_attached; [eapply PROMISE | eapply RSV_ATTACH | eapply LOCAL | eauto..].
    ii; des.
    exploit IHn; [eapply x1 | eapply x2 | eapply A23 | eauto..].
    ii; des; subst.
    do 6 eexists.
    split.
    eapply Relation_Operators.rt1n_trans; [idtac | eapply x | eauto..].
    econstructor; eauto.
    econstructor; eauto.
    split; eauto.
Qed. 

Lemma reorder_promise_split_reserve
      lc1 mem1 loc1 from1 to1 val released ts msg
      lc2 mem2 loc2 from2 to2 lc3 mem3
      (PRM_ADD: Local.promise_step lc1 mem1 loc1 from1 to1 (Message.concrete val released) lc2 mem2
                                   (Memory.op_kind_split ts msg))
      (RSV: Local.promise_step lc2 mem2 loc2 from2 to2 Message.reserve lc3 mem3 Memory.op_kind_add):
  (exists lc' mem',
      Local.promise_step lc1 mem1 loc2 from2 to2 Message.reserve lc' mem' Memory.op_kind_add /\
      Local.promise_step lc' mem' loc1 from1 to1 (Message.concrete val released) lc3 mem3
                         (Memory.op_kind_split ts msg)).
Proof.
  inv PRM_ADD; inv RSV; ss.
  inv PROMISE; inv PROMISE0.
  des; subst.
  exploit MemoryReorder.split_add; [eapply PROMISES | eapply PROMISES0 | eauto..].
  ii; des; subst.
  exploit MemoryReorder.split_add; [eapply MEM | eapply MEM0 | eauto..].
  ii; des; subst.
  do 2 eexists.
  split.
  econstructor.
  econstructor.
  eapply ADD1.
  eapply ADD0.
  ss.
  ii; ss.
  ss.
  ss.
  econstructor; eauto.
  econstructor; eauto.
  eapply Memory.add_closed_message; eauto.
Qed.

Lemma reorder_promise_lower_reserve
      lc1 mem1 loc1 from1 to1 val released msg
      lc2 mem2 loc2 from2 to2 lc3 mem3
      (PRM_ADD: Local.promise_step lc1 mem1 loc1 from1 to1 (Message.concrete val released) lc2 mem2
                                   (Memory.op_kind_lower msg))
      (RSV: Local.promise_step lc2 mem2 loc2 from2 to2 Message.reserve lc3 mem3 Memory.op_kind_add):
  (exists lc' mem',
      Local.promise_step lc1 mem1 loc2 from2 to2 Message.reserve lc' mem' Memory.op_kind_add /\
      Local.promise_step lc' mem' loc1 from1 to1 (Message.concrete val released) lc3 mem3
                         (Memory.op_kind_lower msg)).
Proof.
  inv PRM_ADD; inv RSV; ss.
  inv PROMISE; inv PROMISE0.
  exploit MemoryReorder.lower_add; [eapply PROMISES | eapply PROMISES0 | eauto..].
  ii; des.
  exploit MemoryReorder.lower_add; [eapply MEM | eapply MEM0 | eauto..].
  ii; des.
  do 2 eexists.
  split.
  econstructor.
  econstructor.
  eapply ADD1. eapply ADD0. ss.
  ii; ss. ss. ss.
  econstructor; eauto.
  eapply Memory.add_closed_message; eauto.
Qed.
  
Lemma reorder_promise_step_reserve_steps:
  forall n lang (e e' e'': Thread.t lang) pf te lo
    (PROMISE: Thread.promise_step pf te e e')
    (RSVs: rtcn (Thread.reserve_step lo) n e' e'')
    (NO_RSV_CCL: Thread.not_rsv_ccl_scfence te = true),
    (exists e0, rtc (Thread.reserve_step lo) e e0 /\ Thread.promise_step pf te e0 e'') \/
    (exists e0 e1 loc to ts from msg,
        rtc (Thread.reserve_step lo) e e0 /\
        Thread.promise_step pf te e0 e1 /\ te = ThreadEvent.promise loc from ts msg Memory.op_kind_add /\ 
        Thread.promise_step false (ThreadEvent.promise loc ts to Message.reserve Memory.op_kind_add) e1 e'').
Proof.
  induction n; ii.
  - inv RSVs; eauto.
  - inv RSVs. inv A12. 
    inv PROMISE; inv STEP; ss. 
    destruct msg; ss.
    destruct kind; ss.
    {
      (* promise add / reserve *)
      exploit reorder_promise_add_reserve; eauto. ii.
      des.
      { 
        eapply IHn with (e := Thread.mk lang st lc' sc1 mem') (pf := false)
                        (te := ThreadEvent.promise loc0 from0 to0 (Message.concrete val released) Memory.op_kind_add)
          in A23; eauto.
        des.
        {
          left.
          eexists.
          split.
          eapply Relation_Operators.rt1n_trans; eauto.
          econstructor; eauto.
          econstructor; eauto.
          eauto.
        }
        {
          inv A1; ss.
          right.
          do 7 eexists.
          split.
          eapply Relation_Operators.rt1n_trans; [|eapply A23]; eauto.
          econstructor; eauto.
          econstructor; eauto.
          split; eauto.
        }
        econstructor; eauto.
      }
      {
        subst.
        right.
        exploit reorder_promise_add_reservations_attached; [eapply LOCAL | eapply LOCAL0 | eapply A23 | eauto..].
        ii; des; subst.
        do 7 eexists.
        split.
        eapply x0.
        split.
        econstructor; eauto.
        split.
        econstructor; eauto.
        econstructor; eauto.
      }
    }
    {
      (* promise split / reserve *)
      exploit reorder_promise_split_reserve; eauto.
      ii; des.
      eapply IHn with (e := Thread.mk lang st lc' sc1 mem')
                      (te := ThreadEvent.promise loc0 from0 to0 (Message.concrete val released)
                                                 (Memory.op_kind_split ts3 msg3)) in A23; eauto.
      des.
      {
        left.
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eauto.
      }
      {
        right.
        inv A1.
      }
      econstructor; eauto.
    }
    {
      (* promise lower / reserve *)
      exploit reorder_promise_lower_reserve; [eapply LOCAL | eapply LOCAL0 | eauto..].
      ii; des.
      eapply IHn with (e := Thread.mk lang st lc' sc1 mem')
                      (te := ThreadEvent.promise loc0 from0 to0 (Message.concrete val released)
                                                 (Memory.op_kind_lower msg1)) in A23; eauto.
      des.
      {
        left.
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eauto.
      }
      {
        right.
        do 7 eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
        econstructor; eauto.
        econstructor; eauto.
        split.
        eauto.
        split; eauto.
      }
      econstructor; eauto.
    }
    {
      (* promise reserve: contradiction *)
      destruct kind; ss.
      clear - LOCAL.
      inv LOCAL.
      inv PROMISE.
      des; ss.
      inv LOCAL.
      inv PROMISE; ss.
      des; ss; subst.
      inv PROMISES.
      inv LOWER.
      clear - MSG_LE.
      inv MSG_LE.
    }
Qed.

Lemma reorder_read_reservation
      lc1 mem1 loc to val released ord lc2 lo
      loc2 from2 to2 lc3 mem3
      (READ: Local.read_step lc1 mem1 loc to val released ord lc2 lo)
      (PROMISE: Local.promise_step lc2 mem1 loc2 from2 to2 Message.reserve lc3 mem3 Memory.op_kind_add):
  exists lc',
    Local.promise_step lc1 mem1 loc2 from2 to2 Message.reserve lc' mem3 Memory.op_kind_add /\
    Local.read_step lc' mem3 loc to val released ord lc3 lo.
Proof.
  inv READ; inv PROMISE; ss.
  inv PROMISE0.
  destruct lc1; ss.
  eexists.
  split.
  econstructor; eauto.
  econstructor; eauto.
  eapply Memory.add_get1; eauto.
Qed.

Lemma reorder_read_reserve_steps:
  forall n lang st
    lc1 mem1 loc to val released ord lo
    sc2 lc2 lc2' mem2 sc2'
    (READ: Local.read_step lc1 mem1 loc to val released ord lc2 lo)
    (RSVs: rtcn (Thread.reserve_step lo) n (Thread.mk lang st lc2 sc2 mem1) (Thread.mk lang st lc2' sc2' mem2)),
  exists lc',
    rtc (Thread.reserve_step lo) (Thread.mk lang st lc1 sc2 mem1) (Thread.mk lang st lc' sc2' mem2) /\
    Local.read_step lc' mem2 loc to val released ord lc2' lo.
Proof.
  induction n; ii.
  - inv RSVs.
    eexists. split; eauto.
  - inv RSVs.
    inv A12. inv STEP.
    eapply reorder_read_reservation in READ; eauto.
    des.
    eapply IHn in A23; eauto.
    des; eauto.
    eexists.
    split; [idtac | eapply A0].
    eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
    econstructor; eauto.
    econstructor; eauto.
Qed.

Lemma reorder_write_reserve
      lc1 sc1 mem1 loc1 from1 to1 val releasedr releasedw ord
      lc2 sc2 mem2 kind lo
      loc2 from2 to2 lc3 mem3
      (WRITE: Local.write_step lc1 sc1 mem1 loc1 from1 to1 val releasedr releasedw ord lc2 sc2 mem2 kind lo)
      (RSV: Local.promise_step lc2 mem2 loc2 from2 to2 Message.reserve lc3 mem3 Memory.op_kind_add):
  (exists lc' mem',
      Local.promise_step lc1 mem1 loc2 from2 to2 Message.reserve lc' mem' Memory.op_kind_add /\
      Local.write_step lc' sc1 mem' loc1 from1 to1 val releasedr releasedw ord lc3 sc2 mem3 kind lo) \/
  (loc1 = loc2 /\ to1 = from2 /\ kind = Memory.op_kind_add).
Proof.
  inv WRITE; inv RSV; ss.
  inv WRITE0; inv PROMISE.
  inv PROMISE0.
  - (* add *)
    destruct (classic (loc1 = loc2)); subst.
    {
      destruct (Time.le_lt_dec to2 from1).
      {  
        exploit MemoryReorder.remove_add_disjts; [eapply REMOVE | eapply PROMISES | eauto..].
        ii. des. rename mem1' into promises1'.
        exploit MemoryReorder.add_add; [eapply PROMISES0 | eapply x0 | eauto..].
        ii. des. rename mem1' into promises'.
        exploit MemoryReorder.add_add; [eapply MEM0 | eapply MEM | eauto..].
        ii. des. 
        left.
        do 2 eexists. split. 
        econstructor.
        econstructor. 
        eapply ADD1.
        eapply ADD0.
        ss.
        ii; ss.
        ss.
        ss.
        econstructor; eauto; ss.
        econstructor.
        econstructor.
        eapply ADD2.
        eapply ADD3.
        ss. 
        ii. inv MSG.
        assert(Time.lt to2 to1).
        {
          clear - l ADD3.
          inv ADD3.
          inv ADD.
          eapply DenseOrderFacts.le_lt_lt; eauto.
        }
        assert(Time.lt to2 to').
        { 
          eapply Memory.get_ts in GET.
          clear - GET H. des; subst; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
        }
        exploit Memory.add_o; [eapply ADD0 | eauto..].
        instantiate (2 := loc2); instantiate (1 := to').
        des_if; ss.
        des; subst.
        eapply Time.Time.lt_strorder_obligation_1 in H0; ss.
        ii.
        rewrite x2 in GET.
        eapply ATTACH0 in GET; ss.
        ss.
        i.
        eapply RELEASE in H.
        eapply reserve_non_synch_loc; eauto.
      }
      {
        assert(Time.le to1 from2).
        {  
          destruct (Time.le_lt_dec to1 from2); eauto.
          clear - MEM0 MEM l l0.
          inv MEM.
          inv ADD.
          dup MEM0.
          eapply Memory.add_get0 in MEM1; des.
          unfold Memory.get in GET0.
          unfold Cell.get in GET0.
          eapply DISJOINT in GET0.
          unfold Interval.disjoint in GET0.
          destruct (Time.le_lt_dec to1 to2).
          specialize (GET0 to1).
          exploit GET0; ss.
          inv MEM0.
          inv ADD.
          econstructor; eauto; ss.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          specialize (GET0 to2).
          exploit GET0; ss.
          econstructor; ss.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          econstructor; ss.
          eapply Time.le_lteq; ss; eauto.
        }
        destruct (classic (to1 = from2)); subst.
        right.
        eapply Memory.add_get0 in MEM0; des; eauto. 
        exploit MemoryReorder.remove_add_disjts; [eapply REMOVE | eapply PROMISES | eauto..].
        ii. des. rename mem1' into promises1'.
        exploit MemoryReorder.add_add; [eapply PROMISES0 | eapply x0 | eauto..].
        ii. des. rename mem1' into promises'.
        exploit MemoryReorder.add_add; [eapply MEM0 | eapply MEM | eauto..].
        ii. des.
        left.
        do 2 eexists.
        split.
        econstructor.
        econstructor.
        eapply ADD1.
        eapply ADD0.
        ss.
        ii; ss.
        ss.
        ss.
        econstructor; eauto.
        econstructor; ss.
        econstructor.
        eapply ADD2.
        eapply ADD3.
        ss.
        ii.
        inv MSG.
        assert(to' <> to2).
        {
          intro; subst.
          eapply Memory.add_get0 in ADD0; des.
          rewrite GET1 in GET; inv GET; ss.
        }
        exploit Memory.add_o; [eapply ADD0 | eauto..].
        instantiate(2 := loc2); instantiate(1 := to'); eauto.
        des_if; ss; subst.
        des; subst; ss.
        ii.
        rewrite x2 in GET.
        eauto.
        ss.
        ss; i.
        eapply RELEASE in H1.
        eapply reserve_non_synch_loc; eauto.
      }
    }
    {
      exploit MemoryReorder.remove_add_disjloc; [eapply REMOVE | eapply PROMISES | eauto..].
      ii; des. rename mem1' into promises1'.
      exploit MemoryReorder.add_add; [eapply PROMISES0 | eapply x0 | eauto..].
      ii; des.
      exploit MemoryReorder.add_add; [eapply MEM0 | eapply MEM | eauto..].
      ii; des.
      left.
      do 2 eexists.
      split.
      econstructor.
      econstructor.
      eapply ADD1.
      eapply ADD0.
      ss.
      ii; ss.
      ss.
      ss.
      econstructor; eauto.
      econstructor.
      econstructor.
      eapply ADD2.
      eapply ADD3.
      ss.
      ii.
      inv MSG.  
      exploit Memory.add_o; [eapply ADD0 | eauto..].
      instantiate (2 := loc1); instantiate (1 := to').
      des_if; ss.
      des; ss.
      ii.
      rewrite x2 in GET.
      eauto.
      ss.
      i; ss.
      eapply RELEASE in H0.
      eapply reserve_non_synch_loc; eauto.
    }
  - (* split *)
    des; subst; ss.
    inv RESERVE.
    destruct (classic (loc1 = loc2)); subst.
    { 
      destruct (Time.le_lt_dec to2 from1).
      {  
        exploit MemoryReorder.remove_add_disjts; [eapply REMOVE | eapply PROMISES | eauto..].
        ii. des. rename mem1' into promises1'.
        exploit MemoryReorder.split_add; [eapply PROMISES0 | eapply x0 | eauto..].
        ii. des. rename mem1' into promises'.
        exploit MemoryReorder.split_add; [eapply MEM0 | eapply MEM | eauto..].
        ii. des. 
        left.
        do 2 eexists. split. 
        econstructor.
        econstructor. 
        eapply ADD1.
        eapply ADD0.
        ss.
        ii; ss.
        ss.
        ss.
        econstructor; eauto; ss.
        econstructor.
        econstructor.
        eapply SPLIT2.
        eapply SPLIT0.
        ss.
        do 2 eexists; eauto.
        do 2 eexists; eauto.
        eapply x1.
        i.
        eapply RELEASE in H.
        eapply reserve_non_synch_loc; eauto.
      }
      { 
        assert(Time.lt to1 from2).
        {
          assert(Time.lt to1 ts3).
          {
            inv MEM0.
            inv SPLIT; eauto.
          }
          destruct (Time.le_lt_dec ts3 from2); eauto.
          eapply DenseOrderFacts.lt_le_lt; eauto.
          inv MEM.
          inv ADD.
          eapply Memory.split_get0 in MEM0; des.
          destruct (Time.le_lt_dec ts3 to2).
          unfold Memory.get in GET2.
          unfold Cell.get in GET2.
          eapply DISJOINT in GET2.
          unfold Interval.disjoint in GET2.
          specialize (GET2 ts3).
          exploit GET2.
          econstructor; eauto.
          econstructor; ss; eauto.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          ii; ss.
          destruct (Time.le_lt_dec to2 to1). 
          unfold Memory.get in GET1.
          unfold Cell.get in GET1.
          eapply DISJOINT in GET1.
          unfold Interval.disjoint in GET1.
          specialize (GET1 to2).
          exploit GET1.
          econstructor; eauto; ss.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          econstructor; ss; eauto.
          ii; ss. 
          unfold Memory.get in GET2.
          unfold Cell.get in GET2.
          eapply DISJOINT in GET2.
          unfold Interval.disjoint in GET2.
          specialize (GET2 to2).
          exploit GET2.
          econstructor; eauto; ss.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          econstructor; ss; eauto.
          eapply Time.le_lteq; ss; eauto.          
          ii; ss.
        } 
        exploit MemoryReorder.remove_add_disjts; [eapply REMOVE | eapply PROMISES | eauto..].
        right. eapply Time.le_lteq; eauto.
        ii; des. 
        exploit MemoryReorder.split_add; [eapply PROMISES0 | eapply x0 | eauto..].
        ii; des.
        exploit MemoryReorder.split_add; [eapply MEM0 | eapply MEM | eauto..].
        ii; des.
        left.
        do 2 eexists.
        split.
        econstructor.
        econstructor.
        eapply ADD1. eapply ADD0.
        ss.
        ii; ss.
        ss.
        ss.
        econstructor; eauto.
        econstructor.
        econstructor.
        eapply SPLIT2.
        eapply SPLIT0.
        ss.
        do 2 eexists; eauto.
        do 2 eexists; eauto.
        eauto.
        i; ss.
        eapply RELEASE in H0.
        eapply reserve_non_synch_loc; eauto.
      }
    }
    {
      exploit MemoryReorder.remove_add_disjloc; [eapply REMOVE | eapply PROMISES | eauto..].
      ii; des. rename mem1' into promises1'.
      exploit MemoryReorder.split_add; [eapply PROMISES0 | eapply x0 | eauto..].
      ii; des.
      exploit MemoryReorder.split_add; [eapply MEM0 | eapply MEM | eauto..].
      ii; des.
      left.
      do 2 eexists.
      split.
      econstructor.
      econstructor.
      eapply ADD1.
      eapply ADD0.
      ss.
      ii; ss.
      ss.
      ss.
      econstructor; eauto.
      econstructor.
      econstructor.
      eapply SPLIT2.
      eapply SPLIT0.
      ss.
      do 2 eexists; eauto.
      do 2 eexists; eauto.
      eauto.
      i.
      eapply RELEASE in H0.
      eapply reserve_non_synch_loc; eauto.
    }
  - (* lower *)
    des; subst.
    destruct (classic (loc1 = loc2)); subst.
    {
      destruct (Time.le_lt_dec to2 from1).
      {  
        exploit MemoryReorder.remove_add_disjts; [eapply REMOVE | eapply PROMISES | eauto..].
        ii. des. rename mem1' into promises1'.
        exploit MemoryReorder.lower_add; [eapply PROMISES0 | eapply x0 | eauto..].
        ii. des. rename mem1' into promises'.
        exploit MemoryReorder.lower_add; [eapply MEM0 | eapply MEM | eauto..].
        ii. des. 
        left.
        do 2 eexists. split. 
        econstructor.
        econstructor. 
        eapply ADD1.
        eapply ADD0.
        ss.
        ii; ss.
        ss.
        ss.
        econstructor; eauto; ss.
        i. eapply RELEASE in H.
        eapply reserve_non_synch_loc; eauto.
      }
      { 
        assert(Time.le to1 from2).
        {  
          destruct (Time.le_lt_dec to1 from2); eauto.
          clear - MEM0 MEM l l0.
          inv MEM.
          inv ADD.
          dup MEM0.
          eapply Memory.lower_get0 in MEM1; des.
          unfold Memory.get in GET0.
          unfold Cell.get in GET0.
          eapply DISJOINT in GET0.
          unfold Interval.disjoint in GET0.
          destruct (Time.le_lt_dec to2 to1).
          specialize (GET0 to2).
          exploit GET0; ss.
          econstructor; ss; eauto.
          eapply Time.le_lteq; ss; eauto.
          eapply Memory.get_ts in GET.
          specialize (GET0 to1).
          exploit GET0.
          econstructor; ss; eauto.
          eapply Time.le_lteq; ss; eauto.
          des; subst.
          cut(Time.le Time.bot from2); ii.
          eapply TimeFacts.lt_le_lt in l0; eauto.
          eapply DenseOrder.DenseOrder.lt_strorder_obligation_1 in l0; ss.
          eapply Time.bot_spec.
          econstructor; ss; eauto.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          ii; ss.
        }
        exploit MemoryReorder.remove_add_disjts; [eapply REMOVE | eapply PROMISES | eauto..].
        ii. des. rename mem1' into promises1'.
        exploit MemoryReorder.lower_add; [eapply PROMISES0 | eapply x0 | eauto..].
        ii. des. rename mem1' into promises'.
        exploit MemoryReorder.lower_add; [eapply MEM0 | eapply MEM | eauto..].
        ii. des.
        left.
        do 2 eexists.
        split.
        econstructor.
        econstructor.
        eapply ADD1.
        eapply ADD0.
        ss.
        ii; ss.
        ss.
        ss.
        econstructor; eauto.
        ss; i.
        eapply RELEASE in H0.
        eapply reserve_non_synch_loc; eauto.
      }
    }
    {
      exploit MemoryReorder.remove_add_disjloc; [eapply REMOVE | eapply PROMISES | eauto..].
      ii; des. rename mem1' into promises1'.
      exploit MemoryReorder.lower_add; [eapply PROMISES0 | eapply x0 | eauto..].
      ii; des.
      exploit MemoryReorder.lower_add; [eapply MEM0 | eapply MEM | eauto..].
      ii; des.
      left.
      do 2 eexists.
      split.
      econstructor.
      econstructor.
      eapply ADD1.
      eapply ADD0.
      ss.
      ii; ss.
      ss.
      ss.
      econstructor; eauto.
      i; ss.
      eapply RELEASE in H0.
      eapply reserve_non_synch_loc; eauto.
    }
  - (* reserve contradiction *)
    ss.
Qed.

Lemma reorder_write_reserve_steps_attached:
  forall n lo
    lc1 sc1 mem1 loc from ts val releasedr releasedw ord
    lc2 sc2 to mem2 lc3 mem3 lang st st' e''
    (WRITE: Local.write_step lc1 sc1 mem1 loc from ts val releasedr releasedw ord lc2 sc2 mem2
                             Memory.op_kind_add lo)
    (RSV: Local.promise_step lc2 mem2 loc ts to Message.reserve lc3 mem3 Memory.op_kind_add)
    (RSVs: rtcn (Thread.reserve_step lo) n (Thread.mk lang st lc3 sc2 mem3) e''),    
  exists lc' sc' mem' lc'' sc'' mem'',
    rtc (Thread.reserve_step lo) (Thread.mk lang st' lc1 sc1 mem1) (Thread.mk lang st' lc' sc' mem') /\
    Local.write_step lc' sc' mem' loc from ts val releasedr releasedw ord lc'' sc'' mem''
                     Memory.op_kind_add lo /\
    Local.promise_step lc'' mem'' loc ts to Message.reserve
                       (Thread.local e'') (Thread.memory e'') Memory.op_kind_add /\ (Thread.sc e'' = sc1).
Proof.
  induction n; intros.
  - inv RSVs; eauto.
    assert(SC: sc1 = sc2). { inv WRITE; ss. }
    do 6 eexists.
    split; eauto.
  - inv RSVs.
    assert(SC: sc1 = sc2). { inv WRITE; ss. }
    inv A12.
    inv STEP.
    destruct (classic (loc = loc0)); subst.
    {
      assert(Time.le to0 from \/ Time.le to from0).
      {
        clear - RSV WRITE LOCAL.
        inv RSV; inv WRITE; inv LOCAL; ss.
        inv PROMISE; inv WRITE0; inv PROMISE0.
        inv PROMISE; ss.
        assert(Time.lt ts to).
        {
          inv MEM.
          inv ADD; eauto.
        }
        exploit add_succeed_wf; [eapply MEM0 | eauto..].
        ii; des. 
        eapply Memory.add_get0 in MEM1; eauto; des.
        eapply Memory.add_get1 in GET0; eauto.         
        eapply Memory.add_get0 in MEM; eauto; des.
        eapply DISJOINT in GET0.
        eapply DISJOINT in GET2.
        clear - GET2 GET0 TO1 H.
        destruct(Time.le_lt_dec to0 from); eauto.
        destruct(Time.le_lt_dec to from0); eauto.
        destruct(Time.le_lt_dec to0 ts).
        {
          unfold Interval.disjoint in GET0.
          specialize (GET0 to0).
          exploit GET0.
          econstructor; ss; eauto.
          eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
          econstructor; ss; eauto.
          ii; ss.
        }
        {
          destruct(Time.le_lt_dec to0 to).
          { 
            unfold Interval.disjoint in GET2.
            specialize (GET2 to0).
            exploit GET2. 
            econstructor; ss; eauto.
            eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
            econstructor; ss; eauto.
            ii; ss.
          }
          {
            
            unfold Interval.disjoint in GET2.
            specialize (GET2 to).
            exploit GET2.
            econstructor; ss; eauto.
            eapply Time.le_lteq; ss; eauto.
            econstructor; ss; eauto.
            eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
            ii; ss.
          }
        }
      }
      exploit reorder_promise_reserve_promise; [eapply RSV | eapply LOCAL | eauto..].
      ii; des; subst; ss.
      exploit reorder_write_reserve; [eapply WRITE | eapply STEP1 | eauto..]. 
      ii; des.
      {
        eapply IHn in A23.
        2: eapply x1.
        2: eapply STEP2.
        des.
        do 6 eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23].
        econstructor; eauto.
        econstructor; eauto.
        split; eauto.
      }
      {
        assert(Time.lt from0 to0).
        {
          clear - LOCAL.
          inv LOCAL. inv PROMISE.
          inv MEM. inv ADD; eauto.
        }
        assert(Time.lt from ts).
        {
          clear - WRITE.
          inv WRITE. inv WRITE0. inv PROMISE.
          inv MEM. inv ADD; eauto.
        }
        subst. clear - H H1 H0.
        eapply DenseOrderFacts.le_lt_lt in H; eauto.
        eapply DenseOrder.DenseOrder.lt_strorder_obligation_2 in H; eauto.
        eapply H in H0; eauto.
        eapply DenseOrder.DenseOrder.lt_strorder_obligation_1 in H0; ss.
      }

      exploit reorder_write_reserve; [eapply WRITE | eapply STEP1 | eauto..]. 
      ii; des.
      {
        eapply IHn in A23.
        2: eapply x1.
        2: eapply STEP2.
        des.
        do 6 eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23].
        econstructor; eauto.
        econstructor; eauto.
        split; eauto.
      }
      {
        assert(Time.lt ts to).
        {
          clear - STEP2.
          inv STEP2. inv PROMISE. inv MEM.
          inv ADD; eauto.
        }
        assert(Time.lt ts from0).
        {
          eapply DenseOrderFacts.lt_le_lt; eauto.
        }
        subst.
        eapply DenseOrder.DenseOrder.lt_strorder_obligation_1 in H1; ss.
      }
    }
    {
      exploit reorder_promise_reserve_promise; [eapply RSV | eapply LOCAL | eauto..].
      ii; des; subst; ss.
      exploit reorder_write_reserve; [eapply WRITE | eapply STEP1 | eauto..].
      ii; des; subst; ss.
      eapply IHn in A23.
      2: eapply x1.
      2: eapply STEP2.
      des.
      do 6 eexists.
      split.
      eapply Relation_Operators.rt1n_trans; [idtac | eapply A23].
      econstructor; eauto.
      econstructor; eauto.
      split; eauto.
    }
Qed.

Lemma reorder_fence_reserve
      lc1 sc1 mem1 ordr ordw lc2 sc2
      loc2 from2 to2 lc3 mem3
      (FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (NOSC: ordw <> Ordering.seqcst)
      (PROMISE: Local.promise_step lc2 mem1 loc2 from2 to2 Message.reserve lc3 mem3 Memory.op_kind_add):
  exists lc',
    Local.promise_step lc1 mem1 loc2 from2 to2 Message.reserve lc' mem3 Memory.op_kind_add /\
    Local.fence_step lc' sc1 ordr ordw lc3 sc2.
Proof.
  inv FENCE.
  inv PROMISE; ss.
  eexists.
  split.
  econstructor; eauto.
  econstructor; eauto; ss.
  intro.
  eapply RELEASE in H.
  inv PROMISE0.
  eapply reserve_non_synch; eauto.
Qed. 
  
Lemma reorder_program_step_reserve_steps:
  forall n lang (e e' e'': Thread.t lang) te lo
    (PROG: Thread.program_step te lo e e')
    (RSVs: rtcn (Thread.reserve_step lo) n e' e'')
    (NOSC: ~(exists ordr, te = ThreadEvent.fence ordr Ordering.seqcst))
    (NO_OUT: ThreadEvent.get_machine_event te = MachineEvent.silent),
    (exists e0, rtc (Thread.reserve_step lo) e e0 /\ Thread.program_step te lo e0 e'') \/
    (exists e0 e1 loc to ts from val released ordw,
        rtc (Thread.reserve_step lo) e e0 /\
        Thread.program_step te lo e0 e1 /\ te = ThreadEvent.write loc from ts val released ordw /\
        Thread.promise_step false (ThreadEvent.promise loc ts to Message.reserve Memory.op_kind_add) e1 e'') \/
    (exists e0 e1 loc to ts from valr valw releasedr releasedw ordr ordw,
        rtc (Thread.reserve_step lo) e e0 /\
        Thread.program_step te lo e0 e1 /\
        te = ThreadEvent.update loc from ts valr valw releasedr releasedw ordr ordw /\
        Thread.promise_step false (ThreadEvent.promise loc ts to Message.reserve Memory.op_kind_add) e1 e'').
Proof.
  induction n; intros.
  - inv RSVs; eauto.
  - inv RSVs.
    inv PROG; ss.
    inv LOCAL.
    {
      (* silent *)
      left.
      inv A12.
      inv STEP.  
      eapply IHn with (e := Thread.mk lang st1 lc0 sc2 mem0)
                      (te := ThreadEvent.silent) in A23; eauto.
      des.
      {
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
        econstructor; eauto.
        econstructor; eauto.
        ss.
      }
      ss. ss.      
    }
    {
      (* read *)
      inv A12.
      inv STEP.
      exploit reorder_read_reservation; [eapply LOCAL0 | eapply LOCAL | eauto..].
      ii; des.
      eapply IHn with (e := Thread.mk lang st1 lc' sc2 mem0)
                      (te := ThreadEvent.read loc ts val released ord) in A23; eauto.
      des.
      {
        left.
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
        econstructor; eauto.
        econstructor; eauto.
        ss.
      }
      ss. ss.
    }
    {
      (* write *)
      inv A12.
      inv STEP.
      exploit reorder_write_reserve; [eapply LOCAL0 | eapply LOCAL | eauto..]. 
      ii; des.
      { 
        eapply IHn with (e := Thread.mk lang st1 lc' sc1 mem')
                        (te := ThreadEvent.write loc from to val released ord) in A23; eauto. 
        des. 
        {
          left.
          eexists.
          split.
          eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
          econstructor; eauto.
          econstructor; eauto.
          ss.
        }
        { 
          right. left.
          ss.
          do 9 eexists.
          split.
          eapply Relation_Operators.rt1n_trans; [idtac | eapply A23]; eauto.
          econstructor; eauto.
          econstructor; eauto.
          split; eauto.
        }
        ss.
      }
      {
        subst.
        destruct e''.
        dup A23.
        eapply rtcn_rtc in A0.
        eapply reserve_sc_nochange in A0; ss; des; subst.
        eapply reorder_write_reserve_steps_attached with (st' := st1) in A23; eauto.
        ii; des.
        right. left.
        do 9 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        instantiate (1 := to0).
        ss; subst.
        assert(sc' = sc'').
        {
          clear - A0.
          inv A0; eauto.
        }
        subst. 
        eapply reserve_sc_nochange in A23. ss; des; subst.
        econstructor; eauto.
      }
    }
    {
      (* update *)
      inv A12. inv STEP.
      exploit reorder_write_reserve; [eapply LOCAL2 | eapply LOCAL | eauto..].
      ii; des.
      {
        (* not attach *)
        exploit reorder_read_reservation; [eapply LOCAL1 | eapply x0 | eauto..].
        ii; des.
        eapply IHn with (e := Thread.mk lang st1 lc'0 sc1 mem') in A23; eauto.
        des.
        {
          left.
          eexists.
          split.
          eapply Relation_Operators.rt1n_trans; [idtac | eapply A23 | eauto..].
          econstructor; eauto.
          econstructor; eauto.
          eauto.
        }
        {
          ss.
        }
        {
          inv A1.
          right; right.
          do 12 eexists.
          split.
          eapply Relation_Operators.rt1n_trans; [idtac | eapply A23 | eauto..].
          econstructor; eauto.
          econstructor; eauto.
          eauto.
        }
      }
      {
        (* attach *)
        subst.
        exploit reorder_write_reserve_steps_attached; [eapply LOCAL2 | eapply LOCAL | eauto..].
        instantiate (1 := st1). ii; des.
        eapply rtc_rtcn in x0. destruct x0.
        exploit reorder_read_reserve_steps; [eapply LOCAL1 | eapply H | eauto..].
        ii; des.
        right; right.
        eapply rtcn_rtc in A23.
        destruct e''; ss; subst.
        eapply reserve_sc_nochange in A23.
        ss; des; subst.
        do 12 eexists.
        split; [eapply x4 | eauto..].
        split; eauto. 
        split; eauto. 
        instantiate (1 := to). 
        eapply reserve_sc_nochange in x4; ss; des; subst.
        inv x1; ss.
      }
    }
    {
      (* fence *)
      inv A12. inv STEP. 
      exploit reorder_fence_reserve; [eapply LOCAL0 | idtac | eapply LOCAL | eauto..].
      clear - NOSC; intro; subst.
      contradiction NOSC; eauto.
      ii; des.
      eapply IHn with (e := Thread.mk lang st1 lc' sc1 mem0) in A23; eauto.
      des.
      {
        left. 
        eexists. split. 
        eapply Relation_Operators.rt1n_trans; [idtac | eapply A23 | eauto..].
        econstructor; eauto.
        econstructor; eauto.
        eauto.
      }
      ss. ss.
    }
    {
      (* output *)
      ss.
    }
Qed.

Lemma reorder_lower_step_reserve_steps:
  forall n lang (e e' e'': Thread.t lang) te lo
    (PROG: Thread.promise_step true te e e')
    (RSVs: rtcn (Thread.reserve_step lo) n e' e'')
    (NOCCL: ~ThreadEvent.is_cancel te),
    (exists e0, rtc (Thread.reserve_step lo) e e0 /\ Thread.promise_step true te e0 e'').
Proof.
  induction n; intros.
  - inv RSVs; eauto.
  - inv RSVs. 
    cut (rtcn (Thread.reserve_step lo) 1%nat e' a2). i.
    exploit reorder_promise_step_reserve_steps; [eapply PROG | eapply H | eauto ..].
    inv PROG.
    destruct kind; ss.
    destruct msg1; ss.
    destruct msg; ss.
    destruct msg; ss. inv LOCAL. inv PROMISE. ss.
    ii.
    des; ss. 
    eapply IHn in x1; eauto. des.
    eexists. split. 
    eapply Basic.rtc_PreOrder_obligation_2; [eapply x0 | eapply x1].
    eauto.
    subst.
    inv PROG; ss.
    econs; eauto.
Qed.
