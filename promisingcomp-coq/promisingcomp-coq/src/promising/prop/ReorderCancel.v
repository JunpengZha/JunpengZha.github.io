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
Require Import MemoryMerge.
Require Import ReorderPromise.
Require Import MemoryReorder.
Require Import MemoryFacts.

Set Implicit Arguments.

Lemma reorder_read_cancel
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1 lo
      loc2 to2 val2 released2 ord2
      (STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1 lo)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.read_step lc1' mem1 loc2 to2 val2 released2 ord2 lc2 lo>>).
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get1_diff; eauto.
  { ii. clarify. ss. inv PROMISE.
    eapply Memory.remove_get0 in MEM. des. clarify. }
  i. des. esplits; eauto.
Qed.

Lemma remove_non_synch_loc loc0 prom0 loc1 from to msg prom1
      (NONSYNCH: Memory.nonsynch_loc loc0 prom0)
      (REMOVE: Memory.remove prom0 loc1 from to msg prom1)
  :
    Memory.nonsynch_loc loc0 prom1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma remove_non_synch prom0 loc from to msg prom1
      (NONSYNCH: Memory.nonsynch prom0)
      (REMOVE: Memory.remove prom0 loc from to msg prom1)
  :
    Memory.nonsynch prom1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma reorder_write_cancel
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 lo
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1 sc2 mem1 kind2 lo)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel)
  :
    exists lc1' mem1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1' Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.write_step lc1' sc0 mem1' loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2 lo>>).
Proof.
  inv STEP2. inv PROMISE.
  inv STEP1. ss. inv WRITE.
  exploit MemoryReorder.remove_remove.
  { eapply REMOVE. }
  { eapply PROMISES. } i. des.
  assert (LOCTS: (loc2, to2) <> (loc1, to1)).
  { ii. clarify. apply Memory.remove_get0 in MEM. inv PROMISE.
    - apply Memory.add_get0 in MEM0. des. clarify.
    - apply Memory.split_get0 in MEM0. des. clarify.
    - apply Memory.lower_get0 in MEM0. des. clarify.
    - clarify. }
  inv PROMISE.
  - exploit MemoryReorder.add_remove.
    { eapply LOCTS. }
    { eapply PROMISES0. }
    { eauto. } i. des.
    exploit MemoryReorder.add_remove.
    { eapply LOCTS. }
    { eapply MEM0. }
    { eauto. } i. des.
    esplits.
    + econs; eauto.
    + econs; ss.
      * econs.
        { econs 1; eauto.
          i. erewrite Memory.remove_o in GET; eauto.
          des_ifs. eapply ATTACH; eauto. }
        { eauto. }
      * intros ORD. eapply RELEASE in ORD.
        eapply remove_non_synch_loc; eauto.
  - destruct (classic ((loc2, ts3) = (loc1, to1))) as [|LOCTS2]; clarify.
    { exploit MemoryReorder.split_remove_same.
      { eapply PROMISES0. }
      { eauto. } i. des. clarify.
    }
    { exploit MemoryReorder.split_remove.
      { eapply LOCTS. }
      { eapply LOCTS2. }
      { eapply PROMISES0. }
      { eauto. } i. des.
      exploit MemoryReorder.split_remove.
      { eapply LOCTS. }
      { eapply LOCTS2. }
      { eapply MEM0. }
      { eauto. } i. des.
      esplits.
      + econs; eauto.
      + econs; ss.
        * econs.
          { econs 2; eauto. }
          { eauto. }
        * intros ORD. eapply RELEASE in ORD.
          eapply remove_non_synch_loc; eauto. }
  - exploit MemoryReorder.lower_remove.
    { eapply LOCTS. }
    { eapply PROMISES0. }
    { eauto. } i. des.
    exploit MemoryReorder.lower_remove.
    { eapply LOCTS. }
    { eapply MEM0. }
    { eauto. } i. des.
    esplits.
    + econs; eauto.
    + econs; ss.
      * econs.
        { econs 3; eauto. }
        { eauto. }
      * intros ORD. eapply RELEASE in ORD.
        eapply remove_non_synch_loc; eauto.
  - clarify.
Qed.

Lemma reorder_fence_cancel
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1
      ord1 ord2 sc0 sc1
      (STEP1: Local.fence_step lc0 sc0 ord1 ord2 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.fence_step lc1' sc0 ord1 ord2 lc2 sc1>>).
Proof.
  inv STEP1. inv STEP2. ss. esplits.
  - econs; eauto.
  - econs; eauto.
    + inv PROMISE. i. eapply remove_non_synch; eauto.
    + i. ss. subst. erewrite PROMISES in *; auto.
      inv PROMISE. eapply Memory.remove_get0 in PROMISES0. des.
      erewrite Memory.bot_get in *. ss.
Qed. 

Lemma reorder_reserve_cancel
      lc0 mem0 loc0 from0 to0 lc1 mem1
      loc1 from1 to1 lc2 mem2
      (PROMISE: Local.promise_step lc0 mem0 loc0 from0 to0 Message.reserve lc1 mem1 Memory.op_kind_add)
      (CCL: Local.promise_step lc1 mem1 loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_cancel):
  (lc0 = lc2 /\ mem0 = mem2) \/
  (exists lc' mem',
      Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc' mem' Memory.op_kind_cancel /\
      Local.promise_step lc' mem' loc0 from0 to0 Message.reserve lc2 mem2 Memory.op_kind_add).
Proof.
  inv PROMISE; inv CCL; ss.
  inv PROMISE0; inv PROMISE; ss.
  destruct (loc_ts_eq_dec (loc0, to0) (loc1, to1)); ss.
  {
    (* reserve cancel same message *)
    des; subst.
    dup PROMISES.
    eapply Memory.add_get0 in PROMISES; des.
    dup PROMISES0. 
    eapply Memory.remove_get0 in PROMISES0; des.
    rewrite GET0 in GET1; inv GET1.
    exploit MemoryMerge.add_remove; [eapply PROMISES1 | eapply PROMISES2 | eauto].
    ii; subst.
    exploit MemoryMerge.add_remove; [eapply MEM | eapply MEM0 | eauto].
    ii; subst.
    left; destruct lc0; eauto.
  } 
  {
    (* reserve cancel not same message *)
    exploit MemoryReorder.add_remove.
    instantiate (4 := loc0); instantiate (3 := to0); instantiate (2 := loc1); instantiate (1 := to1).
    intro. inv H; ss. destruct o; ss.
    eapply PROMISES. eapply PROMISES0. ii.
    exploit MemoryReorder.add_remove.
    instantiate (4 := loc0); instantiate (3 := to0); instantiate (2 := loc1); instantiate (1 := to1).
    intro. inv H; ss. destruct o; ss.
    eapply MEM. eapply MEM0. ii.
    clear o; des.
    rename mem1'0 into promise1'0.
    right.
    do 2 eexists.
    split.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    ii; ss.
  }
Qed.

Lemma reorder_promise_add_cancel
      lc0 mem0 loc0 from0 to0 lc1 mem1 msg
      loc1 from1 to1 lc2 mem2
      (PROMISE: Local.promise_step lc0 mem0 loc0 from0 to0 msg lc1 mem1 Memory.op_kind_add)
      (CCL: Local.promise_step lc1 mem1 loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_cancel):
  (lc0 = lc2 /\ mem0 = mem2 /\ msg = Message.reserve) \/
  (exists lc' mem',
      Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc' mem' Memory.op_kind_cancel /\
      Local.promise_step lc' mem' loc0 from0 to0 msg lc2 mem2 Memory.op_kind_add).
Proof.
  destruct msg; ss.
  {
    inv PROMISE; inv CCL.
    inv PROMISE0; inv PROMISE; ss.
    destruct (loc_ts_eq_dec (loc0, to0) (loc1, to1)); ss.
    {
      des; subst.
      eapply Memory.add_get0 in PROMISES; eauto; des.
      eapply Memory.remove_get0 in PROMISES0; eauto; des.
      rewrite GET0 in GET1; inv GET1.
    }
    {
      exploit MemoryReorder.add_remove.
      instantiate (4 := loc0); instantiate (3 := to0); instantiate (2 := loc1); instantiate (1 := to1).
      intro. inv H; ss. destruct o; ss.
      eapply PROMISES. eapply PROMISES0. ii.
      exploit MemoryReorder.add_remove.
      instantiate (4 := loc0); instantiate (3 := to0); instantiate (2 := loc1); instantiate (1 := to1).
      intro. inv H; ss. destruct o; ss.
      eapply MEM. eapply MEM0. ii.
      destruct x0 as (promise1' & REMOVE1 & ADD1).
      destruct x1 as (mem1' & REMOVE2 & ADD2).
      right.
      do 2 eexists.
      split; [econstructor; econstructor; eauto | econstructor; econstructor; eauto].
      ii.
      inv MSG.
      assert(Memory.get loc0 to' mem0 = Some (to0, msg')).
      {
        erewrite Memory.remove_o in GET; eauto.
        destruct (loc_ts_eq_dec (loc0, to') (loc1, to1)); ss.
      }
      eapply ATTACH in H; eauto.
      eapply Memory.cancel_closed_opt_view; eauto.
      inv CLOSED; eauto.
    }
  }
  {  
    eapply reorder_reserve_cancel in PROMISE; eauto.
    des; subst; eauto.
  }
Qed.

Lemma reorder_promise_split_cancel
      lc0 mem0 loc0 from0 to0 lc1 mem1 msg ts3 msg3
      loc1 from1 to1 lc2 mem2
      (PROMISE: Local.promise_step lc0 mem0 loc0 from0 to0 msg lc1 mem1 (Memory.op_kind_split ts3 msg3))
      (CCL: Local.promise_step lc1 mem1 loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_cancel):
  exists lc' mem',
      Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc' mem' Memory.op_kind_cancel /\
      Local.promise_step lc' mem' loc0 from0 to0 msg lc2 mem2 (Memory.op_kind_split ts3 msg3).
Proof.
  inv PROMISE; inv CCL.
  inv PROMISE0; inv PROMISE; ss.
  destruct(classic ((loc0, to0) <> (loc1, to1))).
  {
    destruct(classic ((loc0, ts3) <> (loc1, to1))).
    {
      exploit MemoryReorder.split_remove; [eapply H | eapply H0 | eauto..]. ii.
      des; subst.
      exploit MemoryReorder.split_remove; [eapply H | eapply H0 | eapply PROMISES | eapply PROMISES0 | eauto..]. ii.
      des; subst.
      do 2 eexists.
      split; [econstructor; eauto | econstructor; econstructor; eauto].
      eapply Memory.cancel_closed_opt_view; eauto.
      inv CLOSED; eauto.
    }
    {
      exploit H0; ii; ss.
      inv H1.
      eapply Memory.split_get0 in PROMISES; des.
      eapply Memory.remove_get0 in PROMISES0; des; ss; subst.
      rewrite GET2 in GET3; inv GET3.
    }
  }
  {
    exploit H; ii; ss.
    inv H0.
    eapply Memory.split_get0 in PROMISES; des.
    eapply Memory.remove_get0 in PROMISES0; des.
    subst; rewrite GET1 in GET3; inv GET3.
  }
Qed.

Lemma reorder_promise_lower_cancel
      lc0 mem0 loc0 from0 to0 lc1 mem1 msg msg'
      loc1 from1 to1 lc2 mem2
      (PROMISE: Local.promise_step lc0 mem0 loc0 from0 to0 msg lc1 mem1 (Memory.op_kind_lower msg'))
      (CCL: Local.promise_step lc1 mem1 loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_cancel):
  exists lc' mem',
      Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc' mem' Memory.op_kind_cancel /\
      Local.promise_step lc' mem' loc0 from0 to0 msg lc2 mem2 (Memory.op_kind_lower msg').
Proof.
  inv PROMISE; inv CCL.
  inv PROMISE0; inv PROMISE; ss.
  destruct(classic ((loc0, to0) <> (loc1, to1))).
  {
    exploit MemoryReorder.lower_remove; [eapply H | eapply PROMISES | eapply PROMISES0 | eauto..]. ii.
    exploit MemoryReorder.lower_remove; [eapply H | eapply MEM | eapply MEM0 | eauto..]. ii.
    des.
    do 2 eexists.
    split; [econstructor; eauto | econstructor; eauto].
    eapply Memory.cancel_closed_message; eauto.
  }
  {
    exploit H; ii; ss.
    inv H0.
    eapply Memory.lower_get0 in PROMISES; des; subst.
    eapply Memory.remove_get0 in PROMISES0; des; subst.
    rewrite GET0 in GET1; inv GET1.
    inv MSG_LE.
  }
Qed.

Lemma reorder_promise_cancel_cancel
      lc0 mem0 loc0 from0 to0 lc1 mem1 
      loc1 from1 to1 lc2 mem2
      (PROMISE: Local.promise_step lc0 mem0 loc0 from0 to0 Message.reserve lc1 mem1 Memory.op_kind_cancel)
      (CCL: Local.promise_step lc1 mem1 loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_cancel):
  exists lc' mem',
      Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc' mem' Memory.op_kind_cancel /\
      Local.promise_step lc' mem' loc0 from0 to0 Message.reserve lc2 mem2 Memory.op_kind_cancel.
Proof.
  inv PROMISE; inv CCL.
  inv PROMISE0; inv PROMISE; ss.
  exploit MemoryReorder.remove_remove; [eapply PROMISES | eapply PROMISES0 | eauto..]; ii.
  des.
  exploit MemoryReorder.remove_remove; [eapply MEM | eapply MEM0 | eauto..]; ii.
  des.
  do 2 eexists.
  split.
  econstructor; eauto.
  econstructor; eauto.
Qed.
  
Lemma reorder_promise_cancel
      lc0 mem0 loc0 from0 to0 msg lc1 mem1 kind
      loc1 from1 to1 lc2 mem2
      (PROMISE: Local.promise_step lc0 mem0 loc0 from0 to0 msg lc1 mem1 kind)
      (CCL: Local.promise_step lc1 mem1 loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_cancel):
  (lc0 = lc2 /\ mem0 = mem2 /\ kind = Memory.op_kind_add /\ msg = Message.reserve) \/
  exists lc' mem',
    Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc' mem' Memory.op_kind_cancel /\
    Local.promise_step lc' mem' loc0 from0 to0 msg lc2 mem2 kind.
Proof.
  destruct kind; ss.
  - (* promise add / cancel *)  
    eapply reorder_promise_add_cancel in PROMISE; eauto.
    des; subst; eauto.
  - (* promise split / cancel *)
    right; eapply reorder_promise_split_cancel; eauto.
  - (* promise lower / cancel *)
    right; eapply reorder_promise_lower_cancel; eauto.
  - (* promise cancel / cancel *)
    right.
    assert(msg = Message.reserve).
    {
      clear - PROMISE.
      inv PROMISE.
      inv PROMISE0; eauto.
    }
    subst.
    eapply reorder_promise_cancel_cancel; eauto.
Qed.
  
Lemma reorder_reserve_step_cancel_step
      lang lo (e e' e'': Thread.t lang)
      (RSV: Thread.reserve_step lo e e')
      (CCL: Thread.cancel_step lo e' e''):
  e = e'' \/
  (exists e0, Thread.cancel_step lo e e0 /\ Thread.reserve_step lo e0 e'').
Proof.
  inv RSV; inv CCL.
  inv STEP; inv STEP0; ss.
  inv LOCAL; inv LOCAL0; ss.
  inv PROMISE; inv PROMISE0; ss.
  destruct (loc_ts_eq_dec (loc, to) (loc0, to0)); ss.
  {
    (* reserve cancel same message *)
    des; subst.
    dup PROMISES.
    eapply Memory.add_get0 in PROMISES; des.
    dup PROMISES0. 
    eapply Memory.remove_get0 in PROMISES0; des.
    rewrite GET0 in GET1; inv GET1.
    exploit MemoryMerge.add_remove; [eapply PROMISES1 | eapply PROMISES2 | eauto].
    ii; subst.
    exploit MemoryMerge.add_remove; [eapply MEM | eapply MEM0 | eauto].
    ii; subst.
    left; destruct lc1; eauto.
  } 
  {
    (* reserve cancel not same message *)
    exploit MemoryReorder.add_remove.
    instantiate (4 := loc); instantiate (3 := to); instantiate (2 := loc0); instantiate (1 := to0).
    intro. inv H; ss. destruct o; ss.
    eapply PROMISES. eapply PROMISES0. ii.
    exploit MemoryReorder.add_remove.
    instantiate (4 := loc); instantiate (3 := to); instantiate (2 := loc0); instantiate (1 := to0).
    intro. inv H; ss. destruct o; ss.
    eapply MEM. eapply MEM0. ii.
    clear o; des.
    rename mem1'0 into promise1'0.
    right.
    eexists.
    split.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto; ss.
    econstructor; eauto.
    ii; ss.
  }
Qed.
  
Lemma reorder_reserve_steps_cancel_steps:
  forall n lang lo (e e' e'': Thread.t lang)
    (RSV: Thread.reserve_step lo e e')
    (CCLs: rtcn (Thread.cancel_step lo) n e' e''),
  exists e0,
    rtc (Thread.cancel_step lo) e e0 /\ rtc (Thread.reserve_step lo) e0 e''.
Proof.
  induction n; ii.
  - inv CCLs.
    eexists; split; eauto.
  - inv CCLs.
    eapply reorder_reserve_step_cancel_step in A12; eauto.
    des; subst.
    {
      exists e''.
      eapply rtcn_rtc in A23; split; eauto.
    }
    {
      eapply IHn in A23; [idtac | eauto..].
      des.
      eexists.
      split; [|eapply A1].
      eapply Relation_Operators.rt1n_trans; eauto.
    }
Qed.

Lemma reorder_not_tau_step_cancel_step
      lang lo (e e' e'': Thread.t lang) te
      (STEP: Thread.program_step te lo e e')
      (CCL: Thread.cancel_step lo e' e''):
  exists e0,
    Thread.cancel_step lo e e0 /\
    Thread.program_step te lo e0 e''.
Proof.
  inv STEP; inv CCL. inv STEP.
  inv LOCAL.
  - (* silent *)
    eexists.
    split; [econstructor; econstructor; eauto | eauto].
  - (* read *)
    exploit reorder_read_cancel; eauto.
    ii; des.
    eexists.
    split; [econstructor; econstructor; eauto | econstructor; eauto].
  - (* write *)
    exploit reorder_write_cancel; eauto.
    ii; des.
    eexists.
    split; [econstructor; econstructor; eauto | econstructor; eauto].
  - (* update *)
    exploit reorder_write_cancel; eauto.
    ii; des.
    exploit reorder_read_cancel; eauto.
    ii; des.
    eexists.
    split; [econstructor; econstructor; eauto | econstructor; eauto].
  - (* fence *)
    exploit reorder_fence_cancel; eauto.
    ii; des.
    eexists.
    split; [econstructor; econstructor; eauto | econstructor; eauto].
  - (* output *)
    exploit reorder_fence_cancel; eauto.
    ii; des.
    eexists.
    split; [econstructor; econstructor; eauto | econstructor; eauto].
Qed.

Lemma reorder_not_rsv_ccl_scfence_step_cancel_steps:
  forall n lang lo (e e' e'': Thread.t lang) pf te
    (STEP: Thread.step lo pf te e e')
    (NO_OUT: ThreadEvent.get_machine_event te = MachineEvent.silent)
    (NO_RSV_CCL_SCFENCE: Thread.not_rsv_ccl_scfence te)
    (CCLs: rtcn (Thread.cancel_step lo) n e' e''),
  exists e0,
    rtc (Thread.cancel_step lo) e e0 /\
    Thread.step lo pf te e0 e''.
Proof.
  induction n; ii.
  - inv CCLs; eauto.
  - inv CCLs.
    inv STEP.
    {
      (* promise step *)    
      inv STEP0; inv A12; ss. 
      inv STEP.
      exploit reorder_promise_cancel; [eapply LOCAL | eapply LOCAL0 | eauto..]; ii.
      des; subst; ss.
      eapply IHn with (te := ThreadEvent.promise loc from to msg kind)
                      (e := (Thread.mk lang st lc' sc1 mem')) in A23; eauto.
      des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans; [| eapply A23].
      econstructor; eauto.
      econstructor; eauto.
      eauto.
      econstructor; eauto.
      econstructor; eauto.
    }
    {
      (* program step *)
      eapply reorder_not_tau_step_cancel_step in STEP0; eauto.
      des. 
      eapply IHn with (e := e0) in A23; eauto.
      des.
      exists e1. split; eauto.
    }
Qed.
