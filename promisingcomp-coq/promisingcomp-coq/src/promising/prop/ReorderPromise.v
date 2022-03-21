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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import MemoryReorder.
Require Import PromiseConsistent.
Require Import FulfillStep.

Set Implicit Arguments.


Lemma reorder_promise_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1 kind1
      loc2 to2 val2 released2 ord2 lo
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2 lo)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: (loc1, to1) <> (loc2, to2)):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1' lo>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get_inv_diff; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_promise_promise_lower_None
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 (Message.concrete val2 None) lc2 mem2 kind2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (KIND2: Memory.op_kind_is_lower kind2 = true):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ Message.le (Message.concrete val2 None) msg1 /\ kind2 = Memory.op_kind_lower msg1 /\
   exists kind1', <<STEP: Local.promise_step lc0 mem0 loc1 from1 to1 (Message.concrete val2 None) lc2 mem2 kind1'>>) \/
  (exists lc1' mem1' from2' kind1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2' to2 (Message.concrete val2 None) lc1' mem1' kind2>> /\
       <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 msg1 lc2 mem2 kind1'>>).
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE0; inv KIND2. des. subst.
  inv PROMISE; ss.
  - exploit MemoryReorder.add_lower; try exact PROMISES0; try exact PROMISES; eauto. i. des.
    + subst.
      exploit MemoryReorder.add_lower; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
      left. esplits; ss.
      * inv MEM. inv LOWER. ss.
      * econs; eauto.
    + exploit MemoryReorder.add_lower; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
      right. esplits; eauto; econs; eauto.
      * econs; eauto.
        i. revert GET.
        erewrite Memory.lower_o; eauto. condtac; ss.
        { i. des. subst. inv GET.
          exploit Memory.lower_get0; try exact MEM. i. des.
          revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv LOWER. timetac. }
        { i. exploit Memory.lower_get1; try exact GET; eauto. }
      * eapply Memory.lower_closed_message; eauto.
  - des. subst.
    destruct (classic ((loc1, ts3) = (loc2, to2))).
    { inv H.
      exploit MemoryReorder.split_lower_same; try exact PROMISES0; try exact PROMISES; eauto. i. des.
      exploit MemoryReorder.split_lower_same; try exact MEM1; try exact MEM; eauto. i. des.
      subst. right. esplits; eauto; econs; eauto.
      { clarify. econs 2; eauto. }
      eapply Memory.lower_closed_message; eauto.
    }
    { exploit MemoryReorder.split_lower_diff; try exact PROMISES0; try exact PROMISES; eauto. i. des.
      - subst. inv x3.
        exploit MemoryReorder.split_lower_diff; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
        left. esplits; eauto.
        { inv MEM. inv LOWER. ss. }
        { econs; eauto. econs 2; eauto. }
      - exploit MemoryReorder.split_lower_diff; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
        right. esplits; eauto; econs; eauto.
        { econs 2; eauto. }
        eapply Memory.lower_closed_message; eauto.
    }
  - des. subst.
    exploit MemoryReorder.lower_lower; try exact PROMISES0; try exact PROMISES; eauto. i. des.
    + subst.
      exploit MemoryReorder.lower_lower; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
      left. esplits; eauto. inv MEM. inv LOWER. ss.
    + exploit MemoryReorder.lower_lower; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
      right. esplits; eauto; econs; eauto.
      eapply Memory.lower_closed_message; cycle 1; eauto.
Qed.

Lemma reorder_promise_promise_cancel
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (KIND2: Memory.op_kind_is_cancel kind2 = true):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg1 = Message.reserve /\ kind1 = Memory.op_kind_add /\
   lc0 = lc2 /\ mem0 = mem2) \/
  (exists lc1' mem1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2>> /\
      <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 msg1 lc2 mem2 kind1>>).
Proof.
  inv STEP1. inv STEP2. ss. inv PROMISE0; inv KIND2. inv PROMISE; ss.
  - destruct (classic ((loc1, to1) = (loc2, to2))).
    + inv H.
      exploit MemoryReorder.add_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.add_remove_same; try exact MEM0; eauto. i. des. subst.
      left. splits; auto. destruct lc0; ss.
    + exploit MemoryReorder.add_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_remove; try exact MEM0; eauto. i. des.
      right. esplits; eauto. econs; eauto.
      * econs; eauto.
        i. revert GET.
        erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      * eapply Memory.cancel_closed_message; eauto.
  - des. destruct (classic ((loc1, ts3) = (loc2, to2))).
    + clarify.
      exploit MemoryReorder.split_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.split_remove_same; try exact MEM1; eauto. i. des. subst. ss.
    + destruct (classic ((loc1, to1) = (loc2, to2))).
      { des. inv H0.
        exploit Memory.split_get0; try exact MEM0. i. des.
        exploit Memory.remove_get0; try exact MEM. i. des. congr. }
      exploit MemoryReorder.split_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.split_remove; try exact MEM0; eauto. i. des.
      right. esplits; eauto. econs; eauto.
      { subst. econs 2; eauto. }
      eapply Memory.cancel_closed_message; eauto.
  - des. subst.
    destruct (classic ((loc1, to1) = (loc2, to2))).
    + inv H.
      exploit MemoryReorder.lower_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.lower_remove_same; try exact MEM1; eauto. i. des. subst.
      exploit Memory.lower_get0; try exact MEM0. i. des. inv MSG_LE.
    + exploit MemoryReorder.lower_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_remove; try exact MEM0; eauto. i. des.
      right. esplits; eauto. econs; eauto.
      eapply Memory.cancel_closed_message; eauto.
  - exploit MemoryReorder.remove_remove; try apply PROMISES0; eauto. i. des.
    exploit MemoryReorder.remove_remove; try apply MEM0; eauto. i. des.
    right. esplits; eauto.
Qed.

Lemma reorder_promise_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 released2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 (Message.concrete val2 released2) lc2 mem2 kind2)
      (REL_CLOSED: forall promises1' mem1' kind1'
                     (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 (Message.concrete val2 released2) promises1' mem1' kind1'),
          Memory.closed_opt_view released2 mem1')
      (LOCAL0: Local.wf lc0 mem0)
      (CLOSED0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (LOCTS1: forall to1' msg1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2 /\
          (forall msg2', kind2 <> Memory.op_kind_split to1' msg2'))
      (LOCTS2: forall val released
                 (LOC: loc1 = loc2)
                 (KIND1: kind1 = Memory.op_kind_add)
                 (KIND2: kind2 = Memory.op_kind_add)
                 (MSG1: msg1 = Message.concrete val released),
               Time.lt to2 to1):
  exists lc1' mem1' kind2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 (Message.concrete val2 released2) lc1' mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                (exists from1' kind1',
                    (loc1, to1) <> (loc2, to2) /\
                    (forall to1' msg1'
                       (LOC: loc1 = loc2)
                       (KIND: kind1' = Memory.op_kind_split to1' msg1'),
                        to1' <> to2 /\
                        (forall msg2', kind2 <> Memory.op_kind_split to1' msg2')) /\
                    Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1' /\
                    (forall val released, kind2 = Memory.op_kind_lower (Message.concrete val released) ->
                                     exists val' released, kind2' = Memory.op_kind_lower (Message.concrete val' released))))>> /\
    <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE; ss.
  { inv PROMISE0; ss.
    - (* add/add *)
      exploit MemoryReorder.add_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 (Message.concrete val2 released2)
                            mem1' mem1'0 Memory.op_kind_add).
        { i. econs; eauto. }
        econs; eauto; try congr.
        i. exploit Memory.add_get1; try exact MEM; eauto.
      + right. esplits; eauto. econs; eauto.
        * econs; eauto. i. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; eauto.
          i. des. inv GET.
          exploit LOCTS2; eauto. i.
          inv ADD0. inv ADD. rewrite x in TO. timetac.
        * eapply Memory.add_closed_message; cycle 1; eauto.
      + auto.
    - (* add/split *)
      exploit MemoryReorder.add_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst. inv RESERVE.
        exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 (Message.concrete val'0 released'0)
                              mem1' mem1'0 Memory.op_kind_add).
          { i. econs; eauto. }
          econs; eauto; try congr.
          i. exploit Memory.add_get1; try exact GET; try exact MEM. i.
          exploit Memory.add_get0; try exact MEM. i. des.
          clear GET GET0.
          exploit Memory.get_ts; try exact x4. i. des.
          { subst. inv ADD0. inv ADD. inv TO. }
          exploit Memory.get_ts; try exact GET1. i. des.
          { subst. inv ADD3. inv ADD. inv TO. }
          exploit Memory.get_disjoint; [exact x4|exact GET1|..]. i. des.
          { subst. inv ADD0. inv ADD. timetac. }
          destruct (TimeFacts.le_lt_dec to' ts3).
          { apply (x7 to'); econs; ss; try refl.
            inv ADD0. inv ADD. etrans; eauto. }
          { apply (x7 ts3); econs; ss; try refl.
            - inv ADD3. inv ADD. ss.
            - econs. ss. }
        * right. esplits; ii; ss; eauto.
          { ii. inv H. inv ADD3. inv ADD. timetac. }
          { econs.
            - econs; eauto.
              i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss; eauto. i. des. inv GET.
              inv ADD0. inv ADD. inv ADD3. inv ADD. rewrite TO in TO0. timetac.
            - eapply Memory.split_closed_message; eauto.
            - auto. }
        * auto.
      + inv RESERVE.
        exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs.
          { econs 2; eauto. }
          { econs. eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.split_get0; try exact MEM0; eauto. i. des.
            revert GET. erewrite Memory.add_o; eauto. condtac; ss. des; congr. }
          { econs; eauto.
            - econs; eauto.
              i. revert GET.
              erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
              + i. des. inv GET.
                exploit Memory.split_get0; try exact MEM0. i. des.
                revert GET0. erewrite Memory.add_o; eauto. condtac; ss; eauto.
                i. des. inv GET0.
                inv MEM0. inv SPLIT. rewrite TS12 in TS23. timetac.
              + guardH o. i. des. inv GET.
                exploit Memory.split_get0; try exact SPLIT0. i. des.
                exploit Memory.add_get0; try exact ADD0. i. des.
                exploit Memory.add_get1; try exact GET1; eauto. i.
                clear GET GET0 GET1 GET2 GET3.
                exploit Memory.get_ts; try exact GET4. i. des.
                { subst. inv SPLIT0. inv SPLIT. inv TS12. }
                exploit Memory.get_ts; try exact x0. i. des.
                { subst. inv ADD0. inv ADD. inv TO. }
                exploit Memory.get_disjoint; [exact GET4|exact x0|..]. i. des.
                { subst. exploit Memory.split_get0; try exact SPLIT0. i. des.
                  inv ADD0. inv ADD.
                  hexploit DISJOINT; try eapply GET1. i.
                  apply (H to1); econs; ss; try refl. }
                apply (x3 to1); econs; ss; try refl.
            - eapply Memory.split_closed_message; eauto. }
        * auto.
    - (* add/lower *)
      des. subst.
      exploit MemoryReorder.add_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto.
        * left. auto.
        * auto.
      + exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto.
          econs. eapply REL_CLOSED; eauto.
        * right. esplits; eauto. econs; eauto.
          { econs; eauto.
            i. revert GET.
            erewrite Memory.lower_o; eauto. condtac; ss; eauto.
            i. des. inv GET.
            exploit Memory.lower_get0; try exact LOWER0. i. des. eauto. }
          { eapply Memory.lower_closed_message; eauto. }
        * auto.
  }
  { des. subst. inv PROMISE0; ss.
    - (* split/add *)
      exploit MemoryReorder.split_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.split_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 (Message.concrete val2 released2)
                            mem1' mem1'0 Memory.op_kind_add).
        { i. econs; eauto. }
        econs; eauto; try congr.
        i. exploit Memory.split_get1; try exact GET; eauto. i. des.
        dup GET2. revert GET2.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
        * i. des. inv GET2.
          exploit Memory.split_get0; try exact MEM. i. des.
          rewrite GET in *. ss.
        * guardH o. i. des. inv GET2.
          exploit Memory.split_get0; try exact MEM. i. des.
          rewrite GET in *. inv GET2. eauto.
        * i. rewrite GET in *. inv GET2. eauto.
      + right. esplits; eauto. econs; eauto.
        { econs 2; eauto. }
        eapply Memory.add_closed_message; eauto.
      + auto.
    - (* split/split *)
      des. inv RESERVE.
      exploit MemoryReorder.split_split; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. eapply LOCTS1; eauto. }
      i. des. 
      + subst. exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. inv SPLIT2. inv SPLIT. timetac. }
        i. des; [|congr].
        esplits.
        * econs.
          { econs 2; eauto. }
          { econs. eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; ii; ss; eauto.
          { ii. inv H. inv SPLIT2. inv SPLIT. timetac. }
          { econs; eauto.
            { econs 2; eauto. }
            eapply Memory.split_closed_message; cycle 1; eauto. }
        * congr.
      + exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. eapply LOCTS1; eauto. }
        i. des; [congr|].
        esplits.
        * econs.
          { econs 2; eauto. }
          { econs. eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
            revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
            guardH o0. des; congr. }
          { econs; eauto.
            { econs 2; eauto. }
            eapply Memory.split_closed_message; cycle 1; eauto. }
        * auto.
    - (* split/lower *)
      des. subst.
      exploit MemoryReorder.split_lower_diff; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. exploit LOCTS1; eauto. i. des. congr. }
      i. des.
      + subst. inv x3.
        exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS1; eauto. i. des. congr. }
        i. des; [|congr].
        esplits.
        * econs.
          { econs 2; eauto. }
          { econs. eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * left. auto.
        * congr.
      + subst. exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS1; eauto. i. des. congr. }
        i. des; [congr|].
        esplits.
        * econs; eauto. econs; eauto.
        * right. esplits; eauto. econs; eauto.
          { econs; eauto. }
          eapply Memory.lower_closed_message; eauto.
        * congr.
  }
  { des. subst. inv PROMISE0; ss.
    - (* lower/add *)
      exploit MemoryReorder.lower_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 (Message.concrete val2 released2)
                            mem1' mem1'0 Memory.op_kind_add).
        { i. econs; eauto. }
        econs; eauto; try congr.
        i. exploit Memory.lower_get1; try exact GET; eauto. i. des. eauto.
      + right. esplits; eauto. econs; eauto.
        eapply Memory.add_closed_message; eauto.
      + auto.
    - (* lower/split *)
      des. inv RESERVE.
      exploit MemoryReorder.lower_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_split; try exact MEM; try exact MEM0; eauto. i. des.
      unguardH FROM1. des.
      + inv FROM1. unguardH FROM0. des; [|congr]. inv FROM0.
        esplits.
        * econs.
          { econs 2; eauto. }
          { econs. eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; ii; ss; eauto.
          { ii. inv H. inv SPLIT1. inv SPLIT. timetac. }
          { econs; eauto. eapply Memory.split_closed_message; eauto. }
        * congr.
      + inv FROM2. unguardH FROM0. des; [congr|]. inv FROM2.
        esplits.
        * econs.
          { econs 2; eauto. }
          { econs. eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.lower_get0; try exact MEM; eauto.
            exploit Memory.split_get0; try exact SPLIT0; eauto. i. des. congr. }
          { econs; eauto. eapply Memory.split_closed_message; eauto. }
        * auto.
    - (* lower/lower *)
      des. subst.
      exploit MemoryReorder.lower_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto.
        * left. auto.
        * congr.
      + exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto. econs; eauto.
        * right. esplits; eauto. econs; eauto.
          eapply Memory.lower_closed_message; cycle 1; eauto.
        * auto.
  }
Qed.

Lemma reorder_promise_fulfill
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS1: (loc1, to1) <> (loc2, to2))
      (LOCTS2: forall to1' msg1'
                 (LOC: loc1 = loc2)
                 (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE; ss.
  - exploit MemoryReorder.add_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
  - exploit MemoryReorder.split_remove; try exact PROMISES; try exact REMOVE; eauto.
    { ii. inv H. eapply LOCTS2; eauto. }
    i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss; eauto.
  - des. subst.
    exploit MemoryReorder.lower_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; eauto.
  - exploit MemoryReorder.remove_remove; try exact PROMISES; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
Qed.

Lemma promise_step_nonsynch_loc_inv
      lc1 mem1 loc from to msg lc2 mem2 kind l
      (WF1: Local.wf lc1 mem1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (NONPF: Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg)
      (NONSYNCH: Memory.nonsynch_loc l (Local.promises lc2)):
  Memory.nonsynch_loc l (Local.promises lc1).
Proof.
  guardH NONPF. 
  ii.
  inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.split_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.lower_o; try exact PROMISES; eauto.
    instantiate (1 := t). instantiate (1 := l). condtac; ss.
    + i. des. subst. exploit NONSYNCH; eauto.
      destruct msg; destruct msg0; ss.
      * i. subst. unguard. des; ss.
      * exploit Memory.lower_get0; try exact PROMISES. i. des.
        rewrite GET in GET0. inv GET0.
        inv MEM. inv LOWER. inv MSG_LE0.
    + rewrite GET. i. exploit NONSYNCH; eauto.
  - exploit Memory.remove_get1; try exact GET; eauto. i. des.
    + subst. exploit Memory.remove_get0; try exact PROMISES. i. des.
      rewrite GET0 in GET. inv GET. ss.
    + exploit NONSYNCH; eauto.
Qed.

Lemma promise_step_nonsynch_inv
      lc1 mem1 loc from to msg lc2 mem2 kind
      (WF1: Local.wf lc1 mem1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (NONPF: Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg)
      (NONSYNCH: Memory.nonsynch (Local.promises lc2)):
  Memory.nonsynch (Local.promises lc1).
Proof.
  guardH NONPF. 
  ii.
  inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.split_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.lower_o; try exact PROMISES; eauto.
    instantiate (1 := t). instantiate (1 := loc0). condtac; ss.
    + i. des. subst. exploit NONSYNCH; eauto.
      destruct msg; destruct msg0; ss.
      * i. subst. unguard. des; ss.
      * exploit Memory.lower_get0; try exact PROMISES. i. des.
        rewrite GET in GET0. inv GET0.
        inv MEM. inv LOWER. inv MSG_LE0.
    + rewrite GET. i. exploit NONSYNCH; eauto.
  - exploit Memory.remove_get1; try exact GET; eauto. i. des.
    + subst. exploit Memory.remove_get0; try exact PROMISES. i. des.
      rewrite GET0 in GET. inv GET. ss.
    + exploit NONSYNCH; eauto.
Qed.

Lemma reorder_promise_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2 lo
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2 lo)
      (NONPF: Memory.op_kind_is_lower_concrete kind1 = false \/ ~ Message.is_released_none msg1)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (LOCTS1: forall to1' msg1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2 /\
          (forall msg2', kind2 <> Memory.op_kind_split to1' msg2'))
      (LOCTS2: forall val released
                 (LOC: loc1 = loc2)
                 (KIND1: kind1 = Memory.op_kind_add)
                 (KIND2: kind2 = Memory.op_kind_add)
                 (MSG1: msg1 = Message.concrete val released),
               Time.lt to2 to1):
  exists kind2' lc1' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2' lo>> /\
    <<STEP2: __guard__
               ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                ((loc1, to1) <> (loc2, to2) /\
                 exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>> /\
    <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>.
Proof.
  guardH NONPF. 
  exploit Local.promise_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto; try by viewtac. 
  i. des. 
  exploit reorder_promise_promise; try exact STEP1; eauto.
  { i. subst.
    exploit Memory.promise_op; eauto. i.
    eapply TViewFacts.op_closed_released; try exact x0; eauto.
    inv STEP1. apply LOCAL0.
  }
  i. des.
  unguardH STEP5. des.
  - inv STEP5.
    exploit promise_fulfill_write; try exact STEP4; eauto.
    { i. hexploit ORD; eauto. i.
      eapply promise_step_nonsynch_loc_inv; try exact STEP1; eauto.
    }
    { inv STEP1. ss. }
    instantiate (1 := lo). inv STEP2; eauto.
    i. esplits; eauto. left; eauto.
  - exploit Local.promise_step_future; try exact STEP4; eauto. i. des.
    exploit reorder_promise_fulfill; try exact STEP6; eauto.
    { i. eapply STEP6; eauto. }
    i. des. 
    exploit fulfill_step_future; try exact STEP7; try exact WF0; eauto; try by viewtac. i. des.
    exploit promise_fulfill_write; try exact STEP4; eauto; try by viewtac.
    { i. hexploit ORD; eauto. i.
      eapply promise_step_nonsynch_loc_inv; try exact STEP1; eauto.
    }
    { subst. inv STEP1. ss. }
    instantiate (1 := lo). inv STEP2; eauto.
    i. esplits; eauto.
    right. esplits; eauto.
Qed.

Lemma reorder_promise_write'
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2 lo
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2 lo)
      (NONPF: Memory.op_kind_is_lower_concrete kind1 = false \/ ~ Message.is_released_none msg1)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false):
  (loc1 = loc2 /\ Time.lt to1 to2) \/
  (exists kind2' lc1' mem1',
     <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2' lo>> /\
     <<STEP2: __guard__
                ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                 ((loc1, to1) <> (loc2, to2) /\
                  exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>> /\
     <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>).
Proof.
  guardH NONPF.
  destruct (classic (loc1 = loc2 /\ Time.lt to1 to2)); auto.
  right. eapply reorder_promise_write; eauto. i. subst. splits.
  - ii. subst. apply H. splits; auto.
    inv STEP1. inv PROMISE. inv MEM. inv SPLIT. auto.
  - ii. subst. apply H. splits; auto.
    inv STEP2. inv WRITE. inv PROMISE. exploit Memory.split_get0; eauto. i. des.
    inv STEP1. inv PROMISE. revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + i. des. inv GET0. inv MEM1. inv SPLIT. timetac.
    + guardH o. i. des. inv GET0. inv MEM. inv SPLIT. auto.
    + guardH o. des; congr.
  - i. subst. destruct (TimeFacts.le_lt_dec to2 to1); cycle 1.
    { exfalso. apply H; eauto. }
    inv l; ss. inv H0. exfalso.
    inv STEP1. inv PROMISE. inv STEP2. inv WRITE. inv PROMISE. ss.
    exploit Memory.add_get0; try exact MEM. i. des.
    exploit Memory.add_get0; try exact MEM1. i. des. congr.
Qed.

Hint Constructors Thread.program_step.
Hint Constructors Thread.step.

Lemma reorder_promise_fence
      lc mem loc from to msg lc' mem' kind sc ordr ordw lc'' sc'
      (LOCAL_WF: Local.wf lc mem)
      (PROMISES: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (FENCE: Local.fence_step lc' sc ordr ordw lc'' sc')
      (NOSC: ordw <> Ordering.seqcst)
      (NOPF: Memory.op_kind_is_lower_concrete kind = false \/ ~Message.is_released_none msg):
  exists lc0,
    Local.fence_step lc sc ordr ordw lc0 sc' /\
    Local.promise_step lc0 mem loc from to msg lc'' mem' kind.
Proof.
  dup PROMISES.
  dup FENCE.
  inv PROMISES.
  inv FENCE.
  destruct lc; ss.
  eexists.
  split.
  - econstructor; ss.
    intros ORD; eapply RELEASE in ORD.
    eapply promise_step_nonsynch_inv in PROMISES0; eauto.
  - econstructor; ss. eauto.
Qed.
