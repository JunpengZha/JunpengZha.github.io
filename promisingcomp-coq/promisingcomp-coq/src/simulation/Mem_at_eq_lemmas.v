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

Require Import LocalSim.
Require Import MsgMapping.
Require Import MemoryProps.

Lemma Memory_add_disj_loc_stable
      mem1 mem2 loc from to msg loc0
      (ADD: Memory.add mem1 loc from to msg mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv ADD. rewrite Loc_add_neq; eauto.
Qed.

Lemma Memory_split_disj_loc_stable
      mem1 mem2 loc from to ts msg1 msg2 loc0
      (SPLIT: Memory.split mem1 loc from to ts msg1 msg2 mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv SPLIT. rewrite Loc_add_neq; eauto.
Qed.

Lemma Memory_remove_disj_loc_stable
      mem1 mem2 loc from to msg loc0
      (REMOVE: Memory.remove mem1 loc from to msg mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv REMOVE. rewrite Loc_add_neq; eauto.
Qed.

Lemma Memory_lower_disj_loc_stable
      mem1 mem2 loc from to msg1 msg2 loc0
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv LOWER. rewrite Loc_add_neq; eauto.
Qed.  
  
Lemma Memory_write_disj_loc_stable
      promises1 mem1 loc from to val released promises2 mem2 kind loc0
      (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind)
      (DISJ_LOC: loc <> loc0):
  promises1 loc0 = promises2 loc0 /\ mem1 loc0 = mem2 loc0. 
Proof.
  inv WRITE. inv PROMISE.
  - (* add *)
    split.
    {
      exploit Memory_remove_disj_loc_stable; eauto. ii.
      exploit Memory_add_disj_loc_stable; [eapply PROMISES | eauto..]. ii.
      rewrite x1. rewrite <- x0. eauto.
    }
    {
      eapply Memory_add_disj_loc_stable; eauto.
    }
  - (* split *)
    des. subst. inv RESERVE.
    split.
    {
      exploit Memory_remove_disj_loc_stable; eauto. ii.
      exploit Memory_split_disj_loc_stable; [eapply PROMISES | eauto..]. ii.
      rewrite x1. rewrite <- x0. eauto.
    }
    {
      eapply Memory_split_disj_loc_stable; eauto.
    }
  - (* lower *)
    des. subst.
    split.
    {
      exploit Memory_remove_disj_loc_stable; eauto. ii.
      exploit Memory_lower_disj_loc_stable; [eapply PROMISES | eauto..]. ii.
      rewrite x1. rewrite <- x0. eauto.
    }
    {
      eapply Memory_lower_disj_loc_stable; eauto.
    }
  - (* cancel *)
    des. subst. ss.
Qed.

Lemma Mem_at_eq_na_step_prsv
      lang lo e1 e2 m
      (NA_STEP: @Thread.na_step lang lo e1 e2)
      (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m):
    Mem_at_eq lo (Thread.memory e2) m.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit ATOMIC_COVER; eauto. ii.
  inv NA_STEP.
  - (* na read *)
    inv STEP; ss. inv LOCAL; ss.
  - (* na write *)
    unfold Mem_approxEq_loc in *. des.
    inv STEP; ss. inv LOCAL; ss.
    inv LOCAL0.
    assert(loc0 <> loc).
    {
      ii; subst.
      clear - H LO. rewrite H in LO. ss.
      des; ss.
    }
    unfold Memory.get in *.
    exploit Memory_write_disj_loc_stable; eauto. ii. des.
    rewrite <- x1. eauto.
  - (* na silent *)
    inv STEP; ss. inv LOCAL; ss.
Qed.

Lemma Mem_at_eq_na_steps_prsv':
  forall n lang lo e1 e2 m
    (NA_STEPS: rtcn (@Thread.na_step lang lo) n e1 e2)
    (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m),
    Mem_at_eq lo (Thread.memory e2) m.
Proof.
  induction n; ii.
  - inv NA_STEPS. eauto.
  - inv NA_STEPS. eapply IHn in A23; eauto.
    eapply Mem_at_eq_na_step_prsv; eauto.
Qed.

Lemma Mem_at_eq_na_steps_prsv
      lang lo e1 e2 m
      (NA_STEPS: rtc (@Thread.na_step lang lo) e1 e2)
      (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m):
  Mem_at_eq lo (Thread.memory e2) m.
Proof.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply Mem_at_eq_na_steps_prsv'; eauto.
Qed.

Lemma Mem_approxEq_loc_reflexive
      mem1 mem2 loc
      (MEM_APPROX_EQ: Mem_approxEq_loc loc mem1 mem2):
  Mem_approxEq_loc loc mem2 mem1.
Proof.
  unfold Mem_approxEq_loc in *.
  des.
  split; ii.
  specialize (MEM_APPROX_EQ f t val). des.
  split. eauto. eauto.
  specialize (MEM_APPROX_EQ0 f t).
  des.
  split; eauto.
Qed.
  
Lemma Mem_at_eq_reflexive
      mem1 mem2 lo
      (ATOMIC_COVER: Mem_at_eq lo mem1 mem2):
  Mem_at_eq lo mem2 mem1.
Proof.
  unfold Mem_at_eq in *; ii.
  exploit ATOMIC_COVER; eauto.
  ii.
  eapply Mem_approxEq_loc_reflexive in x; eauto.
Qed.

Lemma Mem_at_eq_init
      lo:
  Mem_at_eq lo Memory.init Memory.init.
Proof.
  unfold Mem_at_eq. ii.
  unfold Memory.init.
  unfold Mem_approxEq_loc.
  unfold Memory.get.
  split.
  ii.
  split; ii; des.
  erewrite Cell.init_get in *.
  des_ifH H0; ss. inv H0.
  unfold Message.elt. eauto.
  erewrite Cell.init_get in *.
  des_ifH H0; ss. inv H0.
  unfold Message.elt. eauto.
  ii; split; ii.
  erewrite Cell.init_get in *.
  des_ifH H0; ss.
  erewrite Cell.init_get in *.
  des_ifH H0; ss.
Qed.

Lemma Mem_approxEq_loc_adjacent
      mem1 mem2 loc from f t to
      (ADJ: Memory.adjacent loc from f t to mem1)
      (MEM_APPROX_EQ: Mem_approxEq_loc loc mem1 mem2):
  Memory.adjacent loc from f t to mem2.
Proof.
  inv MEM_APPROX_EQ.
  inv ADJ.
  destruct m1.
  {
    dup H. specialize (H1 from f val).
    des. clear H2. exploit H1; eauto. ii; des. clear H1.
    destruct m2.
    {
      dup H. specialize (H1 t to val0).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val1). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
    {
      dup H0. specialize (H1 t to).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val0). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
  }
  {
    dup H0. specialize (H1 from f).
    des. clear H2. exploit H1; eauto. ii; des. clear H1.
    destruct m2.
    {
      dup H. specialize (H1 t to val).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val0). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
    {
      dup H0. specialize (H1 t to).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
  }
Qed.

Lemma Mem_approxEq_loc_Mem_max_ts
      mem1 mem2 loc
      (MEM_APPROX_EQ: Mem_approxEq_loc loc mem1 mem2)
      (MEM_CLOSED1: Memory.closed mem1)
      (MEM_CLOSED2: Memory.closed mem2):
  Memory.max_ts loc mem1 = Memory.max_ts loc mem2.
Proof.
  unfold Mem_approxEq_loc in *. des.
  destruct (Time.le_lt_dec (Memory.max_ts loc mem1) (Memory.max_ts loc mem2)).
  {
    eapply Time.le_lteq in l; des; eauto.
    inv MEM_CLOSED1. clear CLOSED.
    inv MEM_CLOSED2. clear CLOSED.
    unfold Memory.inhabited in *.
    specialize (INHABITED loc). specialize (INHABITED0 loc).
    exploit Memory.max_ts_spec; [eapply INHABITED | eauto..]. ii; des.
    exploit Memory.max_ts_spec; [eapply INHABITED0 | eauto..]. ii; des.
    destruct msg0.
    {
      specialize (MEM_APPROX_EQ from0 (Memory.max_ts loc mem2) val). des.
      exploit MEM_APPROX_EQ1; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
    {
      specialize (MEM_APPROX_EQ0 from0 (Memory.max_ts loc mem2)). des.
      exploit MEM_APPROX_EQ1; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
  }
  {
    inv MEM_CLOSED1. clear CLOSED.
    inv MEM_CLOSED2. clear CLOSED.
    unfold Memory.inhabited in *.
    specialize (INHABITED loc). specialize (INHABITED0 loc).
    exploit Memory.max_ts_spec; [eapply INHABITED | eauto..]. ii; des.
    exploit Memory.max_ts_spec; [eapply INHABITED0 | eauto..]. ii; des.
    destruct msg.
    {
      specialize (MEM_APPROX_EQ from (Memory.max_ts loc mem1) val). des.
      exploit MEM_APPROX_EQ; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
    {
      specialize (MEM_APPROX_EQ0 from (Memory.max_ts loc mem1)). des.
      exploit MEM_APPROX_EQ0; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
  }
Qed.
  
Lemma Mem_at_eq_cap
      lo mem1 mem2 mem_c1 mem_c2
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (CAP1: Memory.cap mem1 mem_c1)
      (CAP2: Memory.cap mem2 mem_c2)
      (CLOSED_MEM1: Memory.closed mem1)
      (CLOSED_MEM2: Memory.closed mem2):
  Mem_at_eq lo mem_c1 mem_c2.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii.
  clear - CAP1 CAP2 x CLOSED_MEM1 CLOSED_MEM2.
  unfold Mem_approxEq_loc in *.
  des.
  split; ii.
  {
    split; ii; des.
    {
      exploit Memory.cap_inv; [eapply CLOSED_MEM1| eapply CAP1 | eapply H | eauto..]; eauto.
      ii; des; ss.
      specialize (x f t val). des.
      exploit x; eauto. ii; des.
      inv CAP2.
      eapply SOUND in x4; eauto.
    }
    {
      exploit Memory.cap_inv; [eapply CLOSED_MEM2| eapply CAP2 | eapply H | eauto..]; eauto.
      ii; des; ss.
      specialize (x f t val). des.
      exploit x1; eauto. ii; des.
      inv CAP1.
      eapply SOUND in x4; eauto.
    }
  }
  { 
    split; ii. 
    { 
      exploit Memory.cap_inv; [eapply CLOSED_MEM1| eapply CAP1 | eapply H | eauto..]; eauto.
      ii; des; ss.
      {
        dup x0. specialize (x1 f t). des.
        exploit x1; eauto. ii.
        inv CAP2; eauto.
      }
      {
        destruct(Memory.get loc t mem_c2) eqn: GET_MEM2_CAP; eauto.
        destruct p. destruct t1; eauto.
        exploit Memory.cap_inv; [eapply CLOSED_MEM2 | eapply CAP2 | eapply GET_MEM2_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x t0 t val). des.
        exploit x5; eauto. ii; des. rewrite x2 in x8; ss.
        exploit Memory.cap_inv; [eapply CLOSED_MEM2 | eapply CAP2 | eapply GET_MEM2_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x0 t0 t). des.
        eapply x5 in x6. rewrite x2 in x6. ss.
        assert (Time.le f t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (Time.le t0 t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (t0 = f).
        {
          destruct (Time.le_lt_dec t0 f).
          eapply Time.le_lteq in l. des; subst; eauto.
          inv x1. inv x5.
          specialize (EMPTY0 f). exploit EMPTY0; eauto. ii.
          destruct m1.
          {
            specialize (x from1 f val). des.
            exploit x; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from1 f). des.
            exploit x0; eauto. ii. rewrite x1 in x10. ss.
          }
          inv x1. inv x5.
          specialize (EMPTY t0). exploit EMPTY; eauto. ii.
          destruct m0.
          {
            specialize (x from0 t0 val). des.
            exploit x5; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from0 t0). des.
            exploit x5; eauto. ii. rewrite x1 in x10; ss.
          }
        }
        subst; eauto.
        inv x1.
        assert (Time.le (Time.incr (Memory.max_ts loc mem2)) to2).
        {
          exploit Memory.get_ts; [eapply GET2 | eauto..]. ii; des; subst; eauto.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        destruct m2.
        {          
          specialize (x (Time.incr (Memory.max_ts loc mem2)) to2 val).
          des.
          exploit x; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem2))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }
        {
          specialize (x0 (Time.incr (Memory.max_ts loc mem2)) to2).
          des.
          exploit x0; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem2))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }

        exploit Mem_approxEq_loc_adjacent; eauto.
        instantiate (1 := mem2).
        unfold Mem_approxEq_loc; eauto. ii.
        inv CAP2.
        eapply MIDDLE in x6; eauto.
        rewrite GET_MEM2_CAP in x6; ss.
      }
      {
        subst. 
        exploit Mem_approxEq_loc_Mem_max_ts; [ | eapply CLOSED_MEM1 | eapply CLOSED_MEM2 | eauto..]; eauto.
        instantiate (1 := loc). unfold Mem_approxEq_loc; eauto.
        ii. rewrite x3.
        inv CAP2. eapply BACK; eauto.
      }
    }
    {
      exploit Memory.cap_inv; [eapply CLOSED_MEM2| eapply CAP2 | eapply H | eauto..]; eauto.
      ii; des; ss.
      {
        dup x0. specialize (x1 f t). des.
        exploit x1; eauto. ii.
        inv CAP1; eauto.
      }
      {
        destruct(Memory.get loc t mem_c1) eqn: GET_MEM1_CAP; eauto.
        destruct p. destruct t1; eauto.
        exploit Memory.cap_inv; [eapply CLOSED_MEM1 | eapply CAP1 | eapply GET_MEM1_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x t0 t val). des.
        exploit x; eauto. ii; des. rewrite x2 in x8; ss.
        exploit Memory.cap_inv; [eapply CLOSED_MEM1 | eapply CAP1 | eapply GET_MEM1_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x0 t0 t). des.
        eapply x0 in x6. rewrite x2 in x6. ss.
        assert (Time.le f t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (Time.le t0 t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (t0 = f).
        {
          destruct (Time.le_lt_dec t0 f).
          eapply Time.le_lteq in l. des; subst; eauto.
          inv x1. inv x5.
          specialize (EMPTY0 f). exploit EMPTY0; eauto. ii.
          destruct m1.
          {
            specialize (x from1 f val). des.
            exploit x5; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from1 f). des.
            exploit x5; eauto. ii. rewrite x1 in x10. ss.
          }
          inv x1. inv x5.
          specialize (EMPTY t0). exploit EMPTY; eauto. ii.
          destruct m0.
          {
            specialize (x from0 t0 val). des.
            exploit x; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from0 t0). des.
            exploit x0; eauto. ii. rewrite x1 in x10; ss.
          }
        }
        subst; eauto.
        inv x1.
        assert (Time.le (Time.incr (Memory.max_ts loc mem1)) to2).
        {
          exploit Memory.get_ts; [eapply GET2 | eauto..]. ii; des; subst; eauto.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        destruct m2.
        {           
          specialize (x (Time.incr (Memory.max_ts loc mem1)) to2 val).
          des.
          exploit x1; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem1) (Time.incr (Memory.max_ts loc mem1))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem1))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }
        {
          specialize (x0 (Time.incr (Memory.max_ts loc mem1)) to2).
          des.
          exploit x1; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem1) (Time.incr (Memory.max_ts loc mem1))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem1))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }

        exploit Mem_approxEq_loc_adjacent; eauto.
        instantiate (1 := mem1).
        eapply Mem_approxEq_loc_reflexive; eauto.
        unfold Mem_approxEq_loc; eauto. ii.
        inv CAP1.
        eapply MIDDLE in x6; eauto.
        rewrite GET_MEM1_CAP in x6; ss.
      }
      {
        subst. 
        exploit Mem_approxEq_loc_Mem_max_ts; [ | eapply CLOSED_MEM1 | eapply CLOSED_MEM2 | eauto..]; eauto.
        instantiate (1 := loc). unfold Mem_approxEq_loc; eauto.
        ii. rewrite <- x3.
        inv CAP1. eapply BACK; eauto.
      }
    }
  }
Qed.

Lemma memory_add_split_at_eq_prsv_contr
      loc from to lo
      mem1 mem1'
      mem2 msg2 mem2' ts
      val1 R1 val2 R2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (ADD: Memory.add mem1 loc from to (Message.concrete val1 R1) mem1')
      (SPLIT: Memory.split mem2 loc from to ts msg2 (Message.concrete val2 R2) mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  False.
Proof.
  exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT | eauto..]. ii; des. clear GET3.
  exploit Memory.add_get0; [eapply ADD | eauto..]. ii; des.
  exploit add_succeed_wf; [eapply ADD | eauto..]. ii; des.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x. des.
  specialize (x from ts val2). des.
  exploit x1; eauto. ii; des.
  eapply DISJOINT in x3.
  unfold Interval.disjoint in x3.
  specialize (x3 to). eapply x3; eauto.
  econs; ss. eapply Time.le_lteq; eauto.
  econs; ss. clear - TS23. eapply Time.le_lteq; eauto.
Qed.

Lemma memory_split_split_at_eq_prsv_contr
      loc from to lo
      mem1 mem1' msg1 val1 R1 ts1
      mem2 mem2' msg2 val2 R2 ts2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (SPLIT1: Memory.split mem1 loc from to ts1 msg1 (Message.concrete val1 R1) mem1')
      (SPLIT2: Memory.split mem2 loc from to ts2 msg2 (Message.concrete val2 R2) mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  ts1 = ts2 /\ val1 = val2.
Proof.
  exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT1 | eauto..]. ii; des. clear GET3.
  exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT2 | eauto..]. ii; des. clear GET7.
  assert(ts1 = ts2).
  {
    destruct (Time.le_lt_dec ts1 ts2).
    {
      eapply Time.le_lteq in l. des; subst; ss.
      unfold Mem_at_eq in MEM_AR_EQ.
      exploit MEM_AR_EQ; eauto. ii.
      unfold Mem_approxEq_loc in x.
      des.
      specialize (x from ts1 val1). des.
      exploit x2; eauto. ii; des.
      exploit Memory.get_disjoint; [eapply GET4 | eapply x3 | eauto..]. ii; des; subst; eauto.
      unfold Interval.disjoint in x4.
      specialize (x4 ts1).
      exploit x4; eauto; ss.
      econs; ss; eauto. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
      econs; ss; eauto.
      auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }
    {
      unfold Mem_at_eq in MEM_AR_EQ.
      exploit MEM_AR_EQ; eauto. ii.
      unfold Mem_approxEq_loc in x.
      des.
      specialize (x from ts1 val1). des.
      exploit x; eauto. ii; des.
      exploit Memory.get_disjoint; [eapply GET4 | eapply x3 | eauto..]. ii; des; subst; eauto.
      unfold Interval.disjoint in x4.
      specialize (x4 ts2).
      exploit x4; eauto; ss.
      econs; ss; eauto. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
      econs; ss; eauto.
      auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }
  }
  subst.
  split; eauto.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x.
  des.
  specialize (x from ts2 val2). des.
  exploit x1; eauto. ii; des.
  rewrite GET0 in x3. inv x3; eauto.
Qed.

Lemma memory_add_lower_at_eq_prsv_contr
      loc from to lo
      mem1 mem1'
      mem2 msg2 mem2'
      val1 R1 val2 R2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (ADD: Memory.add mem1 loc from to (Message.concrete val1 R1) mem1')
      (LOWER: Memory.lower mem2 loc from to (Message.concrete val2 R2) msg2 mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  False.
Proof.
  exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
  exploit lower_succeed_wf; [eapply LOWER | eauto..]. ii; des.
  inv MSG_LE0.
  exploit Memory.add_get0; [eapply ADD | eauto..]. ii; des.
  exploit add_succeed_wf; [eapply ADD | eauto..]. ii; des.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x. des.
  specialize (x from to val2). des.
  exploit x1; eauto. ii; des.
  rewrite GET2 in x3. ss.
Qed.

Lemma memory_split_lower_at_eq_prsv_contr
      loc from to lo
      mem1 mem1' msg1 val1 R1 ts1
      mem2 mem2' msg2 val2 R2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (SPLIT: Memory.split mem1 loc from to ts1 msg1 (Message.concrete val1 R1) mem1')
      (LOWER: Memory.lower mem2 loc from to (Message.concrete val2 R2) msg2 mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  False.
Proof.
  exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT | eauto..]. ii; des. clear GET3.
  exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
  inv MSG_LE.
  exploit lower_succeed_wf; [eapply LOWER | eauto..]. ii; des.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x. des.
  specialize (x from to val2). des.
  exploit x1; eauto. ii; des.
  rewrite GET in x3. ss.
Qed.
  
Lemma local_write_Mem_at_eq_prsv_kind_match
      loc from to val lo ord 
      lc1 sc1 mem1 releasedr1 releasedw1 lc1' sc1' mem1' kind1
      lc2 sc2 mem2 releasedr2 releasedw2 lc2' sc2' mem2' kind2
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 releasedw1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from to val releasedr2 releasedw2 ord lc2' sc2' mem2' kind2 lo)
      (MEM_AT_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  kind_match kind1 kind2.
Proof.
  destruct kind1.
  - (* kind1 = add *)
    destruct kind2; ss.
    + (* kind2 = split *)
      inv WRITE2. inv WRITE. inv PROMISE.
      des; subst; ss. inv RESERVE.
      inv WRITE1. inv WRITE. inv PROMISE.
      exploit memory_add_split_at_eq_prsv_contr;
        [eapply MEM_AT_EQ | eapply MEM0 | eapply MEM | eauto..].      
    + (* kind2 = lower *)
      inv WRITE1. inv WRITE. inv PROMISE.
      inv WRITE2. inv WRITE. inv PROMISE.
      des; subst.
      exploit memory_add_lower_at_eq_prsv_contr;
        [eapply MEM_AT_EQ | eapply MEM | eapply MEM0 | eauto..].
    + (* kind2 = cancel *)
      inv WRITE2. inv WRITE. inv PROMISE; ss.
  - (* kind1 = split *)
    destruct kind2; ss.
    + (* kind2 = add *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      inv WRITE2. inv WRITE. inv PROMISE.
      exploit memory_add_split_at_eq_prsv_contr;
        [ | eapply MEM0 | eapply MEM | eauto..].
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    + (* kind2 = split *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      exploit memory_split_split_at_eq_prsv_contr; [eapply MEM_AT_EQ | eapply MEM | eapply MEM0 | eauto..].
    + (* kind2 = lower *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss.
      eapply memory_split_lower_at_eq_prsv_contr;
        [eapply MEM_AT_EQ | eapply MEM | eapply MEM0 | eauto..].
    + (* kind2 = cancel *)
      inv WRITE2. inv WRITE. inv PROMISE. ss.
  - (* kind1 = lower *)
    destruct kind2; ss.
    + (* kind2 = add *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss.
      inv WRITE2. inv WRITE. inv PROMISE.
      exploit memory_add_lower_at_eq_prsv_contr;
        [ | eapply MEM0 | eapply MEM | eauto..].
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    + (* kind2 = split *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      exploit memory_split_lower_at_eq_prsv_contr;
        [ | eapply MEM0 | eapply MEM | eauto..].
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    + (* kind2 = lower *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss.
      exploit lower_succeed_wf; [eapply MEM | eauto..]. ii; des.
      inv MSG_LE.
      exploit lower_succeed_wf; [eapply MEM0 | eauto..]. ii; des.
      inv MSG_LE.
      eauto.
    + (* kind2 = cancel *)
      inv WRITE2. inv WRITE. inv PROMISE; ss.
  - (* kind1 = cancel *)
    inv WRITE1. inv WRITE. inv PROMISE; ss.
Qed.
      
