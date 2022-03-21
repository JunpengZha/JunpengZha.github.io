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
Require Import Reordering.
Require Import ps_to_np_thread.
Require Import WFConfig.
Require Import PromiseConsistent.
Require Import MemoryReorder.
Require Import ReorderPromise.
Require Import ReorderReserve.
Require Import ReorderCancel.
Require Import ConsistentLemmas.
Require Import PromiseInjection.

(** Equivalence between the thread consisten and NPthread consistent *)
Lemma Thread_consistent_nprm_to_consistent
      (lang: language) (e: Thread.t lang) (lo: Ordering.LocOrdMap):
  Thread.consistent_nprm e lo -> Thread.consistent e lo.
Proof.
  intros.
  unfolds Thread.consistent, Thread.consistent_nprm.
  intros.
  eapply H in CAP; eauto.
  destruct CAP as (e2 & Hthrd_nprm_steps & Hfulfill).
  exists e2.
  split; eauto.
  eapply Thread_nprm_step_is_tau_step; eauto.
Qed.

Lemma consistent_nprm_promise_consistent
      lang th lo
      (CONS: @Thread.consistent_nprm lang th lo)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th)):
  Local.promise_consistent (Thread.local th).
Proof.
  eapply Thread_consistent_nprm_to_consistent in CONS.
  eapply consistent_promise_consistent; eauto.
Qed.
  
Ltac solve_one_step :=
  eapply Relation_Operators.rt1n_trans; [idtac | eauto].
Ltac solve_event_contr :=
  let Hcontr := fresh in
  (intro Hcontr; destruct Hcontr; tryfalse).

Lemma nprm_steps_fulfill_implies_no_scfence_nprm_step_fulfill:
  forall n lang lo e e'
    (NPRM_STEPS: rtcn (@Thread.nprm_step lang lo) n e e')
    (BOT: Local.promises (Thread.local e') = Memory.bot),
  exists e0,
    rtc (no_scfence_nprm_step lang lo) e e0 /\
    Local.promises (Thread.local e0) = Memory.bot.
Proof.
  induction n; ii.
  - inv NPRM_STEPS; eauto.
  - inv NPRM_STEPS.
    eapply IHn in A23; eauto. des.
    inv A12.
    + inv PROG. inv LOCAL.
      {
        (* silent *)
        exists e0. split; eauto.
        eapply Relation_Operators.rt1n_trans; [ | eapply A23].
        econs; eauto. ii; des; ss.
      }
      {
        (* read *)
        exists e0. split; eauto.
        eapply Relation_Operators.rt1n_trans; [ | eapply A23].
        econs; eauto. ii; des; ss.
      }
      {
        (* write *)
        exists e0. split; eauto.
        eapply Relation_Operators.rt1n_trans; [ | eapply A23].
        econs; eauto. ii; des; ss.
      }
      {
        (* update *)
        exists e0. split; eauto.
        eapply Relation_Operators.rt1n_trans; [ | eapply A23].
        econs; eauto. ii; des; ss.
      }
      {
        (* fence *)
        assert (SC_FENCE_OR_NOT: ordw = Ordering.seqcst \/ ordw <> Ordering.seqcst).
        {
          destruct ordw; ss; eauto; try solve [right; ii; ss].
        }
        destruct SC_FENCE_OR_NOT as [SC_FENCE | NOT_SC_FENCE].
        {
          subst.
          inv LOCAL0; ss.
          exploit PROMISES; eauto.
        }
        {
          exists e0. split; eauto.
          eapply Relation_Operators.rt1n_trans; [ | eapply A23].
          econs; eauto. ii; des; ss.
          inv H; ss.
        }
      }
      {
        (* output *)
        inv LOCAL0.
        exploit PROMISES; eauto.
      }
    + exists e0. split; eauto.
      eapply Relation_Operators.rt1n_trans; [ | eapply A23].
      eapply no_scfence_nprm_step_intro2; eauto.
Qed.

Lemma no_scfence_step_promise_consistent
      lang lo th1 th2
      (NO_SCFENCE_STEP: no_scfence_nprm_step lo lang th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  inv NO_SCFENCE_STEP; [inv STEP; inv LOCAL | inv STEP]; ss.
  - eapply read_step_promise_consistent; eauto.
  - eapply write_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
    eapply write_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
  - eapply promise_step_promise_consistent; eauto.
Qed.

Lemma no_scfence_steps_promise_consistent
      lang lo th1 th2
      (NO_SCFENCE_STEPS: rtc (no_scfence_nprm_step lo lang) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  induction NO_SCFENCE_STEPS; ss; eauto.
  lets CONS_Y: CONS. eapply IHNO_SCFENCE_STEPS in CONS_Y; eauto.
  eapply no_scfence_step_promise_consistent in H; eauto.
  eapply no_scfence_nprm_step_prsv_local_wf; eauto.
  eapply no_scfence_nprm_step_prsv_memory_closed; eauto.
Qed.

Lemma no_scfence_steps_to_bot_promise_consistent
      lang lo th1 th2
      (NO_SCFENCE_STEPS: rtc (no_scfence_nprm_step lo lang) th1 th2)
      (BOT: Local.promises (Thread.local th2) = Memory.bot)
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  eapply no_scfence_steps_promise_consistent.
  eapply NO_SCFENCE_STEPS.
  unfold Local.promise_consistent. ii; ss.
  rewrite BOT in PROMISE.
  rewrite Memory.bot_get in PROMISE. ss.
  eauto. eauto.
Qed.

Lemma nprm_steps_to_bot_promise_consistent
      lang lo th1 th2
      (NPRM_STEPS: rtc (@Thread.nprm_step lo lang) th1 th2)
      (BOT: Local.promises (Thread.local th2) = Memory.bot)
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  eapply rtc_rtcn in NPRM_STEPS. des.
  eapply nprm_steps_fulfill_implies_no_scfence_nprm_step_fulfill in NPRM_STEPS; eauto. des.
  eapply no_scfence_steps_to_bot_promise_consistent; eauto.
Qed.
    
Lemma program_step_promise_prsv_or_elim'
      (lang: language) (st: Language.state lang) lc sc mem lo te e lc' mem' loc from to msg kind
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem)
      (PROG: Thread.program_step te lo (Thread.mk lang st lc' sc mem') e)
      (NOSCF: ~(exists ordr, te = ThreadEvent.fence ordr Ordering.seqcst))
      (NOT_OUT: ThreadEvent.get_machine_event te = MachineEvent.silent)
      (CONS: Local.promise_consistent (Thread.local e))
      (PRM: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (NONPF: Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg)
      (KIND: Memory.op_kind_is_cancel kind = false):
  exists e',
    rtc (no_scfence_nprm_step lang lo) (Thread.mk lang st lc sc mem) e' /\
    (
      e = e' \/
      (exists from' msg' kind',
          Local.promise_step (Thread.local e') (Thread.memory e') loc from' to msg'
                             (Thread.local e) (Thread.memory e) kind' /\
          (Thread.state e) = (Thread.state e') /\ (Thread.sc e) = (Thread.sc e'))
    ).
Proof.
  assert(CLOSED_MEM': Memory.closed mem').
  {
    eapply promise_step_closed_mem; eauto.
  }
  assert(LOCAL_WF': Local.wf lc' mem').
  {
    inv PRM.
    eapply local_wf_promise; eauto.
    destruct lc; eauto.
  }
  inv PROG; ss.
  inv LOCAL.
  - (* silent step *)
    eexists.
    split.
    eapply Operators_Properties.clos_rt1n_step.
    eapply no_scfence_nprm_step_intro1; [econstructor; eauto | eauto..].
    right; ss.
    do 3 eexists; eauto.
  - (* read step *)
    assert (DISJ: (loc, to) <> (loc0, ts)).
    {
      eapply read_promise_not_consistent; eauto.
    }
    eapply reorder_promise_read in PRM; eauto.
    destruct PRM as (lc1' & READ & PROMISE).
    eexists.
    split.
    eapply Operators_Properties.clos_rt1n_step.
    eapply no_scfence_nprm_step_intro1; [econstructor; eauto | eauto..].
    right; ss.
    do 3 eexists.
    eauto.
  - (* write step *)
    exploit reorder_promise_write'; eauto.
    introv REORDER.
    destruct REORDER as [CONTR | (kind2' & lc1' & mem1' & WRITE' & PROMISE')].
    { 
      destruct CONTR; subst.
      inv PRM. 
      lets PROMISE': PROMISE.
      eapply Memory.promise_get0 in PROMISE; eauto.
      clear NONPF; des.
      destruct kind; ss.
      {
        (* promise add *)
        inv PROMISE'.
        destruct msg.
        { 
          (* add concrete message *)
          eapply promise_consistent_promise_write in LOCAL0; eauto.
          eapply Time_le_gt_false in LOCAL0; ss.
        }
        {
          (* add reservation *)
          eapply reorder_reserve_write in LOCAL0; eauto. des.
          eexists.
          split.
          eapply Operators_Properties.clos_rt1n_step.
          eapply no_scfence_nprm_step_intro1.
          econstructor.
          2: eapply Local.step_write; eauto.
          ss; eauto.
          ss; eauto.
          i; des; ss.
          right; ss.
          do 3 eexists; eauto.
        }
      }
      {
        (* promise split *)
        inv PROMISE'; des; subst; ss.
        eapply promise_consistent_promise_write in LOCAL0; eauto.
        eapply Time_le_gt_false in LOCAL0; ss.
      }
      {
        (* promise lower *)
        inv PROMISE'; des; subst.
        lets PROMISES': PROMISES.
        eapply Memory.lower_get0 in PROMISES; des.
        destruct msg.
        eapply promise_consistent_promise_write in LOCAL0; ss; eauto.
        eapply Time_le_gt_false in LOCAL0; ss.
        clear - PROMISES'.
        inv PROMISES'.
        inv LOWER.
        inv MSG_LE.
      }
    }
    {
      clear NONPF; des.
      destruct STEP2 as [CONFIG_EQ | CONT].
      {
        inv CONFIG_EQ.
        eexists.
        split.
        eapply Operators_Properties.clos_rt1n_step.
        eapply no_scfence_nprm_step_intro1.
        econstructor.
        2: eapply Local.step_write; eauto.
        ss; eauto.
        ss; eauto.
        ii; des; ss.
        left; eauto.
      }
      {
        des.
        eexists.
        split.
        eapply Operators_Properties.clos_rt1n_step.
        eapply no_scfence_nprm_step_intro1.
        econstructor.
        2: eapply Local.step_write; eauto.
        ss; eauto.
        ss; eauto.
        ii; des; ss.
        right.
        do 3 eexists; ss.
        eauto.
      }
    }
  - (* update *)
    assert (DISJ: (loc, to) <> (loc0, tsr)).
    {
      eapply read_promise_not_consistent; eauto.
      eapply write_step_promise_consistent; eauto.
    }
    eapply reorder_promise_read in PRM; eauto.
    destruct PRM as (lc1' & READ & PROMISE).
    exploit reorder_promise_write'; eauto.
    {
      inv LOCAL1; ss.
      eapply closed_mem_implies_wf_msg_view; eauto.
    }
    {
      inv READ; ss.
      eapply closed_mem_implies_closed_msg; eauto.
    }
    {
      eapply local_wf_read; eauto.
    }
    {
      introv REORDER.
      destruct REORDER as [CONTR | (kind2' & lc2' & mem1' & WRITE' & PROMISE')].
      { 
        destruct CONTR; subst.
        inv PROMISE. 
        lets PROMISE': PROMISE0.
        eapply Memory.promise_get0 in PROMISE0; eauto.
        clear NONPF; des.
        destruct kind; ss.
        {
          (* promise add *)
          inv PROMISE'.
          destruct msg.
          { 
            (* add concrete message *)
            eapply promise_consistent_promise_write in LOCAL2; eauto.
            eapply Time_le_gt_false in LOCAL2; ss.
          }
          {
            (* add reservation *)
            eapply reorder_reserve_write in LOCAL2; eauto. des.
            eexists.
            split.
            eapply Operators_Properties.clos_rt1n_step.
            eapply no_scfence_nprm_step_intro1.
            econstructor.
            2: eapply Local.step_update; eauto.
            ss; eauto.
            ss; eauto.
            i; des; ss.
            right; ss.
            do 3 eexists; eauto.
          }
        }
        {
          (* promise split *)
          inv PROMISE'; des; subst; ss.
          eapply promise_consistent_promise_write in LOCAL2; eauto.
          eapply Time_le_gt_false in LOCAL2; ss.
        }
        {
          (* promise lower *)
          inv PROMISE'; des; subst.
          lets PROMISES': PROMISES.
          eapply Memory.lower_get0 in PROMISES; des.
          destruct msg.
          eapply promise_consistent_promise_write in LOCAL2; ss; eauto.
          eapply Time_le_gt_false in LOCAL2; ss.
          clear - PROMISES'.
          inv PROMISES'.
          inv LOWER.
          inv MSG_LE.
        }
      }
      {
        clear NONPF; des.
        destruct STEP2 as [CONFIG_EQ | CONT].
        {
          inv CONFIG_EQ.
          eexists.
          split.
          eapply Operators_Properties.clos_rt1n_step.
          econstructor; eauto.
          left; eauto.
        }
        {
          des; ss.
          eexists.
          split. 
          eapply Operators_Properties.clos_rt1n_step.
          econstructor; eauto.
          econstructor; eauto.
          ss; eauto.
          right; ss.
          do 3 eexists; eauto.
        }
      }
    }
  - (* fence *)
    eapply reorder_promise_fence in PRM; eauto.
    clear NONPF; des.
    eexists.
    split.
    eapply Operators_Properties.clos_rt1n_step; eauto.
    econstructor; eauto.
    right; ss.
    do 3 eexists; eauto.
    intro; contradiction NOSCF; subst.
    simpl; eauto.
  - (* output *)
    tryfalse.
Qed.

Lemma program_step_promise_prsv_or_elim
      (lang: language) (st: Language.state lang) lc sc mem lo te e lc' mem' loc from to msg kind
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem)
      (PROG: Thread.program_step te lo (Thread.mk lang st lc' sc mem') e)
      (NOSCF: ~(exists ordr, te = ThreadEvent.fence ordr Ordering.seqcst))
      (NOT_OUT: ThreadEvent.get_machine_event te = MachineEvent.silent)
      (CONS: Local.promise_consistent (Thread.local e))
      (PRM: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (NONPF: Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg):
  exists e',
    rtc (no_scfence_nprm_step lang lo) (Thread.mk lang st lc sc mem) e' /\
    (
      e = e' \/
      (exists from' msg' kind',
          Local.promise_step (Thread.local e') (Thread.memory e') loc from' to msg'
                             (Thread.local e) (Thread.memory e) kind' /\
          (Thread.state e) = (Thread.state e') /\ (Thread.sc e) = (Thread.sc e'))
    ).
Proof.
  destruct(Memory.op_kind_is_cancel kind) eqn: ISCCL.
  {
    destruct kind; ss.
    eexists.
    split.
    eapply Relation_Operators.rt1n_trans. 
    eapply no_scfence_nprm_step_intro2; eauto.
    econstructor; eauto.
    eapply Operators_Properties.clos_rt1n_step.
    econstructor; eauto.
    left; eauto.
  }
  {
    eapply program_step_promise_prsv_or_elim'; eauto.
  }
Qed.
  
Lemma pf_step_promise_prsv_or_elim'
      (lang: language) (st: Language.state lang) lc sc mem lo te e lc' mem' loc from to msg kind
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem)
      (PROG: Thread.promise_step true te (Thread.mk lang st lc' sc mem') e)
      (CONS: Local.promise_consistent (Thread.local e))
      (PRM: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (NONPF: Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg)
      (KIND: Memory.op_kind_is_cancel kind = false):
  exists e',
    rtc (no_scfence_nprm_step lang lo) (Thread.mk lang st lc sc mem) e' /\
    (
      e = e' \/
      (exists from' msg' kind',
          Local.promise_step (Thread.local e') (Thread.memory e') loc from' to msg'
                             (Thread.local e) (Thread.memory e) kind' /\
          (Thread.state e) = (Thread.state e') /\ (Thread.sc e) = (Thread.sc e'))
    ).
Proof.
  inv PROG; ss.
  destruct kind0; ss; tryfalse.
  {
    destruct msg1; ss; tryfalse.
    destruct msg0; ss; tryfalse.
    destruct released0; ss; tryfalse.
    destruct(classic (exists to1' msg1', loc = loc0 /\ kind = Memory.op_kind_split to1' msg1' /\ to1' = to0))
            as [SPLIT_LOWER_SAME | SPLIT_LOWER_NOT_SAME].
    {
      destruct SPLIT_LOWER_SAME as (to1' & msg1' & LOC & KIND' & TO'); subst.
      inv PRM; inv LOCAL; ss.
      inv PROMISE; inv PROMISE0; ss.
      clear NONPF; des; ss.
      inv RESERVE0; ss.  
      exploit MemoryReorder.split_lower_same; [eapply PROMISES | eapply PROMISES0 | eauto..].
      ii; des; subst.
      exploit MemoryReorder.split_lower_same; [eapply MEM | eapply MEM0 | eauto..].
      ii; des; subst. inv H1.
      renames mem1' to promise1'.
      eexists.
      split.
      eapply Operators_Properties.clos_rt1n_step.
      eapply no_scfence_nprm_step_intro2.
      econstructor.
      econstructor. 
      eapply Memory.promise_lower; eauto.
      ss; eauto.
      ss; eauto.
      ss; eauto.
      ss; right. 
      do 3 eexists. 
      split; eauto.  
      econstructor. 
      eapply Memory.promise_split; eauto.
      eapply Memory.lower_closed_message; eauto.
      ss.
    }
    {
      exploit reorder_promise_promise; [eapply PRM | eapply LOCAL | eauto..].
      {
        ii; subst.
        split; [|ii; tryfalse].
        intro; subst.
        contradiction SPLIT_LOWER_NOT_SAME; eauto.
      }
      {
        ii; tryfalse.
      }
      {
        clear NONPF; ii.
        des.
        destruct STEP2 as [CONFIG_EQ | CONT].
        {
          inv CONFIG_EQ.
          eexists.
          split; eauto.
          right; ss.
          do 3 eexists; eauto.
        }
        {
          des. 
          exploit CONT2; eauto; ii.
          des; subst.
          eexists.
          split.
          eapply Operators_Properties.clos_rt1n_step.
          eapply no_scfence_nprm_step_intro2; eauto.
          econstructor; eauto.
          right; ss.
          do 3 eexists; eauto.
        }
      }
    }
  }
  { 
    exploit reorder_promise_promise_cancel; [eapply PRM | eapply LOCAL | eauto..].
    clear NONPF; ii; des; subst.
    {
      eexists.
      split; [eauto | ..].
      left; eauto.
    }
    {
      eexists.
      split.
      eapply Operators_Properties.clos_rt1n_step.
      eapply no_scfence_nprm_step_intro2; eauto.
      econstructor; [eapply STEP1 | eauto..].
      right; ss.
      do 3 eexists; eauto.
    }
  }
Qed.

Lemma pf_step_promise_prsv_or_elim
      (lang: language) (st: Language.state lang) lc sc mem lo te e lc' mem' loc from to msg kind
      (CLOSED_MEM: Memory.closed mem)
      (LOCAL_WF: Local.wf lc mem)
      (PROG: Thread.promise_step true te (Thread.mk lang st lc' sc mem') e)
      (CONS: Local.promise_consistent (Thread.local e))
      (PRM: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (NONPF: Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg):
  exists e',
    rtc (no_scfence_nprm_step lang lo) (Thread.mk lang st lc sc mem) e' /\
    (
      e = e' \/
      (exists from' msg' kind',
          Local.promise_step (Thread.local e') (Thread.memory e') loc from' to msg'
                             (Thread.local e) (Thread.memory e) kind' /\
          (Thread.state e) = (Thread.state e') /\ (Thread.sc e) = (Thread.sc e'))
    ).
Proof.
  destruct(Memory.op_kind_is_cancel kind) eqn:ISCCL.
  {
    destruct kind; ss.
    eexists.
    split.
    eapply rtc_compose.
    eapply Operators_Properties.clos_rt1n_step.
    eapply no_scfence_nprm_step_intro2.
    econstructor; eauto.
    eapply Operators_Properties.clos_rt1n_step.
    eapply no_scfence_nprm_step_intro2; eauto.
    left; eauto.
  }
  {
    eapply pf_step_promise_prsv_or_elim'; eauto.
  }
Qed.
  
Lemma promise_step_noccl_promise_bot_prsv
      lc mem loc from to msg lc' mem' kind
      (PSTEP: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (NOCCL: kind <> Memory.op_kind_cancel)
      (PBot: Local.promises lc' = Memory.bot):
  Local.promises lc = Memory.bot.
Proof.
  inv PSTEP; ss.
  inv PROMISE; ss.
  {
    (* add *)
    inv PROMISES.
    inv ADD.
    assert(CONTR1: LocFun.find loc (LocFun.add loc r (Local.promises lc)) = Memory.bot loc).
    rewrite <- MEM2; eauto.
    rewrite IdentFun.add_spec_eq in CONTR1; subst.
    assert(CONTR2: DenseOrder.DOMap.find to Cell.Raw.bot =
                   DenseOrder.DOMap.find to (DenseOrder.DOMap.add to (from, msg)
                                                                  (Cell.raw (Local.promises lc loc)))).
    rewrite <- CELL2; eauto.
    rewrite DenseOrder.DOMap.Facts.empty_o, DenseOrder.DOMap.gss in CONTR2; tryfalse.
  }
  {
    (* split *)
    inv PROMISES.
    inv SPLIT.
    assert(CONTR1: LocFun.find loc (LocFun.add loc r (Local.promises lc)) = Memory.bot loc).
    rewrite <- MEM2; eauto.
    rewrite IdentFun.add_spec_eq in CONTR1; subst; simpls.
    assert(CONTR2: DenseOrder.DOMap.find to Cell.Raw.bot =
                   DenseOrder.DOMap.find
                     to (DenseOrder.DOMap.add to (from, msg)
                                              (DenseOrder.DOMap.add ts3 (to, msg3)
                                                                    (Cell.raw (Local.promises lc loc))))).
    rewrite <- CELL2; eauto.
    rewrite DenseOrder.DOMap.Facts.empty_o, DenseOrder.DOMap.gss in CONTR2; tryfalse.
  }
  {
    (* lower *)
    inv PROMISES.
    inv LOWER.
    assert(CONTR1: LocFun.find loc (LocFun.add loc r (Local.promises lc)) = Memory.bot loc).
    rewrite <- MEM2; eauto.
    rewrite IdentFun.add_spec_eq in CONTR1; subst; simpls.
    assert(CONTR2: DenseOrder.DOMap.find to Cell.Raw.bot =
                   DenseOrder.DOMap.find
                     to (DenseOrder.DOMap.add to (from, msg) (Cell.raw (Local.promises lc loc)))).
    rewrite <- CELL2; eauto.
    rewrite DenseOrder.DOMap.Facts.empty_o, DenseOrder.DOMap.gss in CONTR2; tryfalse.
  }
Qed.

Lemma Thread_promise_step_cons_nprm_fulfill':
  forall n lang lo st lc sc mem st' lc' sc' mem' lc'' mem'' msg loc from to kind
         (CLOSED_MEM: Memory.closed mem)
         (LOCAL_WF: Local.wf lc mem)
         (PROMISE: Local.promise_step lc mem loc from to msg lc' mem' kind)
         (NPRM_STEPS: rtcn (@Thread.nprm_step lang lo) n
                           (Thread.mk lang st lc' sc mem') (Thread.mk lang st' lc'' sc' mem''))
         (FULFILL: Local.promises lc'' = Memory.bot),
  exists st0 lc0 sc0 mem0,
    rtc (@Thread.nprm_step lang lo)
        (Thread.mk lang st lc sc mem) (Thread.mk lang st0 lc0 sc0 mem0) /\
    Local.promises lc0 = Memory.bot.
Proof.
  induction n; intros.
  - inv NPRM_STEPS.
    destruct(classic (kind = Memory.op_kind_cancel)); subst.
    {
      (* cancel *)
      do 4 eexists.
      split.
      eapply Operators_Properties.clos_rt1n_step.
      eapply Thread.nprm_step_pf_step; eauto.
      econstructor; eauto. eauto.
    }
    {
      (* not cancel *)
      eapply promise_step_noccl_promise_bot_prsv in PROMISE; eauto.
      do 4 eexists.
      split; eauto.
    }
  - inv NPRM_STEPS.
    destruct a2.
    destruct (classic (Memory.op_kind_is_lower_concrete kind = false \/ ~ Message.is_released_none msg))
             as [NONPF | ISPF].
    {
      (* Not promise-free *)
      inv A12.
      {
        (* program step *)
        destruct(classic (exists ordr, e = ThreadEvent.fence ordr Ordering.seqcst)).
        { 
          (* fence sc step *) 
          destruct H as (ordr & E); subst; tryfalse.
          inv PROG. 
          inv LOCAL.
          inv LOCAL0; ss.
          exploit PROMISES; eauto.
          introv BOT.
          clear - PROMISE BOT.
          destruct(classic (kind = Memory.op_kind_cancel)); subst.
          {
            do 4 eexists.
            split; [|eauto].
            eapply Operators_Properties.clos_rt1n_step.
            eapply Thread.nprm_step_pf_step; eauto.
            econstructor; ss; eauto.
          }
          {
            eapply promise_step_noccl_promise_bot_prsv in PROMISE; eauto.
            do 4 eexists.
            split; eauto.
          }
        }
        { 
          (* not fence sc step *)
          eapply program_step_promise_prsv_or_elim in PROG; eauto; ss.
          destruct PROG as (e' & NOFENCE_SC_PF_STEPS & CONT).
          destruct CONT as [CONT | CONT]; subst.
          {
            eapply rtcn_rtc in A23.
            eapply no_scfence_nprm_steps_is_nprm_steps in NOFENCE_SC_PF_STEPS.
            do 4 eexists.
            split; [eapply rtc_compose; [eapply NOFENCE_SC_PF_STEPS | eapply A23] | eauto].
          }
          {
            destruct e'; ss.
            destruct CONT as (from' & msg' & kind' & LOCAL_PROM & ST & SC); subst. 
            eapply IHn with (lc := local0) (mem := memory0) in A23; eauto.
            destruct A23 as (st0 & lc0 & sc0 & mem0 & NPRM_STEPS' & BOT).
            eapply no_scfence_nprm_steps_is_nprm_steps in NOFENCE_SC_PF_STEPS.
            do 4 eexists.
            split; [eapply rtc_compose; [eapply NOFENCE_SC_PF_STEPS | eapply NPRM_STEPS'] | eauto].
            eapply rtc_rtcn in NOFENCE_SC_PF_STEPS.
            destruct NOFENCE_SC_PF_STEPS as (n0 & NOFENCE_SC_PF_STEPS).
            eapply no_scfence_nprm_steps_prsv_memory_closed in NOFENCE_SC_PF_STEPS; eauto.
            eapply rtc_rtcn in NOFENCE_SC_PF_STEPS.
            destruct NOFENCE_SC_PF_STEPS as (n0 & NOFENCE_SC_PF_STEPS).
            eapply no_scfence_nprm_steps_prsv_local_wf in NOFENCE_SC_PF_STEPS; eauto.
          }
          
          eapply promise_consistent_prsv_thread_nprm_step in A23; ss; eauto.
          exploit no_scfence_nprm_step_prsv_memory_closed; eauto.
          econstructor; eauto. 
          ss. eapply promise_step_closed_mem; eauto.
          ss. inv PROMISE. eapply local_wf_promise in PROMISE0; eauto.
          destruct lc; eauto.
          ss. exploit no_scfence_nprm_step_prsv_local_wf; [econstructor; eauto | ss; eauto ..].
          eapply promise_step_closed_mem; eauto.
          inv PROMISE. eapply local_wf_promise in PROMISE0; eauto.
          destruct lc; eauto.
          eapply Local.bot_promise_consistent; eauto.
        }
      }
      {
        eapply pf_step_promise_prsv_or_elim in PF; eauto; ss.
        destruct PF as (e' & NO_SCFENCE_FP_STEPS & CONT).
        destruct CONT as [CONT | CONT]; subst.
        {
          eapply no_scfence_nprm_steps_is_nprm_steps in NO_SCFENCE_FP_STEPS.
          eapply rtcn_rtc in A23.
          do 4 eexists.
          split; [eapply rtc_compose; [eapply NO_SCFENCE_FP_STEPS | eapply A23] | eauto].
        }
        {
          destruct CONT as (from' & msg' & kind' & PROMISE' & ST & SC); subst.
          destruct e'; ss.
          eapply IHn with (lc := local0) (mem := memory0) in A23; eauto.
          destruct A23 as (st0 & lc0 & sc1 & mem0 & STEPS & BOT).
          eapply no_scfence_nprm_steps_is_nprm_steps in NO_SCFENCE_FP_STEPS.
          do 4 eexists.
          split; [eapply rtc_compose; [eapply NO_SCFENCE_FP_STEPS | eapply STEPS] | eauto].
          eapply rtc_rtcn in NO_SCFENCE_FP_STEPS.
          destruct NO_SCFENCE_FP_STEPS as (n0 & NO_SCFENCE_FP_STEPS).
          exploit no_scfence_nprm_steps_prsv_memory_closed; eauto.
          eapply rtc_rtcn in NO_SCFENCE_FP_STEPS.
          destruct NO_SCFENCE_FP_STEPS as (n0 & NO_SCFENCE_FP_STEPS).
          exploit no_scfence_nprm_steps_prsv_local_wf; eauto.
        }

        eapply promise_consistent_prsv_thread_nprm_step in A23; simpl; eauto; simpl.
        inv PF.
        eapply promise_step_closed_mem; eauto.
        inv PROMISE.
        eapply local_wf_promise in PROMISE0; eauto.
        destruct lc; eauto.
        eapply promise_step_closed_mem; eauto.
        inv PF. inv LOCAL.
        eapply local_wf_promise in PROMISE0; eauto.
        eapply promise_step_closed_mem; eauto.
        inv PROMISE.
        eapply local_wf_promise in PROMISE1; eauto; ss.
        destruct lc; eauto.
        eapply Local.bot_promise_consistent; eauto.
      }
    }
    {
      (* Promise free *)
      eapply rtcn_rtc in A23.
      eapply Operators_Properties.clos_rt1n_step in A12.
      do 4 eexists.
      split.
      eapply rtc_compose; [|eapply A23].
      eapply Relation_Operators.rt1n_trans; [|eapply A12].
      eapply Thread.nprm_step_pf_step.
      econstructor; eauto.
      clear - ISPF.
      eapply not_or_and in ISPF.
      des. eapply NNPP in ISPF0.
      destruct kind; ss.
      destruct msg1; ss.
      rewrite ISPF0; ss.
      eauto.
    }
Qed.    
  
Lemma Thread_promise_step_cons_nprm_fulfill:
  forall n lang lo te (e e' e'': Thread.t lang) pf
         (CLOSED_MEM: Memory.closed (Thread.memory e))
         (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
         (PROMISE: Thread.promise_step pf te e e')
         (NPRM_STEPS: rtcn (@Thread.nprm_step lang lo) n e' e'')
         (FULFILL: Local.promises (Thread.local e'') = Memory.bot),
  exists e0, rtc (@Thread.nprm_step lang lo) e e0 /\ Local.promises (Thread.local e0) = Memory.bot.
Proof.
  intros.
  destruct e, e', e''; simpls.
  inv PROMISE.
  eapply Thread_promise_step_cons_nprm_fulfill' in NPRM_STEPS; eauto.
  des.
  eexists.
  split; eauto.
Qed.
  
Lemma tau_steps_fulfill_implies_nprm_steps_fulfill:
  forall n (lang: language) (e e': Thread.t lang) (lo: Ordering.LocOrdMap)
         (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
         (CLOSED_MEM: Memory.closed (Thread.memory e))
         (TAU_STEPS: rtcn (@Thread.tau_step lang lo) n e e')
         (FULFILL: Local.promises (Thread.local e') = Memory.bot),
  exists e0,
    rtc (@Thread.nprm_step lang lo) e e0 /\ Local.promises (Thread.local e0) = Memory.bot.
Proof.
  induction n; intros.
  - inv TAU_STEPS.
    exists e'. split; eauto.
  - inv TAU_STEPS.
    inv A12.
    inv TSTEP.
    inv STEP.
    {
      (* promise step *)
      eapply IHn in A23; eauto.
      destruct A23 as (e1 & NPRM_STEPS & FULFILL').
      eapply rtc_rtcn in NPRM_STEPS. destruct NPRM_STEPS as (n' & NPRM_STEPS).
      eapply Thread_promise_step_cons_nprm_fulfill with (e'' := e1); eauto.
      inv STEP0; simpls.
      inv LOCAL.
      eapply local_wf_promise; eauto.
      destruct lc1; eauto.
      eapply Memory.future_closed with (mem1 := (Thread.memory e)); eauto.
      econstructor; [idtac | eauto].
      inv STEP0.
      inv LOCAL; simpl.
      econstructor.
      eapply Memory.promise_op; eauto.
      eauto.
      inv PROMISE; eauto.
    }
    {
      (* non-promise step *)
      Ltac apply_IHn IHn A :=
        eapply IHn in A; eauto;
        [destruct A as (?e0 & ?NPRM_STEPS & ?FULFILL');
         exists e0;
         split; eauto;
         eapply Relation_Operators.rt1n_trans; [idtac | eapply NPRM_STEPS] | idtac..].
      
      inv STEP0.
      inv LOCAL; simpls.
      {
        (* silent *)
        apply_IHn IHn A23.
        eapply Thread.nprm_step_program_step with (e := ThreadEvent.silent); eauto.
      }
      {
        (* read *)
        apply_IHn IHn A23.
        eapply Thread.nprm_step_program_step.
        econstructor; eauto; simpl.
        eauto. eauto.
        eapply local_wf_read; eauto.
      }
      {
        (* write *)
        apply_IHn IHn A23.
        eapply Thread.nprm_step_program_step.
        econstructor; eauto; simpl; eauto.
        eauto.
        eapply local_wf_write; eauto.
        eapply write_step_closed_mem; eauto.
      }
      {
        (* update *)
        apply_IHn IHn A23.
        eapply Thread.nprm_step_program_step.
        econstructor; eauto; simpl; eauto.
        eauto.
        eapply local_wf_upd; eauto. 
        eapply write_step_closed_mem in LOCAL2; eauto.
        inv LOCAL1.
        eapply closed_mem_implies_closed_msg; eauto.
        eapply local_wf_read; eauto.
      }
      {
        (* fence *)
        inv LOCAL0.
        destruct (Ordering.le Ordering.seqcst ordw) eqn:Hordw_seqcst.
        {
          (* seqcst *)
          destruct ordw; simpl in Hordw_seqcst; tryfalse.
          exploit PROMISES; eauto.
        }
        {
          (* not seqcst *)
          apply_IHn IHn A23; simpl.
          eapply Thread.nprm_step_program_step.
          econstructor; eauto; simpl.
          eauto.
          eauto.
          eapply local_wf_fence_not_seqcst; eauto.
          destruct lc1; simpls; eauto.
        }
      }
      {
        (* output *)
        tryfalse.
      }
    }
Qed.
  
Lemma Thread_consistent_to_consistent_nprm
      (lang: language) (e: Thread.t lang) (lo: Ordering.LocOrdMap)
      (TVIEW_WF: Local.wf (Thread.local e) (Thread.memory e))
      (CLOSED_MEM: Memory.closed (Thread.memory e)):
  Thread.consistent e lo -> Thread.consistent_nprm e lo.
Proof.
  intros.
  unfolds Thread.consistent, Thread.consistent_nprm.
  intros.
  lets FULFILL_NPRM: CAP.
  eapply H in FULFILL_NPRM; simpls; eauto.
  clear - CAP TVIEW_WF CLOSED_MEM FULFILL_NPRM.
  destruct FULFILL_NPRM as (e2 & STEPS & FULFILL_NPRM).
  eapply rtc_rtcn in STEPS. destruct STEPS as (n & STEPS). 
  eapply tau_steps_fulfill_implies_nprm_steps_fulfill in STEPS; eauto; simpls.
  simpl; eauto.
  eapply Local.cap_wf; eauto.
  eapply Memory.cap_closed; eauto.
Qed.

(** construct consistent from fulfill *)
Definition spec_inj (mem: Memory.t) : Mapping :=
  fun loc t =>
    match (Memory.get loc t mem) with
    | Some (from, Message.concrete _ _) => Some t
    | _ => None
    end.

Lemma spec_inj_implies_promises_inj
      promises mem
      (LE: Memory.le promises mem):
  promise_inj (spec_inj mem) promises promises.
Proof.
  econs; eauto; ii.
  {
    exists to released.
    split; eauto. eapply LE in H.
    unfold spec_inj. rewrite H; eauto.
  }
  {
    exists to' released'.
    split; eauto. eapply LE in H.
    unfold spec_inj. rewrite H; eauto.
  }
Qed.
  
Lemma spec_inj_identity_inj loc mem t t'
      (INJ: (spec_inj mem) loc t = Some t'):
  t = t'.
Proof.
  unfolds spec_inj.
  destruct(Memory.get loc t mem) in INJ; ss; eauto.
  destruct p; ss.
  destruct t1; ss.
  inv INJ; ss.
Qed.

Lemma spec_inj_tmapinj mem tm:
  TMapInj (spec_inj mem) tm tm.
Proof.
  unfold TMapInj; ii.
  unfolds spec_inj.
  destruct (Memory.get loc (tm loc) mem); ss.
  destruct p; ss.
  destruct t0; ss.
  inv injDom; ss.
Qed.

Lemma spec_inj_optviewinj mem R:
  opt_ViewInj (spec_inj mem) R R.
Proof.
  destruct R; ss.
  unfold ViewInj. destruct t; ss.
  split; eapply spec_inj_tmapinj.
Qed.

Lemma spec_inj_monotonic mem: 
  monotonic_inj (spec_inj mem).
Proof.
  unfold monotonic_inj; ii.
  unfolds spec_inj.
  destruct (Memory.get loc t1 mem); ss. destruct p; ss. destruct t0; ss. inv INJ1.
  destruct (Memory.get loc t2 mem); ss. destruct p; ss. destruct t1; ss. inv INJ2.
  eauto.
Qed.

Lemma ViewInj_spec_inj_id mem view:
  ViewInj (spec_inj mem) view view.
Proof.
  unfold ViewInj.
  destruct view; ss.
  split; eapply spec_inj_tmapinj.
Qed.

Lemma TViewInj_spec_inj_id mem tview:
  TViewInj (spec_inj mem) tview tview.
Proof.
  unfold TViewInj.
  split; ii. eapply ViewInj_spec_inj_id.
  split; try solve [eapply ViewInj_spec_inj_id].
Qed.

Lemma read_step_consistent_construction
      lang loc to val released ord st1 lc1 sc1 mem1 st2 lc2 lo
      (STATE: Language.step lang (ProgramEvent.read loc val ord) st1 st2)
      (READ: Local.read_step lc1 mem1 loc to val released ord lc2 lo)
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc1 mem1) lo):
  Thread.consistent (Thread.mk lang st1 lc1 sc1 mem1) lo.
Proof.
  unfolds Thread.consistent; ss; ii.
  exploit CONS; eauto.
  ii; des.
  eexists.
  split.
  eapply Relation_Operators.rt1n_trans; [idtac | eapply STEPS].
  econstructor; eauto.
  econstructor.
  eapply Thread.step_program.
  econstructor; ss; eauto.
  ss; eauto.
  instantiate (1 := ThreadEvent.read loc to val released ord).
  ss; eauto.
  econstructor; eauto.
  inv READ; ss.
  econstructor; eauto.
  clear CONS STEPS. inv CAP.
  eapply SOUND; eauto.
  ss; eauto.
  eauto.
Qed.

Lemma write_add_step_consistent_construction
      lang st1 st2 loc val lc1 sc1 mem1
      from to releasedw ord
      lc2 sc2 mem2 lo
      (STATE: Language.step lang (ProgramEvent.write loc val ord) st1 st2)
      (WRITE_ADD: Local.write_step lc1 sc1 mem1 loc from to val None releasedw ord lc2 sc2 mem2
                                   Memory.op_kind_add lo)
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc2 mem2) lo)
      (LOCAL_WF: Local.wf lc1 mem1)
      (MEM_CLOSED: Memory.closed mem1):
  exists e0,
    Thread.reserve_step lo (Thread.mk lang st1 lc1 sc1 mem1) e0 /\
    Thread.consistent e0 lo.
Proof.
  assert(LOCAL_WF': Local.wf lc2 mem2).
  {
    eapply local_wf_write; eauto.
  }
  assert(MEM_CLOSED': Memory.closed mem2).
  {
    eapply write_step_closed_mem; eauto.
  }
  eapply Thread_consistent_to_consistent_nprm in CONS; eauto.
  assert(CAP_EXIST: exists mem2', Memory.cap mem2 mem2').
  {
    eapply Memory.cap_exists; eauto.
  }
  destruct CAP_EXIST as (mem2' & CAP_EXIST). 
  assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem2' sc1').
  {
    eapply Memory.max_concrete_timemap_exists.
    eapply Memory.cap_closed in CAP_EXIST; eauto.
    inv CAP_EXIST; eauto.
  } 
  destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
  destruct(classic (Memory.max_ts loc mem2 = to)).
  {
    (* new message is the max one *)
    inv WRITE_ADD.
    inv WRITE; ss. inv PROMISE; ss.
    assert(LT_MSG_T: Time.lt from (Memory.max_ts loc mem2)).
    {
      inv MEM.
      inv ADD; eauto.
    }
    cut(forall t, Interval.mem (from, (Memory.max_ts loc mem2)) t -> ~ Cover.covered loc t mem1).
    2: eapply MemoryProps.memory_add_cover_disjoint; eauto.
    i. 
    cut(forall t, Interval.mem ((Memory.max_ts loc mem2), Time.incr (Memory.max_ts loc mem2)) t ->
             ~ Cover.covered loc t mem1).
    i.
    assert(NOCOVER: forall t, Interval.mem (from, Time.incr (Memory.max_ts loc mem2)) t -> ~ Cover.covered loc t mem1).
    {
      clear - H H0 LT_MSG_T. i.
      eapply Interval.mem_split with (mb := Memory.max_ts loc mem2) in H1.
      destruct H1; eauto.
      econstructor; ss.
      inv H1; ss.
      eapply Time.le_lteq. left.
      eapply Time.incr_spec.
    }
    clear H H0.
    assert(MEM_ADD: exists mem', Memory.add mem1 loc from (Time.incr (Memory.max_ts loc mem2)) Message.reserve mem').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_MSG_T.
      eapply Time.incr_spec.
      econstructor; eauto.
    }
    destruct MEM_ADD as (mem' & MEM_ADD). 
    assert(PRM_ADD: exists promises',
              Memory.add (Local.promises lc1) loc from (Time.incr (Memory.max_ts loc mem2))
                         Message.reserve promises').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_MSG_T.
      eapply Time.incr_spec.
      econstructor; eauto.
      clear - LOCAL_WF NOCOVER.
      ii.
      eapply NOCOVER in H.
      contradiction H.
      inv LOCAL_WF; eauto.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD as (promises' & PRM_ADD).
    exists (Thread.mk lang st1 (Local.mk (Local.tview lc1) promises') sc1 mem').
    split.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply PRM_ADD.
    eapply MEM_ADD.
    econstructor; eauto.
    ii; des; ss.
    econstructor; eauto.
    ss.
    ss.
    unfold Thread.consistent; ss.
    ii.
    exploit CONS; simpl; [eapply CAP_EXIST | eauto..].
    introv CONS'. destruct CONS' as (e2 & TAU_STEPS & FULFILL).  
    assert(REMOVE_RSV_MEM: 
             exists mem0', Memory.remove mem0 loc from (Time.incr (Memory.max_ts loc mem2)) Message.reserve mem0').
    {
      eapply Memory.remove_exists.
      cut (Memory.get loc (Time.incr (Memory.max_ts loc mem2)) mem' = Some (from, Message.reserve)).
      clear - CAP; ii.
      inv CAP; eauto.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_MEM as (mem0' & REMOVE_RSV_MEM).
    assert(REMOVE_RSV_PRM: exists promises0',
              Memory.remove promises' loc from (Time.incr (Memory.max_ts loc mem2)) Message.reserve promises0').
    {
      eapply Memory.remove_exists.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_PRM as (promises0' & REMOVE_RSV_PRM).
    assert(REMOVE_NOT_COVER: 
             forall t, Interval.mem (from, (Time.incr (Memory.max_ts loc mem2))) t ->
                  ~ Cover.covered loc t mem0').
    {
      eapply Cover.remove_not_cover; eauto.
    }
    assert(PRM_LE: Memory.le promises0' mem0').
    {
      eapply Memory.promise_le with (promises1 := promises') (mem1 := mem0); eauto.
      eapply Memory.cap_le; eauto.
      eapply Memory.promise_le with (promises1 := Local.promises lc1) (mem1 := mem1); eauto.
      inv LOCAL_WF; eauto.
      econstructor; eauto.
      ii; des.
      ss.
    }
    assert(WRITE': exists mem1',
              Memory.write promises0' mem0' loc from (Memory.max_ts loc mem2) val
                           (TView.write_released (Local.tview lc1) sc1 loc (Memory.max_ts loc mem2) None ord)
                           promises0' mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      {
        clear - REMOVE_NOT_COVER. ii.
        eapply REMOVE_NOT_COVER; eauto.
        eapply Interval.le_mem; eauto.
        econstructor; ss.
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
        eapply Time.le_lteq. left.
        eapply Time.incr_spec.
      }
      {
        inv TS; eauto.
      }
      { 
        clear - REMOVE_NOT_COVER LT_MSG_T.
        introv CONTR. inv CONTR; des.
        exploit Memory.get_ts; eauto. i; des; subst.
        rewrite H in LT_MSG_T.
        eapply Time.Time_lt_bot_false in LT_MSG_T; ss. 
        destruct(Time.le_lt_dec x (Time.incr (Memory.max_ts loc mem2))).
        {
          specialize (REMOVE_NOT_COVER x).
          eapply REMOVE_NOT_COVER; eauto.
          econstructor; eauto; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          econstructor; ss; eauto.
          econstructor; ss; eauto.
          eapply Time.le_lteq; eauto.
        }
        {
          specialize (REMOVE_NOT_COVER (Time.incr (Memory.max_ts loc mem2))).
          eapply REMOVE_NOT_COVER; eauto.
          econstructor; ss; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.incr_spec.
          eapply Time.le_lteq; eauto.
          econstructor; eauto.
          econstructor; ss; eauto.
          eapply Time.incr_spec.
          eapply Time.le_lteq; eauto.
        }
      }
      {
        clear - MEM.
        inv MEM. inv ADD; ss.
      }
    }
    destruct WRITE' as (mem1' & WRITE'). 
    assert(PRM_LE': Memory.le promises0' mem1').
    { eapply MemoryProps.write_memory_le; eauto. }
    eapply rtc_rtcn in TAU_STEPS.
    destruct TAU_STEPS as (n & TAU_STEPS). destruct e2.
    assert(LOCAL_WRITE: 
             Local.write_step (Local.mk (Local.tview lc1) promises0') sc0 mem0' loc
                              from (Memory.max_ts loc mem2) val None
                              (TView.write_released (Local.tview lc1) sc1 loc (Memory.max_ts loc mem2) None ord) ord
                              (Local.mk (TView.write_tview (Local.tview lc1) sc1 loc
                                                           (Memory.max_ts loc mem2) ord) promises0')
                              sc0 mem1' Memory.op_kind_add lo).
    {
      econs; ss.
      clear - WRITABLE. inv WRITABLE. econs; eauto.
      eapply WRITE'.
      introv NONSYNC. eapply RELEASE in NONSYNC.
      clear - NONSYNC PRM_ADD REMOVE_RSV_PRM.
      eapply reserve_non_synch_loc in PRM_ADD; eauto.      
      eapply remove_non_synch_loc in REMOVE_RSV_PRM; eauto.
    }
    assert(LOCAL_WF'': Local.wf {| Local.tview := Local.tview lc1; Local.promises := promises0' |} mem0').
    {
      eapply local_wf_promise.
      eapply Memory.promise_cancel. eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM. ss.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      ss.
      eapply Local.cap_wf with (mem1 := mem'); eauto.
      eapply local_wf_promise.
      eapply Memory.promise_add. eapply PRM_ADD. eapply MEM_ADD.
      ss.
      ii; ss.
      ss.
      ss.
      destruct lc1; ss.
    }
    eapply additional_msg_consistent_construction with
        (inj := (spec_inj mem2'))
        (max_ts := Memory.max_ts loc mem2')
        (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem0)) in TAU_STEPS.
    destruct TAU_STEPS as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL').
    {
      eexists. split.
      (* cancel the reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_promise.
      econs.
      econs; ss.
      eapply Memory.promise_cancel.
      eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM.
      ss. ss. ss.
      (* write add *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_program.
      econs.
      instantiate (2 := ThreadEvent.write loc from (Memory.max_ts loc mem2) val
                                          (TView.write_released (Local.tview lc1) sc1 loc (Memory.max_ts loc mem2)
                                                                None ord) ord).
      ss. eapply STATE.
      eapply Local.step_write.
      eapply LOCAL_WRITE.
      ss.
      eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
      ss.
    }  
    {
      (* local wf *)
      eapply Local.cap_wf with (mem1 := mem2); eauto.
    }
    {
      (* local wf *) 
      eapply local_wf_write.
      eapply LOCAL_WRITE.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      eauto.
    }
    {
      (* closed memory *)
      eapply Memory.cap_closed with (mem1 := mem2); eauto.
    }
    {
      (* closed memory *)
      eapply write_step_closed_mem; ss.
      eapply LOCAL_WRITE.
      eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* other identity injection *)
      instantiate (1 := loc).
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max identity injection *)
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max_ts *)
      eapply Time.join_l.
    }
    {
      (* msg injection *)
      econs.
      {
        ii.
        unfold spec_inj at 1. rewrite MSG.
        exists t f R. split; eauto.
        split. eapply spec_inj_optviewinj; eauto.
        assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val0 R)).
        {
          eapply Memory.cap_inv in MSG; eauto.
          des; ss.
        }
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o; eauto.
        des_if.
        {
          ss; des; subst.
          erewrite Memory.add_o in GET1; eauto.
          des_ifH GET1; ss.
          destruct o; ss.
        }
        {
          ss. 
          eapply Memory.concrete_msg_remove_rsv_stable with (mem := mem0); eauto.
          erewrite Memory.add_o with (mem1 := mem1) in GET1; eauto.
          des_ifH GET1; ss. destruct a; subst; ss. destruct o; subst; ss.
          eapply Memory.add_get1 with (m2 := mem') in GET1; eauto.
          clear - CAP GET1.
          inv CAP.
          eapply SOUND; eauto.
        }
      } 
      {
        ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
        destruct t1; ss. inv INJ.
        do 3 eexists. eauto.
      }
      {
        eapply spec_inj_monotonic; eauto.
      }
    }
    {
      (* TView inj *)
      ss. eapply TViewInj_spec_inj_id.
    }
    {
      (* promise eq *)
      ss.
      eapply MemoryMerge.MemoryMerge.add_remove in PRM_ADD; eauto.
      eapply MemoryMerge.MemoryMerge.add_remove in PROMISES; eauto.
      subst; eauto. 
      eapply spec_inj_implies_promises_inj; eauto.
      clear - LOCAL_WF' CAP_EXIST.
      inv LOCAL_WF'; eauto; ss. eapply Memory.cap_le; eauto.
    }
    {
      (* OTHER cover *)
      ii.
      contradiction H0. clear H0.
      inv H1.
      assert(GET1: Memory.get loc0 to mem0' = Some (from0, msg)).
      {  
        clear - WRITE' GET H. 
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
      }
      erewrite Memory.remove_o with (mem1 := mem0) in GET1; eauto.
      des_ifH GET1; ss.
      cut(mem' loc0 = mem2 loc0). ii.
      eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H0; eauto.
      econs.
      unfolds Memory.get.
      rewrite <- H0; eauto.
      ss.
      eapply Memory.add_closed; ss.
      eapply MEM_ADD. ss.
      clear - MEM_ADD MEM H.
      inv MEM_ADD; inv MEM. inv ADD0; inv ADD.
      assert(LocFun.find loc0 (LocFun.add loc r mem1) = LocFun.find loc0 (LocFun.add loc r0 mem1)).
      rewrite LocFun.add_spec_neq; ss. rewrite LocFun.add_spec_neq; ss.
      unfold LocFun.find in *; ss.
    }  
    {
      (* loc0 cover *) 
      clear - MEM_CLOSED' CAP_EXIST. ii.
      exploit Memory.cap_max_ts; eauto.
      instantiate (1 := loc); ii.
      inv H1.
      assert(ts <> Time.bot).
      {
        intro; subst.
        inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
      }
      eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
      contradiction H.
      des; subst.
      eapply CAP_EXIST.
      rewrite H2 in H0.
      econs; ss.
      destruct (Time.le_lt_dec Time.bot ts); eauto.
      eapply Time.le_lteq in l; des; ss. subst; ss.
      eapply Time_lt_bot_false in l; ss.
    }
    { 
      (* spec_view *)
      ss.
      eapply spec_view_intro_le_max_ts.
      {
        exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
        instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
        cut(Time.le (TimeMap.join (View.rlx (TView.acq (Local.tview lc1)))
                                  (TimeMap.singleton loc (Memory.max_ts loc mem2)) loc)
                    (Memory.max_ts loc mem2)).
        ii. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
        eapply Time.incr_spec.
        eapply Time.join_spec.
        {
          clear - LOCAL_WF MEM.
          inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
          inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
          specialize (RLX loc). des.
          eapply Memory.add_get1 in RLX; eauto.
          eapply Memory.max_ts_spec in RLX; des; ss.
        }
        {
          unfold TimeMap.singleton.
          cut(LocFun.find loc (LocFun.add loc (Memory.max_ts loc mem2) (LocFun.init Time.bot)) =
              Memory.max_ts loc mem2). ii.
          unfolds LocFun.find. rewrite H. eapply Time.le_lteq; eauto.
          rewrite LocFun.add_spec_eq; eauto.
        }
      }
      {
        eapply Cover.gt_max_not_covered.
      }
      {
        ii. inv H0. inv WRITE'. inv PROMISE. 
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; ss.
        {
          destruct a; subst. inv GET.
          eapply Time.Time_lt_join in H; destruct H.
          exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
          instantiate (1 := loc); introv MAX_TS.
          clear - H ITV MAX_TS.
          rewrite MAX_TS in H. inv ITV; ss.
          cut(Time.lt (Memory.max_ts loc mem2) ts'); ii. 
          eapply Time.Time_le_gt_false in TO; ss.
          cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.incr_spec.
        }
        {
          erewrite Memory.remove_o in GET; eauto.
          des_ifH GET; ss.
          eapply Time.Time_lt_join in H; destruct H.
          clear - H0 ITV GET. inv ITV; ss. eapply Memory.max_ts_spec in GET; des.
          cut(Time.lt to ts'); ii.
          eapply Time.Time_le_gt_false; eauto. 
          eapply TimeFacts.le_lt_lt; eauto.
        }
      }
    }
    {
      (* max cover *)
      clear - CAP_EXIST MEM_CLOSED'.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      inv CAP_EXIST.
      specialize (BACK loc).
      rewrite H; eauto.
    }
    {
      (* promise le *)
      ss.
      clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
      inv LOCAL_WF'; ss; ii.
      eapply PROMISES in H.
      eapply Memory.max_ts_spec in H; eauto; des.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      rewrite H.
      cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    {
      (* FULFill *)
      ss.
    }
    clear - MEM. ii.
    inv H0.
    eapply Memory.add_get1 in GET; eauto.
    eapply Memory.max_ts_spec in GET; des.
    inv ITV; ss.
    inv H; ss.
    cut(Time.lt to t). ii.
    eapply Time_le_gt_false in TO; ss.
    eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto.
  }
  {
    (* new message is not the max one *)
    inv WRITE_ADD.
    inv WRITE; ss. inv PROMISE; ss.
    assert(NOT_COVER1: forall t, Interval.mem (from, to) t -> ~ Cover.covered loc t mem1).
    {
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    }
    lets GET: MEM.
    eapply Memory.add_get0 in GET. destruct GET as [ _ GET]. 
    exploit Memory.next_exists; [eapply GET | idtac..]. instantiate (1 := to).
    {
      eapply Memory.max_ts_spec in GET; des.
      eapply Time.le_lteq in MAX. destruct MAX; subst; ss.
    }
    introv NEXT.
    destruct NEXT as (from0 & to0 & msg0 & GET_NEXT & NEXT & WF_NEXT).
    assert(LT_ADD: Time.lt from to).
    {
      eapply MemoryProps.add_succeed_wf in MEM; des; ss.
    }
    assert(LE_ORIGIN_MSG: Time.lt from0 to0).
    {
      eapply Memory.get_ts in GET_NEXT.
      des; subst; ss.
      eapply Time.Time_lt_bot_false in NEXT; eauto; ss.
    }
    assert(GET_NEXT_PRSV: Memory.get loc to0 mem1 = Some (from0, msg0)).
    {
      erewrite Memory.add_o in GET_NEXT; eauto.
      des_ifH GET_NEXT; ss; des; subst.
      eapply Time.Time.lt_strorder_obligation_1 in NEXT; ss.
    }
    assert(IS_NEXT: Time.lt to from0).
    {
      exploit Memory.get_disjoint; [eapply GET_NEXT | eapply GET | eauto..].
      clear - H GET GET_NEXT NEXT ATTACH LT_ADD GET_NEXT_PRSV. ii.
      des. subst.
      {
        eapply Time.Time.lt_strorder_obligation_1 in NEXT; ss.
      }
      {
        destruct (Time.le_lt_dec from0 to); eauto.
        eapply Time.le_lteq in l. des; subst.
        unfold Interval.disjoint in H0. specialize (H0 to).
        exploit H0; ii; ss.  
        econs; ss; eauto. eapply Time.le_lteq; eauto. 
        econs; ss; eauto. 
        eapply Time.le_lteq; eauto.
        eapply ATTACH in GET_NEXT_PRSV; eauto; ss.
      }
    }
    assert(NOT_COVER2: forall t, Interval.mem (to, from0) t -> ~ Cover.covered loc t mem1).
    {  
      clear - GET_NEXT_PRSV NEXT WF_NEXT IS_NEXT LE_ORIGIN_MSG MEM. ii.
      inv H0.
      destruct(Time.le_lt_dec to0 to1).
      {
        eapply Time.le_lteq in l; des; subst.
        {
          exploit Memory.get_disjoint; [eapply GET_NEXT_PRSV | eapply GET | eauto..]. ii; des; subst.
          eapply Time.Time.lt_strorder_obligation_1 in l; ss.
          destruct(Time.le_lt_dec to0 from1).
          clear - LE_ORIGIN_MSG H l0 ITV.
          inv H; ss. inv ITV; ss.
          cut(Time.le t to0); ii.
          cut(Time.lt to0 t); ii. 
          eapply Time_le_gt_false; eauto.
          eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto.
          eapply Time.le_lteq. left.
          eapply DenseOrder.DenseOrderFacts.le_lt_lt with (b := from0); eauto.
          eapply H0 with (x := to0).
          econs; ss; eauto. eapply Time.le_lteq; eauto.
          econs; ss; eauto. eapply Time.le_lteq; eauto.
        }
        {
          inv H; ss.
          rewrite GET_NEXT_PRSV in GET; inv GET.
          inv ITV; ss. eapply Time_le_gt_false in TO; eauto.
        }
      }
      {
        inv H. inv ITV; ss. 
        eapply WF_NEXT in l; eauto.
        erewrite Memory.add_o in l; eauto.
        des_ifH l; ss.
        rewrite GET in l; ss.
        eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto.
      }
    }
    assert(NOT_COVER3: forall t, Interval.mem (from, from0) t -> ~ Cover.covered loc t mem1).
    {
      clear - NOT_COVER1 LT_ADD NOT_COVER2 IS_NEXT. ii. 
      eapply Interval.mem_split with (mb := to) in H; eauto.
      destruct H; eauto.
      eapply NOT_COVER1; eauto. eapply NOT_COVER2; eauto.
      econs; ss. eapply Time.le_lteq; eauto.
    }
    assert(MEM_ADD: exists mem', Memory.add mem1 loc from from0 Message.reserve mem').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_ADD. eapply IS_NEXT.
      econstructor; eauto.
    }
    destruct MEM_ADD as (mem' & MEM_ADD).
    assert(PRM_ADD: exists promises',
              Memory.add (Local.promises lc1) loc from from0
                         Message.reserve promises').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2; eauto.
      econstructor.
      clear - LOCAL_WF NOT_COVER3.
      ii.
      eapply NOT_COVER3 in H.
      contradiction H.
      inv LOCAL_WF; eauto.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD as (promises' & PRM_ADD).
    exists (Thread.mk lang st1 (Local.mk (Local.tview lc1) promises') sc1 mem').
    split.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply PRM_ADD.
    eapply MEM_ADD.
    econstructor; eauto.
    ii; des; ss.
    econstructor; eauto.
    ss.
    ss.
    unfold Thread.consistent; ss.
    ii. 
    exploit CONS; simpl; [eapply CAP_EXIST | eauto..].
    introv CONS'. destruct CONS' as (e2 & TAU_STEPS & FULFILL).  
    assert(REMOVE_RSV_MEM: 
             exists mem0', Memory.remove mem0 loc from from0 Message.reserve mem0').
    {
      eapply Memory.remove_exists.
      cut (Memory.get loc from0 mem' = Some (from, Message.reserve)).
      clear - CAP; ii.
      inv CAP; eauto.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_MEM as (mem0' & REMOVE_RSV_MEM).
    assert(REMOVE_RSV_PRM: exists promises0',
              Memory.remove promises' loc from from0 Message.reserve promises0').
    {
      eapply Memory.remove_exists.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_PRM as (promises0' & REMOVE_RSV_PRM).
    assert(REMOVE_NOT_COVER: 
             forall t, Interval.mem (from, from0) t -> ~ Cover.covered loc t mem0').
    {
      eapply Cover.remove_not_cover; eauto.
    }
    assert(PRM_LE: Memory.le promises0' mem0').
    {
      eapply Memory.promise_le with (promises1 := promises') (mem1 := mem0); eauto.
      eapply Memory.cap_le; eauto.
      eapply Memory.promise_le with (promises1 := Local.promises lc1) (mem1 := mem1); eauto.
      inv LOCAL_WF; eauto.
      econstructor; eauto.
      ii; des.
      ss.
    }
    assert(WRITE': exists mem1',
              Memory.write promises0' mem0' loc from to val
                           (TView.write_released (Local.tview lc1) sc1 loc to None ord)
                           promises0' mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      {
        clear - REMOVE_NOT_COVER IS_NEXT. ii.
        eapply REMOVE_NOT_COVER; eauto.
        eapply Interval.le_mem; eauto.
        econstructor; ss.
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
        eapply Time.le_lteq. eauto.
      }
      {
        inv TS; eauto.
      }
      {
        clear - LT_ADD LE_ORIGIN_MSG IS_NEXT REMOVE_NOT_COVER.
        introv CONTR. inv CONTR. des.
        destruct(Time.le_lt_dec x from0).
        {
          specialize (REMOVE_NOT_COVER x).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD; ss.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
        {
          specialize (REMOVE_NOT_COVER from0).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.le_lteq. eauto.
          econs; ss; eauto.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
      }
      {
        clear - MEM.
        inv MEM. inv ADD; ss.
      }
    }
    destruct WRITE' as (mem1' & WRITE'). 
    assert(PRM_LE': Memory.le promises0' mem1').
    { eapply MemoryProps.write_memory_le; eauto. }
    eapply rtc_rtcn in TAU_STEPS.
    destruct TAU_STEPS as (n & TAU_STEPS). destruct e2.
    assert(LOCAL_WRITE: 
             Local.write_step (Local.mk (Local.tview lc1) promises0') sc0 mem0' loc
                              from to val None
                              (TView.write_released (Local.tview lc1) sc1 loc to None ord) ord
                              (Local.mk (TView.write_tview (Local.tview lc1) sc1 loc to ord) promises0')
                              sc0 mem1' Memory.op_kind_add lo).
    {
      econs; ss.
      clear - WRITABLE. inv WRITABLE. econs; eauto.
      eapply WRITE'.
      introv NONSYNC. eapply RELEASE in NONSYNC.
      clear - NONSYNC PRM_ADD REMOVE_RSV_PRM.
      eapply reserve_non_synch_loc in PRM_ADD; eauto.      
      eapply remove_non_synch_loc in REMOVE_RSV_PRM; eauto.
    }
    assert(ADD_LT_MAX: Time.lt to (Memory.max_ts loc mem2)).
    {
      eapply Memory.add_get0 in MEM; eauto.
      clear - MEM H. des.
      eapply Memory.max_ts_spec in GET0. des.
      eapply Time.le_lteq in MAX; des; subst; ss.
    }
    assert(LOCAL_WF'': Local.wf {| Local.tview := Local.tview lc1; Local.promises := promises0' |} mem0').
    {
      eapply local_wf_promise.
      eapply Memory.promise_cancel. eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM. ss.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      ss.
      eapply Local.cap_wf with (mem1 := mem'); eauto.
      eapply local_wf_promise.
      eapply Memory.promise_add. eapply PRM_ADD. eapply MEM_ADD.
      ss.
      ii; ss.
      ss.
      ss.
      destruct lc1; ss.
    }
    eapply additional_msg_consistent_construction with
        (inj := (spec_inj mem2'))
        (max_ts := Memory.max_ts loc mem2')
        (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem0)) in TAU_STEPS.
    destruct TAU_STEPS as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL').
    {
      eexists. split.
      (* cancel the reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_promise.
      econs.
      econs; ss.
      eapply Memory.promise_cancel.
      eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM.
      ss. ss. ss.
      (* write add *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_program.
      econs.
      instantiate (2 := ThreadEvent.write loc from to val
                                          (TView.write_released (Local.tview lc1) sc1 loc to None ord) ord).
      ss. eapply STATE.
      eapply Local.step_write.
      eapply LOCAL_WRITE.
      ss.
      eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
      ss.
    }
    {
      (* local wf *)
      eapply Local.cap_wf with (mem1 := mem2); eauto.
    }
    {
      (* local wf *) 
      eapply local_wf_write.
      eapply LOCAL_WRITE.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      eauto.
    }
    {
      (* closed memory *)
      eapply Memory.cap_closed with (mem1 := mem2); eauto.
    }
    {
      (* closed memory *)
      eapply write_step_closed_mem; ss.
      eapply LOCAL_WRITE.
      eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* other identity injection *)
      instantiate (1 := loc).
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max identity injection *)
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max_ts *)
      eapply Time.join_l.
    }
    {
      (* msg injection *)
      econs.
      {
        ii.
        unfold spec_inj at 1. rewrite MSG.
        exists t f R. split; eauto.
        split. eapply spec_inj_optviewinj; eauto.
        assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val0 R)).
        {
          eapply Memory.cap_inv in MSG; eauto.
          des; ss.
        }
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o; eauto.
        des_if.
        {
          ss; des; subst.
          erewrite Memory.add_o in GET1; eauto.
          des_ifH GET1; ss.
          destruct o; ss.
        }
        {
          ss. 
          eapply Memory.concrete_msg_remove_rsv_stable with (mem := mem0); eauto.
          erewrite Memory.add_o with (mem1 := mem1) in GET1; eauto.
          des_ifH GET1; ss. destruct a; subst; ss. destruct o; subst; ss.
          eapply Memory.add_get1 with (m2 := mem') in GET1; eauto.
          clear - CAP GET1.
          inv CAP.
          eapply SOUND; eauto.
        }
      }
      {
        ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
        destruct t1; ss. inv INJ.
        do 3 eexists. eauto. 
      }
      {
        eapply spec_inj_monotonic; eauto.
      }
    }
    {
      (* TView inj *)
      ss. eapply TViewInj_spec_inj_id.
    }
    {
      (* promise eq *)
      ss.
      eapply MemoryMerge.MemoryMerge.add_remove in PRM_ADD; eauto.
      eapply MemoryMerge.MemoryMerge.add_remove in PROMISES; eauto.
      subst; eauto.
      eapply spec_inj_implies_promises_inj; eauto.
      clear - LOCAL_WF' CAP_EXIST.
      inv LOCAL_WF'; eauto; ss. eapply Memory.cap_le; eauto.
    }
    {
      (* OTHER COVER *)
      ii.
      contradiction H1. clear H1.
      inv H2. 
      assert(GET1: Memory.get loc0 to1 mem0' = Some (from1, msg)).
      {     
        clear - WRITE' GET0 H0. 
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o in GET0; eauto.
        des_ifH GET0; subst; des; ss.
      }
      erewrite Memory.remove_o with (mem1 := mem0) in GET1; eauto.
      des_ifH GET1; ss.
      cut(mem' loc0 = mem2 loc0). ii.
      eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H1; eauto.
      econs.
      unfolds Memory.get.
      rewrite <- H1; eauto.
      ss.
      eapply Memory.add_closed; ss.
      eapply MEM_ADD. ss. 
      clear - MEM_ADD MEM H0.
      inv MEM_ADD; inv MEM. inv ADD0; inv ADD.
      assert(LocFun.find loc0 (LocFun.add loc r mem1) = LocFun.find loc0 (LocFun.add loc r0 mem1)).
      rewrite LocFun.add_spec_neq; ss. rewrite LocFun.add_spec_neq; ss.
      unfold LocFun.find in *; ss.
    }
    {
      (* loc0 cover *) 
      clear - MEM_CLOSED' CAP_EXIST. ii.
      exploit Memory.cap_max_ts; eauto.
      instantiate (1 := loc); ii.
      inv H1.
      assert(ts <> Time.bot).
      {
        intro; subst.
        inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
      }
      eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
      contradiction H.
      des; subst.
      eapply CAP_EXIST.
      rewrite H2 in H0.
      econs; ss.
      destruct (Time.le_lt_dec Time.bot ts); eauto.
      eapply Time.le_lteq in l; des; ss. subst; ss.
      eapply Time_lt_bot_false in l; ss.
    }
    { 
      (* spec view *)
      ss. 
      eapply spec_view_intro_le_max_ts.
      {
        exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
        instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
        cut(Time.le (TimeMap.join (View.rlx (TView.acq (Local.tview lc1)))
                                  (TimeMap.singleton loc to) loc)
                    (Memory.max_ts loc mem2)).
        ii. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; [eapply H0 | idtac ..].
        eapply Time.incr_spec.
        eapply Time.join_spec.
        {
          clear - LOCAL_WF MEM.
          inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
          inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
          specialize (RLX loc). des.
          eapply Memory.add_get1 in RLX; eauto.
          eapply Memory.max_ts_spec in RLX; des; ss.
        }
        {
          unfold TimeMap.singleton.
          cut(LocFun.find loc (LocFun.add loc to (LocFun.init Time.bot)) = to). ii.
          unfolds LocFun.find. rewrite H0. eapply Time.le_lteq; eauto.
          rewrite LocFun.add_spec_eq; eauto.
        }
      }
      {
        eapply Cover.gt_max_not_covered.
      }
      { 
        ii. eapply Time_lt_join in H0. destruct H0. inv H1.
        inv LOCAL_WRITE; ss. inv LC2. inv WRITE. inv PROMISE.
        erewrite Memory.add_o in GET0; eauto.
        des_ifH GET0; ss.
        {
          des; subst. inv GET0.
          clear - CAP_EXIST H0 ITV ADD_LT_MAX MEM_CLOSED'.
          inv ITV; ss.
          eapply Memory.cap_max_ts in CAP_EXIST; eauto.
          rewrite CAP_EXIST in H0.
          cut(Time.lt to ts'); ii.
          eapply Time_le_gt_false in TO; eauto.
          eapply Time.Time.lt_strorder_obligation_2. eapply ADD_LT_MAX.
          eapply Time.Time.lt_strorder_obligation_2. 2: eapply H0.
          eapply Time.incr_spec.
        }
        {
          destruct o; ss. 
          clear - H2 REMOVE_RSV_MEM H1 GET0 ITV.
          erewrite Memory.remove_o in GET0; eauto.
          des_ifH GET0; ss; des; subst; ss.
          eapply Memory.max_ts_spec in GET0; des.
          inv ITV; ss.
          cut(Time.lt (Memory.max_ts loc mem0) to1). ii.
          eapply Time_le_gt_false in MAX; eauto.
          eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto.
        }
      }
    }
    {
      (* max cover *)
      clear - CAP_EXIST MEM_CLOSED'.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      inv CAP_EXIST.
      specialize (BACK loc).
      rewrite H; eauto.
    }
    {
      (* promise le *)
      ss.
      clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
      inv LOCAL_WF'; ss; ii.
      eapply PROMISES in H.
      eapply Memory.max_ts_spec in H; eauto; des.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      rewrite H.
      cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    {
      (* FULFill *)
      ss.
    }
  }
Qed.

Lemma write_not_add_cap_exit
      mem1 mem1' lc1 sc1
      mem2 mem2' lc2 sc2 sc
      loc from to val releasedr releasedw ord kind lo
      (LE: Memory.le (Local.promises lc1) mem1)
      (WRITE: Local.write_step lc1 sc1 mem1 loc from to val releasedr releasedw ord lc2 sc2 mem2 kind lo)
      (CAP1: Memory.cap mem1 mem1')
      (CAP2: Memory.cap mem2 mem2')
      (CLOSED: Memory.closed mem1)
      (NOT_ADD: kind <> Memory.op_kind_add):
  exists mem', Local.write_step lc1 sc mem1' loc from to val releasedr releasedw ord lc2 sc mem' kind lo.
Proof.
  inv WRITE.
  inv WRITE0.
  assert(Memory.le (Local.promises lc1) mem1').
  {
    inv CAP1. clear - LE SOUND.
    unfolds Memory.le; ii. eauto.
  }
  inv PROMISE; ss.
  - (* split *)
    des; subst; ss. inv RESERVE. 
    exploit Memory.split_exists_le; [eapply H | eauto..]. ii.
    des.
    exists mem0.
    econs; eauto. 
    econs; eauto. inv WRITABLE; eauto.
    econs; eauto.
    unfolds TView.write_released.
    econs; eauto.
  - (* lower *)
    des; subst; ss. 
    exploit Memory.lower_exists_le; [eapply H | eauto..]. ii.
    des.
    exists mem0.
    econs; eauto.
    inv WRITABLE; econs; eauto.
Qed.

Lemma write_step_not_add_cap_get_stable
      lc sc mem loc to from val R loc' from' to' val' releasedr releasedw
      lc' sc' mem' kind ord lo
      mem1 mem1' sc1 sc1'
      (GET: Memory.get loc to mem' = Some (from, Message.concrete val R))
      (WRITE: Local.write_step lc sc mem loc' from' to' val' releasedr releasedw ord lc' sc' mem' kind lo)
      (NOT_ADD: kind <> Memory.op_kind_add)
      (CLOSED: Memory.closed mem)
      (CAP: Memory.cap mem mem1)
      (WRITE': Local.write_step lc sc1 mem1 loc' from' to' val' releasedr releasedw ord lc' sc1' mem1' kind lo):
  Memory.get loc to mem1' = Some (from, Message.concrete val R).
Proof.
  destruct kind; ss.
  Focus 3. inv WRITE. inv WRITE0. inv PROMISE. ss.
  {
    (* split *)
    inv WRITE. inv WRITE'. inv LC2. inv RELEASED.
    inv WRITE0. inv WRITE.
    inv PROMISE. inv PROMISE0. des; ss; subst; ss.
    inv RESERVE0. inv RESERVEORIGINAL0. inv RESERVE.
    clear - GET CLOSED CAP MEM MEM0.
    erewrite Memory.split_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss.
    {
      inv GET.
      eapply Memory.split_get0 in MEM0. des.
      rewrite GET1; ss.
    }
    des_ifH GET; ss; des; ss.
    {
      inv CAP. eapply SOUND in GET.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
    }
    {
      inv CAP. eapply SOUND in GET.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
    }
    {
      des_ifH GET; ss; des; subst; ss. inv GET.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      inv CAP.
      eapply SOUND in GET.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
      inv CAP.
      eapply SOUND in GET.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
      des_if; ss; des; ss.
    }
  }
  {
    (* lower *)
    inv WRITE. inv WRITE'. inv LC2. inv WRITE0. inv WRITE.
    inv PROMISE. inv PROMISE0. des; ss; subst; ss.
    inv RESERVE0. inv RELEASED.
    clear - GET CLOSED CAP MEM MEM0. 
    erewrite Memory.lower_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss. inv GET.
    {
      eapply Memory.lower_get0 in MEM0. des.
      rewrite GET0; ss.
    }
    {
      inv CAP. eapply SOUND in GET.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; ss.
    }
    {
      inv CAP. eapply SOUND in GET.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; ss.
    }
  }
Qed.

Lemma lower_PF_cap_get_stable
      lc mem loc to from val R loc' from' to' val0 val' released
      lc' mem' mem1 mem1' 
      (GET: Memory.get loc to mem' = Some (from, Message.concrete val R))
      (WRITE: Local.promise_step lc mem loc' from' to' (Message.concrete val0 None) lc' mem'
                                 (Memory.op_kind_lower (Message.concrete val' released)))
      (CLOSED: Memory.closed mem)
      (CAP: Memory.cap mem mem1)
      (WRITE': Local.promise_step lc mem1 loc' from' to' (Message.concrete val0 None) lc' mem1'
                                  (Memory.op_kind_lower (Message.concrete val' released))):
  Memory.get loc to mem1' = Some (from, Message.concrete val R).
Proof.
  inv WRITE. inv WRITE'. inv LC2. 
  inv PROMISE. inv PROMISE0. des; ss; subst; ss.
  inv RESERVE0.
  clear - GET CLOSED CAP MEM MEM0. 
  erewrite Memory.lower_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss. inv GET.
  {
    eapply Memory.lower_get0 in MEM0. des.
    rewrite GET0; ss.
  }
  {
    inv CAP. eapply SOUND in GET.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; ss.
  }
  {
    inv CAP. eapply SOUND in GET.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; ss.
  }
Qed.
  
Lemma write_not_add_step_consistent_construction
      lang st1 st2 loc val lc1 sc1 mem1
      from to releasedw ord kind
      lc2 sc2 mem2 lo
      (STATE: Language.step lang (ProgramEvent.write loc val ord) st1 st2)
      (WRITE: Local.write_step lc1 sc1 mem1 loc from to val None releasedw ord lc2 sc2 mem2 kind lo)
      (NOADD: kind <> Memory.op_kind_add)
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc2 mem2) lo)
      (LOCAL_WF: Local.wf lc1 mem1)
      (MEM_CLOSED: Memory.closed mem1):
  Thread.consistent (Thread.mk lang st1 lc1 sc1 mem1) lo.
Proof.
  assert(LOCAL_WF': Local.wf lc2 mem2).
  {
    eapply local_wf_write; eauto.
  }
  assert(MEM_CLOSED': Memory.closed mem2).
  {
    eapply write_step_closed_mem; [idtac | eapply WRITE | eauto..]. ss.
  }
  eapply Thread_consistent_to_consistent_nprm in CONS; eauto.
  assert(CAP_EXIST: exists mem2', Memory.cap mem2 mem2').
  {
    eapply Memory.cap_exists; eauto.
  }
  destruct CAP_EXIST as (mem2' & CAP_EXIST). 
  assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem2' sc1').
  {
    eapply Memory.max_concrete_timemap_exists.
    eapply Memory.cap_closed in CAP_EXIST; eauto.
    inv CAP_EXIST; eauto.
  } 
  destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
  lets CONS': MAX_CONCRETE_TM_EXIT.
  eapply CONS in CONS'; ss; eauto.
  destruct CONS' as (e2 & CONS' & FULFILL').
  unfold Thread.consistent; ss; ii. 
  exploit write_not_add_cap_exit; [idtac | eapply WRITE | eauto..].
  inv LOCAL_WF; eauto. instantiate (1 := sc0). introv WRITE'.
  destruct WRITE' as (mem' & WRITE').
  assert(LOCAL_WF'': Local.wf lc2 mem').
  {
    eapply local_wf_write; eauto.
    eapply Memory.cap_closed; eauto.
    eapply Local.cap_wf; eauto.
  }
  assert(CLOSED_MEM'': Memory.closed mem').
  {
    eapply write_step_closed_mem; eauto.
    eapply Local.cap_wf; eauto.
    eapply Memory.cap_closed; eauto.
  }
  eapply rtc_rtcn in CONS'. destruct CONS' as (n & CONS').
  destruct e2. 
  eapply additional_msg_consistent_construction with
      (inj := (spec_inj mem2'))
      (max_ts := Memory.max_ts loc mem2')
      (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem')) in CONS'.
  destruct CONS' as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL'').
  {
    (* write *)
    eexists. split.
    eapply Relation_Operators.rt1n_trans.
    econs.
    econs.
    eapply Thread.step_program.
    econs.
    instantiate (2 := ThreadEvent.write loc from to val
                                        (TView.write_released (Local.tview lc1) sc1 loc to None ord) ord).
    ss. eapply STATE.
    econs. lets RELEASE: WRITE'. inv RELEASE; subst. eauto.
    ss; eauto.
    eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
    ss.
  }
  {
    (* local wf *)
    eapply Local.cap_wf with (mem1 := mem2); eauto.
  }
  {
    (* local wf *) 
    eauto.
  }
  {
    (* closed memory *)
    eapply Memory.cap_closed with (mem1 := mem2); eauto.
  }
  {
    (* closed memory *)
    eauto.
  }
  {
    (* other identity injection *)
    instantiate (1 := loc).
    ii; eapply spec_inj_identity_inj; eauto.
  }
  {
    (* le max identity injection *)
    ii; eapply spec_inj_identity_inj; eauto.
  }
  {
    (* le max_ts *)
    eapply Time.join_l.
  }
  {
    (* msg injection *)
    econs.
    {
      ii.
      unfold spec_inj at 1. rewrite MSG.
      assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val0 R)).
      { 
        eapply Memory.cap_inv with (mem1 := mem2) in MSG; eauto.
        des; ss.
      }
      exploit write_step_not_add_cap_get_stable; [eapply GET1 | eapply WRITE | eauto..].
      ii.
      exists t f R. split; eauto. split; eauto.
      eapply spec_inj_optviewinj; eauto.
    }
    {
      ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
      destruct t1; ss. inv INJ.
      do 3 eexists. eauto. 
    }
    {
      eapply spec_inj_monotonic; eauto.
    }
  }
  {
    (* TView inj *)
    ss. eapply TViewInj_spec_inj_id.
  }
  {
    (* promise eq *)
    eapply spec_inj_implies_promises_inj; eauto.
    clear - LOCAL_WF' CAP_EXIST.
    inv LOCAL_WF'; eauto; ss. eapply Memory.cap_le; eauto.
  }
  { 
    ii.
    contradiction H0. clear H0.
    inv H1.
    econs; eauto. instantiate (1 := msg).
    assert(GET1: Memory.get loc0 to0 mem0 = Some (from0, msg)).
    {     
      clear - WRITE' GET H NOADD. 
      inv WRITE'. inv WRITE. inv PROMISE; des; subst; ss.
      inv RESERVE.
      erewrite Memory.split_o in GET; eauto.
      des_ifH GET; subst; des; ss.
      des_ifH GET; subst; des; ss.
      des_ifH GET; subst; des; ss.
      erewrite Memory.lower_o in GET; eauto.
      des_ifH GET; subst; des; ss.
    }
    cut(mem1 loc0 = mem2 loc0). ii.   
    eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H0; eauto.
    unfolds Memory.get. rewrite <- H0; eauto.
    clear - WRITE H NOADD.
    inv WRITE. inv WRITE0. inv PROMISE; des; ss; subst; ss.
    inv RESERVE.
    inv MEM. inv SPLIT.
    assert(LocFun.find loc0 (LocFun.add loc r mem1) = mem1 loc0).
    rewrite LocFun.add_spec_neq; ss.
    unfold LocFun.find in *; ss.
    inv MEM. inv LOWER.
    assert(LocFun.find loc0 (LocFun.add loc r mem1) = mem1 loc0).
    rewrite LocFun.add_spec_neq; ss.
    unfold LocFun.find in *; ss.
  }
  {
    (* loc covered *)
    clear - MEM_CLOSED' CAP_EXIST. ii.
    exploit Memory.cap_max_ts; eauto.
    instantiate (1 := loc); ii.
    inv H1.
    assert(ts <> Time.bot).
    {
      intro; subst.
      inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
    }
    eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
    contradiction H.
    des; subst.
    eapply CAP_EXIST.
    rewrite H2 in H0.
    econs; ss.
    destruct (Time.le_lt_dec Time.bot ts); eauto.
    eapply Time.le_lteq in l; des; ss. subst; ss.
    eapply Time_lt_bot_false in l; ss.
  }
  {
    (* spec view *)
    eapply spec_view_intro_le_max_ts.
    { 
      exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
      instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS. 
      cut(Time.le (View.rlx (TView.acq (Local.tview lc2)) loc)
                  (Memory.max_ts loc mem2)).
      ii. eapply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
      eapply Time.incr_spec.
      clear - LOCAL_WF WRITE NOADD.
      inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
      inv WRITE. inv WRITE0. inv PROMISE; des; subst; ss.
      {
        (* split *)
        inv RESERVE.
        inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
        specialize (RLX loc). des.
        eapply Memory.split_get1 in RLX; eauto. des.
        eapply Memory.max_ts_spec in GET2; des; ss.
        eapply Time.join_spec; eauto.
        unfold TimeMap.singleton.
        cut(LocFun.find loc (LocFun.add loc to (LocFun.init Time.bot)) = to). ii.
        unfolds LocFun.find. rewrite H.
        eapply Memory.split_get0 in MEM. des.
        eapply Memory.max_ts_spec in GET2; des; eauto.
        rewrite LocFun.add_spec_eq; eauto.
      }
      {
        (* lower *)
        inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
        specialize (RLX loc). des.
        eapply Memory.lower_get1 in RLX; eauto. des.
        eapply Memory.max_ts_spec in GET2; des; ss.
        eapply Time.join_spec; eauto.
        unfold TimeMap.singleton.
        cut(LocFun.find loc (LocFun.add loc to (LocFun.init Time.bot)) = to). ii.
        unfolds LocFun.find. rewrite H.
        eapply Memory.lower_get0 in MEM. des.
        eapply Memory.max_ts_spec in GET1; des; eauto.
        rewrite LocFun.add_spec_eq; eauto.
      }
    }
    {
      eapply Cover.gt_max_not_covered.
    }
    {  
      ii. eapply Time_lt_join in H. destruct H. inv H0.
      inv WRITE'. inv WRITE0. inv PROMISE; des; subst; ss. inv RESERVE.
      {
        (* split *)
        eapply Memory.max_ts_spec in GET; des.
        clear - H1 MAX ITV.
        inv ITV; ss.  
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2 in TO; eauto.
        eapply TO in MAX.
        eapply Time_le_gt_false in MAX; eauto. 
      }
      {
        (* lower *)
        eapply Memory.max_ts_spec in GET; des.
        clear - H1 MAX ITV.
        inv ITV; ss.  
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2 in TO; eauto.
        eapply TO in MAX.
        eapply Time_le_gt_false in MAX; eauto. 
      }
    }
  }
  {
    (* max cover *)
    clear - CAP_EXIST MEM_CLOSED'.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
    inv CAP_EXIST.
    specialize (BACK loc).
    rewrite H; eauto.
  }
  {
    (* promise le *)
    ss.
    clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
    inv LOCAL_WF'; ss; ii.
    eapply PROMISES in H.
    eapply Memory.max_ts_spec in H; eauto; des.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
    rewrite H.
    cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
  {
    (* FULFill *)
    ss.
  }
Qed.

Lemma update_add_step_consistent_construction
      lang st1 loc valr valw lc1 sc1 mem1
      tsr tsw releasedr releasedw ordr ordw
      lc1' st2 lc2 sc2 mem2 lo
      (STATE: Language.step lang (ProgramEvent.update loc valr valw ordr ordw) st1 st2)
      (READ: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc1' lo)
      (WRITE_ADD: Local.write_step lc1' sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc2 sc2 mem2
                                   Memory.op_kind_add lo)
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc2 mem2) lo)
      (ATOMIC_LOC: lo loc = Ordering.atomic)
      (LOCAL_WF: Local.wf lc1 mem1)
      (MEM_CLOSED: Memory.closed mem1):
  exists e0,
    Thread.reserve_step lo (Thread.mk lang st1 lc1 sc1 mem1) e0 /\
    Thread.consistent e0 lo.
Proof.
  assert(LOCAL_WF_READ: Local.wf lc1' mem1).
  {
    eapply local_wf_read; eauto.
  }
  assert(LOCAL_WF': Local.wf lc2 mem2).
  {
    eapply local_wf_write; eauto.
  }
  assert(MEM_CLOSED': Memory.closed mem2).
  {
    eapply write_step_closed_mem; [| eapply WRITE_ADD | eapply LOCAL_WF_READ | eauto..]; eauto.
    inv READ; ss. eapply closed_mem_implies_closed_msg; eauto.
  }
  eapply Thread_consistent_to_consistent_nprm in CONS; eauto.
  assert(CAP_EXIST: exists mem2', Memory.cap mem2 mem2').
  {
    eapply Memory.cap_exists; eauto.
  }
  destruct CAP_EXIST as (mem2' & CAP_EXIST). 
  assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem2' sc1').
  {
    eapply Memory.max_concrete_timemap_exists.
    eapply Memory.cap_closed in CAP_EXIST; eauto.
    inv CAP_EXIST; eauto.
  } 
  destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
  destruct(classic (Memory.max_ts loc mem2 = tsw)).
  {
    (* new message is the max one *)
    inv WRITE_ADD.
    inv WRITE; ss. inv PROMISE; ss.
    assert(LT_MSG_T: Time.lt tsr (Memory.max_ts loc mem2)).
    {
      inv MEM. inv ADD; eauto.
    }
    cut(forall t, Interval.mem (tsr, (Memory.max_ts loc mem2)) t -> ~ Cover.covered loc t mem1).
    2: eapply MemoryProps.memory_add_cover_disjoint; eauto.
    i. 
    cut(forall t, Interval.mem ((Memory.max_ts loc mem2), Time.incr (Memory.max_ts loc mem2)) t ->
             ~ Cover.covered loc t mem1).
    i.
    assert(NOCOVER: forall t, Interval.mem (tsr, Time.incr (Memory.max_ts loc mem2)) t -> ~ Cover.covered loc t mem1).
    {
      clear - H H0 LT_MSG_T. i.
      eapply Interval.mem_split with (mb := Memory.max_ts loc mem2) in H1.
      destruct H1; eauto.
      econstructor; ss.
      inv H1; ss.
      eapply Time.le_lteq. left.
      eapply Time.incr_spec.
    }
    clear H H0.
    assert(MEM_ADD: exists mem', Memory.add mem1 loc tsr (Time.incr (Memory.max_ts loc mem2)) Message.reserve mem').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_MSG_T.
      eapply Time.incr_spec.
      econstructor; eauto.
    }
    destruct MEM_ADD as (mem' & MEM_ADD).
    assert(PRM_READ_UNCHANGE: Local.promises lc1 = Local.promises lc1').
    {
      inv READ; ss.
    }
    assert(PRM_ADD: exists promises',
              Memory.add (Local.promises lc1) loc tsr (Time.incr (Memory.max_ts loc mem2))
                         Message.reserve promises').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_MSG_T.
      eapply Time.incr_spec.
      econstructor; eauto.
      clear - LOCAL_WF NOCOVER.
      ii.
      eapply NOCOVER in H.
      contradiction H.
      inv LOCAL_WF; eauto.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD as (promises' & PRM_ADD).
    exists (Thread.mk lang st1 (Local.mk (Local.tview lc1) promises') sc1 mem').
    split.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply PRM_ADD.
    eapply MEM_ADD.
    econstructor; eauto.
    ii; des; ss.
    econstructor; eauto.
    ss.
    ss.
    unfold Thread.consistent; ss.
    ii.
    exploit CONS; simpl; [eapply CAP_EXIST | eauto..].
    introv CONS'. destruct CONS' as (e2 & TAU_STEPS & FULFILL).  
    assert(REMOVE_RSV_MEM: 
             exists mem0', Memory.remove mem0 loc tsr (Time.incr (Memory.max_ts loc mem2)) Message.reserve mem0').
    {
      eapply Memory.remove_exists.
      cut (Memory.get loc (Time.incr (Memory.max_ts loc mem2)) mem' = Some (tsr, Message.reserve)).
      clear - CAP; ii.
      inv CAP; eauto.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_MEM as (mem0' & REMOVE_RSV_MEM).
    assert(REMOVE_RSV_PRM: exists promises0',
              Memory.remove promises' loc tsr (Time.incr (Memory.max_ts loc mem2)) Message.reserve promises0').
    {
      eapply Memory.remove_exists.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_PRM as (promises0' & REMOVE_RSV_PRM).
    assert(REMOVE_NOT_COVER: 
             forall t, Interval.mem (tsr, (Time.incr (Memory.max_ts loc mem2))) t ->
                  ~ Cover.covered loc t mem0').
    {
      eapply Cover.remove_not_cover; eauto.
    }
    assert(PRM_LE: Memory.le promises0' mem0').
    {
      eapply Memory.promise_le with (promises1 := promises') (mem1 := mem0); eauto.
      eapply Memory.cap_le; eauto.
      eapply Memory.promise_le with (promises1 := Local.promises lc1) (mem1 := mem1); eauto.
      inv LOCAL_WF; eauto.
      econstructor; eauto.
      ii; des.
      ss.
    }
    assert(WRITE': exists mem1',
              Memory.write promises0' mem0' loc tsr (Memory.max_ts loc mem2) valw
                           (TView.write_released (Local.tview lc1') sc1 loc (Memory.max_ts loc mem2) releasedr ordw)
                           promises0' mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      {
        clear - REMOVE_NOT_COVER. ii.
        eapply REMOVE_NOT_COVER; eauto.
        eapply Interval.le_mem; eauto.
        econstructor; ss.
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
        eapply Time.le_lteq. left.
        eapply Time.incr_spec.
      }
      {
        inv TS; eauto.
      }
      { 
        clear - REMOVE_NOT_COVER LT_MSG_T.
        introv CONTR. inv CONTR; des.
        exploit Memory.get_ts; eauto. i; des; subst.
        rewrite H in LT_MSG_T.
        eapply Time.Time_lt_bot_false in LT_MSG_T; ss. 
        destruct(Time.le_lt_dec x (Time.incr (Memory.max_ts loc mem2))).
        {
          specialize (REMOVE_NOT_COVER x).
          eapply REMOVE_NOT_COVER; eauto.
          econstructor; eauto; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          econstructor; ss; eauto.
          econstructor; ss; eauto.
          eapply Time.le_lteq; eauto.
        }
        {
          specialize (REMOVE_NOT_COVER (Time.incr (Memory.max_ts loc mem2))).
          eapply REMOVE_NOT_COVER; eauto.
          econstructor; ss; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.incr_spec.
          eapply Time.le_lteq; eauto.
          econstructor; eauto.
          econstructor; ss; eauto.
          eapply Time.incr_spec.
          eapply Time.le_lteq; eauto.
        }
      }
      {
        clear - MEM.
        inv MEM. inv ADD; ss.
      }
    }
    destruct WRITE' as (mem1' & WRITE'). 
    assert(PRM_LE': Memory.le promises0' mem1').
    { eapply MemoryProps.write_memory_le; eauto. }
    eapply rtc_rtcn in TAU_STEPS.
    destruct TAU_STEPS as (n & TAU_STEPS). destruct e2.
    assert(LOCAL_READ: 
             Local.read_step (Local.mk (Local.tview lc1) promises0') mem0' loc tsr valr releasedr ordr
                             (Local.mk (Local.tview lc1') promises0') lo).
    {
      ss. inv READ; ss. 
      econs; eauto. instantiate (1 := from). 
      clear - GET REMOVE_RSV_MEM MEM_ADD CAP MEM_CLOSED. 
      exploit Memory.add_get1; [eapply MEM_ADD | eapply GET | eauto..]. ii.
      inv CAP. eapply SOUND in H.
      clear - REMOVE_RSV_MEM H. 
      erewrite Memory.remove_o; eauto. des_if; eauto; ss.
      des; subst.
      exploit Memory.remove_get0; eauto. ii; des.
      exploit Memory.get_ts; eauto. ii; des; subst.
      cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))). ii.
      rewrite H0 in H2. clear - H2. auto_solve_time_rel.
      auto_solve_time_rel.
      auto_solve_time_rel.
    }
    assert(LOCAL_WRITE: 
             Local.write_step (Local.mk (Local.tview lc1') promises0') sc0 mem0' loc
                              tsr (Memory.max_ts loc mem2) valw releasedr
                              (TView.write_released (Local.tview lc1') sc1 loc (Memory.max_ts loc mem2) releasedr ordw)
                              ordw
                              (Local.mk (TView.write_tview (Local.tview lc1') sc1 loc
                                                           (Memory.max_ts loc mem2) ordw) promises0')
                              sc0 mem1' Memory.op_kind_add lo).
    {
      econs; ss.
      clear - WRITABLE. inv WRITABLE. econs; eauto.
      eapply WRITE'.
      introv NONSYNC. eapply RELEASE in NONSYNC.
      clear - NONSYNC PRM_ADD REMOVE_RSV_PRM PRM_READ_UNCHANGE.
      rewrite <- PRM_READ_UNCHANGE in NONSYNC.
      eapply reserve_non_synch_loc in PRM_ADD; eauto.       
      eapply remove_non_synch_loc in REMOVE_RSV_PRM; eauto.
    }
    assert(LOCAL_WF'': Local.wf {| Local.tview := Local.tview lc1; Local.promises := promises0' |} mem0').
    {
      eapply local_wf_promise.
      eapply Memory.promise_cancel. eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM. ss.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      ss.
      eapply Local.cap_wf with (mem1 := mem'); eauto.
      eapply local_wf_promise.
      eapply Memory.promise_add. eapply PRM_ADD. eapply MEM_ADD.
      ss.
      ii; ss.
      ss.
      ss.
      destruct lc1; ss.
    }
    eapply additional_msg_consistent_construction with
        (inj := (spec_inj mem2'))
        (max_ts := Memory.max_ts loc mem2')
        (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem0)) in TAU_STEPS.
    destruct TAU_STEPS as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL').
    {
      eexists. split.
      (* cancel the reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_promise.
      econs.
      econs; ss.
      eapply Memory.promise_cancel.
      eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM.
      ss. ss. ss.
      (* update add *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_program.
      econs.
      instantiate (2 := ThreadEvent.update loc tsr (Memory.max_ts loc mem2) valr valw releasedr
                                           (TView.write_released (Local.tview lc1') sc1 loc (Memory.max_ts loc mem2)
                                                                 releasedr ordw) ordr ordw).
      ss. eapply STATE.
      eapply Local.step_update; eauto.
      ss.
      eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
      ss.
    }  
    {
      (* local wf *)
      eapply Local.cap_wf with (mem1 := mem2); eauto.
    }
    {
      (* local wf *) 
      eapply local_wf_write.
      eapply LOCAL_WRITE.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      eapply local_wf_read; eauto. 
      eapply Memory.cancel_closed; eauto. 
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* closed memory *)
      eapply Memory.cap_closed with (mem1 := mem2); eauto.
    }
    {
      (* closed memory *)
      eapply write_step_closed_mem with (releasedr := releasedr); ss; eauto.
      eapply Memory.cancel_closed_opt_view; eauto.
      eapply Memory.cap_closed_opt_view; eauto.
      eapply Memory.add_closed_opt_view; eauto.
      clear - MEM_CLOSED READ. inv READ. inv MEM_CLOSED.
      eapply CLOSED in GET; ss; des. inv MSG_CLOSED; eauto.
      eapply local_wf_read; eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* other identity injection *)
      instantiate (1 := loc).
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max identity injection *)
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max_ts *)
      eapply Time.join_l.
    }
    {
      (* msg injection *)
      econs.
      {
        ii.
        unfold spec_inj at 1. rewrite MSG.
        exists t f R. split; eauto.
        split. eapply spec_inj_optviewinj; eauto.
        assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val R)).
        {
          eapply Memory.cap_inv in MSG; eauto.
          des; ss.
        }
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o; eauto.
        des_if.
        {
          ss; des; subst.
          erewrite Memory.add_o in GET1; eauto.
          des_ifH GET1; ss.
          destruct o; ss.
        }
        {
          ss. 
          eapply Memory.concrete_msg_remove_rsv_stable with (mem := mem0); eauto.
          erewrite Memory.add_o with (mem1 := mem1) in GET1; eauto.
          des_ifH GET1; ss. destruct a; subst; ss. destruct o; subst; ss.
          eapply Memory.add_get1 with (m2 := mem') in GET1; eauto.
          clear - CAP GET1.
          inv CAP.
          eapply SOUND; eauto.
        }
      } 
      {
        ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
        destruct t1; ss. inv INJ.
        do 3 eexists. eauto.
      }
      {
        eapply spec_inj_monotonic; eauto.
      }
    }
    {
      (* TView inj *)
      ss. eapply TViewInj_spec_inj_id.
    }
    {
      (* promise eq *)
      ss.
      eapply MemoryMerge.MemoryMerge.add_remove in PRM_ADD; eauto.
      eapply MemoryMerge.MemoryMerge.add_remove in PROMISES; eauto.
      subst; eauto.
      inv READ; ss.
      eapply spec_inj_implies_promises_inj; eauto.
      clear - LOCAL_WF' CAP_EXIST.
      inv LOCAL_WF'; eauto; ss. eapply Memory.cap_le; eauto.
    }
    {
      (* OTHER cover *)
      ii.
      contradiction H0. clear H0.
      inv H1.
      assert(GET1: Memory.get loc0 to mem0' = Some (from, msg)).
      {  
        clear - WRITE' GET H. 
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
      }
      erewrite Memory.remove_o with (mem1 := mem0) in GET1; eauto.
      des_ifH GET1; ss.
      cut(mem' loc0 = mem2 loc0). ii.
      eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H0; eauto.
      econs.
      unfolds Memory.get.
      rewrite <- H0; eauto.
      ss.
      eapply Memory.add_closed; ss.
      eapply MEM_ADD. ss.
      clear - MEM_ADD MEM H.
      inv MEM_ADD; inv MEM. inv ADD0; inv ADD.
      assert(LocFun.find loc0 (LocFun.add loc r mem1) = LocFun.find loc0 (LocFun.add loc r0 mem1)).
      rewrite LocFun.add_spec_neq; ss. rewrite LocFun.add_spec_neq; ss.
      unfold LocFun.find in *; ss.
    }  
    {
      (* loc0 cover *) 
      clear - MEM_CLOSED' CAP_EXIST. ii.
      exploit Memory.cap_max_ts; eauto.
      instantiate (1 := loc); ii.
      inv H1.
      assert(ts <> Time.bot).
      {
        intro; subst.
        inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
      }
      eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
      contradiction H.
      des; subst.
      eapply CAP_EXIST.
      rewrite H2 in H0.
      econs; ss.
      destruct (Time.le_lt_dec Time.bot ts); eauto.
      eapply Time.le_lteq in l; des; ss. subst; ss.
      eapply Time_lt_bot_false in l; ss.
    }
    { 
      (* spec_view *)
      ss.
      eapply spec_view_intro_le_max_ts.
      { 
        exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
        instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
        cut(Time.le (TimeMap.join (View.rlx (TView.acq (Local.tview lc1')))
                                  (TimeMap.singleton loc (Memory.max_ts loc mem2)) loc)
                    (Memory.max_ts loc mem2)).
        ii. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
        eapply Time.incr_spec.
        eapply Time.join_spec.
        {
          clear - LOCAL_WF_READ MEM.
          inv LOCAL_WF_READ. clear TVIEW_WF PROMISES FINITE BOT. ss.
          inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
          specialize (RLX loc). des.
          eapply Memory.add_get1 in RLX; eauto.
          eapply Memory.max_ts_spec in RLX; des; ss.
        }
        {
          unfold TimeMap.singleton.
          cut(LocFun.find loc (LocFun.add loc (Memory.max_ts loc mem2) (LocFun.init Time.bot)) =
              Memory.max_ts loc mem2). ii.
          unfolds LocFun.find. rewrite H. eapply Time.le_lteq; eauto.
          rewrite LocFun.add_spec_eq; eauto.
        }
      }
      {
        eapply Cover.gt_max_not_covered.
      }
      {
        ii. inv H0. inv WRITE'. inv PROMISE. 
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; ss.
        {
          destruct a; subst. inv GET.
          eapply Time.Time_lt_join in H; destruct H.
          exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
          instantiate (1 := loc); introv MAX_TS.
          clear - H ITV MAX_TS.
          rewrite MAX_TS in H. inv ITV; ss.
          cut(Time.lt (Memory.max_ts loc mem2) ts'); ii. 
          eapply Time.Time_le_gt_false in TO; ss.
          cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.incr_spec.
        }
        {
          erewrite Memory.remove_o in GET; eauto.
          des_ifH GET; ss.
          eapply Time.Time_lt_join in H; destruct H.
          clear - H0 ITV GET. inv ITV; ss. eapply Memory.max_ts_spec in GET; des.
          cut(Time.lt to ts'); ii.
          eapply Time.Time_le_gt_false; eauto. 
          eapply TimeFacts.le_lt_lt; eauto.
        }
      }
    }
    {
      (* max cover *)
      clear - CAP_EXIST MEM_CLOSED'.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      inv CAP_EXIST.
      specialize (BACK loc).
      rewrite H; eauto.
    }
    {
      (* promise le *)
      ss.
      clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
      inv LOCAL_WF'; ss; ii.
      eapply PROMISES in H.
      eapply Memory.max_ts_spec in H; eauto; des.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      rewrite H.
      cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    {
      (* FULFill *)
      ss.
    }
    clear - MEM. ii.
    inv H0.
    eapply Memory.add_get1 in GET; eauto.
    eapply Memory.max_ts_spec in GET; des.
    inv ITV; ss.
    inv H; ss.
    cut(Time.lt to t). ii.
    eapply Time_le_gt_false in TO; ss.
    eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto.
  }
  {
    (* write not max *)
    inv WRITE_ADD.
    inv WRITE; ss. inv PROMISE; ss.
    assert(NOT_COVER1: forall t, Interval.mem (tsr, tsw) t -> ~ Cover.covered loc t mem1).
    {
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    }
    lets GET: MEM.
    eapply Memory.add_get0 in GET. destruct GET as [ _ GET]. 
    exploit Memory.next_exists; [eapply GET | idtac..]. instantiate (1 := tsw).
    {
      eapply Memory.max_ts_spec in GET; des.
      eapply Time.le_lteq in MAX. destruct MAX; subst; ss.
    }
    introv NEXT.
    destruct NEXT as (from0 & to0 & msg0 & GET_NEXT & NEXT & WF_NEXT).
    assert(LT_ADD: Time.lt tsr tsw).
    {
      eapply MemoryProps.add_succeed_wf in MEM; des; ss.
    }
    assert(LE_ORIGIN_MSG: Time.lt from0 to0).
    {
      eapply Memory.get_ts in GET_NEXT.
      des; subst; ss.
      eapply Time.Time_lt_bot_false in NEXT; eauto; ss.
    }
    assert(GET_NEXT_PRSV: Memory.get loc to0 mem1 = Some (from0, msg0)).
    {
      erewrite Memory.add_o in GET_NEXT; eauto.
      des_ifH GET_NEXT; ss; des; subst.
      eapply Time.Time.lt_strorder_obligation_1 in NEXT; ss.
    }
    assert(IS_NEXT: Time.lt tsw from0).
    {
      exploit Memory.get_disjoint; [eapply GET_NEXT | eapply GET | eauto..].
      clear - H GET GET_NEXT NEXT ATTACH LT_ADD GET_NEXT_PRSV. ii.
      des. subst.
      {
        eapply Time.Time.lt_strorder_obligation_1 in NEXT; ss.
      }
      {
        destruct (Time.le_lt_dec from0 tsw); eauto.
        eapply Time.le_lteq in l. des; subst.
        unfold Interval.disjoint in H0. specialize (H0 tsw).
        exploit H0; ii; ss.  
        econs; ss; eauto. eapply Time.le_lteq; eauto. 
        econs; ss; eauto. 
        eapply Time.le_lteq; eauto.
        eapply ATTACH in GET_NEXT_PRSV; eauto; ss.
      }
    }
    assert(NOT_COVER2: forall t, Interval.mem (tsw, from0) t -> ~ Cover.covered loc t mem1).
    {  
      clear - GET_NEXT_PRSV NEXT WF_NEXT IS_NEXT LE_ORIGIN_MSG MEM. ii.
      inv H0.
      destruct(Time.le_lt_dec to0 to).
      {
        eapply Time.le_lteq in l; des; subst.
        {
          exploit Memory.get_disjoint; [eapply GET_NEXT_PRSV | eapply GET | eauto..]. ii; des; subst.
          eapply Time.Time.lt_strorder_obligation_1 in l; ss.
          destruct(Time.le_lt_dec to0 from).
          clear - LE_ORIGIN_MSG H l0 ITV.
          inv H; ss. inv ITV; ss.
          cut(Time.le t to0); ii.
          cut(Time.lt to0 t); ii. 
          eapply Time_le_gt_false; eauto.
          eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto.
          eapply Time.le_lteq. left.
          eapply DenseOrder.DenseOrderFacts.le_lt_lt with (b := from0); eauto.
          eapply H0 with (x := to0).
          econs; ss; eauto. eapply Time.le_lteq; eauto.
          econs; ss; eauto. eapply Time.le_lteq; eauto.
        }
        {
          inv H; ss.
          rewrite GET_NEXT_PRSV in GET; inv GET.
          inv ITV; ss. eapply Time_le_gt_false in TO; eauto.
        }
      }
      {
        inv H. inv ITV; ss. 
        eapply WF_NEXT in l; eauto.
        erewrite Memory.add_o in l; eauto.
        des_ifH l; ss.
        rewrite GET in l; ss.
        eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto.
      }
    }
    assert(NOT_COVER3: forall t, Interval.mem (tsr, from0) t -> ~ Cover.covered loc t mem1).
    {
      clear - NOT_COVER1 LT_ADD NOT_COVER2 IS_NEXT. ii. 
      eapply Interval.mem_split with (mb := tsw) in H; eauto.
      destruct H; eauto.
      eapply NOT_COVER1; eauto. eapply NOT_COVER2; eauto.
      econs; ss. eapply Time.le_lteq; eauto.
    }
    assert(MEM_ADD: exists mem', Memory.add mem1 loc tsr from0 Message.reserve mem').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_ADD. eapply IS_NEXT.
      econstructor; eauto.
    }
    destruct MEM_ADD as (mem' & MEM_ADD).
    assert(PRM_ADD: exists promises',
              Memory.add (Local.promises lc1) loc tsr from0 Message.reserve promises').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2; eauto.
      econstructor.
      clear - LOCAL_WF NOT_COVER3.
      ii.
      eapply NOT_COVER3 in H.
      contradiction H.
      inv LOCAL_WF; eauto.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD as (promises' & PRM_ADD).
    exists (Thread.mk lang st1 (Local.mk (Local.tview lc1) promises') sc1 mem').
    split.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply PRM_ADD.
    eapply MEM_ADD.
    econstructor; eauto.
    ii; des; ss.
    econstructor; eauto.
    ss.
    ss.
    unfold Thread.consistent; ss.
    ii. 
    exploit CONS; simpl; [eapply CAP_EXIST | eauto..].
    introv CONS'. destruct CONS' as (e2 & TAU_STEPS & FULFILL).  
    assert(REMOVE_RSV_MEM: 
             exists mem0', Memory.remove mem0 loc tsr from0 Message.reserve mem0').
    {
      eapply Memory.remove_exists.
      cut (Memory.get loc from0 mem' = Some (tsr, Message.reserve)).
      clear - CAP; ii.
      inv CAP; eauto.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_MEM as (mem0' & REMOVE_RSV_MEM).
    assert(REMOVE_RSV_PRM: exists promises0',
              Memory.remove promises' loc tsr from0 Message.reserve promises0').
    {
      eapply Memory.remove_exists.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_PRM as (promises0' & REMOVE_RSV_PRM).
    assert(REMOVE_NOT_COVER: 
             forall t, Interval.mem (tsr, from0) t -> ~ Cover.covered loc t mem0').
    {
      eapply Cover.remove_not_cover; eauto.
    }
    assert(PRM_LE: Memory.le promises0' mem0').
    {
      eapply Memory.promise_le with (promises1 := promises') (mem1 := mem0); eauto.
      eapply Memory.cap_le; eauto.
      eapply Memory.promise_le with (promises1 := Local.promises lc1) (mem1 := mem1); eauto.
      inv LOCAL_WF; eauto.
      econstructor; eauto.
      ii; des.
      ss.
    }
    assert(WRITE': exists mem1',
              Memory.write promises0' mem0' loc tsr tsw valw
                           (TView.write_released (Local.tview lc1') sc1 loc tsw releasedr ordw)
                           promises0' mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      {
        clear - REMOVE_NOT_COVER IS_NEXT. ii.
        eapply REMOVE_NOT_COVER; eauto.
        eapply Interval.le_mem; eauto.
        econstructor; ss.
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1; eauto.
        eapply Time.le_lteq. eauto.
      }
      {
        inv TS; eauto.
      }
      {
        clear - LT_ADD LE_ORIGIN_MSG IS_NEXT REMOVE_NOT_COVER.
        introv CONTR. inv CONTR. des.
        destruct(Time.le_lt_dec x from0).
        {
          specialize (REMOVE_NOT_COVER x).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD; ss.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
        {
          specialize (REMOVE_NOT_COVER from0).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.le_lteq. eauto.
          econs; ss; eauto.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
      }
      {
        clear - MEM.
        inv MEM. inv ADD; ss.
      }
    }
    destruct WRITE' as (mem1' & WRITE'). 
    assert(PRM_LE': Memory.le promises0' mem1').
    { eapply MemoryProps.write_memory_le; eauto. }
    eapply rtc_rtcn in TAU_STEPS.
    destruct TAU_STEPS as (n & TAU_STEPS). destruct e2.
    assert(LOCAL_READ: 
             Local.read_step (Local.mk (Local.tview lc1) promises0') mem0' loc tsr valr releasedr ordr
                             (Local.mk (Local.tview lc1') promises0') lo).
    {
      ss. inv READ; ss. 
      econs; eauto. instantiate (1 := from). 
      clear - GET0 REMOVE_RSV_MEM MEM_ADD CAP MEM_CLOSED. 
      exploit Memory.add_get1; [eapply MEM_ADD | eapply GET0 | eauto..]. ii.
      inv CAP. eapply SOUND in H.
      clear - REMOVE_RSV_MEM H. 
      erewrite Memory.remove_o; eauto. des_if; eauto; ss.
      des; subst.
      exploit Memory.remove_get0; eauto. ii; des.
      exploit Memory.get_ts; eauto. ii; des; subst.
      rewrite H in GET. ss.
      rewrite H in GET. ss.
    }
    assert(LOCAL_WRITE: 
             Local.write_step (Local.mk (Local.tview lc1') promises0') sc0 mem0' loc
                              tsr tsw valw releasedr
                              (TView.write_released (Local.tview lc1') sc1 loc tsw releasedr ordw) ordw
                              (Local.mk (TView.write_tview (Local.tview lc1') sc1 loc tsw ordw) promises0')
                              sc0 mem1' Memory.op_kind_add lo).
    {
      econs; ss.
      clear - WRITABLE READ. inv WRITABLE. econs; eauto.
      eapply WRITE'.
      introv NONSYNC. eapply RELEASE in NONSYNC.
      clear - NONSYNC PRM_ADD REMOVE_RSV_PRM READ.
      inv READ; ss.
      eapply reserve_non_synch_loc in PRM_ADD; eauto.      
      eapply remove_non_synch_loc in REMOVE_RSV_PRM; eauto.
    }
    assert(ADD_LT_MAX: Time.lt tsw (Memory.max_ts loc mem2)).
    {
      eapply Memory.add_get0 in MEM; eauto.
      clear - MEM H. des.
      eapply Memory.max_ts_spec in GET0. des.
      eapply Time.le_lteq in MAX; des; subst; ss.
    }
    assert(LOCAL_WF'': Local.wf {| Local.tview := Local.tview lc1'; Local.promises := promises0' |} mem0').
    {
      eapply local_wf_promise.
      eapply Memory.promise_cancel. eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM. ss.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      ss.
      eapply Local.cap_wf with (mem1 := mem'); eauto.
      eapply local_wf_promise.
      eapply Memory.promise_add. eapply PRM_ADD. eapply MEM_ADD.
      ss.
      ii; ss.
      ss.
      ss.
      destruct lc1; ss.
      inv READ; subst; ss.
    }
    eapply additional_msg_consistent_construction with
        (inj := (spec_inj mem2'))
        (max_ts := Memory.max_ts loc mem2')
        (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem0)) in TAU_STEPS.
    destruct TAU_STEPS as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL').
    {
      eexists. split.
      (* cancel the reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_promise.
      econs.
      econs; ss.
      eapply Memory.promise_cancel.
      eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM.
      ss. ss. ss.
      (* update add *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_program.
      econs.
      instantiate (2 := ThreadEvent.update
                          loc tsr tsw valr valw releasedr
                          (TView.write_released (Local.tview lc1') sc1 loc tsw releasedr ordw) ordr ordw).
      ss. eapply STATE.
      econs; eauto.
      ss.
      eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
      ss.
    }
    {
      (* local wf *)
      eapply Local.cap_wf with (mem1 := mem2); eauto.
    }
    {
      (* local wf *)
      eapply local_wf_write.
      eapply LOCAL_WRITE.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      eauto.
    }
    {
      (* closed memory *)
      eapply Memory.cap_closed with (mem1 := mem2); eauto.
    }
    {
      (* closed memory *)
      eapply write_step_closed_mem with (releasedr := releasedr); ss; eauto.
      eapply Memory.cancel_closed_opt_view; eauto.
      eapply Memory.cap_closed_opt_view; eauto.
      eapply Memory.add_closed_opt_view; eauto.
      clear - MEM_CLOSED READ. inv READ. inv MEM_CLOSED.
      eapply CLOSED in GET; ss; des. inv MSG_CLOSED; eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* other identity injection *)
      instantiate (1 := loc).
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max identity injection *)
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max_ts *)
      eapply Time.join_l.
    }
    {
      (* msg injection *)
      econs.
      {
        ii.
        unfold spec_inj at 1. rewrite MSG.
        exists t f R. split; eauto.
        split. eapply spec_inj_optviewinj; eauto.
        assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val R)).
        {
          eapply Memory.cap_inv in MSG; eauto.
          des; ss.
        }
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o; eauto.
        des_if.
        {
          ss; des; subst.
          erewrite Memory.add_o in GET1; eauto.
          des_ifH GET1; ss.
          destruct o; ss.
        }
        {
          ss. 
          eapply Memory.concrete_msg_remove_rsv_stable with (mem := mem0); eauto.
          erewrite Memory.add_o with (mem1 := mem1) in GET1; eauto.
          des_ifH GET1; ss. destruct a; subst; ss. destruct o; subst; ss.
          eapply Memory.add_get1 with (m2 := mem') in GET1; eauto.
          clear - CAP GET1.
          inv CAP.
          eapply SOUND; eauto.
        }
      }
      {
        ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
        destruct t1; ss. inv INJ.
        do 3 eexists. eauto. 
      }
      {
        eapply spec_inj_monotonic; eauto.
      }
    }
    {
      (* TView inj *)
      ss. eapply TViewInj_spec_inj_id.
    }
    {
      (* promise eq *)
      ss.
      eapply MemoryMerge.MemoryMerge.add_remove in PRM_ADD; eauto.
      eapply MemoryMerge.MemoryMerge.add_remove in PROMISES; eauto.
      subst; eauto. inv READ; ss.
      eapply spec_inj_implies_promises_inj; eauto.
      clear - LOCAL_WF' CAP_EXIST.
      inv LOCAL_WF'; eauto; ss. eapply Memory.cap_le; eauto.
    }
    {
      (* OTHER COVER *)
      ii.
      contradiction H1. clear H1.
      inv H2. 
      assert(GET1: Memory.get loc0 to mem0' = Some (from, msg)).
      {     
        clear - WRITE' GET0 H0. 
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o in GET0; eauto.
        des_ifH GET0; subst; des; ss.
      }
      erewrite Memory.remove_o with (mem1 := mem0) in GET1; eauto.
      des_ifH GET1; ss.
      cut(mem' loc0 = mem2 loc0). ii.
      eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H1; eauto.
      econs.
      unfolds Memory.get.
      rewrite <- H1; eauto.
      ss.
      eapply Memory.add_closed; ss.
      eapply MEM_ADD. ss. 
      clear - MEM_ADD MEM H0.
      inv MEM_ADD; inv MEM. inv ADD0; inv ADD.
      assert(LocFun.find loc0 (LocFun.add loc r mem1) = LocFun.find loc0 (LocFun.add loc r0 mem1)).
      rewrite LocFun.add_spec_neq; ss. rewrite LocFun.add_spec_neq; ss.
      unfold LocFun.find in *; ss.
    }
    {
      (* loc0 cover *) 
      clear - MEM_CLOSED' CAP_EXIST. ii.
      exploit Memory.cap_max_ts; eauto.
      instantiate (1 := loc); ii.
      inv H1.
      assert(ts <> Time.bot).
      {
        intro; subst.
        inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
      }
      eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
      contradiction H.
      des; subst.
      eapply CAP_EXIST.
      rewrite H2 in H0.
      econs; ss.
      destruct (Time.le_lt_dec Time.bot ts); eauto.
      eapply Time.le_lteq in l; des; ss. subst; ss.
      eapply Time_lt_bot_false in l; ss.
    }
    { 
      (* spec view *)
      ss. 
      eapply spec_view_intro_le_max_ts.
      {
        exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
        instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
        cut(Time.le (TimeMap.join (View.rlx (TView.acq (Local.tview lc1')))
                                  (TimeMap.singleton loc tsw) loc)
                    (Memory.max_ts loc mem2)).
        ii. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; [eapply H0 | idtac ..].
        eapply Time.incr_spec.
        eapply Time.join_spec.
        {
          clear - LOCAL_WF_READ MEM.
          inv LOCAL_WF_READ. clear TVIEW_WF PROMISES FINITE BOT.
          inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
          specialize (RLX loc). des.
          eapply Memory.add_get1 in RLX; eauto.
          eapply Memory.max_ts_spec in RLX; des; ss.
        }
        {
          unfold TimeMap.singleton.
          rewrite Loc_add_eq; eauto.
          eapply Time.le_lteq; eauto.
        }
      }
      {
        eapply Cover.gt_max_not_covered.
      }
      { 
        ii. eapply Time_lt_join in H0. destruct H0. inv H1.
        inv LOCAL_WRITE; ss. inv LC2. inv WRITE. inv PROMISE.
        erewrite Memory.add_o in GET0; eauto.
        des_ifH GET0; ss.
        {
          des; subst. inv GET0.
          clear - CAP_EXIST H0 ITV ADD_LT_MAX MEM_CLOSED'.
          inv ITV; ss.
          eapply Memory.cap_max_ts in CAP_EXIST; eauto.
          rewrite CAP_EXIST in H0.
          cut(Time.lt tsw ts'); ii.
          eapply Time_le_gt_false in TO; eauto.
          eapply Time.Time.lt_strorder_obligation_2. eapply ADD_LT_MAX.
          eapply Time.Time.lt_strorder_obligation_2. 2: eapply H0.
          eapply Time.incr_spec.
        }
        {
          destruct o; ss. 
          clear - H2 REMOVE_RSV_MEM H1 GET0 ITV.
          erewrite Memory.remove_o in GET0; eauto.
          des_ifH GET0; ss; des; subst; ss.
          eapply Memory.max_ts_spec in GET0; des.
          inv ITV; ss.
          cut(Time.lt (Memory.max_ts loc mem0) to). ii.
          eapply Time_le_gt_false in MAX; eauto.
          eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto.
        }
      }
    }
    {
      (* max cover *)
      clear - CAP_EXIST MEM_CLOSED'.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      inv CAP_EXIST.
      specialize (BACK loc).
      rewrite H; eauto.
    }
    {
      (* promise le *)
      ss.
      clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
      inv LOCAL_WF'; ss; ii.
      eapply PROMISES in H.
      eapply Memory.max_ts_spec in H; eauto; des.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      rewrite H.
      cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    {
      (* FULFill *)
      ss.
    }
  }
Qed.

Lemma update_not_add_step_consistent_construction
      lang st1 loc valr valw lc1 sc1 mem1
      tsr tsw releasedr releasedw ordr ordw
      lc1' st2 lc2 sc2 mem2 kind lo
      (STATE: Language.step lang (ProgramEvent.update loc valr valw ordr ordw) st1 st2)
      (READ: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc1' lo)
      (WRITE: Local.write_step lc1' sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc2 sc2 mem2 kind lo)
      (NOADD: kind <> Memory.op_kind_add)
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc2 mem2) lo)
      (ATOMIC_LOC: lo loc = Ordering.atomic)
      (LOCAL_WF: Local.wf lc1 mem1)
      (MEM_CLOSED: Memory.closed mem1):
  Thread.consistent (Thread.mk lang st1 lc1 sc1 mem1) lo.
Proof.
  assert(LOCAL_WF_READ: Local.wf lc1' mem1).
  {
    eapply local_wf_read; eauto.
  }
  assert(LOCAL_WF': Local.wf lc2 mem2).
  {
    eapply local_wf_write; eauto.
  }
  assert(MEM_CLOSED': Memory.closed mem2).
  {
    eapply write_step_closed_mem; [| eapply WRITE | eapply LOCAL_WF_READ | eauto..]; eauto.
    inv READ; ss. eapply closed_mem_implies_closed_msg; eauto.
  }
  eapply Thread_consistent_to_consistent_nprm in CONS; eauto.
  assert(CAP_EXIST: exists mem2', Memory.cap mem2 mem2').
  {
    eapply Memory.cap_exists; eauto.
  }
  destruct CAP_EXIST as (mem2' & CAP_EXIST). 
  assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem2' sc1').
  {
    eapply Memory.max_concrete_timemap_exists.
    eapply Memory.cap_closed in CAP_EXIST; eauto.
    inv CAP_EXIST; eauto.
  } 
  destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
  lets CONS': MAX_CONCRETE_TM_EXIT.
  eapply CONS in CONS'; ss; eauto.
  destruct CONS' as (e2 & CONS' & FULFILL').
  unfold Thread.consistent; ss; ii. 
  exploit write_not_add_cap_exit; [idtac | eapply WRITE | eauto..].
  inv LOCAL_WF_READ; eauto. instantiate (1 := sc0). introv WRITE'.
  destruct WRITE' as (mem' & WRITE').
  assert(LOCAL_WF'': Local.wf lc2 mem').
  {
    eapply local_wf_write; eauto.
    eapply Memory.cap_closed; eauto.
    eapply Local.cap_wf; eauto.
  }
  assert(CLOSED_MEM'': Memory.closed mem').
  {
    eapply write_step_closed_mem with (releasedr := releasedr); eauto. 
    inv READ; ss. eapply closed_mem_implies_closed_msg; eauto.
    eapply Memory.cap_closed; eauto.
    inv CAP. eapply SOUND; eauto.
    eapply Local.cap_wf; eauto.
    eapply Memory.cap_closed; eauto.
  }
  eapply rtc_rtcn in CONS'. destruct CONS' as (n & CONS').
  destruct e2. 
  eapply additional_msg_consistent_construction with
      (inj := (spec_inj mem2'))
      (max_ts := Memory.max_ts loc mem2')
      (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem')) in CONS'.
  destruct CONS' as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL'').
  {
    (* write *)
    eexists. split.
    eapply Relation_Operators.rt1n_trans.
    econs.
    econs.
    eapply Thread.step_program.
    econs.
    instantiate (2 := ThreadEvent.update loc tsr tsw valr valw releasedr
                                         (TView.write_released (Local.tview lc1') sc1 loc tsw releasedr ordw)
                                         ordr ordw).
    ss. eapply STATE.
    econs; eauto; ss.
    {
      instantiate (1 := lc1'). inv READ; ss.
      econs; eauto.
      inv CAP; ss. eapply SOUND; eauto.
    }
    {
      lets RELEASE: WRITE'. inv RELEASE; subst. eauto.
    }
    ss; eauto.
    eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
    ss.
  }
  {
    (* local wf *)
    eapply Local.cap_wf with (mem1 := mem2); eauto.
  }
  {
    (* local wf *) 
    eauto.
  }
  {
    (* closed memory *)
    eapply Memory.cap_closed with (mem1 := mem2); eauto.
  }
  {
    (* closed memory *)
    eauto.
  }
  {
    (* other identity injection *)
    instantiate (1 := loc).
    ii; eapply spec_inj_identity_inj; eauto.
  }
  {
    (* le max identity injection *)
    ii; eapply spec_inj_identity_inj; eauto.
  }
  {
    (* le max_ts *)
    eapply Time.join_l.
  }
  {
    (* msg injection *)
    econs.
    {
      ii.
      unfold spec_inj at 1. rewrite MSG.
      assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val R)).
      { 
        eapply Memory.cap_inv with (mem1 := mem2) in MSG; eauto.
        des; ss.
      }
      exploit write_step_not_add_cap_get_stable; [eapply GET1 | eapply WRITE | eauto..].
      ii.
      exists t f R. split; eauto. split; eauto.
      eapply spec_inj_optviewinj; eauto.
    }
    {
      ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
      destruct t1; ss. inv INJ.
      do 3 eexists. eauto. 
    }
    {
      eapply spec_inj_monotonic; eauto.
    }
  }
  {
    (* TView inj *)
    ss. eapply TViewInj_spec_inj_id.
  }
  {
    (* promise eq *)
    eapply spec_inj_implies_promises_inj; eauto.
    clear - LOCAL_WF' CAP_EXIST.
    inv LOCAL_WF'; eauto; ss. eapply Memory.cap_le; eauto.
  }
  { 
    ii.
    contradiction H0. clear H0.
    inv H1.
    econs; eauto. instantiate (1 := msg).
    assert(GET1: Memory.get loc0 to mem0 = Some (from, msg)).
    {     
      clear - WRITE' GET H NOADD. 
      inv WRITE'. inv WRITE. inv PROMISE; des; subst; ss.
      inv RESERVE.
      erewrite Memory.split_o in GET; eauto.
      des_ifH GET; subst; des; ss.
      des_ifH GET; subst; des; ss.
      des_ifH GET; subst; des; ss.
      erewrite Memory.lower_o in GET; eauto.
      des_ifH GET; subst; des; ss.
    }
    cut(mem1 loc0 = mem2 loc0). ii.   
    eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H0; eauto.
    unfolds Memory.get. rewrite <- H0; eauto.
    clear - WRITE H NOADD.
    inv WRITE. inv WRITE0. inv PROMISE; des; ss; subst; ss.
    inv RESERVE.
    inv MEM. inv SPLIT.
    assert(LocFun.find loc0 (LocFun.add loc r mem1) = mem1 loc0).
    rewrite LocFun.add_spec_neq; ss.
    unfold LocFun.find in *; ss.
    inv MEM. inv LOWER.
    assert(LocFun.find loc0 (LocFun.add loc r mem1) = mem1 loc0).
    rewrite LocFun.add_spec_neq; ss.
    unfold LocFun.find in *; ss.
  }
  {
    (* loc covered *)
    clear - MEM_CLOSED' CAP_EXIST. ii.
    exploit Memory.cap_max_ts; eauto.
    instantiate (1 := loc); ii.
    inv H1.
    assert(ts <> Time.bot).
    {
      intro; subst.
      inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
    }
    eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
    contradiction H.
    des; subst.
    eapply CAP_EXIST.
    rewrite H2 in H0.
    econs; ss.
    destruct (Time.le_lt_dec Time.bot ts); eauto.
    eapply Time.le_lteq in l; des; ss. subst; ss.
    eapply Time_lt_bot_false in l; ss.
  }
  {
    (* spec view *)
    eapply spec_view_intro_le_max_ts.
    { 
      exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
      instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS. 
      cut(Time.le (View.rlx (TView.acq (Local.tview lc2)) loc)
                  (Memory.max_ts loc mem2)).
      ii. eapply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
      eapply Time.incr_spec.
      clear - LOCAL_WF_READ WRITE NOADD.
      inv LOCAL_WF_READ. clear TVIEW_WF PROMISES FINITE BOT.
      inv WRITE. inv WRITE0. inv PROMISE; des; subst; ss.
      {
        (* split *)
        inv RESERVE.
        inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
        specialize (RLX loc). des.
        eapply Memory.split_get1 in RLX; eauto. des.
        eapply Memory.max_ts_spec in GET2; des; ss.
        eapply Time.join_spec; eauto.
        unfold TimeMap.singleton.
        rewrite Loc_add_eq.
        eapply Memory.split_get0 in MEM. des.
        eapply Memory.max_ts_spec in GET2; des; eauto.
      }
      {
        (* lower *)
        inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
        specialize (RLX loc). des.
        eapply Memory.lower_get1 in RLX; eauto. des.
        eapply Memory.max_ts_spec in GET2; des; ss.
        eapply Time.join_spec; eauto.
        unfold TimeMap.singleton.
        erewrite Loc_add_eq.
        eapply Memory.lower_get0 in MEM. des.
        eapply Memory.max_ts_spec in GET1; des; eauto.
      }
    }
    {
      eapply Cover.gt_max_not_covered.
    }
    {  
      ii. eapply Time_lt_join in H. destruct H. inv H0.
      inv WRITE'. inv WRITE0. inv PROMISE; des; subst; ss. inv RESERVE.
      {
        (* split *)
        eapply Memory.max_ts_spec in GET; des.
        clear - H1 MAX ITV.
        inv ITV; ss.  
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2 in TO; eauto.
        eapply TO in MAX.
        eapply Time_le_gt_false in MAX; eauto. 
      }
      {
        (* lower *)
        eapply Memory.max_ts_spec in GET; des.
        clear - H1 MAX ITV.
        inv ITV; ss.  
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2 in TO; eauto.
        eapply TO in MAX.
        eapply Time_le_gt_false in MAX; eauto. 
      }
    }
  }
  {
    (* max cover *)
    clear - CAP_EXIST MEM_CLOSED'.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
    inv CAP_EXIST.
    specialize (BACK loc).
    rewrite H; eauto.
  }
  {
    (* promise le *)
    ss.
    clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
    inv LOCAL_WF'; ss; ii.
    eapply PROMISES in H.
    eapply Memory.max_ts_spec in H; eauto; des.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
    rewrite H.
    cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
  {
    (* FULFill *)
    ss.
  }
Qed.

Lemma fence_no_sc_step_consistent_construction
      lang ordr ordw st1 lc1 sc1 mem st2 lc2 sc2 lo
      (STATE: Language.step lang (ProgramEvent.fence ordr ordw) st1 st2)
      (FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc2 mem) lo)
      (NO_SC: ordw <> Ordering.seqcst):
  Thread.consistent (Thread.mk lang st1 lc1 sc1 mem) lo.
Proof.
  unfolds Thread.consistent; ss; ii.
  exploit CONS; eauto.
  ii; des.
  eexists.
  split.
  eapply Relation_Operators.rt1n_trans; [idtac | eapply STEPS].
  econstructor; eauto.
  econstructor.
  eapply Thread.step_program.
  econstructor; ss; eauto.
  instantiate (1 := ThreadEvent.fence ordr ordw).
  ss; eauto.
  econs.
  clear - FENCE NO_SC.
  inv FENCE; ss. econs; eauto.
  erewrite write_fence_tview_not_sc; eauto.
  erewrite write_fence_tview_not_sc; eauto.
  unfold TView.write_fence_sc.
  assert(Ordering.le Ordering.seqcst ordw = false).
  {
    destruct ordw; ss.
  }
  rewrite H; eauto.
  ss.
  ss.
Qed.
  
Lemma program_step_consistent_construction
      lang te (e e': Thread.t lang) lo
      (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
      (CLOSED: Memory.closed (Thread.memory e))
      (PROG: Thread.program_step te lo e e')
      (NOSC: ~(exists ordr, te = ThreadEvent.fence ordr Ordering.seqcst))
      (TAU: ThreadEvent.get_machine_event te = MachineEvent.silent)
      (CONS: Thread.consistent e' lo):
  exists e0,
    rtc (Thread.reserve_step lo) e e0 /\ Thread.consistent e0 lo.
Proof.
  inv PROG.
  inv LOCAL.
  - (* silent *)
    eexists.
    split; eauto.
    unfolds Thread.consistent; ss; ii.
    exploit CONS; eauto; ii; des.
    eexists.
    split.
    eapply Relation_Operators.rt1n_trans; [idtac | eapply STEPS].
    econstructor; eauto.
    econstructor.
    eapply Thread.step_program.
    econstructor; ss; eauto.
    ss; eauto.
    ss; eauto.
  - (* read *)
    eexists. ss.
    split; eauto.
    eapply read_step_consistent_construction; eauto.
  - (* write *)
    destruct(classic (kind = Memory.op_kind_add)); subst.
    {
      eapply write_add_step_consistent_construction in LOCAL0; eauto.
      des.
      eexists.
      split.
      eapply Operators_Properties.clos_rt1n_step; eauto.
      ss.
    }
    {
      eapply write_not_add_step_consistent_construction in LOCAL0; eauto.
    }
  - (* update *)
    destruct(classic (kind = Memory.op_kind_add)); subst.
    {
      exploit update_add_step_consistent_construction; [ | eapply LOCAL1 | eapply LOCAL2 | eauto..]; eauto.
      ii; des.
      eexists.
      split.
      eapply Operators_Properties.clos_rt1n_step; eauto.
      ss.
    }
    {
      ss.
      eapply update_not_add_step_consistent_construction in LOCAL1; eauto.
    }
  - (* fence *)
    eapply fence_no_sc_step_consistent_construction in LOCAL0; eauto.
    ii; subst. contradiction NOSC. eauto.
  - (* output *)
    inv LOCAL0; ss.
Qed.

Lemma lower_PF_cap_exit
      mem1 mem1' lc1 
      mem2 mem2' lc2 
      loc from to val val0 released 
      (LE: Memory.le (Local.promises lc1) mem1)
      (WRITE: Local.promise_step lc1 mem1 loc from to (Message.concrete val0 None) lc2 mem2
                                 (Memory.op_kind_lower (Message.concrete val released)))
      (CAP1: Memory.cap mem1 mem1')
      (CAP2: Memory.cap mem2 mem2')
      (CLOSED: Memory.closed mem1):
  exists mem', Local.promise_step lc1 mem1' loc from to (Message.concrete val0 None) lc2 mem'
                             (Memory.op_kind_lower (Message.concrete val released)).
Proof.
  inv WRITE.
  inv PROMISE. des; subst. inv RESERVE.
  assert(Memory.le (Local.promises lc1) mem1').
  {
    inv CAP1. clear - LE SOUND.
    unfolds Memory.le; ii. eauto.
  }
  exploit Memory.lower_exists_le; [eapply H | eauto..]. ii.
  des.
  exists mem0.
  econs; eauto.
Qed.

Lemma lower_PF_consistent_construction
      lang st2 loc lc1 sc1 mem1
      from to val val0 released
      lc2 sc2 mem2 lo
      (PROM: Local.promise_step lc1 mem1 loc from to (Message.concrete val0 None) lc2 mem2
                                 (Memory.op_kind_lower (Message.concrete val released)))
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 sc2 mem2) lo)
      (LOCAL_WF: Local.wf lc1 mem1)
      (MEM_CLOSED: Memory.closed mem1):
  Thread.consistent (Thread.mk lang st2 lc1 sc1 mem1) lo.
Proof.
  assert(LOCAL_WF': Local.wf lc2 mem2).
  {
    inv PROM.
    eapply local_wf_promise; eauto. destruct lc1; eauto.
  }
  assert(MEM_CLOSED': Memory.closed mem2).
  {
    eapply promise_step_closed_mem; [eapply PROM | eapply LOCAL_WF | eauto..]. 
  }
  eapply Thread_consistent_to_consistent_nprm in CONS; eauto.
  assert(CAP_EXIST: exists mem2', Memory.cap mem2 mem2').
  {
    eapply Memory.cap_exists; eauto.
  }
  destruct CAP_EXIST as (mem2' & CAP_EXIST). 
  assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem2' sc1').
  {
    eapply Memory.max_concrete_timemap_exists.
    eapply Memory.cap_closed in CAP_EXIST; eauto.
    inv CAP_EXIST; eauto.
  } 
  destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
  lets CONS': MAX_CONCRETE_TM_EXIT.
  eapply CONS in CONS'; ss; eauto.
  destruct CONS' as (e2 & CONS' & FULFILL').
  unfold Thread.consistent; ss; ii. 
  exploit lower_PF_cap_exit; [idtac | eapply PROM | eauto..].
  inv LOCAL_WF; eauto. introv PROM'.
  destruct PROM' as (mem' & PROM').
  assert(LOCAL_WF'': Local.wf lc2 mem').
  {
    inv PROM'.
    eapply local_wf_promise; eauto.
    eapply Memory.cap_closed; eauto.
    eapply Local.cap_wf; eauto.
    destruct lc1; eauto.
  }
  assert(CLOSED_MEM'': Memory.closed mem').
  {
    eapply promise_step_closed_mem; eauto.
    eapply Local.cap_wf; eauto.
    eapply Memory.cap_closed; eauto.
  }
  eapply rtc_rtcn in CONS'. destruct CONS' as (n & CONS').
  destruct e2. 
  eapply additional_msg_consistent_construction with
      (inj := (spec_inj mem2'))
      (max_ts := Memory.max_ts loc mem2')
      (max_ts' := Time.join (Memory.max_ts loc mem2') (Memory.max_ts loc mem')) in CONS'; eauto. 
  destruct CONS' as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL'').
  {
    (* lower PF *)
    eexists. split.
    eapply Relation_Operators.rt1n_trans.
    econs.
    econs.
    eapply Thread.step_promise.
    econs; [eapply PROM' | eauto..].
    ss; eauto.
    eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
    ss.
  }
  {
    (* local wf *)
    eapply Local.cap_wf with (mem1 := mem2); eauto.
  }
  {
    (* closed memory *)
    eapply Memory.cap_closed with (mem1 := mem2); eauto.
  }
  {
    (* other identity injection *)
    instantiate (1 := loc).
    ii; eapply spec_inj_identity_inj; eauto.
  }
  {
    (* le max identity injection *)
    ii; eapply spec_inj_identity_inj; eauto.
  }
  {
    (* le max_ts *)
    eapply Time.join_l.
  }
  {
    (* msg injection *)
    econs.
    {
      ii.
      unfold spec_inj at 1. rewrite MSG.
      assert(GET1: Memory.get loc0 t mem2 = Some (f, Message.concrete val1 R)).
      { 
        eapply Memory.cap_inv with (mem1 := mem2) in MSG; eauto.
        des; ss.
      }
      exploit lower_PF_cap_get_stable; [eapply GET1 | eapply PROM | eauto..].
      ii.
      exists t f R. split; eauto. split; eauto.
      eapply spec_inj_optviewinj; eauto.
    }
    {
      ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem2') eqn:Heqe; ss; eauto. destruct p; ss. 
      destruct t1; ss. inv INJ.
      do 3 eexists; eauto. 
    }
    {
      eapply spec_inj_monotonic; eauto.
    }
  }
  {
    (* TView inj *)
    ss. eapply TViewInj_spec_inj_id.
  }
  {
    eapply spec_inj_implies_promises_inj; eauto.
    eapply Memory.cap_le; eauto. inv LOCAL_WF'; eauto.
  }
  {  
    ii.
    contradiction H0. clear H0.
    inv H1.
    econs; eauto. instantiate (1 := msg).
    assert(GET1: Memory.get loc0 to0 mem0 = Some (from0, msg)).
    {     
      clear - PROM' GET H.
      inv PROM'. inv PROMISE. des; subst. inv RESERVE.
      erewrite Memory.lower_o in GET; eauto.
      des_ifH GET; subst; des; ss.
    }
    cut(mem1 loc0 = mem2 loc0). ii.   
    eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem2') in H0; eauto.
    unfolds Memory.get. rewrite <- H0; eauto.
    clear - PROM H.
    inv PROM. inv PROMISE. des; ss. inv RESERVE.
    inv MEM. inv LOWER.
    assert(LocFun.find loc0 (LocFun.add loc r mem1) = mem1 loc0).
    rewrite LocFun.add_spec_neq; ss.
    unfold LocFun.find in *; ss.
  }
  {
    (* loc covered *)
    clear - MEM_CLOSED' CAP_EXIST. ii.
    exploit Memory.cap_max_ts; eauto.
    instantiate (1 := loc); ii.
    inv H1.
    assert(ts <> Time.bot).
    {
      intro; subst.
      inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
    }
    eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
    contradiction H.
    des; subst.
    eapply CAP_EXIST.
    rewrite H2 in H0.
    econs; ss.
    destruct (Time.le_lt_dec Time.bot ts); eauto.
    eapply Time.le_lteq in l; des; ss. subst; ss.
    eapply Time_lt_bot_false in l; ss.
  }
  {
    (* spec view *)
    eapply spec_view_intro_le_max_ts.
    { 
      exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
      instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS. 
      cut(Time.le (View.rlx (TView.acq (Local.tview lc2)) loc)
                  (Memory.max_ts loc mem2)).
      ii. eapply Time.le_lteq. left.
      eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
      eapply Time.incr_spec.
      clear - LOCAL_WF PROM.
      inv LOCAL_WF. clear TVIEW_WF PROMISES FINITE BOT.
      inv PROM. inv PROMISE; des; subst; ss.
      {
        (* lower *)
        inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
        specialize (RLX loc). des.
        eapply Memory.lower_get1 in RLX; eauto. des.
        eapply Memory.max_ts_spec in GET2; des; ss.
      }
    }
    {
      eapply Cover.gt_max_not_covered.
    }
    {  
      ii. eapply Time_lt_join in H. destruct H. inv H0.
      inv PROM'. inv PROMISE; des; subst; ss. inv RESERVE.
      {
        (* lower *)
        eapply Memory.max_ts_spec in GET; des.
        clear - H1 MAX ITV.
        inv ITV; ss.  
        eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2 in TO; eauto.
        eapply TO in MAX.
        eapply Time_le_gt_false in MAX; eauto. 
      }
    }
  }
  {
    (* max cover *)
    clear - CAP_EXIST MEM_CLOSED'.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
    inv CAP_EXIST.
    specialize (BACK loc).
    rewrite H; eauto.
  }
  {
    (* promise le *)
    ss.
    clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
    inv LOCAL_WF'; ss; ii.
    eapply PROMISES in H.
    eapply Memory.max_ts_spec in H; eauto; des.
    exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
    rewrite H.
    cut(Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))); ii.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
Qed. 

Lemma write_step_attached_consistent_construction
      lang (e e' e'': Thread.t lang) from loc ts to val released ordw lo
      (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
      (CLOSED: Memory.closed (Thread.memory e))
      (PROG: Thread.program_step (ThreadEvent.write loc from ts val released ordw) lo e e')
      (ATTACH_RESERVE: 
         Thread.promise_step false (ThreadEvent.promise loc ts to Message.reserve Memory.op_kind_add) e' e'')
      (CONS: Thread.consistent e'' lo):
  exists e0,
    rtc (Thread.reserve_step lo) e e0 /\ Thread.consistent e0 lo.
Proof.
  inv PROG; ss. inv ATTACH_RESERVE; ss.
  inv LOCAL; ss.
  exploit reorder_write_reserve; eauto. ii. des.
  - (* not add: reorder *)
    destruct kind.
    {
      (* add *)
      eapply write_add_step_consistent_construction in H0; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply H. ss.
      eapply Relation_Operators.rt1n_trans.
      eapply H0. eauto.
      eauto. 
      inv H. 
      eapply local_wf_promise; eauto. destruct lc1; eauto.
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* split *)
      eapply write_not_add_step_consistent_construction in H0; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply H. ss.  
      eauto.
      eauto.
      intro; ss.
      inv H. 
      eapply local_wf_promise; eauto. destruct lc1; eauto.
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* lower *)
      eapply write_not_add_step_consistent_construction in H0; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply H. ss.  
      eauto.
      eauto.
      intro; ss.
      inv H. 
      eapply local_wf_promise; eauto. destruct lc1; eauto.
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* cancel *)
      inv H. inv H0. ss. inv WRITE. inv PROMISE0. ss.
    }
  - (* add *)
    subst. clear H H0 PF. 
    assert(LOCAL_WF': Local.wf lc3 mem3).
    {
      inv LOCAL0.
      eapply local_wf_promise; eauto.
      eapply write_step_closed_mem; eauto.
      destruct lc1, lc2.
      eapply local_wf_write; eauto.
    }
    assert(MEM_CLOSED': Memory.closed mem3).
    {
      eapply promise_step_closed_mem; eauto.
      eapply local_wf_write; eauto.
      eapply write_step_closed_mem; eauto.
    }
    eapply Thread_consistent_to_consistent_nprm in CONS; eauto; ss.
    assert(CAP_EXIST: exists mem3', Memory.cap mem3 mem3').
    {
      eapply Memory.cap_exists; eauto.
    } 
    destruct CAP_EXIST as (mem3' & CAP_EXIST). 
    assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem3' sc1').
    {
      eapply Memory.max_concrete_timemap_exists.
      eapply Memory.cap_closed in CAP_EXIST; eauto.
      inv CAP_EXIST; eauto.
    }  
    destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
    assert(LT_ADD1: Time.lt from ts).
    {
      clear - LOCAL1.
      destruct lc1, lc2. eapply MemoryProps.write_msg_wf in LOCAL1; des; ss.
    }
    assert(LT_ADD2: Time.lt ts to).
    {
      clear - LOCAL0.
      inv LOCAL0. inv PROMISE. inv MEM. inv ADD; eauto.
    }
    inv LOCAL0. inv LOCAL1. ss.
    inv WRITE; ss. inv PROMISE; ss.
    inv PROMISE0.
    assert(NOT_COVER1: forall t, Interval.mem (from, ts) t -> ~ Cover.covered loc t mem1).
    {
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    }
    assert(NOT_COVER2: forall t, Interval.mem (ts, to) t -> ~ Cover.covered loc t mem1).
    {
      clear - MEM MEM0.
      cut(forall t, Interval.mem (ts, to) t -> ~ Cover.covered loc t mem2). intro.
      intros. eapply H in H0; eauto. intro. contradiction H0.
      eapply Cover.add_covered; eauto.
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    }
    assert(NOT_COVER: forall t, Interval.mem (from, to) t -> ~ Cover.covered loc t mem1).
    {
      clear - NOT_COVER1 NOT_COVER2 LT_ADD1 LT_ADD2. ii.   
      eapply Interval.mem_split with (mb := ts) in H; eauto.
      destruct H; eauto.
      eapply NOT_COVER1; eauto. eapply NOT_COVER2; eauto.
      econs; ss. eapply Time.le_lteq; eauto.
    }
    (* reserve *)
    assert(MEM_ADD: exists mem', Memory.add mem1 loc from to Message.reserve mem').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_ADD1. eapply LT_ADD2.
      econstructor; eauto.
    }
    destruct MEM_ADD as (mem' & MEM_ADD).
    assert(PRM_ADD: exists promises',
              Memory.add (Local.promises lc1) loc from to Message.reserve promises').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2; eauto.
      econstructor.
      clear - LOCAL_WF NOT_COVER.
      ii.
      eapply NOT_COVER in H.
      contradiction H.
      inv LOCAL_WF; eauto.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD as (promises' & PRM_ADD).
    exists (Thread.mk lang st1 (Local.mk (Local.tview lc1) promises') sc1 mem').
    split.
    econs. econs. econs. econs. econs.
    eapply PRM_ADD.
    eapply MEM_ADD.
    econstructor; eauto.
    ii; des; ss.
    econstructor; eauto.
    ss.
    ss.
    eauto.
    unfold Thread.consistent; ss.
    ii. 
    exploit CONS; simpl; [eapply CAP_EXIST | eauto..].
    introv CONS'. destruct CONS' as (e2 & TAU_STEPS & FULFILL).  
    assert(REMOVE_RSV_MEM: 
             exists mem0', Memory.remove mem0 loc from to Message.reserve mem0').
    {
      eapply Memory.remove_exists.
      cut (Memory.get loc to mem' = Some (from, Message.reserve)).
      clear - CAP; ii.
      inv CAP; eauto.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_MEM as (mem0' & REMOVE_RSV_MEM).
    assert(REMOVE_RSV_PRM: exists promises0',
              Memory.remove promises' loc from to Message.reserve promises0').
    {
      eapply Memory.remove_exists.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_PRM as (promises0' & REMOVE_RSV_PRM).
    assert(REMOVE_NOT_COVER: 
             forall t, Interval.mem (from, to) t -> ~ Cover.covered loc t mem0').
    {
      eapply Cover.remove_not_cover; eauto.
    }
    assert(PRM_LE: Memory.le promises0' mem0').
    {
      eapply Memory.promise_le with (promises1 := promises') (mem1 := mem0); eauto.
      eapply Memory.cap_le; eauto.
      eapply Memory.promise_le with (promises1 := Local.promises lc1) (mem1 := mem1); eauto.
      inv LOCAL_WF; eauto.
      econstructor; eauto.
      ii; des.
      ss.
    }
    assert(WRITE': exists mem1',
              Memory.write promises0' mem0' loc from ts val
                           (TView.write_released (Local.tview lc1) sc1 loc ts None ordw)
                           promises0' mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      {
        clear - REMOVE_NOT_COVER LT_ADD1 LT_ADD2. ii.
        eapply REMOVE_NOT_COVER; eauto.
        inv H; ss. econs; eauto; ss. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; eauto.
      }
      { 
        inv TS0; eauto.
      }
      {
        clear - LT_ADD1 LT_ADD2  REMOVE_NOT_COVER.
        introv CONTR. inv CONTR. des.
        destruct(Time.le_lt_dec x to).
        {
          specialize (REMOVE_NOT_COVER x).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD1; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD1; ss.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
        {
          specialize (REMOVE_NOT_COVER to).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.le_lteq. eauto.
          econs; ss; eauto.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
      }
      {
        clear - MEM0.
        inv MEM0. inv ADD; ss.
      }
    }
    destruct WRITE' as (mem1' & WRITE'). 
    assert(PRM_LE': Memory.le promises0' mem1').
    { eapply MemoryProps.write_memory_le; eauto. }
    assert(STILL_NOT_COVER: 
             forall t, Interval.mem (ts, to) t -> ~ Cover.covered loc t mem1').
    {
      clear - REMOVE_NOT_COVER WRITE' LT_ADD1 LT_ADD2.
      inv WRITE'. inv PROMISE. ii. specialize (REMOVE_NOT_COVER t).
      eapply REMOVE_NOT_COVER; eauto. 
      inv H; ss. econs; eauto; ss. eapply Time.Time.lt_strorder_obligation_2; eauto.
      eapply Cover.add_covered in H0; eauto. des; eauto.
      inv H. inv H1. ss.
      eapply TimeFacts.lt_le_lt in FROM; eauto.
      eapply Time.Time.lt_strorder_obligation_1 in FROM; ss.
    }
    assert(MEM_ADD': exists mem2', Memory.add mem1' loc ts to Message.reserve mem2').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      econstructor; eauto.
    }
    destruct MEM_ADD' as (mem2' & MEM_ADD').
    assert(PRM_ADD': exists promises2',
              Memory.add promises0' loc ts to Message.reserve promises2').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      econstructor.
      clear - PRM_LE' STILL_NOT_COVER.
      ii.
      eapply STILL_NOT_COVER in H.
      contradiction H.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD' as (promises2' & PROM_ADD').
    eapply rtc_rtcn in TAU_STEPS.
    destruct TAU_STEPS as (n & TAU_STEPS). destruct e2.
    assert(LOCAL_WRITE: 
             Local.write_step (Local.mk (Local.tview lc1) promises0') sc0 mem0' loc
                              from ts val None
                              (TView.write_released (Local.tview lc1) sc1 loc ts None ordw) ordw
                              (Local.mk (TView.write_tview (Local.tview lc1) sc1 loc ts ordw) promises0')
                              sc0 mem1' Memory.op_kind_add lo).
    {
      econs; ss.
      clear - WRITABLE. inv WRITABLE. econs; eauto.
      eapply WRITE'.
      introv NONSYNC. eapply RELEASE in NONSYNC.
      clear - NONSYNC PRM_ADD REMOVE_RSV_PRM.
      eapply reserve_non_synch_loc in PRM_ADD; eauto.      
      eapply remove_non_synch_loc in REMOVE_RSV_PRM; eauto.
    } 
    assert(LOCAL_PROMISE: 
             Local.promise_step (Local.mk (TView.write_tview (Local.tview lc1) sc1 loc ts ordw) promises0') mem1'
                                loc ts to Message.reserve
                                (Local.mk (TView.write_tview (Local.tview lc1) sc1 loc ts ordw) promises2') mem2'
                                Memory.op_kind_add).
    {
      econs; ss. econs; eauto. ii; ss.
    }
    assert(ADD_LT_MAX: Time.lt ts (Memory.max_ts loc mem3)).
    {
      eapply Memory.add_get0 in MEM; eauto.
      clear - MEM LT_ADD2. des.
      eapply Memory.max_ts_spec in GET0. des.
      eapply TimeFacts.lt_le_lt; eauto.
    }
    assert(ADD_LE_MAX: Time.le to (Memory.max_ts loc mem3)).
    {
      eapply Memory.add_get0 in MEM; eauto.
      clear - MEM LT_ADD2. des.
      eapply Memory.max_ts_spec in GET0. des. eauto.
    }
    assert(LOCAL_WF'': Local.wf {| Local.tview := Local.tview lc1; Local.promises := promises0' |} mem0').
    {
      eapply local_wf_promise.
      eapply Memory.promise_cancel. eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM. ss.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      ss.
      eapply Local.cap_wf with (mem1 := mem'); eauto.
      eapply local_wf_promise.
      eapply Memory.promise_add. eapply PRM_ADD. eapply MEM_ADD.
      ss.
      ii; ss.
      ss.
      ss.
      destruct lc1; ss.
    }
    assert(PROM_EQ: promises2 = promises2').
    {
      eapply MemoryMerge.MemoryMerge.add_remove in PRM_ADD; eauto. subst.  
      eapply MemoryMerge.MemoryMerge.add_remove in PROMISES0; eauto. subst.
      clear - PROMISES PROM_ADD'.
      eapply Memory.ext. ii.
      destruct (Memory.get loc0 ts0 promises2) as [[from' msg'] | ] eqn:GET1.
      erewrite Memory.add_o in GET1; eauto.
      des_ifH GET1; ss; des; subst; ss. inv GET1.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
      erewrite Memory.add_o in GET1; eauto.
      des_ifH GET1; ss.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
    }
    eapply additional_msg_consistent_construction with
        (inj := (spec_inj mem3'))
        (max_ts := Memory.max_ts loc mem3')
        (max_ts' := Time.join (Memory.max_ts loc mem3') (Memory.max_ts loc mem0)) in TAU_STEPS.
    destruct TAU_STEPS as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL').
    {
      eexists. split.
      (* cancel the reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_promise.
      econs.
      econs; ss.
      eapply Memory.promise_cancel.
      eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM.
      ss. ss. ss.
      (* write add *) 
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_program.
      econs.
      instantiate (2 := ThreadEvent.write loc from ts val
                                          (TView.write_released (Local.tview lc1) sc1 loc ts None ordw) ordw).
      ss. eapply STATE.
      eapply Local.step_write.
      eapply LOCAL_WRITE.
      ss.
      (* reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs. 
      eapply Thread.step_promise.
      econs. eauto. eauto. ss.
      eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
      ss.
    }
    {
      (* local wf *)
      eapply Local.cap_wf with (mem1 := mem3); eauto.
    }
    {
      (* local wf *) 
      cut(Memory.closed mem0'). i.
      inv LOCAL_PROMISE. inv LC2. ss.
      eapply local_wf_promise; eauto.
      eapply write_step_closed_mem; eauto.
      eapply local_wf_write; eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* closed memory *)
      eapply Memory.cap_closed with (mem1 := mem3); eauto.
    }
    {
      (* closed memory *)
      eapply Memory.add_closed; eauto.
      eapply write_step_closed_mem; ss.
      eapply LOCAL_WRITE.
      eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* other identity injection *)
      instantiate (1 := loc).
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max identity injection *)
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max_ts *)
      eapply Time.join_l.
    }
    {
      (* msg injection *)
      econs.
      {
        ii.
        unfold spec_inj at 1. rewrite MSG.
        exists t f R. split; eauto.
        split. eapply spec_inj_optviewinj; eauto. 
        assert(GET1: Memory.get loc0 t mem3 = Some (f, Message.concrete val0 R)).
        {
          eapply Memory.cap_inv in MSG; eauto.
          des; ss.
        }
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o; eauto. 
        des_if.
        {
          ss; des; subst.
          erewrite Memory.add_o in GET1; eauto.
          des_ifH GET1; ss.
          destruct o; ss.
        }
        {
          ss.
          erewrite Memory.add_o with (mem1 := mem2) in GET1; eauto.
          des_ifH GET1; ss.
          erewrite Memory.add_o with (mem1 := mem1) in GET1; eauto.
          des_ifH GET1; ss. inv GET1.
          destruct a; subst; ss. destruct o; subst; ss. 
          erewrite Memory.add_o; eauto. des_if; ss. destruct o; ss. 
          erewrite Memory.add_o; eauto. des_if; ss. destruct a; subst; ss. destruct o1; ss.
          eapply Memory.concrete_msg_remove_rsv_stable with (mem := mem0); eauto.
          inv CAP.
          eapply SOUND; eauto.
          erewrite Memory.add_o; eauto.
          des_if; eauto; ss. des; subst; ss.
        }
      }
      {
        ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem3') eqn:Heqe; ss; eauto. destruct p; ss. 
        destruct t1; ss. inv INJ.
        do 3 eexists; eauto. 
      }
      {
        eapply spec_inj_monotonic; eauto.
      }
    }
    {
      (* TView inj *)
      ss. eapply TViewInj_spec_inj_id.
    }
    {
      (* promise eq *)
      ss. subst promises2'.
      eapply spec_inj_implies_promises_inj; eauto.
      eapply Memory.cap_le; eauto.
      inv LOCAL_WF'; eauto.
    }
    {
      (* OTHER COVER *)
      ii.
      contradiction H0. clear H0.
      inv H1. 
      assert(GET1: Memory.get loc0 to0 mem0' = Some (from0, msg)).
      {      
        clear - WRITE' LOCAL_PROMISE GET H. 
        inv WRITE'. inv PROMISE.
        inv LOCAL_PROMISE. inv LC2. ss. inv PROMISE.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
      }
      erewrite Memory.remove_o with (mem1 := mem0) in GET1; eauto.
      des_ifH GET1; ss.
      cut(mem' loc0 = mem3 loc0). ii.  
      eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem3') in H0; eauto.
      econs. 
      unfolds Memory.get.
      rewrite <- H0; eauto.
      ss.
      eapply Memory.add_closed; eauto. 
      clear - MEM_ADD MEM0 MEM H.
      inv MEM_ADD; inv MEM; inv MEM0. inv ADD0; inv ADD; inv ADD1.
      rewrite IdentFun.add_add_eq.
      assert(LocFun.find loc0 (LocFun.add loc r mem1) = LocFun.find loc0 (LocFun.add loc r0 mem1)).
      rewrite LocFun.add_spec_neq; ss. rewrite LocFun.add_spec_neq; ss.
      unfold LocFun.find in *; ss.
    }
    {
      (* loc0 cover *) 
      clear - MEM_CLOSED' CAP_EXIST. ii.
      exploit Memory.cap_max_ts; eauto.
      instantiate (1 := loc); ii.
      inv H1.
      assert(ts <> Time.bot).
      {
        intro; subst.
        inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
      }
      eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
      contradiction H.
      des; subst.
      eapply CAP_EXIST.
      rewrite H2 in H0.
      econs; ss.
      destruct (Time.le_lt_dec Time.bot ts); eauto.
      eapply Time.le_lteq in l; des; ss. subst; ss.
      eapply Time_lt_bot_false in l; ss.
    }
    { 
      (* spec view *)
      ss. 
      eapply spec_view_intro_le_max_ts.
      {
        exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
        instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
        cut(Time.le (TimeMap.join (View.rlx (TView.acq (Local.tview lc1))) (TimeMap.singleton loc ts) loc)
                    (Memory.max_ts loc mem3)).
        ii. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
        eapply Time.incr_spec.
        eapply Time.join_spec.
        { 
          clear - LOCAL_WF' MEM.
          inv LOCAL_WF'. clear TVIEW_WF PROMISES FINITE BOT. ss.
          inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
          specialize (RLX loc). des. 
          eapply Memory.max_ts_spec in RLX; des; ss.
          unfolds TimeMap.join.
          eapply Time_le_join in MAX; des; eauto.
        }
        {
          unfold TimeMap.singleton.
          cut(LocFun.find loc (LocFun.add loc ts (LocFun.init Time.bot)) = ts). ii.
          unfolds LocFun.find. rewrite H. eapply Time.le_lteq; eauto.
          rewrite LocFun.add_spec_eq; eauto.
        }
      }
      {
        eapply Cover.gt_max_not_covered.
      }
      {
        ii. eapply Time_lt_join in H. destruct H. inv H0.
        inv LOCAL_PROMISE; ss. inv LC2. inv PROMISE.
        erewrite Memory.add_o in GET; eauto. 
        des_ifH GET; ss.
        {
          des; subst. inv GET. 
          clear - H ITV ADD_LE_MAX CAP_EXIST MEM_CLOSED'.
          inv ITV; ss.
          eapply Memory.cap_max_ts in CAP_EXIST; eauto.
          rewrite CAP_EXIST in H.
          cut(Time.lt to ts'); ii.
          eapply Time_le_gt_false in TO; eauto.
          eapply TimeFacts.le_lt_lt; eauto.
          eapply Time.Time.lt_strorder_obligation_2. 2: eapply H.
          eapply Time.incr_spec.
        }
        {
          destruct o; ss. 
          clear - H ITV GET H0 REMOVE_RSV_MEM WRITE' ADD_LT_MAX ADD_LE_MAX CAP_EXIST H1 MEM_CLOSED'.
          inv WRITE'. inv PROMISE.
          erewrite Memory.add_o in GET; eauto.
          des_ifH GET. des; ss; subst.
          inv ITV; ss.
          eapply Memory.cap_max_ts in CAP_EXIST; eauto.
          rewrite CAP_EXIST in H.
          cut(Time.lt ts ts'); ii.
          eapply Time_le_gt_false in TO; eauto. clear FROM H1.
          eapply TimeFacts.le_lt_lt; eauto. 
          eapply Time.le_lteq. left.  
          eapply Time.Time.lt_strorder_obligation_2. eapply ADD_LT_MAX.
          eapply Time.incr_spec.
          des; ss; subst; ss. 
          erewrite Memory.remove_o in GET; eauto.
          des_ifH GET; ss; des; subst; ss.
          eapply Memory.max_ts_spec in GET; des.
          inv ITV; ss. 
          cut(Time.lt (Memory.max_ts loc mem0) to0). ii.
          clear - MAX H2. eapply Time_le_gt_false in MAX; eauto. 
          eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto.
        }
      }
    }
    {
      (* max cover *)
      clear - CAP_EXIST MEM_CLOSED'.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      inv CAP_EXIST.
      specialize (BACK loc).
      rewrite H; eauto.
    }
    {
      (* promise le *)
      ss.
      clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
      inv LOCAL_WF'; ss; ii.
      eapply PROMISES in H.
      eapply Memory.max_ts_spec in H; eauto; des.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      rewrite H.
      cut(Time.lt (Memory.max_ts loc mem3) (Time.incr (Memory.max_ts loc mem3))); ii.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    {
      (* FULFill *)
      ss.
    }
Qed.

Lemma update_step_attached_consistent_construction
      lang (e e' e'': Thread.t lang) tsr loc tsw to valr valw releasedr released ordr ordw lo
      (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
      (CLOSED: Memory.closed (Thread.memory e))
      (PROG: Thread.program_step (ThreadEvent.update loc tsr tsw valr valw releasedr released ordr ordw) lo e e')
      (ATTACH_RESERVE: 
         Thread.promise_step false (ThreadEvent.promise loc tsw to Message.reserve Memory.op_kind_add) e' e'')
      (CONS: Thread.consistent e'' lo):
  exists e0,
    rtc (Thread.reserve_step lo) e e0 /\ Thread.consistent e0 lo.
Proof.
  inv PROG; ss. inv ATTACH_RESERVE; ss.
  inv LOCAL; ss. 
  exploit reorder_write_reserve; eauto. ii. des.
  - (* not add: reorder *)
    exploit reorder_read_reservation; eauto. ii; des.
    destruct kind.
    {
      (* add *)
      eapply update_add_step_consistent_construction in H0; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply H1. ss.
      eapply Relation_Operators.rt1n_trans.
      eapply H0. eauto.
      eauto.  
      inv H1.
      eapply local_wf_promise; eauto. destruct lc1; eauto.
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* split *)
      eapply update_not_add_step_consistent_construction in H0; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply H1. ss.  
      eauto.
      eauto.
      intro; ss.
      inv H1. 
      eapply local_wf_promise; eauto. destruct lc1; eauto.
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* lower *)
      eapply update_not_add_step_consistent_construction in H0; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply H1. ss.  
      eauto.
      eauto.
      intro; ss.
      inv H1. 
      eapply local_wf_promise; eauto. destruct lc1; eauto.
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* cancel *)
      inv H0. inv WRITE. inv PROMISE. ss.
    }
  - (* add *)
    subst. clear H H0 PF.
    assert(CLOSED_OPT_VIEW: Memory.closed_opt_view releasedr mem1).
    {
      clear - LOCAL1 CLOSED. inv CLOSED. inv LOCAL1.
      exploit CLOSED0; eauto. ii; des. inv MSG_CLOSED; eauto.
    }
    assert(LOCAL_WF_READ: Local.wf lc4 mem1).
    {
      eapply local_wf_read; eauto.
    }
    assert(LOCAL_WF': Local.wf lc3 mem3).
    {
      inv LOCAL0.
      eapply local_wf_promise; eauto. 
      eapply write_step_closed_mem; [| eapply LOCAL2 | eauto..]; eauto.
      destruct lc1, lc2.
      eapply local_wf_write; eauto.
    }
    assert(MEM_CLOSED': Memory.closed mem3).
    {
      eapply promise_step_closed_mem; eauto.
      eapply local_wf_write; eauto.
      eapply write_step_closed_mem; eauto.
    }
    eapply Thread_consistent_to_consistent_nprm in CONS; eauto; ss.
    assert(CAP_EXIST: exists mem3', Memory.cap mem3 mem3').
    {
      eapply Memory.cap_exists; eauto.
    } 
    destruct CAP_EXIST as (mem3' & CAP_EXIST). 
    assert(MAX_CONCRETE_TM_EXIT: exists sc1', Memory.max_concrete_timemap mem3' sc1').
    {
      eapply Memory.max_concrete_timemap_exists.
      eapply Memory.cap_closed in CAP_EXIST; eauto.
      inv CAP_EXIST; eauto.
    }  
    destruct MAX_CONCRETE_TM_EXIT as (sc1' & MAX_CONCRETE_TM_EXIT).
    assert(LT_ADD1: Time.lt tsr tsw).
    {
      clear - LOCAL2.
      destruct lc4, lc2. eapply MemoryProps.write_msg_wf in LOCAL2; des; ss.
    }
    assert(LT_ADD2: Time.lt tsw to).
    {
      clear - LOCAL0.
      inv LOCAL0. inv PROMISE. inv MEM. inv ADD; eauto.
    }
    inv LOCAL0. inv LOCAL2. ss.
    inv WRITE; ss. inv PROMISE; ss.
    inv PROMISE0.
    assert(NOT_COVER1: forall t, Interval.mem (tsr, tsw) t -> ~ Cover.covered loc t mem1).
    {
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    }
    assert(NOT_COVER2: forall t, Interval.mem (tsw, to) t -> ~ Cover.covered loc t mem1).
    {
      clear - MEM MEM0.
      cut(forall t, Interval.mem (tsw, to) t -> ~ Cover.covered loc t mem2). intro.
      intros. eapply H in H0; eauto. intro. contradiction H0.
      eapply Cover.add_covered; eauto.
      eapply MemoryProps.memory_add_cover_disjoint; eauto.
    }
    assert(NOT_COVER: forall t, Interval.mem (tsr, to) t -> ~ Cover.covered loc t mem1).
    {
      clear - NOT_COVER1 NOT_COVER2 LT_ADD1 LT_ADD2. ii.   
      eapply Interval.mem_split with (mb := tsw) in H; eauto.
      destruct H; eauto.
      eapply NOT_COVER1; eauto. eapply NOT_COVER2; eauto.
      econs; ss. eapply Time.le_lteq; eauto.
    }
    (* reserve *)
    assert(MEM_ADD: exists mem', Memory.add mem1 loc tsr to Message.reserve mem').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2. eapply LT_ADD1. eapply LT_ADD2.
      econstructor; eauto.
    }
    destruct MEM_ADD as (mem' & MEM_ADD).
    assert(PRM_ADD: exists promises',
              Memory.add (Local.promises lc1) loc tsr to Message.reserve promises').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      eapply Time.Time.lt_strorder_obligation_2; eauto.
      econstructor.
      clear - LOCAL_WF NOT_COVER.
      ii.
      eapply NOT_COVER in H.
      contradiction H.
      inv LOCAL_WF; eauto.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD as (promises' & PRM_ADD).
    exists (Thread.mk lang st1 (Local.mk (Local.tview lc1) promises') sc1 mem').
    split.
    econs. econs. econs. econs. econs.
    eapply PRM_ADD.
    eapply MEM_ADD.
    econstructor; eauto.
    ii; des; ss.
    econstructor; eauto.
    ss.
    ss.
    eauto.
    unfold Thread.consistent; ss.
    ii. 
    exploit CONS; simpl; [eapply CAP_EXIST | eauto..].
    introv CONS'. destruct CONS' as (e2 & TAU_STEPS & FULFILL).  
    assert(REMOVE_RSV_MEM: 
             exists mem0', Memory.remove mem0 loc tsr to Message.reserve mem0').
    {
      eapply Memory.remove_exists.
      cut (Memory.get loc to mem' = Some (tsr, Message.reserve)).
      clear - CAP; ii.
      inv CAP; eauto.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_MEM as (mem0' & REMOVE_RSV_MEM).
    assert(REMOVE_RSV_PRM: exists promises0',
              Memory.remove promises' loc tsr to Message.reserve promises0').
    {
      eapply Memory.remove_exists.
      eapply Memory.add_get0; eauto.
    }
    destruct REMOVE_RSV_PRM as (promises0' & REMOVE_RSV_PRM).
    assert(REMOVE_NOT_COVER: 
             forall t, Interval.mem (tsr, to) t -> ~ Cover.covered loc t mem0').
    {
      eapply Cover.remove_not_cover; eauto.
    }
    assert(PRM_LE: Memory.le promises0' mem0').
    {
      eapply Memory.promise_le with (promises1 := promises') (mem1 := mem0); eauto.
      eapply Memory.cap_le; eauto.
      eapply Memory.promise_le with (promises1 := Local.promises lc1) (mem1 := mem1); eauto.
      inv LOCAL_WF; eauto.
      econstructor; eauto.
      ii; des.
      ss.
    }
    assert(WRITE': exists mem1',
              Memory.write promises0' mem0' loc tsr tsw valw
                           (TView.write_released (Local.tview lc4) sc1 loc tsw releasedr ordw)
                           promises0' mem1' Memory.op_kind_add).
    {
      eapply MemoryProps.write_succeed_valid; eauto.
      {
        clear - REMOVE_NOT_COVER LT_ADD1 LT_ADD2. ii.
        eapply REMOVE_NOT_COVER; eauto.
        inv H; ss. econs; eauto; ss. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; eauto.
      }
      { 
        inv TS0; eauto.
      }
      {
        clear - LT_ADD1 LT_ADD2  REMOVE_NOT_COVER.
        introv CONTR. inv CONTR. des.
        destruct(Time.le_lt_dec x to).
        {
          specialize (REMOVE_NOT_COVER x).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD1; ss.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          econs; ss; eauto.
          eapply Memory.get_ts in GET; eauto; ss; des; subst.
          eapply Time_lt_bot_false in LT_ADD1; ss.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
        {
          specialize (REMOVE_NOT_COVER to).
          contradiction REMOVE_NOT_COVER; eauto.
          econs; ss; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.le_lteq. eauto.
          econs; ss; eauto.
          econs; ss; eauto.
          eapply Time.le_lteq. eauto.
        }
      }
      {
        clear - MEM0.
        inv MEM0. inv ADD; ss.
      }
    }
    destruct WRITE' as (mem1' & WRITE'). 
    assert(PRM_LE': Memory.le promises0' mem1').
    { eapply MemoryProps.write_memory_le; eauto. }
    assert(STILL_NOT_COVER: 
             forall t, Interval.mem (tsw, to) t -> ~ Cover.covered loc t mem1').
    {
      clear - REMOVE_NOT_COVER WRITE' LT_ADD1 LT_ADD2.
      inv WRITE'. inv PROMISE. ii. specialize (REMOVE_NOT_COVER t).
      eapply REMOVE_NOT_COVER; eauto. 
      inv H; ss. econs; eauto; ss. eapply Time.Time.lt_strorder_obligation_2; eauto.
      eapply Cover.add_covered in H0; eauto. des; eauto.
      inv H. inv H1. ss.
      eapply TimeFacts.lt_le_lt in FROM; eauto.
      eapply Time.Time.lt_strorder_obligation_1 in FROM; ss.
    }
    assert(MEM_ADD': exists mem2', Memory.add mem1' loc tsw to Message.reserve mem2').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      econstructor; eauto.
    }
    destruct MEM_ADD' as (mem2' & MEM_ADD').
    assert(PRM_ADD': exists promises2',
              Memory.add promises0' loc tsw to Message.reserve promises2').
    {
      eapply Cover.not_covered_add_succ; ss; eauto.
      econstructor.
      clear - PRM_LE' STILL_NOT_COVER.
      ii.
      eapply STILL_NOT_COVER in H.
      contradiction H.
      eapply MemoryProps.memory_le_covered; eauto.
    }
    destruct PRM_ADD' as (promises2' & PROM_ADD').
    eapply rtc_rtcn in TAU_STEPS.
    destruct TAU_STEPS as (n & TAU_STEPS). destruct e2.
    assert(PROM_EQ0: Local.promises lc1 = Local.promises lc4).
    {
      inv LOCAL1; eauto.
    }
    assert(LOCAL_READ: 
             Local.read_step (Local.mk (Local.tview lc1) promises0') mem0' loc tsr valr releasedr ordr
                             (Local.mk (Local.tview lc4) promises0') lo).
    {
      inv LOCAL1; ss.
      econs; eauto. instantiate (1 := from).
      eapply Memory.concrete_msg_remove_rsv_stable; [ | eapply REMOVE_RSV_MEM | eauto..].
      inv CAP. eapply SOUND.
      eapply Memory.add_get1; eauto.
    }
    assert(LOCAL_WRITE: 
             Local.write_step (Local.mk (Local.tview lc4) promises0') sc0 mem0' loc
                              tsr tsw valw releasedr
                              (TView.write_released (Local.tview lc4) sc1 loc tsw releasedr ordw) ordw
                              (Local.mk (TView.write_tview (Local.tview lc4) sc1 loc tsw ordw) promises0')
                              sc0 mem1' Memory.op_kind_add lo).
    {
      econs; ss.
      clear - WRITABLE PROM_EQ0. inv WRITABLE. econs; eauto.
      eapply WRITE'.
      introv NONSYNC. eapply RELEASE in NONSYNC.
      clear - NONSYNC PRM_ADD REMOVE_RSV_PRM PROM_EQ0.
      rewrite <- PROM_EQ0 in NONSYNC.
      eapply reserve_non_synch_loc in PRM_ADD; eauto.      
      eapply remove_non_synch_loc in REMOVE_RSV_PRM; eauto.
    } 
    assert(LOCAL_PROMISE: 
             Local.promise_step (Local.mk (TView.write_tview (Local.tview lc4) sc1 loc tsw ordw) promises0') mem1'
                                loc tsw to Message.reserve
                                (Local.mk (TView.write_tview (Local.tview lc4) sc1 loc tsw ordw) promises2') mem2'
                                Memory.op_kind_add).
    {
      econs; ss. econs; eauto. ii; ss.
    }
    assert(ADD_LT_MAX: Time.lt tsw (Memory.max_ts loc mem3)).
    {
      eapply Memory.add_get0 in MEM; eauto.
      clear - MEM LT_ADD2. des.
      eapply Memory.max_ts_spec in GET0. des.
      eapply TimeFacts.lt_le_lt; eauto.
    }
    assert(ADD_LE_MAX: Time.le to (Memory.max_ts loc mem3)).
    {
      eapply Memory.add_get0 in MEM; eauto.
      clear - MEM LT_ADD2. des.
      eapply Memory.max_ts_spec in GET0. des. eauto.
    }
    assert(LOCAL_WF'': Local.wf {| Local.tview := Local.tview lc4; Local.promises := promises0' |} mem0').
    {
      eapply local_wf_promise.
      eapply Memory.promise_cancel. eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM. ss.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
      ss.
      eapply Local.cap_wf with (mem1 := mem'); eauto.
      eapply local_wf_promise.
      eapply Memory.promise_add. eapply PRM_ADD. eapply MEM_ADD.
      ss.
      ii; ss.
      ss.
      ss.
      destruct lc4; ss; subst; ss.
    }
    assert(PROM_EQ: promises2 = promises2').
    {
      eapply MemoryMerge.MemoryMerge.add_remove in PRM_ADD; eauto. subst.  
      eapply MemoryMerge.MemoryMerge.add_remove in PROMISES0; eauto. subst.
      clear - PROMISES PROM_ADD' PROM_EQ0. rewrite <- PROM_EQ0 in PROMISES. clear PROM_EQ0.
      eapply Memory.ext. ii.
      destruct (Memory.get loc0 ts promises2) as [[from' msg'] | ] eqn:GET1.
      erewrite Memory.add_o in GET1; eauto.
      des_ifH GET1; ss; des; subst; ss. inv GET1.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
      erewrite Memory.add_o in GET1; eauto.
      des_ifH GET1; ss.
      erewrite Memory.add_o; eauto. des_if; ss. des; ss.
    }
    eapply additional_msg_consistent_construction with
        (inj := (spec_inj mem3'))
        (max_ts := Memory.max_ts loc mem3')
        (max_ts' := Time.join (Memory.max_ts loc mem3') (Memory.max_ts loc mem0)) in TAU_STEPS.
    destruct TAU_STEPS as (st'' & lc'' & sc'' & mem'' & TAU_STEPS' & FULFILL').
    {
      eexists. split.
      (* cancel the reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_promise.
      econs.
      econs; ss.
      eapply Memory.promise_cancel.
      eapply REMOVE_RSV_PRM. eapply REMOVE_RSV_MEM.
      ss. ss. ss.
      (* update add *) 
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs.
      eapply Thread.step_program.
      econs.
      instantiate (2 := ThreadEvent.update loc tsr tsw valr valw releasedr
                                           (TView.write_released (Local.tview lc4) sc1 loc tsw releasedr ordw)
                                           ordr ordw).
      ss. eapply STATE.
      econs; eauto.
      ss.
      (* reserve *)
      eapply Relation_Operators.rt1n_trans.
      econs.
      econs. 
      eapply Thread.step_promise.
      econs. eauto. eauto. ss.
      eapply Thread_nprm_step_is_tau_step. eapply TAU_STEPS'.
      ss.
    }
    {
      (* local wf *)
      eapply Local.cap_wf with (mem1 := mem3); eauto.
    }
    {
      (* local wf *) 
      cut(Memory.closed mem0'). i.
      inv LOCAL_PROMISE. inv LC2. ss.
      eapply local_wf_promise; eauto.
      eapply write_step_closed_mem; [ | eapply LOCAL_WRITE | eauto..].
      eapply Memory.cancel_closed_opt_view; eauto.
      eapply Memory.cap_closed_opt_view; eauto.
      eapply Memory.add_closed_opt_view; eauto.
      eapply local_wf_write; eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed; eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* closed memory *)
      eapply Memory.cap_closed with (mem1 := mem3); eauto.
    }
    {
      (* closed memory *)
      eapply Memory.add_closed; eauto.
      eapply write_step_closed_mem; [ | eapply LOCAL_WRITE | eauto..].
      eapply Memory.cancel_closed_opt_view; eauto.
      eapply Memory.cap_closed_opt_view; eauto.
      eapply Memory.add_closed_opt_view; eauto.
      eapply Memory.cancel_closed; eauto.
      eapply Memory.cap_closed with (mem1 := mem'); eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      (* other identity injection *)
      instantiate (1 := loc).
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max identity injection *)
      ii; eapply spec_inj_identity_inj; eauto.
    }
    {
      (* le max_ts *)
      eapply Time.join_l.
    }
    {
      (* msg injection *)
      econs.
      {
        ii.
        unfold spec_inj at 1. rewrite MSG.
        exists t f R. split; eauto.
        split. eapply spec_inj_optviewinj; eauto. 
        assert(GET1: Memory.get loc0 t mem3 = Some (f, Message.concrete val R)).
        {
          eapply Memory.cap_inv in MSG; eauto.
          des; ss.
        }
        inv WRITE'.
        inv PROMISE.
        erewrite Memory.add_o; eauto. 
        des_if.
        {
          ss; des; subst.
          erewrite Memory.add_o in GET1; eauto.
          des_ifH GET1; ss.
          destruct o; ss.
        }
        {
          ss.
          erewrite Memory.add_o with (mem1 := mem2) in GET1; eauto.
          des_ifH GET1; ss.
          erewrite Memory.add_o with (mem1 := mem1) in GET1; eauto.
          des_ifH GET1; ss. inv GET1.
          destruct a; subst; ss. destruct o; subst; ss. 
          erewrite Memory.add_o; eauto. des_if; ss. destruct o; ss. 
          erewrite Memory.add_o; eauto. des_if; ss. destruct a; subst; ss. destruct o1; ss.
          eapply Memory.concrete_msg_remove_rsv_stable with (mem := mem0); eauto.
          inv CAP.
          eapply SOUND; eauto.
          erewrite Memory.add_o; eauto.
          des_if; eauto; ss. des; subst; ss.
        }
      }
      {
        ii. unfold spec_inj in INJ. destruct (Memory.get loc0 t mem3') eqn:Heqe; ss; eauto. destruct p; ss. 
        destruct t1; ss. inv INJ.
        do 3 eexists; eauto. 
      }
      {
        eapply spec_inj_monotonic; eauto.
      }
    }
    {
      (* TView inj *)
      ss. eapply TViewInj_spec_inj_id.
    }
    {
      (* promise eq *)
      ss. subst promises2'.
      eapply spec_inj_implies_promises_inj; eauto.
      eapply Memory.cap_le; eauto.
      inv LOCAL_WF'; eauto.
    }
    {
      (* OTHER COVER *)
      ii.
      contradiction H0. clear H0.
      inv H1. 
      assert(GET1: Memory.get loc0 to0 mem0' = Some (from, msg)).
      {      
        clear - WRITE' LOCAL_PROMISE GET H. 
        inv WRITE'. inv PROMISE.
        inv LOCAL_PROMISE. inv LC2. ss. inv PROMISE.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; subst; des; ss.
      }
      erewrite Memory.remove_o with (mem1 := mem0) in GET1; eauto.
      des_ifH GET1; ss.
      cut(mem' loc0 = mem3 loc0). ii.  
      eapply Memory.cap_slice_inj with (mem1' := mem0) (mem2' := mem3') in H0; eauto.
      econs. 
      unfolds Memory.get.
      rewrite <- H0; eauto.
      ss.
      eapply Memory.add_closed; eauto. 
      clear - MEM_ADD MEM0 MEM H.
      inv MEM_ADD; inv MEM; inv MEM0. inv ADD0; inv ADD; inv ADD1.
      rewrite IdentFun.add_add_eq.
      assert(LocFun.find loc0 (LocFun.add loc r mem1) = LocFun.find loc0 (LocFun.add loc r0 mem1)).
      rewrite LocFun.add_spec_neq; ss. rewrite LocFun.add_spec_neq; ss.
      unfold LocFun.find in *; ss.
    }
    {
      (* loc0 cover *) 
      clear - MEM_CLOSED' CAP_EXIST. ii.
      exploit Memory.cap_max_ts; eauto.
      instantiate (1 := loc); ii.
      inv H1.
      assert(ts <> Time.bot).
      {
        intro; subst.
        inv ITV; ss. eapply Time_lt_bot_false in FROM; ss.
      }
      eapply MemoryProps.memory_cap_covered in CAP_EXIST; eauto.
      contradiction H.
      des; subst.
      eapply CAP_EXIST.
      rewrite H2 in H0.
      econs; ss.
      destruct (Time.le_lt_dec Time.bot ts); eauto.
      eapply Time.le_lteq in l; des; ss. subst; ss.
      eapply Time_lt_bot_false in l; ss.
    }
    { 
      (* spec view *)
      ss. 
      eapply spec_view_intro_le_max_ts.
      {
        exploit Memory.cap_max_ts; [|eapply CAP_EXIST|eauto..]; ss.
        instantiate (1 := loc). introv MAX_TS. rewrite MAX_TS.
        cut(Time.le (TimeMap.join (View.rlx (TView.acq (Local.tview lc4))) (TimeMap.singleton loc tsw) loc)
                    (Memory.max_ts loc mem3)).
        ii. eapply Time.le_lteq. left.
        eapply TimeFacts.le_lt_lt; [eapply H | idtac ..].
        eapply Time.incr_spec.
        eapply Time.join_spec.
        {  
          clear - LOCAL_WF' MEM.
          inv LOCAL_WF'. clear TVIEW_WF PROMISES FINITE BOT. ss.
          inv TVIEW_CLOSED. inv ACQ. unfold Memory.closed_timemap in RLX.
          specialize (RLX loc). des. 
          eapply Memory.max_ts_spec in RLX; des; ss.
          unfolds TimeMap.join.
          eapply Time_le_join in MAX; des; eauto.
        }
        {
          unfold TimeMap.singleton.
          rewrite Loc_add_eq. eapply Time.le_lteq; eauto.
        }
      }
      {
        eapply Cover.gt_max_not_covered.
      }
      {
        ii. eapply Time_lt_join in H. destruct H. inv H0.
        inv LOCAL_PROMISE; ss. inv LC2. inv PROMISE.
        erewrite Memory.add_o in GET; eauto. 
        des_ifH GET; ss.
        {
          des; subst. inv GET. 
          clear - H ITV ADD_LE_MAX CAP_EXIST MEM_CLOSED'.
          inv ITV; ss.
          eapply Memory.cap_max_ts in CAP_EXIST; eauto.
          rewrite CAP_EXIST in H.
          cut(Time.lt to ts'); ii.
          eapply Time_le_gt_false in TO; eauto.
          eapply TimeFacts.le_lt_lt; eauto.
          eapply Time.Time.lt_strorder_obligation_2. 2: eapply H.
          eapply Time.incr_spec.
        }
        {
          destruct o; ss. 
          clear - H ITV GET H0 REMOVE_RSV_MEM WRITE' ADD_LT_MAX ADD_LE_MAX CAP_EXIST H1 MEM_CLOSED'.
          inv WRITE'. inv PROMISE.
          erewrite Memory.add_o in GET; eauto.
          des_ifH GET. des; ss; subst.
          inv ITV; ss.
          eapply Memory.cap_max_ts in CAP_EXIST; eauto.
          rewrite CAP_EXIST in H.
          cut(Time.lt tsw ts'); ii.
          eapply Time_le_gt_false in TO; eauto. clear FROM H1.
          eapply TimeFacts.le_lt_lt; eauto. 
          eapply Time.le_lteq. left.  
          eapply Time.Time.lt_strorder_obligation_2. eapply ADD_LT_MAX.
          eapply Time.incr_spec.
          des; ss; subst; ss. 
          erewrite Memory.remove_o in GET; eauto.
          des_ifH GET; ss; des; subst; ss.
          eapply Memory.max_ts_spec in GET; des.
          inv ITV; ss. 
          cut(Time.lt (Memory.max_ts loc mem0) to0). ii.
          clear - MAX H2. eapply Time_le_gt_false in MAX; eauto. 
          eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto.
        }
      }
    }
    {
      (* max cover *)
      clear - CAP_EXIST MEM_CLOSED'.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      inv CAP_EXIST.
      specialize (BACK loc).
      rewrite H; eauto.
    }
    {
      (* promise le *)
      ss.
      clear - LOCAL_WF' MEM_CLOSED' CAP_EXIST.
      inv LOCAL_WF'; ss; ii.
      eapply PROMISES in H.
      eapply Memory.max_ts_spec in H; eauto; des.
      exploit Memory.cap_max_ts; [eapply MEM_CLOSED' | eapply CAP_EXIST | eauto..]. ii.
      rewrite H.
      cut(Time.lt (Memory.max_ts loc mem3) (Time.incr (Memory.max_ts loc mem3))); ii.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    {
      (* FULFill *)
      ss.
    }
Qed.

Lemma consistent_construct_from_fulfill':
  forall n lang lo (e e': Thread.t lang)
    (FULFILL_STEPS: rtcn (Thread.nprm_step lo) n e e')
    (IS_FULFILL: Local.promises (Thread.local e') = Memory.bot)
    (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
    (CLOSED: Memory.closed (Thread.memory e)),
  exists e0 e1,
    rtc (Thread.cancel_step lo) e e0 /\ rtc (Thread.reserve_step lo) e0 e1 /\ 
    Thread.consistent e1 lo.
Proof.
  induction n; ii.
  - inv FULFILL_STEPS.
    do 2 eexists.
    split; eauto.
    split; eauto.
    unfold Thread.consistent; ii.
    eexists.
    split; eauto.
  - inv FULFILL_STEPS.
    inv A12.
    {
      (* program step *)
      destruct (classic (exists ordr, e0 = ThreadEvent.fence ordr Ordering.seqcst)).
      {
        (* sc fence *)
        des; subst.
        inv PROG; ss.
        inv LOCAL; ss.
        inv LOCAL0; ss.
        exploit PROMISES; eauto. ii.
        do 2 eexists.
        split; eauto.
        split; eauto.
        unfold Thread.consistent; ii; ss.
        eexists.
        split; eauto.
      }
      {
        eapply IHn in A23; eauto. des.
        eapply rtc_rtcn in A23; destruct A23 as (n0 & CCLs).
        eapply reorder_not_rsv_ccl_scfence_step_cancel_steps in CCLs; eauto.
        destruct CCLs as (e0' & CCLs' & RSVs).
        inv RSVs.
        {
          (* not promise step *)
          clear - PROG STEP.
          inv PROG; inv STEP; ss. inv LOCAL.
        }
        eapply rtc_rtcn in A0. 
        destruct A0 as (n' & RSVs). 
        exploit reorder_program_step_reserve_steps; [eapply STEP | eapply RSVs | eauto..].
        intro; des; subst; ss.
        { 
          eapply program_step_consistent_construction in H1; eauto.
          des. do 2 eexists.
          split. eapply CCLs'.
          split.
          eapply rtc_compose; [eapply H0 | eapply H1].
          eauto.
          eapply local_wf_prsv_rsv_steps; eauto.
          eapply local_wf_prsv_cancel_steps; eauto.
          eapply memory_closed_prsv_rsv_steps; eauto.
          eapply local_wf_prsv_cancel_steps; eauto.
          eapply memory_closed_prsv_cancel_steps; eauto.
        }
        {
          eapply write_step_attached_consistent_construction in H1; eauto. des.
          clear - CCLs' H0 H1 H2.
          do 2 eexists.
          split. eauto.
          split.
          eapply rtc_compose; [eapply H0 | eapply H1].
          eauto.
          eapply local_wf_prsv_rsv_steps; eauto.
          eapply local_wf_prsv_cancel_steps; eauto.
          eapply memory_closed_prsv_rsv_steps; eauto.
          eapply local_wf_prsv_cancel_steps; eauto.
          eapply memory_closed_prsv_cancel_steps; eauto.
        }
        {
          eapply update_step_attached_consistent_construction in H1; eauto. des.
          clear - CCLs' H0 H1 H2.
          do 2 eexists.
          split. eauto.
          split.
          eapply rtc_compose; [eapply H0 | eapply H1].
          eauto.
          eapply local_wf_prsv_rsv_steps; eauto.
          eapply local_wf_prsv_cancel_steps; eauto.
          eapply memory_closed_prsv_rsv_steps; eauto.
          eapply local_wf_prsv_cancel_steps; eauto.
          eapply memory_closed_prsv_cancel_steps; eauto.
        }
        inv PROG; ss.
        inv LOCAL; ss.
        destruct ordw; ss.
        contradiction H; eauto.
        eapply no_scfence_nprm_step_prsv_local_wf; eauto.
        eapply no_scfence_nprm_step_intro1; eauto.
        eapply no_scfence_nprm_step_prsv_memory_closed; eauto.
        econs; eauto.
      }
    }
    {
      (* cancel or lower to none step *)
      inv PF.
      destruct kind; ss.
      {
        (* lower *)
        destruct msg1; ss. destruct msg; ss. destruct released0; ss.
        eapply IHn in A23; eauto. des.
        eapply rtc_rtcn in A23; destruct A23 as (n0 & CCLs).
        eapply reorder_not_rsv_ccl_scfence_step_cancel_steps in CCLs; eauto.
        destruct CCLs as (e0' & CCLs' & RSVs).
        Focus 2.
        econs. econs; eauto. 2: ss.
        eapply rtc_rtcn in A0. 
        destruct A0 as (n' & RSVs').
        inv RSVs. 
        exploit reorder_lower_step_reserve_steps; [eapply STEP | eapply RSVs' | eauto..].
        ii. des.
        inv H0; ss.
        eapply lower_PF_consistent_construction in LOCAL0; eauto.
        eapply local_wf_prsv_cancel_steps in CCLs'; eauto.
        eapply local_wf_prsv_rsv_steps in H; eauto.
        lets CCLs'': CCLs'.
        eapply memory_closed_prsv_cancel_steps in CCLs'; eauto.
        eapply memory_closed_prsv_rsv_steps in H; eauto.
        eapply local_wf_prsv_cancel_steps; eauto.
        inv STEP. inv LOCAL0.
        econs.
        ss.
        inv LOCAL.
        eapply local_wf_promise; eauto. destruct lc1; eauto.
        ss.
        eapply promise_step_closed_mem; eauto.
      }
      {
        (* cancel step *)
        eapply IHn in A23; eauto; ss. des.
        do 2 eexists.
        split; [eapply Relation_Operators.rt1n_trans; [|eapply A23] |
                split; [eapply A0 | eapply A1]].
        econs; eauto.
        econs; eauto.
        inv LOCAL.
        inv PROMISE; eauto.
        inv LOCAL.
        eapply local_wf_promise; eauto. destruct lc1; eauto.
        eapply promise_step_closed_mem; eauto.
      }
    }
Qed.

Lemma consistent_construct_from_fulfill:
  forall n lang lo (e e': Thread.t lang)
    (FULFILL_STEPS: rtcn (Thread.tau_step lo) n e e')
    (IS_FULFILL: Local.promises (Thread.local e') = Memory.bot)
    (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
    (CLOSED: Memory.closed (Thread.memory e)),
  exists e0 e1,
    rtc (Thread.cancel_step lo) e e0 /\ rtc (Thread.reserve_step lo) e0 e1 /\ 
    Thread.consistent e1 lo.
Proof.
  intros.
  exploit tau_steps_fulfill_implies_nprm_steps_fulfill; eauto. ii. des.
  eapply rtc_rtcn in H. des.
  exploit consistent_construct_from_fulfill'; eauto.
Qed.
