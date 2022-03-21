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
Require Import Cover.
Require Import ps_to_np_thread.
Require Import PromiseInjection.
Require Import WFConfig.
Require Import PromiseConsistent.
Require Import MemoryReorder.
Require Import ReorderPromise.
Require Import ReorderReserve.
Require Import ReorderCancel.
Require Import PromiseInjectionWeak.
Require Import ConsistentLemmas.

Lemma promise_fulfill_step_msgInj_stable
      lc1 sc1 mem1 loc from1 to1 val R1 R1' ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 R2 R2' lc2' sc2' mem2' kind2 inj inj'
      (MEM_INJ: MsgInj inj mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val R1 R1' ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val R2 R2' ord lc2' sc2' mem2' kind2 lo)
      (KIND_MATCH: promise_fulfill_kind_match kind1 kind2)
      (OPT_VIEW_INJ: opt_ViewInj inj' R1' R2')
      (INJ_INCR: incr_inj inj inj')
      (MON: monotonic_inj inj')
      (INJ: inj' loc to1 = Some to2)
      (COMPLETE_INJ: forall loc to to',
          inj' loc to = Some to' -> exists from val R, Memory.get loc to mem1' = Some (from, Message.concrete val R))
      (CLOSED_MEM: Memory.closed mem1):
  MsgInj inj' mem1' mem2'.
Proof.
  inv WRITE1. inv WRITE. inv PROMISE; ss.
  - destruct msg3; ss. destruct kind2; ss. destruct msg3; ss.
    des; subst. inv RESERVE. inv RESERVEORIGINAL.
    inv WRITE2. inv WRITE. inv PROMISE.
    des; subst. inv RESERVE. inv RESERVEORIGINAL.
    eapply split_msgInj_stable_concrete; eauto.
  - des; subst.
    destruct kind2; ss.
    destruct msg1; ss; subst; ss.
    inv WRITE2. inv WRITE. inv PROMISE.
    des; subst. inv RESERVE.
    eapply lower_msgInj_stable_concrete; eauto.
Qed.

Lemma Memory_remove_concrete_reserves_same
      prom0 loc from to val R prom1 loc0 from0 to0
      (REMOVE: Memory.remove prom0 loc from to (Message.concrete val R) prom1)
      (GET: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve)):
  Memory.get loc0 to0 prom1 = Some (from0, Message.reserve).
Proof.
  erewrite Memory.remove_o; eauto.
  des_if; ss; des; subst; ss.
  exploit Memory.remove_get0; [eapply REMOVE | eauto..].
  ii; des.
  rewrite GET in GET0. ss.
Qed.

Lemma Memory_remove_concrete_reserves_prsv
      prom0 loc from to val R prom1 loc0 from0 to0
      (REMOVE: Memory.remove prom0 loc from to (Message.concrete val R) prom1)
      (GET: Memory.get loc0 to0 prom1 = Some (from0, Message.reserve)):
  Memory.get loc0 to0 prom0 = Some (from0, Message.reserve).
Proof.
  erewrite Memory.remove_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
Qed.

Lemma Memory_split_concrete_reserves_same
      prom0 loc from to ts val R val' R' prom1 loc0 from0 to0 
      (SPLIT: Memory.split prom0 loc from to ts
                           (Message.concrete val R) (Message.concrete val' R') prom1)
      (GET: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve)):
  Memory.get loc0 to0 prom1 = Some (from0, Message.reserve).
Proof.
  exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
  erewrite Memory.split_o; eauto.
  des_if; ss; des; subst; ss; eauto.
  rewrite GET in GET0; ss.
  des_if; ss; des; subst; ss; eauto.
  des_if; ss; des; subst; ss; eauto.
  rewrite GET in GET1. inv GET1.
Qed.

Lemma Memory_split_concrete_reserves_prsv
      prom0 loc from to ts val R val' R' prom1 loc0 from0 to0 
      (SPLIT: Memory.split prom0 loc from to ts
                           (Message.concrete val R) (Message.concrete val' R') prom1)
      (GET: Memory.get loc0 to0 prom1 = Some (from0, Message.reserve)):
  Memory.get loc0 to0 prom0 = Some (from0, Message.reserve).
Proof.
  exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
  erewrite Memory.split_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
Qed.

Lemma Promise_fulfill_sc_not_care:
  forall n lang lo st lc sc mem e' sc0
    (STEPS: rtcn (@Thread.nprm_step lang lo) n (Thread.mk lang st lc sc mem) e')
    (BOT: Local.promises (Thread.local e') = Memory.bot),
  exists e'', rtc (@Thread.tau_step lang lo) (Thread.mk lang st lc sc0 mem) e'' /\
         Local.promises (Thread.local e'') = Memory.bot.
Proof.
  induction n; ii.
  - inv STEPS. eauto.
  - inv STEPS.
    destruct a2.
    inv A12.
    + inv PROG.
      eapply IHn with (sc0 := sc0) in A23; eauto. des.
      inv LOCAL; ss.
      {
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_silent; eauto.
        eauto. eauto. eapply A23. eauto.
      }
      {
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_read; eauto.
        eauto. eauto. eapply A23. eauto.
      }
      {
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_write; eauto.
        inv LOCAL0. econs; eauto. inv WRITABLE. econs; eauto.
        eauto. eauto. eapply A23. eauto.
      }
      {
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_update; eauto.
        inv LOCAL2. econs; eauto. inv WRITABLE. econs; eauto.
        eauto. eauto. eapply A23. eauto.
      }
      {
        destruct ordw; ss.
        
        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_fence; eauto.
        econs; eauto. instantiate (1 := Ordering.plain). ii; ss. ii; ss.
        eauto. eauto.
        inv LOCAL0. eapply A23; eauto. eauto.

        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_fence; eauto.
        econs; eauto. instantiate (1 := Ordering.relaxed). ii; ss. ii; ss.
        eauto. eauto.
        inv LOCAL0. eapply A23; eauto. eauto.

        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_fence; eauto.
        econs; eauto. instantiate (1 := Ordering.strong_relaxed).
        inv LOCAL0; eauto. ii; ss.
        eauto. eauto.
        inv LOCAL0. eapply A23; eauto. eauto.

        eexists.
        split.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program. econs.
        Focus 2. eapply Local.step_fence; eauto.
        econs; eauto. instantiate (1 := Ordering.acqrel).
        inv LOCAL0; eauto. ii; ss.
        eauto. eauto.
        inv LOCAL0. eapply A23; eauto. eauto.

        inv LOCAL0; ss.
        exploit PROMISES; eauto.
      }
    + eapply IHn in A23; eauto. des.
      eexists.
      split.
      eapply Relation_Operators.rt1n_trans.
      econs. econs.
      instantiate (3 := true). instantiate (2 := e).
      inv PF.
      eapply Thread.step_promise. econs; eauto.
      inv PF. ss.
      eapply A23. eauto.
Qed.

Lemma wf_monotonic_inj
      inj mem mem' loc to1 to1' to2 to2'
      (MSG_INJ: MsgInj inj mem mem')
      (TIME_LT: Time.lt to1 to2)
      (INJ_GET1: inj loc to1 = Some to1')
      (INJ_GET2: inj loc to2 = Some to2'):
  exists val2' R2' from2', Memory.get loc to2' mem' = Some (from2', Message.concrete val2' R2') /\
  Time.le to1' from2'.
Proof.
  inv MSG_INJ.
  exploit COMPLETE; [eapply INJ_GET1 | eauto..]. ii; des.
  exploit COMPLETE; [eapply INJ_GET2 | eauto..]. ii; des.
  exploit SOUND; [eapply H | eauto..]. ii; des.
  exploit SOUND; [eapply H0 | eauto..]. ii; des.
  rewrite INJ_GET1 in H1. inv H1.
  rewrite INJ_GET2 in H4. inv H4.
  do 3 eexists. split; eauto.
  exploit Memory.get_disjoint; [eapply H3 | eapply H6 | eauto..]. ii; des; subst; ss.
  unfold monotonic_inj in MONOTONIC.
  exploit MONOTONIC; [eapply TIME_LT | eapply INJ_GET1 | eapply INJ_GET2 | eauto..].
  ii. clear - H1. auto_solve_time_rel.
  unfold Interval.disjoint in H1.
  destruct (Time.le_lt_dec t' f'0); eauto.
  assert (Time.lt t' t'0).
  {
    eapply MONOTONIC; [eapply TIME_LT | eapply INJ_GET1 | eapply INJ_GET2 | eauto..].
  } 
  exploit Memory.get_ts; [eapply H3 | eauto..].
  ii; des; subst; ss. auto_solve_time_rel.
  specialize (H1 t').
  false.
  eapply H1; eauto.
  econs; ss; eauto. eapply Time.le_lteq; eauto.
  econs; ss; eauto. eapply Time.le_lteq; eauto.
Qed.
  
Lemma next_concrete_ext
      mem loc to
      (FINITE_MEM: Memory.finite mem):
  (exists nxt_ts f0 val0 R0, Time.lt to nxt_ts /\
                        Memory.get loc nxt_ts mem = Some (f0, Message.concrete val0 R0) /\
                        (forall t' f' val' R',
                            Memory.get loc t' mem = Some (f', Message.concrete val' R') -> t' <> nxt_ts ->
                            (Time.le t' to \/ Time.lt nxt_ts t'))) \/
  (forall t' f' val' R', Memory.get loc t' mem = Some (f', Message.concrete val' R') -> Time.le t' to).
Proof.
  unfold Memory.finite in *. des.
  generalize dependent mem.
  induction dom; ii; ss.
  - right. ii. eapply FINITE_MEM in H; eauto. ss.
  - destruct a as (loc0 & to0).
    destruct (Memory.get loc0 to0 mem) eqn:GET.
    + destruct p as (from0 & msg0).
      destruct msg0.
      {
        exploit Memory.remove_exists; eauto. ii; des.
        assert (IN_DOM_PROGRESS: forall loc from to msg,
                   Memory.get loc to mem2 = Some (from, msg) -> In (loc, to) dom).
        {
          ii.
          erewrite Memory.remove_o in H0; eauto.
          des_ifH H0; ss.
          eapply FINITE_MEM in H0; eauto. des; eauto.
          inv H0; ss. inv H0; ss.
        }
        eapply IHdom in IN_DOM_PROGRESS; eauto.
        des.
        {
          destruct (Loc.eq_dec loc loc0). subst.
          {
            destruct (Time.le_lt_dec to0 to).

            left.
            exists nxt_ts f0 val0 R0.
            split; eauto.
            split.
            erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
            des_ifH IN_DOM_PROGRESS0; ss; eauto.
            ii.
            destruct (Time.eq_dec to0 t'); subst; eauto.
            eapply IN_DOM_PROGRESS1; eauto.
            instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
            erewrite Memory.remove_o; eauto. des_if; ss; eauto. des; subst; ss.
            
            destruct (Time.le_lt_dec to0 nxt_ts).
            left.
            exists to0 from0 val released.
            split; eauto.
            split; eauto.
            ii.
            destruct (Time.eq_dec to0 t'); subst; eauto; ss.
            assert (GET': Memory.get loc0 t' mem2 = Some (f', Message.concrete val' R')).
            {
              erewrite Memory.remove_o; eauto.
              des_if; ss; des; subst; ss.
            }
            destruct (Time.eq_dec t' nxt_ts); subst.
            clear - l l0 n. eapply Time.le_lteq in l0; ss.
            des; subst; eauto. ss.
            eapply IN_DOM_PROGRESS1 in GET'; eauto.
            des; eauto.
            clear - l0 GET'. right. auto_solve_time_rel.

            left.
            exists nxt_ts f0 val0 R0.
            split; eauto. split; eauto.
            erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
            des_ifH IN_DOM_PROGRESS0; ss.
            ii.
            destruct (Time.eq_dec to0 t'); subst; eauto; ss.
            eapply IN_DOM_PROGRESS1; eauto.
            instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
            erewrite Memory.remove_o; eauto. des_if; ss; eauto. des; subst; ss.
          }
          {
            left.
            exists nxt_ts f0 val0 R0.
            split; eauto.
            split. 
            erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
            des_ifH IN_DOM_PROGRESS0; ss; eauto.
            ii.
            eapply IN_DOM_PROGRESS1; eauto.
            instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
            erewrite Memory.remove_o; eauto.
            des_if; ss; des; subst; ss.
          }
        }
        {
          destruct (Loc.eq_dec loc loc0). subst.
          {
            destruct (Time.le_lt_dec to0 to).
            right.
            ii.
            destruct (Time.eq_dec t' to0); subst; eauto.
            eapply IN_DOM_PROGRESS; eauto.
            instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
            erewrite Memory.remove_o; eauto.
            des_if; ss; subst; des; ss.
            left.
            exists to0 from0 val released.
            split; eauto.
            split; eauto.
            ii.
            left.
            eapply IN_DOM_PROGRESS; eauto.
            instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
            erewrite Memory.remove_o; eauto.
            des_if; ss; des; subst; ss.
          }
          {
            right.
            ii.
            eapply IN_DOM_PROGRESS; eauto.
            instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
            erewrite Memory.remove_o; eauto.
            des_if; ss; des; subst; ss.
          }
        }
      }
      {
        exploit Memory.remove_exists; eauto. ii; des.
        assert (IN_DOM_PROGRESS: forall loc from to msg,
                   Memory.get loc to mem2 = Some (from, msg) -> In (loc, to) dom).
        {
          ii.
          erewrite Memory.remove_o in H0; eauto.
          des_ifH H0; ss.
          eapply FINITE_MEM in H0; eauto. des; eauto.
          inv H0; ss. inv H0; ss.
        }
        eapply IHdom in IN_DOM_PROGRESS; eauto.
        des.
        {
          left.
          exists nxt_ts f0 val0 R0.
          split; eauto.
          split. erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
          des_ifH IN_DOM_PROGRESS0; ss.
          ii.
          eapply IN_DOM_PROGRESS1; eauto.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          rewrite GET in H0. ss.
        }
        {
          right.
          ii.
          eapply IN_DOM_PROGRESS.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          rewrite GET in H0. ss.
        }
      }
    + assert (IN_DOM_PROGRESS: forall loc from to msg,
                   Memory.get loc to mem = Some (from, msg) -> In (loc, to) dom).
      {
        ii. lets GET': H.
        eapply FINITE_MEM in H; eauto. des; eauto.
        inv H; ss.
        rewrite GET in GET'; ss.
      }
      eapply IHdom in IN_DOM_PROGRESS; eauto.
Qed.

Lemma Memory_write_o
      promises mem promises' mem' loc from to val released kind loc0 to0 from0 msg0
      (WRITE: Memory.write promises mem loc from to val released promises' mem' kind)
      (GET: Memory.get loc0 to0 mem' = Some (from0, msg0)):
  (exists from0', Memory.get loc0 to0 mem = Some (from0', msg0)) \/
                  (loc0 = loc /\ to0 = to).
Proof.
  inv WRITE. inv PROMISE; ss.
  - erewrite Memory.add_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
  - des; subst. inv RESERVE.
    erewrite Memory.split_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    inv GET.
    exploit Memory.split_get0; eauto. ii; des; eauto.
  - des; subst.
    erewrite Memory.lower_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
Qed.

Lemma write_step_concrete_msg_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo ts f loc0 val0 R0
      (WRITE1: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (RESERVE: Memory.get loc0 ts mem = Some (f, Message.concrete val0 R0)):
  exists f' R0', Memory.get loc0 ts mem' = Some (f', Message.concrete val0 R0').
Proof.
  inv WRITE1. inv WRITE. inv PROMISE; ss.
  - do 2 eexists. eapply Memory.add_get1; eauto.
  - des; subst. inv RESERVE0.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; eauto. ii; des.
    rewrite RESERVE in GET; ss.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.split_get0; eauto. ii; des.
    rewrite RESERVE in GET0. inv GET0. eauto.
  - des; subst.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
    rewrite RESERVE in GET. inv GET.
    inv MSG_LE. eauto.
Qed.

Lemma write_step_promise_concrete_le_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0 max_ts to' from' val' R'
      (WRITE1: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (PRM_LE: forall ts from val R,
          Memory.get loc0 ts (Local.promises lc) = Some (from, Message.concrete val R) -> Time.le ts max_ts)
      (RESERVE: Memory.get loc0 to' (Local.promises lc') = Some (from', Message.concrete val' R')):
  Time.le to' max_ts.
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

Lemma injection_write_step_id_weak
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
      (PRM_EQ: promise_inj_weak inj (Local.promises lc) (Local.promises lc'))
      (PRM_ITV_SAME: forall from to val R,
          Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) ->
          exists R', Memory.get loc to (Local.promises lc') = Some (from, Message.concrete val R')):
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
                                       inj loc t = Some t'>> /\ 
    <<PRM_ITV_SAME': forall from to val R,
                             Memory.get loc to (Local.promises lc1) = Some (from, Message.concrete val R) ->
                             exists R', Memory.get loc to (Local.promises lc1') = Some (from, Message.concrete val R')>>.
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
    eapply mem_nonsynch_loc_msgInj_weak in ORDER; eauto.
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

    split; eauto.
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

    split; ii; ss.
    eapply PRM_ITV_SAME with (R := R).
    clear - WRITE0 H.
    inv WRITE0. inv PROMISE.
    exploit MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
    ii; subst. eauto.
    
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
      clear - NO_GT_MAX WRITE0 INJ_LOC0 PRM_EQ LT_TS3 PRM_ITV_SAME.
      inv WRITE0. inv PROMISE. des; subst. inv RESERVE.
      exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des; eauto.
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
      eapply mem_nonsynch_loc_msgInj_weak; eauto.
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

    split; eauto.
    ii. inv H. do 3 eexists. split; eauto.
    clear - INJ_LOC0 LT_TS3 WRITE0 MEM_INJ.
    inv WRITE0. inv PROMISE. des; subst. inv RESERVE. inv RESERVEORIGINAL.
    exploit Memory.split_get0; [eapply MEM | eauto..]; ii; des.
    inv MEM_INJ. exploit SOUND; eauto. ii; des.
    exploit INJ_LOC0; eauto. ii; subst; eauto.

    ss. ii.
    clear - WRITE0 WRITE1 H PRM_ITV_SAME.
    inv WRITE0. inv PROMISE. des; subst; ss. inv RESERVE.
    inv WRITE1. inv PROMISE. des; subst; ss. inv RESERVE. inv RESERVEORIGINAL.
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; subst; ss.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss.
    des_ifH H; ss; des; subst; ss.
    inv H.
    exploit Memory.split_get0; [eapply PROMISES0 | eauto..]. ii; des.
    exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
    eapply PRM_ITV_SAME in GET4. des.
    rewrite GET0 in GET4. inv GET4. eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    des_if; ss; des; subst; ss; eauto.
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
      clear - ID_INJ GET_PROMISE MEM_INJ LOCAL_WF LOCAL_WF' PRM_ITV_SAME.
      inv MEM_INJ.
      exploit PRM_ITV_SAME; eauto. ii; des.
      exists R'. split; eauto.
      inv LOCAL_WF; ss. exploit PROMISES; eauto; ii.
      inv LOCAL_WF'; ss. exploit PROMISES0; eauto; ii.
      exploit SOUND; eauto. ii; des.
      rewrite ID_INJ in H2. inv H2.
      rewrite H1 in H4. inv H4. eauto.
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
      eapply mem_nonsynch_loc_msgInj_weak; eauto.
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
    split.
    { 
      clear - MEM_INJ WRITE0. ii. inv MEM_INJ; eauto.
      eapply COMPLETE in H; eauto; des.
      inv WRITE0. inv PROMISE. des. inv RESERVE.
      exploit Memory.lower_get1; eauto. ii; des; eauto. inv MSG_LE; eauto.
    }
    split; try solve [ii; ss].
    {
      ss. ii.
      clear - WRITE0 WRITE1 H PRM_ITV_SAME.
      inv WRITE0. inv PROMISE. des; subst. inv RESERVE.
      inv WRITE1. inv PROMISE. des; subst. inv RESERVE.
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.lower_get0; [eapply PROMISES | eauto..]. 
    }
  }
  {
    (* cancel *)
    clear - WRITE. inv WRITE; ss. inv LC2.
    inv WRITE0. inv PROMISE; ss.
  }
Qed.

Lemma injection_write_step_id_weak_GT
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
      (PRM_EQ: promise_inj_weak inj (Local.promises lc) (Local.promises lc'))
      (*(PRM_ITV_SAME: forall from to val R,
          Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) ->
          exists R', Memory.get loc to (Local.promises lc') = Some (from, Message.concrete val R'))*)
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
    (*<<PRM_ITV_SAME': forall from to val R,
                             Memory.get loc to (Local.promises lc1) = Some (from, Message.concrete val R) ->
                             exists R', Memory.get loc to (Local.promises lc1') = Some (from, Message.concrete val R')>>.*)
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
      eapply mem_nonsynch_loc_msgInj_weak in ORDER; eauto.
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
            
Lemma injection_write_step_id_weak2
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
      (PRM_EQ: promise_inj_weak inj (Local.promises lc) (Local.promises lc'))
      (PRM_ITV_SAME: forall from to val R,
          Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) ->
          exists R', Memory.get loc to (Local.promises lc') = Some (from, Message.concrete val R')):
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
                                       inj loc t = Some t'>> /\
    <<PRM_ITV_SAME': forall from to val R,
                             Memory.get loc to (Local.promises lc1) = Some (from, Message.concrete val R) ->
                             exists R', Memory.get loc to (Local.promises lc1') = Some (from, Message.concrete val R')>>.
Proof.
  destruct (Time.le_lt_dec to (Memory.max_ts loc mem)) as [LE_MAX | GT_MAX].
  {
    lets TEMP: WRITE. 
    destruct (classic (exists f' ts' msg', Memory.get loc ts' mem = Some (f', msg'))).
    {
      eapply injection_write_step_id_weak with (lc' := lc') (mem' := mem') in TEMP; eauto.
      ii. exploit Memory.max_ts_spec; eauto. ii; des; eauto.
      des. exploit Memory.max_ts_spec; eauto. ii; des; eauto.
    }
    {
      clear - CLOSED_MEM H.
      inv CLOSED_MEM. unfold Memory.inhabited in INHABITED.
      specialize (INHABITED loc).
      contradiction H. eauto.
    }
  }
  {
    lets TEMP: WRITE.
    eapply injection_write_step_id_weak_GT with (from' := from) (to' := to)
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
    split. ii; ss.
    {
      clear - WRITE PRM_ITV_SAME INJ_WRITE.
      inv WRITE. inv INJ_WRITE.
      exploit MemoryFacts.MemoryFacts.write_add_promises; [eapply WRITE0 | eauto..]. introv PROM_EQ1.
      exploit MemoryFacts.MemoryFacts.write_add_promises; [eapply WRITE | eauto..]. introv PROM_EQ2.
      ss. subst. eauto.
    }
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

Lemma injection_write_step_na_weak
      inj mem mem' lc sc mem1 lc1 sc1 loc from to val releasedr releasedr' releasedw lo ord 
      max_ts lc' sc'
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw
                               ord lc1 sc1 mem1 Memory.op_kind_add lo)
      (LE_MAX: Time.le to max_ts)
      (*(NO_GT_MAX: forall ts from val R,
          Memory.get loc ts mem = Some (from, Message.concrete val R) -> Time.le ts max_ts)*)
      (MAX_RESERVE: exists from val R, Memory.get loc max_ts mem = Some (from, Message.concrete val R))
      (GT_PROMISE: forall ts f' val' R',
          Memory.get loc ts mem = Some (f', Message.concrete val' R') -> Time.lt to ts ->
          Memory.get loc ts (Local.promises lc) = Some (f', Message.concrete val' R'))
      (MEM_INJ: MsgInj inj mem mem')
      (LOCAL_WF: Local.wf lc mem)
      (LOCAL_WF': Local.wf lc' mem')
      (CLOSED_MEM: Memory.closed mem)
      (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
      (CLOSED_VIEW: Memory.closed_opt_view releasedr mem)
      (VIEW_INJ: opt_ViewInj inj releasedr releasedr')
      (PRM_EQ: promise_inj_weak inj (Local.promises lc) (Local.promises lc')):
  exists lc1' releasedw' mem1' inj' from' to' ts' msg',
    <<INJ_WRITE: Local.write_step lc' sc' mem' loc from' to' val releasedr' releasedw'
                                  ord lc1' sc' mem1' (Memory.op_kind_split ts' msg') lo>> /\
    <<INJ_MSG: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)>> /\
    <<INJ_INCR: incr_inj inj inj'>> /\ <<MON_INJ: monotonic_inj inj' >> /\
    <<MSG_INJ: MsgInj inj' mem1 mem1'>> /\
    <<INJ_VIEW: opt_ViewInj inj' releasedw releasedw'>> /\
    <<PROM_INJ': promise_inj_weak inj' (Local.promises lc1) (Local.promises lc1')>>.
Proof.
  destruct lc, lc1. 
  destruct MAX_RESERVE as (from''' & val''' & R''' & MAX_RESERVE).
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
  assert(LT_MAX: Time.lt to max_ts).
  {
    eapply Local_write_add_lt_max_ts_reserve; eauto.
  }
  inv WRITE. inv LC2. ss.
  exploit next_concrete_ext.
  {
    inv LOCAL_WF; ss. eauto.
  }
  instantiate (1 := to). instantiate (1 := loc).
  introv NXT_CONCRETE.
  des.

  Focus 2.
  eapply GT_PROMISE in MAX_RESERVE; eauto.
  eapply NXT_CONCRETE in MAX_RESERVE.
  clear - MAX_RESERVE LT_MAX. auto_solve_time_rel.

  assert (PROM_S: exists ts' f0' R0',
             Memory.get loc ts' (Local.promises lc') = Some (f0', Message.concrete val0 R0') /\
             inj loc nxt_ts = Some ts' /\ Time.lt f0' ts' /\ opt_ViewInj inj R0 R0').
  {
    clear - NXT_CONCRETE0 MEM_INJ PRM_EQ LOCAL_WF LOCAL_WF'.
    inv MEM_INJ. inv PRM_EQ.
    exploit SOUND0; [eapply NXT_CONCRETE0 | eauto..]. ii; des.
    do 3 eexists.
    split. eauto. split; eauto. split; eauto.
    inv LOCAL_WF; ss.
    inv LOCAL_WF'; ss.
    eapply PROMISES in NXT_CONCRETE0.
    eapply PROMISES0 in H0.
    exploit SOUND; [eapply NXT_CONCRETE0 | eauto..]. ii; des.
    rewrite H in H2. inv H2.
    rewrite H0 in H4. inv H4. eauto.
  }
  destruct PROM_S as (to' & from' & R0' & GET_PROMISE & INJ_MSG_SPLIT & SPLIT_MSG_ITV & OPT_VIEWINJ).
  exploit Time.middle_spec; [eapply SPLIT_MSG_ITV | eauto..].
  introv SPLIT_MSG. destruct SPLIT_MSG as (SPLIT_MSG1 & SPLIT_MSG2).
  inv WRITE0. inv PROMISE.
  exploit wf_inj_incr.
  {
    inv MEM_INJ; eauto.
  }
  {
    instantiate (2 := loc). instantiate (1 := to).
    clear - MEM_INJ MEM.
    destruct (inj loc to) eqn: INJ_MSG; eauto.
    inv MEM_INJ.
    eapply COMPLETE in INJ_MSG; eauto. des.
    exploit Memory.add_get0; eauto. ii; des.
    rewrite INJ_MSG in GET. ss.
  }
  {
    instantiate (1 := (Time.middle from' to')).
    introv INJ_MSG LT.
    assert (Time.lt ts nxt_ts). clear - NXT_CONCRETE LT. auto_solve_time_rel.
    exploit wf_monotonic_inj; [eapply MEM_INJ | eapply H | eapply INJ_MSG | eapply INJ_MSG_SPLIT | eauto..].
    ii; des.
    inv LOCAL_WF'. eapply PROMISES0 in GET_PROMISE.
    rewrite GET_PROMISE in H0. inv H0.
    clear - SPLIT_MSG1 H1. auto_solve_time_rel.
  }
  {
    introv INJ_MSG LT.
    destruct (Time.le_lt_dec ts nxt_ts).
    {
      eapply Time.le_lteq in l; des; subst; eauto.
      {
        inv MEM_INJ.
        exploit COMPLETE; [eapply INJ_MSG | eauto..]. ii; des.
        exploit GT_PROMISE; [eapply H | eauto..]. ii.
        eapply NXT_CONCRETE1 in H0. des.
        clear - LT H0. auto_solve_time_rel.
        clear - l H0. cut (Time.lt ts ts). ii. auto_solve_time_rel.
        auto_solve_time_rel.
        ii; subst. auto_solve_time_rel.
      }
      {
        rewrite INJ_MSG_SPLIT in INJ_MSG. inv INJ_MSG. eauto.
      }
    }
    {
      inv MEM_INJ.
      exploit MONOTONIC; [eapply l | eapply INJ_MSG_SPLIT | eapply INJ_MSG | eauto..].
      ii.
      clear - SPLIT_MSG2 H.
      auto_solve_time_rel.
    }
  } 
  ii; des.
  assert (MSG_WF': Message.wf
                     (Message.concrete val (TView.write_released (Local.tview lc')
                                                                 sc' loc (Time.middle from' to') releasedr' ord))).
  {
    inv MSGWF. econs.   
    eapply View_opt_wf_inj with
        (inj := fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then
                                Some (Time.middle from' to') else inj loc1 to1); eauto.
    eapply incr_inj_TViewInj; eauto. 
    eapply incr_inj_opt_ViewInj; eauto. 
    eapply incr_inj_closed_tviewInj; eauto.
    eapply incr_inj_closed_opt_ViewInj; eauto.
    des_if; eauto. ss; tryfalse. des; tryfalse.
  }
  exploit Memory.split_exists; [eapply GET_PROMISE | eapply SPLIT_MSG1 | eapply SPLIT_MSG2 | idtac..].
  {
    instantiate (1 := Message.concrete val (TView.write_released (Local.tview lc') sc' loc
                                                                 (Time.middle from' to') releasedr' ord)).
    eauto.
  }
  introv SPLIT_PROMISE. des.
  assert (GET_MEM: Memory.get loc to' mem' = Some (from', Message.concrete val0 R0')).
  {
    inv LOCAL_WF'. eauto.
  }
  exploit Memory.split_exists; [eapply GET_MEM | eapply SPLIT_MSG1 | eapply SPLIT_MSG2 | idtac..].
  {
    instantiate (1 := Message.concrete val (TView.write_released (Local.tview lc') sc' loc
                                                                 (Time.middle from' to') releasedr' ord)).
    eauto.
  }
  introv SPLIT_MEM. des.
  exploit Memory.split_get0; [eapply SPLIT_PROMISE | eauto..]. ii; des.
  exploit Memory.remove_exists; [eapply GET1 | eauto..].
  introv REMOVE_PROMISE. des.
  renames mem2 to promises2', mem3 to promises3'.
  assert(MEM_INJ': MsgInj inj' mem1 mem0).
  { 
    inv MEM_INJ. econs; eauto; ii.

    erewrite Memory.add_o in MSG; eauto.
    des_ifH MSG; ss; des; subst; ss. inv MSG.
    exists (Time.middle from' to') from'
      (TView.write_released (Local.tview lc') sc' loc (Time.middle from' to') releasedr' ord).
    split; eauto.
    des_if; ss; des; subst; ss.
    split; eauto.
    eapply opt_ViewInj_write_released_inj; eauto.
    eapply incr_inj_TViewInj; eauto. 
    eapply incr_inj_closed_tviewInj; eauto.
    des_if; ss; des; subst; ss.
    eapply incr_inj_opt_ViewInj; eauto.
    eapply incr_inj_closed_opt_ViewInj; eauto.
    exploit Memory.split_get0; [eapply SPLIT_MEM | eauto..]. ii; des; eauto.

    exploit SOUND; [eapply MSG | eauto..]. ii; des.
    exists t' f' R'.
    split; eauto. split; eauto.
    eapply incr_inj_opt_ViewInj; eauto.
    eapply closed_optview_msginj_implies_closed_viewInj with (mem := mem); eauto.
    clear - CLOSED_MEM MSG.
    inv CLOSED_MEM. eapply CLOSED in MSG. des. inv MSG_CLOSED. eauto.
    instantiate (1 := mem'). econs; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; subst; ss. des; subst; ss.
    des_if; ss; subst; ss. des; subst; ss.
 
    exploit SOUND; [eapply MSG | eauto..]. ii; des.
    destruct (Loc.eq_dec loc loc0); subst.
    destruct (Time.eq_dec t nxt_ts); subst.
    rewrite INJ_MSG_SPLIT in H. inv H.
    rewrite GET_MEM in H1. inv H1.
    { 
      exists t' (Time.middle f' t') R'.
      split; eauto. split; eauto.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply closed_optview_msginj_implies_closed_viewInj with (mem := mem); eauto.
      clear - CLOSED_MEM MSG.
      inv CLOSED_MEM. eapply CLOSED in MSG. des. inv MSG_CLOSED. eauto.
      instantiate (1 := mem'). econs; eauto.
      erewrite Memory.split_o; eauto.
      des_if; ss; subst; ss. des; ss; subst.
      exploit Time.middle_spec.
      instantiate (2 := f'). instantiate (1 := t'). eauto.
      ii. des; subst. rewrite <- a0 in H1. auto_solve_time_rel.
      des_if; ss; des; subst; ss.
    }
    {
      exists t' f' R'.
      split. des_if; ss; des; subst; ss.
      split.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply closed_optview_msginj_implies_closed_viewInj with (mem := mem); eauto.
      clear - CLOSED_MEM MSG.
      inv CLOSED_MEM. eapply CLOSED in MSG. des. inv MSG_CLOSED. eauto.
      instantiate (1 := mem'). econs; eauto.
      erewrite Memory.split_o; eauto.
      des_if; ss; subst; ss. des; ss; subst.
      clear - MON INCR_INJ o H n. 
      exploit monotonic_inj_implies_disj_mapping; [eapply MON | | | eapply o | eauto..].
      instantiate (2 := loc0).
      ss. des_if; ss; subst; des; ss.
      ss. des_if; ss; eauto. des; ss.
      ii; ss.
      des; ss.
      des_if; ss; des; subst; ss.
      clear - MONOTONIC H INJ_MSG_SPLIT n.
      exploit monotonic_inj_implies_disj_mapping;
        [eapply MONOTONIC | eapply H | eapply INJ_MSG_SPLIT | eapply n | eauto..].
      ii; ss.
    }
    {
      exists t' f' R'.
      split; eauto.
      split; eauto.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply closed_optview_msginj_implies_closed_viewInj with (mem := mem); eauto.
      clear - CLOSED_MEM MSG.
      inv CLOSED_MEM. eapply CLOSED in MSG. des. inv MSG_CLOSED. eauto.
      instantiate (1 := mem'). econs; eauto.
      erewrite Memory.split_o; eauto.
      des_if; ss; subst; ss. des; ss; subst. ss.
      des_if; ss; subst; ss. des; subst; ss.
    }

    des_ifH INJ; ss. des; subst. inv INJ.
    exploit Memory.add_get0; [eapply MEM | eauto..].  ii; des. eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  }
  do 8 eexists.
  split.
  { 
    econs. eauto. eauto.
    instantiate (1 := Time.middle from' to').
    inv WRITABLE. econs. 
    eapply writable_inj with
        (inj := fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then
                                Some (Time.middle from' to') else inj loc1 to1); eauto.
    eapply incr_inj_TViewInj; eauto. eapply incr_inj_closed_tviewInj; eauto.
    des_if; eauto; ss; des; ss.

    econs. econs. eapply SPLIT_PROMISE. eapply SPLIT_MEM.
    econs.
    eapply TLE_write_prs with (inj := inj'); eauto.
    rewrite NEW_INJ. des_if; eauto. ss; subst; ss. destruct o; ss.
    eapply incr_inj_opt_ViewInj; eauto.
    eapply incr_inj_TViewInj; eauto.
    eapply incr_inj_closed_tviewInj; eauto.
    eapply incr_inj_closed_opt_ViewInj; eauto.
    eauto.
    eauto.
    eapply REMOVE_PROMISE.
 
    introv ORDERING.
    clear MEM_INJ'. eapply mem_nonsynch_loc_msgInj_weak; eauto.
    inv LOCAL_WF; eauto.
    inv LOCAL_WF'; eauto.

    eauto. eauto.
  }
  ss.
  split. eauto.
  split. eauto.
  split. eauto.
  split. eauto.
  split.
  {
    eapply opt_ViewInj_write_released_inj; eauto.
    eapply incr_inj_TViewInj; eauto.
    eapply incr_inj_closed_tviewInj; eauto.
    rewrite NEW_INJ. des_if; eauto; des; subst; ss.
    eapply incr_inj_opt_ViewInj; eauto.
    eapply incr_inj_closed_opt_ViewInj; eauto.
  }
  {
    assert(promises = promises2).
    {
      eapply MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
    }
    subst promises2. 
    inv PRM_EQ.
    econs; eauto; ii.
    exploit SOUND; [eapply H | eauto..].
    ii; des.
    inv LOCAL_WF; ss.
    exploit PROMISES0; [eapply H | eauto..]. introv GET_MEM0.
    inv MEM_INJ. exploit SOUND0; [eapply GET_MEM0 | eauto..]. ii; des.
    rewrite H0 in H3. inv H3.
    inv LOCAL_WF'; ss.
    exploit PROMISES1; [eapply H1 | eauto..]. introv GET_MEM0'.
    rewrite GET_MEM0' in H5. inv H5.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.add_get0; [eapply MEM | eauto..]. ii; des.
    eapply COMPLETE0 in H0; eauto. des. rewrite H0 in GET3. ss.
    do 3 eexists. split; eauto.
    split.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    eauto.

    destruct (Loc.eq_dec loc loc0); subst.
    destruct (Time.eq_dec to0 nxt_ts); subst.
    rewrite INJ_MSG_SPLIT in H0; ss. inv H0.
    rewrite GET0 in H1. inv H1.
    exists t' R' (Time.middle f' t'). split; eauto. split; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Time.middle_spec; [eapply H2 | eauto..]. ii; des.
    rewrite <- a0 in H1. clear - H1. auto_solve_time_rel.
    exists t' R' f'.
    split; eauto. split; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    rewrite GET in H1. ss.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    clear - MONOTONIC INJ_MSG_SPLIT H0 n.
    exploit monotonic_inj_implies_disj_mapping;
      [eapply MONOTONIC | eapply H0 | eapply INJ_MSG_SPLIT | eapply n | eauto..]. ii; ss.
    exists t' R' f'.
    split; eauto. split; eauto.
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

    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    des_ifH H; ss; des; subst; ss; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto. 
    des_ifH H; ss; des; subst; ss; eauto. 
    inv H.
    exists nxt_ts R0 f0.
    split; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    exploit COMPLETE; [eapply H | eauto..]. ii; des.
    exists to0 released from0.
    split; eauto.
    eapply Memory_remove_concrete_reserves_same; eauto.
    eapply Memory_split_concrete_reserves_same; eauto. 
    eapply Memory_remove_concrete_reserves_prsv with (prom0 := promises2') in H; eauto.
    eapply Memory_split_concrete_reserves_prsv with (prom0 := (Local.promises lc')) in H; eauto.
  }
Qed.

Lemma injection_write_step_weak_not_add
      inj mem mem' lc sc mem1 lc1 sc1 loc from to val releasedr releasedr' releasedw kind lo ord lc' sc' max_ts
      (WRITE: Local.write_step lc sc mem loc from to val releasedr releasedw ord lc1 sc1 mem1 kind lo)
      (NOT_ADD: kind <> Memory.op_kind_add)
      (MEM_INJ: MsgInj inj mem mem')
      (LOCAL_WF: Local.wf lc mem)
      (LOCAL_WF': Local.wf lc' mem')
      (CLOSED_MEM: Memory.closed mem)
      (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
      (CLOSED_VIEW: Memory.closed_opt_view releasedr mem)
      (VIEW_INJ: opt_ViewInj inj releasedr releasedr')
      (PRM_EQ: promise_inj_weak inj (Local.promises lc) (Local.promises lc'))
      (PROM_LESS: forall from to val R,
          Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) -> Time.le to max_ts):
  exists lc1' releasedw' mem1' inj' kind' from' to',
    <<INJ_WRITE: Local.write_step lc' sc' mem' loc from' to' val releasedr' releasedw' ord lc1' sc' mem1' kind' lo>> /\
    <<KIND: promise_fulfill_kind_match kind kind'>> /\
    <<LE_WRITE: Time.le to max_ts>> /\
    <<LE_PROMISE: exists ts ts' f val R, Memory.get loc ts (Local.promises lc) = Some (f, Message.concrete val R) /\
                                    inj loc ts = Some ts' /\ Time.le to' ts'>> /\                    
    <<INJ_MSG: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)>> /\
    <<INJ_INCR: incr_inj inj inj'>> /\ <<MON_INJ: monotonic_inj inj' >> /\
    <<INJ_VIEW: opt_ViewInj inj' releasedw releasedw'>> /\ 
    <<INJ_COMPLETE: forall loc to to', inj' loc to = Some to' ->
                                  exists val f R, Memory.get loc to mem1 = Some (f, Message.concrete val R)>> /\
    <<SPLIT_INJ: forall t val R, kind = Memory.op_kind_split t (Message.concrete val R) ->
                         exists t' val' R', kind' = Memory.op_kind_split t' (Message.concrete val' R') /\
                                       inj loc t = Some t'>>.
Proof.
  assert(CLOSED_RELEASEDR: closed_opt_viewinj inj releasedr).
  {
    eapply closed_optview_msginj_implies_closed_viewInj; eauto. 
  }
  assert(CLOSED_TVIEWINJ: closed_tviewInj inj (Local.tview lc)).
  {
    clear - LOCAL_WF MEM_INJ.
    eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
    inv LOCAL_WF; eauto.
  }
  inv WRITE. inv WRITE0; ss. inv PROMISE; ss.
  - (* split *)
    des; subst. inv RESERVE. inv TS.
    exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
    assert (PROM_S: exists ts3' f0' R0',
             Memory.get loc ts3' (Local.promises lc') = Some (f0', Message.concrete val' R0') /\
             inj loc ts3 = Some ts3' /\ Time.lt f0' ts3' /\ opt_ViewInj inj released' R0').
    {
      clear - MEM_INJ PRM_EQ GET0 LOCAL_WF LOCAL_WF'.
      inv MEM_INJ. inv PRM_EQ.
      exploit SOUND0; [eapply GET0 | eauto..]. ii; des.
      inv LOCAL_WF. inv LOCAL_WF'.
      exploit PROMISES; [eapply GET0 | eauto..]. ii.
      exploit PROMISES0; [eapply H0 | eauto..]. ii.
      exploit SOUND; [eapply H2 | eauto..]. ii; des.
      rewrite H in H4. inv H4.
      do 3 eexists.
      split; eauto. split; eauto. split; eauto.
      rewrite H3 in H6. inv H6. eauto.
    }
    destruct PROM_S as (ts3' & from' & released0' & GET_PROMISE & INJ_MSG_SPLIT & SPLIT_MSG_ITV & OPT_VIEWINJ).
    exploit Time.middle_spec; [eapply SPLIT_MSG_ITV | eauto..].
    introv SPLIT_MSG. destruct SPLIT_MSG as (SPLIT_MSG1 & SPLIT_MSG2).
    assert (GET_MEM_S: Memory.get loc ts3' mem' = Some (from', Message.concrete val' released0')).
    {
      inv LOCAL_WF'. eauto.
    }
    exploit MemoryProps.split_succeed_wf; eauto. ii; des.
    exploit wf_inj_incr.
    {
      inv MEM_INJ; eauto.
    }
    {
      instantiate (2 := loc). instantiate (1 := to).
      clear - MEM_INJ MEM.
      destruct (inj loc to) eqn: INJ_MSG; eauto.
      inv MEM_INJ.
      eapply COMPLETE in INJ_MSG; eauto. des.
      exploit Memory.split_get0; eauto. ii; des.
      rewrite INJ_MSG in GET. ss.
    }
    {
      instantiate (1 := (Time.middle from' ts3')).
      introv INJ_MSG LT. 
      exploit wf_monotonic_inj; [eapply MEM_INJ | | eapply INJ_MSG | eapply INJ_MSG_SPLIT | eauto..].
      auto_solve_time_rel. ii; des.
      rewrite GET_MEM_S in H. inv H.
      auto_solve_time_rel.
    }
    {
      introv INJ_MSG LT.
      inv MEM_INJ.
      exploit COMPLETE; [eapply INJ_MSG | eauto..]. ii; des.
      exploit Memory.get_disjoint; [eapply H | eapply GET3 | eauto..].
      ii; des; subst. inv H2.
      rewrite INJ_MSG_SPLIT in INJ_MSG. inv INJ_MSG.
      eauto.
      assert (LT_TS3: Time.lt ts3 ts).
      {
        destruct (Time.le_lt_dec ts ts3); eauto. 
        exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst; ss.
        auto_solve_time_rel.
        unfold Interval.disjoint in H0.
        specialize (H0 ts).
        false.
        eapply H0; eauto.
        econs; ss; eauto. eapply Time.le_lteq; eauto.
        econs; eauto; ss.
        clear - TS12 LT. auto_solve_time_rel.
      }
      exploit wf_monotonic_inj; [ | eapply LT_TS3 | eapply INJ_MSG_SPLIT | eapply INJ_MSG | eauto..].
      econs; eauto.
      ii; des.
      eapply MemoryProps.memory_get_ts_le in H1.
      clear - SPLIT_MSG2 H2 H1.
      cut (Time.le ts3' ts'). ii.
      clear - SPLIT_MSG2 H. auto_solve_time_rel.
      auto_solve_time_rel.
    } 
    ii; des.
    assert
      (MSG_WF': Message.wf
                  (Message.concrete val'0 (TView.write_released (Local.tview lc')
                                                               sc' loc (Time.middle from' ts3') releasedr' ord))).
    {
      inv MSG_WF. econs.   
      eapply View_opt_wf_inj with
          (inj := fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then
                                  Some (Time.middle from' ts3') else inj loc1 to1); eauto.
      eapply incr_inj_TViewInj; eauto. 
      eapply incr_inj_opt_ViewInj; eauto. 
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      des_if; eauto. ss; tryfalse. des; tryfalse.
    }
    exploit Memory.split_exists;
      [eapply GET_PROMISE | eapply SPLIT_MSG1 | eapply SPLIT_MSG2 | eapply MSG_WF' | eauto..].
    introv PROMISE_SPLIT. destruct PROMISE_SPLIT as (prom' & PROMISE_SPLIT).
    exploit Memory.split_get0; [eapply PROMISE_SPLIT | eauto..]. ii; des.
    exploit Memory.remove_exists; [eapply GET6 | eauto..].
    introv PROMISE_REMOVE. destruct PROMISE_REMOVE as (prom1' & PROMISE_REMOVE).
    exploit Memory.split_exists;
      [eapply GET_MEM_S | eapply SPLIT_MSG1 | eapply SPLIT_MSG2 | eauto..].
    introv MEM_SPLIT. destruct MEM_SPLIT as (mem1' & MEM_SPLIT). 
    do 7 eexists.
    split.
    { 
      econs. eauto. eauto.
      instantiate (1 := (Time.middle from' ts3')).
      inv WRITABLE. econs. 
      eapply writable_inj with
          (inj := fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then
                                  Some (Time.middle from' ts3') else inj loc1 to1); eauto.
      eapply incr_inj_TViewInj; eauto. eapply incr_inj_closed_tviewInj; eauto.
      des_if; eauto; ss; des; ss.

      econs. eapply Memory.promise_split. eapply PROMISE_SPLIT.
      eapply MEM_SPLIT. 
      econs. 
      eapply TLE_write_prs with (inj := inj'); eauto.
      rewrite NEW_INJ. des_if; eauto. ss; subst; ss. destruct o; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      eauto.
      eauto.
      eapply PROMISE_REMOVE.
      
      introv ORDERING.
      eapply mem_nonsynch_loc_msgInj_weak; eauto.
      inv LOCAL_WF; eauto.
      inv LOCAL_WF'; eauto.
      eauto. eauto.
    } 
    split. eauto.
    split.
    {
      clear - PROM_LESS GET0 TS23.
      eapply PROM_LESS in GET0.
      eapply Time.le_lteq. left. auto_solve_time_rel.
    }
    split.
    {
      exists ts3 ts3' from val' released'.
      split; eauto. split; eauto. eapply Time.le_lteq; eauto.
    }
    split. eauto.
    split. eauto.
    split. eauto.
    split.
    {
      eapply opt_ViewInj_write_released_inj; eauto.
      eapply incr_inj_TViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      rewrite NEW_INJ. des_if; eauto; des; subst; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }
    split.
    {
      introv INJ'.
      rewrite NEW_INJ in INJ'.
      des_ifH INJ'; ss. des; subst. inv INJ'.
      clear - MEM. exploit Memory.split_get0; eauto.
      ii; des. eauto.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      inv MEM_INJ. eauto.
      inv MEM_INJ. eauto.
      des_if; ss; des; subst; ss.
      inv MEM_INJ. eauto.
      inv MEM_INJ. eauto.
      des_if; ss; des; subst; ss.
      inv MEM_INJ. eauto.
      inv MEM_INJ. eauto.
      des_if; ss; des; subst; ss.
      inv MEM_INJ. eauto.
      inv MEM_INJ. eauto.
      inv MEM_INJ. eauto.
    }
    {
      introv KIND. inv KIND.
      do 3 eexists. split; eauto.
    }
  - (* lower *)
    des; subst. inv TS.
    exploit MemoryProps.lower_succeed_wf; [eapply PROMISES | eauto..].
    ii; des. inv MSG_LE.
    assert (PROM_GET': exists to' from' released',
               Memory.get loc to' (Local.promises lc') = Some (from', Message.concrete val0 released') /\
               inj loc to = Some to' /\ Time.lt from' to').
    {
      inv PRM_EQ.
      eapply SOUND in GET. des; eauto.
      do 3 eexists. split; eauto.
    }
    destruct PROM_GET' as (to' & from' & released' & PROM_GET' & INJ_TO & LT).
    assert (MEM_GFT': Memory.get loc to' mem' = Some (from', Message.concrete val0 released')).
    {
      inv LOCAL_WF'; eauto.
    }
    assert
      (MSG_WF': Message.wf
                  (Message.concrete val0 (TView.write_released (Local.tview lc') sc' loc to' releasedr' ord))).
    {
      inv MSG_WF. econs.   
      eapply View_opt_wf_inj with (inj := inj); eauto.
      inv MEM_INJ. eauto.
    }
    assert (MSG_VIEW_INJ: opt_ViewInj inj released released').
    {
      inv LOCAL_WF. inv LOCAL_WF'.
      eapply PROMISES0 in GET. eapply PROMISES1 in PROM_GET'.
      clear - MEM_INJ GET PROM_GET' INJ_TO.
      inv MEM_INJ.
      exploit SOUND; eauto. ii; des.
      rewrite INJ_TO in H. inv H.
      rewrite PROM_GET' in H1. inv H1. eauto.
    }
    assert(VIEW_LE: View.opt_le (TView.write_released (Local.tview lc') sc' loc to' releasedr' ord) released').
    {
      eapply view_opt_le_inj; eauto.
      eapply opt_ViewInj_write_released_inj; eauto.
      inv MEM_INJ; eauto.
      eapply closed_opt_viewInj_write_released; eauto.
      eapply closed_optview_msginj_implies_closed_viewInj; eauto.
      clear - CLOSED_MEM GET LOCAL_WF.
      inv CLOSED_MEM. inv LOCAL_WF. eapply PROMISES in GET.
      eapply CLOSED in GET; des. inv MSG_CLOSED; eauto.
      inv MEM_INJ; eauto.
    }
    exploit Memory.lower_exists; [eapply PROM_GET' | eapply LT | eapply MSG_WF' | eauto..].
    introv PROM_LOWER'.
    destruct PROM_LOWER' as (prom' & PROM_LOWER').
    exploit Memory.lower_get0; [eapply PROM_LOWER' | eauto..].
    ii; des.
    exploit Memory.remove_exists; [eapply GET1 | eauto..].
    introv PROM_REMOVE. destruct PROM_REMOVE as (prom1' & PROM_REMOVE).
    exploit Memory.lower_exists_le; [ | eapply PROM_LOWER' | eauto..].
    inv LOCAL_WF'; eauto.
    introv MEM_LOWER. destruct MEM_LOWER as (mem1' & MEM_LOWER).
    do 2 eexists. exists mem1' inj. eexists. exists from' to'.
    split.
    {
      econs; eauto.
      inv WRITABLE. econs.
      eapply writable_inj with (inj := inj); eauto.
      inv MEM_INJ. eauto.
      econs. eapply Memory.promise_lower; eauto.
      econs. 
      eapply TLE_write_prs with (inj := inj); eauto.
      inv MEM_INJ. eauto. eauto.
      introv ORDERING.
      eapply mem_nonsynch_loc_msgInj_weak; eauto.
      inv LOCAL_WF; eauto.
      inv LOCAL_WF'; eauto.
    }
    split. eauto.
    split. eauto.
    split.
    {
      exists to to' from val0 released.
      split; eauto. split; eauto. eapply Time.le_lteq; eauto.
    }
    split.
    {
      eapply functional_extensionality_dep. ii.
      eapply functional_extensionality_dep. ii.
      des_if; ss; des; subst; ss.
    }
    split. unfold incr_inj. ii; eauto.
    split. inv MEM_INJ. eauto.
    split.
    {
      eapply opt_ViewInj_write_released_inj; eauto.
      inv MEM_INJ. eauto.
    }
    split.
    {
      clear - MEM_LOWER MEM MEM_INJ. ii.
      erewrite Memory.lower_o; eauto.
      inv MEM_INJ.
      des_if; ss; des; subst; ss; eauto.
    }
    {
      ii; ss.
    }
Qed.

Lemma injection_weak_fecne_step
      inj mem mem' lc1 sc1 ordr ordw lc2 sc2 lc1' sc1'
      (LOCAL_FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (MEM_INJ: MsgInj inj mem mem')
      (TVIEW_INJ: TViewInj inj (Local.tview lc1) (Local.tview lc1'))
      (PRM_EQ: promise_inj_weak inj (Local.promises lc1) (Local.promises lc1'))
      (LOCAL_WF: Local.wf lc1 mem)
      (LOCAL_WF': Local.wf lc1' mem')
      (NOT_SC_FENCE: ordw <> Ordering.seqcst):
  exists lc2' sc2',
    <<INJ_FENCE: Local.fence_step lc1' sc1' ordr ordw lc2' sc2'>> /\
    <<TVIEW_INJ': TViewInj inj (Local.tview lc2) (Local.tview lc2')>> /\
    <<PRM_EQ': promise_inj_weak inj (Local.promises lc2) (Local.promises lc2')>>.
Proof.
  inv LOCAL_FENCE.
  do 2 eexists.
  split.
  {
    econs; eauto. introv ORDER. 
    inv LOCAL_WF. inv LOCAL_WF'.
    eapply mem_nonsynch_msgInj_weak with (promises := Local.promises lc1); eauto.
    ii. eapply PROMISES in H. eapply promise_inj_weak_bot; eauto.
  }
  ss. split; eauto.
  {
    eapply TView_inj_fence_prsv; eauto. 
    eapply read_fence_tview_prsv; eauto.
  }
Qed.

Lemma injection_weak_lower_to_none
      inj lc1 mem1 loc from to val' lc2 mem2 val released lc1' mem1' lo
      (LOCAL_PROMISE: Local.promise_step lc1 mem1 loc from to (Message.concrete val' None) lc2 mem2
                                         (Memory.op_kind_lower (Message.concrete val released)))
      (MEM_INJ: MsgInj inj mem1 mem1')
      (PROM_EQ: promise_inj_weak inj (Local.promises lc1) (Local.promises lc1'))
      (LOCAL_WF: Local.wf lc1 mem1)
      (LOCAL_WF': Local.wf lc1' mem1')
      (CLOSED_MEM: Memory.closed mem1)
      (AT_INJ_ID: forall loc to to', lo loc = Ordering.atomic -> inj loc to = Some to' -> to = to')
      (AT_PRM_SAME_ITV: 
         forall loc from to val R,
           lo loc = Ordering.atomic ->
           Memory.get loc to (Local.promises lc1) = Some (from, Message.concrete val R) ->
           exists R', Memory.get loc to (Local.promises lc1') = Some (from, Message.concrete val R')):
  exists lc2' mem2' released' from' to',
    <<INJ_PROMISE': Local.promise_step lc1' mem1' loc from' to' (Message.concrete val' None) lc2' mem2'
                                       (Memory.op_kind_lower (Message.concrete val released'))>> /\
    <<MEM_INJ': MsgInj inj mem2 mem2'>> /\
    <<PROM_EQ': promise_inj_weak inj (Local.promises lc2) (Local.promises lc2')>> /\
    <<TVIEW_EQ1: Local.tview lc1 = Local.tview lc2>> /\
    <<TVIEW_EQ2: Local.tview lc1' = Local.tview lc2'>> /\ 
    <<AT_PRM_SAME_ITV': 
         forall loc from to val R,
           lo loc = Ordering.atomic ->
           Memory.get loc to (Local.promises lc2) = Some (from, Message.concrete val R) ->
           exists R', Memory.get loc to (Local.promises lc2') = Some (from, Message.concrete val R')>>.
Proof.
  inv LOCAL_PROMISE; ss. inv PROMISE. des; subst; ss. inv RESERVE.
  exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
  assert(GET'_LOWER: exists released0' from' to',
            Memory.get loc to' (Local.promises lc1') = Some (from', Message.concrete val0 released0')
            /\ Time.lt from' to' /\ inj loc to = Some to').
  {
    inv PROM_EQ.
    exploit SOUND; [eapply GET | eauto..]. ii; des.
    do 3 eexists. split; eauto.
  }
  des.
  assert(exists promises2', Memory.lower (Local.promises lc1') loc from' to' (Message.concrete val0 released0')
                                    (Message.concrete val' None) promises2').
  {
    eapply Memory.lower_exists; eauto.
    econs; eauto.
    inv MSG_LE.
    econs; eauto.
  }
  des.
  assert(exists mem2', Memory.lower mem1' loc from' to' (Message.concrete val0 released0')
                               (Message.concrete val' None) mem2').
  {
    eapply Memory.lower_exists_le; eauto.
    inv LOCAL_WF'; eauto.
  }
  des.
  do 5 eexists.
  split.
  {
    econs. econs.
    eapply H. eapply H0.
    econs. unfold View.unwrap. ss.
    unfold TimeMap.bot. eapply Time.bot_spec.
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
    eapply promise_inj_weak_lower in PROM_EQ; eauto.
  }
  split; eauto.
  split; eauto.
  {
    ii.
    erewrite Memory.lower_o in H2; eauto.
    des_ifH H2; ss; des; subst; ss; eauto.
    inv H2.
    eapply AT_INJ_ID in GET'_LOWER1; eauto. subst.
    exploit Memory.lower_get0; [eapply H | eauto..]. ii; des; eauto.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
    eapply AT_PRM_SAME_ITV in GET3; eauto.
    des. rewrite GET1 in GET3. inv GET3.
    eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply H | eauto..]. ii; des.
    eapply AT_PRM_SAME_ITV in H2; eauto. des.
    rewrite H2 in GET1. inv GET1; eauto.
    inv MSG_LE0. eauto.
  }
Qed.

Lemma injection_weak_cancel
      inj lc1 mem1 loc from to lc2 mem2 msg lc1' mem1' lo
      (LOCAL_PROMISE: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel)
      (MEM_INJ: MsgInj inj mem1 mem1')
      (PROM_EQ: promise_inj_weak inj (Local.promises lc1) (Local.promises lc1'))
      (LOCAL_WF': Local.wf lc1' mem1')
      (AT_PRM_SAME_ITV: 
         forall loc from to val R,
           lo loc = Ordering.atomic ->
           Memory.get loc to (Local.promises lc1) = Some (from, Message.concrete val R) ->
           exists R', Memory.get loc to (Local.promises lc1') = Some (from, Message.concrete val R')):
  exists lc2' mem2',
    <<INJ_PROMISE': Local.promise_step lc1' mem1' loc from to msg lc2' mem2' Memory.op_kind_cancel>> /\
    <<MEM_INJ': MsgInj inj mem2 mem2'>> /\
    <<PROM_EQ': promise_inj_weak inj (Local.promises lc2) (Local.promises lc2')>> /\
    <<TVIEW_EQ1: Local.tview lc1 = Local.tview lc2>> /\
    <<TVIEW_EQ2: Local.tview lc1' = Local.tview lc2'>> /\
    <<AT_PRM_SAME_ITV': 
         forall loc from to val R,
           lo loc = Ordering.atomic ->
           Memory.get loc to (Local.promises lc2) = Some (from, Message.concrete val R) ->
           exists R', Memory.get loc to (Local.promises lc2') = Some (from, Message.concrete val R')>>.
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
    eapply promise_inj_weak_remove_reseve; eauto.
  }
  split; eauto.
  split; eauto.
  {
    introv AT_LOC GET_PROM.
    erewrite Memory.remove_o in GET_PROM; eauto.
    des_ifH GET_PROM; ss.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  }
Qed.
    
Hint Resolve local_wf_read local_wf_write write_step_closed_mem: local_wf.
  
Inductive na_view (loc0: Loc.t): TView.t -> TView.t -> Time.t -> Time.t -> Memory.t -> Memory.t -> Prop :=
| na_view_intro_le_max_ts
    tview tview' max_ts max_ts' mem mem'
    (LE_MAX_TS: Time.le ((View.rlx (TView.acq tview)) loc0) max_ts)
    (GT_MAX_NOCOVER: forall ts from msg, Time.lt max_ts ts ->
                                    Memory.get loc0 ts mem = Some (from, msg) ->
                                    msg = Message.reserve)
    (GT_MAX_NOCOVER': forall ts', Time.lt max_ts' ts' -> ~ (Cover.covered loc0 ts' mem')):
    na_view loc0 tview tview' max_ts max_ts' mem mem'
| na_view_intro_gt_max_ts
    tview tview' max_ts max_ts' mem mem'
    (GT_MAX_TS: Time.lt max_ts ((View.pln (TView.cur tview)) loc0))
    (GT_MAX_TS': Time.lt max_ts' ((View.pln (TView.cur tview')) loc0))
    (MAX_MSG: forall ts from msg, Time.lt ((View.pln (TView.cur tview)) loc0) ts ->
                             Memory.get loc0 ts mem = Some (from, msg) ->
                             msg = Message.reserve)
    (MAX_MSG': forall ts', Time.lt ((View.pln (TView.cur tview')) loc0) ts' ->
                    ~ (Cover.covered loc0 ts' mem')):
    na_view loc0 tview tview' max_ts max_ts' mem mem'.

Lemma na_view_read_prsv
      loc0 tview tview' max_ts max_ts' mem mem' inj released released' loc to to' ord from val R
      (MEM_INJ: MsgInj inj mem mem')
      (NA_VIEW: na_view loc0 tview tview' max_ts max_ts' mem mem')
      (TVIEW_WF: TView.wf tview)
      (OPT_VIEWINJ: opt_ViewInj inj released released')
      (CLOSED_OPT_VIEW: Memory.closed_opt_view released mem)
      (GET: Memory.get loc to mem = Some (from, Message.concrete val R))
      (READ: Time.le ((View.pln (TView.cur tview)) loc) to)
      (INJ_MSG: inj loc to = Some to'):
  na_view loc0 (TView.read_tview tview loc to released ord)
            (TView.read_tview tview' loc to' released' ord) max_ts max_ts' mem mem'.
Proof.
  inv NA_VIEW.
  - assert(LE: loc = loc0 -> Time.le to max_ts).
    {
      ii. destruct(Time.le_lt_dec to max_ts); subst; eauto.
      exploit GT_MAX_NOCOVER; eauto; ii; ss.
    }
    eapply na_view_intro_le_max_ts; eauto.
    unfold TView.read_tview; ss. des_if.
    { 
      unfold View.singleton_ur_if. destruct released; ss.
      {
        viewtac.
        eapply time_le_singleton_prsv; eauto.
        inv CLOSED_OPT_VIEW. inv CLOSED.
        unfold Memory.closed_timemap in RLX.
        specialize (RLX loc0). des.
        destruct (Time.le_lt_dec (View.rlx t loc0) max_ts); eauto.
        eapply GT_MAX_NOCOVER in l; eauto. ss.
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
  - eapply na_view_intro_gt_max_ts; eauto.
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
      eapply MAX_MSG'; eauto.
    }
Qed. 

Lemma na_view_read_gt_max_ts
      lc1 mem1 loc to1 val1 released1 ord1 lc1' lo
      lc2 mem2 to2 val2 released2 ord2 lc2' max_ts1 max_ts2
      (NA_VIEW: na_view loc (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (LOCAL_READ1: Local.read_step lc1 mem1 loc to1 val1 released1 ord1 lc1' lo)
      (LOCAL_READ2: Local.read_step lc2 mem2 loc to2 val2 released2 ord2 lc2' lo)
      (LT_MAX: Time.lt max_ts1 to1):
  Time.lt max_ts2 to2 /\ Time.le (Memory.max_ts loc mem2) to2.
Proof.
  inv LOCAL_READ1. inv LOCAL_READ2.
  inv NA_VIEW.
  - exploit GT_MAX_NOCOVER; [eapply LT_MAX | eauto..]; ii; ss.
  - inv READABLE. inv READABLE0.
    split.
    {
      clear - GT_MAX_TS' PLN0.
      auto_solve_time_rel.
    }
    {
      exploit Memory.max_ts_spec; [eapply GET0 | eauto..]. ii; des.
      destruct (Time.le_lt_dec (Memory.max_ts loc mem2) to2); eauto. 
      clear - PLN0 l GET1 MAX_MSG'.
      eapply Time.le_lteq in PLN0; des; eauto.
      cut(Time.lt (View.pln (TView.cur (Local.tview lc2)) loc) (Memory.max_ts loc mem2)). ii.
      eapply MAX_MSG' in H; eauto.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      rewrite H1 in l. clear - l. auto_solve_time_rel.
      contradiction H. econs; ss; eauto. econs; ss.
      eapply Time.le_lteq; eauto.
      auto_solve_time_rel.
      subst.
      exploit MAX_MSG'; eauto; ii; ss.
      exploit Memory.get_ts; eauto. ii; des; subst; ss.
      rewrite H0 in l. auto_solve_time_rel.
      econs; eauto. econs; ss; eauto.
      eapply Time.le_lteq; eauto.
    }
Qed.

Lemma na_view_write_prsv_loc_write_disj
      lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 val2 releasedr2 released2 lc2' sc2' mem2' kind2 max_ts1 max_ts2 loc0
      (NA_VIEW: na_view loc0 (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val2 releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (DISJ_LOC: loc <> loc0):
  na_view loc0 (Local.tview lc1') (Local.tview lc2') max_ts1 max_ts2 mem1' mem2'.
Proof.
  inv WRITE1. inv WRITE2. ss.
  inv NA_VIEW.
  - eapply na_view_intro_le_max_ts; eauto.
    {
      clear - LE_MAX_TS DISJ_LOC.
      unfold TView.write_tview; ss.
      unfold TimeMap.join, TimeMap.singleton; ss.
      rewrite Loc_add_neq; eauto. ss. unfold LocFun.init.
      eapply Time.join_spec; eauto.
      eapply Time.bot_spec.
    }
    {
      ii. 
      exploit Memory_write_o; [eapply WRITE | eapply H0 | eauto..]. ii; des.
      eapply GT_MAX_NOCOVER in H1; eauto.
      subst. ss.
    }
    {
      ii. eapply GT_MAX_NOCOVER' in H; eauto. contradiction H.
      eapply write_disj_cover_prsv with (mem := mem2) (mem' := mem2'); eauto.
    }
  - eapply na_view_intro_gt_max_ts; eauto.
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
      ii.
      exploit Memory_write_o; [eapply WRITE | eapply H0 | eauto..]. ii; des; subst; ss.
      eapply MAX_MSG in H1; eauto.
      clear - H.
      eapply Time_lt_join in H. des; eauto.
    }
    {
      ii. unfold TView.write_tview in H; ss.
      unfold TimeMap.join, TimeMap.singleton in H; ss.
      rewrite Loc_add_neq in H; eauto. unfold LocFun.init in H.
      eapply Time_lt_join in H; des.
      eapply MAX_MSG' in H; eauto. contradiction H.
      eapply write_disj_cover_prsv with (mem := mem2) (mem' := mem2'); eauto.
    }
Qed.

Lemma na_view_write_prsv_loc_write_le_max
      lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 val2 releasedr2 released2 lc2' sc2' mem2' kind2
      max_ts1 max_ts2
      (LOCAL_WF: Local.wf lc1 mem1)
      (NA_VIEW: na_view loc (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val2 releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (LE1: Time.le to1 max_ts1)
      (LE2: Time.le to2 max_ts2):
  na_view loc (Local.tview lc1') (Local.tview lc2') max_ts1 max_ts2 mem1' mem2'.
Proof.
  inv NA_VIEW.
  - inv WRITE1; ss. inv WRITE2; ss.
    eapply na_view_intro_le_max_ts.
    {
      clear - LE_MAX_TS LE1.
      unfold TView.write_tview; ss.
      unfold TimeMap.singleton.
      eapply Time.join_spec; eauto.
      rewrite Loc_add_eq; eauto.
    }
    {
      ii.
      eapply Memory_write_o in H0; eauto. des; eauto.
      subst. clear - LE1 H. auto_solve_time_rel.
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

Lemma na_view_write_gt_max_implies_max_write
      lc lc0 max_ts max_ts0 sc mem loc from to val releasedr released ord
      lc' sc' mem' kind lo ts f val' R' mem0
      (LOCAL_WF: Local.wf lc mem)
      (NA_VIEW: na_view loc (Local.tview lc) (Local.tview lc0) max_ts max_ts0 mem mem0)
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (LT: Time.lt max_ts to)
      (GET: Memory.get loc ts mem = Some (f, Message.concrete val' R')):
  Time.lt ts to.
Proof.
  inv NA_VIEW.
  - assert(LE_MAX_TS': Time.le ts max_ts).
    {
      destruct (Time.le_lt_dec ts max_ts); eauto.
      exploit MemoryProps.memory_get_ts_strong; eauto. ii; des; subst.
      auto_solve_time_rel.
      exploit GT_MAX_NOCOVER; eauto; ii; ss.
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
Qed.

Lemma na_view_write_prsv_loc_write_gt_max
      lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 val2 releasedr2 released2 lc2' sc2' mem2' kind2
      max_ts1 max_ts2
      (LOCAL_WF: Local.wf lc1 mem1)
      (LOCAL_WF': Local.wf lc2 mem2)
      (NA_VIEW: na_view loc (Local.tview lc1) (Local.tview lc2) max_ts1 max_ts2 mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val1 releasedr1 released1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val2 releasedr2 released2 ord lc2' sc2' mem2' kind2 lo)
      (LE1: Time.lt max_ts1 to1)
      (LE2: Time.lt max_ts2 to2):
  na_view loc (Local.tview lc1') (Local.tview lc2') max_ts1 max_ts2 mem1' mem2'.
Proof.
  inv NA_VIEW.
  - inv WRITE1; ss. inv WRITE2; ss.
    eapply na_view_intro_gt_max_ts.
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
      clear - LE1 GT_MAX_NOCOVER WRITE H1 H0.
      inv WRITE. inv PROMISE; ss.
      {
        erewrite Memory.add_o in H0; eauto. des_ifH H0; ss; des; subst; ss.
        auto_solve_time_rel. eapply GT_MAX_NOCOVER in H0; eauto.
        clear - LE1 H1. auto_solve_time_rel.
      }
      {
        des; subst. inv RESERVE.
        erewrite Memory.split_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss.
        auto_solve_time_rel.
        des_ifH H0; ss; des; subst; ss.
        clear - LE1 GT_MAX_NOCOVER H1 MEM.
        exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
        cut (Time.lt max_ts1 ts3). ii.
        exploit GT_MAX_NOCOVER; [eapply H | eapply GET0 | eauto..]. ii; ss.
        auto_solve_time_rel.
        eapply GT_MAX_NOCOVER in H0; eauto.
        auto_solve_time_rel.
      }
      {
        des; subst.
        erewrite Memory.lower_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss.
        auto_solve_time_rel.
        eapply GT_MAX_NOCOVER in H0; eauto.
        auto_solve_time_rel.
      }
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
    eapply na_view_intro_gt_max_ts.
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
      clear - GT_MAX_TS H H1 H0 WRITE MAX_MSG.
      inv WRITE. inv PROMISE; ss.
      {
        erewrite Memory.add_o in H0; eauto.
        des_ifH H0; ss; des; subst; ss.
        auto_solve_time_rel.
        eapply MAX_MSG in H0; eauto.
      }
      {
        des; subst. inv RESERVE.
        erewrite Memory.split_o in H0; eauto. des_ifH H0; ss; des; subst; ss.
        auto_solve_time_rel.
        des_ifH H0; ss; des; subst; ss.
        exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
        eapply MAX_MSG in GET0; eauto. ss.
        eapply MAX_MSG in H0; eauto.
      }
      {
        des; subst.
        erewrite Memory.lower_o in H0; eauto. des_ifH H0; ss; des; subst; ss.
        auto_solve_time_rel.
        eapply MAX_MSG in H0; eauto.
      }
    }
    {
      ii. unfold TView.write_tview in H; ss. unfold TimeMap.join, TimeMap.singleton in H.
      rewrite Loc_add_eq in H.
      eapply Time_lt_join in H. des.
      exploit write_gt_not_cover_prs'; [eapply WRITE0 | eauto..]. ii.
      eapply MAX_MSG' with (ts' := ts); eauto.
      clear - LOCAL_WF' WRITABLE0 H2. inv WRITABLE0.
      inv LOCAL_WF'. clear TVIEW_CLOSED PROMISES FINITE BOT.
      inv TVIEW_WF. inv CUR. unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc).
      clear - H2 TS PLN_RLX.
      cut (Time.lt (View.pln (TView.cur (Local.tview lc2)) loc) to2). ii.
      auto_solve_time_rel.
      auto_solve_time_rel.
    }
Qed.

Lemma na_view_fence_step_prsv
      loc max_ts max_ts' mem mem' ordr ordw
      lc1 sc1 lc2 sc2
      lc1' sc1' lc2' sc2'
      (NA_VIEW: na_view loc (Local.tview lc1) (Local.tview lc1') max_ts max_ts' mem mem')
      (FENCE_STEP1: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (FENCE_STEP2: Local.fence_step lc1' sc1' ordr ordw lc2' sc2')
      (NOT_SC_FENCE: ordw <> Ordering.seqcst)
      (LOCAL_WF1: Local.wf lc1 mem)
      (LOCAL_WF2: Local.wf lc1' mem'):
  na_view loc (Local.tview lc2) (Local.tview lc2') max_ts max_ts' mem mem'.
Proof.
  inv FENCE_STEP1; ss. inv FENCE_STEP2; ss.
  inv NA_VIEW.
  - eapply na_view_intro_le_max_ts; eauto.
    clear - LOCAL_WF1 LE_MAX_TS NOT_SC_FENCE. inv LOCAL_WF1.
    clear TVIEW_CLOSED PROMISES FINITE BOT.
    erewrite write_fence_tview_not_sc; eauto.
  - erewrite write_fence_tview_not_sc; eauto.
    erewrite write_fence_tview_not_sc; eauto.
    eapply na_view_intro_gt_max_ts; eauto; ss.
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
      eapply MAX_MSG'; eauto.
      inv LOCAL_WF2. inv TVIEW_WF.
      inv CUR_ACQ. unfold TimeMap.le in PLN.
      specialize (PLN loc).
      clear - LT PLN. auto_solve_time_rel.
    }
Qed.

Lemma na_view_lower_none_step_prsv
      loc0 max_ts max_ts'
      lc1 mem1 loc from to val' lc2 mem2 val released
      lc1' mem1' from' to' lc2' mem2' released'
      (NA_VIEW: na_view loc0 (Local.tview lc1) (Local.tview lc1') max_ts max_ts' mem1 mem1')
      (LOCAL_PROMISE: Local.promise_step lc1 mem1 loc from to (Message.concrete val' None) lc2 mem2
                                         (Memory.op_kind_lower (Message.concrete val released)))
      (LOCAL_PROMISE': Local.promise_step lc1' mem1' loc from' to' (Message.concrete val' None) lc2' mem2'
                                          (Memory.op_kind_lower (Message.concrete val released'))):
  na_view loc0 (Local.tview lc2) (Local.tview lc2') max_ts max_ts' mem2 mem2'.
Proof.
  inv LOCAL_PROMISE. inv PROMISE. des; ss. inv RESERVE.
  inv LOCAL_PROMISE'. inv PROMISE. des; ss. inv RESERVE.
  inv NA_VIEW.
  - eapply na_view_intro_le_max_ts; eauto.
    ii.
    erewrite Memory.lower_o in H0; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    inv H0.
    exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
    eapply GT_MAX_NOCOVER in GET; eauto. ss.
    ii. exploit GT_MAX_NOCOVER'; eauto.
    eapply lower_covered with (mem1 := mem1') (mem2 := mem2'); eauto.
  - eapply na_view_intro_gt_max_ts; eauto.
    ii.
    erewrite Memory.lower_o in H0; eauto.
    des_ifH H0; ss; des; subst; ss; eauto.
    inv H0.
    exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
    eapply MAX_MSG in GET; eauto. ss.
    ii. exploit MAX_MSG'; eauto.
    eapply lower_covered with (mem1 := mem1') (mem2 := mem2'); eauto.
Qed.

Lemma na_view_cancel_step_prsv
      loc0 max_ts max_ts'
      lc1 mem1 loc from to msg lc2 mem2
      lc1' mem1' lc2' mem2' 
      (NA_VIEW: na_view loc0 (Local.tview lc1) (Local.tview lc1') max_ts max_ts' mem1 mem1')
      (CANCEL: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel)
      (CANCEL': Local.promise_step lc1' mem1' loc from to msg lc2' mem2' Memory.op_kind_cancel):
  na_view loc0 (Local.tview lc2) (Local.tview lc2') max_ts max_ts' mem2 mem2'.
Proof.
  inv CANCEL; ss. inv PROMISE.
  inv CANCEL'; ss. inv PROMISE.
  inv NA_VIEW.
  - econs; eauto. ii.
    erewrite Memory.remove_o in H0; eauto.
    des_ifH H0; ss.
    eapply GT_MAX_NOCOVER in H0; eauto.
    ii. eapply GT_MAX_NOCOVER'; eauto.
    eapply remove_covered with (mem2 := mem2') in H0; eauto. des; eauto.
  - eapply na_view_intro_gt_max_ts; eauto.
    ii.
    erewrite Memory.remove_o in H0; eauto.
    des_ifH H0; ss.
    eapply MAX_MSG in H0; eauto.
    ii.
    eapply MAX_MSG'; eauto.
    eapply remove_covered with (mem2 := mem2') in H0; eauto. des; eauto.
Qed.

Lemma no_na_race_consistent_construction:
  forall n lang (inj: Mapping) (max_ts max_ts': Loc.t -> Time.t)
    st lc sc mem lc' sc' mem' st0 lc0 sc0 mem0 lo sc_temp
    (WF_LOCAL: Local.wf lc mem)
    (WF_LOCAL': Local.wf lc' mem')
    (CLOSED_MEM: Memory.closed mem)
    (CLOSED_MEM': Memory.closed mem')
    (ATOM_INJ_ID: forall loc t t', lo loc = Ordering.atomic -> inj loc t = Some t' -> t = t')
    (ATOM_NOTCOVER: forall loc ts,
        lo loc = Ordering.atomic -> ~ (Cover.covered loc ts mem) -> ~ (Cover.covered loc ts mem'))
    (NA_MAX_TS: forall loc, lo loc = Ordering.nonatomic ->
                       (exists to', inj loc (max_ts loc) = Some to' /\ Time.le to' (max_ts' loc)))
    (MEM_INJ: MsgInj inj mem mem')
    (TVIEW_INJ: TViewInj inj (Local.tview lc) (Local.tview lc'))
    (PRM_EQ: promise_inj_weak inj (Local.promises lc) (Local.promises lc'))
    (AT_PRM_SAME_ITV: forall loc from to val R,
        lo loc = Ordering.atomic ->
        Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) ->
        exists R', Memory.get loc to (Local.promises lc') = Some (from, Message.concrete val R'))
    (SPEC_VIEW: forall loc,
        lo loc = Ordering.nonatomic ->
        na_view loc (Local.tview lc) (Local.tview lc') (max_ts loc) (max_ts' loc) mem mem')
    (NA_MAX_RESERVE: forall loc,
        lo loc = Ordering.nonatomic ->
        exists from val R, Memory.get loc (max_ts loc) mem = Some (from, Message.concrete val R))
    (PRM_LESS: forall loc to from val R,
        lo loc = Ordering.nonatomic ->
        Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) ->
        Time.le to (max_ts loc))
    (NO_WW_RACE : ~ @thrd_ww_race lang lo (Thread.mk lang st lc sc_temp mem))
    (STEPS: rtcn (Thread.nprm_step lo) n (Thread.mk lang st lc sc mem)
                 (Thread.mk lang st0 lc0 sc0 mem0))
    (FULFILL: Local.promises lc0 = Memory.bot),
  exists st0' lc0' sc0' mem0',
    rtc (Thread.nprm_step lo) (Thread.mk lang st lc' sc' mem') (Thread.mk lang st0' lc0' sc0' mem0') /\
    Local.promises lc0' = Memory.bot.
Proof.
  induction n; ii.
  - (* fulfill all *)
    inv STEPS.
    exploit promise_inj_weak_bot; [eapply PRM_EQ | eapply FULFILL | eauto..].
    ii.
    do 4 eexists.
    split.
    eauto. eauto.
  - (* fulfill in progress *)
    inv STEPS.
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
      introv THRD_WW_RACE.
      contradiction NO_WW_RACE.
      clear - STATE THRD_WW_RACE.
      inv THRD_WW_RACE.
      econs.
      eapply Relation_Operators.rt1n_trans.
      econs. econs.
      eapply Thread.step_program.
      econs.
      Focus 2. eapply Local.step_silent; eauto.
      ss; eauto.
      eapply STEPS.
      eauto. eauto. eauto. eauto. eauto. eauto.
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
        introv GET_PROM. 
        clear - LOCAL0 INJ_READ AT_PRM_SAME_ITV GET_PROM.
        inv LOCAL0. inv INJ_READ. ss.
        eapply AT_PRM_SAME_ITV; eauto.
      }
      {
        (* na view *)
        ii. 
        inv LOCAL0; ss.
        inv INJ_READ; ss.
        eapply na_view_read_prsv; eauto.
        inv WF_LOCAL; eauto.
        eapply closed_mem_implies_closed_msg; eauto.
        inv READABLE; eauto.
      }
      {
        (* promise less max *)
        rewrite <- PROM_EQ; eauto.
      }
      clear - NO_WW_RACE STATE LOCAL0.
      introv THRD_WW_RACE.
      contradiction NO_WW_RACE.
      inv THRD_WW_RACE.
      econs.
      eapply Relation_Operators.rt1n_trans.
      econs. econs.
      eapply Thread.step_program.
      econs.
      Focus 2. eapply Local.step_read; eauto.
      ss; eauto.
      eapply STEPS.
      eauto. eauto. eauto. eauto. eauto. eauto.
    + (* write *)
      destruct (lo loc) eqn:AT_NA_LOC.
      {
        (* write atomic location *)
        exploit injection_write_step_id_weak2; [eapply LOCAL0 | | eapply MEM_INJ | eauto..].
        ii. eapply ATOM_NOTCOVER in H; eauto.
        instantiate (1 := None). econs; eauto.
        instantiate (1 := sc). ii; des.
        assert (sc = sc2). inv LOCAL0. eauto. subst sc2.
        assert(Promise_inj: promise_inj_weak inj' (Local.promises lc2) (Local.promises lc1')).
        {
          exploit write_step_promise_inj_weak_stable; [eapply LOCAL0 | eapply INJ_WRITE | eapply PRM_EQ | eauto..].
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
                        (max_ts := max_ts) in A23; eauto.
        {
          (* fulfill *) 
          destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
          exists st0'. do 3 eexists. split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eapply STEPS.
          econs. econs. 
          instantiate (1 := ThreadEvent.write loc from to val releasedw' ord).
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
        ii. rewrite INJ_MSG in H0. des_ifH H0; des; ss; subst; ss; eauto. inv H0; eauto.
        {
          (* OTHER NOT COVER *)
          introv OTHER_LOC.
          destruct(Loc.eq_dec loc loc0); subst.  
          eapply write_not_cover_prsv_write; [| eapply LOCAL0 | eapply INJ_WRITE | eauto..]; eauto.
          ii.
          eapply ATOM_NOTCOVER with (ts := ts) in OTHER_LOC; eauto. 
          contradiction OTHER_LOC; eauto.
          eapply write_disj_cover_prsv with (mem := mem') (mem' := mem1') in H0; eauto.
          ii. contradiction H.
          eapply write_disj_cover_prsv with (mem := mem) (mem' := mem2); eauto.
        }
        {
          (* max_ts' *)
          instantiate (1 := max_ts').
          ii. exploit NA_MAX_TS; eauto. ii; des.
          eexists. split; eauto.
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
          (* promise itv *)
          ii.
          destruct (Loc.eq_dec loc loc0). subst loc0. eauto.
          rewrite <- write_step_disj_promise_prsv with (lc := lc) in H0; eauto.
          eapply AT_PRM_SAME_ITV in H; eauto. des.
          exists R'.
          rewrite <- write_step_disj_promise_prsv with (lc := lc'); eauto.
        }
        {
          (* na view *)
          ii. 
          eapply na_view_write_prsv_loc_write_disj with (lc1 := lc) (lc2 := lc'); eauto.
          ii; subst. rewrite AT_NA_LOC in H; ss.
        }
        {
          (* Reserve *)
          ii.
          exploit NA_MAX_RESERVE; eauto. ii; des.
          eapply write_step_concrete_msg_prsv in H0; eauto.
          des. eauto.
        }
        {
          (* promise less *)
          ii. eapply write_step_promise_concrete_le_prsv; [eapply LOCAL0 | eauto..].
        }

        clear - NO_WW_RACE STATE LOCAL0.
        instantiate (1 := sc_temp). introv THRD_WW_RACE.
        contradiction NO_WW_RACE.
        inv THRD_WW_RACE.
        econs.
        eapply Relation_Operators.rt1n_trans.
        econs. econs.
        eapply Thread.step_program.
        econs.
        Focus 2. eapply Local.step_write; eauto.
        inv LOCAL0. econs; eauto. inv WRITABLE. econs; eauto.
        ss; eauto.
        eapply STEPS.
        eauto. eauto. eauto. eauto. eauto. eauto.
      }
      {
        (* write non-atomic location *)
        assert(KIND_ADD_OR_OTHER: kind = Memory.op_kind_add \/ kind <> Memory.op_kind_add).
        {
          destruct kind; ss; eauto.
          right. ii; ss.
          right. ii; ss.
          right. ii; ss.
        } 
        assert (ord = Ordering.plain).
        {
          clear - LOCAL0 AT_NA_LOC.
          inv LOCAL0. rewrite AT_NA_LOC in LO.
          destruct ord; ss.
        }
        subst ord.
        destruct KIND_ADD_OR_OTHER as [KIND_ADD | KIND_OTHER].
        {
          subst.
          destruct (Time.le_lt_dec to (max_ts loc)) as [LE_MAX | GT_MAX].
          {
            exploit injection_write_step_na_weak; [eapply LOCAL0 | eapply LE_MAX | | | eapply MEM_INJ | eauto..]. 
            {
              eapply NA_MAX_RESERVE in AT_NA_LOC. eauto.
            }
            {
              introv GET_MEM MAY_RACE.
              destruct (Memory.get loc ts (Local.promises lc)) eqn: GET_PROMISE.
              destruct p. inv WF_LOCAL.
              eapply PROMISES in GET_PROMISE. rewrite GET_MEM in GET_PROMISE.
              inv GET_PROMISE; eauto.
              contradiction NO_WW_RACE.
              eapply Promise_fulfill_sc_not_care in A23; eauto. des.
              econs.
              eauto.
              ss. eauto.
              eapply GET_MEM. eauto. 
              clear - LOCAL0 MAY_RACE. inv LOCAL0. inv WRITABLE.
              auto_solve_time_rel. 
              eapply Relation_Operators.rt1n_trans.
              2: eapply A23. 
              econs; eauto. econs. eapply Thread.step_program.
              econs; eauto.
              econs. inv LOCAL0. econs; eauto. inv WRITABLE. econs; eauto.
              ss.
            }
            {
              instantiate (1 := None). econs; eauto.
            }
            instantiate (1 := sc').
            ii; des.
            eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                            (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
            {
              (* fulfill *)
              destruct A23 as (st0' & lc0' & sc0' & mem0' & FULFILL_STEPS & BOT).
              exists st0' lc0' sc0' mem0'.
              split; eauto.
              eapply Relation_Operators.rt1n_trans.
              eapply Thread.nprm_step_program_step. econs.
              Focus 2. eapply Local.step_write. eapply INJ_WRITE.
              ss; eauto.
              ss; eauto.
              eauto.
            }
            {
              (* local wf *)
              eapply local_wf_write; eauto.
            }
            {
              (* local wf *)
              eapply local_wf_write; eauto.
            }
            {
              (* memory closed *)
              eapply write_step_closed_mem; eauto.
            }
            {
              (* memory closed *)
              eapply write_step_closed_mem; eauto.
            }
            {
              (* atomic injection identity *)
              introv AT_LOC INJ'.
              rewrite INJ_MSG in INJ'.
              des_ifH INJ'; ss; des; subst; ss; eauto.
              inv INJ'.
              rewrite AT_NA_LOC in AT_LOC. ss.
            }
            {
              (* atomic cover *)
              introv AT_LOC NOT_COVER COVER. contradiction NOT_COVER.
              assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in AT_LOC. ss.
              rewrite <- write_disj_cover_prsv with (mem := mem') in COVER; eauto.
              rewrite <- write_disj_cover_prsv with (mem := mem); eauto.
              eapply ATOM_NOTCOVER in AT_LOC; tryfalse.
              eapply AT_LOC in COVER; ss.
              ii.
              contradiction NOT_COVER.
              rewrite <- write_disj_cover_prsv with (mem := mem); eauto.
            }
            {
              ii. exploit NA_MAX_TS; eauto.
              ii; des. eexists. split; eauto.
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
              (* atomic promise cover same *)
              ii.
              assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in H. ss.
              rewrite <- write_step_disj_promise_prsv with (lc := lc) in H0; eauto.
              eapply AT_PRM_SAME_ITV in H0; eauto. des.
              exists R'.
              rewrite <- write_step_disj_promise_prsv with (lc := lc'); eauto.
            } 
            {
              (* na view *)
              ii. 
              destruct (Loc.eq_dec loc loc0); subst.
              eapply na_view_write_prsv_loc_write_le_max with
                  (mem1 := mem) (mem2 := mem'); eauto.
              clear - NA_MAX_TS LE_MAX MON_INJ INJ_INCR H.
              exploit NA_MAX_TS; eauto. ii; des.
              eapply INJ_INCR in H0.
              exploit Time_le_monotonic_inj; [eapply LE_MAX | | | eapply MON_INJ | idtac..].
              instantiate (2 := loc0).
              ss. des_if; ss; des; subst; ss; eauto.
              instantiate (1 := to'0). ss.
              ii.
              auto_solve_time_rel.
              eapply na_view_write_prsv_loc_write_disj; eauto.
            } 
            {
              (* max reserve *)
              introv NA_LOC. 
              eapply NA_MAX_RESERVE in NA_LOC. des.
              eapply write_step_concrete_msg_prsv in NA_LOC; eauto.
              des. eauto.
            }
            {
              (* Promise less *)
              ii. eapply write_step_promise_concrete_le_prsv; [eapply LOCAL0 | eauto..].
            }

            introv THRD_RACE.
            contradiction NO_WW_RACE.
            inv THRD_RACE.
            econs.
            eapply Relation_Operators.rt1n_trans.
            econs. econs. eapply Thread.step_program.
            econs.
            Focus 2. eapply Local.step_write; eauto.
            inv LOCAL0. econs; eauto. inv WRITABLE. econs; eauto.
            ss. eauto.
            eapply STEPS.
            eauto. eauto. eauto. eauto. eauto. eauto.
          }
          {
            assert(WRITE_MAX: forall ts f val' R',
                      Memory.get loc ts mem = Some (f, Message.concrete val' R') -> Time.lt ts to).
            {
              ii. specialize (SPEC_VIEW loc). exploit SPEC_VIEW; eauto. introv NA_VIEW_LOC.
              eapply na_view_write_gt_max_implies_max_write; [eapply WF_LOCAL | eapply NA_VIEW_LOC | eauto..].
            }
            exploit injection_write_step_id_weak_GT;
            [eapply LOCAL0 | eapply GT_MAX | | eapply MEM_INJ | eapply WF_LOCAL | eapply WF_LOCAL' | eauto..]. 
            eauto.
            instantiate (1 := None). econs.
            instantiate (1 := Time.join (max_ts' loc) (Memory.max_ts loc mem')).
            introv GET'.
            exploit Memory.max_ts_spec; [eapply GET' | eauto..]. ii; des.
            clear - MAX.
            cut(Time.le (Memory.max_ts loc mem') (Time.join (max_ts' loc) (Memory.max_ts loc mem'))). ii.
            auto_solve_time_rel.
            eapply Time.join_r.
            instantiate (1 := Time.incr (Time.join (max_ts' loc) (Memory.max_ts loc mem'))). ii.
            exploit H; eauto. auto_solve_time_rel.
            clear H. instantiate (1 := sc'). ii. des.
            assert(Promise_inj: promise_inj_weak inj' (Local.promises lc2) (Local.promises lc1')).
            {
              exploit write_step_promise_inj_weak_stable; [eapply LOCAL0 | eapply INJ_WRITE | eapply PRM_EQ | eauto..].
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
                            (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
            {
              (* fulfill *)
              destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
              exists st0' lc0' sc0' mem0'.
              split; eauto.
              eapply Relation_Operators.rt1n_trans.
              eapply Thread.nprm_step_program_step. econs.
              Focus 2. eapply Local.step_write. eapply INJ_WRITE.
              ss; eauto.
              ss; eauto.
              eauto.
            }
            {
              (* local wf *)
              eapply local_wf_write; eauto.
            }
            {
              (* local wf *)
              eapply local_wf_write; eauto.
            }
            {
              (* memory closed *)
              eapply write_step_closed_mem; eauto.
            }
            {
              (* memory closed *)
              eapply write_step_closed_mem; eauto.
            }
            {
              (* atomic injection identity *)
              introv AT_LOC INJ'.
              destruct (Loc.eq_dec loc loc0). subst loc0. rewrite AT_NA_LOC in AT_LOC. ss.
              rewrite INJ_MSG in INJ'.
              des_ifH INJ'; ss; des; subst; ss; eauto.
            }
            {
              (* atomic cover *)
              introv AT_LOC NOT_COVER COVER. contradiction NOT_COVER.
              assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in AT_LOC. ss.
              rewrite <- write_disj_cover_prsv with (mem := mem') in COVER; eauto.
              rewrite <- write_disj_cover_prsv with (mem := mem); eauto.
              eapply ATOM_NOTCOVER in AT_LOC; tryfalse.
              eapply AT_LOC in COVER; ss.
              ii.
              contradiction NOT_COVER.
              rewrite <- write_disj_cover_prsv with (mem := mem); eauto.
            }
            {
              ii. exploit NA_MAX_TS; eauto.
              ii; des. eexists. split; eauto.
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
              (* atomic promise cover same *)
              ii.
              assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in H. ss.
              rewrite <- write_step_disj_promise_prsv with (lc := lc) in H0; eauto.
              eapply AT_PRM_SAME_ITV in H0; eauto. des.
              exists R'.
              rewrite <- write_step_disj_promise_prsv with (lc := lc'); eauto.
            }
            {
              introv NA_LOC.
              destruct (Loc.eq_dec loc loc0). 
              {
                subst loc0.
                exploit SPEC_VIEW; [eapply NA_LOC | eauto..]. introv NA_VIEW.
                eapply na_view_write_prsv_loc_write_gt_max;
                  [eapply WF_LOCAL | eapply WF_LOCAL' | eapply NA_VIEW | eapply LOCAL0 | eapply INJ_WRITE | eauto..].
                cut (Time.lt (Time.join (max_ts' loc) (Memory.max_ts loc mem'))
                             (Time.incr (Time.join (max_ts' loc) (Memory.max_ts loc mem')))).
                ii.
                cut (Time.le (max_ts' loc) (Time.join (max_ts' loc) (Memory.max_ts loc mem'))).
                ii.
                auto_solve_time_rel.
                eapply Time.join_l.
                auto_solve_time_rel.
              }
              {
                eapply na_view_write_prsv_loc_write_disj; eauto.
              }
            } 
            {
              (* max reserve *)
              introv NA_LOC. 
              eapply NA_MAX_RESERVE in NA_LOC. des.
              eapply write_step_concrete_msg_prsv in NA_LOC; eauto.
              des. eauto.
            }
            {
              (* Promise less *)
              ii. eapply write_step_promise_concrete_le_prsv; [eapply LOCAL0 | eauto..].
            }

            introv THRD_RACE.
            contradiction NO_WW_RACE.
            inv THRD_RACE.
            econs.
            eapply Relation_Operators.rt1n_trans.
            econs. econs. eapply Thread.step_program.
            econs.
            Focus 2. eapply Local.step_write; eauto.
            inv LOCAL0. econs; eauto. inv WRITABLE. econs; eauto.
            ss. eauto.
            eapply STEPS.
            eauto. eauto. eauto. eauto. eauto. eauto.
          }
        }
        {
          exploit injection_write_step_weak_not_add; eauto.
          instantiate (1 := None). econs.
          instantiate (1 := sc'). ii; des.
          assert(Promise_inj: promise_inj_weak inj' (Local.promises lc2) (Local.promises lc1')).
          {
            exploit promise_fulfill_promise_inj_weak_stable;
              [eapply LOCAL0 | eapply INJ_WRITE | eapply PRM_EQ | eauto..].
            rewrite INJ_MSG.
            des_if; ss; des; subst; ss; eauto. 
          }
          assert(MEM_INJ': MsgInj inj' mem2 mem1').
          {
            eapply promise_fulfill_step_msgInj_stable; eauto. 
            rewrite INJ_MSG. des_if; des; ss; subst; ss.
            introv INJ'. eapply INJ_COMPLETE in INJ'. des.
            do 3 eexists. eauto.
          }
          assert(LE: Time.le to' (max_ts' loc)).
          {
            clear - NA_MAX_TS MEM_INJ LE_PROMISE LE_PROMISE0 LE_PROMISE1 PRM_LESS AT_NA_LOC.
            exploit NA_MAX_TS; eauto. ii; des.
            eapply PRM_LESS in LE_PROMISE; eauto.
            inv MEM_INJ.
            exploit monotonic_inj_implies_le_prsv;
              [eapply MONOTONIC | eapply LE_PROMISE | eapply LE_PROMISE0 | eapply H | eauto..].
            ii.
            clear - LE_PROMISE1 H1 H0.
            cut (Time.le ts' (max_ts' loc)). ii.
            clear - LE_PROMISE1 H. auto_solve_time_rel.
            auto_solve_time_rel.
          }
          eapply IHn with (sc' := sc') (lc' := lc1') (mem' := mem1') (inj := inj')
                          (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
          {
            (* fulfill *)
            destruct A23 as (st0' & lc0' & sc0' & mem0' & STEPS & BOT).
            exists st0' lc0' sc0' mem0'.
            split; eauto.
            eapply Relation_Operators.rt1n_trans.
            eapply Thread.nprm_step_program_step. econs.
            Focus 2. eapply Local.step_write. eapply INJ_WRITE.
            ss; eauto.
            ss; eauto.
            eauto.
          }
          {
            (* local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* local wf *)
            eapply local_wf_write; eauto.
          }
          {
            (* memory closed *)
            eapply write_step_closed_mem; eauto.
          }
          {
            (* memory closed *)
            eapply write_step_closed_mem; eauto.
          }
          {
            (* atomic injection identity *)
            introv AT_LOC INJ'.
            destruct (Loc.eq_dec loc loc0). subst loc0. rewrite AT_NA_LOC in AT_LOC. ss.
            rewrite INJ_MSG in INJ'.
            des_ifH INJ'; ss; des; subst; ss; eauto.
          }
          {
            (* atomic cover *)
            introv AT_LOC NOT_COVER COVER. contradiction NOT_COVER.
            assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in AT_LOC. ss.
            rewrite <- write_disj_cover_prsv with (mem := mem') in COVER; eauto.
            rewrite <- write_disj_cover_prsv with (mem := mem); eauto.
            eapply ATOM_NOTCOVER in AT_LOC; tryfalse.
            eapply AT_LOC in COVER; ss.
            ii.
            contradiction NOT_COVER.
            rewrite <- write_disj_cover_prsv with (mem := mem); eauto.
          }
          {
            ii. exploit NA_MAX_TS; eauto.
            ii; des. eexists. split; eauto.
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
            (* atomic promise cover same *)
            ii.
            assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in H. ss.
            rewrite <- write_step_disj_promise_prsv with (lc := lc) in H0; eauto.
            eapply AT_PRM_SAME_ITV in H0; eauto. des.
            exists R'.
            rewrite <- write_step_disj_promise_prsv with (lc := lc'); eauto.
          }
          {
            introv NA_LOC.
            destruct (Loc.eq_dec loc loc0). 
            {
              subst loc0.
              exploit SPEC_VIEW; eauto. introv NA_VIEW.
              eapply na_view_write_prsv_loc_write_le_max;
                [eapply WF_LOCAL | eapply NA_VIEW | eapply LOCAL0 | eapply INJ_WRITE |
                 eapply LE_WRITE | eapply LE | eauto..].
            }
            {
              eapply na_view_write_prsv_loc_write_disj; eauto.
            }
          } 
          {
            (* max reserve *)
            introv NA_LOC. 
            eapply NA_MAX_RESERVE in NA_LOC. des.
            eapply write_step_concrete_msg_prsv in NA_LOC; eauto.
            des. eauto.
          }
          {
            (* Promise less *)
            ii. eapply write_step_promise_concrete_le_prsv; [eapply LOCAL0 | eauto..].
          }

          introv THRD_RACE.
          contradiction NO_WW_RACE.
          inv THRD_RACE.
          econs.
          eapply Relation_Operators.rt1n_trans.
          econs. econs. eapply Thread.step_program.
          econs.
          Focus 2. eapply Local.step_write; eauto.
          inv LOCAL0. econs; eauto. inv WRITABLE. econs; eauto.
          ss. eauto.
          eapply STEPS.
          eauto. eauto. eauto. eauto. eauto. eauto.
        }
      }
    + (* update *)
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
      assert(NA_VIEW': forall loc, lo loc = Ordering.nonatomic ->
                              na_view loc (Local.tview lc3) (Local.tview lc3') (max_ts loc) (max_ts' loc) mem mem').
      {
        introv NA_LOC.
        assert (loc <> loc0). ii; subst. rewrite AT in NA_LOC. ss.
        destruct lc, lc3. inv LOCAL1. inv LC2; ss.
        destruct lc', lc3'. inv INJ_READ. inv LC2; ss.
        eapply na_view_read_prsv; eauto.
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
      assert(Promise_inj0: promise_inj_weak inj (Local.promises lc3) (Local.promises lc3')).
      {
        rewrite <- PROM_EQ. rewrite <- PROM_EQ'. eauto.
      }
      assert(tsr = tsr').
      {
        exploit ATOM_INJ_ID; eauto.
      }
      subst tsr'.
      (* construct write *) 
      exploit injection_write_step_id_weak2;
        [eapply LOCAL2 | | eapply MEM_INJ | eapply WF_LOCAL3 | eapply WF_LOCAL3' | eauto..].
      {
        clear - ATOM_NOTCOVER AT.
        ii. eapply ATOM_NOTCOVER in H0; eauto.
      }
      {
        clear - AT_PRM_SAME_ITV AT PROM_EQ PROM_EQ'. ii.
        rewrite <- PROM_EQ in H. rewrite <- PROM_EQ'. eauto.
      }
      instantiate (1 := sc'). ii. des.
      assert(Promise_inj: promise_inj_weak inj' (Local.promises lc2) (Local.promises lc1')).
      {
        exploit write_step_promise_inj_weak_stable; [eapply LOCAL2 | eapply INJ_WRITE | eapply Promise_inj0 | eauto..].
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
                      (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
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
        (* OTHER NOT COVER *)
        introv OTHER_LOC.
        destruct(Loc.eq_dec loc loc0); subst.  
        eapply write_not_cover_prsv_write; [| eapply LOCAL2 | eapply INJ_WRITE | eauto..]; eauto.
        ii.
        eapply ATOM_NOTCOVER with (ts := ts) in OTHER_LOC; eauto. 
        contradiction OTHER_LOC; eauto.
        eapply write_disj_cover_prsv with (mem := mem') (mem' := mem1') in H0; eauto.
        ii. contradiction H.
        eapply write_disj_cover_prsv with (mem := mem) (mem' := mem2); eauto.
      }
      {
        (* max_ts' *)
        ii. exploit NA_MAX_TS; eauto. ii; des.
        eexists. split; eauto.
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
        (* promise itv *)
        ii.
        destruct (Loc.eq_dec loc loc0). subst loc0. eauto.
        rewrite <- write_step_disj_promise_prsv with (lc := lc3) in H0; eauto.
        eapply AT_PRM_SAME_ITV in H; eauto. des.
        exists R'.
        rewrite <- write_step_disj_promise_prsv with (lc := lc3'); eauto.
        rewrite <- PROM_EQ'. eauto.
        rewrite <- PROM_EQ in H0. eauto.
      }
      {
        (* na view *)
        ii. 
        eapply na_view_write_prsv_loc_write_disj with (lc1 := lc3) (lc2 := lc3'); eauto.
        ii; subst. rewrite AT in H; ss.
      }
      {
        (* Reserve *)
        ii.
        exploit NA_MAX_RESERVE; eauto. ii; des.
        eapply write_step_concrete_msg_prsv in H0; eauto.
        des. eauto.
      }
      {
        (* promise less *)
        ii. eapply write_step_promise_concrete_le_prsv; [eapply LOCAL2 | eauto..].
        rewrite <- PROM_EQ. eauto.
      }

      introv THRD_RACE.
      contradiction NO_WW_RACE.
      inv THRD_RACE.
      econs.
      eapply Relation_Operators.rt1n_trans.
      econs. econs. eapply Thread.step_program.
      econs.
      Focus 2. eapply Local.step_update; eauto.
      inv LOCAL2. econs; eauto. inv WRITABLE. econs; eauto.
      ss. eauto.
      eapply STEPS.
      eauto. eauto. eauto. eauto. eauto. eauto.
    + (* fence *)
      assert (SC_FENCE_OR_NOT: ordw = Ordering.seqcst \/ ordw <> Ordering .seqcst).
      {
        destruct ordw; ss; try solve [right; ii; ss]; eauto.
      }
      destruct SC_FENCE_OR_NOT as [SC_FENCE | NOT_SC_FENCE].
      {
        (* sc fence *)
        subst.
        inv LOCAL0; ss. exploit PROMISES; eauto. ii.
        exploit promise_inj_weak_bot; eauto.
        ii.
        do 4 eexists.
        split. eauto. eauto.
      }
      {
        (* not sc fence *)
        exploit injection_weak_fecne_step; eauto.
        instantiate (1 := sc'). ii; des.
        assert (sc' = sc2').
        {
          clear - INJ_FENCE NOT_SC_FENCE.
          inv INJ_FENCE.
          destruct ordw; ss.
        }
        subst sc2'.
        assert (PROM_EQ: Local.promises lc = Local.promises lc2).
        {
          inv LOCAL0; ss.
        }
        assert (PROM_EQ': Local.promises lc' = Local.promises lc2').
        {
          inv INJ_FENCE; eauto.
        }
        eapply IHn with (sc' := sc') (lc' := lc2') (mem' := mem') (inj := inj)
                        (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
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
          (* local wf *)
          eapply Local_wf_fence_not_sc; eauto.
        }
        {
          (* local wf *)
          eapply Local_wf_fence_not_sc; eauto.
        }
        {
          (* atomic promise ITV *)
          rewrite <- PROM_EQ. rewrite <- PROM_EQ'. eauto.
        }
        {
          (* na atomic view *)
          introv NA_LOC.
          eapply na_view_fence_step_prsv; eauto.
        }
        {
          (* non-atomic promise less *)
          introv NA_LOC GET_PROM.
          rewrite <- PROM_EQ in GET_PROM; eauto.
        }

        instantiate (1 := sc_temp).
        introv THRD_WW_RACE.
        contradiction NO_WW_RACE.
        inv THRD_WW_RACE.
        econs.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_program.
        econs.
        Focus 2. eapply Local.step_fence; eauto.
        instantiate (4 := ordr). instantiate (3 := ordw).
        instantiate (2 := lc2). instantiate (1 := sc_temp).
        inv LOCAL0.
        econs; eauto.
        clear - NOT_SC_FENCE.
        destruct ordw; ss.
        destruct ordw; ss.
        eauto. eapply STEPS.
        eauto. eauto. eauto. eauto. eauto. eauto.
      }
    + (* no output *)
      inv LOCAL0; ss.
    + (* PF promise step *)
      inv PF. destruct kind; ss.
      {
        (* lower to none *)
        destruct msg1; ss.
        destruct msg; ss. destruct released0; ss.
        exploit injection_weak_lower_to_none; eauto.
        ii; des.
        eapply IHn with (sc' := sc') (lc' := lc2') (mem' := mem2')
                        (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
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
          (* ATOMIC Loc NOT COVER *)
          introv ATOM_LOC NOT_COVER1 NOT_COVER2. contradiction NOT_COVER1.
          inv LOCAL. inv PROMISE. des; subst. inv RESERVE.
          inv INJ_PROMISE'. inv PROMISE. des; subst. inv RESERVE.
          eapply lower_covered with (mem1 := mem); eauto.
          eapply lower_covered with (mem1 := mem') in NOT_COVER2; eauto.
          exploit ATOM_NOTCOVER; eauto. ii.
          contradiction NOT_COVER1.
          eapply lower_covered with (mem1 := mem); eauto. ii; ss.
        }
        {
          (* TView Inj *)
          rewrite <- TVIEW_EQ1. rewrite <- TVIEW_EQ2. eauto.
        }
        {
          (* na view *)
          introv NA_LOC.
          eapply na_view_lower_none_step_prsv; eauto.
        }
        {
          (* MAX Resereve *)
          ii.
          exploit NA_MAX_RESERVE; eauto. ii; des.
          inv LOCAL. inv PROMISE. des. inv RESERVE.
          erewrite Memory.lower_o; eauto.
          des_if; ss; des; subst; ss; eauto.
        }
        {
          (* Promise lt *)
          introv NA_LOC PROM_GET.
          inv LOCAL; ss. inv PROMISE. des. inv RESERVE.
          erewrite Memory.lower_o in PROM_GET; eauto.
          des_ifH PROM_GET; ss; des; subst; ss; eauto.
          inv PROM_GET.
          exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
          eauto.
        }

        instantiate (1 := sc_temp).
        introv THRD_WW_RACE.
        contradiction NO_WW_RACE.
        inv THRD_WW_RACE.
        econs.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_promise.
        econs. eapply LOCAL. ss. 
        eapply STEPS.
        eauto. eauto. eauto. eauto. eauto. eauto.
      }
      {
        (* Cancel *)
        exploit injection_weak_cancel; eauto. ii; des.
        eapply IHn with (sc' := sc') (lc' := lc2') (mem' := mem2')
                        (max_ts := max_ts) (max_ts' := max_ts') in A23; eauto.
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
          (* Atomic loc not cover *)
          introv AT_LOC. 
          assert(~ covered loc0 ts mem -> ~ covered loc0 ts mem').
          {            
            eapply ATOM_NOTCOVER; eauto.
          }
          introv NOT_COVER.
          eapply cancel_not_cover_prsv with (mem2 := mem2) (mem2' := mem2') in H; eauto.
        }
        {
          (* TView Inj *)
          rewrite <- TVIEW_EQ1. rewrite <- TVIEW_EQ2. eauto.
        }
        {
          (* Spec view *)
          introv NA_LOC.
          eapply na_view_cancel_step_prsv with (mem1 := mem) (mem1' := mem'); eauto.
        }
        {
          (* MAX reserve *)
          introv NA_LOC.
          exploit NA_MAX_RESERVE; eauto. ii; des.
          exists from0 val R. inv LOCAL; ss. inv PROMISE.
          erewrite Memory.remove_o; eauto. des_if; eauto; ss.
          des; subst.
          exploit Memory.remove_get0; [eapply PROMISES | eauto..]. ii; des.
          inv WF_LOCAL. eapply PROMISES0 in GET.
          rewrite H in GET. inv GET.
        }
        {
          (* PROM LE *)
          ii. inv LOCAL; ss. inv PROMISE.
          erewrite Memory.remove_o in H0; eauto.
          des_ifH H0; ss. eauto.
        }

        instantiate (1 := sc_temp).
        introv THRD_WW_RACE.
        contradiction NO_WW_RACE.
        inv THRD_WW_RACE.
        econs.
        eapply Relation_Operators.rt1n_trans.
        econs. econs. eapply Thread.step_promise.
        econs. eapply LOCAL. ss. 
        eapply STEPS.
        eauto. eauto. eauto. eauto. eauto. eauto.
      }
Qed.
