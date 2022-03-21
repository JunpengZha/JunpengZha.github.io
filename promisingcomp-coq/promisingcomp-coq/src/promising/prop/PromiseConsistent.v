Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Loc.

Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import WFConfig.

Set Implicit Arguments.


Lemma promise_step_promise_consistent
      lc1 mem1 loc from to msg lc2 mem2 kind
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  destruct (Memory.op_kind_is_cancel kind) eqn:KIND.
  - destruct kind; ss. inv PROMISE.
    destruct (Memory.get loc0 ts promises2) as [[]|] eqn:GET2.
    + dup GET2. revert GET0.
      erewrite Memory.remove_o; eauto. condtac; ss. i.
      rewrite PROMISE0 in *. inv GET0. eauto.
    + revert GET2. erewrite Memory.remove_o; eauto. condtac; ss; i.
      * des. subst. exploit Memory.remove_get0; eauto. i. des. congr.
      * congr.
  - exploit Memory.promise_get1_promise; eauto. i. des.
    inv MSG_LE. exploit CONS; eauto.
Qed.

Lemma read_step_promise_consistent
      lc1 mem1 loc to val released ord lc2 lo
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2 lo)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii. exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto. ss.
  etrans; [|apply Time.join_l]. etrans; [|apply Time.join_l]. refl.
Qed.

Lemma fulfill_unset_promises
      loc from ts msg
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts msg promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ Message.le msg m.
Proof.
  revert TH2. erewrite Memory.remove_o; eauto. condtac; ss; [|congr].
  des. subst. exploit Memory.remove_get0; eauto. i. des.
  rewrite GET in TH1. inv TH1.
  esplits; eauto. refl.
Qed.

Lemma write_step_promise_consistent
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind lo
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind lo)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. inv WRITE. ii.
  exploit Memory.promise_get1_promise; eauto.
  { inv PROMISE; ss. }
  i. des. inv MSG_LE.
  destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X.
  - dup X. revert X0.
    erewrite Memory.remove_o; eauto. condtac; ss; i.
    rewrite GET in *. inv X0.
    apply CONS in X. eapply TimeFacts.le_lt_lt; eauto.
    s. etrans; [|apply Time.join_l]. refl.
  - exploit fulfill_unset_promises; eauto. i. des. subst.
    apply WRITABLE.
Qed.

Lemma fence_step_promise_consistent
      lc1 sc1 mem1 ordr ordw lc2 sc2
      (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (WF: Local.wf lc1 mem1)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto.
  cut (TView.le (Local.tview lc1)
                (TView.write_fence_tview (TView.read_fence_tview (Local.tview lc1) ordr) sc1 ordw)).
  { i. inv H. apply CUR. }
  etrans.
  - eapply TViewFacts.write_fence_tview_incr. apply WF.
  - eapply TViewFacts.write_fence_tview_mon; try refl; try apply WF.
    eapply TViewFacts.read_fence_tview_incr. apply WF.
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.strong_relaxed ord.
Proof. destruct ord; auto. Qed.

Lemma step_promise_consistent
      lang pf lo e th1 th2
      (STEP: @Thread.step lo lang pf e th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (*(SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))*)
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss.
  - eapply promise_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
  - eapply write_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
    eapply write_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
Qed.

Lemma opt_step_promise_consistent
      lang e th1 th2 lo
      (STEP: @Thread.opt_step lang lo e th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (*(SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))*)
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  inv STEP; eauto using step_promise_consistent.
Qed.

Lemma rtc_all_step_promise_consistent
      lang th1 th2 lo
      (STEP: rtc (@Thread.all_step lang lo) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  revert_until STEP. induction STEP; auto. i.
  inv H. inv USTEP. exploit Thread.step_future; eauto. i. des.
  eapply step_promise_consistent; eauto.
Qed.

Lemma rtc_tau_step_promise_consistent
      lang th1 th2 lo
      (STEP: rtc (@Thread.tau_step lang lo) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  eapply rtc_all_step_promise_consistent; cycle 1; eauto.
  eapply rtc_implies; [|eauto].
  intros. inv H; econstructor; eauto.
Qed.

Lemma rtc_reserve_step_promise_consistent
      lang th1 th2 lo
      (STEPS: rtc (@Thread.reserve_step lang lo) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2)):
  Local.promise_consistent (Thread.local th1).
Proof.
  ginduction STEPS; eauto. i. eapply IHSTEPS in CONS.
  inv H. inv STEP. inv LOCAL. inv PROMISE. ss.
  ii. eapply Memory.add_get1 in PROMISE; eauto.
Qed.

Lemma rtc_cancel_step_promise_consistent
      lang th1 th2 lo
      (STEPS: rtc (@Thread.cancel_step lang lo) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2)):
  Local.promise_consistent (Thread.local th1).
Proof.
  ginduction STEPS; eauto. i. eapply IHSTEPS in CONS.
  inv H. inv STEP. inv LOCAL. inv PROMISE. ss.
  ii. dup PROMISE. eapply Memory.remove_get1 in PROMISE; eauto. des; eauto.
  clarify. eapply Memory.remove_get0 in PROMISES. des. clarify.
Qed.

Lemma rtc_reserve_step_promise_consistent2
      lang (th1 th2: Thread.t lang) lo
      (CONS: Local.promise_consistent (Thread.local th1))
      (STEPS: rtc (@Thread.reserve_step lang lo) th1 th2)
  :
    Local.promise_consistent (Thread.local th2).
Proof.
  ginduction STEPS; eauto.  i. eapply IHSTEPS.
  inv H. inv STEP. inv LOCAL. inv PROMISE. ss.
  ii. erewrite Memory.add_o in PROMISE; eauto. des_ifs.
  eapply CONS; eauto.
Qed.

Lemma rtc_cancel_step_promise_consistent2
      lang (th1 th2: Thread.t lang) lo
      (CONS: Local.promise_consistent (Thread.local th1))
      (STEPS: rtc (@Thread.cancel_step lang lo) th1 th2)
  :
    Local.promise_consistent (Thread.local th2).
Proof.
  ginduction STEPS; eauto.  i. eapply IHSTEPS.
  inv H. inv STEP. inv LOCAL. inv PROMISE. ss.
  ii. erewrite Memory.remove_o in PROMISE; eauto. des_ifs.
  eapply CONS; eauto.
Qed.

Lemma consistent_promise_consistent
      lang th lo
      (CONS: @Thread.consistent lang th lo)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th)):
  Local.promise_consistent (Thread.local th).
Proof.
  destruct th. ss.
  exploit Memory.cap_exists; eauto. i. des.
  exploit Memory.cap_closed; eauto. i.
  exploit Local.cap_wf; eauto. i.
  exploit Memory.max_concrete_timemap_exists; try apply x0. i. des.
  hexploit Memory.max_concrete_timemap_closed; eauto. i.
  exploit CONS; eauto. s. i. des.
  hexploit rtc_tau_step_promise_consistent; try exact STEPS; eauto.
  ii. rewrite PROMISES, Memory.bot_get in *. congr.
Qed.

Lemma promise_consistent_promise_read
      lc1 mem1 loc to val ord released lc2
      f t v r lo
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2 lo)
      (PROMISE: Memory.get loc t (Local.promises lc1) = Some (f, Message.concrete v r))
      (CONS: Local.promise_consistent lc2):
  Time.lt to t.
Proof.
  inv STEP. exploit CONS; eauto. s. i.
  apply TimeFacts.join_lt_des in x. des.
  apply TimeFacts.join_lt_des in AC. des.
  revert BC0. unfold View.singleton_ur_if. condtac; ss.
  - unfold TimeMap.singleton, LocFun.add. condtac; ss.
  - unfold TimeMap.singleton, LocFun.add. condtac; ss.
Qed.

Lemma promise_consistent_promise_write
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      f t v r lo
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind lo)
      (PROMISE: Memory.get loc t (Local.promises lc1) = Some (f, Message.concrete v r))
      (CONS: Local.promise_consistent lc2):
  Time.le to t.
Proof.
  destruct (Memory.get loc t (Local.promises lc2)) as [[]|] eqn:X.
  - inv STEP. inv WRITE. ss.
    dup X. revert X0.
    erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
    exploit Memory.promise_get1_promise; try exact PROMISE; eauto.
    { inv PROMISE0; ss. }
    i. des. inv MSG_LE.
    rewrite X0 in *. inv GET.
    exploit CONS; eauto. i. ss.
    apply TimeFacts.join_lt_des in x. des.
    left. revert BC. unfold TimeMap.singleton, LocFun.add. condtac; ss.
  - inv STEP. inv WRITE.
    exploit Memory.promise_get1_promise; eauto.
    { inv PROMISE0; ss. }
    i. des. inv MSG_LE.
    exploit fulfill_unset_promises; eauto. i. des. subst. refl.
Qed.

Hint Resolve read_step_promise_consistent write_step_promise_consistent promise_step_promise_consistent:
  solve_promise_consistent.

Lemma promise_consistent_prsv_thread_nprm_step:
  forall n lang lo (e e': Thread.t lang)
         (CLOSED_MEM: Memory.closed (Thread.memory e))
         (LOCAL_WF: Local.wf (Thread.local e) (Thread.memory e))
         (NPRM_STEPS: rtcn (@Thread.nprm_step lang lo) n e e')
         (CONS: Local.promise_consistent (Thread.local e')),
    Local.promise_consistent (Thread.local e).
Proof.
  induction n; intros.
  - inv NPRM_STEPS; eauto.
  - inv NPRM_STEPS.  
    inv A12.
    {
      (* program step *)
      des.
      inv PROG; simpls.
      Ltac solve_not_sc_fence A IHn:=
        eapply IHn in A; eauto with solve_promise_consistent.
      
      inv LOCAL.
      {
        (* silent *)
        solve_not_sc_fence A23 IHn.
      }
      {
        (* read *)
        solve_not_sc_fence A23 IHn.
        simpl.
        eapply local_wf_read; eauto.
      }
      {
        (* write *)
        solve_not_sc_fence A23 IHn; simpl.
        eapply write_step_closed_mem; eauto.
        eapply local_wf_write; eauto.
      }
      {
        (* update *)
        solve_not_sc_fence A23 IHn; simpl.
        eapply write_step_closed_mem with (releasedr := releasedr); eauto.
        inv LOCAL1.
        eapply closed_mem_implies_closed_msg; eauto.
        eapply local_wf_read; eauto.
        eapply local_wf_upd; eauto.
      }
      {
        (* fence *)
        destruct (Ordering.le Ordering.seqcst ordw) eqn:SEQCST.
        {
          (* sc fence *)
          destruct ordw; simpls.
          inv LOCAL0.
          eapply Local.bot_promise_consistent.
          exploit PROMISES; eauto.
        }
        {
          (* not sc fence *)
          solve_not_sc_fence A23 IHn; simpl.
          eapply fence_step_promise_consistent; eauto.
          inv LOCAL0.
          eapply local_wf_fence_not_seqcst; eauto.
          destruct lc1; eauto.
        }
      }
      {
        ss.
      }
    }
    {
      (* cancel step *)
      inv PF. ss.
      destruct kind; ss.
      destruct msg1; ss.
      solve_not_sc_fence A23 IHn; eauto; simpl.
      inv LOCAL.
      inv PROMISE.
      eapply Memory.lower_closed; eauto.
      inv LOCAL.
      eapply local_wf_promise; eauto.
      destruct lc1; eauto.
      inv LOCAL; simpls.
      inv PROMISE; ss.
      solve_not_sc_fence A23 IHn; eauto; simpl.
      eapply Memory.cancel_closed; eauto.
      eapply local_wf_promise; eauto.
      destruct lc1; eauto.
    }
Qed.

Lemma read_promise_not_consistent
      lc mem loc from to msg lc' mem' kind loc0 to0 val0 released ord lc'' lo
      (PROMISE: Local.promise_step lc mem loc from to msg lc' mem' kind)
      (LOCAL: Local.read_step lc' mem' loc0 to0 val0 released ord lc'' lo)
      (CONS: Local.promise_consistent lc''):
  (loc, to) <> (loc0, to0).
Proof.
  intro CONTR; inv CONTR.
  inv PROMISE.
  cut(Memory.op_kind_is_cancel kind = false); ii.
  eapply Memory.promise_get2 in PROMISE0; eauto.
  des.
  dup LOCAL.
  inv LOCAL0; ss.
  rewrite GET_MEM in GET. inv GET.
  eapply promise_consistent_promise_read in LOCAL; eauto.
  eapply Time.lt_strorder in LOCAL; eauto.
  destruct (Memory.op_kind_is_cancel kind) eqn:IS_CCL; eauto.
  destruct kind; ss.
  inv PROMISE0.
  eapply Memory.remove_get0 in MEM; des.
  inv LOCAL; ss.
  rewrite GET0 in GET1; ss.
Qed.
