Require Import sflib. 
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Loc.
Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import Local.

Set Implicit Arguments.


Inductive covered (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
.

Inductive covered_reserve (loc: Loc.t) (ts: Time.t) (mem: Memory.t): Prop :=
| covered_reserve_intro
    from to
    (GET: Memory.get loc to mem = Some (from, Message.reserve))
    (ITV: Interval.mem (from, to) ts)
.

Lemma covered_disjoint
      mem1 mem2 loc from to
      (COVER: forall loc ts, covered loc ts mem1 -> covered loc ts mem2)
      (DISJOINT: forall to2 from2 msg2
                   (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)):
  forall to2 from2 msg2
    (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
    Interval.disjoint (from, to) (from2, to2).
Proof.
  ii. exploit COVER; eauto.
  { econs; eauto. }
  i. inv x0. eapply DISJOINT; eauto.
Qed.

Lemma get_disjoint_covered_disjoint
      mem loc from to:
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)) ->
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts).
Proof.
  ii. inv H0. eapply H; eauto.
Qed.

Lemma covered_disjoint_get_disjoint
      mem loc from to:
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts) ->
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)).
Proof.
  ii. eapply H; eauto. econs; eauto.
Qed.

Lemma add_covered
      mem2 mem1 loc from to msg
      l t
      (ADD: Memory.add mem1 loc from to msg mem2):
  covered l t mem2 <->
  covered l t mem1 \/ (l = loc /\ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. auto.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    + subst. econs; eauto. erewrite Memory.add_o; eauto. condtac; ss.
      des; congr.
Qed.

Lemma split_covered
      mem2 mem1 loc ts1 ts2 ts3 msg2 msg3
      l t
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - exploit Memory.split_get0; eauto. i. des.
    inv H. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [refl|].
      inv SPLIT. inv SPLIT0. left. auto.
    + guardH o. des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [|refl].
      inv SPLIT. inv SPLIT0. left. auto.
    + i. econs; eauto.
  - exploit Memory.split_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to) (loc, ts3)); ss.
    + des. subst. rewrite GET0 in GET3. inv GET3.
      destruct (Time.le_lt_dec t ts2).
      * econs.
        { instantiate (2 := from). instantiate (2 := ts2).
          erewrite Memory.split_o; eauto. condtac; ss.
          des; congr.
        }
        { inv ITV. econs; ss. }
      * econs.
        { instantiate (2 := ts2). instantiate (2 := ts3).
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          - des. subst. inv SPLIT. inv SPLIT0.
            exfalso. eapply Time.lt_strorder. eauto.
          - guardH o. des; congr.
        }
        { inv ITV. econs; ss. }
    + econs; eauto. erewrite Memory.split_o; eauto.
      repeat condtac; ss; eauto.
      * guardH o. des. subst. congr.
      * guardH o. guardH o0. des. subst.
        unguardH o. des; congr.
Qed.

Lemma lower_covered
      mem2 mem1 loc from to msg1 msg2
      l t
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. econs; eauto.
      hexploit Memory.lower_get0; eauto. i. des. eauto.
    + i. econs; eauto.
  - exploit Memory.lower_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to0) (loc, to)); ss.
    + des. subst. econs; cycle 1; eauto.
      erewrite Memory.lower_o; eauto. condtac; [|by des].
      rewrite GET in GET1. inv GET1. eauto.
    + econs; eauto.
      erewrite Memory.lower_o; eauto. rewrite GET1. condtac; ss.
      des; congr.
Qed.

Lemma remove_covered
      mem2 mem1 loc from to msg
      l t
      (REMOVE: Memory.remove mem1 loc from to msg mem2):
  covered l t mem2 <->
  covered l t mem1 /\ (l <> loc \/ ~ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.remove_o; eauto. condtac; ss.
    i. split.
    + econs; eauto.
    + destruct (Loc.eq_dec l loc); eauto. subst. des; ss.
      right. ii.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.get_disjoint; [exact GET|exact GET0|..]. i. des; ss.
      apply (x0 t); auto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.remove_get0; eauto. i. des. congr.
    + inv H. econs; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst.
      exploit Memory.remove_get0; eauto. i. des.
      rewrite GET in *. inv GET0. ss.
Qed.

Lemma cap_covered
      mem1 mem2 loc ts
      (CAP: Memory.cap mem1 mem2)
      (COVER: covered loc ts mem1):
  covered loc ts mem2.
Proof.
  inv CAP. inv COVER.
  exploit SOUND; eauto. i.
  econs; eauto.
Qed.

Lemma gt_max_not_covered
      mem loc t
      (GT_MAX: Time.lt (Memory.max_ts loc mem) t):
  ~ covered loc t mem.
Proof.
  intro. inv H.
  eapply Memory.max_ts_spec in GET; des.
  inv ITV; ss.
  cut(Time.lt (Memory.max_ts loc mem) to).
  i. 
  eapply Time_le_gt_false in MAX; eauto.
  eapply DenseOrderFacts.lt_le_lt; eauto.
Qed.

Lemma not_covered_add_succ
      loc from to mem msg
      (LT: Time.lt from to)
      (MSG_WF: Message.wf msg)
      (NOT_COVER: forall t, Interval.mem (from, to) t -> ~ Cover.covered loc t mem):
  exists mem', Memory.add mem loc from to msg mem'.
Proof.
  exploit Memory.add_exists; eauto.
  intros.
  unfold Interval.disjoint; i.
  inv RHS; ss.
  eapply NOT_COVER in LHS.
  contradiction LHS.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma remove_not_cover
      loc from to mem msg mem'
      (REMOVE: Memory.remove mem loc from to msg mem'):
  forall t, Interval.mem (from, to) t -> ~ Cover.covered loc t mem'.
Proof. 
  intros.
  intro.
  inv H0.
  dup REMOVE.
  eapply Memory.remove_get0 in REMOVE0; des.
  destruct (Loc.eq_dec to to0); subst.
  rewrite GET in GET1; inv GET1.
  assert(Memory.get loc to0 mem = Some (from0, msg0)).
  { 
    erewrite Memory.remove_o in GET; eauto.
    des_ifH GET; ss.
  } 
  inv REMOVE.
  inv REMOVE0.
  destruct r; ss; subst.
  unfold Memory.get in *.
  unfold Cell.get in *.
  destruct mem; ss.
  inv WF0.
  exploit DISJOINT; [eapply GET2 | eapply H0 | eapply n | eauto..].
Qed.

Lemma add_not_cover_prsv
      mem1 mem1' loc from to msg1 msg2 mem2 mem2' max_ts
      (NOT_COVER: forall t, ~ Cover.covered loc t mem1 -> Time.le t max_ts -> ~ Cover.covered loc t mem2)
      (ADD1: Memory.add mem1 loc from to msg1 mem1')
      (ADD2: Memory.add mem2 loc from to msg2 mem2')
      (LE: Time.le to max_ts):
  forall t, ~ Cover.covered loc t mem1' -> Time.le t max_ts -> ~ Cover.covered loc t mem2'.
Proof.
  ii. contradiction H. clear H.
  inv H1.
  erewrite Memory.add_o in GET; eauto.
  des_ifH GET; des; ss; subst; ss.
  - inv GET.
    exploit Memory.add_get0; [eapply ADD1 | eauto..]. ii; des.
    econs; eauto.
  - assert(covered loc t mem1).
    {
      destruct (classic (covered loc t mem1)); eauto.
      eapply NOT_COVER in H; eauto.
      contradiction H.
      econs; eauto.
    }
    inv H.
    exploit Memory.add_get1; [eapply ADD1 | eauto..]. ii.
    econs; eauto.
Qed.

Lemma write_disj_cover_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0 ts
      (LOCAL: Local.write_step lc sc mem loc0 from to val releasedr released ord lc' sc' mem' kind lo)
      (DISJ: loc <> loc0):
  covered loc ts mem <-> covered loc ts mem'.
Proof.
  inv LOCAL. inv WRITE. inv PROMISE; ss.
  {
    (* add *)
    split; ii.
    {
      inv H.
      exploit Memory.add_get1; eauto. ii.
      econs; eauto.
    }
    {
      inv H.
      erewrite Memory.add_o in GET; eauto.
      des_ifH GET; ss; des; subst; ss; try solve [econs; eauto].
    }
  }
  {
    (* split *)
    split; ii.
    {
      inv H.
      assert(GET': Memory.get loc to0 mem' = Some (from0, msg)).
      {
        erewrite Memory.split_o; eauto.
        des_if; des; ss; subst; eauto.
        des_if; des; ss; subst; eauto.
        des_if; des; ss; subst; eauto.
      }
      econs; eauto.
    }
    {
      inv H.
      erewrite Memory.split_o in GET; eauto.
      des_ifH GET; des; subst; ss.
      des_ifH GET; des; subst; ss.
      econs; eauto.
      econs; eauto.
      des_ifH GET; des; subst; ss.
      econs; eauto.
      econs; eauto.
    }
  }
  {
    (* lower *)
    des; subst.
    split; ii.
    {
      inv H. econs; eauto. instantiate (1 := msg).
      erewrite Memory.lower_o; eauto. des_if; des; subst; ss. 
    }
    {
      inv H.
      erewrite Memory.lower_o in GET; eauto.
      des_ifH GET; des; subst; ss.
      econs; eauto.
      econs; eauto.
    }
  }
Qed.

Lemma write_le_not_cover_prs
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0 max_ts
      (LOCAL: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (GT_MAX_NOCOVER: forall ts, Time.lt max_ts ts -> ~ covered loc0 ts mem)
      (LE: Time.le to max_ts):
  forall ts, Time.lt max_ts ts -> ~ covered loc0 ts mem'.
Proof.
  ii.
  inv LOCAL. inv WRITE. inv PROMISE; ss.
  - (* add *)
    exploit GT_MAX_NOCOVER; eauto.
    inv H0.
    erewrite Memory.add_o in GET; eauto.
    des_ifH GET; des; ss; subst; ss; try solve [econs; eauto].
    {
      inv GET.
      clear - H LE ITV. inv ITV; ss.
      clear - LE H TO.
      assert(Time.lt max_ts to).
      {
        clear - H TO. eapply DenseOrderFacts.lt_le_lt; eauto.
      }
      clear - LE H0.
      exploit Time_le_gt_false; eauto. ii; ss.
    }
  - (* split *)
    des. subst. inv RESERVE.
    exploit GT_MAX_NOCOVER; eauto.
    eapply split_covered with (mem1 := mem) (mem2 := mem'); eauto.
  - (* lower *)
    des. subst.
    exploit GT_MAX_NOCOVER; eauto.
    eapply lower_covered with (mem1 := mem) (mem2 := mem'); eauto.
Qed.

Lemma write_gt_not_cover_prs'
      promises1 mem1 loc from to val released promises2 mem2 kind loc0
      (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind)
      (GT_NOT_COVER: forall ts, Time.lt to ts -> ~ covered loc0 ts mem1):
  forall ts, Time.lt to ts -> ~ covered loc0 ts mem2.
Proof.
  ii. inv H0. inv ITV; ss.
  inv WRITE. inv PROMISE; ss.
  - (* add *)
    erewrite Memory.add_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss.
    clear - H TO. exploit Time_lt_ge_false; eauto.
    eapply GT_NOT_COVER; eauto. econs; eauto. econs; ss; eauto.
    eapply GT_NOT_COVER; eauto. econs; eauto. econs; ss; eauto.
  - (* split *)
    eapply GT_NOT_COVER; eauto.
    eapply split_covered with (mem2 := mem2); eauto.
    econs; eauto. econs; ss; eauto.
  - (* lower *)
    eapply GT_NOT_COVER; eauto.
    eapply lower_covered with (mem2 := mem2); eauto.
    econs; eauto. econs; ss; eauto.
Qed.

Lemma cancel_not_cover_prsv
      lc1 mem1 loc from to msg lc2 mem2
      lc1' mem1' lc2' mem2' ts loc0
      (NOT_COVER_IMP: ~ covered loc0 ts mem1 -> ~ covered loc0 ts mem1')
      (CANCEL1: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel)
      (CANCEL2: Local.promise_step lc1' mem1' loc from to msg lc2' mem2' Memory.op_kind_cancel)
      (NOT_COVER: ~ covered loc0 ts mem2):
  ~ covered loc0 ts mem2'.
Proof.
  inv CANCEL1. inv PROMISE. inv CANCEL2. inv PROMISE.
  ii.
  exploit NOT_COVER_IMP; eauto.
  {
    ii.
    exploit remove_covered; [eapply MEM | eauto..].
    instantiate (1 := ts). instantiate (1 := loc0). ii.
    exploit remove_covered; [eapply MEM0 | eauto..].
    instantiate (1 := ts). instantiate (1 := loc0). ii.
    contradiction NOT_COVER.
    eapply x0.
    eapply x1 in H. destruct H.
    split; eauto.
  }
  {
    exploit remove_covered; [eapply MEM | eauto..].
    instantiate (1 := ts). instantiate (1 := loc0). ii.
    exploit remove_covered; [eapply MEM0 | eauto..].
    instantiate (1 := ts). instantiate (1 := loc0). ii.
    eapply x1 in H.
    destruct H; eauto.
  }
Qed.
