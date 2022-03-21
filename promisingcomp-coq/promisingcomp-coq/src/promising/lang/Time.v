Require Import Orders. 

Require Import sflib.
From Paco Require Import paco.

Require Import DataStructure.
Require Import DenseOrder.
Require Import Basic.
Require Import Loc.

Require Import Coqlib.


Set Implicit Arguments.


Module Time := DenseOrder.
Module TimeFacts := DenseOrderFacts.

Ltac timetac :=
  repeat
    (try match goal with
         | [H: Some _ = None |- _] => inv H
         | [H: None = Some _ |- _] => inv H
         | [H: ?x <> ?x |- _] => by contradict H
         | [H: Time.lt ?x ?x |- _] =>
           apply Time.lt_strorder in H; by inv H
         | [H1: Time.lt ?a ?b, H2: Time.le ?b ?a |- _] =>
           exploit (@TimeFacts.lt_le_lt a b a); eauto;
           let H := fresh "H" in
           intro H; apply Time.lt_strorder in H; by inv H

         | [H: Some _ = Some _ |- _] => inv H

         | [H: context[Time.eq_dec ?a ?b] |- _] =>
           destruct (Time.eq_dec a b)
         | [H: context[TimeFacts.le_lt_dec ?a ?b] |- _] =>
           destruct (TimeFacts.le_lt_dec a b)
         | [|- context[Time.eq_dec ?a ?b]] =>
           destruct (Time.eq_dec a b)
         | [|- context[TimeFacts.le_lt_dec ?a ?b]] =>
           destruct (TimeFacts.le_lt_dec a b)
         end;
     ss; subst; auto).

Module TimeSet := UsualSet Time.
Module TimeFun := UsualFun Time.

Module Interval <: UsualOrderedType.
  Include UsualProd Time Time.

  Inductive mem (interval:t) (x:Time.t): Prop :=
  | mem_intro
      (FROM: Time.lt (fst interval) x)
      (TO: Time.le x (snd interval))
  .

  Lemma mem_dec i x: {mem i x} + {~ mem i x}.
  Proof.
    destruct i as [lb ub].
    destruct (TimeFacts.le_lt_dec x lb).
    - right. intro X. inv X. ss. timetac.
    - destruct (TimeFacts.le_lt_dec x ub).
      + left. econs; s; auto.
      + right. intro X. inv X. ss. timetac.
  Defined.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (FROM: Time.le (fst rhs) (fst lhs))
      (TO: Time.le (snd lhs) (snd rhs))
  .

  Lemma le_mem lhs rhs x
        (LE: le lhs rhs)
        (LHS: mem lhs x):
    mem rhs x.
  Proof.
    inv LE. inv LHS. econs.
    - eapply TimeFacts.le_lt_lt; eauto.
    - etrans; eauto.
  Qed.

  Lemma mem_ub
        lb ub (LT: Time.lt lb ub):
    mem (lb, ub) ub.
  Proof.
    econs; s; auto. refl.
  Qed.

  Lemma mem_split
        lb ub mb t
        (IN: mem (lb, ub) t)
        (MB: mem (lb, ub) mb):
    mem (lb, mb) t \/ mem (mb, ub) t.
  Proof.
    inv IN; inv MB; ss.
    destruct (Time.le_lt_dec t mb).
    left; econstructor; eauto.
    right; econstructor; eauto.
  Qed.

  Definition disjoint (lhs rhs:t): Prop :=
    forall x
      (LHS: mem lhs x)
      (RHS: mem rhs x),
      False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eapply H; eauto.
  Qed.

  Lemma disjoint_imm a b c:
    disjoint (a, b) (b, c).
  Proof.
    ii. inv LHS. inv RHS. ss.
    eapply DenseOrder.lt_strorder.
    eapply TimeFacts.le_lt_lt; [apply TO|apply FROM0].
  Qed.

  Lemma le_disjoint
        a b c
        (DISJOINT: disjoint b c)
        (LE: le a b):
    disjoint a c.
  Proof.
    ii. eapply DISJOINT; eauto. eapply le_mem; eauto.
  Qed. 

  Lemma disjoint_spec
        a b c d
        (DISJOINT: disjoint (a, b) (c, d))
        (LE1: Time.lt a b)
        (LE2: Time.lt c d):
    Time.le d a \/ Time.le b c.
  Proof.
    destruct (Time.le_lt_dec b d).
    {
      destruct (Time.le_lt_dec b c); eauto.
      unfold disjoint in *.
      specialize (DISJOINT b).
      exploit DISJOINT; eauto; ii; ss.
      econs; ss; eauto.
      eapply Time.le_lteq; eauto.
    }
    {
      destruct (Time.le_lt_dec d a); eauto.
      unfold disjoint in DISJOINT.
      specialize (DISJOINT d).
      exploit DISJOINT; eauto; ii; ss.
      econs; ss; eauto.
      eapply Time.le_lteq; eauto.
      econs; eauto; ss.
      eapply Time.le_lteq; eauto.
    }
  Qed.
End Interval.

Lemma lt_join_l
      o lhs rhs
      (LT: Time.lt o lhs):
  Time.lt o (Time.join lhs rhs).
Proof.
  unfold Time.join.
  des_if; eauto.
  eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma Time_le_gt_false
      t t'
      (LE: Time.le t t')
      (GT: Time.lt t' t):
  False.
Proof.
  eapply Time.le_lteq in LE; des; ss.
  eapply Time.Time.lt_strorder_obligation_2 in LE; eauto.
  eapply LE in GT.
  eapply Time.Time.lt_strorder_obligation_1 in GT; ss.
  subst.
  eapply Time.Time.lt_strorder_obligation_1 in GT; ss.
Qed.

Lemma Time_lt_ge_false
      t t'
      (LT: Time.lt t t')
      (GE: Time.le t' t):
  False.
Proof.
  eapply Time.le_lteq in GE; des; ss.
  eapply Time.Time.lt_strorder_obligation_2 in GE; eauto.
  eapply GE in LT. 
  eapply Time.Time.lt_strorder_obligation_1 in LT; ss.
  subst.
  eapply Time.Time.lt_strorder_obligation_1 in LT; ss.
Qed.

Lemma Time_lt_bot_false
      t
      (LT: Time.lt t Time.bot):
  False.
Proof.
  eapply Time_lt_ge_false in LT; ss.
  eapply Time.bot_spec.
Qed.

Lemma Time_join_bot
      to:
  Time.join to Time.bot = to.
Proof.
  unfold Time.join.
  des_if; ss; eauto.
  eapply Time.le_lteq in l. des; subst; eauto.
  eapply Time_lt_bot_false in l; ss.
Qed.

Lemma Time_lt_join
      lhs rhs o
      (LT: Time.lt (Time.join lhs rhs) o):
  Time.lt lhs o /\ Time.lt rhs o.
Proof.
  unfold Time.join in *.
  des_ifH LT. 
  {
    split; eauto.
    eapply DenseOrderFacts.le_lt_lt; eauto.
  }
  {
    split; eauto;
    try eapply Time.lt_strorder_obligation_2; eauto.
  }
Qed.

Lemma Time_le_join
      lhs rhs o
      (LE: Time.le (Time.join lhs rhs) o):
  Time.le lhs o /\ Time.le rhs o.
Proof.
  unfold Time.join in *.
  des_ifH LE.
  {
    split; eauto.
  }
  {
    split; eauto.
    eapply Time.le_lteq. left.
    eapply TimeFacts.lt_le_lt; eauto.
  }
Qed.
