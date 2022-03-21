Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import MSetList.
Require Import MSetFacts.

Require Import sflib.

Set Implicit Arguments.


Module Type HasJoin (Import T:EqLe).
  Parameter join: forall (lhs rhs:t), t.
  Axiom join_comm: forall lhs rhs, join lhs rhs = join rhs lhs.
  Axiom join_assoc: forall a b c, join (join a b) c = join a (join b c).
  Axiom join_l: forall lhs rhs, le lhs (join lhs rhs).
  Axiom join_r: forall lhs rhs, le rhs (join lhs rhs).
  Axiom join_spec: forall lhs rhs o (LHS: le lhs o) (RHS: le rhs o), le (join lhs rhs) o.
End HasJoin.

Module Type HasCaseJoin (Import T:EqLe).
  Include (HasJoin T).
  Axiom join_cases: forall lhs rhs, join lhs rhs = lhs \/ join lhs rhs = rhs.
End HasCaseJoin.

Module Type JoinableType := EqLe <+ HasJoin.


Module UsualOrderedTypeWithLeibniz (S: UsualOrderedType) <: OrderedTypeWithLeibniz.
  Include S.

  Lemma eq_leibniz : forall x y : t, eq x y -> x = y.
  Proof.
    i. unfold eq in *. auto.
  Qed.
End UsualOrderedTypeWithLeibniz.


Module UsualProd (A B:UsualOrderedType) <: UsualOrderedType.
  Definition t := (A.t * B.t)%type.

  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.
  #[export]
  Hint Resolve (Equivalence_Transitive eq_equiv): core.

  Inductive lt_ (lhs rhs:t): Prop :=
  | lt_hd
      (HD: A.lt (fst lhs) (fst rhs))
  | lt_tl
      (HD: (fst lhs) = (fst rhs))
      (TL: B.lt (snd lhs) (snd rhs))
  .
  Definition lt := lt_.
  Global Program Instance lt_strorder: StrictOrder lt.
  Next Obligation.
    ii. inv H.
    - eapply A.lt_strorder; eauto.
    - eapply B.lt_strorder; eauto.
  Qed.
  Next Obligation.
    ii. inv H; inv H0.
    - econs 1. etransitivity; eauto.
    - econs 1. rewrite <- HD0. eauto.
    - econs 1. rewrite HD. eauto.
    - econs 2; etransitivity; eauto.
  Qed.
  #[export]
  Hint Resolve lt_strorder_obligation_2: core.

  Global Program Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. subst. auto.
  Qed.

  Definition compare (lhs rhs:t): comparison :=
    match A.compare (fst lhs) (fst rhs) with
    | Eq =>
      B.compare (snd lhs) (snd rhs)
    | Lt => Lt
    | Gt => Gt
    end.
   Lemma compare_spec :
     forall x y : t,
       CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
   Proof.
     i. destruct x, y. unfold compare. s.
     destruct (A.compare_spec t0 t2);
       try (econs; econs 1; eauto).
     destruct (B.compare_spec t1 t3); subst; econs; auto.
     - econs 2; auto.
     - econs 2; auto.
   Defined.

   Lemma eq_dec: forall x y : t, {x = y} + {x <> y}.
   Proof.
     i. destruct x, y.
     destruct (A.eq_dec t0 t2).
     - destruct (B.eq_dec t1 t3).
       + left. subst. auto.
       + right. contradict n. inv n. auto.
     - right. contradict n. inv n. auto.
   Defined.
End UsualProd.


Module UsualFun (A:UsualDecidableType).
  Polymorphic Definition t (B:Type) := forall (a:A.t), B.

  Section UsualFun.
    Variable (B:Type).

    Definition init (b:B): t B := fun _ => b.

    Definition find (a:A.t) (f:t B): B := f a.

    Definition add (a:A.t) (b:B) (f:t B): t B :=
      fun a' =>
        if A.eq_dec a' a
        then b
        else find a' f.

    Definition init_spec a b:
      find a (init b) = b.
    Proof. auto. Qed.

    Definition add_spec a' a b f:
      find a' (add a b f) =
      if A.eq_dec a' a
      then b
      else find a' f.
    Proof. auto. Qed.

    Lemma add_spec_eq a b f:
      find a (add a b f) = b.
    Proof.
      rewrite add_spec.
      destruct (A.eq_dec a a); auto.
      congruence.
    Qed.

    Lemma add_spec_neq a' a b f (NEQ: a' <> a):
      find a' (add a b f) = find a' f.
    Proof.
      rewrite add_spec.
      destruct (A.eq_dec a' a); auto.
      congruence.
    Qed.

    Lemma ext lhs rhs
          (EQ: forall i, find i lhs = find i rhs):
      lhs = rhs.
    Proof. extensionality i. apply EQ. Qed.

    Lemma add_add a1 a2 b1 b2 f
          (DIFF: a1 <> a2):
      add a1 b1 (add a2 b2 f) = add a2 b2 (add a1 b1 f).
    Proof.
      apply ext. i.
      rewrite ? add_spec.
      destruct (A.eq_dec i a1), (A.eq_dec i a2); auto.
      congruence.
    Qed.

    Lemma add_add_eq a b1 b2 f:
      add a b1 (add a b2 f) = add a b1 f.
    Proof.
      apply ext. i.
      rewrite ? add_spec.
      destruct (A.eq_dec i a); auto.
    Qed.

    Lemma add_init a b:
      add a b (init b) = init b.
    Proof.
      apply ext. i.
      rewrite add_spec.
      destruct (A.eq_dec i a); auto.
    Qed.
  End UsualFun.
End UsualFun.


Module UsualSet (S: UsualOrderedType).
  Module S' := UsualOrderedTypeWithLeibniz (S).
  Module Self := MSetList.MakeWithLeibniz (S').
  Module Facts := MSetFacts.Facts (Self).
  Include Self.

  Definition disjoint (lhs rhs:t): Prop :=
    forall s
      (LHS: In s lhs)
      (RHS: In s rhs),
      False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eapply H; eauto.
  Qed.

  Lemma disjoint_add a lhs rhs:
    disjoint (add a lhs) rhs <-> ~ In a rhs /\ disjoint lhs rhs.
  Proof.
    econs; i.
    - splits; ii; eapply H; eauto.
      + apply add_spec. auto.
      + apply add_spec. auto.
    - ii. apply add_spec in LHS. des; subst; auto.
      eapply H0; eauto.
  Qed.

  Lemma disjoint_union
        lhs1 lhs2 rhs
        (DISJOINT1: disjoint lhs1 rhs)
        (DISJOINT2: disjoint lhs2 rhs):
    disjoint (union lhs1 lhs2) rhs.
  Proof.
    ii. rewrite union_spec in LHS. des.
    - eapply DISJOINT1; eauto.
    - eapply DISJOINT2; eauto.
  Qed.

  Lemma disjoint_union_inv_l
        lhs1 lhs2 rhs
        (DISJOINT: disjoint (union lhs1 lhs2) rhs):
    disjoint lhs1 rhs.
  Proof.
    ii. eapply DISJOINT; eauto.
    apply Facts.union_2. ss.
  Qed.

  Lemma disjoint_union_inv_r
        lhs1 lhs2 rhs
        (DISJOINT: disjoint (union lhs1 lhs2) rhs):
    disjoint lhs2 rhs.
  Proof.
    ii. eapply DISJOINT; eauto.
    apply Facts.union_3. ss.
  Qed.

  Lemma ext lhs rhs
        (EXT: forall i, mem i lhs = mem i rhs):
    lhs = rhs.
  Proof.
    apply eq_leibniz. intro i.
    rewrite ? Facts.mem_iff. rewrite EXT.
    constructor; auto.
  Qed.

  Lemma add_mem a s
        (MEM: mem a s = true):
    add a s = s.
  Proof.
    apply ext. i. destruct (mem i s) eqn:H.
    - rewrite mem_spec in *. rewrite add_spec. auto.
    - destruct (mem i (add a s)) eqn:H'; auto.
      rewrite mem_spec, add_spec in H'. des.
      + subst. rewrite MEM in H. inv H.
      + rewrite <- mem_spec in H'.
        rewrite H in H'. inv H'.
  Qed.

  Definition remove_if_exists i s :=
    if mem i s
    then Some (remove i s)
    else None.

  Lemma remove_if_exists_spec i s s'
        (REMOVE: remove_if_exists i s = Some s'):
    forall i', mem i' s' = mem i' s && if S.eq_dec i i' then false else true.
  Proof.
    i. unfold remove_if_exists in *.
    destruct (mem i s) eqn:IS; inv REMOVE.
    rewrite Facts.remove_b. destruct (mem i' s); auto.
    unfold Facts.eqb, Self.E.eq_dec. destruct (S.eq_dec i i'); auto.
  Qed.
End UsualSet.
