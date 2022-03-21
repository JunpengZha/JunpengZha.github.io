(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Bounded and unbounded iterators *)

Require Import Axioms.
Require Import Coqlib.
Require Import Wfsimpl.

Set Asymmetric Patterns.

(** This modules defines several Coq encodings of a general "while" loop.
  The loop is presented in functional style as the iteration
  of a [step] function of type [A -> B + A]:
<<
        let rec iterate step a =
          match step a with
          | inl b -> b
          | inr a' -> iterate step a'
>>
  This iteration cannot be defined directly in Coq using [Fixpoint],
  because Coq is a logic of total functions, and therefore we must
  guarantee termination of the loop.
*)

(** * Terminating iteration *)

(** We first implement the case where termination is guaranteed because
  the current state [a] decreases at each iteration. *)

Module WfIter.

Section ITERATION.

Variables A B: Type.
Variable step: A -> B + A.
Variable ord: A -> A -> Prop.
Hypothesis ord_wf: well_founded ord.
Hypothesis step_decr: forall a a', step a = inr _ a' -> ord a' a.

Definition step_info (a: A) : {b | step a = inl _ b} + {a' | step a = inr _ a' & ord a' a}.
Proof.
  caseEq (step a); intros. left; exists b; auto. right; exists a0; auto.
Defined.

Definition iterate_F (a: A) (rec: forall a', ord a' a -> B) : B :=
  match step_info a with
  | inl (exist b P) => b
  | inr (exist2 a' P Q) => rec a' Q
  end.

Definition iterate (a: A) : B := Fix ord_wf iterate_F a.

(** We now prove an invariance property [iterate_prop], similar to the Hoare
  logic rule for "while" loops. *)

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iterate_prop:
  forall a, P a -> Q (iterate a).
Proof.
  intros a0. pattern a0. apply well_founded_ind with (R := ord). auto.
  intros. unfold iterate; rewrite unroll_Fix. unfold iterate_F.
  destruct (step_info x) as [[b U] | [a' U V]].
  exploit step_prop; eauto. rewrite U; auto.
  apply H. auto. exploit step_prop; eauto. rewrite U; auto.
Qed.

End ITERATION.

End WfIter.

(** * Bounded iteration *)

(** The presentation of iteration shown above is predicated on the existence
  of a well-founded ordering that decreases at each step of the iteration.
  In several parts of the CompCert development, it is very painful to define
  such a well-founded ordering and to prove decrease, even though we know our
  iterations always terminate.

  In the presentation below, we choose instead to bound the number of iterations
  by an arbitrary constant.  [iterate] then becomes a function that can fail,
  of type [A -> option B].  The [None] result denotes failure to reach
  a result in the number of iterations prescribed, or, in other terms,
  failure to find a solution to the dataflow problem.  The compiler
  passes that exploit dataflow analysis (the [Constprop], [CSE] and
  [Allocation] passes) will, in this case, either fail ([Allocation])
  or turn off the optimization pass ([Constprop] and [CSE]).

  Since we know (informally) that our computations terminate, we can
  take a very large constant as the maximal number of iterations.
  Failure will therefore never happen in practice, but of
  course our proofs also cover the failure case and show that
  nothing bad happens in this hypothetical case either.  *)

Module PrimIter.

Section ITERATION.

Variables A B: Type.
Variable step: A -> B + A.

Definition num_iterations := 1000000000000%positive.

(** The simple definition of bounded iteration is:
<<
Fixpoint iterate (niter: nat) (a: A) {struct niter} : option B :=
  match niter with
  | O => None
  | S niter' =>
      match step a with
      | inl b => b
      | inr a' => iterate niter' a'
      end
  end.
>>
  This function is structural recursive over the parameter [niter]
  (number of iterations), represented here as a Peano integer (type [nat]).
  However, we want to use very large values of [niter].  As Peano integers,
  these values would be much too large to fit in memory.  Therefore,
  we must express iteration counts as a binary integer (type [positive]).
  However, Peano induction over type [positive] is not structural recursion,
  so we cannot define [iterate] as a Coq fixpoint and must use
  Noetherian recursion instead. *)

Definition iter_step (x: positive)
                     (next: forall y, Plt y x -> A -> option B)
                     (s: A) : option B :=
  match peq x xH with
  | left EQ => None
  | right NOTEQ =>
      match step s with
      | inl res => Some res
      | inr s'  => next (Pos.pred x) (Ppred_Plt x NOTEQ) s'
      end
  end.

Definition iter: positive -> A -> option B := Fix Plt_wf iter_step.

(** The [iterate] function is defined as [iter] up to
    [num_iterations] through the loop. *)

Definition iterate := iter num_iterations.

(** We now prove the invariance property [iterate_prop]. *)

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iter_prop:
  forall n a b, P a -> iter n a = Some b -> Q b.
Proof.
  apply (well_founded_ind Plt_wf
         (fun p => forall a b, P a -> iter p a = Some b -> Q b)).
  intros. unfold iter in H1. rewrite unroll_Fix in H1. unfold iter_step in H1.
  destruct (peq x 1). discriminate.
  specialize (step_prop a H0).
  destruct (step a) as [b'|a'] eqn:?.
  inv H1. auto.
  apply H with (Pos.pred x) a'. apply Ppred_Plt; auto. auto. auto.
Qed.

Lemma iterate_prop:
  forall a b, iterate a = Some b -> P a -> Q b.
Proof.
  intros. apply iter_prop with num_iterations a; assumption.
Qed.

End ITERATION.

End PrimIter.
