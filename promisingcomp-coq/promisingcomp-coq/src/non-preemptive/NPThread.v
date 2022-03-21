Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Language.

(** * Thread step in the non-preemptive semantics *)

(** This file define the thread step in the non-preemptive semantics (in Figure 7 in paper). *)
  
Module NPAuxThread.
    Section NPAuxThread.
        Variable (lang: language).

        (** Thread state in the non-preemptive semantics. It includes:
            - The thread state [state] in PS2.1, including
              thread-local state, thread view and promise set;
            - A 'switch bit' [preempt] indicate whether a switch step is allowed
              + [preempt = true]: a switch step is allowed
              + [preempt = false]: a switch step is disallowed *)
        Structure t := mk {
            state: (Thread.t lang);
            preempt: bool;
        }. 

        (** After non-atomic step, the switch step is disallowed [preempt = false]  *)
        Definition na_step (lo: Ordering.LocOrdMap) (e1 e2:t): Prop :=
          Thread.na_step lo (state e1) (state e2) /\ (preempt e2 = false).

        (** After atomic step, the switch step is allowed [preempt = true]  *)
        Definition at_step (lo: Ordering.LocOrdMap) (e1 e2:t): Prop := 
          Thread.at_step lo (state e1) (state e2) /\ (preempt e2 = true). 

        (** After output step, the switch step is allowed [preempt = true]  *)
        Definition out_step (lo: Ordering.LocOrdMap) (e: Event.t) (e1 e2:t): Prop := 
          Thread.out_step lo e (state e1) (state e2) /\ (preempt e2 = true). 

        (** The promise/reservation and cancel steps are only permitted to occur when [preempt = true] *)
        (** In our paper, for simply preservation, we weakened the non-preemptive semantics definition
            but it does not influence our result,
            and allowed the cancel step to take when [preempt = false] *)
        Definition prc_step (lo: Ordering.LocOrdMap) (e1 e2:t): Prop :=
          Thread.prc_step lo (state e1) (state e2) /\ (preempt e1 = true) /\ (preempt e2 = true).

        Definition tau_step (lo: Ordering.LocOrdMap) (e1 e2:t): Prop :=
          na_step lo e1 e2 \/ at_step lo e1 e2 \/ prc_step lo e1 e2.

        Definition consistent := Thread.consistent_nprm.

        Definition all_step (lo: Ordering.LocOrdMap) (e1 e2:t): Prop :=
          tau_step lo e1 e2 \/ (exists e, out_step lo e e1 e2). 

    End NPAuxThread.
End NPAuxThread.
