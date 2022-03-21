Require Import sflib.
From Paco Require Import paco.

Require Import Basic.
Require Import Loc.

Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import NPConfiguration.

Set Implicit Arguments.

(** * The behaviors of a program on the non-preemptive semantics *)

(** This file defines the behaviors of the program in the non-preemptive semantics. *)
(** The behaviors of a programs are defined as a set of observable events. *)

(** ** Observable event trace. *)

Inductive NPconf_behaviors: forall (c: NPConfiguration.t) (lo: Ordering.LocOrdMap) (n: nat) (b: list VisibleEvent.t), Prop := 
  | behaviors_nil
      c lo :
      NPconf_behaviors c lo 0 nil
  | behaviors_abort
      c lo n
      (IS_ABORT: NPConfiguration.is_abort c lo)
    :
      NPconf_behaviors c lo (S n) (VisibleEvent.abort::nil)
  | behaviors_done 
      c lo n
      (IS_DONE: NPConfiguration.is_done c)
    :
      NPconf_behaviors c lo (S n) (VisibleEvent.done::nil)
  | behaviors_out
      c c' lo n e behs
      (STEP: NPConfiguration.step (MachineEvent.syscall e) lo c c')
      (BEHS: NPconf_behaviors c' lo n behs)
    :
      NPconf_behaviors c lo (S n) (VisibleEvent.out e :: behs)
  | behaviors_tau 
      c c' lo n behs 
      (STEP: NPConfiguration.step (MachineEvent.silent) lo c c' \/ 
             NPConfiguration.step (MachineEvent.switch) lo c c') 
      (BEHS: NPconf_behaviors c' lo n behs)
    :
      NPconf_behaviors c lo (S n) behs
.

(** ** Program behaviors of programs in the non-preemptive semantics *)
Definition NPprog_behaviors {lang: language} (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key)
           (lo: Ordering.LocOrdMap) (b: list VisibleEvent.t) : Prop :=
  exists n npc, NPConfiguration.init fs code ctid = Some npc /\  NPconf_behaviors npc lo n b.

Lemma NPconf_behav_sw
      c lo n behs tid
      (NP_BEH: NPconf_behaviors (NPConfiguration.mk c true) lo n behs):
  exists n', NPconf_behaviors (NPConfiguration.mk (Configuration.sw_tid c tid) true) lo n' behs.
Proof.
  inv NP_BEH.
  - exists 0%nat. econs; eauto.
  - dup IS_ABORT.
    inv IS_ABORT0; ss. des; subst; ss.
    exists 2%nat.
    eapply behaviors_tau. right. econs; eauto.
    ss. econs; eauto. destruct c; ss.
  - dup IS_DONE.
    inv IS_DONE0; ss. des; subst; ss.
    exists 2%nat.
    eapply behaviors_tau. right. econs; eauto.
    ss. econs; eauto.
  - dup STEP.
    inv STEP; ss.
    exists (S (S n0))%nat.
    eapply behaviors_tau. right. econs; eauto.
    ss. destruct c; ss. econs; eauto.
  - des.
    + dup STEP.
      inv STEP0; ss.
      exists (S (S n0)).
      eapply behaviors_tau. right. econs; eauto.
      ss. destruct c; ss. econs; eauto.
    + dup STEP.
      inv STEP0; ss.
      {
        exists (S n0).
        eapply behaviors_tau. right. econs; eauto.
        ss.
      }
      {
        exists (S (S n0)).
        eapply behaviors_tau. right. econs; eauto.
        ss.
        eapply behaviors_tau. right.
        eapply NPConfiguration.step_thread_term; eauto.
        ss. eauto. ss.
      }
Qed.
