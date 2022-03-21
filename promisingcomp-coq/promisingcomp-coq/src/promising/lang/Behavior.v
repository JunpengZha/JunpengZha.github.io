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
Require Import Omega.

Set Implicit Arguments.

(** * Program behaviors in promising semantics *)

(** This file defines the behaviors of the program in promising semantics. *)
(** The behaviors of a programs are defined as a set of observable events *)

(** ** Observable event trace *)
(* Event trace (list VisibleEvent.t) is a list of observable event.
   The observable event trace (defined as (EvtTrace) in Figure 5 in paper) includes:
   - empty observable event;
   - program abort;
   - program done;
   - output event (system call) *)
Inductive conf_behaviors: forall (c: Configuration.t) (lo: Ordering.LocOrdMap) (n: nat) (b: list VisibleEvent.t), Prop := 
  | behaviors_nil
      c lo :
      conf_behaviors c lo 0 nil
  | behaviors_abort
      c lo n
      (IS_ABORT: Configuration.is_abort c lo)
    :
      conf_behaviors c lo (S n) (VisibleEvent.abort::nil)  (* not append, change trace to single `abort` event*)
  | behaviors_done 
      c lo n
      (IS_DONE: Configuration.is_done c)
    :
      conf_behaviors c lo (S n) (VisibleEvent.done::nil)
  | behaviors_out
      c c' lo n e behs
      (STEP: Configuration.step (MachineEvent.syscall e) lo c c')
      (BEHS: conf_behaviors c' lo n behs)
    :
      conf_behaviors c lo (S n) (VisibleEvent.out e :: behs)
  | behaviors_tau 
      c c' lo n e behs 
      (EVENT: ~(exists e0, e = MachineEvent.syscall e0))
      (STEP: Configuration.step e lo c c') 
      (BEHS: conf_behaviors c' lo n behs)
    :
      conf_behaviors c lo (S n) behs
.
Hint Constructors conf_behaviors.

(** ** Program behavior in promising semantics *)
Definition prog_behaviors {lang: language} (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key)
           (lo: Ordering.LocOrdMap) (b: list VisibleEvent.t) : Prop :=
  exists n c, Configuration.init fs code ctid = Some c /\ conf_behaviors c lo n b.

(** ** Event trace refinement *)
Definition evttr_refinement {lang: language}
           (fs: list Language.fid) (ctid: IdentMap.key) (lo: Ordering.LocOrdMap)
           (code_t: Language.syntax lang) (code_s: Language.syntax lang)
           (behs_t: list Language.fid -> Language.syntax lang -> IdentMap.key ->
                    Ordering.LocOrdMap -> list VisibleEvent.t -> Prop)
           (behs_s: list Language.fid -> Language.syntax lang -> IdentMap.key ->
                    Ordering.LocOrdMap -> list VisibleEvent.t -> Prop) : Prop:=
  forall b, behs_t fs code_t ctid lo b -> behs_s fs code_s ctid lo b.

(** ** Event trace equivalence *)
Definition evttr_equivalence {lang: language}
           (fs: list Language.fid) (ctid: IdentMap.key) (lo: Ordering.LocOrdMap)
           (code_t: Language.syntax lang) (code_s: Language.syntax lang)
           (behs_t: list Language.fid -> Language.syntax lang -> IdentMap.key ->
                    Ordering.LocOrdMap -> list VisibleEvent.t -> Prop)
           (behs_s: list Language.fid -> Language.syntax lang -> IdentMap.key ->
                    Ordering.LocOrdMap -> list VisibleEvent.t -> Prop) : Prop:=
  forall b, behs_t fs code_t ctid lo b <-> behs_s fs code_s ctid lo b.  

Inductive aux_conf_behaviors: forall (c: Configuration.t) (lo: Ordering.LocOrdMap) (n: nat) (b: list VisibleEvent.t), Prop := 
  | aux_behaviors_nil
      c lo :
      aux_conf_behaviors c lo 0 nil
  | aux_behaviors_abort
      c lo n
      (IS_ABORT: Configuration.is_abort c lo)
    :
      aux_conf_behaviors c lo (S n) (VisibleEvent.abort::nil)  (* not append, change trace to single `abort` event*)
  | aux_bahaviors_done 
      c lo n
      (IS_DONE: Configuration.is_done c)
    :
      aux_conf_behaviors c lo (S n) (VisibleEvent.done::nil)
  | aux_behaviors_out
      c c' lo n e behs
      (STEP: Configuration.aux_step (AuxEvent.out e) lo c c')
      (BEHS: aux_conf_behaviors c' lo n behs)
    :
      aux_conf_behaviors c lo (S n) (VisibleEvent.out e :: behs)
  | aux_behaviors_tau
      c c' npe lo n behs 
      (EVENT: ~(exists e, npe = AuxEvent.out e))
      (STEP: Configuration.aux_step npe lo c c') 
      (BEHS: aux_conf_behaviors c' lo n behs)
    :
      aux_conf_behaviors c lo (S n) behs
.
Hint Constructors aux_conf_behaviors.

Definition aux_prog_behaviors {lang: language} (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key)
           (lo: Ordering.LocOrdMap) (b: list VisibleEvent.t) : Prop :=
  exists n c, Configuration.init fs code ctid = Some c /\ aux_conf_behaviors c lo n b.

Lemma rtcn_tail:
  forall A R n 
  (a1 a3:A)
  (REL: rtcn R (S n) a1 a3),
  (exists a2, rtcn R n a1 a2 /\ R a2 a3).
Proof.
  induction n.
  - intros. exists a1. splits; eauto.
    inv REL. inv A23; eauto. 
  - intros. inv REL.
    eapply IHn in A23.
    destruct A23 as (a2' & STEPS). 
    exists a2'. splits; destruct STEPS as (STEPS & FSTEP); eauto.
Qed.

Lemma tau_steps_aux_behaviors: 
  forall ape lo n1 c1 c2 n2 behs 
  (EVENT: ~(exists e, ape = AuxEvent.out e))
  (STEPS: rtcn (Configuration.aux_step ape lo) n1 c1 c2) 
  (BEHS: aux_conf_behaviors c2 lo n2 behs),
  aux_conf_behaviors c1 lo (n1+n2) behs.
Proof.
  induction n1. 
  - intros. simpls. inv STEPS; eauto.
  - intros. eapply rtcn_tail in STEPS. destruct STEPS as (c' & STEPS & STEP).
    eapply aux_behaviors_tau in STEP; eauto.
    eapply IHn1 in STEPS; eauto.  
    replace (n1 + S n2) with (S n1 + n2) in STEPS by omega; eauto.
Qed.

Lemma tau_steps_aux_behaviors': 
  forall lo n1 c1 c2 n2 behs 
  (STEPS: rtcn (Configuration.aux_tau_step lo) n1 c1 c2) 
  (BEHS: aux_conf_behaviors c2 lo n2 behs),
  aux_conf_behaviors c1 lo (n1+n2) behs.
Proof.
  induction n1. 
  - intros. simpls. inv STEPS; eauto.
  - intros. eapply rtcn_tail in STEPS. destruct STEPS as (c' & STEPS & STEP).
    inv STEP. 
    eapply aux_behaviors_tau in WP_STEP; eauto.
    eapply IHn1 in STEPS; eauto.  
    replace (n1 + S n2) with (S n1 + n2) in STEPS by omega. 
    eauto.
Qed.

Lemma tau_steps_behaviors: 
  forall e lo n1 c1 c2 n2 behs 
  (EVENT: ~(exists e0, e = MachineEvent.syscall e0))
  (STEPS: rtcn (Configuration.step e lo) n1 c1 c2) 
  (BEHS: conf_behaviors c2 lo n2 behs),
  conf_behaviors c1 lo (n1+n2) behs.
Proof.
  induction n1. 
  - intros. simpls. inv STEPS; eauto.
  - intros. eapply rtcn_tail in STEPS. destruct STEPS as (c' & STEPS & STEP).
    eapply behaviors_tau in STEP; eauto.
    eapply IHn1 in STEPS; eauto.  
    replace (n1 + S n2) with (S n1 + n2) in STEPS by omega; eauto.
Qed.

Lemma tau_steps_behaviors': 
  forall lo n1 c1 c2 n2 behs 
  (STEPS: rtcn (Configuration.tau_step lo) n1 c1 c2) 
  (BEHS: conf_behaviors c2 lo n2 behs),
  conf_behaviors c1 lo (n1+n2) behs.
Proof.
  induction n1. 
  - intros. simpls. inv STEPS; eauto.
  - intros. eapply rtcn_tail in STEPS. destruct STEPS as (c' & STEPS & STEP).
    inv STEP.
    eapply behaviors_tau in WP_STEP; eauto.
    eapply IHn1 in STEPS; eauto.  
    replace (n1 + S n2) with (S n1 + n2) in STEPS by omega; eauto.
Qed.

Inductive prefix_behs: list VisibleEvent.t -> Prop :=
| prefix_behs_nil:
  prefix_behs nil
| prefix_behs_cons
    behs e
    (PREFIX: prefix_behs behs):
  prefix_behs ((VisibleEvent.out e) :: behs). 
