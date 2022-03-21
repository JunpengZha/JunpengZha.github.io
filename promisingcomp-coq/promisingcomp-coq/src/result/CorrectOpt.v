Require Import sflib. 

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Language.

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import NPConfiguration.
Require Import ww_RF.
Require Import Behavior.
Require Import LocalSim.

Require Import LibTactics.

Require Import SemaEq.
Require Import wwRFEq.
Require Import Compositionality.
Require Import GlobSim.
Require Import NPBehavior.
Require Import wwRFPrsv.

Set Implicit Arguments.

(** * Framework Final Theorem *)

(** This file defines the final theorem of our framework (Theorem 6.4). *)

(** The main result (theorem [Verif_implies_Correctness] in this file) is that:
    a verified optimizer is a correct optimizer. *)

(** * Correctness of Optimizer *)
Section Correct_Optimizer.
  Variable lang: language.
  
  (** ** Type of optimizer *)
  Definition Optimizer :=
    forall (lo: Ordering.LocOrdMap) (code: Language.syntax lang), option (Language.syntax lang).
  
  (** ** Correctness of optimizer (Definition 6.3 in paper) *)
  (** An optimizer is correct if,

      for any optimization,
      if the source program is write-write race freedom [ww_rf] and safe [Configuration.safe],
      we have the refinement between the target program optimized and the source program,
      and the write-write race freedom and safety properties are preserved during optimization *)
  Definition Correct (optimizer: Optimizer) :=
    forall (code_s code_t: Language.syntax lang) fs lo ctid
           (OPTIMIZE: optimizer lo code_s = Some code_t)
           (WWRF_S: ww_rf lo fs code_s ctid)
           (SAFE_S: Configuration.safe lo fs code_s ctid),
      <<REFINE: evttr_refinement fs ctid lo code_t code_s prog_behaviors prog_behaviors>> /\
      <<WWRF_T: ww_rf lo fs code_t ctid>> /\ <<SAFE_T: Configuration.safe lo fs code_t ctid>>.

  (** ** Optimizers linking *)
  (** It contructs an optimizer with two optimization phases. *)
  (** opt_link (optimizer1, optimizer) (code_s) =
       let code_m := optimizer2(code_s) in optimizer1(code_m)   *)
  Definition opt_link (optimizer1 optimizer2: Optimizer) : Optimizer :=
    fun (lo: Ordering.LocOrdMap) (code_s: Language.syntax lang) =>
      match (optimizer2 lo code_s) with
      | Some code_m => optimizer1 lo code_m
      | None => None
      end.

  (** ** Correctness of optimizers linking *)
  Lemma correct_optimizer_transitive:
    forall (optimizer1 optimizer2: Optimizer)
      (CORRECT1: Correct(optimizer1))
      (CORRECT2: Correct(optimizer2)),
      Correct(opt_link optimizer1 optimizer2).
  Proof.
    intros; unfolds Correct; intros.
    unfold evttr_refinement in *.
    unfold opt_link in OPTIMIZE. destruct (optimizer2 lo code_s) eqn:H_OPTIMIZER2; simpls; tryfalse.
    eapply CORRECT2 in H_OPTIMIZER2; eauto.
    destruct H_OPTIMIZER2 as (Hrefine2 & Hww_rf2 & Hsafe2).
    eapply CORRECT1 in OPTIMIZE; eauto.
    destruct OPTIMIZE as (Hrefine1 & Hww_rf1 & Hsafe1).
    split; eauto.
  Qed.

  (** ** Verified optimizer: Definition 5.1 in paper *)
  (** An optimizer is verified if we can establish the thread-local simulation [local_sim]
      between the target and source programs *)
  Definition Verif (optimizer: Optimizer): Prop := 
    forall (code_s code_t: Language.syntax lang) (lo: Ordering.LocOrdMap),
        optimizer lo code_s = Some code_t -> 
          exists invariant index ord, 
            @local_sim index ord lang invariant lo code_t code_s.

  (** The following lemma [Verif_opt_implies_localsim]
      shows that for a verified optimizer,
      the source program and the target program optimized
      are simulated by the thread-local simulation.

      Lemma [Verif_opt_implies_localsim] corresponds to
      the step 2 in Figure 3 (Our proof path) in our paper *)
  Lemma Verif_opt_implies_localsim
        optimizer code_s code_t lo
        (VERIF: Verif optimizer)
        (OPT: optimizer lo code_s = Some code_t):
    exists invariant index ord,
      @local_sim index ord lang invariant lo code_t code_s.
  Proof.
    eauto.
  Qed.

  (** ** A verified optimizer is a correct optimizer (Theorem 6.4 in paper) *)
  Theorem Verif_implies_Correctness: 
    forall (optimizer: Optimizer),
      Verif optimizer -> Correct optimizer.
  Proof.
    ii. renames H to WF_OPT.
    eapply Verif_opt_implies_localsim in WF_OPT; eauto.
    renames WF_OPT to LOCAL_SIM. des.
    lets GLOB_SIM: LOCAL_SIM.
    eapply compositionality in GLOB_SIM; eauto.
    Focus 2. eapply config_safe_eq; eauto.
    Focus 2. eapply ww_RF_eq; eauto.
    split.
    {
      ii. eapply sema_eq_ps_nps in H.
      eapply sema_eq_ps_nps.
      eapply glob_sim_implies_refinement; eauto.
    }
    split.
    {
      lets WW_RF: LOCAL_SIM.
      eapply ww_RF_preservation in WW_RF.
      eapply ww_RF_eq; eauto.
      eapply config_safe_eq; eauto.
      eapply ww_RF_eq; eauto.
    }
    {
      lets SAFE_S': SAFE_S.
      eapply safe_implies_not_abort_tr in SAFE_S'.
      eapply not_abort_tr_implies_safe. ii; des.
      contradiction SAFE_S'.
      eapply sema_eq_ps_nps in H.
      eapply glob_sim_implies_refinement in GLOB_SIM; eauto.
      eapply sema_eq_ps_nps in GLOB_SIM; eauto.
    }
  Qed.

End Correct_Optimizer.
