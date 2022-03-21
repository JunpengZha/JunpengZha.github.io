Require Import sflib. 

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Language.

Require Import Coqlib.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import MsgMapping.
Require Import DelaySet.
Require Import NPConfiguration.
Require Import NPBehavior.

(** * Whole program simulation *)

(** This file defines the whole program simulation (or global simulation) [glob_sim]
    between the target and source programs on the non-preemptive semantics *)

(** The theorem [glob_sim_implies_refinement] in this file
    shows that, if the whole target and source programs are simulated,
    they have refinement relation *)

(** The theorem [glob_sim_implies_refinement] in this file
    corresponds to the step 4 in Figure 3 (Our proof path) in our paper *)

CoInductive glob_sim_state: Ordering.LocOrdMap -> NPConfiguration.t -> NPConfiguration.t -> Prop :=
| glob_sim_state_intro
    lo npc_tgt npc_src
    (CUR_TID_EQ: (Configuration.tid (NPConfiguration.cfg npc_tgt)) = (Configuration.tid (NPConfiguration.cfg npc_src)))
    (TAU_STEP: 
       forall npc_tgt' 
              (TGT_TAU: NPConfiguration.step MachineEvent.silent lo npc_tgt npc_tgt'),
       exists npc_src',
         rtc (NPConfiguration.step MachineEvent.silent lo) npc_src npc_src' /\
         glob_sim_state lo npc_tgt' npc_src')
    (OUT_STEP: 
       forall npc_tgt' e
              (TGT_OUT: NPConfiguration.step (MachineEvent.syscall e) lo npc_tgt npc_tgt'),
       exists npc_src' npc_src'',
         rtc (NPConfiguration.step MachineEvent.silent lo) npc_src npc_src' /\
         NPConfiguration.step (MachineEvent.syscall e) lo npc_src' npc_src'' /\
         glob_sim_state lo npc_tgt' npc_src'')
    (SW_STEP: 
       forall npc_tgt'
              (TGT_SW: NPConfiguration.step MachineEvent.switch lo npc_tgt npc_tgt'),
       exists npc_src0 npc_src',
         rtc (NPConfiguration.step MachineEvent.silent lo) npc_src npc_src0 /\
         NPConfiguration.step MachineEvent.switch lo npc_src0 npc_src' /\
         glob_sim_state lo npc_tgt' npc_src')
    (DONE_STEP: 
       forall
         (TGT_DONE: NPConfiguration.is_done npc_tgt),
       exists npc_src',
         rtc (NPConfiguration.step MachineEvent.silent lo) npc_src npc_src' /\
         NPConfiguration.is_done npc_src')
    (ABORT_STEP: 
       forall
         (TGT_ABORT: NPConfiguration.is_abort npc_tgt lo),
       exists npc_src',
         rtc (NPConfiguration.step MachineEvent.silent lo) npc_src npc_src' /\
         NPConfiguration.is_abort npc_src' lo)
  :
    glob_sim_state lo npc_tgt npc_src.

(** ** Global simulation for whole program transition *)
Definition glob_sim (lang: language) (lo: Ordering.LocOrdMap) (fs: list Language.fid) (ctid: IdentMap.key)
       (code_t code_s: Language.syntax lang): Prop :=
  forall npc_tgt
         (TGT_INIT: NPConfiguration.init fs code_t ctid = Some npc_tgt),
  exists npc_src, NPConfiguration.init fs code_s ctid = Some npc_src /\
                  glob_sim_state lo npc_tgt npc_src.

(** ** Global simulation implies refinement proof *)
Lemma prefix_tau_np_behav_construct:
  forall n npc npc' lo n0 b
    (TAU_STEPS: rtcn (NPConfiguration.step MachineEvent.silent lo) n npc npc')
    (CONT_BEHAV: NPconf_behaviors npc' lo n0 b), 
  exists n', NPconf_behaviors npc lo n' b.
Proof.
  induction n; intros.
  - inv TAU_STEPS. eauto.
  - inv TAU_STEPS.
    eapply IHn in A23; eauto.
    destruct A23.
    exists (S x). eapply behaviors_tau; eauto.
Qed. 

Lemma sw_np_behav_construct:
  forall npc npc' lo b n
         (SW_STEP: NPConfiguration.step MachineEvent.switch lo npc npc')
         (CONT_BEHAV: NPconf_behaviors npc' lo n b),
    NPconf_behaviors npc lo (S n) b.
Proof.
  ii. econs; eauto.
Qed.

Lemma glob_sim_state_implies_refinement:
  forall n b
         (npc_tgt npc_src: NPConfiguration.t) (lo: Ordering.LocOrdMap)
         (TGT_BEHAV: NPconf_behaviors npc_tgt lo n b)
         (GLOB_SIM_STATE: glob_sim_state lo npc_tgt npc_src),
  exists n', NPconf_behaviors npc_src lo n' b.
Proof.
  induction n; intros.
  - inv TGT_BEHAV. exists 0%nat. econstructor; eauto.
  - inv GLOB_SIM_STATE.
    inv TGT_BEHAV.
    {
      (* abort *)
      clear TAU_STEP OUT_STEP SW_STEP DONE_STEP.
      eapply ABORT_STEP in IS_ABORT; eauto.
      clear - IS_ABORT.
      destruct IS_ABORT as (npc_src' & Htau_steps & His_abort).
      eapply rtc_rtcn in Htau_steps.
      destruct Htau_steps as (n & Htau_steps).
      eapply prefix_tau_np_behav_construct with (n0 := 1%nat); eauto.
      econstructor; eauto.
    }
    {
      (* done *)
      clear TAU_STEP OUT_STEP SW_STEP ABORT_STEP.
      eapply DONE_STEP in IS_DONE; eauto.
      clear - IS_DONE.
      destruct IS_DONE as (npc_src' & Htau_steps & His_done).
      eapply rtc_rtcn in Htau_steps.
      destruct Htau_steps as (n & Htau_steps).
      eapply prefix_tau_np_behav_construct with (n0 := 1%nat); eauto.
      econstructor; eauto.
    }
    {
      (* output *)
      clear TAU_STEP SW_STEP DONE_STEP ABORT_STEP.
      eapply OUT_STEP in STEP; eauto.
      destruct STEP as (npc_src' & npc_src'' & Htau_steps & Hout_step & Hglob_sim_state).
      eapply rtc_rtcn in Htau_steps.
      destruct Htau_steps as (n' & Htau_steps).
      eapply IHn in Hglob_sim_state; eauto.
      destruct Hglob_sim_state as (n'' & Hglob_sim_state). 
      eapply prefix_tau_np_behav_construct with (n0 := S n'') (npc' := npc_src'); eauto.
      eapply behaviors_out; eauto.
    }
    {
      (* tau or switch *)
      destruct STEP as [Htau_step | Hsw_step].
      {
        (* tau *)
        clear OUT_STEP SW_STEP DONE_STEP ABORT_STEP.
        eapply TAU_STEP in Htau_step; eauto.
        destruct Htau_step as (npc_src' & Htau_steps & Hglob_sim_state).
        eapply rtc_rtcn in Htau_steps.
        destruct Htau_steps as (n' & Htau_steps).
        eapply IHn in Hglob_sim_state; eauto.
        destruct Hglob_sim_state as (n'' & Hcont_behav).
        eapply prefix_tau_np_behav_construct with (n0 := n'') (npc' := npc_src'); eauto.
      }
      {
        (* switch *)
        clear TAU_STEP OUT_STEP DONE_STEP ABORT_STEP.
        eapply SW_STEP in Hsw_step; eauto.
        destruct Hsw_step as (npc_src' & Hsw_step & Hglob_sim_state).
        des.
        eapply IHn in Hglob_sim_state1; eauto.
        destruct Hglob_sim_state1 as (n' & Hcont_behav).
        exploit sw_np_behav_construct; eauto. ii.
        eapply rtc_rtcn in Hglob_sim_state. des.
        eapply prefix_tau_np_behav_construct; eauto.
      }
    }
Qed.
    
(** ** Global simulation implies refinement *)
Theorem glob_sim_implies_refinement
        (lang: language) (fs: list Language.fid) (code_t code_s: Language.syntax lang) (ctid: IdentMap.key)
        (lo: Ordering.LocOrdMap) (b: list VisibleEvent.t)
        (GLOB_SIM: glob_sim lang lo fs ctid code_t code_s)
        (TGT_BEHAV: NPprog_behaviors fs code_t ctid lo b):
  NPprog_behaviors fs code_s ctid lo b.
Proof.
  intros.
  inv TGT_BEHAV.
  unfold glob_sim in *.
  destruct H as (npc_tgt & H_tgt_init & H_tgt_behav).
  eapply GLOB_SIM in H_tgt_init; eauto.
  destruct H_tgt_init as (npc_src & H_src_init & H_src_behav).
  unfold NPprog_behaviors.
  eapply glob_sim_state_implies_refinement in H_src_behav; eauto.
  destruct H_src_behav as (n' & H_src_behav).
  exists n', npc_src.
  split; eauto.
Qed.
