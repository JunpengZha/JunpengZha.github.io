Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import DenseOrder.
Require Import List. 

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import MsgMapping.
Require Import LibTactics.
Require Import Local.

Require Import Language.
Require Import Thread.
Require Import NPThread.
Require Import ps_to_np_thread.

(** * Delayed write set *)

(** This file defines the delayed write set and
    some operations about the delayed write set (definitions in Figure 9 in paper). *)

(** [DelaySet] in this file is the definition of the delayed write set.
    The delayed write set is a partial mapping from the delayed items to indexes.
    In our paper, the delayed item is either a message (a promise has been fulfilled) or a location (has been written).
    However, in the coq implement, we unify the categories of the delayed item to a pair of location and timestamp
    and simply the presentation.
    A pair of location x and timestamp t presents a write on location x at timestamp t.  *)


Fixpoint union_DOMap' {A: Type} (elements: list (DOMap.Raw.key * A)) (dm: DOMap.t A): DOMap.t A :=
  match elements with
  | (key, t) :: elements => union_DOMap' elements (DOMap.add key t dm)
  | nil => dm
  end.

Definition union_DOMap {A: Type} (dm1 dm2: DOMap.t A): DOMap.t A :=
  let elements := DOMap.elements dm1 in
  union_DOMap' elements dm2.

Lemma DOMap_element_no_dup:
  forall A (dm: DOMap.t A) key t t'
         (IN_ELEMENTS1: In (key, t) (DOMap.elements dm))
         (IN_ELEMENTS2: In (key, t') (DOMap.elements dm)),
    t = t'.
Proof.
  intros.
  eapply DOMap.elements_complete in IN_ELEMENTS1; eauto.
  eapply DOMap.elements_complete in IN_ELEMENTS2; eauto.
  rewrite IN_ELEMENTS1 in IN_ELEMENTS2; eauto. inversion IN_ELEMENTS2; eauto.
Qed.

Lemma union_DOMap_proper':
  forall A elements (dm: DOMap.t A) key t
         (IN_UNION: DOMap.find key (union_DOMap' elements dm) = Some t),
    In (key, t) elements \/ DOMap.find key dm = Some t.
Proof.
  intros A elements; induction elements; intros; simpls; eauto.
  destruct a; simpls.
  eapply IHelements in IN_UNION; eauto.
  destruct IN_UNION as [IN_UNION | IN_UNION]; eauto.
  destruct (Ident.eq_dec key k) eqn:Heqe; subst.
  rewrite DOMap.gss in IN_UNION; inv IN_UNION; eauto.
  rewrite DOMap.gso in IN_UNION; eauto.
Qed.

Lemma union_DOMap_proper_none':
  forall A elements (dm: DOMap.t A) key
         (IN_UNION: DOMap.find key (union_DOMap' elements dm) = None),
    ~(exists t, In (key, t) elements) /\ DOMap.find key dm = None.
Proof.
  intros A elements; induction elements; intros; simpls; eauto.
  split; eauto. ii; des. ss.
  destruct a; ss.
  eapply IHelements in IN_UNION; eauto. des.
  split; eauto.
  ii.
  contradiction IN_UNION. des; eauto.
  inv H.
  rewrite DOMap.gss in IN_UNION0. ss.
  destruct (Loc.eq_dec key k); subst.
  rewrite DOMap.gss in IN_UNION0. ss.
  rewrite DOMap.gso in IN_UNION0; eauto.
Qed.

Lemma union_DOMap_proper:
  forall A (dm1 dm2: DOMap.t A) key t
         (IN_UNION: DOMap.find key (union_DOMap dm1 dm2) = Some t),
    (DOMap.find key dm1 = Some t) \/ (DOMap.find key dm2 = Some t).
Proof.
  intros.
  unfold union_DOMap in IN_UNION.
  eapply union_DOMap_proper' in IN_UNION; eauto.
  destruct IN_UNION as [IN_UNION | IN_UNION]; eauto.
  eapply DOMap.elements_complete in IN_UNION; eauto.
Qed.

Lemma union_DOMap_proper_none:
  forall A (dm1 dm2: DOMap.t A) key
         (IN_UNION: DOMap.find key (union_DOMap dm1 dm2) = None),
    DOMap.find key dm1 = None /\ DOMap.find key dm2 = None.
Proof.
  intros.
  unfold union_DOMap in IN_UNION.
  exploit union_DOMap_proper_none'; [eapply IN_UNION | eauto..].
  ii; des.
  split; eauto.
  destruct (DOMap.find key dm1) eqn:GET; eauto.
  contradiction x0.
  eapply DOMap.elements_correct in GET.
  eauto.
Qed.

Section DELAYSET.

  (** ** Delayed write set *)
  (** Delayed write set records the messages in the target memory that the source thread
      has not generate the corresponding messages. *)
  (** We use a pair of location and timestamp to represent a delayed write. *)
  Definition DelaySet {index: Type} := Loc.t -> (DOMap.t index).

  (** ** dset initialize *)
  Definition dset_init {index: Type} := fun (loc: Loc.t) => DOMap.empty index.

  (** ** delayed write set: get method *)
  Definition dset_get {index: Type}
             (loc: Loc.t) (t: Time.t) (dset: @DelaySet index) :=
    DOMap.find t (dset loc). 

  (** ** delayed write set: add method *)
  Definition dset_add {index: Type}
             (loc: Loc.t) (t: Time.t) (i: index) (dset: @DelaySet index) :=
    fun (loc': Loc.t) =>
      if Loc.eq_dec loc loc' then
        if DOMap.mem t (dset loc) then (dset loc) else DOMap.add t i (dset loc)
      else (dset loc').

  (** ** delayed write set: remove method *)
  Definition dset_remove {index: Type}
             (loc: Loc.t) (t: Time.t) (dset: @DelaySet index) :=
    fun (loc': Loc.t) =>
      if Loc.eq_dec loc loc' then
        DOMap.remove t (dset loc')
      else (dset loc').

  (** ** disjoint delayed write set *)
  Inductive dset_disjoint {index: Type} (dset1 dset2: @DelaySet index): Prop :=
  | dset_disjoint_intro
      (DISJOINT: forall loc t d,
          dset_get loc t dset1 = Some d -> dset_get loc t dset2 = None).

  (** ** union delayed write set *)
  Definition union_dset {index: Type} (dset1 dset2: @DelaySet index): @DelaySet index :=
    fun (loc: Loc.t) => union_DOMap (dset1 loc) (dset2 loc).

  (** ** location in delayed write set *)
  Definition loc_in_dset {index: Type} (loc: Loc.t) (dset: @DelaySet index) :=
    exists i t, dset_get loc t dset = Some i.

  (** ** empty delayed write set *)
  Definition empty_dset {index: Type} (dset: @DelaySet index) :=
    forall loc, DOMap.is_empty (dset loc).

  (** ** reducing delayed write set *)
  Inductive reduce_dset {index: Type} (index_order: index -> index -> Prop)
            (dset1 dset2: @DelaySet index) :=
  | reduce_dset_intro
      (REDUCE: forall loc t i,
          dset_get loc t dset1 = Some i ->
          (exists j, index_order i j /\ dset_get loc t dset2 = Some j))
      (COMPLETE: forall loc t j,
          dset_get loc t dset2 = Some j ->
          exists i, dset_get loc t dset1 = Some i).
 
  (** ** dset subset *)
  Definition dset_subset {index: Type} (pdset dset: @DelaySet index) :=
    forall loc t i, dset_get loc t pdset = Some i -> dset_get loc t dset = Some i.

  (** ** the delay set becoming after na step *)
  Inductive dset_after_na_step {index: Type}
            (te: ThreadEvent.t) (dset dset': @DelaySet index): Prop :=
  | dset_become_na_write
      loc f t val R i lo
      (NA_WRITE: te = ThreadEvent.write loc f t val R lo)
      (DSET_INCR: dset_add loc t i dset = dset')
  | dset_become_na_read
      (NOT_NA_WRITE: ~(ThreadEvent.is_writing te))
      (DSET_EQ: dset = dset').

  (* little dset *) 
  Inductive lt_dset {index: Type} (index_order: index -> index -> Prop):
    list (option (Loc.t * Time.t * index)) ->
    list (Loc.t * Time.t * index) -> Prop :=
  | lt_dset_some:
      forall loc t j i ols ls
        (LT: index_order j i)
        (LT_DSET: lt_dset index_order ols ls),
        lt_dset index_order (Some (loc, t, j) :: ols) ((loc, t, i) :: ls)
  | lt_dset_none:
      forall loc t i ols ls
        (LT_DSET: lt_dset index_order ols ls),
        lt_dset index_order (None :: ols) ((loc, t, i) :: ls)
  | lt_dset_some_nil:
      forall loc t j i
        (LT: index_order j i),
        lt_dset index_order (Some (loc, t, j) :: nil) ((loc, t, i) :: nil)
  | lt_dset_none_nil:
      forall loc t i,
        lt_dset index_order (None :: nil) ((loc, t, i) :: nil).

  Fixpoint remove_none {A: Type} (ls: list (option A)) :=
    match ls with
    | nil => nil
    | (Some a) :: ls' => a :: remove_none ls'
    | None :: ls' => remove_none ls'
    end.

  Inductive Acc_lt_dset {index: Type} (index_order: index -> index -> Prop)
            (ls: list (Loc.t * Time.t * index)): Prop :=
  | Acc_lt_dset_intro
      (Acc_Prsv: forall ols ls', lt_dset index_order ols ls ->
                            remove_none ols = ls' -> ls' <> nil ->
                            Acc_lt_dset index_order ls').

  Lemma Acc_lt_dset_single
        index (index_order: index -> index -> Prop) loc t i
        (WELL_FOUND: well_founded index_order):
    Acc_lt_dset index_order [(loc, t, i)].
  Proof.
    unfold well_founded in *.
    specialize (WELL_FOUND i).
    generalize dependent loc.
    generalize dependent t.
    induction WELL_FOUND. ii.
    econs; eauto. ii.
    inv H1; ss.
    - inv LT_DSET.
    - inv LT_DSET.
    - eauto.
  Qed.

  Lemma Acc_lt_dset_remove_prsv
        index (index_order: index -> index -> Prop) ols ls
        (LT_DSET: lt_dset index_order ols ls)
        (ACC_LT_DSET: Acc_lt_dset index_order ls):
    Acc_lt_dset index_order (remove_none ols).
  Proof.
    generalize dependent ols.
    induction ACC_LT_DSET; ii; eauto.
    destruct (remove_none ols) eqn:REMOVE.
    - econs. ii. inv H0.
    - eapply Acc_Prsv in LT_DSET; eauto. ii; ss.
  Qed.
                          
  Lemma well_founded_index_additional0:
    forall index (index_order: index -> index -> Prop) ls loc t i
      (WELL_FOUND: well_founded index_order)
      (ACC_LE_DSET: Acc_lt_dset index_order ls),
      Acc_lt_dset index_order ((loc, t, i) :: ls).
  Proof.
    ii. lets WELL_FOUND': WELL_FOUND.
    unfold well_founded in WELL_FOUND.
    specialize (WELL_FOUND i).
    generalize dependent ls.
    generalize dependent loc.
    generalize dependent t.
    induction WELL_FOUND. ii.
    econs; ii. inv H1; ss.
    - inv ACC_LE_DSET.
      destruct (remove_none ols0) eqn:REMOVE; ss.
      eapply Acc_lt_dset_single; eauto. 
      exploit Acc_Prsv; [eapply LT_DSET | eauto..].
      ii; tryfalse.
    - eapply Acc_lt_dset_remove_prsv; eauto.
    - eapply Acc_lt_dset_single; eauto.
  Qed.

  Lemma well_founded_index_additional1:
    forall index (index_order: index -> index -> Prop) ols ls loc t i
      (WELL_FOUND: well_founded index_order)
      (LT_DSET: lt_dset index_order ols ls)
      (ACC_LT_DSET: Acc_lt_dset index_order ls),
      Acc_lt_dset index_order
                  ((loc, t, i) :: remove_none ols).
  Proof.
    ii.
    generalize dependent ols.
    generalize dependent loc.
    generalize dependent t.
    generalize dependent i.
    induction ACC_LT_DSET. ii; eauto.
    destruct (remove_none ols) eqn:REMOVE_NONE.
    - eapply Acc_lt_dset_single; eauto.
    - specialize (H ols (remove_none ols)).
      eapply Acc_Prsv with (ls' := remove_none ols) in LT_DSET; eauto.
      2: rewrite REMOVE_NONE; ss; ii; tryfalse.
      rewrite <- REMOVE_NONE.
      eapply well_founded_index_additional0; eauto.
  Qed.

  Lemma well_founded_index_implies_Acc_lt_dset:
    forall n index (index_order: index -> index -> Prop) ls
      (WELL_FOUND: well_founded index_order)
      (LS_LEN: n = length ls),
      Acc_lt_dset index_order ls.
  Proof.
    induction n; ii.
    - econs; ii. 
      inv H; ss; tryfalse.
    - econs; ii.
      inv H; ss; eauto.
      + inv LS_LEN.
        exploit IHn; eauto. ii.
        eapply well_founded_index_additional1; eauto.
      + inv LS_LEN.
        exploit IHn; eauto. ii.
        eapply Acc_lt_dset_remove_prsv; eauto.
      + eapply Acc_lt_dset_single; eauto.
  Qed.

  Lemma dset_get_gss
        index loc t i (dset: @DelaySet index):
    exists j, dset_get loc t (dset_add loc t i dset) = Some j.
  Proof.
    unfold dset_get, dset_add; ss.
    des_if; ss.
    destruct (DOMap.mem t (dset loc)) eqn:MEM; eauto.
    rewrite DOMap.mem_find in MEM.
    destruct (DOMap.find t (dset loc)) eqn:FIND; eauto; ss.
    rewrite DOMap.gss; eauto.
  Qed.

  Lemma dset_get_union
        index loc t i (dset1 dset2: @DelaySet index)
        (GET_UNION: dset_get loc t (union_dset dset1 dset2) = Some i):
    dset_get loc t dset1 = Some i \/ dset_get loc t dset2 = Some i.
  Proof.
    unfold dset_get, union_dset in *.
    eapply union_DOMap_proper; eauto.
  Qed.

  Lemma dset_union_init:
    forall index (dset: @DelaySet index),
      dset = union_dset dset dset_init.
  Proof.
    ii. eapply functional_extensionality_dep. ii.
    eapply DOMap.eq_leibniz.
    unfold DOMap.Equal. ii.
    destruct (DOMap.find y (union_dset dset dset_init x)) eqn:Heqe.
    {
      eapply union_DOMap_proper in Heqe. des; eauto.
      unfold dset_init in *; ss. rewrite DOMap.gempty in Heqe. ss.
    }
    {
      eapply union_DOMap_proper_none in Heqe. des; eauto.
    }
  Qed.

  Lemma dset_get_add1
        index loc t i j (dset: @DelaySet index) loc0 t0
        (GET: dset_get loc t dset = Some i):
    dset_get loc t (dset_add loc0 t0 j dset) = Some i.
  Proof.
    unfold dset_get, dset_add in *.
    des_if; ss; subst.
    destruct (DOMap.mem t0 (dset loc)) eqn: MEM; eauto.
    rewrite DOMap.mem_find in MEM.
    destruct (DOMap.find t0 (dset loc)) eqn:DSET_FIND; eauto; ss.
    destruct (Time.eq_dec t t0); subst; eauto.
    rewrite GET in DSET_FIND. ss.
    rewrite DOMap.gso; eauto.
  Qed.

  Lemma dset_get_proper
        index loc t i (dset: @DelaySet index) loc0 t0 i0
        (GET: dset_get loc t (dset_add loc0 t0 i0 dset) = Some i):
    dset_get loc t dset = None \/ dset_get loc t dset = Some i.
  Proof.
    unfold dset_get, dset_add in *; ss.
    des_ifH GET; ss; subst; ss.
    destruct (DOMap.mem t0 (dset loc)) eqn:Heqe; eauto.
    destruct (Time.eq_dec t t0); subst; ss.
    rewrite DOMap.mem_find in Heqe.
    destruct (DOMap.find t0 (dset loc)) eqn:Heqe'; ss. eauto.
    rewrite DOMap.gso in GET; eauto.
    eauto.
  Qed.

  Lemma dset_get_remove
        index loc t i (dset: @DelaySet index) loc0 t0
        (GET_REMOVE: dset_get loc t (dset_remove loc0 t0 dset) = Some i):
    dset_get loc t dset = Some i.
  Proof.
    unfold dset_get, dset_remove in *; ss.
    des_ifH GET_REMOVE; subst; ss.
    destruct (Time.eq_dec t t0); subst.
    rewrite DOMap.grs in GET_REMOVE. ss.
    erewrite DOMap.gro in GET_REMOVE; eauto.
  Qed.

  Lemma dset_after_na_step_origin_prsv
        index (dset dset': @DelaySet index) e loc t i
        (AFTER_NA: dset_after_na_step e dset dset')
        (IN: dset_get loc t dset = Some i):
    dset_get loc t dset' = Some i.
  Proof.
    inv AFTER_NA; eauto.
    eapply dset_get_add1; eauto.
  Qed.

  Lemma dset_reduce
        index index_order (dset dset': @DelaySet index) loc t i
        (REDUCE: reduce_dset index_order dset' dset)
        (IN: dset_get loc t dset = Some i):
    exists j, dset_get loc t dset' = Some j /\ index_order j i.
  Proof.
    inv REDUCE. exploit COMPLETE; eauto.
    ii; des. exploit REDUCE0; eauto. ii; des; eauto.
    rewrite IN in x1. inv x1. eauto.
  Qed.

  Lemma init_dset_subset: 
    forall index (dset: @DelaySet index), 
      dset_subset dset_init dset.
  Proof.
    intros.
    unfolds dset_subset. intros.
    unfolds dset_get. unfolds dset_init. 
    pose proof (DOMap.gempty index t). 
    rewrite H in H0. discriminate. 
  Qed.

  Lemma dset_gempty:
    forall index loc t, 
      (@dset_get index) loc t dset_init = None.
  Proof.
    intros.
    unfolds dset_get; unfolds dset_init.
    eapply (DOMap.gempty index t).
  Qed. 

  Lemma loc_in_init_dset_false: 
    forall index loc, 
    (@loc_in_dset index) loc dset_init -> False.
  Proof.
    intros.
    unfolds loc_in_dset. destruct H as (a & b & c).
    rewrite dset_gempty in c. discriminate.
  Qed.

  Lemma dset_disjoint_init:                         
    forall index (dset: @DelaySet index), 
      dset_disjoint dset dset_init.
  Proof.
    intros.
    eapply dset_disjoint_intro.
    intros.
    rewrite dset_gempty. 
    trivial.
  Qed.

  Lemma dset_reduce_init: 
    forall index index_order,
    @reduce_dset index index_order dset_init dset_init.
  Proof.
    intros.
    eapply reduce_dset_intro.
    intros.
    rewrite dset_gempty in H. discriminate.
    intros. 
    rewrite dset_gempty in H. discriminate.
  Qed. 

  Lemma dset_remove_add:
    forall index loc to (i: index),
      dset_remove loc to (dset_add loc to i dset_init) = dset_init.
  Proof.
    ii. eapply functional_extensionality_dep. ii. ss.
    unfold dset_remove, dset_add; ss.
    des_if; ss; subst.
    destruct (DOMap.mem to (dset_init x)) eqn:Heqe.
    - unfold dset_init in Heqe. rewrite DOMap.mem_find in Heqe.
      destruct (DOMap.find to (DOMap.empty index)) eqn:Heqe'; ss.
      rewrite DOMap.gempty in Heqe'. ss.
    - eapply DOMap.eq_leibniz. ii.
      unfold dset_init; ss.
      rewrite DOMap.gempty.
      destruct (DOMap.Properties.F.eq_dec y to); subst.
      rewrite DOMap.grs. ss.
      rewrite DOMap.gro; ss. rewrite DOMap.gso; eauto.
      rewrite DOMap.gempty; ss.
  Qed.
    
End DELAYSET.

(** ** Auxiliary thread step **)
(** The definition [na_step_dset] encapsulates
    - thread step of the source thread;
    - modification of the delayed write set by the source thread step;
    - restriction for memory reads, if such memory read reads a location recorded in the delayed write set

    If a memory read wants to read a location that is recorded in the delayed write set,
    it forbids to read the message unobserved by its current relaxed view.

    If a memory write performs, it may catch up a delayed write in the delayed write set and
    remove such delayed item in the delayed write set.
 *)
Inductive na_step_dset {lang: language} {index: Type} (lo: Ordering.LocOrdMap):
  (Thread.t lang * @DelaySet index) -> (Thread.t lang * @DelaySet index) -> Prop :=
| na_steps_dset_tau
    e1 e2 dset
    (STEP: Thread.program_step ThreadEvent.silent lo e1 e2):
    na_step_dset lo (e1, dset) (e2, dset)
| na_steps_dset_read
    e1 e2 loc ts v R dset
    (STEP: Thread.program_step (ThreadEvent.read loc ts v R Ordering.plain) lo e1 e2)
    (RLX: forall loc ts i, dset_get loc ts dset = Some i ->
                      View.rlx (TView.cur (Local.tview (Thread.local e1))) loc =
                      View.rlx (TView.cur (Local.tview (Thread.local e2))) loc):
    na_step_dset lo (e1, dset) (e2, dset)
| na_steps_dset_write
    e1 e2 loc from to v R dset dset'
    (STEP: Thread.program_step (ThreadEvent.write loc from to v R Ordering.plain) lo e1 e2)
    (DSET_REMOVE: dset' = dset \/ (exists ts, dset' = dset_remove loc ts dset)):
    na_step_dset lo (e1, dset) (e2, dset').

Lemma na_step_dset_subset
      lang index lo e1 dset1 e2 dset2
      (NA_STEP_DSET: @na_step_dset lang index lo (e1, dset1) (e2, dset2)):
  dset_subset dset2 dset1.
Proof.
  inv NA_STEP_DSET; try solve [unfold dset_subset; ii; eauto].
  des; subst.
  unfold dset_subset; ii; eauto.
  unfold dset_subset; ii.
  eapply dset_get_remove; eauto.
Qed.

Lemma na_steps_dset_subset':
  forall n lang index lo e1 dset1 e2 dset2
    (NA_STEPS_DSET: rtcn (@na_step_dset lang index lo) n (e1, dset1) (e2, dset2)),
    dset_subset dset2 dset1.
Proof.
  induction n; ii.
  - inv NA_STEPS_DSET. eauto.
  - inv NA_STEPS_DSET. destruct a2.
    eapply IHn in A23; eauto.
    eapply na_step_dset_subset in A12.
    clear - H A12 A23. unfold dset_subset in *; ss.
    eapply A23 in H. eapply A12 in H. eauto.
Qed.

Lemma na_steps_dset_subset
      lang index lo e1 dset1 e2 dset2
      (NA_STEPS_DSET: rtc (@na_step_dset lang index lo) (e1, dset1) (e2, dset2)):
  dset_subset dset2 dset1.
Proof.
  eapply rtc_rtcn in NA_STEPS_DSET. des.
  eapply na_steps_dset_subset'; eauto.
Qed.

Lemma na_step_dset_to_Thread_na_step:
  forall lang index lo e1 dset1 e2 dset2
    (NA_STEP_DSET: @na_step_dset lang index lo (e1, dset1) (e2, dset2)),
    Thread.na_step lo e1 e2.
Proof.
  ii. inv NA_STEP_DSET; eauto.
  eapply Thread.na_tau_step_intro; eauto.
  eapply Thread.na_plain_read_step_intro; eauto.
  eapply Thread.na_plain_write_step_intro; eauto.
Qed.

Lemma na_steps_dset_to_Thread_na_steps':
  forall n lang index lo e1 dset1 e2 dset2
    (NA_STEPS_DSET: rtcn (@na_step_dset lang index lo) n (e1, dset1) (e2, dset2)),
    rtc (Thread.na_step lo) e1 e2.
Proof.
  induction n; ii.
  - inv NA_STEPS_DSET. eauto.
  - inv NA_STEPS_DSET. destruct a2.
    eapply IHn in A23; eauto.
    eapply na_step_dset_to_Thread_na_step in A12.
    eauto.
Qed.

Lemma na_steps_dset_to_Thread_na_steps
      lang index lo e1 dset1 e2 dset2
      (NA_STEPS_DSET: rtc (@na_step_dset lang index lo) (e1, dset1) (e2, dset2)):
  rtc (Thread.na_step lo) e1 e2.
Proof.
  eapply rtc_rtcn in NA_STEPS_DSET. des.
  eapply na_steps_dset_to_Thread_na_steps'; eauto.
Qed.

Lemma na_steps_dset_to_NPThread_tau_steps
      lang index lo e1 dset1 e2 dset2 b
      (NA_STEPS_DSET: rtc (@na_step_dset lang index lo) (e1, dset1) (e2, dset2)):
  exists b', rtc (NPAuxThread.tau_step lang lo) (NPAuxThread.mk lang e1 b) (NPAuxThread.mk lang e2 b').
Proof.
  eapply na_steps_dset_to_Thread_na_steps in NA_STEPS_DSET.
  eapply rtc_rtcn in NA_STEPS_DSET. des.
  eapply rtc_na_p_to_np in NA_STEPS_DSET. des.
  eapply np_na_steps_is_tau_steps in NA_STEPS_DSET. eauto.
Qed.


