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

Set Implicit Arguments.

(** * Message mapping *)

(** The message mapping defined as [Mapping] in the file
    relates the "to"-timestamps of the target and source messages. *)

(** This file also contains some properties on message mapping. *)

(** [TMapInj]: message mapping related timemap (in Figure 8 in paper). *)

(** [opt_ViewInj]: message mapping related message view (in Figure 8 in paper). *)

(** [weak_MsgInj] in this file corresponds to
    the well-formed message mapping (Definition 4.1 in paper).
    It requires that every concrete message in the target level
    has a related concrete message in the source level through the message mapping parameter.

    In Coq formalization, we remove the restriction that
    the message view of the message in the target level is also related with
    the message view of its corresponding message in the source level,
    since we find that such restriction will never be used in the proof of the soundness of
    our verification framework. 
 *)

Lemma Loc_add_eq
      A loc (r: A) f:
  (LocFun.add loc r f) loc = r.
Proof.
  assert(LocFun.find loc (LocFun.add loc r f) = r).
  rewrite LocFun.add_spec_eq; eauto.
  unfold LocFun.find in *. eauto.
Qed.

Lemma Loc_add_neq
      A loc (r: A) f loc'
      (NEQ: loc <> loc'):
  (LocFun.add loc r f) loc' = f loc'.
Proof.
  assert(LocFun.find loc' (LocFun.add loc r f) = f loc').
  rewrite LocFun.add_spec_neq; eauto.
  unfold LocFun.find in *. eauto.
Qed.

Ltac auto_solve_time_rel :=
  match goal with
  | H1: Memory.get ?loc ?to ?mem = Some (?from, ?msg), H2: Time.lt ?to0 ?to |- Time.lt ?from ?to =>
    eapply Memory.get_ts in H1; des; subst; ss; auto_solve_time_rel
  | H: Time.lt ?to ?to |- _ => eapply Time.lt_strorder in H; ss
  | H: Time.lt ?to Time.bot |- _ => eapply Time_lt_bot_false in H; ss
  | H1: Time.le ?from ?ts, H2: Time.lt ?ts ?to |- Time.lt ?from ?to =>
    eapply TimeFacts.le_lt_lt; eauto; ss
  | H1: Time.lt ?from ?ts, H2: Time.le ?ts ?to |- Time.lt ?from ?to =>
    eapply TimeFacts.lt_le_lt; eauto; ss
  | H1: Time.lt ?from ?to, H2: Time.le ?to ?from |- _ =>
    exploit Time_lt_ge_false; [eapply H1 | eapply H2 | eauto..]; ii; ss
  | H1: Time.le ?from ?to, H2: Time.lt ?to ?from |- _ =>
    exploit Time_le_gt_false; [eapply H1 | eapply H2 | eauto..]; ii; ss
  | H1: Time.lt ?from ?ts, H2: Time.lt ?ts ?to |- _ =>
    exploit Time.Time.lt_strorder_obligation_2; [eapply H1 | eapply H2 | eauto..]
  | H1: Time.le ?from ?ts, H2: Time.le ?ts ?to |- Time.le ?from ?to =>
    exploit DenseOrder.DenseOrder_le_PreOrder_obligation_2; [eapply H1 | eapply H2 | eauto..]
  | |- Time.lt ?to (Time.incr ?to) => eapply Time.incr_spec; eauto
  | H: Memory.get ?loc ?to ?mem = Some _ |- Time.le ?to (Memory.max_ts ?loc ?mem) =>
    eapply Memory.max_ts_spec in H; des; eauto
  | |- Time.le ?to ?to => eapply Time.le_lteq; eauto
  | H: Time.lt ?from ?to |- Time.le ?from ?to => eapply Time.le_lteq; left; eapply H
  | _ => idtac
  end.

(** ** Message mapping *)
(** Message mapping maps a message in the location x with "to"-timestamp t1 in the target level 
    to the message in the location x with "to"-timestamp t2 in the source level.
    It corresponds to [MMap] defined in Figure 8 in our paper *)
Definition Mapping := Loc.t -> Time.t -> option Time.t.

(** ** A monotonic message mapping *)
Definition monotonic_inj (inj: Mapping) :=
  forall loc t1 t1' t2 t2'
         (TIME_LT: Time.lt t1 t2)
         (INJ1: inj loc t1 = Some t1')
         (INJ2: inj loc t2 = Some t2'),
    Time.lt t1' t2'.

Lemma monotonic_inj_implies_le_prsv
      (inj: Mapping) t1 t1' t2 t2' loc
      (MON: monotonic_inj inj)
      (TIME_LE: Time.le t1 t2)
      (INJ1: inj loc t1 = Some t1')
      (INJ2: inj loc t2 = Some t2'):
  Time.le t1' t2'.
Proof.
  eapply Time.le_lteq in TIME_LE. des.
  eapply MON in TIME_LE; eauto.
  eapply Time.le_lteq. left. eauto.
  subst.
  rewrite INJ1 in INJ2. inv INJ2.
  eapply Time.le_lteq; eauto.
Qed.

Lemma monotonic_inj_implies_disj_mapping
      inj loc to1 to2 to1' to2'
      (MON: monotonic_inj inj)
      (INJ1: inj loc to1 = Some to1')
      (INJ2: inj loc to2 = Some to2')
      (DISJ: to1 <> to2):
  to1' <> to2'.
Proof.
  ii; subst.
  destruct (Time.le_lt_dec to1 to2).
  {
    eapply Time.le_lteq in l; des; subst; ss.
    eapply MON in l; eauto.
    exploit l; eauto; ii.
    eapply Time.Time.lt_strorder_obligation_1 in x; eauto.
  }
  {
    eapply MON in l; eauto.
    exploit l; eauto; ii.
    eapply Time.Time.lt_strorder_obligation_1 in x; eauto.
  }
Qed.

Lemma inj_join_comp
      t1 t1' t2 t2' inj loc
      (INJ1: inj loc t1 = Some t1')
      (INJ2: inj loc t2 = Some t2')
      (MON: monotonic_inj inj):
  inj loc (Time.join t1 t2) = Some (Time.join t1' t2').
Proof.
  unfold Time.join. des_if.
  eapply Time.le_lteq in l. des; subst.
  exploit MON; eauto. ii.
  des_if; eauto. 
  clear - x l0. auto_solve_time_rel. ii. auto_solve_time_rel.
  des_if; eauto.
  des_if; eauto.
  exploit MON; eauto. ii.
  auto_solve_time_rel.
Qed.

Lemma monotonic_inj_implies_injective
      to1 to2 to' inj loc
      (MONOTONIC: monotonic_inj inj)
      (INJ1: inj loc to1 = Some to')
      (INJ2: inj loc to2 = Some to'):
  to1 = to2.
Proof.
  destruct (Time.eq_dec to1 to2); subst; eauto.
  exploit monotonic_inj_implies_disj_mapping;
    [eapply MONOTONIC | eapply INJ1 | eapply INJ2 | eapply n | eauto..].
  ii; ss.
Qed.
  
(** ** Timemaps mapping *)
Definition TMapInj (inj: Mapping) (tm_tgt tm_src: TimeMap.t): Prop :=
  forall (loc: Loc.t) (t': Time.t)
         (injDom: inj loc (tm_tgt loc) = Some t'),
    tm_src loc = t'. 

Definition closed_TMapInj (inj: Mapping) (tm: TimeMap.t): Prop :=
  forall loc,
  exists t', inj loc (tm loc) = Some t'.

Lemma closed_TMapInj_implies_TMap
      inj tm_tgt
      (CLOSED_TMINJ: closed_TMapInj inj tm_tgt):
  exists tm_src, TMapInj inj tm_tgt tm_src.
Proof.
  cut (exists tm_src,
          forall loc,
            (fun loc0 t0 => inj loc0 (tm_tgt loc0) = Some t0) loc (tm_src loc)).
  {
    ii. des.
    exists tm_src.
    unfold TMapInj; ii; subst.
    specialize (H loc).
    rewrite H in injDom.
    inv injDom; eauto.
  }
  eapply choice; ii.
  unfold closed_TMapInj in *.
  specialize (CLOSED_TMINJ x); des.
  exists t'. ss.
Qed.

Lemma closed_TMapInj_implies_inj
      inj tm_tgt tm_src loc
      (TM_INJ: TMapInj inj tm_tgt tm_src)
      (CLOSED_TM: closed_TMapInj inj tm_tgt):
  inj loc (tm_tgt loc) = Some (tm_src loc).
Proof.
  unfold closed_TMapInj in *.
  specialize (CLOSED_TM loc). des.
  dup CLOSED_TM.
  eapply TM_INJ in CLOSED_TM; subst; eauto.
Qed.

Lemma Montonic_TMapInj_join
      inj tm_tgt tm_tgt' tm_src tm_src'
      (CLOSED_TMAP1: closed_TMapInj inj tm_tgt)
      (CLOSED_TMAP2: closed_TMapInj inj tm_tgt')
      (MON: monotonic_inj inj)
      (TMAP_INJ1: TMapInj inj tm_tgt tm_src)
      (TMAP_INJ2: TMapInj inj tm_tgt' tm_src'):
  TMapInj inj (TimeMap.join tm_tgt tm_tgt') (TimeMap.join tm_src tm_src').
Proof. 
  unfold TMapInj in *; ii.
  unfold TimeMap.join in *; ii.
  unfold closed_TMapInj in *.
  specialize (CLOSED_TMAP1 loc).
  specialize (CLOSED_TMAP2 loc).
  des.
  unfold Time.join in *.
  des_ifH injDom; subst.
  {
    rewrite CLOSED_TMAP2 in injDom. inv injDom.
    eapply Time.le_lteq in l; des.
    { 
      cut(Time.lt (tm_src loc) (tm_src' loc)); ii.
      des_if; ss.
      eapply TMAP_INJ2 in CLOSED_TMAP2; eauto.
      cut(Time.le (tm_src' loc) (tm_src loc)); ii.
      eapply Time_le_gt_false in H0; ss.
      eapply Time.le_lteq; eauto.
      unfold monotonic_inj in *.
      eapply MON; eauto.
      dup CLOSED_TMAP1.
      eapply TMAP_INJ1 in CLOSED_TMAP0; subst; ss.
      eapply CLOSED_TMAP1.
      dup CLOSED_TMAP2.
      eapply TMAP_INJ2 in CLOSED_TMAP0; subst; ss.
    }
    {
      dup CLOSED_TMAP1.
      dup CLOSED_TMAP2.
      eapply TMAP_INJ1 in CLOSED_TMAP1.
      eapply TMAP_INJ2 in CLOSED_TMAP2. subst.
      rewrite l in CLOSED_TMAP0.
      rewrite CLOSED_TMAP0 in CLOSED_TMAP3. inv CLOSED_TMAP3.
      des_if; ss.
    }
  }
  { 
    dup CLOSED_TMAP1.
    dup CLOSED_TMAP2.
    eapply TMAP_INJ1 in CLOSED_TMAP1.
    eapply TMAP_INJ2 in CLOSED_TMAP2. subst.
    cut(Time.lt (tm_src' loc) (tm_src loc)); ii.
    des_if; ss.
    eapply Time_lt_ge_false in H; ss.
    rewrite CLOSED_TMAP0 in injDom. inv injDom; ss.
    eapply MON; eauto.
  }
Qed.

Lemma TMapInj_singleton
      inj tm tm' to to' loc
      (MON: monotonic_inj inj)
      (CLOSED: closed_TMapInj inj tm)
      (INJ_TM: TMapInj inj tm tm')
      (INJ_MSG: inj loc to = Some to'):
  TMapInj inj (TimeMap.join tm (TimeMap.singleton loc to))
          (TimeMap.join tm' (TimeMap.singleton loc to')).
Proof.
  unfold TMapInj. ii.
  unfold TimeMap.singleton in *.
  unfold TimeMap.join in *.
  destruct (Loc.eq_dec loc loc0); subst.
  {
    cut(LocFun.find loc0 (LocFun.add loc0 to (LocFun.init Time.bot)) = to). ii.
    unfold LocFun.find in *. try rewrite H in *.
    cut(LocFun.find loc0 (LocFun.add loc0 to' (LocFun.init Time.bot)) = to'). ii.
    unfold LocFun.find in *. try rewrite H0 in *.
    clear H H0.
    unfold Time.join in *.
    des_ifH injDom.
    rewrite INJ_MSG in injDom. inv injDom.
    unfold closed_TMapInj in *.
    specialize (CLOSED loc0). des.
    unfold TMapInj in INJ_TM.
    exploit INJ_TM; [eapply CLOSED | eauto..]. ii. subst.
    exploit monotonic_inj_implies_le_prsv; eauto. ii.
    des_if; eauto.
    eapply Time_le_gt_false in x0; eauto; ss.
    exploit MON; [eapply l | eauto..]. ii.
    des_if; eauto.
    unfold TMapInj in *.
    exploit INJ_TM; [eapply injDom | eauto..]. ii. subst.
    eapply Time_lt_ge_false in x; eauto; ss.
    eapply LocFun.add_spec_eq; eauto.
    eapply LocFun.add_spec_eq; eauto.
  }
  {
    cut(LocFun.find loc0 (LocFun.add loc to (LocFun.init Time.bot)) = Time.bot). ii.
    unfold LocFun.find in *. try rewrite H in *.
    cut(LocFun.find loc0 (LocFun.add loc to' (LocFun.init Time.bot)) = Time.bot). ii.
    unfold LocFun.find in *. try rewrite H0 in *.
    clear H H0.
    rewrite TimeFacts.le_join_l in injDom.
    rewrite TimeFacts.le_join_l.
    unfold TMapInj in *. exploit INJ_TM; [eapply injDom | eauto..].
    eapply Time.bot_spec. eapply Time.bot_spec.
    eapply LocFun.add_spec_neq; eauto.
    eapply LocFun.add_spec_neq; eauto.
  }
Qed.

Lemma closed_TMapInj_implies_inj_singleton
      tm_tgt tm_src loc loc0 to to' inj
      (TM_INJ: TMapInj inj tm_tgt tm_src)
      (INJ: inj loc to = Some to')
      (CLOSED_TM: closed_TMapInj inj tm_tgt)
      (MON: monotonic_inj inj):
  inj loc0 (Time.join (tm_tgt loc0) (TimeMap.singleton loc to loc0)) =
  Some (Time.join (tm_src loc0) (TimeMap.singleton loc to' loc0)).
Proof.
  unfold TMapInj, closed_TMapInj in *.
  unfold TimeMap.singleton.
  destruct(Loc.eq_dec loc loc0); subst.
  {
    repeat (rewrite Loc_add_eq; eauto).
    unfold Time.join.
    des_if.
    {
      specialize (CLOSED_TM loc0). des.
      dup CLOSED_TM.
      eapply TM_INJ in CLOSED_TM0; eauto; subst.
      exploit monotonic_inj_implies_le_prsv; eauto. ii.
      des_if; eauto.
      auto_solve_time_rel.
    }
    {
      specialize (CLOSED_TM loc0). des.
      dup CLOSED_TM.
      eapply TM_INJ in CLOSED_TM0; eauto; subst.
      des_if; eauto.
      unfold monotonic_inj in *.
      exploit MON; [eapply l | eapply INJ | eapply CLOSED_TM | eauto..]. ii.
      auto_solve_time_rel.
    }
  }
  {
    repeat (rewrite Loc_add_neq; eauto).
    unfold LocFun.init.
    assert(inj loc0 (tm_tgt loc0) = Some (tm_src loc0)).
    {
      specialize (CLOSED_TM loc0). des. dup CLOSED_TM.
      eapply TM_INJ in CLOSED_TM0; eauto. subst; eauto.
    }
    unfold Time.join. des_if.
    eapply Time.le_lteq in l; eauto. des. auto_solve_time_rel.
    des_if.
    eapply Time.le_lteq in l0; eauto. des. auto_solve_time_rel.
    rewrite <- l at 1. rewrite <- l0. eauto.
    rewrite <- l. eauto.
    des_if; eauto.
    eapply Time.le_lteq in l0; eauto. des; eauto.
    auto_solve_time_rel.
    rewrite <- l0; eauto.
  }
Qed.

Lemma closed_TMapInj_join
      tm1 tm2 inj
      (CLOSED_TMAP1: closed_TMapInj inj tm1)
      (CLOSED_TMAP2: closed_TMapInj inj tm2):
  closed_TMapInj inj (TimeMap.join tm1 tm2).
Proof.
  unfold closed_TMapInj in *. ii.
  specialize (CLOSED_TMAP1 loc). specialize (CLOSED_TMAP2 loc). des.
  unfold TimeMap.join. unfold Time.join.
  des_if; eauto.
Qed.

Lemma closed_TMapinj_join_singletion
      inj tm loc to to'
      (INJ: inj loc to = Some to')
      (CLOSED: closed_TMapInj inj tm):
  closed_TMapInj inj (TimeMap.join tm (TimeMap.singleton loc to)).
Proof.
  unfold closed_TMapInj in *; ss. ii.
  dup CLOSED.
  specialize (CLOSED loc). des.
  unfold TimeMap.singleton. unfold TimeMap.join. unfold Time.join.
  des_if.
  {
    destruct (Loc.eq_dec loc loc0); subst.
    {
      cut(LocFun.find loc0 (LocFun.add loc0 to (LocFun.init Time.bot)) = to). ii.
      unfold LocFun.find in *. rewrite H in l. rewrite H. eauto.
      eapply LocFun.add_spec_eq.
    }
    {
      cut(LocFun.find loc0 (LocFun.add loc to (LocFun.init Time.bot)) = Time.bot). ii.
      unfold LocFun.find in *. try rewrite H in *.
      eapply Time.le_lteq in l. des; subst. eapply Time_lt_bot_false in l; ss.
      specialize (CLOSED0 loc0). des. rewrite l in CLOSED0. eauto.
      eapply LocFun.add_spec_neq; eauto.
    }
  }
  {
    specialize (CLOSED0 loc0). eauto.
  }
Qed.

Definition ViewInj (inj: Mapping) (view_tgt view_src: View.t): Prop :=
  match view_tgt, view_src with
  | View.mk pln_tgt rlx_tgt, View.mk pln_src rlx_src =>
    TMapInj inj pln_tgt pln_src /\ TMapInj inj rlx_tgt rlx_src
  end.

Definition closed_viewInj (inj: Mapping) (view: View.t): Prop :=
  closed_TMapInj inj (View.pln view) /\ closed_TMapInj inj (View.rlx view).

Lemma closed_viewInj_implies_view
      inj view_tgt
      (CLOSED_VIEWINJ: closed_viewInj inj view_tgt):
  exists view_src, ViewInj inj view_tgt view_src.
Proof.
  inv CLOSED_VIEWINJ.
  eapply closed_TMapInj_implies_TMap in H.
  eapply closed_TMapInj_implies_TMap in H0.
  des.
  exists (View.mk tm_src0 tm_src).
  unfold ViewInj.
  destruct view_tgt; ss.
Qed. 

Lemma Monotonic_viewInj_join
      inj view_tgt view_tgt' view_src view_src'
      (CLOSED_VIEW1: closed_viewInj inj view_tgt)
      (CLOSED_VIEW2: closed_viewInj inj view_tgt')
      (MON: monotonic_inj inj)
      (VIEW_INJ1: ViewInj inj view_tgt view_src)
      (VIEW_INJ2: ViewInj inj view_tgt' view_src'):
  ViewInj inj (View.join view_tgt view_tgt') (View.join view_src view_src').
Proof.
  unfold closed_viewInj in *; ss.
  unfold ViewInj in *; ss.
  destruct view_tgt; destruct view_tgt'; ss.
  destruct view_src; destruct view_src'; ss; des.
  split.
  eapply Montonic_TMapInj_join; eauto.
  eapply Montonic_TMapInj_join; eauto.
Qed.

Lemma Monotonic_viewInj_join_singleton
      inj view view' loc to to'
      (CLOSED_VIEW: closed_viewInj inj view)
      (MON: monotonic_inj inj)
      (INJ: inj loc to = Some to')
      (VIEW_INJ: ViewInj inj view view'):
  ViewInj inj (View.join view (View.singleton_ur loc to))
          (View.join view' (View.singleton_ur loc to')).
Proof.
  unfold View.singleton_ur.
  unfold ViewInj in *; ss. destruct view, view'; ss; des.
  unfold closed_viewInj in *; ss; des.
  split; eapply TMapInj_singleton; eauto.
Qed.

Lemma closed_viewInj_join
      inj view1 view2
      (CLOSED_VIEW1: closed_viewInj inj view1)
      (CLOSED_VIEW2: closed_viewInj inj view2):
  closed_viewInj inj (View.join view1 view2).
Proof.
  unfold closed_viewInj in *. des.
  split; eapply closed_TMapInj_join; eauto.
Qed.

Lemma closed_viewInj_join_singleton
      inj view loc to to'
      (CLOSED_VIEW: closed_viewInj inj view)
      (INJ: inj loc to = Some to'):
  closed_viewInj inj (View.join view (View.singleton_ur loc to)).
Proof.
  unfold closed_viewInj in *; ii. des.
  split; eapply closed_TMapinj_join_singletion; eauto.
Qed.
  
(** ** View mapping *)
Definition opt_ViewInj (inj: Mapping) (opt_view_tgt opt_view_src: option View.t): Prop :=
  match opt_view_tgt, opt_view_src with
  | Some view_tgt, Some view_src => ViewInj inj view_tgt view_src
  | None, None => True
  | _, _ => False
  end. 

Definition closed_opt_viewinj (inj: Mapping) (opt_view: option View.t) :=
  match opt_view with
  | Some view => closed_viewInj inj view
  | None => True
  end.

(** ** TView mapping *)
Definition TViewInj (inj: Mapping) (tview_tgt tview_src: TView.t): Prop :=
  (forall loc, ViewInj inj ((TView.rel tview_tgt) loc) ((TView.rel tview_src) loc)) /\
  (ViewInj inj (TView.cur tview_tgt) (TView.cur tview_src)) /\
  (ViewInj inj (TView.acq tview_tgt) (TView.acq tview_src)).

Definition closed_tviewInj (inj: Mapping) (tview: TView.t): Prop :=
  (forall loc, closed_viewInj inj ((TView.rel tview) loc)) /\
  (closed_viewInj inj (TView.cur tview)) /\ (closed_viewInj inj (TView.acq tview)).

(** ** Message mapping: restriction on message injection *)
Inductive MsgInj: forall (inj: Mapping) (mem_tgt mem_src: Memory.t), Prop :=
| MsgInj_intro inj mem_tgt mem_src
    (SOUND: forall loc val f t R
              (MSG: Memory.get loc t mem_tgt = Some (f, Message.concrete val R)),
        exists t' f' R',
          inj loc t = Some t' /\ opt_ViewInj inj R R' /\
          Memory.get loc t' mem_src = Some (f', Message.concrete val R'))
    (COMPLETE: forall loc t t'
                 (INJ: inj loc t = Some t'),
        exists val f R, Memory.get loc t mem_tgt = Some (f, Message.concrete val R))
    (MONOTONIC: monotonic_inj inj):
    MsgInj inj mem_tgt mem_src.

(** ** Weak message mapping *)
Inductive weak_MsgInj: forall (inj: Mapping) (mem_tgt mem_src: Memory.t), Prop :=
| weak_MsgInj_intro
    inj mem_tgt mem_src
    (** Message view R and R' are not required to be inj related  *)
    (SOUND: forall loc val f t R
              (MSG: Memory.get loc t mem_tgt = Some (f, Message.concrete val R)),
        exists t' f' R',
          inj loc t = Some t' /\
          Memory.get loc t' mem_src = Some (f', Message.concrete val R'))
    (COMPLETE: forall loc t t'
                 (INJ: inj loc t = Some t'),
        exists val f R, Memory.get loc t mem_tgt = Some (f, Message.concrete val R))
    (MONOTONIC: monotonic_inj inj):
    weak_MsgInj inj mem_tgt mem_src.

Lemma msgInj_implies_weak_msgInj
      inj mem_tgt mem_src
      (MSG_INJ: MsgInj inj mem_tgt mem_src):
  weak_MsgInj inj mem_tgt mem_src.
Proof.
  inv MSG_INJ. econs; eauto. ii.
  eapply SOUND in MSG; des; ss; eauto.
Qed.

Lemma weak_MsgInj_not_in_dom
      inj mem mem' loc to
      (MSG_INJ: weak_MsgInj inj mem mem')
      (GET: Memory.get loc to mem = None):
  inj loc to = None.
Proof.
  inv MSG_INJ.
  destruct(inj loc to) eqn:Heqe; eauto.
  eapply COMPLETE in Heqe; eauto. des.
  rewrite GET in Heqe; ss.
Qed.

Lemma MsgInj_not_in_dom
      inj mem mem' loc to
      (MSG_INJ: MsgInj inj mem mem')
      (GET: Memory.get loc to mem = None):
  inj loc to = None.
Proof.
  eapply weak_MsgInj_not_in_dom; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma weak_MsgInj_implies_closed_view
      inj mem_tgt mem_src loc to from val released
      (MSG_INJ: weak_MsgInj inj mem_tgt mem_src)
      (CLOSED_MEM: Memory.closed mem_tgt)
      (GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)):
  released = None \/ (exists view, released = Some view /\ closed_viewInj inj view).
Proof.
  destruct released; eauto.
  right.
  eexists.
  split; eauto.
  inv MSG_INJ.
  inv CLOSED_MEM.
  dup GET.
  eapply CLOSED in GET0; des.
  inv MSG_CLOSED.
  inv CLOSED0.
  inv CLOSED1.
  unfold closed_viewInj. split.
  {
    unfold closed_TMapInj; ii.
    unfold Memory.closed_timemap in PLN.
    specialize (PLN loc0). des.
    eapply SOUND in PLN; ss.
    des; eauto.
  }
  {
    unfold closed_TMapInj; ii.
    unfold Memory.closed_timemap in RLX.
    specialize (RLX loc0). des.
    eapply SOUND in RLX; ss.
    des; eauto.
  }
Qed.

Lemma wf_msginj_implies_closed_view
      inj mem_tgt mem_src loc to from val released
      (MSG_INJ: MsgInj inj mem_tgt mem_src)
      (CLOSED_MEM: Memory.closed mem_tgt)
      (GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)):
  released = None \/ (exists view, released = Some view /\ closed_viewInj inj view).
Proof.
  eapply weak_MsgInj_implies_closed_view; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma TViewInj_sound_cur_acq'
      tview tview' mem mem' inj loc
      (CLOSED_TVIEW: TView.closed tview mem)
      (TVIEWINJ: TViewInj inj tview tview')
      (MSGINJ: weak_MsgInj inj mem mem'):
  <<INJ_CUR_PLN: inj loc (View.pln (TView.cur tview) loc) = Some (View.pln (TView.cur tview') loc)>> /\
  <<INJ_CUR_RLX: inj loc (View.rlx (TView.cur tview) loc) = Some (View.rlx (TView.cur tview') loc)>> /\ 
  <<INJ_ACQ_PLN: inj loc (View.pln (TView.acq tview) loc) = Some (View.pln (TView.acq tview') loc)>> /\
  <<INJ_ACQ_RLX: inj loc (View.rlx (TView.acq tview) loc) = Some (View.rlx (TView.acq tview') loc)>>.
Proof.
  inv TVIEWINJ. des. clear H.
  unfold ViewInj in *.
  destruct tview, tview'; ss. destruct cur, acq; ss.
  destruct cur0, acq0; ss. des.
  inv CLOSED_TVIEW; ss.
  inv CUR; inv ACQ; ss.
  unfold TMapInj in *.
  unfold Memory.closed_timemap in *.
  specialize (PLN loc). specialize (RLX loc).
  specialize (PLN0 loc). specialize (RLX0 loc).
  des.
  inv MSGINJ.
  eapply SOUND in PLN; eauto.
  eapply SOUND in RLX; eauto.
  eapply SOUND in PLN0; eauto.
  eapply SOUND in RLX0; eauto.
  des.
  exploit H0; eauto.
  exploit H3; eauto.
  exploit H1; eauto.
  exploit H2; eauto.
  ii; subst.
  eauto.
Qed.

Lemma TViewInj_sound_cur_acq
      tview tview' mem mem' inj loc
      (CLOSED_TVIEW: TView.closed tview mem)
      (TVIEWINJ: TViewInj inj tview tview')
      (MSGINJ: MsgInj inj mem mem'):
  <<INJ_CUR_PLN: inj loc (View.pln (TView.cur tview) loc) = Some (View.pln (TView.cur tview') loc)>> /\
  <<INJ_CUR_RLX: inj loc (View.rlx (TView.cur tview) loc) = Some (View.rlx (TView.cur tview') loc)>> /\ 
  <<INJ_ACQ_PLN: inj loc (View.pln (TView.acq tview) loc) = Some (View.pln (TView.acq tview') loc)>> /\
  <<INJ_ACQ_RLX: inj loc (View.rlx (TView.acq tview) loc) = Some (View.rlx (TView.acq tview') loc)>>.
Proof.
  eapply TViewInj_sound_cur_acq'; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma TViewInj_sound_rel'
      tview tview' mem mem' inj loc loc0
      (CLOSED_TVIEW: TView.closed tview mem)
      (TVIEWINJ: TViewInj inj tview tview')
      (MSGINJ: weak_MsgInj inj mem mem'):
  <<INJ_REL_PLN: inj loc (View.pln (TView.rel tview loc0) loc) = Some (View.pln (TView.rel tview' loc0) loc)>> /\
  <<INJ_REL_RLX: inj loc (View.rlx (TView.rel tview loc0) loc) = Some (View.rlx (TView.rel tview' loc0) loc)>>.
Proof.
  inv TVIEWINJ. des. clear H0 H1. specialize (H loc0).
  unfold ViewInj in *.
  inv CLOSED_TVIEW; ss.
  specialize (REL loc0).
  clear CUR ACQ.
  inv REL.
  unfold Memory.closed_timemap in *.
  specialize (PLN loc). specialize (RLX loc). des.
  destruct tview, tview'; ss.
  destruct (rel loc0).
  destruct (rel0 loc0). ss.
  des.
  unfold TMapInj in *.
  inv MSGINJ.
  eapply SOUND in PLN; eauto.
  eapply SOUND in RLX; eauto.
  des.
  exploit H; eauto.
  exploit H0; eauto.
  ii; subst; eauto.
Qed.

Lemma TViewInj_sound_rel
      tview tview' mem mem' inj loc loc0
      (CLOSED_TVIEW: TView.closed tview mem)
      (TVIEWINJ: TViewInj inj tview tview')
      (MSGINJ: MsgInj inj mem mem'):
  <<INJ_REL_PLN: inj loc (View.pln (TView.rel tview loc0) loc) = Some (View.pln (TView.rel tview' loc0) loc)>> /\
  <<INJ_REL_RLX: inj loc (View.rlx (TView.rel tview loc0) loc) = Some (View.rlx (TView.rel tview' loc0) loc)>>.
Proof.
  eapply TViewInj_sound_rel'; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma Time_le_monotonic_inj
      to1 to2 to1' to2' inj loc 
      (LE: Time.le to1 to2)
      (INJ1: inj loc to1 = Some to1')
      (INJ2: inj loc to2 = Some to2')
      (MON: monotonic_inj inj):
  Time.le to1' to2'.
Proof.
  eapply Time.le_lteq in LE.
  des.
  eapply MON in LE; eauto.
  eapply Time.le_lteq; eauto.
  subst.
  rewrite INJ1 in INJ2; eauto.
  inv INJ2; eauto.
  eapply Time.le_lteq; eauto.
Qed.

Lemma closed_view_weak_msginj_implies_closed_viewInj
      view mem mem' inj
      (VIEW_CLOSED: Memory.closed_view view mem)
      (MEM_INJ: weak_MsgInj inj mem mem'):
  closed_viewInj inj view.
Proof.
  inv VIEW_CLOSED.
  destruct view; ss.
  inv MEM_INJ.
  econs; eauto; ss.
  {
    unfold Memory.closed_timemap in *.
    unfold closed_TMapInj. ii.
    exploit PLN; eauto. instantiate (1 := loc). ii. des.
    exploit SOUND; eauto. ii; des; eauto.
  }
  {
    unfold Memory.closed_timemap in *.
    unfold closed_TMapInj. ii.
    exploit RLX; eauto. instantiate (1 := loc). ii. des.
    exploit SOUND; eauto. ii; des; eauto.
  }
Qed.
  
Lemma closed_view_msginj_implies_closed_viewInj
      view mem mem' inj
      (VIEW_CLOSED: Memory.closed_view view mem)
      (MEM_INJ: MsgInj inj mem mem'):
  closed_viewInj inj view.
Proof.
  eapply closed_view_weak_msginj_implies_closed_viewInj; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma closed_optview_weak_msginj_implies_closed_viewInj
      opt_view mem mem' inj
      (VIEW_CLOSED: Memory.closed_opt_view opt_view mem)
      (MEM_INJ: weak_MsgInj inj mem mem'):
  closed_opt_viewinj inj opt_view.
Proof.
  destruct opt_view; ss.
  eapply closed_view_weak_msginj_implies_closed_viewInj; eauto.
  inv VIEW_CLOSED; eauto.
Qed.

Lemma closed_optview_msginj_implies_closed_viewInj
      opt_view mem mem' inj
      (VIEW_CLOSED: Memory.closed_opt_view opt_view mem)
      (MEM_INJ: MsgInj inj mem mem'):
  closed_opt_viewinj inj opt_view.
Proof.
  eapply closed_optview_weak_msginj_implies_closed_viewInj; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma closed_tview_weak_msginj_implies_closed_tviewInj
      tview mem mem' inj
      (TVIEW_CLOSED: TView.closed tview mem)
      (MEM_INJ: weak_MsgInj inj mem mem'):
  closed_tviewInj inj tview.
Proof.
  inv TVIEW_CLOSED.
  econs; eauto. i.
  eapply closed_view_weak_msginj_implies_closed_viewInj; eauto.
  split; eapply closed_view_weak_msginj_implies_closed_viewInj; eauto.
Qed.

Lemma closed_tview_msginj_implies_closed_tviewInj
      tview mem mem' inj
      (TVIEW_CLOSED: TView.closed tview mem)
      (MEM_INJ: MsgInj inj mem mem'):
  closed_tviewInj inj tview.
Proof.
  eapply closed_tview_weak_msginj_implies_closed_tviewInj; eauto.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma closed_opt_viewInj_write_released
      inj tview sc loc to releasedr ord to'
      (CLOSED_TVIEW: closed_tviewInj inj tview)
      (CLOSED_RELEASEDR: closed_opt_viewinj inj releasedr)
      (INJ: inj loc to = Some to'):
  closed_opt_viewinj inj (TView.write_released tview sc loc to releasedr ord).
Proof.
  unfold TView.write_released.
  des_if; ss.
  rewrite Loc_add_eq.
  des_if.
  destruct releasedr; unfold View.unwrap.
  eapply closed_viewInj_join; eauto.
  eapply closed_viewInj_join_singleton; eauto.
  unfold closed_tviewInj in *; ss; des; eauto.
  rewrite View.join_bot_l.
  eapply closed_viewInj_join_singleton; eauto.
  unfold closed_tviewInj in *; ss; des; eauto.
  destruct releasedr; unfold View.unwrap.
  eapply closed_viewInj_join; eauto.
  eapply closed_viewInj_join_singleton; eauto.
  unfold closed_tviewInj in *; ss; des; eauto.
  rewrite View.join_bot_l.
  eapply closed_viewInj_join_singleton; eauto.
  unfold closed_tviewInj in *; ss; des; eauto.
Qed.
 
Ltac solve_timemap_closed :=
  match goal with
  | H: closed_tviewInj _ _ |- _ =>
    inv H; ss; unfold closed_viewInj in *; des; eauto
  | _ => idtac
  end.

Ltac solve_timemap_inj_join :=
  match goal with
  | |- context [View.singleton_ur _ _] => unfold View.singleton_ur; ss; solve_timemap_inj_join
  | |- context [View.singleton_rw _ _] => unfold View.singleton_rw; ss; solve_timemap_inj_join
  | |- context [(TimeMap.join ?lhs TimeMap.bot)] => rewrite TimeMap.join_bot; solve_timemap_inj_join
  | |- closed_TMapInj ?inj (TimeMap.join ?lhs (TimeMap.singleton ?loc ?to)) =>
    eapply closed_TMapinj_join_singletion; eauto; solve_timemap_inj_join 
  | |- TimeMap.join (TimeMap.join ?lhs ?rhs) (TimeMap.join ?lhs' ?rhs) =>
    eapply Montonic_TMapInj_join; eauto; solve_timemap_inj_join
  | |- TMapInj ?inj (TimeMap.join ?lhs (TimeMap.singleton ?loc ?to))
              (TimeMap.join ?rhs (TimeMap.singleton ?loc ?to')) =>
    eapply TMapInj_singleton; eauto; solve_timemap_inj_join
  | |- TMapInj ?inj (TimeMap.join ?lhs ?rhs) (TimeMap.join ?lhs' ?rhs') =>
    eapply Montonic_TMapInj_join; eauto; solve_timemap_inj_join
  | |- closed_TMapInj ?inj ?tm => try solve_timemap_closed 
  | _ => idtac
  end.

Ltac unfold_time_le_join_hyp :=
  match goal with
  | H: Time.le (Time.join ?lhs ?rhs) ?o |- _ => eapply Time_le_join in H; des; unfold_time_le_join_hyp
  | _ => idtac
  end.

Ltac solve_tmapinj tview tview' cur cur0 t t0 :=
    unfold TViewInj in *; unfold ViewInj in *; des; destruct tview, tview'; ss;
    destruct cur, cur0; ss; destruct t, t0; ss; des; ss.
Ltac solve_tmapinj' tview tview' cur cur0 :=
  unfold TViewInj in *; unfold ViewInj in *; des; destruct tview, tview'; ss;
  destruct cur, cur0; ss; des; ss.

Ltac unfold_tviewinj H :=
  unfold TViewInj in H; ss; des; try unfold ViewInj in *; ss.
Ltac unfold_closed_tviewInj H :=
  unfold closed_tviewInj in H; ss; des; unfold closed_viewInj in *; ss; des.

Lemma wf_view_inj_singleton
      view view' inj to to' loc
      (VIEW_INJ : ViewInj inj view view')
      (CLOSED : closed_viewInj inj view)
      (INJ: inj loc to = Some to')
      (MON: monotonic_inj inj)
      (WF: View.wf (View.join view (View.singleton_ur loc to))):
  View.wf (View.join view' (View.singleton_ur loc to')).
Proof.
  unfold View.singleton_ur in *; ss.
  unfold View.join in *; ss.
  inv WF; ss.  
  econs; eauto; ss. 
  unfold TimeMap.le, TimeMap.join in *. ii. specialize (PLN_RLX loc0); ss.
  eapply Time_le_monotonic_inj with (loc := loc0); eauto.
  eapply closed_TMapInj_implies_inj_singleton; eauto.
  unfold_tviewinj VIEW_INJ. clear - VIEW_INJ.  destruct view, view'; ss. des; eauto.
  unfold_closed_tviewInj CLOSED; eauto.
  eapply closed_TMapInj_implies_inj_singleton; eauto.
  unfold_tviewinj VIEW_INJ. clear - VIEW_INJ.  destruct view, view'; ss. des; eauto.
  unfold_closed_tviewInj CLOSED; eauto.
Qed.

Lemma wf_view_inj_join_singleton
      view view' inj t t' to to' loc
      (VIEW_INJ : ViewInj inj view view')
      (VIEW_INJ' : ViewInj inj t t')
      (CLOSED : closed_viewInj inj view)
      (CLOSED_VIEW': closed_viewInj inj t)
      (INJ: inj loc to = Some to')
      (MON: monotonic_inj inj)
      (WF: View.wf (View.join t (View.join view (View.singleton_ur loc to)))):
  View.wf (View.join t' (View.join view' (View.singleton_ur loc to'))).
Proof.
  unfold View.singleton_ur in *; ss.
  unfold View.join in *; ss.
  inv WF; ss.  
  econs; eauto; ss. 
  unfold TimeMap.le, TimeMap.join in *. ii. specialize (PLN_RLX loc0); ss.
  eapply Time_le_monotonic_inj with (loc := loc0); eauto. 
  eapply inj_join_comp; eauto.
  clear - VIEW_INJ' CLOSED_VIEW'. 
  destruct t, t'; ss. des. unfold closed_viewInj in *; ss; des. 
  eapply closed_TMapInj_implies_inj; eauto.
  eapply closed_TMapInj_implies_inj_singleton; eauto.
  unfold_tviewinj VIEW_INJ. clear - VIEW_INJ.  destruct view, view'; ss. des; eauto.
  unfold_closed_tviewInj CLOSED; eauto.
  eapply inj_join_comp; eauto. 
  clear - VIEW_INJ' CLOSED_VIEW'.
  unfold ViewInj, closed_viewInj in *. destruct t, t'; ss; des; eauto.
  unfold TMapInj, closed_TMapInj in *.
  specialize (CLOSED_VIEW'0 loc0). des.
  dup CLOSED_VIEW'0. eapply VIEW_INJ'0 in CLOSED_VIEW'0; eauto. subst; eauto.
  eapply closed_TMapInj_implies_inj_singleton; eauto.
  unfold_tviewinj VIEW_INJ. destruct view, view'; ss. des; eauto.
  unfold closed_tviewInj in *; des. unfold closed_viewInj in *; des; eauto.
Qed.

Lemma View_opt_wf_inj
      tview sc loc to released released' tview' sc' to' inj ord 
      (VIEW_OPT_WF: View.opt_wf (TView.write_released tview sc loc to released ord))
      (TVIEW_INJ: TViewInj inj tview tview')
      (OPT_VIEW_INJ: opt_ViewInj inj released released')
      (CLOSED: closed_tviewInj inj tview)
      (CLOSED_OPT_VIEW: closed_opt_viewinj inj released)
      (INJ: inj loc to = Some to')
      (MON: monotonic_inj inj):
  View.opt_wf (TView.write_released tview' sc' loc to' released' ord).
Proof.
  destruct released in *; destruct released' in *; ss. 
  - unfold TView.write_released in *.
    des_ifH VIEW_OPT_WF; eauto. inv VIEW_OPT_WF.
    econs. ss.
    try rewrite Loc_add_eq in *.  
    des_ifH WF.  
    + eapply wf_view_inj_join_singleton with (t := t) (view := TView.cur tview); eauto.
      unfold TViewInj in *; des; eauto.
      unfold closed_tviewInj in *. des; eauto.
    + eapply wf_view_inj_join_singleton with (t := t) (view := TView.rel tview loc); eauto.
      unfold TViewInj in *; des; eauto.
      unfold closed_tviewInj in *. des; eauto.
  - unfold TView.write_released in *.
    des_ifH VIEW_OPT_WF; eauto. inv VIEW_OPT_WF. ss.
    try rewrite View.join_bot_l in *.
    try rewrite Loc_add_eq in *.
    econs; eauto.
    des_ifH WF.
    + eapply wf_view_inj_singleton; eauto.
      unfold TViewInj in *; des; eauto.
      unfold closed_tviewInj in *. des; eauto.
    + eapply wf_view_inj_singleton; eauto.
      unfold TViewInj in *; des; eauto.
      unfold closed_tviewInj in *. des; eauto.
Qed.

Lemma TView_inj_read_prsv
      tview loc to released ord
      tview' to' released' inj
      (MON: monotonic_inj inj)
      (TVIEW_INJ: TViewInj inj tview tview')
      (CLOSED_TVIEW: closed_tviewInj inj tview)
      (MSG_INJ: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj released released')
      (CLOSE_VIEW: closed_opt_viewinj inj released):
  TViewInj inj (TView.read_tview tview loc to released ord) (TView.read_tview tview' loc to' released' ord).
Proof.
  unfold TView.read_tview. unfold TViewInj; simpl.
  split.
  {
    (* released *)
    ii. unfold TViewInj in TVIEW_INJ. des.
    specialize (TVIEW_INJ loc0); eauto.
  }
  split.
  {
    (* cur *)
    split.
    {
      des_if.
      { 
        unfold View.unwrap. destruct released, released'; ss.
        {
          
          unfold View.singleton_ur_if.
          des_if.
          solve_timemap_inj_join.
          solve_tmapinj tview tview' cur cur0 t t0.
          solve_tmapinj tview tview' cur cur0 t t0.
          solve_timemap_inj_join.
          solve_tmapinj tview tview' cur cur0 t t0.
          solve_tmapinj tview tview' cur cur0 t t0.
        }
        {
          unfold View.singleton_ur_if.
          des_if; ss.
          solve_timemap_inj_join.
          solve_tmapinj' tview tview' cur cur0.
          solve_timemap_inj_join.
          solve_tmapinj' tview tview' cur cur0.
        }
      }
      {
        unfold View.singleton_ur_if; ss.
        des_if; ss.
        solve_timemap_inj_join.
        solve_tmapinj' tview tview' cur cur0.
        solve_timemap_inj_join.
        solve_tmapinj' tview tview' cur cur0.
      }
    }
    {
      des_if; ss.
      {
        unfold View.unwrap. destruct released, released'; ss.
        {
          unfold View.singleton_ur_if.
          des_if.
          solve_timemap_inj_join.
          solve_tmapinj tview tview' cur cur0 t t0.
          solve_tmapinj tview tview' cur cur0 t t0.
          solve_timemap_inj_join.
          solve_tmapinj tview tview' cur cur0 t t0.
          solve_tmapinj tview tview' cur cur0 t t0.
        }
        {
          unfold View.singleton_ur_if.
          des_if.
          solve_timemap_inj_join.
          solve_tmapinj' tview tview' cur cur0.
          solve_timemap_inj_join.
          solve_tmapinj' tview tview' cur cur0.
        }
      }
      {
        unfold View.singleton_ur_if.
        des_if.
        solve_timemap_inj_join.
        solve_tmapinj' tview tview' cur cur0.
        solve_timemap_inj_join.
        solve_tmapinj' tview tview' cur cur0.
      }
    }
  }
  {
    (* acq *)
    split.
    {
      des_if.
      { 
        unfold View.unwrap. destruct released, released'; ss.
        {
          solve_timemap_inj_join. 
          solve_tmapinj tview tview' acq acq0 t t0.
          solve_tmapinj tview tview' acq acq0 t t0.
        }
        {
          solve_timemap_inj_join.
          solve_tmapinj' tview tview' acq acq0.
        }
      }
      {
        unfold View.singleton_ur_if; ss.
        solve_timemap_inj_join.
        solve_tmapinj' tview tview' acq acq0.
      }
    }
    {
      des_if; ss.
      {
        unfold View.unwrap. destruct released, released'; ss.
        {
          solve_timemap_inj_join.
          solve_tmapinj tview tview' acq acq0 t t0.
          solve_tmapinj tview tview' acq acq0 t t0.
        }
        {
          solve_timemap_inj_join.
          solve_tmapinj' tview tview' acq acq0.
        }
      }
      {
        solve_timemap_inj_join.
        solve_tmapinj' tview tview' acq acq0.
      }
    }
  }
Qed.

Lemma TView_inj_write_prsv
      tview loc to sc ord
      tview' to' sc' inj
      (MON: monotonic_inj inj)
      (TVIEW_INJ: TViewInj inj tview tview')
      (CLOSED_TVIEW: closed_tviewInj inj tview)
      (MSG_INJ: inj loc to = Some to'):
  TViewInj inj (TView.write_tview tview sc loc to ord) (TView.write_tview tview' sc' loc to' ord).
Proof.
  unfold TView.write_tview. unfold TViewInj; simpl.
  split.
  {
    ii. inv TVIEW_INJ. des.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      specialize (H loc0).
      repeat (erewrite Loc_add_eq). inv CLOSED_TVIEW; des.
      des_if; try solve [eapply Monotonic_viewInj_join_singleton; eauto].
    }
    {
      repeat (erewrite Loc_add_neq); eauto.
    }
  } 
  split.
  {
    inv TVIEW_INJ. des. clear H. unfold ViewInj in *. destruct tview, tview'; ss.
    destruct cur, cur0, acq, acq0; ss. des.
    inv CLOSED_TVIEW; ss. des.
    unfold closed_viewInj in *. des; ss.
    split; eapply TMapInj_singleton; eauto.
  }
  {
    inv TVIEW_INJ. des. clear H. unfold ViewInj in *. destruct tview, tview'; ss.
    destruct cur, cur0, acq, acq0; ss. des.
    inv CLOSED_TVIEW; ss. des.
    unfold closed_viewInj in *. des; ss.
    split; eapply TMapInj_singleton; eauto.
  }
Qed.

Lemma read_fence_tview_prsv
      tview tview' ord inj
      (TVIEW_INJ: TViewInj inj tview tview'):
  TViewInj inj (TView.read_fence_tview tview ord) (TView.read_fence_tview tview' ord).
Proof.
  unfold TView.read_fence_tview. inv TVIEW_INJ; des.
  econs; eauto; ss.
  split; eauto.
  des_if; eauto.
Qed.
  
Lemma write_fence_tview_not_sc
      ord tview sc
      (ORD: ord <> Ordering.seqcst):
  TView.write_fence_tview tview sc ord =
  {|
    TView.rel := fun l : BinNums.positive =>
                   if Ordering.le Ordering.acqrel ord then (TView.cur tview) else (TView.rel tview) l;
    TView.cur := TView.cur tview;
    TView.acq := TView.acq tview
  |}.
Proof.
  destruct tview.
  unfold TView.write_fence_tview; ss.
  assert(Ordering.le Ordering.seqcst ord = false).
  {
    destruct ord; ss; eauto.
  }
  rewrite H.
  rewrite View.join_bot_r. auto.
Qed.

Lemma TView_inj_fence_prsv
      tview tview' sc sc' ord inj
      (TVIEW_INJ: TViewInj inj tview tview')
      (ORD: ord <> Ordering.seqcst):
  TViewInj inj (TView.write_fence_tview tview sc ord) (TView.write_fence_tview tview' sc' ord).
Proof.
  erewrite write_fence_tview_not_sc; eauto.
  erewrite write_fence_tview_not_sc; eauto.
  destruct tview, tview'; ss.
  inv TVIEW_INJ; ss. des.
  des_if.
  {
    econs; eauto.
  }
  {
    econs; eauto.
  }
Qed.
  
Lemma TLE_write_prs
      tview tview' sc loc to to' releasedr releasedr' ord inj sc'
      (TLE_WRITE: Time.le (View.rlx (View.unwrap (TView.write_released tview sc loc to releasedr ord)) loc) to)
      (INJ: inj loc to = Some to')
      (RELEASE_INJ: opt_ViewInj inj releasedr releasedr')
      (TVIEW_INJ: TViewInj inj tview tview')
      (MON: monotonic_inj inj)
      (CLOSED_TVIEW: closed_tviewInj inj tview)
      (CLOSED_OPT_VIEW: closed_opt_viewinj inj releasedr):
  Time.le (View.rlx (View.unwrap (TView.write_released tview' sc' loc to' releasedr' ord)) loc) to'.
Proof.
  unfold TView.write_released in *.
  des_if; ss.
  {
    des_if; ss.
    {
      try rewrite Loc_add_eq in *.
      destruct releasedr, releasedr'; ss.
      {
        destruct tview, tview'; ss.
        unfold TimeMap.join in *.
        unfold_time_le_join_hyp.
        eapply Time.join_spec; eauto.
        unfold ViewInj in *. destruct t, t0; des; ss.
        clear TLE_WRITE0 TLE_WRITE1.
        eapply monotonic_inj_implies_le_prsv; eauto.
        unfold closed_viewInj in *. des; ss.
        unfold closed_TMapInj in *.
        specialize (CLOSED_OPT_VIEW0 loc). des. rewrite CLOSED_OPT_VIEW0.
        eapply RELEASE_INJ0 in CLOSED_OPT_VIEW0; subst; eauto.
        eapply Time.join_spec; eauto.
        unfold_tviewinj TVIEW_INJ. destruct cur, cur0; ss; des.
        clear TLE_WRITE TLE_WRITE1.
        eapply monotonic_inj_implies_le_prsv; eauto.
        unfold_closed_tviewInj CLOSED_TVIEW.
        unfold closed_TMapInj in CLOSED_TVIEW3. specialize (CLOSED_TVIEW3 loc). des.
        rewrite CLOSED_TVIEW3.
        eapply TVIEW_INJ2 in CLOSED_TVIEW3; eauto; subst; ss.
        unfold TimeMap.singleton in *.
        try rewrite Loc_add_eq in *. eapply Time.le_lteq; eauto.
      }
      {
        try rewrite TimeMap.join_comm in *.
        try rewrite TimeMap.join_bot in *.
        unfold TimeMap.join in *. unfold_time_le_join_hyp.
        eapply Time.join_spec.
        clear TLE_WRITE0.
        eapply monotonic_inj_implies_le_prsv; eauto.
        clear - TVIEW_INJ CLOSED_TVIEW.
        unfold_tviewinj TVIEW_INJ.
        destruct tview, tview'; ss. destruct cur, cur0; ss. des.
        unfold_closed_tviewInj CLOSED_TVIEW.
        unfold closed_TMapInj in CLOSED_TVIEW3. specialize (CLOSED_TVIEW3 loc). des.
        rewrite CLOSED_TVIEW3. eapply TVIEW_INJ2 in CLOSED_TVIEW3. subst; eauto.
        unfold TimeMap.singleton in *.
        try rewrite Loc_add_eq in *. eapply Time.le_lteq; eauto.
      }
    }
    {
      try rewrite Loc_add_eq in *.
      unfold View.singleton_ur in *; ss.
      destruct releasedr, releasedr'; ss.
      {
        destruct tview, tview'; ss.
        unfold TimeMap.join in *.
        unfold_time_le_join_hyp.
        eapply Time.join_spec; eauto.
        unfold ViewInj in *. destruct t, t0; des; ss.
        clear TLE_WRITE0 TLE_WRITE1.
        eapply monotonic_inj_implies_le_prsv; eauto.
        unfold closed_viewInj in *. des; ss.
        unfold closed_TMapInj in *.
        specialize (CLOSED_OPT_VIEW0 loc). des. rewrite CLOSED_OPT_VIEW0.
        eapply RELEASE_INJ0 in CLOSED_OPT_VIEW0; subst; eauto.
        eapply Time.join_spec; eauto.
        unfold_tviewinj TVIEW_INJ.
        clear TLE_WRITE TLE_WRITE1.
        eapply monotonic_inj_implies_le_prsv; eauto.
        unfold_closed_tviewInj CLOSED_TVIEW.
        specialize (CLOSED_TVIEW loc).  des.
        unfold closed_TMapInj in CLOSED_TVIEW4. specialize (CLOSED_TVIEW4 loc). des.
        rewrite CLOSED_TVIEW4.
        specialize (TVIEW_INJ loc). destruct (rel loc), (rel0 loc); ss; des.
        eapply TVIEW_INJ2 in CLOSED_TVIEW4; eauto; subst; ss.
        unfold TimeMap.singleton in *.
        try rewrite Loc_add_eq in *. eapply Time.le_lteq; eauto.
      }
      {
        try rewrite TimeMap.join_comm in *.
        try rewrite TimeMap.join_bot in *.
        unfold TimeMap.join in *. unfold_time_le_join_hyp.
        eapply Time.join_spec.
        clear TLE_WRITE0.
        eapply monotonic_inj_implies_le_prsv; eauto.
        clear - TVIEW_INJ CLOSED_TVIEW.
        unfold_tviewinj TVIEW_INJ.
        destruct tview, tview'; ss. specialize (TVIEW_INJ loc).
        unfold_closed_tviewInj CLOSED_TVIEW.
        specialize (CLOSED_TVIEW loc). des.
        unfold closed_TMapInj in CLOSED_TVIEW4. specialize (CLOSED_TVIEW4 loc). des.
        rewrite CLOSED_TVIEW4.
        destruct (rel loc), (rel0 loc); ss; des.
        eapply TVIEW_INJ2 in CLOSED_TVIEW4. subst; eauto.
        unfold TimeMap.singleton in *.
        try rewrite Loc_add_eq in *. eapply Time.le_lteq; eauto.
      }
    }
  }
  {
    unfold TimeMap.bot; ss. eapply Time.bot_spec.
  }
Qed.
  
(** ** Increasing mapping *)
Definition incr_inj (inj inj': Mapping):Prop :=
  forall loc t t', inj loc t = Some t' -> inj' loc t = Some t'.

Definition eq_inj (inj inj': Mapping): Prop := 
  forall loc t t', inj loc t = Some t' <-> inj' loc t = Some t'.

Definition eq_inj_implies_incr:
  forall inj inj', 
  eq_inj inj inj' -> incr_inj inj inj'.
Proof.
  intros.
  unfold eq_inj in H; unfold incr_inj. eapply H.
Qed.

Lemma incr_inj_refl: 
  forall inj,
  incr_inj inj inj.
Proof.
  intro. unfold incr_inj. intros. trivial.
Qed.

Lemma incr_inj_transitivity
      inj inj' inj''
      (INCR_INJ1: incr_inj inj inj')
      (INCR_INJ2: incr_inj inj' inj''):
  incr_inj inj inj''.
Proof.
  unfold incr_inj in *; ii.
  eapply INCR_INJ1 in H.
  eapply INCR_INJ2 in H.
  eauto.
Qed.

Lemma incr_inj_TMapInj
      inj inj' tm tm'
      (TMAP_INJ: TMapInj inj tm tm')
      (INCR: incr_inj inj inj')
      (CLOSED: closed_TMapInj inj tm):
  TMapInj inj' tm tm'.
Proof.
  unfold TMapInj in *. ii.
  unfold closed_TMapInj in *.
  unfold incr_inj in *.
  destruct (inj loc (tm loc)) eqn:INJ; eauto.
  dup INJ.
  eapply TMAP_INJ in INJ; eauto.
  eapply INCR in INJ0. rewrite INJ0 in injDom; inv injDom. eauto.
  specialize (CLOSED loc); des. rewrite CLOSED in INJ; ss.
Qed.

Lemma incr_inj_closedTMapInj
      inj inj' tm
      (CLOSED: closed_TMapInj inj tm)
      (INCR: incr_inj inj inj'):
  closed_TMapInj inj' tm.
Proof.
  unfold closed_TMapInj in *. ii.
  specialize (CLOSED loc). des; eauto.
Qed.
  
Lemma incr_inj_ViewInj
      inj inj' view view'
      (VIEW_INJ: ViewInj inj view view')
      (INCR: incr_inj inj inj')
      (CLOSED: closed_viewInj inj view):
  ViewInj inj' view view'.
Proof.
  unfold ViewInj in *.
  destruct view, view'; ss. des.
  unfold closed_viewInj in CLOSED; ss. des.
  split; try solve [eapply incr_inj_TMapInj; eauto].
Qed.

Lemma incr_inj_closedViewInj
      inj inj' view
      (CLOSED: closed_viewInj inj view)
      (INCR: incr_inj inj inj'):
  closed_viewInj inj' view.
Proof.
  unfold closed_viewInj in *. des.
  split; try solve [eapply incr_inj_closedTMapInj; eauto].
Qed.

Lemma incr_inj_opt_ViewInj
      inj inj' opt_view opt_view'
      (OPT_VIEW_INJ: opt_ViewInj inj opt_view opt_view')
      (INCR: incr_inj inj inj')
      (CLOSED: closed_opt_viewinj inj opt_view):
  opt_ViewInj inj' opt_view opt_view'.
Proof.
  unfold opt_ViewInj in *.
  destruct opt_view, opt_view'; ss.
  eapply incr_inj_ViewInj; eauto.
Qed.

Lemma incr_inj_closed_opt_ViewInj
      inj inj' opt_view
      (CLOSED: closed_opt_viewinj inj opt_view)
      (INCR: incr_inj inj inj'):
  closed_opt_viewinj inj' opt_view.
Proof.
  unfold closed_opt_viewinj in *.
  destruct opt_view; ss.
  eapply incr_inj_closedViewInj; eauto.
Qed.

Lemma incr_inj_TViewInj
      inj inj' tview tview'
      (TVIEW_INJ: TViewInj inj tview tview')
      (INCR: incr_inj inj inj')
      (CLOSED: closed_tviewInj inj tview):
  TViewInj inj' tview tview'.
Proof.
  unfold TViewInj in *. des.
  unfold closed_tviewInj in *. des.
  split.
  ii. specialize (TVIEW_INJ loc). specialize (CLOSED loc).
  eapply incr_inj_ViewInj; eauto.
  split.
  eapply incr_inj_ViewInj; eauto.
  eapply incr_inj_ViewInj; eauto.
Qed.

Lemma incr_inj_closed_tviewInj
      inj inj' tview
      (CLOSED: closed_tviewInj inj tview)
      (INCR: incr_inj inj inj'):
  closed_tviewInj inj' tview.
Proof.
  unfold closed_tviewInj in *. des.
  split. ii.
  specialize (CLOSED loc).
  eapply incr_inj_closedViewInj; eauto.
  split; eapply incr_inj_closedViewInj; eauto.
Qed.

Lemma writable_inj
      inj tview tview' loc to to'
      (WRITABLE: Time.lt (View.rlx (TView.cur tview) loc) to)
      (TVIEW_INJ: TViewInj inj tview tview')
      (CLOSED_TVIEWINJ: closed_tviewInj inj tview)
      (INJ: inj loc to = Some to')
      (MON: monotonic_inj inj):
  Time.lt (View.rlx (TView.cur tview') loc) to'.
Proof.
  unfold monotonic_inj in *.
  inv TVIEW_INJ; des.
  unfold ViewInj in H0.
  destruct tview, tview'; ss.
  destruct cur, cur0; ss. des.
  unfold TMapInj in H2.
  unfold_closed_tviewInj CLOSED_TVIEWINJ.
  unfold closed_TMapInj in CLOSED_TVIEWINJ3.
  specialize (CLOSED_TVIEWINJ3 loc). des.
  exploit H2; eauto. ii; subst.
  eauto.
Qed.

Lemma opt_ViewInj_write_released_inj
      inj tview tview' sc sc' loc to to' releasedr releasedr' ord
      (TVIEW_INJ: TViewInj inj tview tview')
      (CLOSED_TVIEWINJ: closed_tviewInj inj tview)
      (INJ: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj releasedr releasedr')
      (CLOSED_RELEASEDR: closed_opt_viewinj inj releasedr)
      (MON: monotonic_inj inj):
  opt_ViewInj inj (TView.write_released tview sc loc to releasedr ord)
              (TView.write_released tview' sc' loc to' releasedr' ord).
Proof.
  unfold opt_ViewInj. unfold TView.write_released. des_if; eauto. 
  destruct releasedr, releasedr'; try solve [simpl in VIEW_INJ; ss].
  { 
    unfold View.unwrap. eapply Monotonic_viewInj_join; eauto.
    {
      unfold TView.write_tview; ss. des_if.
      rewrite Loc_add_eq.
      eapply closed_viewInj_join_singleton; eauto.
      inv CLOSED_TVIEWINJ; des; eauto.
      rewrite Loc_add_eq.
      eapply closed_viewInj_join_singleton; eauto.
      inv CLOSED_TVIEWINJ; des; eauto.
    }
    {
      unfold TView.write_tview; ss. do 2 (rewrite Loc_add_eq).
      unfold closed_tviewInj in CLOSED_TVIEWINJ; des.
      unfold TViewInj in TVIEW_INJ; des.
      des_if; eapply Monotonic_viewInj_join_singleton; try solve [eapply incr_inj_closedViewInj; eauto]; eauto.
    }
  }
  {
    unfold View.unwrap. repeat (rewrite View.join_bot_l).
    unfold TView.write_tview; ss. repeat (rewrite Loc_add_eq). 
    unfold closed_tviewInj in CLOSED_TVIEWINJ; des. 
    unfold TViewInj in TVIEW_INJ; des.
    des_if; eapply Monotonic_viewInj_join_singleton; try solve [eapply incr_inj_closedViewInj; eauto]; eauto.
  }
Qed. 

Lemma timemap_le_inj
      tm1 tm1' tm2 tm2' inj
      (TMAPINJ1: TMapInj inj tm1 tm1')
      (TMAPINJ2: TMapInj inj tm2 tm2')
      (CLOSED_TMAPINJ1: closed_TMapInj inj tm1)
      (CLOSED_TMAPINJ2: closed_TMapInj inj tm2)
      (LE: TimeMap.le tm1 tm2)
      (MON: monotonic_inj inj):
  TimeMap.le tm1' tm2'.
Proof.
  unfold TMapInj in *.
  unfold closed_TMapInj in *.
  unfold TimeMap.le in *. ii.
  specialize (LE loc). 
  specialize (CLOSED_TMAPINJ1 loc).
  specialize (CLOSED_TMAPINJ2 loc).
  des.
  exploit TMAPINJ1; eauto; ii; subst.
  exploit TMAPINJ2; eauto; ii; subst.
  eapply Time_le_monotonic_inj; eauto.
Qed.
  
Lemma view_le_inj
      R1 R1' R2 R2' inj
      (VIEWINJ1: ViewInj inj R1 R1')
      (VIEWINJ2: ViewInj inj R2 R2')
      (CLOSED_VIEWINJ1: closed_viewInj inj R1)
      (CLOSED_VIEWINJ2: closed_viewInj inj R2)
      (LE: View.le R1 R2)
      (MON: monotonic_inj inj):
  View.le R1' R2'.
Proof.
  inv LE.
  unfold ViewInj in *. destruct R1, R1'; ss. destruct R2, R2'; ss. des.
  unfold closed_viewInj in *; ss; des.
  econs; eauto; ss; try solve [eapply timemap_le_inj; eauto].
Qed.

Lemma view_opt_le_inj
      released1 released1' released2 released2' inj
      (VIEW_OPT_LE: View.opt_le released1 released2)
      (OPT_RELEASED_INJ1: opt_ViewInj inj released1 released1')
      (OPT_RELEASED_INJ2: opt_ViewInj inj released2 released2')
      (CLOSED_RELEASED1: closed_opt_viewinj inj released1)
      (CLOSED_RELEASED2: closed_opt_viewinj inj released2)
      (MON: monotonic_inj inj):
  View.opt_le released1' released2'.
Proof.
  inv VIEW_OPT_LE.
  {
    unfold opt_ViewInj in *. destruct released1'; ss.
  }
  {
    unfold opt_ViewInj in *. destruct released1'; ss.
    destruct released2'; ss.
    econs.
    eapply view_le_inj; eauto.
  }
Qed.
 
Lemma add_msgInj_stable_concrete
      mem1 loc from to val R mem1'
      mem2 from' to' R' mem2' inj inj'
      (MEM_INJ: MsgInj inj mem1 mem2)
      (ADD1: Memory.add mem1 loc from to (Message.concrete val R) mem1')
      (ADD2: Memory.add mem2 loc from' to' (Message.concrete val R') mem2')
      (OPT_VIEW_INJ: opt_ViewInj inj' R R')
      (INJ_INCR: incr_inj inj inj')
      (MON: monotonic_inj inj')
      (INJ: inj' loc to = Some to')
      (COMPLETE_INJ: forall loc to to', inj' loc to = Some to' ->
                                   exists from val R, Memory.get loc to mem1' = Some (from, Message.concrete val R))
      (CLOSED_MEM: Memory.closed mem1):
  MsgInj inj' mem1' mem2'.
Proof.
  inv MEM_INJ.
  inv CLOSED_MEM.
  econs; ii; eauto.
  {
    erewrite Memory.add_o in MSG; eauto.
    des_ifH MSG; ss; des; subst.
    {
      inv MSG.
      do 3 eexists. split; eauto. split; eauto.
      erewrite Memory.add_o; eauto.
      des_if; eauto; ss; des; ss.
    }
    {
      exploit SOUND; eauto. ii; des.
      do 3 eexists.
      split; eauto. 
      split. eapply incr_inj_opt_ViewInj; eauto.
      eapply CLOSED in MSG. des. inv MSG_CLOSED.
      eapply closed_optview_msginj_implies_closed_viewInj; eauto.
      econs; eauto.
      erewrite Memory.add_o; eauto.
      des_if; ss; des; subst; ss; eauto.
    }
    {
      exploit SOUND; eauto. ii; des.
      do 3 eexists.
      split; eauto.
      split. eapply incr_inj_opt_ViewInj; eauto.
      eapply CLOSED in MSG. des. inv MSG_CLOSED.
      eapply closed_optview_msginj_implies_closed_viewInj; eauto.
      econs; eauto.
      erewrite Memory.add_o; eauto.
      instantiate (1 := f').
      des_if; ss; des; subst; ss.
      assert(to' <> to').
      {
        eapply INJ_INCR in x.
        eapply monotonic_inj_implies_disj_mapping; [eapply MON | eapply INJ | eapply x | eauto..].
      }
      ss.
    }
  }
  {
    eapply COMPLETE_INJ in INJ0. des. eauto.
  }
Qed.

Lemma split_msgInj_stable_concrete
      mem1 loc from to ts val R msg1 mem1'
      mem2 from' to' ts' R' msg2 mem2' inj inj'
      (MEM_INJ: MsgInj inj mem1 mem2)
      (SPLIT1: Memory.split mem1 loc from to ts (Message.concrete val R) msg1 mem1')
      (SPLIT2: Memory.split mem2 loc from' to' ts' (Message.concrete val R') msg2 mem2')
      (OPT_VIEW_INJ: opt_ViewInj inj' R R')
      (INJ_INCR: incr_inj inj inj')
      (MON: monotonic_inj inj')
      (INJ: inj' loc to = Some to')
      (COMPLETE_INJ: forall loc to to',
          inj' loc to = Some to' -> exists from val R, Memory.get loc to mem1' = Some (from, Message.concrete val R))
      (CLOSED_MEM: Memory.closed mem1):
  MsgInj inj' mem1' mem2'.
Proof.
  inv MEM_INJ.
  inv CLOSED_MEM.
  econs; ii; eauto.
  {
    erewrite Memory.split_o in MSG; eauto.
    des_ifH MSG; des; ss; subst; ss.
    {
      inv MSG. 
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
      do 3 eexists.
      split; eauto. 
    }
    {
      des_ifH MSG; ss; des; subst; ss.
      {
        exploit SOUND; eauto. ii; des.
        assert(GET1: Memory.get loc0 t' mem2' = Some (f', Message.concrete val0 R'0)).
        {
          erewrite Memory.split_o; eauto.
          des_if; eauto; ss; des; subst; ss.
          des_if; eauto; ss; des; subst; ss.
          des_if; eauto; ss; des; subst; ss.
        }
        do 3 eexists. split; eauto. split; eauto.
        eapply incr_inj_opt_ViewInj; eauto.
        eapply CLOSED in MSG; eauto. des. inv MSG_CLOSED.
        eapply closed_optview_msginj_implies_closed_viewInj; eauto.
        econs; eauto.
      }
      {
        exploit SOUND; eauto; ii; des.
        exploit Memory.split_get1; [eapply SPLIT2 | eauto..]. ii; des.
        do 3 eexists. split; eauto.
        split; eauto.
        eapply incr_inj_opt_ViewInj; eauto.
        eapply CLOSED in MSG; eauto. des. inv MSG_CLOSED.
        eapply closed_optview_msginj_implies_closed_viewInj; eauto.
        econs; eauto.
      }
    }
    {
      des_ifH MSG; ss; des; subst; ss.
      {
        inv MSG.
        exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
        exploit SOUND; [eapply GET0 | eauto..]. ii; des.
        exploit Memory.split_get1; [eapply SPLIT2 | eauto..]. ii; des.
        do 3 eexists.
        split; eauto.
        split; eauto.
        eapply incr_inj_opt_ViewInj; eauto.
        eapply CLOSED in GET0; eauto. des. inv MSG_CLOSED.
        eapply closed_optview_msginj_implies_closed_viewInj; eauto.
        econs; eauto.
      }
      {
        exploit SOUND; eauto. ii; des.
        exploit Memory.split_get1; eauto. ii; des.
        do 3 eexists. split; eauto. split; eauto.
        eapply incr_inj_opt_ViewInj; eauto.
        eapply CLOSED in MSG; eauto. des. inv MSG_CLOSED.
        eapply closed_optview_msginj_implies_closed_viewInj; eauto.
        econs; eauto.
      }
      {
        exploit SOUND; eauto. ii; des.
        exploit Memory.split_get1; eauto. ii; des.
        do 3 eexists. split; eauto. split; eauto.
        eapply incr_inj_opt_ViewInj; eauto.
        eapply CLOSED in MSG; eauto. des. inv MSG_CLOSED.
        eapply closed_optview_msginj_implies_closed_viewInj; eauto.
        econs; eauto.
      }
    }
  }
  {
    eapply COMPLETE_INJ in INJ0; eauto.
    des. do 3 eexists. eauto.
  }
Qed.

Lemma lower_msgInj_stable_concrete
      mem1 loc from to val R msg1 mem1'
      mem2 from' to' R' msg2 mem2' inj inj'
      (MEM_INJ: MsgInj inj mem1 mem2)
      (LOWER1: Memory.lower mem1 loc from to msg1 (Message.concrete val R) mem1')
      (LOWER2: Memory.lower mem2 loc from' to' msg2 (Message.concrete val R') mem2')
      (OPT_VIEW_INJ: opt_ViewInj inj' R R')
      (INJ_INCR: incr_inj inj inj')
      (MON: monotonic_inj inj')
      (INJ: inj' loc to = Some to')
      (COMPLETE_INJ: forall loc to to',
          inj' loc to = Some to' -> exists from val R, Memory.get loc to mem1' = Some (from, Message.concrete val R))
      (CLOSED_MEM: Memory.closed mem1):
  MsgInj inj' mem1' mem2'.
Proof.
  inv MEM_INJ.
  inv CLOSED_MEM.
  econs; ii; eauto.
  {
    erewrite Memory.lower_o in MSG; eauto.
    des_ifH MSG; ss; des; subst; ss.
    {
      inv MSG.
      exploit Memory.lower_get0; eauto. ii; des.
      exploit Memory.lower_get0; [eapply LOWER2 | eauto..]. ii; des.
      do 3 eexists.
      split; eauto.
    }
    {
      exploit SOUND; [eapply MSG | eauto..]. ii; des.
      assert(GET: Memory.get loc0 t' mem2' = Some (f', Message.concrete val0 R'0)).
      {
        erewrite Memory.lower_o; eauto.
        des_if; des; ss; subst; ss.
      }
      do 3 eexists.
      split; eauto.
      split; eauto.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply CLOSED in MSG; eauto. des. inv MSG_CLOSED.
      eapply closed_optview_msginj_implies_closed_viewInj; eauto.
      econs; eauto.
    }
    {
      exploit SOUND; [eapply MSG | eauto..]. ii; des.
      assert(GET: Memory.get loc0 t' mem2' = Some (f', Message.concrete val0 R'0)).
      {
        erewrite Memory.lower_o; eauto.
        des_if; des; ss; subst; ss.
        eapply INJ_INCR in x.
        clear - MON INJ x o.
        exploit monotonic_inj_implies_disj_mapping; [eapply MON | eapply x | eapply INJ | eauto..].
        ii; ss.
      }
      do 3 eexists.
      split; eauto.
      split; eauto.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply CLOSED in MSG; eauto. des. inv MSG_CLOSED.
      eapply closed_optview_msginj_implies_closed_viewInj; eauto.
      econs; eauto.
    }
  }
  {
    eapply COMPLETE_INJ in INJ0. des. do 3 eexists. eauto.
  }
Qed.

Lemma cancel_msg_stable
      mem1 loc from to mem1'
      mem2 mem2' inj
      (MEM_INJ: MsgInj inj mem1 mem2)
      (CANCEL1: Memory.remove mem1 loc from to Message.reserve mem1')
      (CANCEL2: Memory.remove mem2 loc from to Message.reserve mem2'):
  MsgInj inj mem1' mem2'.
Proof.
  inv MEM_INJ.
  econs; eauto.
  {
    ii.
    dup MSG.
    erewrite Memory.remove_o in MSG; eauto.
    des_ifH MSG; ss.
    exploit SOUND; [eapply MSG | eauto..].
    ii; des.
    do 3 eexists. split; eauto. split; eauto.
    instantiate (1 := f').
    erewrite Memory.remove_o; eauto.
    des_if; des; ss; eauto.
    do 3 eexists. split; eauto. split; eauto.
    instantiate (1 := f').
    erewrite Memory.remove_o; eauto.
    des_if; des; ss; subst; ss.
    exploit Memory.remove_get0; eauto. ii; des.
    rewrite x1 in GET. inv GET.
  }
  {
    ii.
    exploit COMPLETE; eauto. ii; des.
    exists val, f, R.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; ss; eauto; subst.
    exploit Memory.remove_get0; [eapply CANCEL1 | eauto..]. ii; des.
    rewrite x in GET. inv GET.
  }
Qed.
  
Definition kind_match (kind1 kind2: Memory.op_kind) :=
  match kind1, kind2 with
  | Memory.op_kind_add, Memory.op_kind_add => True
  | Memory.op_kind_split to (Message.concrete val R),
    Memory.op_kind_split to' (Message.concrete val' R') => to = to' /\ val = val'
  | Memory.op_kind_lower (Message.concrete val R),
    Memory.op_kind_lower (Message.concrete val' R') => val = val' 
  | Memory.op_kind_cancel, Memory.op_kind_cancel => True
  | _, _ => False
  end.

Lemma write_step_msgInj_stable
      lc1 sc1 mem1 loc from1 to1 val R1 R1' ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 R2 R2' lc2' sc2' mem2' kind2 inj inj'
      (MEM_INJ: MsgInj inj mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val R1 R1' ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val R2 R2' ord lc2' sc2' mem2' kind2 lo)
      (KIND_MATCH: kind_match kind1 kind2)
      (OPT_VIEW_INJ: opt_ViewInj inj' R1' R2')
      (INJ_INCR: incr_inj inj inj')
      (MON: monotonic_inj inj')
      (INJ: inj' loc to1 = Some to2)
      (COMPLETE_INJ: forall loc to to',
          inj' loc to = Some to' -> exists from val R, Memory.get loc to mem1' = Some (from, Message.concrete val R))
      (CLOSED_MEM: Memory.closed mem1):
  MsgInj inj' mem1' mem2'.
Proof.
  inv WRITE1. inv WRITE. inv PROMISE.
  - destruct kind2; ss.
    inv WRITE2. inv WRITE. inv PROMISE.
    eapply add_msgInj_stable_concrete; eauto.
  - des; subst. inv RESERVE.
    destruct kind2; ss.
    destruct msg3; ss. des; subst.
    inv WRITE2. inv WRITE. inv PROMISE.
    des; subst. inv RESERVE. inv RESERVEORIGINAL.
    eapply split_msgInj_stable_concrete; eauto.
  - des; subst.
    destruct kind2; ss.
    destruct msg1; ss; subst; ss.
    inv WRITE2. inv WRITE. inv PROMISE.
    des; subst. inv RESERVE.
    eapply lower_msgInj_stable_concrete; eauto.
  - ss.
Qed.

Lemma wf_inj_incr
      inj loc to to'
      (MON: monotonic_inj inj)
      (NEW: inj loc to = None)
      (WF_ADD1: forall ts ts', inj loc ts = Some ts' -> Time.lt ts to -> Time.lt ts' to')
      (WF_ADD2: forall ts ts', inj loc ts = Some ts' -> Time.lt to ts -> Time.lt to' ts'):
  exists inj',
    <<NEW_INJ: inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)>> /\
    <<MON: monotonic_inj inj'>> /\
    <<INCR_INJ: incr_inj inj inj'>>.
Proof.
  eexists. split. ss. split.
  unfold monotonic_inj in *. ii.
  des_ifH INJ1; ss; des; subst; ss.
  {
    inv INJ1; ss; des; subst.
    des_ifH INJ2; ss; des; subst; ss; eauto.
    inv INJ2. auto_solve_time_rel.
  }
  {
    des_ifH INJ2; ss; des; subst; ss; try solve [eapply MON; eauto].
  }
  {
    des_ifH INJ2; ss; des; subst; ss; try solve [eapply MON; eauto].
    inv INJ2. eauto.
  }
  unfold incr_inj. ii.
  des_if; ss; des; subst; ss.
  rewrite NEW in H. ss.
Qed.

Inductive mem_inj_dom_eq: forall (inj: Mapping) (mem: Memory.t), Prop := 
| mem_inj_dom_eq_intro
    inj mem
    (SOUND: forall loc val f t R 
      (MSG: Memory.get loc t mem = Some (f, Message.concrete val R)),
      exists t',
      inj loc t = Some t'
    )
    (COMPLETE: forall loc t t'
      (INJ: inj loc t = Some t'),
      exists val f R, 
        Memory.get loc t mem = Some (f, Message.concrete val R)):
    mem_inj_dom_eq inj mem.


Definition eq_ident_mapping (inj: Mapping) (mem: Memory.t) : Prop :=
  mem_inj_dom_eq inj mem /\ 
  forall loc t t',
    (inj loc t = Some t') -> 
        <<ID_MAPPING: (t = t')>>.
    
