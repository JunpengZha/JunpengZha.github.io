Require Import Omega.
Require Import RelationClasses.
Require Import Program.

From Paco Require Import paco.
Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Language.
Require Import Loc.

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import PromiseConsistent.
Require Import MemoryMerge.
Require Import Cover.


Set Implicit Arguments.

Ltac dep_clarify :=
  (repeat
     match goal with
     | H:existT ?P ?p ?x = existT ?P ?p ?y |- _ =>
       eapply inj_pair2 in H; subst
     end); ss; clarify.

Ltac dep_inv H :=
  inv H; dep_clarify.

Notation "p \\2// q" :=
  (fun x0 x1 => __guard__(p x0 x1 \/ q x0 x1))
    (at level 50, no associativity).

Notation "p \\3// q" :=
  (fun x0 x1 x2 => __guard__(p x0 x1 x2 \/ q x0 x1 x2))
    (at level 50, no associativity).

Section GENERAL.

  Definition ternary A (b: bool) (a_true a_false: A) :=
    if b then a_true else a_false.

  Lemma option_rel_mon A B (R0 R1: A -> B-> Prop)
        (LE: R0 <2= R1)
    :
      option_rel R0 <2= option_rel R1.
  Proof. i. unfold option_rel in *. des_ifs. auto. Qed.

  Lemma list_filter_exists A (P: A -> Prop) (l: list A)
    :
      exists l',
        (<<COMPLETE: forall a, ((<<IN: List.In a l>>) /\ (<<SAT: P a>>))
                               <-> (<<IN: List.In a l'>>)>>).
  Proof.
    induction l.
    - exists []. ii. split; i; des.
      + inv IN.
      + inv H.
    - des. destruct (classic (P a)).
      + exists (a :: l'). split; i; ss; des; clarify; eauto.
        * right. eapply COMPLETE; eauto.
        * eapply COMPLETE in H0. des. eauto.
      + exists l'. split; i; ss; des; clarify; eauto.
        * eapply COMPLETE; eauto.
        * eapply COMPLETE in H0. des; eauto.
  Qed.

  Lemma or_strengthen A B
        (OR: A \/ B)
  :
    (A \/ ((<<NOT: ~ A>>) /\ (<<SAT: B>>))).
  Proof.
    destruct (classic A); eauto. des; eauto.
  Qed.

  Lemma list_Forall_app A P (l0 l1: list A)
    :
      List.Forall P (l0 ++ l1) <-> (<<FORALL0: List.Forall P l0>> /\ <<FORALL1: List.Forall P l1>>).
  Proof.
    induction l0; split; i; ss.
    - split; auto.
    - des. auto.
    - inv H. apply IHl0 in H3. des. split; auto.
    - des. inv FORALL0. econs; eauto.
  Qed.

  Lemma list_Forall2_app A B P (lhd0 ltl0: list A) (lhd1 ltl1: list B)
        (FORALL0: List.Forall2 P lhd0 lhd1)
        (FORALL1: List.Forall2 P ltl0 ltl1)
    :
      List.Forall2 P (lhd0 ++ ltl0) (lhd1 ++ ltl1).
  Proof.
    ginduction FORALL0; eauto. i. ss. econs; eauto.
  Qed.

  Lemma list_Forall2_in A B P (l0: list A) (l1: list B)
        (FORALL: List.Forall2 P l0 l1)
        b
        (IN: List.In b l1)
    :
      exists a,
        (<<IN: List.In a l0>>) /\ (<<SAT: P a b>>).
  Proof.
    ginduction FORALL; eauto; i; ss. des; clarify.
    - esplits; eauto.
    - eapply IHFORALL in IN; eauto. des. esplits; eauto.
  Qed.

  Lemma list_Forall2_in2 A B P (l0: list A) (l1: list B)
        (FORALL: List.Forall2 P l0 l1)
        a
        (IN: List.In a l0)
    :
      exists b,
        (<<IN: List.In b l1>>) /\ (<<SAT: P a b>>).
  Proof.
    ginduction FORALL; eauto; i; ss. des; clarify.
    - esplits; eauto.
    - eapply IHFORALL in IN; eauto. des. esplits; eauto.
  Qed.

  Lemma list_Forall_sum A (P Q R: A -> Prop) (l: list A)
        (FORALL0: List.Forall P l)
        (FORALL1: List.Forall Q l)
        (SUM: forall a (SAT0: P a) (SAT1: Q a), R a)
    :
      List.Forall R l.
  Proof.
    ginduction l; eauto. i. inv FORALL0. inv FORALL1. econs; eauto.
  Qed.

  Lemma list_Forall2_compose A B C
        (P: A -> B -> Prop) (Q: B -> C -> Prop) (R: A -> C -> Prop)
        (la: list A) (lb: list B) (lc: list C)
        (FORALL0: List.Forall2 P la lb)
        (FORALL1: List.Forall2 Q lb lc)
        (IMPLY: forall a b c (SAT0: P a b) (SAT1: Q b c), R a c)
    :
      List.Forall2 R la lc.
  Proof.
    ginduction la; i.
    { inv FORALL0. inv FORALL1. econs. }
    { inv FORALL0. inv FORALL1. econs; eauto. }
  Qed.

  Lemma list_Forall2_symm A B
        (P: A -> B -> Prop) (Q: B -> A -> Prop)
        (la: list A) (lb: list B)
        (FORALL: List.Forall2 P la lb)
        (IMPLY: forall a b (SAT: P a b), Q b a)
    :
      List.Forall2 Q lb la.
  Proof.
    ginduction la; i.
    { inv FORALL. econs. }
    { inv FORALL. econs; eauto. }
  Qed.

  Lemma list_Forall2_rev A B
        (P: A -> B -> Prop)
        (la: list A) (lb: list B)
        (FORALL: List.Forall2 P la lb)
    :
      List.Forall2 (fun b a => P a b) lb la.
  Proof.
    ginduction la; i.
    { inv FORALL. econs. }
    { inv FORALL. econs; eauto. }
  Qed.

  Lemma list_Forall2_impl A B (P Q: A -> B -> Prop) (la: list A) (lb: list B)
        (FORALL: List.Forall2 P la lb)
        (IMPL: forall a b (SAT: P a b), Q a b)
    :
      List.Forall2 Q la lb.
  Proof.
    revert lb FORALL. induction la.
    { i. inv FORALL. econs. }
    { i. inv FORALL. econs; eauto. }
  Qed.

  Lemma list_match_rev A (l: list A)
    :
      l = [] \/ exists tl_rev hd_rev, l = tl_rev++[hd_rev].
  Proof.
    induction l; auto. des; subst.
    { right. exists []. ss. eauto. }
    { right. esplits. erewrite List.app_comm_cons. eauto. }
  Qed.

  Lemma list_first_occurence A (P: A -> Prop) (l: list A)
    :
      (<<ALL: List.Forall P l>>) \/
      (exists l0 a l1,
          (<<EQ: l = l0 ++ a :: l1>>) /\
          (<<ALL: List.Forall P l0>>) /\
          (<<FAIL: ~ P a>>)).
  Proof.
    induction l.
    { left. ss. }
    { destruct (classic (P a)).
      { des; eauto. subst.
        right. exists (a::l0), a0, l1. esplits; eauto. }
      { right. exists [], a, l. splits; auto. }
    }
  Qed.

  Lemma list_filter_idempotent A P (l: list A)
    :
      List.filter P (List.filter P l) = List.filter P l.
  Proof.
    induction l; eauto. ss. des_ifs. ss. des_ifs. f_equal; auto.
  Qed.

  Lemma list_filter_app A P (l0 l1: list A)
    :
      List.filter P (l0 ++ l1) = (List.filter P l0) ++ (List.filter P l1) .
  Proof.
    induction l0; eauto. ss. des_ifs. ss. f_equal; auto.
  Qed.

  Lemma list_filter_forall A P (Q R: A -> Prop) (l: list A)
        (FORALL: List.Forall Q l)
        (REL: forall a (SAT0: P a = true) (SAT1: Q a), R a)
    :
      List.Forall R (List.filter P l).
  Proof.
    induction l; ss. inv FORALL. des_ifs; eauto.
  Qed.

  Lemma list_map_forall A B (P: A -> Prop) (Q: B -> Prop) f (l: list A)
        (FORALL: List.Forall P l)
        (REL: forall a (SAT: P a), Q (f a))
    :
      List.Forall Q (List.map f l).
  Proof.
    induction l; ss. inv FORALL. eauto.
  Qed.

End GENERAL.


Section CELL.

  Inductive times_sorted: list Time.t -> Prop :=
  | times_sorted_nil
    :
      times_sorted []
  | times_sorted_cons
      hd tl
      (HD: List.Forall (Time.lt hd) tl)
      (TL: times_sorted tl)
    :
      times_sorted (hd :: tl)
  .
  Hint Constructors times_sorted.

  Fixpoint insert (to: Time.t) (l: list Time.t): list Time.t :=
    match l with
    | [] => [to]
    | hd :: tl =>
      match (Time.le_lt_dec to hd) with
      | left LE => match (Time.eq_dec to hd) with
                   | left EQ => hd :: tl
                   | right LT => to :: hd :: tl
                   end
      | right LT => hd :: (insert to tl)
      end
    end.

  Fixpoint sorting (l: list Time.t): list Time.t :=
    match l with
    | [] => []
    | hd :: tl => insert hd (sorting tl)
    end.

  Lemma insert_complete a l
    :
      forall b, List.In b (insert a l) <-> (a = b \/ List.In b l).
  Proof.
    ginduction l; ss. i. des_ifs; ss.
    - split; i; des; eauto.
    - split; i; des; eauto.
      + eapply IHl in H. des; eauto.
      + clarify. right. eapply IHl; eauto.
      + right. eapply IHl; eauto.
  Qed.

  Lemma insert_sorted a l
        (SORTED: times_sorted l)
    :
      times_sorted (insert a l).
  Proof.
    ginduction l; ss.
    - i. econs; ss.
    - i. des_ifs.
      + econs; eauto. inv SORTED. econs.
        * destruct l0; clarify.
        * eapply List.Forall_impl; cycle 1; eauto.
          i. eapply TimeFacts.le_lt_lt; eauto.
      + econs.
        * inv SORTED.
          eapply List.Forall_forall. i.
          eapply insert_complete in H. des; clarify.
          eapply List.Forall_forall in HD; eauto.
        * inv SORTED. eapply IHl; eauto.
  Qed.

  Lemma sorting_sorted l
    :
      (<<COMPLETE: forall a, List.In a l <-> List.In a (sorting l)>>) /\
      (<<SORTED: times_sorted (sorting l)>>).
  Proof.
    induction l; ss.
    - split; i; ss.
    - i. des. splits.
      + i. erewrite insert_complete.
        split; i; des; eauto.
        * right. eapply COMPLETE; eauto.
        * right. eapply COMPLETE; eauto.
      + eapply insert_sorted; eauto.
  Qed.

  Inductive disjoint_cell_msgs: list (Time.t * Time.t * Message.t) -> Prop :=
  | disjoint_cell_msgs_nil
    :
      disjoint_cell_msgs []
  | disjoint_cell_msgs_cons
      from to msg tl
      (HD: List.Forall (fun ftm =>
                          match ftm with
                          | (f, t, m) => Time.le to f
                          end) tl)
      (TL: disjoint_cell_msgs tl)
    :
      disjoint_cell_msgs ((from, to, msg) :: tl)
  .


  Definition wf_cell_msgs l :=
    (<<DISJOINT: disjoint_cell_msgs l>>) /\
    (<<MSGSWF: List.Forall (fun ftm =>
                              match ftm with
                              | (from, to, msg) =>
                                (<<MSGWF: Message.wf msg>>) /\
                                (<<TS: (from = Time.bot /\ to = Time.bot) \/ (Time.lt from to)>>)
                              end) l>>)
  .

  Lemma cell_finite_sound_exists c
    :
      exists dom,
        (<<COMPLETE: forall to,
            (List.In to dom <-> exists from msg,
                (<<GET: Cell.get to c = Some (from, msg)>>))>>).
  Proof.
    generalize (Cell.finite c). i. des.
    generalize (list_filter_exists (fun to => exists from msg, (<<GET: Cell.get to c = Some (from, msg)>>)) dom). i. des.
    exists l'. i. split; i.
    - eapply COMPLETE in H0. des. eauto.
    - eapply COMPLETE. splits; eauto.
      des. eapply H; eauto.
  Qed.

  Lemma wf_cell_msgs_exists c
    :
      exists l,
        (<<COMPLETE:
           forall from to msg,
             (<<GET: Cell.get to c = Some (from, msg)>>) <->
             (<<IN: List.In (from, to, msg) l>>)>>) /\
        (<<WFMSGS: wf_cell_msgs l>>).
  Proof.
    generalize (cell_finite_sound_exists c). i. des.
    generalize (sorting_sorted dom). i. des.
    assert (COMPLETE1: forall a, List.In a (sorting dom) <->
                                 exists from msg,
                                   (<<GET: Cell.get a c = Some (from, msg)>>)).
    { i. split; i.
      - eapply COMPLETE0 in H. eapply COMPLETE in H. eauto.
      - eapply COMPLETE0. eapply COMPLETE. eauto. }
    remember (sorting dom). clear - SORTED COMPLETE1.
    exists (List.map (fun to => match (Cell.get to c) with
                                | Some (from, msg) => (from, to, msg)
                                | None => (to, Time.bot, Message.reserve)
                                end) l).
    ginduction l; ss.
    - i. splits.
      + ii. split; clarify.
        i. eapply COMPLETE1. eauto.
      + econs.
        * econs.
        * econs.
    - i. hexploit (proj1 (COMPLETE1 a)); eauto. i. des.
      hexploit Cell.remove_exists; eauto. i. des.
      hexploit (IHl cell2).
      { inv SORTED. eauto. }
      { i. split; i.
        - hexploit (proj1 (COMPLETE1 a0)); eauto. i. des.
          exists from0, msg0. erewrite Cell.remove_o; eauto. des_ifs.
          exfalso. inv SORTED.
          eapply List.Forall_forall in H0; eauto.
          eapply Time.lt_strorder; eauto.
        - des. erewrite Cell.remove_o in GET0; eauto. des_ifs.
          hexploit (proj2 (COMPLETE1 a0)); eauto.
          i. des; clarify. }
      i. des. rewrite GET in *.
      replace (List.map
                 (fun to0 =>
                    match Cell.get to0 c with
                    | Some (from1, msg1) => (from1, to0, msg1)
                    | None => (to0, Time.bot, Message.reserve)
                    end) l) with
          (List.map
             (fun to0 =>
                match Cell.get to0 cell2 with
                | Some (from1, msg1) => (from1, to0, msg1)
                | None => (to0, Time.bot, Message.reserve)
                end) l); cycle 1.
      { eapply List.map_ext_in. i.
        erewrite (@Cell.remove_o cell2); eauto.
        des_ifs. exfalso. inv SORTED.
        eapply List.Forall_forall in H0; eauto.
        eapply Time.lt_strorder; eauto. }
      assert (COMPLETE2:
                forall from0 to msg0,
                  Cell.get to c = Some (from0, msg0) <->
                  (from, a, msg) = (from0, to, msg0) \/
                  List.In (from0, to, msg0)
                          (List.map
                             (fun to0 =>
                                match Cell.get to0 cell2 with
                                | Some (from1, msg1) => (from1, to0, msg1)
                                | None => (to0, Time.bot, Message.reserve)
                                end) l)).
      { i. split; i.
        - generalize (Cell.remove_o to H). intros GET0.
          des_ifs; eauto. right.
          rewrite H0 in GET0. eapply COMPLETE in GET0. eauto.
        - des; clarify.
          eapply (proj2 (COMPLETE from0 to msg0)) in H0.
          erewrite Cell.remove_o in H0; eauto. des_ifs. }
      splits; auto.
      unfold wf_cell_msgs in WFMSGS. des. econs; eauto.
      + econs; eauto. inv SORTED.
        eapply List.Forall_forall. i.
        eapply List.in_map_iff in H0. des.
        erewrite Cell.remove_o in H0; eauto. des_ifs.
        * dup GET. eapply Cell.get_ts in GET0. des; clarify.
          { eapply Time.bot_spec. }
          destruct (Time.le_lt_dec a t0); auto. exfalso.
          exploit Cell.get_disjoint.
          { eapply GET. }
          { eapply Heq0. }
          i. des; clarify. eapply x0.
          { instantiate (1:=a). econs; ss. refl. }
          { econs; ss.
            eapply List.Forall_forall in HD; eauto. left. auto. }
        * refl.
        * exfalso. hexploit (proj1 (COMPLETE1 t0)); eauto.
          i. des. clarify.
      + econs; eauto. splits.
        { eapply Cell.get_opt_wf; eauto. }
        { eapply Cell.get_ts; eauto. }
  Qed.

  Lemma finite_greatest P (l: list Time.t)
    :
      (exists to,
          (<<SAT: P to>>) /\
          (<<IN: List.In to l>>) /\
          (<<GREATEST: forall to'
                              (IN: List.In to' l)
                              (SAT: P to'),
              Time.le to' to>>)) \/
      (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
  Proof.
    induction l.
    - right. ii. inv IN.
    - destruct (classic (P a)).
      + des.
        * destruct (Time.le_lt_dec to a).
          { left. exists a. esplits; ss; eauto.
            i. des; clarify; eauto. refl.
            eapply GREATEST in IN0; eauto. eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2; eauto. }
          { left. exists to. esplits; ss; eauto.
            i. des; clarify; eauto. left. eauto. }
        * left. exists a. esplits; ss; eauto.
          i. des; clarify.
          { refl. }
          { exfalso. eapply EMPTY; eauto. }
      + des.
        * left. esplits; ss; eauto.
          i. des; clarify. eapply GREATEST; eauto.
        * right. ii. ss. des; clarify.
          eapply EMPTY; eauto.
  Qed. 

  Lemma cell_elements_greatest cell P
    :
      (exists to from msg,
          (<<GET: Cell.get to cell = Some (from, msg)>>) /\
          (<<SAT: P to>>) /\
          (<<GREATEST: forall to' from' msg'
                              (GET': Cell.get to' cell = Some (from', msg'))
                              (SAT: P to'),
              Time.le to' to>>)) \/
      (<<EMPTY: forall to from msg
                       (GET: Cell.get to cell = Some (from, msg)),
          ~ P to>>).
  Proof.
    hexploit (Cell.finite cell). i. des.
    hexploit (finite_greatest (fun to => P to /\ exists from msg, Cell.get to cell = Some (from, msg)) dom).
    i. des.
    - left. esplits; eauto. i.
      dup GET'. eapply H in GET'. eauto.
    - right. ii. dup GET. eapply H in GET0.
      eapply EMPTY in GET0. eapply GET0.
      esplits; eauto.
  Qed.

  Lemma finite_least P (l: list Time.t)
    :
      (exists to,
          (<<SAT: P to>>) /\
          (<<IN: List.In to l>>) /\
          (<<LEAST: forall to'
                           (IN: List.In to' l)
                           (SAT: P to'),
              Time.le to to'>>)) \/
      (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
  Proof.
    induction l.
    - right. ii. inv IN.
    - destruct (classic (P a)).
      + des.
        * destruct (Time.le_lt_dec a to).
          { left. exists a. esplits; ss; eauto.
            i. des; clarify; eauto. refl.
            eapply LEAST in IN0; eauto. eapply DenseOrder.DenseOrder_le_PreOrder_obligation_2; eauto.
          }
          { left. exists to. esplits; ss; eauto.
            i. des; clarify; eauto. left. eauto. }
        * left. exists a. esplits; ss; eauto.
          i. des; clarify.
          { refl. }
          { exfalso. eapply EMPTY; eauto. }
      + des.
        * left. esplits; ss; eauto.
          i. des; clarify. eapply LEAST; eauto.
        * right. ii. ss. des; clarify.
          eapply EMPTY; eauto.
  Qed.

  Lemma cell_elements_least cell P
    :
      (exists to from msg,
          (<<GET: Cell.get to cell = Some (from, msg)>>) /\
          (<<SAT: P to>>) /\
          (<<LEAST: forall to' from' msg'
                           (GET': Cell.get to' cell = Some (from', msg'))
                           (SAT: P to'),
              Time.le to to'>>)) \/
      (<<EMPTY: forall to from msg
                       (GET: Cell.get to cell = Some (from, msg)),
          ~ P to>>).
  Proof.
    hexploit (Cell.finite cell). i. des.
    hexploit (finite_least (fun to => P to /\ exists from msg, Cell.get to cell = Some (from, msg)) dom).
    i. des.
    - left. esplits; eauto. i.
      dup GET'. eapply H in GET'. eauto.
    - right. ii. dup GET. eapply H in GET0.
      eapply EMPTY in GET0. eapply GET0.
      esplits; eauto.
  Qed.

End CELL.



Section MEMORYLEMMAS. 

  (* to0 < from1 ==> (from0, to0) # (from1, to1)  *)
  Lemma interval_le_disjoint from0 from1 to0 to1
        (TS: Time.le to0 from1)
  :
    Interval.disjoint (from0, to0) (from1, to1).
  Proof.
    ii. inv LHS. inv RHS. ss.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply FROM0. } etrans.
    { eapply TO. }
    { eauto. }
  Qed. 

  Lemma disjoint_equivalent from0 to0 from1 to1
  :
    (<<INTERSECT: ~ Interval.disjoint (from0, to0) (from1, to1)>>) <->
    ((<<TS0: Time.lt from0 to0>>) /\ (<<TS1: Time.lt from1 to1>>) /\
     (<<TS0: Time.lt (Time.join from0 from1) (Time.meet to0 to1)>>)).
  Proof.
    split; i. des.
    - unfold Interval.disjoint in H.
      eapply not_all_ex_not in H. des.
      dup H. eapply not_imply_elim in H. eapply not_imply_elim2 in H0.
      apply NNPP in H0.
      destruct H. destruct H0. ss. splits.
      + eapply TimeFacts.lt_le_lt; eauto.
      + eapply TimeFacts.lt_le_lt; eauto.
      + unfold Time.join, Time.meet. des_ifs.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
    - des. ii. eapply H.
      + instantiate (1:=Time.meet to0 to1). econs; ss.
        * unfold Time.join, Time.meet in *. des_ifs.
          eapply TimeFacts.le_lt_lt; eauto.
        * eapply Time.meet_l.
      + econs; ss.
        * unfold Time.join, Time.meet in *. des_ifs.
          etrans; eauto.
        * eapply Time.meet_r.
  Qed.

  Lemma disjoint_equivalent2 from0 to0 from1 to1
    :
      (<<DISJOINT: Interval.disjoint (from0, to0) (from1, to1)>>) <->
      ((<<TS0: ~ Time.lt from0 to0>>) \/ (<<TS1: ~ Time.lt from1 to1>>) \/
       (<<TS0: Time.le (Time.meet to0 to1) (Time.join from0 from1)>>)).
  Proof.
    set (disjoint_equivalent from0 to0 from1 to1).
    eapply not_iff_compat in i. split; i.
    - des. hexploit i.
      { ii. clarify. } i.
      apply not_and_or in H0. des; eauto.
      apply not_and_or in H0. des; eauto.
      right. right. red.
      destruct (Time.le_lt_dec (Time.meet to0 to1) (Time.join from0 from1)); eauto.
      exfalso. eauto.
    - destruct i. hexploit H1.
      { ii. des; eauto. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. }
      ii. eauto.
  Qed.

  (* a message is whether a initial message or insert message *)
  Lemma memory_get_ts_strong loc to mem from msg
        (GET: Memory.get loc to mem = Some (from, msg))
    :
      (from = Time.bot /\ to = Time.bot) \/
      ((<<TS: Time.lt from to>>) /\ (<<TO: to <> Time.bot>>)).
  Proof.
    apply Memory.get_ts in GET.
    destruct (classic (to = Time.bot)); clarify.
    - des; clarify; eauto.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
    - des; clarify. right. eauto.
  Qed.

  Lemma memory_get_from_inj mem loc from to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from, msg0))
        (GET1: Memory.get loc to1 mem = Some (from, msg1))
    :
      (<<TO: to0 = to1>>) \/
      (((<<BOT: to0 = Time.bot>>) \/ (<<BOT: to1 = Time.bot>>)) /\ (<<BOT: from = Time.bot>>) /\
       (<<TO: to0 <> to1>>)).
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify; eauto.
      eapply memory_get_ts_strong in GET0.
      eapply memory_get_ts_strong in GET1.
      des; clarify; eauto.
      { right. esplits; eauto. }
      { right. esplits; eauto. }
      exfalso. eapply x0.
      + instantiate (1:=Time.meet to0 to1). econs; ss; eauto.
        * unfold Time.meet. des_ifs.
        * eapply Time.meet_l.
      + econs; ss; eauto.
        * unfold Time.meet. des_ifs.
        * eapply Time.meet_r.
  Qed.

  Lemma memory_get_to_mon mem loc from0 from1 to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (TO: Time.lt from0 from1)
    :
      Time.lt to0 to1.
  Proof. 
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify.
      + exfalso. eapply Time.lt_strorder. eauto.
      + dup GET0. dup GET1.
        eapply memory_get_ts_strong in GET0.
        eapply memory_get_ts_strong in GET1.
        des; clarify.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * hexploit (Time.bot_spec from1). i.
          destruct H; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
          eapply Time.Time.lt_strorder_obligation_2; eauto.
        * eapply disjoint_equivalent2 in x0. des; clarify.
          unfold Time.meet, Time.join in *. des_ifs; eauto.
          { destruct l; eauto. destruct H; eauto. clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          { destruct l; eauto. destruct H; eauto. clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto.
            eapply Time.Time.lt_strorder_obligation_2; eauto. }
  Qed. 

  Lemma memory_get_from_mon mem loc from0 from1 to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (TO: Time.lt to0 to1)
    :
      Time.le to0 from1.
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify.
      + exfalso. eapply Time.lt_strorder. eauto.
      + dup GET0. dup GET1.
        eapply memory_get_ts_strong in GET0.
        eapply memory_get_ts_strong in GET1.
        des; clarify.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * apply Time.bot_spec.
        * destruct (Time.le_lt_dec to0 from1); auto. exfalso.
          eapply x0.
          { instantiate (1:=to0).
            econs; ss. refl. }
          { econs; ss. left. auto. }
  Qed.

  Lemma closed_point mem loc from
        to
        (TS: Time.lt from to)
        (COVERED: forall t (ITV: Interval.mem (from, to) t), covered loc t mem)
    :
      exists from' to' msg,
        (<<GET: Memory.get loc to' mem = Some (from', msg)>>) /\
        (<<TS0: Time.le from' from>>) /\
        (<<TS1: Time.lt from to'>>).
  Proof.
    hexploit (cell_elements_least
                (mem loc)
                (fun to' =>
                   exists from' msg',
                     (<<GET: Memory.get loc to' mem = Some (from', msg')>>) /\
                     (<<FROMLE: Time.lt from to'>>))). i. des.
    - destruct (Time.le_lt_dec from' from).
      + esplits; eauto.
      + exfalso. exploit (COVERED (Time.meet from' to)).
        * unfold Time.meet. des_ifs; econs; ss. refl.
        * i. inv x0. inv ITV. ss.
          exploit LEAST; try apply GET1; eauto.
          { esplits; try apply GET1.
            eapply TimeFacts.lt_le_lt; [|apply TO].
            unfold Time.meet. des_ifs. }
          { i. setoid_rewrite GET0 in GET. clarify.
            exploit memory_get_to_mon.
            - eapply GET1.
            - eapply GET0.
            - unfold Time.meet in FROM. des_ifs. etrans; eauto.
            - i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. }
    - exfalso. exploit (COVERED to).
      + econs; ss. refl.
      + i. inv x0. inv ITV. ss.
        eapply EMPTY; eauto. esplits; eauto.
        eapply TimeFacts.lt_le_lt; eauto.
  Qed.

  Lemma memory_get_ts_le loc to mem from msg
        (GET: Memory.get loc to mem = Some (from, msg))
    :
      Time.le from to.
  Proof.
    eapply Memory.get_ts in GET. des; clarify.
    - refl.
    - left. auto.
  Qed.

  Lemma memory_get_disjoint_strong mem loc from0 to0 from1 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
    :
      (to0 = to1 /\ from0 = from1 /\ msg0 = msg1) \/
      (<<TS: Time.le to0 from1>> /\ <<TS: Time.lt to0 to1>>) \/
      (<<TS: Time.le to1 from0>> /\ <<TS: Time.lt to1 to0>>).
  Proof.
    destruct (Time.le_lt_dec to0 to1).
    { destruct l.
      { dup H. eapply memory_get_from_mon in H; eauto. }
      { inv H. clarify. auto. }
    }
    { dup l. eapply memory_get_from_mon in l; eauto. }
  Qed.

  Lemma max_concrete_timemap_get mem tm loc to from val released
        (MAX: Memory.max_concrete_timemap mem tm)
        (GET: Memory.get loc to mem = Some (from, Message.concrete val released))
    :
      Time.le to (tm loc).
  Proof.
    specialize (MAX loc). inv MAX. eapply MAX0; eauto.
  Qed.

  Lemma le_inhabited mem0 mem1
        (INHABITED: Memory.inhabited mem0)
        (MLE: Memory.le mem0 mem1)
    :
      Memory.inhabited mem1.
  Proof.
    ii. eapply MLE; eauto.
  Qed.

  Lemma remove_le mem0 loc from to msg mem1
        (REMOVE: Memory.remove mem0 loc from to msg mem1)
  :
    Memory.le mem1 mem0.
  Proof.
    ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
  Qed.

  Lemma step_promises_le lang (th0 th1: Thread.t lang) e lo
        (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
        (STEP: Thread.step_allpf lo e th0 th1)
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
  Proof.
    inv STEP. inv STEP0.
    - inv STEP. inv LOCAL. ss.
      eapply Memory.promise_le; eauto.
    - inv STEP. inv LOCAL; ss.
      + inv LOCAL0; ss.
      + inv LOCAL0. ss. inv WRITE.
        eapply Memory.promise_le in PROMISE; eauto. red in PROMISE.
        eapply remove_le in REMOVE.
        etrans; eauto.
      + inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        eapply Memory.promise_le in PROMISE; eauto. red in PROMISE.
        eapply remove_le in REMOVE.
        etrans; eauto.
      + inv LOCAL0; ss.
      + inv LOCAL0; ss.
  Qed.

  Lemma inhabited_future mem1 mem2
        (FUTURE: Memory.future mem1 mem2)
        (INHABITED: Memory.inhabited mem1)
  :
    Memory.inhabited mem2.
  Proof.
    induction FUTURE; auto. apply IHFUTURE.
    inv H. hexploit Memory.op_inhabited; eauto.
  Qed.

  Lemma memory_le_get_none msrc mtgt loc to
        (MLE: Memory.le msrc mtgt)
        (NONE: Memory.get loc to mtgt = None)
    :
      Memory.get loc to msrc = None.
  Proof.
    destruct (Memory.get loc to msrc) eqn:GET; auto.
    destruct p. eapply MLE in GET. clarify.
  Qed.

  Lemma memory_le_covered msrc mtgt loc to
        (MLE: Memory.le msrc mtgt)
        (COVERED: covered loc to msrc)
    :
      covered loc to mtgt.
  Proof.
    inv COVERED. econs; eauto.
  Qed.

  Lemma memory_add_cover_disjoint mem0 loc from to msg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        t
        (IN: Interval.mem (from, to) t)
    :
      ~ covered loc t mem0.
  Proof.
    ii. inv H. dup ADD. eapply Memory.add_get0 in ADD. des.
    exploit Memory.get_disjoint.
    + eapply Memory.add_get1; eauto.
    + eauto.
    + i. des; clarify. eauto.
  Qed.

  Definition attatched_time (mem: Memory.t) (loc: Loc.t) (to: Time.t) :=
    exists to' msg, <<GET: Memory.get loc to' mem = Some (to, msg)>>.

  Lemma write_succeed_valid prom mem1 loc from1 to1 val released
        (MLE: Memory.le prom mem1)
        (NCOVER: forall t (COVER: covered loc t mem1),
            ~ Interval.mem (from1, to1) t)
        (TO: Time.le (View.rlx (View.unwrap released) loc) to1)
        (FROMTO: Time.lt from1 to1)
        (NOATTATCH: ~ attatched_time mem1 loc to1)
        (MSGWF: Message.wf (Message.concrete val released))
    :
      exists mem2,
        (<<WRITE: Memory.write prom mem1 loc from1 to1 val released prom mem2 Memory.op_kind_add>>).
  Proof.
    exploit Memory.add_exists; eauto.
    { instantiate (1:=mem1). instantiate (1:=loc).
      ii. eapply NCOVER; eauto. econs; eauto. }
    i. des. exists mem2.
    exploit Memory.add_exists_le; eauto. i. des.
    econs.
    - econs; eauto; ss.
      i. eapply NOATTATCH; eauto. econs; eauto.
    - exploit Memory.remove_exists; eauto.
      { eapply Memory.add_get0 in x1. des. eauto. } i. des.
      exploit MemoryFacts.MemoryFacts.add_remove_eq; eauto.
      i. clarify.
  Qed.

  Lemma write_disjoint promises1 mem1 loc from1 to1 val released promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (WRITE: Memory.write
                  promises1 mem1 loc from1 to1 val released promises3 mem2 kind)
        to
        (INT: Interval.mem (from1, to1) to)
    :
      (<<PROMISED: covered loc to promises1>>) \/
      (<<NEWMSG: ~ covered loc to mem1>>).
  Proof.
    inv WRITE. inv PROMISE.
    - right. ii. inv H. inv MEM. inv ADD.
      exploit DISJOINT; eauto.
    - left. dup PROMISES. eapply Memory.split_get0 in PROMISES. des.
      econs; eauto.
      inv INT. inv PROMISES0. inv SPLIT. econs; ss.
      etrans; eauto. left. auto.
    - left. dup PROMISES. eapply Memory.lower_get0 in PROMISES. des.
      econs; eauto.
    - clarify.
  Qed. 

  Lemma write_msg_wf v prom v' prom'
        loc from to val releasedm released ord sc sc' mem_tgt mem_tgt' kind lo
        (WRITE: Local.write_step
                  (Local.mk v prom) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind lo)
    :
      (<<TLE: Time.le
                (View.rlx (View.unwrap (TView.write_released v sc loc to releasedm ord)) loc) to>>) /\
      (<<FROMTO: Time.lt from to>>) /\
      (<<MSGWF: Message.wf (Message.concrete val (TView.write_released v sc loc to releasedm ord))>>) /\
      (<<NOATTATCH: forall (KIND: kind = Memory.op_kind_add), ~ attatched_time mem_tgt loc to>>)
  .
  Proof.
    inv WRITE. inv WRITE0. inv PROMISE.
    - inv TS. inv MEM. inv ADD. esplits; eauto. ii. clarify.
      unfold attatched_time in *. des. exploit ATTACH; eauto.
    - inv TS. inv MEM. inv SPLIT. esplits; eauto. ii. clarify.
    - inv TS. inv MEM. inv LOWER. esplits; eauto. ii. clarify.
    - clarify.
  Qed.

  Lemma memory_write_bot_add
        mem1 loc from1 to1 val released promises3 mem2 kind
        (WRITE: Memory.write
                  Memory.bot mem1 loc from1 to1 val released promises3 mem2 kind)
    :
      kind = Memory.op_kind_add.
  Proof.
    inv WRITE. inv PROMISE; auto.
    - exfalso. eapply Memory.split_get0 in PROMISES. des.
      rewrite Memory.bot_get in *. clarify.
    - exfalso. eapply Memory.lower_get0 in PROMISES. des.
      rewrite Memory.bot_get in *. clarify.
    - clarify.
  Qed.

  Lemma add_succeed_wf mem1 loc from to msg mem2
        (ADD: Memory.add mem1 loc from to msg mem2)
    :
      (<<DISJOINT: forall to2 from2 msg2
                          (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)>>) /\
      (<<TO1: Time.lt from to>>) /\
      (<<MSG_WF: Message.wf msg>>).
  Proof.
    inv ADD. inv ADD0. esplits; eauto.
  Qed.

  Lemma lower_succeed_wf mem1 loc from to msg1 msg2 mem2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
    :
      (<<GET: Memory.get loc to mem1 = Some (from, msg1)>>) /\
      (<<TS: Time.lt from to>>) /\
      (<<MSG_WF: Message.wf msg2>>) /\
      (<<MSG_LE: Message.le msg2 msg1>>).
  Proof.
    inv LOWER. inv LOWER0. esplits; eauto.
  Qed.

  Lemma split_succeed_wf mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      (<<GET2: Memory.get loc ts3 mem1 = Some (ts1, msg3)>>) /\
      (<<TS12: Time.lt ts1 ts2>>) /\
      (<<TS23: Time.lt ts2 ts3>>) /\
      (<<MSG_WF: Message.wf msg2>>).
  Proof.
    inv SPLIT. inv SPLIT0. esplits; eauto.
  Qed.

  Lemma promise_include_boundary prom0 mem0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (BOTNONE: Memory.bot_none prom0)
    :
      Interval.mem (from, to) to.
  Proof.
    econs; ss; [|refl]. inv PROMISE.
    - eapply add_succeed_wf in MEM. des. auto.
    - eapply split_succeed_wf in MEM. des. auto.
    - eapply Memory.lower_get0 in PROMISES. des.
      dup GET. eapply Memory.get_ts in GET1. des; clarify.
      rewrite BOTNONE in *. clarify.
    - eapply Memory.remove_get0 in PROMISES. des.
      dup GET. eapply Memory.get_ts in GET1. des; clarify.
      rewrite BOTNONE in *. clarify.
  Qed.

  Lemma promise_wf_event prom0 mem0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (INHABITED: Memory.inhabited mem0)
    :
      Time.lt from to.
  Proof.
    inv PROMISE.
    - eapply add_succeed_wf in PROMISES. des. eauto.
    - eapply split_succeed_wf in PROMISES. des. eauto.
    - eapply lower_succeed_wf in PROMISES. des. eauto.
    - eapply Memory.remove_get0 in MEM. des. dup GET.
      eapply memory_get_ts_strong in GET. des; auto.
      clarify. erewrite INHABITED in GET1. clarify.
  Qed.

  Lemma write_wf_event prom0 mem0 loc from to val released prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc from to val released prom1 mem1 kind)
        (INHABITED: Memory.inhabited mem0)
    :
      Time.lt from to.
  Proof.
    inv WRITE. eapply promise_wf_event; eauto.
  Qed.

  Lemma lower_remove_exists mem1 loc from to msg1 msg2
        (GET: Memory.get loc to mem1 = Some (from, msg1))
        (TLT: Time.lt from to)
        (MSGWF: Message.wf msg2)
        (MSGLE: Message.le msg2 msg1)
    :
      exists mem2 mem3,
        (<<LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2>>) /\
        (<<REMOVE: Memory.remove mem2 loc from to msg2 mem3>>) /\
        (<<SPEC: forall l t,
             Memory.get l t mem3 =
             if loc_ts_eq_dec (l, t) (loc, to) then None else Memory.get l t mem1>>).
  Proof.
    exploit Memory.lower_exists; eauto. i. des.
    dup x0. eapply Memory.lower_get0 in x0. des.
    exploit Memory.remove_exists.
    { eapply GET1. }
    i. des.
    esplits; eauto.
    i. erewrite (@Memory.remove_o mem0 mem2); eauto.
    erewrite (@Memory.lower_o mem2 mem1); eauto. des_ifs.
  Qed.

  Lemma lower_remove_remove mem1 mem2 mem3 loc from to msg1 msg2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
        (REMOVE: Memory.remove mem2 loc from to msg2 mem3)
    :
      Memory.remove mem1 loc from to msg1 mem3.
  Proof.
    dup LOWER. eapply Memory.lower_get0 in LOWER0. des.
    exploit Memory.remove_exists.
    { eapply GET. }
    i. des.
    replace mem3 with mem0; auto.
    eapply Memory.ext. i.
    erewrite (@Memory.remove_o mem0 mem1); eauto.
    erewrite (@Memory.remove_o mem3 mem2); eauto.
    erewrite (@Memory.lower_o mem2 mem1); eauto.
    des_ifs.
  Qed.

  Lemma split_remove_exists mem1 loc ts1 ts2 ts3 msg2 msg3
        (GET: Memory.get loc ts3 mem1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSGWF: Message.wf msg2)
    :
      exists mem2 mem3,
        (<<SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2>>) /\
        (<<REMOVE: Memory.remove mem2 loc ts1 ts2 msg2 mem3>>).
  Proof.
    exploit Memory.split_exists; eauto. i. des.
    dup x0. eapply Memory.split_get0 in x0. des.
    exploit Memory.remove_exists.
    { eapply GET2. }
    i. des. esplits; eauto.
  Qed.

  Lemma split_remove_shorten mem1 loc ts1 ts2 ts3 msg2 msg3 mem2 mem3
        (REMOVE: Memory.remove mem2 loc ts1 ts2 msg2 mem3)
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      forall l t,
        Memory.get l t mem3 =
        if loc_ts_eq_dec (l, t) (loc, ts3) then Some (ts2, msg3) else Memory.get l t mem1.
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    i. erewrite (@Memory.remove_o mem3 mem2); eauto.
    erewrite (@Memory.split_o mem2 mem1); eauto. des_ifs; ss; des; clarify.
  Qed.

  Lemma memory_op_le mem_src0 mem_tgt0 loc from to msg mem_src1 mem_tgt1 kind
        (MLE: Memory.le mem_src0 mem_tgt0)
        (OPSRC: Memory.op mem_src0 loc from to msg mem_src1 kind)
        (OPTGT: Memory.op mem_tgt0 loc from to msg mem_tgt1 kind)
    :
      Memory.le mem_src1 mem_tgt1.
  Proof.
    inv OPSRC; inv OPTGT.
    - ii. erewrite Memory.add_o in LHS; eauto.
      erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
    - ii. erewrite Memory.split_o in LHS; eauto.
      erewrite Memory.split_o; cycle 1; eauto. des_ifs; eauto.
    - ii. erewrite Memory.lower_o in LHS; eauto.
      erewrite Memory.lower_o; cycle 1; eauto. des_ifs; eauto.
    - ii. erewrite Memory.remove_o in LHS; eauto.
      erewrite Memory.remove_o; cycle 1; eauto. des_ifs; eauto.
  Qed.

  Lemma max_concrete_ts_le_max_ts mem loc ts
        (MAX: Memory.max_concrete_ts mem loc ts)
    :
      Time.le ts (Memory.max_ts loc mem).
  Proof.
    inv MAX. des.
    eapply Memory.max_ts_spec in GET. des; auto.
  Qed.

End MEMORYLEMMAS.


Section VIEW.


  Lemma time_join_mon t0 t1 t0' t1'
        (TS0: Time.le t0 t0')
        (TS1: Time.le t1 t1')
    :
      Time.le (Time.join t0 t1) (Time.join t0' t1').
  Proof.
    unfold Time.join. des_ifs.
    - left. eapply TimeFacts.le_lt_lt; eauto.
    - etrans; eauto.
  Qed.

  Lemma timemap_join_mon tm0 tm1 tm0' tm1'
        (TM0: TimeMap.le tm0 tm0')
        (TM1: TimeMap.le tm1 tm1')
    :
      TimeMap.le (TimeMap.join tm0 tm1) (TimeMap.join tm0' tm1').
  Proof.
    unfold TimeMap.join. ii.
    eapply time_join_mon; eauto.
  Qed.

  Lemma view_join_mon vw0 vw1 vw0' vw1'
        (VW0: View.le vw0 vw0')
        (VW1: View.le vw1 vw1')
    :
      View.le (View.join vw0 vw1) (View.join vw0' vw1').
  Proof.
    inv VW0. inv VW1. econs.
    - eapply timemap_join_mon; eauto.
    - eapply timemap_join_mon; eauto.
  Qed.

  Lemma view_ur_rw_le loc ts
    :
      View.le (View.singleton_rw loc ts) (View.singleton_ur loc ts).
  Proof.
    unfold View.singleton_rw, View.singleton_ur. econs; ss; eauto.
    - eapply TimeMap.bot_spec.
    - refl.
  Qed.

  Lemma read_tview_mon
        tview1 tview2 loc ts released1 released2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (REL: View.opt_le released1 released2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.read_tview tview1 loc ts released1 ord1)
      (TView.read_tview tview2 loc ts released2 ord2).
  Proof.
    unfold TView.read_tview, View.singleton_ur_if.
    inv TVIEW. econs; ss.
    - eapply view_join_mon.
      + eapply view_join_mon; eauto. inv ORD.
        des_ifs; eauto.
        * refl.
        * exfalso. destruct ord1, ord2; ss.
        * apply view_ur_rw_le.
        * refl.
      + des_ifs.
        * eapply View.unwrap_opt_le; eauto.
        * exfalso. destruct ord1, ord2; ss.
        * apply View.bot_spec.
        * refl.
    - eapply view_join_mon.
      + eapply view_join_mon; eauto. inv ORD.
        des_ifs; eauto.
        * refl.
        * exfalso. destruct ord1, ord2; ss.
        * apply view_ur_rw_le.
        * refl.
      + des_ifs.
        * eapply View.unwrap_opt_le; eauto.
        * exfalso. destruct ord1, ord2; ss.
        * apply View.bot_spec.
        * refl.
  Qed.

  Lemma write_tview_mon_same_ord
        tview1 tview2 sc1 sc2 loc ts ord
        (TVIEW: TView.le tview1 tview2)
        (SC: TimeMap.le sc1 sc2)
    :
      TView.le
        (TView.write_tview tview1 sc1 loc ts ord)
        (TView.write_tview tview2 sc1 loc ts ord).
  Proof.
    unfold TView.write_tview.
    inv TVIEW. econs; ss.
    - i. unfold LocFun.find, LocFun.add. des_ifs.
      + eapply view_join_mon; eauto. refl.
      + eapply view_join_mon; eauto. refl.
    - eapply view_join_mon; eauto. refl.
    - eapply view_join_mon; eauto. refl.
  Qed.

  Lemma write_tview_mon_same_ord'
        tview1 tview2 sc1 sc2 loc ts ord
        (TVIEW: TView.le tview1 tview2)
    :
      TView.le
        (TView.write_tview tview1 sc1 loc ts ord)
        (TView.write_tview tview2 sc2 loc ts ord).
  Proof.
    unfold TView.write_tview.
    inv TVIEW. econs; ss.
    - i. unfold LocFun.find, LocFun.add. des_ifs.
      + eapply view_join_mon; eauto. refl.
      + eapply view_join_mon; eauto. refl.
    - eapply view_join_mon; eauto. refl.
    - eapply view_join_mon; eauto. refl.
  Qed.

  Lemma read_fence_tview_mon_same_ord
        tview1 tview2 ord
        (TVIEW: TView.le tview1 tview2)
    :
      TView.le
        (TView.read_fence_tview tview1 ord)
        (TView.read_fence_tview tview2 ord).
  Proof.
    unfold TView.read_fence_tview.
    inv TVIEW. econs; ss.
    des_ifs.
  Qed.

  Lemma write_fence_fc_mon_same_ord
        tview1 tview2 ord sc1 sc2
        (SC: TimeMap.le sc1 sc2)
        (TVIEW: TView.le tview1 tview2)
    :
      TimeMap.le
        (TView.write_fence_sc tview1 sc1 ord)
        (TView.write_fence_sc tview2 sc2 ord).
  Proof.
    inv TVIEW. inv CUR.
    unfold TView.write_fence_sc. des_ifs.
    eapply timemap_join_mon; eauto.
  Qed.

  Lemma write_fence_tview_mon_same_ord
        tview1 tview2 ord sc1 sc2
        (SC: TimeMap.le sc1 sc2)
        (TVIEW: TView.le tview1 tview2)
    :
      TView.le
        (TView.write_fence_tview tview1 sc1 ord)
        (TView.write_fence_tview tview2 sc2 ord).
  Proof.
    unfold TView.write_fence_tview.
    dup TVIEW. inv TVIEW. econs; ss.
    - i. unfold LocFun.find, LocFun.add. des_ifs; eauto.
      econs; ss.
      + eapply write_fence_fc_mon_same_ord; eauto.
      + eapply write_fence_fc_mon_same_ord; eauto.
    - des_ifs.
      econs; ss.
      + eapply write_fence_fc_mon_same_ord; eauto.
      + eapply write_fence_fc_mon_same_ord; eauto.
    - des_ifs.
      + eapply view_join_mon; eauto.
        econs; ss.
        * eapply write_fence_fc_mon_same_ord; eauto.
        * eapply write_fence_fc_mon_same_ord; eauto.
      + eapply view_join_mon; eauto. refl.
  Qed.

  Lemma write_fence_tview_mon_same_ord_not_scfence
        tview1 tview2 ord sc1 sc2
        (TVIEW: TView.le tview1 tview2)
        (NOT_SC: ord <> Ordering.seqcst)
    :
      TView.le
        (TView.write_fence_tview tview1 sc1 ord)
        (TView.write_fence_tview tview2 sc2 ord).
  Proof.
    unfold TView.write_fence_tview.
    inv TVIEW.
    destruct ord; ss.
    - des_ifs. econs; ss.
      ii. repeat (rewrite View.join_bot_r); eauto.
    - des_ifs.
      repeat (rewrite View.join_bot_r); eauto.
      econs; ss.
    - des_ifs.
      repeat (rewrite View.join_bot_r); eauto.
      econs; ss.
    - des_ifs.
      repeat (rewrite View.join_bot_r); eauto.
      econs; ss.
  Qed.

End VIEW.


Section UNCHANGABLES.

  Inductive unchangable (mem prom: Memory.t) (l: Loc.t) (t: Time.t) (from: Time.t) (msg: Message.t): Prop :=
  | unchangable_intro
      (GET: Memory.get l t mem = Some (from, msg))
      (NPROM: Memory.get l t prom = None)
  .

  Inductive unwritable (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unwritable_intro
      to from msg
      (UNCH: unchangable mem prom l to from msg)
      (ITV: Interval.mem (from, to) t)
  .

  Lemma unwritable_covered prom mem loc to
        (UNWRITABLE: unwritable mem prom loc to)
    :
      covered loc to mem.
  Proof.
    inv UNWRITABLE. inv UNCH. econs; eauto.
  Qed.

  Inductive unchangable_ts (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unchangable_ts_intro
      from msg
      (UNCH: unchangable mem prom l t from msg)
  .

  Lemma unchangable_promise mem0 prom0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
    :
      unchangable mem0 prom0 <4= unchangable mem1 prom1.
  Proof.
    ii. inv PR. inv PROMISE.
    - econs.
      + eapply Memory.add_get1; eauto.
      + eapply Memory.add_get0 in MEM. erewrite Memory.add_o; eauto.
        des_ifs. ss. des. clarify.
    - econs.
      + erewrite Memory.split_o; eauto. eapply Memory.split_get0 in MEM.
        des. des_ifs.
        * ss. des. clarify.
        * ss. destruct a. clarify. eapply Memory.split_get0 in PROMISES. des; clarify.
      + eapply Memory.split_get0 in MEM. des.
        erewrite Memory.split_o; eauto.
        eapply Memory.split_get0 in PROMISES.
        des_ifs; ss; des; clarify.
    - econs.
      + erewrite Memory.lower_o; eauto. eapply Memory.lower_get0 in MEM.
        des. des_ifs. ss. des. clarify. exfalso.
        eapply Memory.lower_get0 in PROMISES. des. clarify.
      + erewrite Memory.lower_o; eauto.
        eapply Memory.lower_get0 in PROMISES.
        des_ifs. ss. des. clarify.
    - econs.
      + erewrite Memory.remove_o; eauto. eapply Memory.remove_get0 in MEM.
        des. des_ifs. ss. des. clarify. exfalso.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
      + erewrite Memory.remove_o; eauto.
        eapply Memory.remove_get0 in PROMISES. des_ifs.
  Qed.

  Lemma unchangable_remove mem prom0 loc from to msg prom1
        (PROMISE: Memory.remove prom0 loc from to msg prom1)
    :
      unchangable mem prom0 <4= unchangable mem prom1.
  Proof.
    ii. inv PR. econs; eauto.
    erewrite Memory.remove_o; eauto. des_ifs.
  Qed.

  Lemma unchangable_increase pf e lang (th0 th1: Thread.t lang) lo
        (STEP: Thread.step lo pf e th0 th1)
    :
      unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) <4=
      unchangable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    inv STEP.
    - inv STEP0; ss. inv LOCAL. i.
      hexploit unchangable_promise; eauto.
    - i. inv STEP0; ss. inv LOCAL; try inv LOCAL0; ss.
      + inv WRITE. exploit unchangable_promise; eauto.
        eapply unchangable_remove; eauto.
      + inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        exploit unchangable_promise; eauto.
        eapply unchangable_remove; eauto.
  Qed.

  Lemma other_promise_unchangable c tid1 tid2 st1 st2 lc1 lc2
        (CWF: Configuration.wf c)
        (TID1: IdentMap.find tid1 (Configuration.threads c) = Some (st1, lc1))
        (TID2: IdentMap.find tid2 (Configuration.threads c) = Some (st2, lc2))
        (DIFF: tid1 <> tid2)
        l t from msg
        (GET: Memory.get l t (Local.promises lc2) = Some (from, msg))
    :
      unchangable (Configuration.memory c) (Local.promises lc1) l t from msg.
  Proof.
    inv CWF. inv WF. destruct st1, st2. econs; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF. eauto.
    - destruct (Memory.get l t (Local.promises lc1)) eqn:GET0; eauto. exfalso.
      exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ. destruct p.
      inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply Memory.get_ts in GET. eapply Memory.get_ts in GET0. des; clarify.
      eapply x1; eauto.
      + instantiate (1:=t). econs; ss; eauto. refl.
      + econs; ss; eauto. refl.
  Qed.

  Definition promise_not_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | _ => True
    end.

  Lemma step_promise_not_in_other_msgs
        promises1 mem1 loc from1 to1 msg promises3 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind)
    :
      ~ unchangable_ts mem1 promises1 loc to1.
  Proof.
    ii. inv H. inv UNCH. inv PROMISE.
    - dup GET. eapply Memory.add_get1 in GET; eauto.
      eapply Memory.add_get0 in MEM. des. clarify.
    - dup GET. eapply Memory.split_get1 in GET; eauto.
      eapply Memory.split_get0 in MEM. des. clarify.
    - dup GET. eapply Memory.lower_get1 in GET; eauto.
      eapply Memory.lower_get0 in MEM. des. clarify.
      eapply Memory.lower_get0 in PROMISES. des. clarify.
    - eapply Memory.remove_get0 in PROMISES. des. clarify.
  Qed.

  Definition unwritable2 (mem prom: Memory.t) (l: Loc.t) (t: Time.t) :=
    (<<COV: covered l t mem>>) /\
    (<<NCOV: ~ covered l t prom>>).

  Lemma unwritable_eq mem prom
        (MLE: Memory.le prom mem)
        l t
    :
      unwritable mem prom l t <-> unwritable2 mem prom l t.
  Proof.
    split; i.
    - inv H. inv UNCH. econs.
      + econs; eauto.
      + ii. inv H.
        exploit Memory.get_disjoint.
        { eapply MLE. eapply GET0. }
        { eapply GET. }
        i. des; clarify.
        eapply x0; eauto.
    - inv H. inv H0. econs; eauto. econs; eauto.
      destruct (Memory.get l to prom) eqn:GET0; auto. destruct p. exfalso.
      dup GET0. eapply MLE in GET0. clarify. eapply H1. econs; eauto.
  Qed.

  Lemma step_write_not_in_promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (PROMISE: Memory.promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind)
        t
        (IN: Interval.mem (from1, to1) t)
    :
      ~ unwritable mem1 promises1 loc t.
  Proof.
    rewrite unwritable_eq; auto.
    unfold unwritable2. apply or_not_and. inv PROMISE.
    - left. ii. inv H. dup GET. eapply Memory.add_get1 in GET; eauto.
      eapply Memory.add_get0 in MEM. des.
      exploit Memory.get_disjoint.
      + eapply GET.
      + eapply GET2.
      + i. des; clarify. eauto.
    - right. eapply Memory.split_get0 in PROMISES. des. ii. apply H.
      econs; eauto. inv IN. econs; ss; eauto. etrans; eauto.
      inv MEM. inv SPLIT. left. eauto.
    - right. eapply Memory.lower_get0 in PROMISES. des. ii. apply H.
      econs; eauto.
    - right. eapply Memory.remove_get0 in PROMISES. des. ii. apply H.
      econs; eauto.
  Qed.

  Lemma step_write_not_in_write promises1 mem1 loc from1 to1 val released promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (WRITE: Memory.write promises1 mem1 loc from1 to1 val released promises3 mem2 kind)
        t
        (IN: Interval.mem (from1, to1) t)
    :
      ~ unwritable mem1 promises1 loc t.
  Proof.
    inv WRITE. eapply step_write_not_in_promise; eauto.
  Qed.

  Lemma unwritable_increase pf e lang (th0 th1: Thread.t lang) lo
        (STEP: Thread.step lo pf e th0 th1)
    :
      unwritable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
      unwritable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    ii. inv PR.
    eapply unchangable_increase in UNCH; eauto.
    econs; eauto.
  Qed.

  Lemma rtc_unwritable_increase lang (th0 th1: Thread.t lang) lo
        (STEP: rtc (Thread.tau_step (lang:=lang) lo) th0 th1)
    :
      unwritable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
      unwritable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    induction STEP; eauto.
    i. inv H. inv TSTEP. eapply IHSTEP. eapply unwritable_increase; eauto.
  Qed.

  Lemma other_promise_unwritable c tid1 tid2 st1 st2 lc1 lc2
        (CWF: Configuration.wf c)
        (TID1: IdentMap.find tid1 (Configuration.threads c) = Some (st1, lc1))
        (TID2: IdentMap.find tid2 (Configuration.threads c) = Some (st2, lc2))
        (DIFF: tid1 <> tid2)
        l t
        (COV: covered l t (Local.promises lc2))
    :
      unwritable (Configuration.memory c) (Local.promises lc1) l t.
  Proof.
    inv CWF. inv WF. inv COV. destruct st1, st2.
    rewrite unwritable_eq; cycle 1.
    { exploit THREADS; try apply TID1. i. inv x1. auto. }
    unfold unwritable2. esplits; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF.
      econs; eauto.
    - ii. inv H. exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ.
      inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply x1; eauto.
  Qed.

  Inductive unreadable (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unreadable_intro
      (UNWRITABLE: unwritable mem prom l t)
      (NOTCONCRETE: forall
          from val released
          (GET: Memory.get l t mem = Some (from, Message.concrete val released)), False)
  .

  Lemma unreadable_increase pf e lang (th0 th1: Thread.t lang) lo
        (STEP: Thread.step lo pf e th0 th1)
    :
      unreadable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
      unreadable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    ii. inv PR. inv UNWRITABLE.
    dup UNCH. eapply unchangable_increase in UNCH; eauto. split.
    { econs; eauto. }
    { ii. inv UNCH. exploit Memory.get_disjoint.
      { eapply GET. }
      { eapply GET0. }
      i. des.
      { subst. eapply NOTCONCRETE; eauto.
        inv UNCH0. eauto. }
      { eapply x2; eauto. econs; ss; [|refl].
        eapply memory_get_ts_strong in GET. des; auto.
        subst. inv ITV. ss. inv FROM. }
    }
  Qed.

  Lemma rtc_unreadable_increase lang (th0 th1: Thread.t lang) lo
        (STEP: rtc (Thread.tau_step (lang:=lang) lo) th0 th1)
    :
      unreadable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
      unreadable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    induction STEP; eauto.
    i. inv H. inv TSTEP. eapply IHSTEP. eapply unreadable_increase; eauto.
  Qed.

  Lemma promise_write_not_in_covered prom0 prom1 mem0 mem1 MSGS
        loc from to msg kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (NOTIN: kind = Memory.op_kind_add ->
                forall ts (ITV: Interval.mem (from, to) ts), ~ MSGS loc ts)
        l t
        (COVERED: covered l t mem1)
    :
      covered l t mem0 \/ ~ MSGS l t.
  Proof.
    inv PROMISE.
    { erewrite add_covered in COVERED; eauto. des; auto.
      subst. right. eapply NOTIN; eauto. }
    { erewrite split_covered in COVERED; eauto. }
    { erewrite lower_covered in COVERED; eauto. }
    { erewrite remove_covered in COVERED; eauto. des; auto. }
  Qed.

End UNCHANGABLES.


Section PROMISED.

  Inductive promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
  | promised_intro
      msg
      (GET: Memory.get loc to mem = Some msg)
    :
      promised mem loc to
  .

  Inductive concrete_promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
  | concrete_promised_intro
      from val released
      (GET: Memory.get loc to mem = Some (from, Message.concrete val released))
  .

  Inductive concrete_covered (prom mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  | concrete_covered_intro
      max
      (MAX: Memory.max_concrete_ts mem loc max)
      (COVERED: covered loc to prom)
      (TS: Time.le to max)
  .

  Lemma concrete_covered_covered prom mem loc to
        (COVERED: concrete_covered prom mem loc to)
    :
      covered loc to prom.
  Proof.
    inv COVERED. auto.
  Qed.

  Lemma concrete_promised_increase_promise promises1 mem1 loc from to msg promises2 mem2 kind
        (STEP: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
    :
      concrete_promised mem1 <2= concrete_promised mem2.
  Proof.
    inv STEP.
    - ii. inv PR.
      exploit Memory.add_get1; eauto. i.
      econs; eauto.
    - ii. inv PR.
      exploit Memory.split_get1; eauto. i. des.
      econs; eauto.
    - ii. inv PR.
      exploit Memory.lower_get1; eauto. i. des.
      inv MSG_LE. econs; eauto.
    - ii. inv PR. econs; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; eauto.
      eapply Memory.remove_get0 in MEM. ss; des; clarify.
  Qed.

  Lemma concrete_promised_increase lang (th0 th1: Thread.t lang) pf e lo
        (STEP: Thread.step lo pf e th0 th1)
    :
      concrete_promised (Thread.memory th0) <2= concrete_promised (Thread.memory th1).
  Proof.
    i. inv STEP.
    - inv STEP0. ss. inv LOCAL.
      eapply concrete_promised_increase_promise; eauto.
    - inv STEP0; ss. inv LOCAL; ss.
      + inv LOCAL0. inv WRITE.
        eapply concrete_promised_increase_promise; eauto.
      + inv LOCAL1. inv LOCAL2. inv WRITE.
        eapply concrete_promised_increase_promise; eauto.
  Qed.

  Lemma rtc_concrete_promised_increase lang (th0 th1: Thread.t lang) lo
        (STEP: rtc (@Thread.tau_step lang lo) th0 th1)
    :
      concrete_promised (Thread.memory th0) <2= concrete_promised (Thread.memory th1).
  Proof.
    ginduction STEP; auto. i. eapply IHSTEP.
    inv H. inv TSTEP. eapply concrete_promised_increase; eauto.
  Qed.

  Lemma configuration_step_concrete_promised_increase c0 c1 e tid
        (STEP: Configuration.step e tid c0 c1)
    :
      concrete_promised (Configuration.memory c0) <2= concrete_promised (Configuration.memory c1).
  Proof.
    inv STEP; ss.
    { i. eapply rtc_concrete_promised_increase in STEPS; eauto.
      inv STEP0.
      inv TSTEP.
      exploit concrete_promised_increase; eauto. }
    { i. eapply rtc_concrete_promised_increase in STEPS; eauto.
      inv STEP_OUT.
      exploit concrete_promised_increase; eauto.
      eapply Thread.step_program; eauto. ss. }
    { ii. rewrite C2; ss. }
  Qed.

  Lemma memory_future_concrete_promised mem0 mem1
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      concrete_promised mem0 <2= concrete_promised mem1.
  Proof.
    ii. inv PR. eapply FUTURE in GET. des.
    { econs; eauto. }
    { econs; eauto. }
  Qed.

End PROMISED.


Lemma promise_memory_le prom0 mem0 loc from to msg prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
  :
    Memory.le prom1 mem1.
Proof.
  inv PROMISE.
  - ii. erewrite Memory.add_o in LHS; eauto.
    erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.split_o in LHS; eauto.
    erewrite Memory.split_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.lower_o in LHS; eauto.
    erewrite Memory.lower_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.remove_o in LHS; eauto.
    erewrite Memory.remove_o; cycle 1; eauto. des_ifs; eauto.
Qed.

Lemma write_memory_le prom0 mem0 loc from to val released prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (PROMISE: Memory.write prom0 mem0 loc from to val released prom1 mem1 kind)
  :
    Memory.le prom1 mem1.
Proof.
  inv PROMISE. etrans.
  - eapply remove_le; eauto.
  - eapply promise_memory_le; eauto.
Qed.

Lemma step_memory_le lang (th0 th1: Thread.t lang) pf e lo
      (STEP: Thread.step lo pf e th0 th1)
      (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
Proof.
  inv STEP.
  - inv STEP0. ss. inv LOCAL.
    eapply promise_memory_le; eauto.
  - inv STEP0. ss. inv LOCAL; ss; try (inv LOCAL0; ss).
    + eapply write_memory_le; eauto.
    + inv LOCAL1. inv LOCAL2. ss.
      eapply write_memory_le; eauto.
Qed.

Definition no_reserves (proms: Memory.t): Prop :=
  forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
    msg <> Message.reserve.

Definition memory_concrete_le (lhs rhs: Memory.t): Prop :=
  forall loc to from val released
         (GET: Memory.get loc to lhs = Some (from, Message.concrete val released)),
    Memory.get loc to rhs = Some (from, Message.concrete val released).
Global Program Instance concrete_le_PreOrder: PreOrder memory_concrete_le.
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

Lemma memory_concrete_le_le
  :
    Memory.le <2= memory_concrete_le.
Proof.
  ii. eauto.
Qed.
Hint Resolve memory_concrete_le_le.

Lemma memory_concrete_le_closed_timemap tm mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (TM: Memory.closed_timemap tm mem0)
  :
    Memory.closed_timemap tm mem1.
Proof.
  ii. hexploit (TM loc). i. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_closed_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_view vw mem0)
  :
    Memory.closed_view vw mem1.
Proof.
  inv VW. econs.
  - eapply memory_concrete_le_closed_timemap; eauto.
  - eapply memory_concrete_le_closed_timemap; eauto.
Qed.

Lemma memory_concrete_le_closed_opt_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_opt_view vw mem0)
  :
    Memory.closed_opt_view vw mem1.
Proof.
  inv VW; econs.
  eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_closed_msg msg mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (MSG: Memory.closed_message msg mem0)
  :
    Memory.closed_message msg mem1.
Proof.
  inv MSG; econs.
  eapply memory_concrete_le_closed_opt_view; eauto.
Qed.

Lemma memory_concrete_le_closed_tview vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: TView.closed vw mem0)
  :
    TView.closed vw mem1.
Proof.
  inv VW. econs.
  - i. eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_local_wf lc mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (PROM: Memory.le (Local.promises lc) mem1)
      (LOCAL: Local.wf lc mem0)
  :
    Local.wf lc mem1.
Proof.
  inv LOCAL. econs; eauto.
  eapply memory_concrete_le_closed_tview; eauto.
Qed.


Section CANCEL.

  Inductive only_reserves (proms: Memory.t): Prop :=
  | only_reserves_intro
      (RESERVES: forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
          msg = Message.reserve)
      (FINITE: Memory.finite proms)
  .

  Lemma promise_not_cacncel_reserves_same prom0 mem0 loc from to msg prom1 mem1 kind
        (PROM: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (NOTCANCEL: kind <> Memory.op_kind_cancel)
        loc0 to0 from0
        (GET: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve))
    :
      exists from1,
        Memory.get loc0 to0 prom1 = Some (from1, Message.reserve).
  Proof.
    inv PROM.
    - eapply Memory.add_get1 in GET; eauto.
    - des. clarify. erewrite Memory.split_o; eauto.
      dup PROMISES. eapply Memory.split_get0 in PROMISES0.
      eapply split_succeed_wf in PROMISES. des. des_ifs.
      + ss. des. clarify.
      + ss. guardH o. des. clarify.
      + esplits; eauto.
    - des. clarify. erewrite Memory.lower_o; eauto. des_ifs.
      + ss. des. clarify.
        eapply lower_succeed_wf in PROMISES. des. clarify.
      + esplits; eauto.
    - clarify.
  Qed.

  Lemma remove_not_cacncel_reserves_same prom0 loc from to val released prom1
        (REMOVE: Memory.remove prom0 loc from to (Message.concrete val released) prom1)
        loc0 to0 from0
        (GET: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve))
    :
      exists from1,
        Memory.get loc0 to0 prom1 = Some (from1, Message.reserve).
  Proof.
    dup REMOVE. eapply Memory.remove_get0 in REMOVE. des.
    eapply Memory.remove_o in REMOVE0.
    instantiate (1:=to0) in REMOVE0.
    instantiate (1:=loc0) in REMOVE0. des_ifs.
    - ss. des. clarify.
    - esplits. etrans; eauto.
  Qed.

End CANCEL.

Section FORGETMEMORY.

  Inductive forget_memory P msrc mtgt : Prop :=
  | forget_memory_intro
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          Memory.get l t msrc = Memory.get l t mtgt)
      (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
  .

  Lemma forget_compose P0 P1 m0 m1 m2
        (FORGET0: forget_memory P0 m0 m1)
        (FORGET1: forget_memory P1 m1 m2)
    :
      forget_memory (P0 \2/ P1) m0 m2.
  Proof.
    inv FORGET0. inv FORGET1. econs; eauto.
    - ii. apply not_or_and in NPROMS. des.
      erewrite COMPLETE; eauto.
    - i. destruct (classic (P0 l t)); auto.
      des; clarify. erewrite COMPLETE; eauto.
  Qed.

  Lemma forget_compose_middle P0 P1 m0 m1 m2
        (FORGET: forget_memory (P0 \2/ P1) m0 m2)
        (FORGET1: forget_memory P1 m1 m2)
    :
      forget_memory P0 m0 m1.
  Proof.
    inv FORGET. inv FORGET1. econs; eauto.
    ii. destruct (classic (P1 l t)).
    - erewrite FORGET; eauto.
    - erewrite COMPLETE; eauto.
      + erewrite COMPLETE0; eauto.
      + ii. des; clarify.
  Qed.

  Lemma forget_memory_le P msrc mtgt
        (FORGET: forget_memory P msrc mtgt)
    :
      Memory.le msrc mtgt.
  Proof.
    inv FORGET. ii.
    destruct (classic (P loc to)).
    - exploit FORGET0; eauto.
      i. clarify.
    - exploit COMPLETE; eauto.
      i. rewrite LHS in *. auto.
  Qed.

  Inductive forget_cell (P: Time.t -> Prop) cell_src cell_tgt : Prop :=
  | forget_cell_intro
      (COMPLETE: forall t (NPROMS: ~ P t),
          Cell.get t cell_src = Cell.get t cell_tgt)
      (FORGET: forall t (PROMS: P t), Cell.get t cell_src = None)
  .

  Lemma forget_exists_list l cell_tgt:
    exists cell_src,
      (<<FORGET: forget_cell (fun to => List.In to l) cell_src cell_tgt>>).
  Proof.
    induction l; ss.
    - exists cell_tgt. econs; ss.
    - des. destruct (Cell.get a cell_src) as [[from msg]|] eqn:GET.
      + exploit Cell.remove_exists; eauto. i. des. exists cell2.
        inv FORGET. econs; i.
        * erewrite Cell.remove_o; eauto. des_ifs; eauto.
          ss; des; clarify. exfalso. eauto.
        * erewrite Cell.remove_o; eauto. des_ifs; clarify.
          eapply FORGET0; eauto. ss. des; clarify; eauto.
      + exists cell_src. inv FORGET.
        econs; eauto. i. des; clarify; eauto.
  Qed.

  Lemma forget_cell_exists P cell_tgt:
    exists cell_src, (<<FORGET: forget_cell P cell_src cell_tgt>>).
  Proof.
    hexploit (cell_finite_sound_exists cell_tgt); eauto. i. des.
    hexploit (list_filter_exists P dom). i. des.
    hexploit (forget_exists_list l' cell_tgt). i. des.
    exists cell_src. inv FORGET. econs; eauto.
    - i. eapply COMPLETE1. ii. apply COMPLETE0 in H. des. clarify.
    - i. destruct (classic (List.In t dom)).
      + eapply FORGET0; eauto. eapply COMPLETE0; eauto.
      + rewrite COMPLETE1; eauto.
        * destruct (Cell.get t cell_tgt) as [[from msg]|] eqn:GET; auto.
          exfalso. eapply H. eapply COMPLETE; eauto.
        * ii. eapply COMPLETE0 in H0. des; clarify.
  Qed.

  Lemma forget_exists P mem_tgt:
    exists mem_src, (<<FORGET: forget_memory P mem_src mem_tgt>>).
  Proof.
    hexploit (choice (fun loc cell => forget_cell (P loc) cell (mem_tgt loc))).
    { i. eapply forget_cell_exists. } i. des.
    exists f. econs.
    - i. destruct (H l). eapply COMPLETE; eauto.
    - i. destruct (H l). eapply FORGET; eauto.
  Qed.

  Lemma forget_unique P mem_tgt mem_src0 mem_src1
        (FORGET0: forget_memory P mem_src0 mem_tgt)
        (FORGET1: forget_memory P mem_src1 mem_tgt)
    :
      mem_src0 = mem_src1.
  Proof.
    inv FORGET0. inv FORGET1.
    eapply Memory.ext. i. destruct (classic (P loc ts)).
    - erewrite FORGET; auto. erewrite FORGET0; auto.
    - erewrite COMPLETE; auto. erewrite COMPLETE0; auto.
  Qed.

  Lemma forget_memory_get P mem0 mem1 loc to msg
        (FORGET: forget_memory P mem0 mem1)
        (GET: Memory.get loc to mem0 = Some msg)
    :
      (<<NOT: ~ P loc to>>) /\ (<<GET: Memory.get loc to mem1 = Some msg>>).
  Proof.
    inv FORGET. destruct (classic (P loc to)).
    - exfalso. rewrite FORGET0 in GET; auto. clarify.
    - esplits; eauto.
      rewrite <- COMPLETE; auto.
  Qed.

  Lemma bot_forget P mem0
        (BOT: P <2= bot2)
    :
      forget_memory P mem0 mem0.
  Proof.
    econs; eauto. i. eapply BOT in PROMS. clarify.
  Qed.

End FORGETMEMORY.

Lemma memory_cap_covered
      mem0 mem1
      (CAP: Memory.cap mem0 mem1)
      (CLOSED: Memory.closed mem0)
      loc to
  :
    Interval.mem (Time.bot, Time.incr (Memory.max_ts loc mem0)) to
    <->
    covered loc to mem1.
Proof.
  split; i.
  {
    inv H. inv CAP. set (@cell_elements_least
                           (mem0 loc)
                           (fun to' => Time.le to to')). des; cycle 1.
    { destruct (Time.le_lt_dec to (Memory.max_ts loc mem0)).
      - exfalso. exploit Memory.max_ts_spec.
        + eapply CLOSED.
        + i. des. exploit EMPTY; eauto.
      - econs.
        + eapply BACK.
        + econs; eauto. }
    set (@cell_elements_greatest
           (mem0 loc)
           (fun to' => Time.lt to' to)). des; cycle 1.
    { exfalso. exploit EMPTY.
      - eapply CLOSED.
      - eauto.
      - ss. }
    destruct (Time.le_lt_dec to from).
    - exploit MIDDLE.
      + econs.
        * eapply GET0.
        * eapply GET.
        * eapply TimeFacts.lt_le_lt; eauto.
        * i. destruct (Memory.get loc ts mem0) eqn:GET1; auto.
          exfalso. destruct p.
          destruct (Time.le_lt_dec to ts).
          { exploit LEAST; eauto. i.
            eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
            { eapply x. }
            eapply TimeFacts.le_lt_lt.
            { eapply TS2. }
            { eapply memory_get_ts_strong in GET. des; clarify; ss.
              exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
              - eapply l.
              - eauto. } }
          { exploit GREATEST; eauto. i.
            eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
            { eapply x. }
            { eauto. } }
      + eapply TimeFacts.lt_le_lt; eauto.
      + i. econs; eauto. econs; eauto.
    - econs.
      + eapply Memory.cap_le; try apply GET; eauto. refl.
      + econs; eauto.
  }
  {
    inv H. apply Memory.max_ts_spec in GET. des.
    inv ITV. ss. econs; ss.
    - eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
    - etrans; eauto. erewrite <- Memory.cap_max_ts; eauto.
  }
Qed.

Section CONCRETELE.

  Definition concrete_promised_le (mem0 mem1: Memory.t): Prop :=
    concrete_promised mem0 <2= concrete_promised mem1.

  Definition concrete_messages_le (mem0 mem1: Memory.t): Prop :=
    forall loc to from0 val released
           (GET0: Memory.get loc to mem0 = Some (from0, Message.concrete val released)),
    exists from1,
      (<<GET1: Memory.get loc to mem1 = Some (from1, Message.concrete val released)>>).

  Global Program Instance concrete_promised_le_PreOrder: PreOrder concrete_promised_le.
  Next Obligation.
    ii. auto.
  Qed.
  Next Obligation.
    ii. auto.
  Qed.

  Global Program Instance concrete_messages_le_PreOrder: PreOrder concrete_messages_le.
  Next Obligation.
    ii. eauto.
  Qed.
  Next Obligation.
    ii. exploit H; eauto. i. des. eauto.
  Qed.

  Lemma concrete_messages_le_concrete_promised_le
    :
      concrete_messages_le <2= concrete_promised_le.
  Proof.
    ii. inv PR0. eapply PR in GET. des. econs; eauto.
  Qed.

  Lemma concrete_promised_le_closed_timemap
        mem0 mem1 tm
        (CONCRETELE: concrete_promised_le mem0 mem1)
        (CLOSED: Memory.closed_timemap tm mem0)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc). des.
    exploit CONCRETELE.
    { econs; eauto. }
    i. inv x. eauto.
  Qed.

  Lemma concrete_promised_le_closed_view
        mem0 mem1 vw
        (CONCRETELE: concrete_promised_le mem0 mem1)
        (CLOSED: Memory.closed_view vw mem0)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    { eapply concrete_promised_le_closed_timemap; try apply PLN; eauto. }
    { eapply concrete_promised_le_closed_timemap; try apply RLX; eauto. }
  Qed.

  Lemma concrete_promised_le_closed_opt_view
        mem0 mem1 vw
        (CONCRETELE: concrete_promised_le mem0 mem1)
        (CLOSED: Memory.closed_opt_view vw mem0)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply concrete_promised_le_closed_view; eauto.
  Qed.

  Lemma concrete_promised_le_closed_message
        mem0 mem1 msg
        (CONCRETELE: concrete_promised_le mem0 mem1)
        (CLOSED: Memory.closed_message msg mem0)
    :
      Memory.closed_message msg mem1.
  Proof.
    inv CLOSED; econs.
    eapply concrete_promised_le_closed_opt_view; eauto.
  Qed.

  Lemma concrete_promised_le_closed_tview
        mem0 mem1 tvw
        (CONCRETELE: concrete_promised_le mem0 mem1)
        (CLOSED: TView.closed tvw mem0)
    :
      TView.closed tvw mem1.
  Proof.
    inv CLOSED. econs.
    { i. eapply concrete_promised_le_closed_view; try apply REL; eauto. }
    { eapply concrete_promised_le_closed_view; try apply CUR; eauto. }
    { eapply concrete_promised_le_closed_view; try apply ACQ; eauto. }
  Qed.

  Lemma memory_le_concrete_messages_le
    :
      Memory.le <2= concrete_messages_le.
  Proof.
    ii. eapply PR in GET0. eauto.
  Qed.

  Lemma concrete_promised_le_local_wf
        mem0 mem1 lc
        (LOCAL: Local.wf lc mem0)
        (CONCRETELE: concrete_promised_le mem0 mem1)
        (MLE: Memory.le (Local.promises lc) mem1)
    :
      Local.wf lc mem1.
  Proof.
    inv LOCAL. econs; eauto.
    eapply concrete_promised_le_closed_tview; eauto.
  Qed.

End CONCRETELE.


Section PROMISEWRITING.

  Inductive promise_writing_event
            (loc: Loc.t) (from to: Time.t) (val: Const.t) (released: option View.t)
  : forall (e: ThreadEvent.t), Prop :=
  | writing_event_write
      from' released' ord
      (FROM: Time.le from from')
      (TO: Time.le from' to)
      (RELEASED: View.opt_le released' released)
      (ORD: Ordering.le ord Ordering.relaxed)
    :
      promise_writing_event
        loc from to val released
        (ThreadEvent.write loc from' to val released' ord)
  | writing_event_update
      from' released' ord valr releasedr ordr
      (FROM: Time.le from from')
      (TO: Time.le from' to)
      (RELEASED: View.opt_le released' released)
      (ORD: Ordering.le ord Ordering.relaxed)
    :
      promise_writing_event
        loc from to val released
        (ThreadEvent.update loc from' to valr val releasedr released' ordr ord)
  .
  Hint Constructors promise_writing_event.

  Lemma promise_writing_event_mon loc from to val released from' released' e
        (FROM: Time.le from from')
        (RELEASED: View.opt_le released' released)
        (WRITING: promise_writing_event loc from' to val released' e)
    :
      promise_writing_event loc from to val released e.
  Proof.
    inv WRITING; econs; eauto; try by (etrans; eauto).
  Qed.

  Lemma promise_promise_decrease prom0 mem0 prom1 mem1
        l f t m k
        (PROMISE: Memory.promise prom0 mem0 l f t m prom1 mem1 k)
        loc from to val released
        (GET: Memory.get loc to prom0 = Some (from, Message.concrete val released))
    :
      exists from' released',
        (<<FROM: Time.le from from'>>) /\
        (<<RELEASED: View.opt_le released' released>>) /\
        (<<GET: Memory.get loc to prom1 = Some (from', Message.concrete val released')>>).
  Proof.
    inv PROMISE.
    { eapply Memory.add_get1 in GET; eauto.
      exists from, released. splits; auto; try by refl. }
    { eapply Memory.split_get1 in GET; eauto. des.
      exists f', released. splits; auto; try by refl. }
    { eapply Memory.lower_get1 in GET; eauto. des. inv MSG_LE.
      exists from, released1. splits; auto; try by refl. }
    { dup GET. eapply Memory.remove_get1 in GET; eauto. des.
      { subst. eapply Memory.remove_get0 in PROMISES. des. clarify. }
      { exists from, released. splits; auto; try by refl. }
    }
  Qed.

  Lemma step_promise_decrease_promise_writing_event lang (th0 th1: Thread.t lang) pf e lo
        (STEP: Thread.step lo pf e th0 th1)
        loc from to val released
        (GET: Memory.get loc to (Local.promises (Thread.local th0)) = Some (from, Message.concrete val released))
    :
      (exists from' released',
          (<<FROM: Time.le from from'>>) /\
          (<<RELEASED: View.opt_le released' released>>) /\
          (<<GET: Memory.get loc to (Local.promises (Thread.local th1)) = Some (from', Message.concrete val released')>>)) \/
      (promise_writing_event loc from to val released e).
  Proof.
    inv STEP.
    { left. inv STEP0; ss. inv LOCAL.
      eapply promise_promise_decrease in GET; eauto. }
    { inv STEP0; ss.
      inv LOCAL; try by (inv LOCAL0; left; exists from, released; splits; auto; refl).
      { left; exists from, released; splits; auto; refl. }
      { inv LOCAL0. ss. inv WRITE.
        eapply promise_promise_decrease in PROMISE; eauto. des.
        dup GET0. eapply Memory.remove_get1 in GET0; eauto. des.
        { subst. eapply Memory.remove_get0 in REMOVE. des. clarify.
          right. econs; eauto.
          { eapply memory_get_ts_le; eauto. }
          apply NNPP. ii.
          exploit RELEASE.
          { destruct ord; ss. }
          { eapply GET. }
          { ss. i. subst. inv RELEASED.
            unfold TView.write_released in *. des_ifs. destruct ord; ss. }
        }
        { left. esplits; eauto. }
      }
      { inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        eapply promise_promise_decrease in PROMISE; eauto. des.
        dup GET1. eapply Memory.remove_get1 in GET1; eauto. des.
        { subst. eapply Memory.remove_get0 in REMOVE. des. clarify.
          right. econs; eauto.
          { eapply memory_get_ts_le; eauto. }
          apply NNPP. ii.
          exploit RELEASE.
          { destruct ordw; ss. }
          { eapply GET. }
          { ss. i. subst. inv RELEASED.
            unfold TView.write_released in *. des_ifs; destruct ordw; ss. }
        }
        { left. esplits; eauto. }
      }
    }
  Qed.

End PROMISEWRITING.

Section WFTIME.

  Definition memory_times_wf (times: Loc.t -> Time.t -> Prop) (mem: Memory.t): Prop :=
    forall loc to from msg
           (GET: Memory.get loc to mem = Some (from, msg)),
      (<<FROM: times loc from>>) /\ (<<TO: times loc to>>).

  Lemma promise_memory_times_wf (times: Loc.t -> Time.t -> Prop)
        prom0 mem0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (FROM: times loc from)
        (TO: times loc to)
        (WF: memory_times_wf times mem0)
    :
      memory_times_wf times mem1.
  Proof.
    inv PROMISE.
    { ii. erewrite Memory.add_o in GET; eauto. des_ifs; eauto.
      ss. des; clarify. }
    { ii. erewrite Memory.split_o in GET; eauto. des_ifs; eauto.
      { ss. des; clarify. }
      { ss. des; clarify. eapply Memory.split_get0 in MEM.
        des. eapply WF in GET0. des. auto. }
    }
    { ii. erewrite Memory.lower_o in GET; eauto. des_ifs; eauto.
      ss. des; clarify. }
    { ii. erewrite Memory.remove_o in GET; eauto. des_ifs; eauto. }
  Qed.

End WFTIME.

Section PROMISED.

  Lemma promised_add mem1 loc from to msg mem2
        (ADD: Memory.add mem1 loc from to msg mem2)
  :
    promised mem2 =
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then fun ts' => if (Time.eq_dec ts' to) then True else promised mem1 loc' ts'
      else promised mem1 loc'. 
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. destruct msg0. erewrite Memory.add_o in GET; eauto.
      des_ifs.
      + ss. des; clarify.
      + econs; eauto.
      + ss. des; clarify.
      + econs; eauto.
    - des_ifs.
      + ss. des; clarify. econs. eapply Memory.add_get0; eauto.
      + inv H. destruct msg0.
        eapply Memory.add_get1 in GET; eauto. econs; eauto.
      + inv H. destruct msg0.
        eapply Memory.add_get1 in GET; eauto. econs; eauto.
  Qed.

  Lemma concrete_promised_add mem1 loc from to msg mem2
        (ADD: Memory.add mem1 loc from to msg mem2)
    :
      concrete_promised mem2 =
      fun loc' =>
        if (Loc.eq_dec loc' loc)
        then fun ts' => if (Time.eq_dec ts' to) then (msg <> Message.reserve) else concrete_promised mem1 loc' ts'
        else concrete_promised mem1 loc'.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. erewrite Memory.add_o in GET; eauto.
      des_ifs.
      + ss. des; clarify.
      + ss. des; clarify.
      + econs; eauto.
      + ss. des; clarify.
      + econs; eauto.
    - des_ifs.
      + destruct msg; ss. econs. eapply Memory.add_get0; eauto.
      + inv H.
        eapply Memory.add_get1 in GET; eauto. econs; eauto.
      + inv H.
        eapply Memory.add_get1 in GET; eauto. econs; eauto.
  Qed.

  Lemma promised_lower mem1 loc from to msg1 msg2 mem2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
    :
      promised mem2 = promised mem1.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. destruct msg. erewrite Memory.lower_o in GET; eauto. des_ifs.
      + ss. des; clarify. econs. eapply (Memory.lower_get0 LOWER); eauto.
      + econs; eauto.
    - inv H. destruct msg. eapply Memory.lower_get1 in GET; eauto.
      des. econs; eauto.
  Qed.

  Lemma concrete_promised_lower mem1 loc from to msg1 msg2 mem2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
        (MSG: msg1 <> Message.reserve)
    :
      concrete_promised mem2 = concrete_promised mem1.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. erewrite Memory.lower_o in GET; eauto. des_ifs.
      + ss. des; clarify.
        exploit lower_succeed_wf; eauto. i. des. inv MSG_LE; clarify.
        econs; eauto.
      + econs; eauto.
    - inv H. eapply Memory.lower_get1 in GET; eauto.
      des. inv MSG_LE. econs; eauto.
  Qed.

  Lemma promised_split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      promised mem2 =
      fun loc' =>
        if (Loc.eq_dec loc' loc)
        then fun ts' => if (Time.eq_dec ts' ts2) then True else promised mem1 loc' ts'
        else promised mem1 loc'.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. destruct msg. erewrite Memory.split_o in GET; eauto.
      des_ifs; try by (des; ss; clarify).
      + ss. des; clarify. econs. eapply (Memory.split_get0 SPLIT); eauto.
      + econs; eauto.
      + econs; eauto.
    - des_ifs.
      + ss. des; clarify. econs. eapply (Memory.split_get0 SPLIT); eauto.
      + inv H. destruct msg. eapply Memory.split_get1 in GET; eauto.
        des. econs; eauto.
      + inv H. destruct msg. eapply Memory.split_get1 in GET; eauto.
        des. econs; eauto.
  Qed.

  Lemma concrete_promised_split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      concrete_promised mem2 =
      fun loc' =>
        if (Loc.eq_dec loc' loc)
        then fun ts' => if (Time.eq_dec ts' ts2) then (msg2 <> Message.reserve) else concrete_promised mem1 loc' ts'
        else concrete_promised mem1 loc'.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. erewrite Memory.split_o in GET; eauto.
      des_ifs; try by (des; ss; clarify).
      + ss. des; clarify. econs. eapply (Memory.split_get0 SPLIT); eauto.
      + econs; eauto.
      + econs; eauto.
    - des_ifs.
      + destruct msg2; ss. econs. eapply (Memory.split_get0 SPLIT); eauto.
      + inv H. eapply Memory.split_get1 in GET; eauto.
        des. econs; eauto.
      + inv H. eapply Memory.split_get1 in GET; eauto.
        des. econs; eauto.
  Qed.

  Lemma promised_remove mem1 loc from to msg mem2
        (REMOVE: Memory.remove mem1 loc from to msg mem2)
    :
      promised mem2 =
      fun loc' =>
        if (Loc.eq_dec loc' loc)
        then fun ts' => if (Time.eq_dec ts' to) then False else promised mem1 loc' ts'
        else promised mem1 loc'.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. destruct msg0. erewrite Memory.remove_o in GET; eauto.
      des_ifs; try by (des; ss; clarify).
      + econs; eauto.
      + econs; eauto.
    - des_ifs.
      + inv H. destruct msg0. eapply Memory.remove_get1 in GET; eauto.
        des; clarify. econs; eauto.
      + inv H. destruct msg0. eapply Memory.remove_get1 in GET; eauto.
        des; clarify. econs; eauto.
  Qed.

  Lemma concrete_promised_remove mem1 loc from to mem2
        (REMOVE: Memory.remove mem1 loc from to Message.reserve mem2)
    :
      concrete_promised mem2 = concrete_promised mem1.
  Proof.
    extensionality loc'. extensionality ts'.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H. erewrite Memory.remove_o in GET; eauto.
      des_ifs; try by (des; ss; clarify). econs; eauto.
    - inv H. dup GET. eapply Memory.remove_get1 in GET; eauto. des.
      + clarify. eapply Memory.remove_get0 in REMOVE. des. clarify.
      + econs; eauto.
  Qed.

End PROMISED.

Section RESERVEFUTURE.

  Inductive reserve_future_memory:
    forall (prom0 mem0 prom1 mem1: Memory.t), Prop :=
  | reserve_future_memory_base
      prom0 mem0
    :
      reserve_future_memory
        prom0 mem0 prom0 mem0
  | reserve_future_memory_step
      prom0 mem0 prom1 mem1 prom2 mem2
      loc from to kind
      (HD: Memory.promise prom0 mem0 loc from to Message.reserve prom1 mem1 kind)
      (TL: reserve_future_memory prom1 mem1 prom2 mem2)
    :
      reserve_future_memory
        prom0 mem0 prom2 mem2
  .
  Hint Constructors reserve_future_memory.

  Lemma reserve_future_future prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Memory.future mem0 mem1.
  Proof.
    ginduction FUTURE; auto. i. transitivity mem1; auto.
    inv HD; clarify.
    - econs; [|refl]. econs; eauto.
    - econs; [|refl]. econs; eauto.
    - econs; [|refl]. econs; eauto.
    - econs; [|refl]. econs; eauto.
  Qed.

  Lemma reserve_future_concrete_promised prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      concrete_promised mem1 <2= concrete_promised mem0.
  Proof.
    ginduction FUTURE; auto. i. apply IHFUTURE in PR; auto.
    inv HD; des; clarify.
    - inv PR. erewrite Memory.add_o in GET; eauto.
      des_ifs. econs; eauto.
    - apply lower_succeed_wf in MEM. des. inv MSG_LE.
    - inv PR. erewrite Memory.remove_o in GET; eauto.
      des_ifs. econs; eauto.
  Qed.

  Lemma reserve_future_memory_trans prom0 mem0 prom1 mem1 prom2 mem2
        (FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1)
        (FUTURE12: reserve_future_memory prom1 mem1 prom2 mem2)
    :
      reserve_future_memory prom0 mem0 prom2 mem2.
  Proof.
    ginduction FUTURE01; i; eauto.
  Qed.

  Lemma reserve_future_memory_le prom0 mem0 prom1 mem1
        (MLE: Memory.le prom0 mem0)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Memory.le prom1 mem1.
  Proof.
    ginduction FUTURE; eauto. i.
    eapply IHFUTURE. eapply promise_memory_le; eauto.
  Qed.

  Lemma reserve_future_memory_bot_none prom0 mem0 prom1 mem1
        (BOTNONE: Memory.bot_none prom0)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Memory.bot_none prom1.
  Proof.
    ginduction FUTURE; eauto. i.
    eapply IHFUTURE. inv HD.
    - eapply Memory.add_bot_none; eauto.
    - eapply Memory.split_bot_none; eauto.
    - eapply Memory.lower_bot_none; eauto.
    - eapply Memory.cancel_bot_none; eauto.
  Qed.

  Lemma reserve_future_memory_finite prom0 mem0 prom1 mem1
        (FIN: Memory.finite prom0)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Memory.finite prom1.
  Proof.
    ginduction FUTURE; eauto. i.
    eapply IHFUTURE. inv HD.
    - eapply Memory.add_finite; eauto.
    - eapply Memory.split_finite; eauto.
    - eapply Memory.lower_finite; eauto.
    - eapply Memory.remove_finite; eauto.
  Qed.

  Lemma reserve_future_concrete_same prom0 mem0 prom1 mem1 loc from to val released
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (GET: Memory.get loc to mem0 = Some (from, Message.concrete val released))
    :
      Memory.get loc to mem1 = Some (from, Message.concrete val released).
  Proof.
    ginduction FUTURE; auto. i. apply IHFUTURE.
    inv HD; des; clarify.
    - erewrite Memory.add_o; eauto.
      des_ifs. ss. des; clarify.
      eapply Memory.add_get0 in MEM. des. clarify.
    - apply lower_succeed_wf in MEM. des. inv MSG_LE.
    - erewrite Memory.remove_o; eauto.
      des_ifs. ss. des; clarify.
      eapply Memory.remove_get0 in MEM. des. clarify.
  Qed.

  Lemma reserve_future_concrete_same_promise prom0 mem0 prom1 mem1 loc from to val released
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (GET: Memory.get loc to prom0 = Some (from, Message.concrete val released))
    :
      Memory.get loc to prom1 = Some (from, Message.concrete val released).
  Proof.
    ginduction FUTURE; auto. i. apply IHFUTURE.
    inv HD; des; clarify.
    - erewrite Memory.add_o; eauto.
      des_ifs. ss. des; clarify.
      eapply Memory.add_get0 in PROMISES. des. clarify.
    - apply lower_succeed_wf in PROMISES. des. inv MSG_LE.
    - erewrite Memory.remove_o; eauto.
      des_ifs. ss. des; clarify.
      eapply Memory.remove_get0 in PROMISES. des. clarify.
  Qed.

  Lemma reserve_future_memory_unch
        prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        loc to from msg
        (GETMEM: Memory.get loc to mem0 = Some (from, msg))
        (GETPROM: Memory.get loc to prom0 = None)
    :
      (<<GETMEM: Memory.get loc to mem1 = Some (from, msg)>>) /\
      (<<GETPROM: Memory.get loc to prom1 = None>>).
  Proof.
    ginduction FUTURE; eauto. i. inv HD; clarify.
    { eapply IHFUTURE; eauto.
      - erewrite Memory.add_o; eauto. des_ifs.
        ss. des; clarify.
        eapply Memory.add_get0 in MEM. des. clarify.
      - erewrite Memory.add_o; eauto. des_ifs.
        ss. des; clarify.
        eapply Memory.add_get0 in MEM. des. clarify. }
    { apply split_succeed_wf in PROMISES. des. clarify. }
    { apply lower_succeed_wf in PROMISES. des. clarify. inv MSG_LE. }
    { eapply IHFUTURE; eauto.
      - erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
      - erewrite Memory.remove_o; eauto. des_ifs. }
  Qed.

  Lemma reserve_future_memory_unchangable
        prom0 mem0 prom1 mem1 loc to from msg
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (UNCH: unchangable mem0 prom0 loc to from msg)
    :
      unchangable mem1 prom1 loc to from msg.
  Proof.
    ginduction FUTURE; eauto. i. exploit IHFUTURE; eauto.
    eapply unchangable_promise; eauto.
  Qed.

  Lemma reserve_future_memory_future
        vw sc prom0 mem0 prom1 mem1
        (LOCAL: Local.wf (Local.mk vw prom0) mem0)
        (SC: Memory.closed_timemap sc mem0)
        (MEM: Memory.closed mem0)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      (<<LOCAL: Local.wf (Local.mk vw prom1) mem1>>) /\
      (<<SC: Memory.closed_timemap sc mem1>>) /\
      (<<MEM: Memory.closed mem1>>).
  Proof.
    ginduction FUTURE; eauto. i.
    exploit Local.promise_step_future.
    { econs.
      - instantiate (9:=Local.mk vw prom0). eauto.
      - eauto.
      - eauto. }
    all: eauto. i. des. ss. eapply IHFUTURE; eauto.
    eapply Memory.future_closed_timemap; eauto.
  Qed.

  Lemma reserve_future_concrete_same_promise2 prom0 mem0 prom1 mem1 loc from to val released
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (GET: Memory.get loc to prom1 = Some (from, Message.concrete val released))
    :
      Memory.get loc to prom0 = Some (from, Message.concrete val released).
  Proof.
    ginduction FUTURE; auto. i. apply IHFUTURE in GET; auto.
    inv HD; des; clarify.
    - erewrite Memory.add_o in GET; eauto. des_ifs.
    - erewrite Memory.lower_o in GET; eauto. des_ifs.
    - erewrite Memory.remove_o in GET; eauto. des_ifs.
  Qed.

  Lemma reserve_future_read_commute
        vw0 prom0 mem0 loc to val released ord vw1 prom' prom1 mem1 lo
        (READ: Local.read_step (Local.mk vw0 prom0) mem0 loc to val released ord (Local.mk vw1 prom') lo)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Local.read_step (Local.mk vw0 prom1) mem1 loc to val released ord (Local.mk vw1 prom1) lo.
  Proof.
    inv READ. clarify. econs; eauto.
    eapply reserve_future_concrete_same; eauto.
  Qed.

End RESERVEFUTURE.


Section SEMICLOSED.

  Definition semi_closed_timemap
             (tm: TimeMap.t)
             (mem: Memory.t)
             (loc: Loc.t)
             (ts: Time.t): Prop :=
    forall l,
      (exists from val released,
          (<<GET: Memory.get l (tm l) mem = Some (from, Message.concrete val released)>>)) \/
      (<<EQ: l = loc /\ tm l = ts>>)
  .

  Lemma closed_timemap_semi_closed tm mem loc ts
        (CLOSED: Memory.closed_timemap tm mem)
    :
      semi_closed_timemap tm mem loc ts.
  Proof.
    ii. left. eauto.
  Qed.

  Lemma semi_closed_timemap_join tm0 tm1 mem loc ts
        (CLOSED0: semi_closed_timemap tm0 mem loc ts)
        (CLOSED1: semi_closed_timemap tm1 mem loc ts)
    :
      semi_closed_timemap (TimeMap.join tm0 tm1) mem loc ts.
  Proof.
    ii. specialize (CLOSED0 l). specialize (CLOSED1 l).
    unfold TimeMap.join, Time.join. des; des_ifs; eauto.
  Qed.

  Lemma semi_closed_timemap_singleton mem loc ts
        (INHABITED: Memory.inhabited mem)
    :
      semi_closed_timemap (TimeMap.singleton loc ts) mem loc ts.
  Proof.
    ii. unfold TimeMap.singleton.
    destruct (Loc.eq_dec loc l).
    - subst. right. split; auto. setoid_rewrite LocFun.add_spec_eq. auto.
    - left. esplits. setoid_rewrite LocFun.add_spec_neq; eauto.
  Qed.

  Lemma semi_closed_timemap_add tm mem0 loc from ts val released mem1
        (CLOSED: semi_closed_timemap tm mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc0). des.
    - esplits. eapply Memory.add_get1 in GET; eauto.
    - subst. eapply Memory.add_get0 in ADD. des. eauto.
  Qed.

  Lemma semi_closed_timemap_split tm mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_timemap tm mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc0). des.
    - eapply Memory.split_get1 in GET; eauto. des. eauto.
    - subst. eapply Memory.split_get0 in SPLIT. des. eauto.
  Qed.

  Lemma semi_closed_timemap_lower tm mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_timemap tm mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc0). des.
    - eapply Memory.lower_get1 in GET; eauto. des. inv MSG_LE. eauto.
    - subst. eapply Memory.lower_get0 in LOWER. des. eauto.
  Qed.

  Lemma semi_closed_timemap_future tm mem0 loc ts mem1
        (CLOSED: semi_closed_timemap tm mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_timemap tm mem1 loc ts.
  Proof.
    ii. specialize (CLOSED l). des.
    - eapply Memory.future_weak_get1 in GET; eauto. des.
      inv MSG_LE. eauto.
    - subst. eauto.
  Qed.

  Inductive semi_closed_view (view:View.t) (mem:Memory.t) (loc: Loc.t) (ts: Time.t): Prop :=
  | semi_closed_view_intro
      (PLN: semi_closed_timemap (View.pln view) mem loc ts)
      (RLX: semi_closed_timemap (View.rlx view) mem loc ts)
  .
  Hint Constructors semi_closed_view.

  Lemma closed_view_semi_closed vw mem loc ts
        (CLOSED: Memory.closed_view vw mem)
    :
      semi_closed_view vw mem loc ts.
  Proof.
    inv CLOSED. econs.
    - eapply closed_timemap_semi_closed; eauto.
    - eapply closed_timemap_semi_closed; eauto.
  Qed.

  Lemma semi_closed_view_join vw0 vw1 mem loc ts
        (CLOSED0: semi_closed_view vw0 mem loc ts)
        (CLOSED1: semi_closed_view vw1 mem loc ts)
    :
      semi_closed_view (View.join vw0 vw1) mem loc ts.
  Proof.
    inv CLOSED0. inv CLOSED1. econs.
    - eapply semi_closed_timemap_join; eauto.
    - eapply semi_closed_timemap_join; eauto.
  Qed.

  Lemma semi_closed_view_singleton mem loc ts
        (INHABITED: Memory.inhabited mem)
    :
      semi_closed_view (View.singleton_ur loc ts) mem loc ts.
  Proof.
    econs; ss.
    - eapply semi_closed_timemap_singleton; eauto.
    - eapply semi_closed_timemap_singleton; eauto.
  Qed.

  Lemma semi_closed_view_add vw mem0 loc from ts val released mem1
        (CLOSED: semi_closed_view vw mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_add; eauto.
    - eapply semi_closed_timemap_add; eauto.
  Qed.

  Lemma semi_closed_view_split vw mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_view vw mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_split; eauto.
    - eapply semi_closed_timemap_split; eauto.
  Qed.

  Lemma semi_closed_view_lower vw mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_view vw mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_lower; eauto.
    - eapply semi_closed_timemap_lower; eauto.
  Qed.

  Lemma semi_closed_view_future vw mem0 loc ts mem1
        (CLOSED: semi_closed_view vw mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_view vw mem1 loc ts.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_future; eauto.
    - eapply semi_closed_timemap_future; eauto.
  Qed.

  Inductive semi_closed_opt_view: forall (view:option View.t) (mem:Memory.t)
                                         (loc: Loc.t) (ts: Time.t), Prop :=
  | semi_closed_opt_view_some
      view mem loc ts
      (CLOSED: semi_closed_view view mem loc ts):
      semi_closed_opt_view (Some view) mem loc ts
  | semi_closed_opt_view_none
      mem loc ts:
      semi_closed_opt_view None mem loc ts
  .
  Hint Constructors semi_closed_opt_view.

  Lemma closed_opt_view_semi_closed vw mem loc ts
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      semi_closed_opt_view vw mem loc ts.
  Proof.
    inv CLOSED; econs.
    eapply closed_view_semi_closed; eauto.
  Qed.

  Lemma unwrap_closed_opt_view
        view mem loc ts
        (CLOSED: semi_closed_opt_view view mem loc ts)
        (INHABITED: Memory.inhabited mem):
    semi_closed_view (View.unwrap view) mem loc ts.
  Proof.
    inv CLOSED; ss.
    eapply closed_view_semi_closed. apply Memory.closed_view_bot. ss.
  Qed.

  Lemma semi_closed_opt_view_add vw mem0 loc from ts val released mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_add; eauto.
  Qed.

  Lemma semi_closed_opt_view_split vw mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_split; eauto.
  Qed.

  Lemma semi_closed_opt_view_lower vw mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_lower; eauto.
  Qed.

  Lemma semi_closed_opt_view_future vw mem0 loc ts mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_opt_view vw mem1 loc ts.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_future; eauto.
  Qed.

  Inductive semi_closed_message: forall (msg:Message.t) (mem:Memory.t)
                                        (loc: Loc.t) (ts: Time.t), Prop :=
  | semi_closed_message_concrete
      val released mem loc ts
      (CLOSED: semi_closed_opt_view released mem loc ts):
      semi_closed_message (Message.concrete val released) mem loc ts
  | semi_closed_message_reserve
      mem loc ts:
      semi_closed_message Message.reserve mem loc ts
  .
  Hint Constructors semi_closed_message.

  Lemma closed_message_semi_closed msg mem loc ts
        (CLOSED: Memory.closed_message msg mem)
    :
      semi_closed_message msg mem loc ts.
  Proof.
    inv CLOSED; econs. eapply closed_opt_view_semi_closed; eauto.
  Qed.

  Lemma semi_closed_message_add vw mem0 loc from ts val released mem1
        (CLOSED: semi_closed_message vw mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_message vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_add; eauto.
  Qed.

  Lemma semi_closed_message_split vw mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_message vw mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_message vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_split; eauto.
  Qed.

  Lemma semi_closed_message_lower vw mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_message vw mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_message vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_lower; eauto.
  Qed.

  Lemma semi_closed_message_future vw mem0 loc ts mem1
        (CLOSED: semi_closed_message vw mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_message vw mem1 loc ts.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_future; eauto.
  Qed.

  Lemma join_singleton_semi_closed_timemap tm mem loc from to
        (CLOSED: semi_closed_timemap tm mem loc from)
        (TS: Time.le from to)
    :
      semi_closed_timemap (TimeMap.join (TimeMap.singleton loc to) tm) mem loc to.
  Proof.
    ii. specialize (CLOSED l).
    remember (TimeMap.join (TimeMap.singleton loc to) tm l).
    unfold TimeMap.join, TimeMap.singleton in Heqt.
    setoid_rewrite LocFun.add_spec in Heqt.
    unfold Time.join in Heqt. des_ifs; des; clarify; eauto.
    - right. splits; auto. eapply TimeFacts.antisym; eauto.
    - erewrite LocFun.init_spec in l0.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
  Qed.

  Lemma join_singleton_semi_closed_view vw mem loc from to
        (CLOSED: semi_closed_view vw mem loc from)
        (TS: Time.le from to)
    :
      semi_closed_view (View.join (View.singleton_ur loc to) vw) mem loc to.
  Proof.
    inv CLOSED. econs; ss.
    - eapply join_singleton_semi_closed_timemap; eauto.
    - eapply join_singleton_semi_closed_timemap; eauto.
  Qed.

  Lemma concrete_promised_le_semi_closed_timemap tm mem0 mem1 loc to
        (CLOSED: semi_closed_timemap tm mem0 loc to)
        (CONCRETE: concrete_promised_le mem0 mem1)
    :
      semi_closed_timemap tm mem1 loc to.
  Proof.
    ii. specialize (CLOSED l). des.
    { exploit CONCRETE.
      { econs; eauto. }
      i. inv x. eauto.
    }
    { clarify. auto. }
  Qed.

  Lemma concrete_promised_le_semi_closed_view vw mem0 mem1 loc to
        (CLOSED: semi_closed_view vw mem0 loc to)
        (CONCRETE: concrete_promised_le mem0 mem1)
    :
      semi_closed_view vw mem1 loc to.
  Proof.
    inv CLOSED. econs.
    - eapply concrete_promised_le_semi_closed_timemap; eauto.
    - eapply concrete_promised_le_semi_closed_timemap; eauto.
  Qed.

End SEMICLOSED.


Section CONCRETEMAX.

  Inductive concrete_promise_max_ts mem prom loc ts: Prop :=
  | concrete_or_promise_max_ts_intro
      (EXISTS:
         (<<CONCRETE: exists from val released,
             (<<GET: Memory.get loc ts mem = Some (from, Message.concrete val released)>>)>>) \/
         (<<PROMISE: exists from msg, (<<GET: Memory.get loc ts prom = Some (from, msg)>>)>>))
      (CONCRETE: forall to from val released
                        (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
          Time.le to ts)
      (PROMISE: forall to from msg
                       (GET: Memory.get loc to prom = Some (from, msg)),
          Time.le to ts)
  .

  Lemma concrete_promise_max_ts_inj mem prom loc ts0 ts1
        (MAX0: concrete_promise_max_ts mem prom loc ts0)
        (MAX1: concrete_promise_max_ts mem prom loc ts1)
    :
      ts0 = ts1.
  Proof.
    eapply TimeFacts.antisym.
    { inv MAX0. des.
      { eapply MAX1 in GET. auto. }
      { eapply MAX1 in GET. auto. }
    }
    { inv MAX1. des.
      { eapply MAX0 in GET. auto. }
      { eapply MAX0 in GET. auto. }
    }
  Qed.

  Lemma concrete_promise_max_ts_exists mem prom loc
        (INHABITED: Memory.inhabited mem)
    :
      exists ts, (<<MAX: concrete_promise_max_ts mem prom loc ts>>).
  Proof.
    exploit Memory.max_concrete_ts_exists; eauto. intros [max MAX].
    exploit Memory.max_concrete_ts_spec.
    { eapply MAX. }
    { eapply INHABITED. } i. des.
    destruct (classic (exists to from msg, (<<INHABITED: Memory.get loc to prom = Some (from, msg)>>))).
    { des. eapply Cell.max_ts_spec in INHABITED0. des.
      exists (Time.join max (Cell.max_ts (prom loc))). econs.
      { unfold Time.join. des_ifs; eauto. left. eauto. }
      { i. etrans; [|eapply Time.join_l].
        eapply Memory.max_concrete_ts_spec in GET1; eauto. des. auto. }
      { i. etrans; [|eapply Time.join_r].
        eapply Cell.max_ts_spec in GET1; eauto. des. auto. }
    }
    { exists max. econs.
      { left. eauto. }
      { i. eapply Memory.max_concrete_ts_spec in GET0; eauto. des. auto. }
      { i. exfalso. eauto. }
    }
  Qed.

  Lemma concrete_promise_max_ts_max_ts mem prom loc ts
        (MAX: concrete_promise_max_ts mem prom loc ts)
        (MLE: Memory.le prom mem)
    :
      Time.le ts (Memory.max_ts loc mem).
  Proof.
    inv MAX. des.
    { eapply Memory.max_ts_spec; eauto. }
    { eapply Memory.max_ts_spec; eauto. }
  Qed.

  Lemma concrete_promise_max_ts_max_concrete_ts mem prom loc ts max
        (MAX: concrete_promise_max_ts mem prom loc ts)
        (CONCRETE: Memory.max_concrete_ts mem loc max)
    :
      Time.le max ts.
  Proof.
    inv CONCRETE. des. eapply MAX in GET; eauto.
  Qed.

  Definition concrete_promise_max_timemap mem prom tm: Prop :=
    forall loc, concrete_promise_max_ts mem prom loc (tm loc).

  Lemma concrete_promise_max_timemap_inj mem prom tm0 tm1
        (MAX0: concrete_promise_max_timemap mem prom tm0)
        (MAX1: concrete_promise_max_timemap mem prom tm1)
    :
      tm0 = tm1.
  Proof.
    extensionality loc.
    eapply concrete_promise_max_ts_inj; eauto.
  Qed.

  Lemma concrete_promise_max_timemap_exists mem prom
        (INHABITED: Memory.inhabited mem)
    :
      exists tm, (<<MAX: concrete_promise_max_timemap mem prom tm>>).
  Proof.
    eapply choice. i. eapply concrete_promise_max_ts_exists; eauto.
  Qed.

  Lemma concrete_promise_max_timemap_future mem0 mem1 prom tm0 tm1
        (MAX0: concrete_promise_max_timemap mem0 prom tm0)
        (MAX1: concrete_promise_max_timemap mem1 prom tm1)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      TimeMap.le tm0 tm1.
  Proof.
    ii. specialize (MAX0 loc). specialize (MAX1 loc). inv MAX0. des.
    { eapply FUTURE in GET. des.
      { eapply MAX1 in GET. eauto. }
      { eapply MAX1 in GET. eauto. }
    }
    { eapply MAX1 in GET. auto. }
  Qed.

End CONCRETEMAX.
