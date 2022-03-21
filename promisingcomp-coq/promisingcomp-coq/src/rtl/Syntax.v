Require Import RelationClasses.
Require Import List.
Require Import Maps.
Require Import Coqlib.
Require Import LibTactics.
Require Import Basics.

Require Import sflib.

Require Import Basic.
Require Import Loc.
Require Import Axioms.

Require Import Language.
Require Import Event.
Require Import Integers.

Set Implicit Arguments.

(** * Syntax of the CSimpRTL language *)

(** This file defines the syntax of the concurrent simple RTL language (CSimpRTL),
    which corresponds to the definitions in Figure 4 in our paper *)

Module Reg := Ident.
Module RegSet := IdentSet.
Module RegMap := IdentMap.
Module RegFun := IdentFun.

Module Op2.
    Inductive t := 
    | add 
    | sub 
    | mul
    .
    Definition eval (op:t): forall (op1 op2:int), int :=
        match op with
        | add => Int.add
        | sub => Int.sub
        | mul => Int.mul
        end.
    Definition eqb (op1 op2: t): bool := 
        match op1, op2 with 
        | add, add => true 
        | sub, sub => true
        | mul, mul => true
        | _, _ => false
        end.
    Definition eq_dec : forall op1 op2: t, {op1 = op2} + {op1 <> op2}.
        decide equality.
    Defined.
End Op2.

(** ** Instruction *)
Module Inst.
    Inductive expr := 
    | expr_val (val: int)
    | expr_reg (reg: Reg.t)
    | expr_op2 (op: Op2.t) (op1 op2: expr)
    .
    
    Definition expr_eq_dec: forall e1 e2: expr, {e1 = e2} + {e1 <> e2}.
        decide equality. eapply Int.eq_dec. eapply Loc.eq_dec. eapply Op2.eq_dec.
    Defined.

    Definition beq_expr (e1 e2: expr): bool := 
        expr_eq_dec e1 e2. 

    Lemma beq_expr_eq:
        forall e e',
        beq_expr e e' = true <-> e = e'.
    Proof.
        intros.
        split.
        - intro. 
          unfolds beq_expr.
          unfolds Coqlib.proj_sumbool.
          des_ifs.
        - intro.         
            unfolds beq_expr.
            unfolds Coqlib.proj_sumbool.
            des_ifs.
    Qed.

    Fixpoint regs_of_expr (r:expr): RegSet.t :=
        match r with
        | expr_val val => RegSet.empty
        | expr_reg reg => RegSet.singleton reg
        | expr_op2 _ op1 op2 => RegSet.union (regs_of_expr op1) (regs_of_expr op2)
        end.

    (** Instruction includes:
        - [skip]: skip;
        - [assign]: register assignments;
        - [load]: memory read;
        - [store]: memory store;
        - [print]: system call for output;
        - [cas]: atomic update;
        - [fence_rel], [fence_acq] and [fence_sc]: release, acquire and sc fences *)
    Inductive t := 
    | skip 
    | assign (lhs: Reg.t) (rhs: expr)
    | load (lhs: Reg.t) (loc: Loc.t) (or: Ordering.t)
    | store (lhs: Loc.t) (rhs: expr) (ow: Ordering.t)
    | print (e: expr)
    | cas (lhs: Reg.t) (loc: Loc.t) (er ew: expr) (or ow: Ordering.t)
    | fence_rel 
    | fence_acq 
    | fence_sc 
    .
    
    Definition regs_of (i:t): RegSet.t :=
        match i with
        | skip => RegSet.empty
        | assign reg rhs => RegSet.add reg (regs_of_expr rhs)
        | load reg loc _ => regs_of_expr (expr_reg reg)
        | store loc rhs _ => regs_of_expr rhs
        | cas r loc er ew _ _ =>
          RegSet.add r (RegSet.union (regs_of_expr er) (regs_of_expr ew))
        | print e => regs_of_expr e 
        | _ => RegSet.empty
        end.
End Inst.

(** ** Basic block *)
(** A list of instructions with a jmp (unconditional branch),
    or call (function call) or be (conditional branch) or ret (function return) instructions as a tail *)
Module BBlock.
    Inductive t := 
    | jmp (f: Language.fid)
    | call (f fret: Language.fid)
    | be (e: Inst.expr) (f1 f2: Language.fid)
    | ret
    | blk (c: Inst.t) (b: t).

    Fixpoint get_out_fids (bb: t): list(Language.fid) := 
        match bb with
        | blk _ bb' => get_out_fids bb'
        | jmp fid => fid::nil
        | be _ fid1 fid2  => fid1::(fid2::nil)
        | _ => nil
        end.

    Fixpoint bb_from_i (bb: t) (i: nat) {struct i} : option t := 
        match i with 
        | O => Some bb
        | S i' =>  
            match bb with 
            | blk _ bb' => bb_from_i bb' i' 
            | _ => None
            end
        end.
    
    Fixpoint len (bb: t) := 
        match bb with 
        | blk c bb' => len(bb') + 1
        | _ => 1
        end.
    
    Lemma len_lt_zero:
    forall bb, 
        len bb > 0.
    Proof.
        intros.
        unfolds len.
        destruct bb; try lia.
    Qed.
      
    Lemma len_none:
    forall i bb,
      bb_from_i bb i = None <-> 
      i >= len bb.
    Proof.
      induction i. 
      -
        intros.
        split.
        unfolds bb_from_i. discriminate.
        intros.
        pose proof (len_lt_zero bb).
        lia.
      -
        intros.
        split.
        {
          intros.
          unfold bb_from_i in H.  
          folds bb_from_i.
          destruct bb; unfolds len; try lia.
          eapply IHi in H.
          lia.
        }
        {
          intros.
          unfold len in H.  
          destruct bb;
          unfolds bb_from_i; trivial.
          folds bb_from_i.
          folds len.
          assert (i >= len bb). {
            lia.
          }
          eapply IHi in H0.
          trivial.
        }
    Qed.

    Lemma len_none_plus:
    forall bb i i',
      bb_from_i bb i = None -> 
      i' >= i ->
      bb_from_i bb i' = None.
    Proof. 
      intros.
      eapply len_none in H.
      assert (i' >= len bb). {lia. }
      eapply len_none in H1. 
      trivial.
    Qed.

End BBlock.
Notation "i ## b" := (BBlock.blk i b) (at level 69, right associativity).
Notation "b [ i :]" := (BBlock.bb_from_i b i) (at level 1, right associativity).

(** ** Codeheap *)
(** A partial mapping from block label to basic block. *)
Definition CodeHeap:Type := PTree.t (BBlock.t). (** fid -> bblock *)
(** ** Function *)
(** A pair of codeheap and a label indicating the function entry. *)
(** In our paper (in Figure 4), for simple presentation,
    we assume that the entry of each function equals to its function identifier.  *)
Definition Func:Type := (CodeHeap * Language.fid).
(** ** Program *)
(** A partial mapping from function identifier to function. *)
Definition Code:Type := PTree.t Func.

Definition succ (bb: BBlock.t): list(Language.fid) := BBlock.get_out_fids bb.

Inductive pred (cdhp: CodeHeap) (f: Language.fid): forall (f': Language.fid), Prop :=
    | pred_intro
        f' bb
        (VALID: cdhp!f' = Some bb)
        (PRED: In f (succ bb))
        :
        pred cdhp f f'
    .

Theorem subblk_same_succ: 
    forall blk inst blk',
        blk = inst ## blk' -> 
        succ blk = succ blk'.
Proof.
    intros.
    unfolds succ.
    unfolds BBlock.get_out_fids. rewrite H. trivial.
Qed.

Definition bb_from_i := BBlock.bb_from_i.

Theorem bb_from_zero:
    forall blk,
    blk[0:] = Some blk.
Proof.
    intros.
    unfolds BBlock.bb_from_i.
    induction blk; trivial.
Qed.

Theorem bb_from_i_plus_one:
    forall i blk inst b',
    blk [i:] = Some (inst ## b') 
    -> 
    blk [i+1:] = Some (b').
Proof.
    induction i.
    - 
        intros.
        unfolds BBlock.bb_from_i.
        destruct blk; try inversion H; eauto.
    -
        intros.
        simpls.
        destruct blk; eauto; try discriminate.
Qed.

Theorem bb_from_i_gnone:
    forall i blk inst blk',
    blk = inst ## blk'
    ->
    blk [i:] = None 
    -> 
    blk' [i:] = None
    .
Proof.
  induction i.
  intros.
  - unfolds BBlock.bb_from_i. discriminate. 
  - intros.
    unfolds BBlock.bb_from_i. rewrite H in H0.
    destruct blk' eqn:EqBlk'; trivial.
    (* pose proof H0.  *)
    (* destruct i; try discriminate; eauto. *)
    eapply BBlock.len_none in H0.
    folds BBlock.bb_from_i.
    eapply BBlock.len_none.
    assert (exists i', i = S i'). {
      pose proof (BBlock.len_lt_zero (c ## t)).
      destruct i; try lia.
      exists i. trivial.
    }
    destruct H1 as (i' & H1).
    rewrite H1.
    rewrite H1 in H0.
    folds bb_from_i.
    eapply BBlock.len_none.
    eapply BBlock.len_none in H0.
    rewrite <- EqBlk' in H0.
    eapply IHi in EqBlk'; eauto.
    eapply BBlock.len_none_plus with (i' := S i') in EqBlk'; eauto; try lia.
    rewrite H1; trivial.
Qed.

Theorem bb_from_i_geq:
    forall i blk inst blk' blk'',
    blk = inst ## blk'
    -> 
    blk' [i:] = blk''
    ->
    blk [i+1:] = blk'' 
    .
Proof.
  induction i.
  - intros. 
    unfolds BBlock.bb_from_i. simpls.
    rewrite H. trivial.
  - intros. 
    unfolds BBlock.bb_from_i. simpls.
    rewrite H.
    replace (i+1) with (S i); try lia.
    trivial.
Qed.
    
Theorem bb_from_i_plus_one_implies_i: 
    forall i blk blk'',
        blk [S i:] = Some blk''
        -> 
      exists inst,
        blk [i:] = Some (inst##blk'').
Proof.
  induction i.
  - 
  intros.
  unfolds BBlock.bb_from_i.
  destruct blk eqn:EqBlk; try discriminate.
  inv H. 
  exists c. econs. 
  - 
  intros.
  unfolds BBlock.bb_from_i.
  destruct blk eqn:EqBlk; try discriminate.
  folds BBlock.bb_from_i.
  destruct t eqn:EqT; try discriminate; eauto.
Qed.  
  

Theorem bb_from_i_invariant:
    forall i blk blk',
      blk [i:] = Some blk'
      -> 
      BBlock.len blk = i + BBlock.len blk'.
Proof.
  induction i.
  -
    intros.
    unfolds BBlock.bb_from_i. inv H. lia.  
  -
    intros. 
    eapply bb_from_i_plus_one_implies_i in H.
    destruct H as (inst & H).
    eapply IHi in H.
    rewrite H.
    unfold BBlock.len; simpls. 
    lia.
Qed.


Theorem blk_partial_i_lt_len:
    forall i blk blk',
        blk[i:] = Some blk'
        -> 
        i < BBlock.len blk.
Proof.
    intros.
    eapply bb_from_i_invariant in H.
    pose proof (BBlock.len_lt_zero blk').
    rewrite H.
    eapply Nat.lt_sub_lt_add_l.
    lia. 
Qed.


