Require Import RelationClasses.
Require Import List.

Require Import sflib.
From Paco Require Import paco.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import Language.
Require Export ZArith.

Require Import Event.
Require Import Syntax.
Require Import Maps.
Require Import Integers.
Require Import LibTactics.

(** * Semantics of the CSimpRTL *)

(* This file defines the semantics of concurrent simple RTL language (RTL) *)

(* The semantics of CSimpRTL is a set of transitions on the thread-local state *)

(** ** Register File *)
Module RegFile.
  (** Register file is a total map from register to value. *)
  Definition t := RegFun.t int.

  (** Register file initialization *)
  Definition init := RegFun.init Int.zero.

  Fixpoint eval_expr (e: Inst.expr) (rf: t): int := 
      match e with 
      | Inst.expr_val val => val
      | Inst.expr_reg r => RegFun.find r rf
      | Inst.expr_op2 op e1 e2 => Op2.eval op (eval_expr e1 rf) (eval_expr e2 rf)
      end.
End RegFile.

(** ** Continuation *)
Module Continuation.
    Inductive t := 
    | done
    | stack (regs: RegFile.t) (blk: BBlock.t) (cdhp: CodeHeap) (cont: t)
    .
End Continuation.

(** ** Thread-local state and state transitions *)
(** Thread-local state includes:
    - regs: register file;
    - blk: current basic block;
    - cdhp: codeheap for current function;
    - cont: continuation, which acts as a call stack;
    - code: whole program *)
Module State. (** This `state` contains program's continuation *)
    Structure t := mk {
        regs: RegFile.t;
        blk: BBlock.t;
        cdhp: CodeHeap;
        cont: Continuation.t;
        code: Code;   
    }.

    Definition init(code:Code) (f:Language.fid) : option t :=
      match (code!f) with
      | Some (ch, fentry) =>
        match (ch!fentry) with
        | Some b => Some (mk RegFile.init b ch Continuation.done code)
        | _ => None
        end
      | _ => None
      end.

    Definition is_terminal (s: t): Prop:= 
        (blk s) = BBlock.ret /\ (cont s) = Continuation.done.
    
    Definition int2loc (i: int) : Loc.t := Z.to_pos (Int.unsigned i).

    Notation "[[ i ]]" := (int2loc i) (at level 75, right associativity).

    (** State transitions *)
    Inductive step: forall (e:ProgramEvent.t) (s1:t) (s2:t), Prop :=
    | step_skip
        rf b b' ch cont code
        (BLK: b = Inst.skip ## b')
        :
        step ProgramEvent.silent
             (mk rf b ch cont code)
             (mk rf b' ch cont code)
    | step_assign
        r e rf rf' b b' ch cont code
        (BLK: b = (Inst.assign r e) ## b')
        (REGFILE: rf' = RegFun.add r (RegFile.eval_expr e rf) rf)
        :
        step ProgramEvent.silent
            (mk rf b ch cont code)
            (mk rf' b' ch cont code)
    | step_load
        r loc or v rf rf' b b' ch cont code
        (BLK: b = (Inst.load r loc or) ## b')
        (REGFILE: rf' = RegFun.add r v rf)
        :
        step (ProgramEvent.read loc v or) 
            (mk rf b ch cont code)
            (mk rf' b' ch cont code)
    | step_store
        loc e ow v  rf b b' ch cont code
        (BLK: b = (Inst.store loc e ow) ## b')
        (VAL: RegFile.eval_expr e rf = v)
        :
        step (ProgramEvent.write loc v ow) 
            (mk rf b ch cont code)
            (mk rf b' ch cont code)     
    | step_out  
        e v rf b b' ch cont code
        (BLK: b = (Inst.print e) ## b')
        (VAL: RegFile.eval_expr e rf = v)
        :
        step (ProgramEvent.syscall (Event.mk v)) 
            (mk rf b ch cont code)
            (mk rf b' ch cont code)    
    | step_cas_same
        r loc er ew or ow vr vw rf rf' b b' ch cont code
        (BLK: b = (Inst.cas r loc er ew or ow) ## b')
        (VALR: RegFile.eval_expr er rf = vr)
        (VALW: RegFile.eval_expr ew rf = vw)
        (REGFILE: rf' = RegFun.add r Int.one rf)
        :
        step (ProgramEvent.update loc vr vw or ow) 
            (mk rf b ch cont code)
            (mk rf' b' ch cont code)   
    | step_cas_flip
        r loc er ew or ow vr' vr vw rf rf' b b' ch cont code
        (BLK: b = (Inst.cas r loc er ew or ow) ## b')
        (VALR: RegFile.eval_expr er rf = vr')
        (VALW: RegFile.eval_expr ew rf = vw)
        (TEST: Int.cmp Cne vr vr')
        (REGFILE: rf' = RegFun.add r Int.zero rf)
        :
        step (ProgramEvent.read loc vr or) 
            (mk rf b ch cont code)
            (mk rf' b' ch cont code)   
    | step_call 
        rf (code:Code) (b:BBlock.t) b' f fret f0 b b0 ch ch0 cont cont0  
        (BLK: b = BBlock.call f fret)
        (FIND_FUNC: (code!f) = Some (ch0, f0))
        (ENTRY_BLK: (ch0!f0) = Some (b0))
        (STACK: ch!fret = Some (b'))
        (CONT: cont0 = (Continuation.stack rf b' ch cont))
        :
        step ProgramEvent.silent 
            (mk rf b ch cont code)
            (mk (RegFile.init) b0 ch0 cont0 code)    
    | step_ret 
        b rf rf0 b0 ch0 cont0 ch cont code
        (BLK: b = BBlock.ret)
        (CONT: cont = (Continuation.stack rf0 b0 ch0 cont0))
        :
        step (ProgramEvent.silent) 
            (mk rf b ch cont code)
            (mk rf0 b0 ch0 cont0 code) 
    | step_fence_rel
        b rf ch b' cont code
        (BLK: b = (Inst.fence_rel) ## b')
        :
        step (ProgramEvent.fence (Ordering.relaxed) (Ordering.acqrel))
            (mk rf b ch cont code)
            (mk rf b' ch cont code)   
    | step_fence_acq
        b rf ch b' cont code
        (BLK: b = (Inst.fence_acq) ## b')
        :
        step (ProgramEvent.fence (Ordering.acqrel) (Ordering.relaxed))
            (mk rf b ch cont code)
            (mk rf b' ch cont code)  
    | step_fence_sc
        b rf ch b' cont code
        (BLK: b = (Inst.fence_sc) ## b')
        :
        step (ProgramEvent.fence (Ordering.relaxed) (Ordering.seqcst))
            (mk rf b ch cont code)
            (mk rf b' ch cont code)  
    | step_jmp
        b f rf ch b' cont code
        (BLK: b = BBlock.jmp f)
        (TGT: ch!f = Some (b'))
        :
        step (ProgramEvent.silent) 
            (mk rf b ch cont code)
            (mk rf b' ch cont code)   
    | step_be 
        b e f1 f2 rf v ch b' cont code
        (BLK: b = BBlock.be e f1 f2)
        (COND: RegFile.eval_expr e rf = v)
        (BRANCH: (ch!f1 = Some (b') /\ Int.eq v Int.zero) \/
                (ch!f2 = Some (b') /\ Int.cmp Cne v Int.zero))
        :
        step (ProgramEvent.silent) 
            (mk rf b ch cont code)
            (mk rf b' ch cont code)   
    .
End State. 

Program Definition rtl_lang:Language.t :=
  Language.mk
    State.init
    State.is_terminal
    State.step _ _ _.
Next Obligation. 
(** prove determinacy of rtl language (required by Language.v) on thread-local transition*)
  inv STEP1; try solve [inv STEP2; inv BLK; tryfalse; eauto];
    inv STEP2; inv BLK; tryfalse.
  {
    right. left.
    exists or0 loc0 v v0; eauto.
  }
  {
    eauto.
  }
  { 
    right; right; left.
    exists or0 ow0 loc0.
    exists (RegFile.eval_expr er0 rf) (RegFile.eval_expr ew0 rf) vr.
    eauto.
  }
  {
    right; right; right.
    exists or0 ow0 loc0.
    exists (RegFile.eval_expr er0 rf) (RegFile.eval_expr ew0 rf) vr.
    eauto.
  }
  { 
    right; left.
    exists or0 loc0 vr vr0.
    eauto.
  }
  {
    left. split; eauto.
    rewrite FIND_FUNC in FIND_FUNC0. inv FIND_FUNC0.
    rewrite ENTRY_BLK in ENTRY_BLK0. inv ENTRY_BLK0.
    rewrite STACK in STACK0. inv STACK0.
    eauto.
  }
  {
    inv CONT; eauto.
  }
  {
    rewrite TGT in TGT0. inv TGT0; eauto.
  }
  {
    left; eauto.
    destruct BRANCH; destruct BRANCH0.
    {
      destruct H, H0.
      rewrite H in H0; inv H0; eauto.
    }
    { 
      destruct H, H0.
      unfolds Int.cmp, Int.eq.
      destruct (Coqlib.zeq (Int.unsigned (RegFile.eval_expr e0 rf)) (Int.unsigned Int.zero)); tryfalse.
    }
    {
      destruct H, H0.
      unfolds Int.cmp, Int.eq.
      destruct (Coqlib.zeq (Int.unsigned (RegFile.eval_expr e0 rf)) (Int.unsigned Int.zero)); tryfalse.
    }
    {
      destruct H, H0.
      rewrite H in H0; inv H0; eauto.
    }
  }
Qed. 
Next Obligation.
  inv READ.
  eexists. left.
  {
    econs; eauto.
  }
  {
    destruct (classic (Int.cmp Cne val' (RegFile.eval_expr er rf))).
    {
      eexists.
      left. eapply State.step_cas_flip; eauto.
    }
    {
      unfold Int.cmp in H.
      unfold negb in H.
      destruct (Int.eq val' (RegFile.eval_expr er rf)) eqn:Heqe; ss.
      eapply Int.same_if_eq in Heqe; subst.
      eexists.
      right.
      do 2 eexists.
      econs; eauto.
    }
  }
Qed.
Next Obligation.
  inv UPDATE.
  destruct (classic (Int.cmp Cne val' (RegFile.eval_expr er rf))).
  {
    eexists.
    left.
    eapply State.step_cas_flip; eauto.
  }
  {
    unfold Int.cmp in H.
    unfold negb in H.
    destruct (Int.eq val' (RegFile.eval_expr er rf)) eqn:Heqe; ss.
    eapply Int.same_if_eq in Heqe; subst.
    eexists.
    right.
    econs; eauto.
  }
Qed.
