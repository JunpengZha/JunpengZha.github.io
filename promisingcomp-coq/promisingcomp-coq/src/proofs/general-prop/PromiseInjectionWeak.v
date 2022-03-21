Require Import sflib.    

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Coqlib.
Require Import Language. 

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import NPThread.
Require Import Configuration.
Require Import MsgMapping.

Require Import MemoryReorder.
Require Import ReorderPromise.
Require Import ReorderReserve.
Require Import ReorderCancel. 

(* Promises injection *)
Inductive promise_inj_weak: Mapping -> Memory.t -> Memory.t -> Prop :=
| Promise_inj_intro
    promises1 promises2 inj
    (SOUND: forall loc to val from released,
        Memory.get loc to promises1 = Some (from, Message.concrete val released) ->
        exists to' released' from',
          inj loc to = Some to' /\
          Memory.get loc to' promises2 = Some (from', Message.concrete val released') /\
          Time.lt from' to')
    (COMPLETE: forall loc to' val from' released',
        Memory.get loc to' promises2 = Some (from', Message.concrete val released') ->
        exists to released from,
          inj loc to = Some to' /\
          Memory.get loc to promises1 = Some (from, Message.concrete val released))
    (RSV_SOUND: forall loc to from,
        Memory.get loc to promises1 = Some (from, Message.reserve) ->
        Memory.get loc to promises2 = Some (from, Message.reserve))
    (RSV_COMPLETE: forall loc to from,
        Memory.get loc to promises2 = Some (from, Message.reserve) ->
        Memory.get loc to promises1 = Some (from, Message.reserve)):
    promise_inj_weak inj promises1 promises2. 

Lemma promise_inj_weak_incr
      inj inj' promises promises'
      (P_INJ: promise_inj_weak inj promises promises')
      (INJ_INCR: incr_inj inj inj'):
  promise_inj_weak inj' promises promises'.
Proof.
  inv P_INJ.
  econs; ii; eauto.
  {
    eapply SOUND in H; eauto.
    des; eauto.
    exists to', released', from'.
    split; eauto.
  }
  {
    eapply COMPLETE in H; eauto.
    des; eauto.
    do 3 eexists.
    split; eauto.
  }
Qed.

Lemma promise_inj_weak_remove_reseve
      inj promises promises' loc from to promises1 promises1'
      (P_INJ: promise_inj_weak inj promises promises')
      (REMOVE_RSV1: Memory.remove promises loc from to Message.reserve promises1)
      (REMOVE_RSV2: Memory.remove promises' loc from to Message.reserve promises1'):
  promise_inj_weak inj promises1 promises1'.
Proof.
  inv P_INJ.
  econs; ii.
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; subst; eauto.
    eapply SOUND in H; eauto. 
    destruct H as (to' & released' & from' & INJ & GET).
    exists to', released', from'. split; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; eauto. ss. des; subst. ss.
    clear - REMOVE_RSV2 GET.
    exploit Memory.remove_get0; eauto; ii; des.
    rewrite GET in GET0; inv GET0; eauto.
  }
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; eauto.
    exploit COMPLETE; eauto; ii; des. 
    exploit Memory.remove_get1; [eapply REMOVE_RSV1 | eauto..]. ii.
    des; subst; ss. 
    do 3 eexists. split; eauto.
    exploit COMPLETE; eauto; ii; des. 
    exploit Memory.remove_get1; [eapply REMOVE_RSV1 | eauto..]. ii.
    des; subst; ss.
    eapply Memory.remove_get0 in REMOVE_RSV1; eauto; des.
    rewrite GET in H1. inv H1.
    do 3 eexists. split; eauto.
  }
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss.
    eapply RSV_SOUND in H.
    exploit Memory.remove_get1; eauto. ii.
    destruct H0; eauto.
    destruct H0; subst; des; ss.
  }
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss.
    eapply RSV_COMPLETE in H.
    erewrite Memory.remove_o; eauto.
    des_if; eauto.
    ss; des; subst; ss.
  }
Qed.

Lemma promise_inj_weak_remove_concrete
      inj promises promises' loc from to msg from' to' msg' promises1 promises1'
      (P_INJ: promise_inj_weak inj promises promises')
      (REMOVE_RSV1: Memory.remove promises loc from to msg promises1)
      (REMOVE_RSV2: Memory.remove promises' loc from' to' msg' promises1')
      (INJ: inj loc to = Some to')
      (MON: monotonic_inj inj)
      (CONCRETE_MSG: exists val released, msg = Message.concrete val released):
  promise_inj_weak inj promises1 promises1'.
Proof.
  des; subst.
  inv P_INJ.
  econs; ii.
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss.
    exploit SOUND; eauto. ii.
    destruct H0 as (to1 & released1 & from1 & INJ1 & GET1 & Time_LT).
    destruct (Loc.eq_dec loc0 loc).
    {
      des; subst; ss.
      assert(to' <> to1).
      {
        eapply monotonic_inj_implies_disj_mapping; eauto.
      }
      eapply Memory.remove_get1 in GET1; eauto; des; subst; ss.
      do 3 eexists; eauto.
    }
    {
      eapply Memory.remove_get1 in GET1; eauto; des; subst; ss.
      do 3 eexists; eauto.
      do 3 eexists; eauto.
    }
  }
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; ss; eauto.
    exploit COMPLETE; eauto; ii; des. 
    exploit Memory.remove_get1; [eapply REMOVE_RSV1 | eauto..]. ii.
    des; subst; ss.
    do 3 eexists. split; eauto.
    exploit COMPLETE; eauto; ii; des. 
    exploit Memory.remove_get1; [eapply REMOVE_RSV1 | eauto..]. ii.
    des; subst; ss.
    rewrite INJ in H0; inv H0; ss.
    do 3 eexists. split; eauto.
  }
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss; des; ss; eauto.
    eapply RSV_SOUND in H; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; eauto; ss; des; subst; ss.
    eapply RSV_SOUND in H; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; eauto; ss; des; subst; ss.
    exploit Memory.remove_get0; eauto; ii; des.
    rewrite GET in H; inv H.
    exploit Memory.remove_get0; [eapply REMOVE_RSV1 | eauto..]; ii; des.
    eapply SOUND in GET1; eauto; des.
    rewrite INJ in GET1; inv GET1.
    rewrite GET in GET3. inv GET3.
  }
  {
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss.
    eapply RSV_COMPLETE in H.
    erewrite Memory.remove_o; eauto.
    des_if. ss. destruct a; subst. des; ss.
    exploit Memory.remove_get0; [eapply REMOVE_RSV1 | eauto..]; ii; des.
    rewrite H in GET; inv GET.
    ss.
  }
Qed.

Lemma promise_inj_weak_split
      inj promises promises' loc from to ts val msg1 msg2 from' to' msg1' msg2' ts' promises1 promises1'
      (P_INJ: promise_inj_weak inj promises promises')
      (SPLIT1: Memory.split promises loc from to ts msg1 msg2 promises1)
      (SPLIT2: Memory.split promises' loc from' to' ts' msg1' msg2' promises1')
      (INJ: inj loc to = Some to')
      (INJ': inj loc ts = Some ts')
      (MON: monotonic_inj inj)
      (CONCRETE_MSG1: exists released, msg1 = Message.concrete val released)
      (CONCRETE_MSG1': exists released, msg1' = Message.concrete val released)
      (CONCRETE_MSG2: exists val released, msg2 = Message.concrete val released)
      (CONCRETE_MSG2': exists val released, msg2' = Message.concrete val released):
  promise_inj_weak inj promises1 promises1'.
Proof.
  subst. des; subst.
  inv P_INJ.
  econs; ii.
  {
    dup H.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; eauto; ss; des; subst.
    {
      inv H.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
      rewrite GET1 in H0; inv H0.
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
      do 3 eexists. split; eauto.
      split; eauto.
      exploit MemoryProps.split_succeed_wf; [eapply SPLIT2 | eauto..]. ii; des; eauto.
    }
    {
      des_ifH H; ss; des; subst; ss. 
      exploit SOUND; [eapply H | eauto..]; ii; des. 
      assert(Memory.get loc0 to'0 promises1' = Some (from'0, Message.concrete val2 released')).
      {
        erewrite Memory.split_o; eauto.
        des_if; ss; subst; des; subst; ss; eauto.
        des_if; ss; subst; des; subst; ss; eauto.
        des_if; ss; subst; des; subst; ss.
      }
      do 3 eexists. split; eauto.
      exploit SOUND; [eapply H | eauto..]; ii; des.
      assert(Memory.get loc0 to'0 promises1' = Some (from'0, Message.concrete val2 released')).
      {
        erewrite Memory.split_o; eauto.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
      }
      do 3 eexists. split; eauto.
    }
    des_ifH H; ss; des; subst; ss.
    {
      inv H.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
      rewrite GET2 in H0; inv H0.
      exploit SOUND; eauto. ii; des.
      rewrite INJ' in H. inv H.
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
      rewrite GET4 in H0. inv H0.
      do 3 eexists. split; eauto.
      split; eauto.
      exploit MemoryProps.split_succeed_wf; [eapply SPLIT2 | eauto..]. ii; des; eauto.
    }
    {
      exploit SOUND; eauto. ii; des.
      assert(Memory.get loc0 to'0 promises1' = Some (from'0, Message.concrete val2 released')).
      {
        erewrite Memory.split_o; eauto.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
      }
      do 3 eexists. split; eauto.
    }
    {
      exploit SOUND; eauto. ii; des.
      do 3 eexists.
      split; eauto.
      erewrite Memory.split_o; eauto.
      instantiate (2 := released').
      instantiate (1 := from'0).
      des_if; ss; des; subst.
      clear - INJ o H1 MON.
      exploit monotonic_inj_implies_disj_mapping; [eapply MON | eapply H1 | eapply INJ | eapply o | eauto..].
      ii; ss.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      clear - INJ' o0 H1 MON.
      exploit monotonic_inj_implies_disj_mapping; [eapply MON | eapply H1 | eapply INJ' | eapply o0 | eauto..].
      ii; ss.
    }
  }
  {
    dup H.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; eauto; ss; des; subst.
    {
      inv H.
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
      rewrite GET1 in H0; inv H0.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
      do 3 eexists. split; eauto.
    }
    {
      des_ifH H; ss; des; subst; ss. 
      exploit COMPLETE; [eapply H | eauto..]; ii; des.  
      assert(Memory.get loc0 to0 promises1 = Some (from0, Message.concrete val2 released3)).
      {
        erewrite Memory.split_o; eauto.
        des_if; ss; subst; des; subst; ss; eauto.
        des_if; ss; subst; des; subst; ss; eauto.
        des_if; ss; subst; des; subst; ss.
      }
      do 3 eexists. split; eauto.
      exploit COMPLETE; [eapply H | eauto..]; ii; des.
      assert(Memory.get loc0 to0 promises1 = Some (from0, Message.concrete val2 released3)).
      {
        erewrite Memory.split_o; eauto.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
      }
      do 3 eexists. split; eauto.
    }
    des_ifH H; ss; des; subst; ss.
    {
      inv H.
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
      rewrite GET2 in H0; inv H0.
      exploit COMPLETE; eauto. ii; des.
      assert(to0 = ts).
      {
        clear - MON INJ' H.
        destruct(Time.eq_dec to0 ts); eauto.
        exploit monotonic_inj_implies_disj_mapping; [eapply MON | eapply H | eapply INJ' | eapply n | eauto..].
        ii; ss.
      }
      subst.
      rewrite INJ' in H. inv H.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
      rewrite GET4 in H0. inv H0.
      do 3 eexists. split; eauto.
    }
    {
      exploit COMPLETE; eauto. ii; des.
      assert(Memory.get loc0 to0 promises1 = Some (from0, Message.concrete val2 released3)).
      {
        erewrite Memory.split_o; eauto.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
        des_if; ss; subst; des; subst; ss.
      }
      do 3 eexists. split; eauto.
    }
    {
      exploit COMPLETE; eauto. ii; des.
      do 3 eexists.
      split; eauto.
      erewrite Memory.split_o; eauto.
      instantiate (1 := released3).
      instantiate (1 := from0).
      des_if; ss; des; subst.
      clear - INJ o H1 MON.
      rewrite INJ in H1. inv H1. ss.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      rewrite INJ' in H1. inv H1. ss.
    }
  }
  {
    erewrite Memory.split_o in H; eauto.
    des_ifH H; eauto; ss; des; ss.
    des_ifH H; eauto; ss; des; ss.
    eapply RSV_SOUND in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    eapply RSV_SOUND in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_ifH H; eauto; ss; des; ss.
    eapply RSV_SOUND in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    eapply RSV_SOUND in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    subst.
    exploit Memory.split_get0; [eapply SPLIT2 | eauto..]; ii; des.
    rewrite H in GET. ss.    
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    subst.
    exploit Memory.split_get0; [eapply SPLIT2 | eauto]; ii; des.
    rewrite GET0 in H. inv H.
  }
  {
    erewrite Memory.split_o in H; eauto.
    des_ifH H; eauto; ss; des; ss.
    des_ifH H; eauto; ss; des; ss.
    eapply RSV_COMPLETE in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    eapply RSV_COMPLETE in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_ifH H; eauto; ss; des; ss.
    eapply RSV_COMPLETE in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    eapply RSV_COMPLETE in H.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; ss.
    subst.
    exploit Memory.split_get0; [eapply SPLIT1 | eauto]; ii; des.
    rewrite H in GET. ss.
    des_if; ss; des; ss.
    des_if; ss; des; ss.
    subst.
    exploit Memory.split_get0; [eapply SPLIT1 | eauto]; ii; des.
    rewrite GET0 in H. inv H.
  }
Qed.
  
Lemma promise_inj_weak_lower
      inj promises promises' loc from to msg1 msg2 from' to' msg1' msg2' promises1 promises1'
      (P_INJ: promise_inj_weak inj promises promises')
      (LOWER1: Memory.lower promises loc from to msg1 msg2 promises1)
      (LOWER2: Memory.lower promises' loc from' to' msg1' msg2' promises1')
      (CONCRETE: exists val released, msg1 = Message.concrete val released)
      (INJ: inj loc to = Some to'):
  promise_inj_weak inj promises1 promises1'.
Proof.
  inv P_INJ. des; subst.
  econs; ii.
  {
    erewrite Memory.lower_o in H; eauto.
    des_ifH H; eauto; ss; des; subst; ss. 
    {
      inv H. 
      eapply Memory.lower_get0 in LOWER1; eauto; des.
      inv MSG_LE.
      exploit SOUND; eauto; ii; des.
      rewrite INJ in H; inv H.
      eapply Memory.lower_get0 in LOWER2; eauto; des.
      rewrite GET1 in H0; inv H0.
      inv MSG_LE. do 3 eexists. split; eauto. 
    }
    {
      eapply SOUND in H; eauto; des; subst.
      eapply Memory.lower_get1 in LOWER2; eauto; des.
      inv MSG_LE.
      do 3 eexists.
      split; eauto.
    }
    {
      eapply SOUND in H; eauto. des; subst.
      eapply Memory.lower_get1 in LOWER2; eauto; des.
      inv MSG_LE.
      do 3 eexists.
      split; eauto.
    }
  }
  {
    erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; eauto.
    {
      inv H.
      eapply Memory.lower_get0 in LOWER1; eauto; des. inv MSG_LE.
      eapply Memory.lower_get0 in LOWER2; eauto; des. inv MSG_LE.
      exploit SOUND; eauto. ii; des.
      rewrite INJ in H; inv H.
      rewrite GET1 in H0. inv H0.
      do 3 eexists. split; eauto.
      exploit SOUND; eauto. ii; des.
      rewrite INJ in H; inv H.
      rewrite GET1 in H0; inv H0.
    }
    {
      eapply COMPLETE in H; eauto. des.
      exploit Memory.lower_get1; [eapply LOWER1 | eauto..].
      ii; des. inv MSG_LE.
      do 3 eexists. split; eauto.
    }
    {
      eapply COMPLETE in H; eauto. des.
      exploit Memory.lower_get1; [eapply LOWER1 | eauto..].
      ii; des. inv MSG_LE.
      do 3 eexists. split; eauto.
    }
  }
  {
    erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss; des; subst; eauto.
    {
      inv H.
      eapply Memory.lower_get0 in LOWER1; eauto; des.
      inv MSG_LE.
    }
    {
      eapply RSV_SOUND in H.
      erewrite Memory.lower_o; eauto.
      des_if; eauto; ss; des; subst; ss.
    }
    {
      eapply RSV_SOUND in H.
      erewrite Memory.lower_o; eauto.
      des_if; eauto; ss; des; subst; ss.
      eapply Memory.lower_get0 in LOWER1; eauto; des.
      eapply Memory.lower_get0 in LOWER2; eauto; des.
      eapply SOUND in GET; des; eauto.
      rewrite INJ in GET; inv GET.
      rewrite GET3 in GET1; inv GET1.
      inv MSG_LE.
      rewrite GET3 in H. inv H.
    }
  }
  {
    erewrite Memory.lower_o in H; eauto.
    des_ifH H; eauto; ss; des; ss; subst.
    {
      inv H.
      eapply Memory.lower_get0 in LOWER1; eauto; des.
      inv MSG_LE.
      eapply SOUND in GET; eauto; des.
      rewrite INJ in GET; inv GET.
      eapply Memory.lower_get0 in LOWER2; eauto; des.
      rewrite GET1 in GET; inv GET.
      inv MSG_LE.
    }
    {
      eapply RSV_COMPLETE in H.
      erewrite Memory.lower_o; eauto.
      des_if; eauto; ss; subst; des; ss.
    }
    {
      eapply RSV_COMPLETE in H.
      erewrite Memory.lower_o; eauto.
      des_if; eauto; ss; des; subst; ss.
      eapply Memory.lower_get0 in LOWER1; eauto; des.
      rewrite GET in H. inv H.
    }
  }
Qed.

Lemma mem_nonsynch_loc_msgInj_weak
      promises promises' mem mem' inj loc
      (MEM_INJ: MsgInj inj mem mem')
      (LE1: Memory.le promises mem)
      (LE2: Memory.le promises' mem')
      (PROM_INJ: promise_inj_weak inj promises promises')
      (NONSYNC_LOC: Memory.nonsynch_loc loc promises):
  Memory.nonsynch_loc loc promises'.
Proof.
  unfold Memory.nonsynch_loc in *; ii.
  inv PROM_INJ.
  destruct msg; ss. 
  dup GET.
  exploit COMPLETE; eauto. ii; des.
  exploit NONSYNC_LOC; eauto. ii; ss; subst.
  inv MEM_INJ.
  dup H0.
  eapply LE1 in H1.
  eapply SOUND0 in H1; eauto. des.
  rewrite H in H1. inv H1.
  unfold opt_ViewInj in H2. destruct R'; ss.
  eapply LE2 in GET.
  rewrite GET in H3. inv H3; eauto.
Qed.

Lemma mem_nonsynch_msgInj_weak
      promises promises' mem mem' inj
      (MEM_INJ: MsgInj inj mem mem')
      (LE1: Memory.le promises mem)
      (LE2: Memory.le promises' mem')
      (PROM_INJ: promise_inj_weak inj promises promises')
      (NONSYNC: Memory.nonsynch promises):
  Memory.nonsynch promises'.
Proof.
  unfold Memory.nonsynch in *. intro loc.
  specialize (NONSYNC loc).
  eapply mem_nonsynch_loc_msgInj_weak; eauto.
Qed.
  
Lemma promise_inj_weak_bot
      promises promises' inj
      (PROM_INJ: promise_inj_weak inj promises promises')
      (BOT: promises = Memory.bot):
  promises' = Memory.bot.
Proof.
  subst.
  inv PROM_INJ. 
  destruct (classic (exists loc to from msg, Memory.get loc to promises' = Some (from, msg))).
  {
    des.
    destruct msg.
    eapply COMPLETE in H; eauto; des.
    rewrite Memory.bot_get in H0; ss.
    eapply RSV_COMPLETE in H; eauto; des.
    rewrite Memory.bot_get in H; ss.
  }
  {
    eapply Memory.ext; ii.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts promises') eqn:Heqe; eauto.
    destruct p.
    contradiction H; eauto.
  }
Qed.

Lemma write_step_promise_inj_weak_stable
      lc1 sc1 mem1 loc from1 to1 val releasedr1 releasedw1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 releasedr2 releasedw2 lc2' sc2' mem2' kind2
      inj inj'
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val releasedr1 releasedw1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val releasedr2 releasedw2 ord lc2' sc2' mem2' kind2 lo)
      (PROM_INJ: promise_inj_weak inj (Local.promises lc1) (Local.promises lc2))
      (INJ_INCR: incr_inj inj inj')
      (INJ: inj' loc to1 = Some to2)
      (MON: monotonic_inj inj')
      (KIND_MATCH: kind_match kind1 kind2)
      (SPLIT: forall t val R, kind1 = Memory.op_kind_split t (Message.concrete val R) ->
                         exists t' val' R', kind2 = Memory.op_kind_split t' (Message.concrete val' R') /\
                                       to1 = to2 /\ inj loc t = Some t'):
  promise_inj_weak inj' (Local.promises lc1') (Local.promises lc2').
Proof.
  inv WRITE1; ss. inv WRITE. inv PROMISE.
  - destruct kind2; ss.
    inv WRITE2; ss. inv WRITE. inv PROMISE.
    assert(Local.promises lc1 = promises2).
    {
      eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    }
    subst.
    assert(Local.promises lc2 = promises1).
    {
      eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    }
    subst.
    eapply promise_inj_weak_incr; eauto.
  - des; subst. inv RESERVE.
    destruct kind2; ss.
    exploit SPLIT; eauto. ii; des; subst.
    inv H. des; subst.
    assert(promise_inj_weak inj' (Local.promises lc1) (Local.promises lc2)).
    {
      eapply promise_inj_weak_incr; eauto.
    }
    inv WRITE2; ss.
    inv WRITE. inv PROMISE. des; ss.
    inv RESERVE. inv RESERVEORIGINAL.
    exploit promise_inj_weak_split; eauto.
    ii.
    eapply promise_inj_weak_remove_concrete; eauto.
  - des; subst.
    destruct kind2; ss.
    inv WRITE2; ss. inv WRITE. inv PROMISE. des; subst.
    subst.
    assert(INJ'': inj loc to1 = Some to2).
    {
      clear - PROM_INJ INJ INJ_INCR PROMISES PROMISES0.
      exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
      inv PROM_INJ.
      eapply SOUND in GET; eauto. des.
      dup GET.
      eapply INJ_INCR in GET. rewrite GET in INJ. inv INJ. eauto.
    }
    exploit promise_inj_weak_lower; eauto. ii.
    eapply promise_inj_weak_incr in H; eauto.
    eapply promise_inj_weak_remove_concrete in H; eauto.
  - ss.
Qed.

Definition promise_fulfill_kind_match (kind1 kind2: Memory.op_kind) :=
  match kind1, kind2 with
  | Memory.op_kind_split to (Message.concrete val R),
    Memory.op_kind_split to' (Message.concrete val' R') => val = val'
  | Memory.op_kind_lower (Message.concrete val R),
    Memory.op_kind_lower (Message.concrete val' R') => val = val' 
  | _, _ => False
  end.

Lemma promise_fulfill_promise_inj_weak_stable
      lc1 sc1 mem1 loc from1 to1 val releasedr1 releasedw1 ord lc1' sc1' mem1' kind1 lo
      lc2 sc2 mem2 from2 to2 releasedr2 releasedw2 lc2' sc2' mem2' kind2
      inj inj'
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from1 to1 val releasedr1 releasedw1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from2 to2 val releasedr2 releasedw2 ord lc2' sc2' mem2' kind2 lo)
      (PROM_INJ: promise_inj_weak inj (Local.promises lc1) (Local.promises lc2))
      (INJ_INCR: incr_inj inj inj')
      (INJ: inj' loc to1 = Some to2)
      (MON: monotonic_inj inj')
      (KIND_MATCH: promise_fulfill_kind_match kind1 kind2)
      (SPLIT: forall t val R, kind1 = Memory.op_kind_split t (Message.concrete val R) ->
                         exists t' val' R', kind2 = Memory.op_kind_split t' (Message.concrete val' R') /\
                                       inj loc t = Some t'):
  promise_inj_weak inj' (Local.promises lc1') (Local.promises lc2').
Proof.
  destruct kind1; ss.
  - destruct msg3; ss.
    destruct kind2; ss.
    destruct msg3; ss. subst.
    inv WRITE1; ss. inv WRITE; ss. inv PROMISE; ss.
    inv WRITE2; ss. inv WRITE; ss. inv PROMISE; ss.
    des; subst. inv RESERVE0. inv RESERVEORIGINAL0. inv RESERVE.
    exploit SPLIT; eauto. ii; des; subst.
    inv H. 
    assert(promise_inj_weak inj' (Local.promises lc1) (Local.promises lc2)).
    {
      eapply promise_inj_weak_incr; eauto.
    }
    exploit promise_inj_weak_split; eauto.
    ii.
    eapply promise_inj_weak_remove_concrete; eauto.
  - destruct msg1; ss. destruct kind2; ss. destruct msg1; ss. subst.
    inv WRITE1; ss. inv WRITE; ss. inv PROMISE; ss.
    inv WRITE2; ss. inv WRITE; ss. inv PROMISE; ss.
    des; subst. inv RESERVE0.
    assert(INJ'': inj loc to1 = Some to2).
    {
      clear - PROM_INJ INJ INJ_INCR PROMISES PROMISES0.
      exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
      inv PROM_INJ.
      eapply SOUND in GET; eauto. des.
      dup GET.
      eapply INJ_INCR in GET. rewrite GET in INJ. inv INJ. eauto.
    }
    exploit promise_inj_weak_lower; eauto. ii.
    eapply promise_inj_weak_incr in H; eauto.
    eapply promise_inj_weak_remove_concrete in H; eauto.
Qed.
