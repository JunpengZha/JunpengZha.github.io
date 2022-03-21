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
Require Import NPThread.
Require Import Configuration.
Require Import MsgMapping.
Require Import DelaySet.
Require Import NPConfiguration.

Require Import Reordering.
Require Import np_to_ps_thread.
Require Import ps_to_np_thread.
Require Import MemoryProps.
Require Import WFConfig.

Require Import LocalSim.
Require Import ww_RF.

Require Import LibTactics.
Require Import ConfigInitLemmas.
Require Import Mem_at_eq_lemmas.
Require Import ConsistentProp.
Require Import PromiseConsistent.

Lemma Local_write_not_care_sc
      lc sc mem loc from to val releasedr released ord
      lc' sc' mem' kind lo sc0
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo):
  Local.write_step lc sc0 mem loc from to val releasedr released ord lc' sc0 mem' kind lo.
Proof.
  inv WRITE.
  econs; eauto.
  inv WRITABLE.
  econs; eauto.
Qed.
  
Lemma memory_additional_rsv_concrete_prsv
      mem mem' loc to from val R
      (MEM_LE: Memory.le mem mem')
      (MORE_RSV: forall loc t f msg,
          Memory.get loc t mem = None -> Memory.get loc t mem' = Some (f, msg) -> msg = Message.reserve)
      (MSG: Memory.get loc to mem' = Some (from, Message.concrete val R)):
  Memory.get loc to mem = Some (from, Message.concrete val R).
Proof.
  destruct (Memory.get loc to mem) eqn: GET.
  destruct p. eapply MEM_LE in GET.
  rewrite MSG in GET. inv GET; eauto.
  exploit MORE_RSV; eauto. ii; ss.
Qed.

Lemma tm_closed_mem_le
      mem mem' tm
      (MEM_LE: Memory.le mem mem')
      (TM_CLOSED: Memory.closed_timemap tm mem):
  Memory.closed_timemap tm mem'.
Proof.
  unfold Memory.closed_timemap in *. ii.
  specialize (TM_CLOSED loc). des.
  eauto.
Qed.
  
Lemma message_closed_rsv_concrete_prsv
      mem mem' msg
      (MEM_LE: Memory.le mem mem')
      (MORE_RSV: forall loc t f msg,
          Memory.get loc t mem = None -> Memory.get loc t mem' = Some (f, msg) -> msg = Message.reserve)
      (MSG_CLOSED: Memory.closed_message msg mem):
  Memory.closed_message msg mem'.
Proof.
  inv MSG_CLOSED; eauto.
  econs; eauto.
  inv CLOSED; eauto.
  econs.
  inv CLOSED0.
  econs; eauto.
  eapply tm_closed_mem_le; eauto.
  eapply tm_closed_mem_le; eauto.
Qed.
  
Lemma memory_closed_additional_rsv
     mem mem'
     (CLOSED_MEM: Memory.closed mem)
     (MEM_LE: Memory.le mem mem')
     (MORE_RSV: forall loc t f msg,
          Memory.get loc t mem = None -> Memory.get loc t mem' = Some (f, msg) -> msg = Message.reserve):
  Memory.closed mem'.
Proof.
  inv CLOSED_MEM.
  econs; ii.
  destruct (Memory.get loc to mem) eqn:Get.
  destruct p. destruct t0.
  exploit CLOSED; eauto. ii; des.
  exploit MEM_LE; eauto. ii. rewrite MSG in x. inv x.
  split; eauto.
  split; eauto.
  eapply message_closed_rsv_concrete_prsv; eauto.
  eapply MEM_LE in Get.
  rewrite MSG in Get. inv Get; eauto.
  split; eauto. econs.
  exploit MORE_RSV; eauto. ii; subst.
  split; eauto. econs.
  unfold Memory.inhabited in *.
  specialize (INHABITED loc).
  eauto.
Qed.

Lemma memory_add_concrete_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to msg
      (MEM_LE: Memory.le mem1 mem1')
      (MORE_RSV: forall loc t f msg,
          Memory.get loc t mem1 = None -> Memory.get loc t mem1' = Some (f, msg) -> msg = Message.reserve)
      (ADD1: Memory.add mem1 loc from to msg mem2)
      (ADD2: Memory.add mem1' loc from to msg mem2'):
  memory_concrete_le mem2' mem2.
Proof.
  unfold memory_concrete_le. ii.
  erewrite Memory.add_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  - inv GET.
    erewrite Memory.add_o; eauto.
    des_if; ss; eauto.
    des; ss.
  - erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss.
    eapply memory_additional_rsv_concrete_prsv; eauto.
    eapply memory_additional_rsv_concrete_prsv; eauto.
  - erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss.
    eapply memory_additional_rsv_concrete_prsv; eauto.
    eapply memory_additional_rsv_concrete_prsv; eauto.
Qed.

Lemma memory_split_concrete_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to ts msg msg'
      (MEM_LE: Memory.le mem1 mem1')
      (MORE_RSV: forall loc t f msg,
          Memory.get loc t mem1 = None -> Memory.get loc t mem1' = Some (f, msg) -> msg = Message.reserve)
      (ADD1: Memory.split mem1 loc from to ts msg msg' mem2)
      (ADD2: Memory.split mem1' loc from to ts msg msg' mem2'):
  memory_concrete_le mem2' mem2.
Proof.
  unfold memory_concrete_le in *. ii.
  erewrite Memory.split_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  - inv GET.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
  - des_ifH GET; ss; des; subst; ss.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
  - des_ifH GET; ss; des; subst; ss.
    + inv GET.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      des_if; ss; des; subst; ss; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
      eapply memory_additional_rsv_concrete_prsv; eauto.
Qed.

Lemma memory_lower_concrete_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to msg msg'
      (MEM_LE: Memory.le mem1 mem1')
      (MORE_RSV: forall loc t f msg,
          Memory.get loc t mem1 = None -> Memory.get loc t mem1' = Some (f, msg) -> msg = Message.reserve)
      (ADD1: Memory.lower mem1 loc from to msg msg' mem2)
      (ADD2: Memory.lower mem1' loc from to msg msg' mem2'):
  memory_concrete_le mem2' mem2.
Proof.
  unfold memory_concrete_le in *. ii.
  erewrite Memory.lower_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  - inv GET.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss.
  - erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss.
    eapply memory_additional_rsv_concrete_prsv; eauto.
    eapply memory_additional_rsv_concrete_prsv; eauto.
  - erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss.
    eapply memory_additional_rsv_concrete_prsv; eauto.
    eapply memory_additional_rsv_concrete_prsv; eauto.
Qed.
  
Lemma memory_add_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to msg
      (MEM_LE: Memory.le mem1 mem1')
      (ADD1: Memory.add mem1 loc from to msg mem2)
      (ADD2: Memory.add mem1' loc from to msg mem2'):
  Memory.le mem2 mem2'.
Proof.
  unfold Memory.le in *. ii.
  erewrite Memory.add_o in LHS; eauto.
  des_ifH LHS; des; ss; subst; ss.
  - inv LHS.
    erewrite Memory.add_o; eauto.
    des_if; ss; eauto. des; subst; ss.
  - erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma memory_split_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to ts msg msg'
      (MEM_LE: Memory.le mem1 mem1')
      (ADD1: Memory.split mem1 loc from to ts msg msg' mem2)
      (ADD2: Memory.split mem1' loc from to ts msg msg' mem2'):
  Memory.le mem2 mem2'.
Proof.
  unfold Memory.le in *. ii.
  erewrite Memory.split_o in LHS; eauto.
  des_ifH LHS; des; ss; subst; ss.
  - inv LHS.
    exploit Memory.split_get0; eauto. ii; des; eauto.
  - des_ifH LHS; des; ss; subst; ss.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
  - des_ifH LHS; ss; des; subst; ss.
    + inv LHS.
      exploit Memory.split_get0; eauto. ii; des; eauto.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
    + erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
      des_if; ss; des; subst; ss; eauto.
Qed.

Lemma memory_lower_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to msg msg'
      (MEM_LE: Memory.le mem1 mem1')
      (ADD1: Memory.lower mem1 loc from to msg msg' mem2)
      (ADD2: Memory.lower mem1' loc from to msg msg' mem2'):
  Memory.le mem2 mem2'.
Proof.
  unfold Memory.le in *; ii.
  erewrite Memory.lower_o in LHS; eauto.
  des_ifH LHS; des; ss; subst; ss.
  - inv LHS.
    exploit Memory.lower_get0; eauto. ii; des; eauto.
  - erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma memory_remove_le_rsv_prsv
      mem1 mem1' mem2 mem2' loc from to msg
      (MEM_LE: Memory.le mem1 mem1')
      (REMOVE1: Memory.remove mem1 loc from to msg mem2)
      (REMOVE2: Memory.remove mem1' loc from to msg mem2'):
  Memory.le mem2 mem2'.
Proof.
  unfold Memory.le in *; ii.
  erewrite Memory.remove_o in LHS; eauto.
  des_ifH LHS; des; ss; subst; ss.
  - erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma Memory_le_remove_stable
      promises promises' mem loc from to msg
      (MEM_LE: Memory.le promises mem)
      (REMOVE: Memory.remove promises loc from to msg promises'):
  Memory.le promises' mem.
Proof.
  unfold Memory.le in *; ii.
  erewrite Memory.remove_o in LHS; eauto.
  des_ifH LHS; ss; des; subst; ss; eauto.
Qed.

Lemma Local_read_step_cap_prsv
      lc mem_c mem lc' released ord val to loc lo
      (READ: Local.read_step lc mem_c loc to val released ord lc' lo)
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve):
  Local.read_step lc mem loc to val released ord lc' lo.
Proof.
  inv READ.
  exploit memory_additional_rsv_concrete_prsv;
    [eapply MEM_LE | eapply MORE_RESERVE | eapply GET | eauto..]; eauto.
Qed.
  
Lemma Local_write_step_cap_prsv
      lo lc sc mem_c mem lc' sc' mem_c' releasedr released kind ord val from to loc
      (WRITE: Local.write_step lc sc mem_c loc from to val releasedr released ord lc' sc' mem_c' kind lo)
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists mem',
    Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo /\
    Memory.le mem' mem_c' /\
    (forall loc to from msg, Memory.get loc to mem' = None ->
                        Memory.get loc to mem_c' = Some (from, msg) ->
                        msg = Message.reserve) /\
    Memory.le (Local.promises lc') mem'.
Proof.
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  {
    (* add *)
    exploit add_succeed_wf; eauto. ii. des.
    lets ADD_MEM: MSG_WF. eapply Memory.add_exists with (mem1 := mem) in ADD_MEM; eauto. des.
    eexists mem2.
    split.
    {
      econs; eauto.
    }
    split.
    {
      eapply memory_add_le_rsv_prsv; [eapply MEM_LE | eapply ADD_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      erewrite Memory.add_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.add_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    {
      eapply memory_add_le_rsv_prsv with (mem2 := promises0) (mem2' := mem2) in PRM_LE; eauto.
      eapply Memory_le_remove_stable; eauto.
    }
  }
  {
    (* split *)
    des; subst.
    exploit split_succeed_wf; eauto. ii; des.
    lets SPLIT_MEM: MSG_WF. 
    eapply Memory.split_exists with
        (mem1 := mem) (loc := loc) (ts1 := from) (ts2 := to) (ts3 := ts3)
        (msg3 := Message.concrete val' released') in SPLIT_MEM; eauto. des.
    eexists mem2.
    split.
    {
      econs; eauto. econs; eauto. econs; eauto.
    }
    split.
    {
      eapply memory_split_le_rsv_prsv; [eapply MEM_LE | eapply SPLIT_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    {
      eapply memory_split_le_rsv_prsv with (mem2 := promises0) (mem2' := mem2) in PRM_LE; eauto.
      eapply Memory_le_remove_stable; eauto.
    }
  }
  {
    (* lower *)
    des; subst.
    exploit lower_succeed_wf; eauto. ii. des.
    lets LOWER_MEM: MSG_WF.
    eapply Memory.lower_exists with (mem1 := mem) (msg1 := Message.concrete val released) in LOWER_MEM; eauto. des.
    eexists mem2.
    split.
    {
      inv MSG_LE.
      econs; eauto. 
    }
    split.
    {
      inv MSG_LE.
      eapply memory_lower_le_rsv_prsv; [eapply MEM_LE | eapply LOWER_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    {
      eapply memory_lower_le_rsv_prsv with (mem2 := promises0) (mem2' := mem2) in PRM_LE; eauto.
      eapply Memory_le_remove_stable; eauto.
      inv MSG_LE; eauto.
    }
    {
      inv MSG_LE; eauto.
    }
    {
      inv MSG_LE; eauto.
    }
  }
Qed.

Lemma promise_step_cap_prsv
      lang st lc sc mem_c mem st' lc' sc' mem_c' te pf
      (PROM_STEP: Thread.promise_step pf te (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists mem', Thread.promise_step pf te (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem') /\
          Memory.le mem' mem_c' /\
          (forall loc to from msg, Memory.get loc to mem' = None ->
                              Memory.get loc to mem_c' = Some (from, msg) ->
                              msg = Message.reserve) /\
          Memory.le (Local.promises lc') mem' /\
          (forall loc to from msg,
              Memory.get loc to mem_c = Some (from, msg) -> Memory.get loc to mem = None ->
              (Memory.get loc to mem_c' = Some (from, msg) /\ Memory.get loc to mem' = None)).
Proof.
  inv PROM_STEP. inv LOCAL; ss. inv PROMISE.
  - (* promise add *)
    exploit add_succeed_wf; eauto. ii. des.
    lets ADD_MEM: MSG_WF. eapply Memory.add_exists with (mem1 := mem) in ADD_MEM; eauto. des.
    eexists mem2.
    split.
    {
      econs; eauto. econs; eauto.
      eapply memory_concrete_le_closed_msg; eauto.
      eapply memory_add_concrete_le_rsv_prsv;
        [eapply MEM_LE | eapply MORE_RESERVE | eapply ADD_MEM | eapply MEM]; eauto.
    }
    split.
    {
      eapply memory_add_le_rsv_prsv; [eapply MEM_LE | eapply ADD_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      erewrite Memory.add_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.add_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    split.
    {
      eapply memory_add_le_rsv_prsv; [eapply PRM_LE | eapply PROMISES | eapply ADD_MEM | eauto..].
    }
    {
      ii. split.
      erewrite Memory.add_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      exploit Memory.add_get0; [eapply MEM | eauto..]. ii; des.
      rewrite H in GET; ss.
      erewrite Memory.add_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      exploit Memory.add_get0; [eapply MEM | eauto..]. ii; des.
      rewrite H in GET; ss.
    }
  - (* promise split *)
    des; subst.
    exploit split_succeed_wf; eauto. ii; des.
    lets SPLIT_MEM: MSG_WF. 
    eapply Memory.split_exists with
        (mem1 := mem) (loc := loc) (ts1 := from) (ts2 := to) (ts3 := ts3)
        (msg3 := Message.concrete val' released') in SPLIT_MEM; eauto. des.
    eexists mem2.
    split.
    {
      econs; eauto.
      econs; eauto. econs; eauto.
      eapply memory_concrete_le_closed_msg; eauto.
      eapply memory_split_concrete_le_rsv_prsv;
        [eapply MEM_LE | eapply MORE_RESERVE | eapply SPLIT_MEM | eapply MEM | eauto..].
    }
    split.
    {
      eapply memory_split_le_rsv_prsv; [eapply MEM_LE | eapply SPLIT_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    split.
    {
      eapply memory_split_le_rsv_prsv; [eapply PRM_LE | eapply PROMISES | eapply SPLIT_MEM | eauto..].
    }
    {
      ii. split.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
      rewrite H in GET; ss.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      exploit Memory.split_get0; [eapply SPLIT_MEM | eauto..]. ii; des.
      rewrite H0 in GET0; ss.
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
      rewrite H in GET; ss.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      exploit Memory.split_get0; [eapply SPLIT_MEM | eauto..]. ii; des.
      rewrite H0 in GET0. ss.
    }
    {
      exploit Memory.split_get0; eauto. ii; des.
      eapply memory_additional_rsv_concrete_prsv; eauto.
    }
  - (* promise lower *)
    des; subst.
    exploit lower_succeed_wf; eauto. ii. des.
    lets LOWER_MEM: MSG_WF.
    eapply Memory.lower_exists with (mem1 := mem) (msg1 := Message.concrete val released) in LOWER_MEM; eauto. des.
    eexists mem2.
    split.
    {
      econs; eauto.
      econs; eauto.
      eapply memory_concrete_le_closed_msg; eauto.
      eapply memory_lower_concrete_le_rsv_prsv;
        [eapply MEM_LE | eapply MORE_RESERVE | eapply LOWER_MEM | eapply MEM | eauto..].
    }
    split.
    {
      eapply memory_lower_le_rsv_prsv; [eapply MEM_LE | eapply LOWER_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    split.
    {
      eapply memory_lower_le_rsv_prsv; [eapply PRM_LE | eapply PROMISES | eapply LOWER_MEM | eauto..].
    }
    {
      ii. split.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.lower_get0; [eapply LOWER_MEM | eauto..]. ii; des.
      rewrite H0 in GET0; ss.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.lower_get0; [eapply LOWER_MEM | eauto..]. ii; des.
      rewrite H0 in GET0; ss.
    }
  - (* promise cancel *)
    exploit Memory.remove_get0; [eapply PROMISES | eauto..]. ii; des.
    exploit PRM_LE; [eapply GET | eauto..]. introv GET_REMOVE_MEM.
    exploit Memory.remove_exists; [eapply GET_REMOVE_MEM | eauto..].
    introv REMOVE_MEM. destruct REMOVE_MEM as (mem2 & REMOVE_MEM).
    eexists.
    split.
    econs; eauto.
    split.
    {
      eapply memory_remove_le_rsv_prsv; [eapply MEM_LE | eapply REMOVE_MEM | eapply MEM | eauto..].
    }
    split.
    {
      ii.
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss; eauto.
    }
    split.
    {
      eapply memory_remove_le_rsv_prsv;
      [eapply PRM_LE | eapply PROMISES | eapply REMOVE_MEM | eauto..].
    }
    {
      ii. split.
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss.
      exploit Memory.remove_get0; [eapply REMOVE_MEM | eauto..].
      ii; des.
      rewrite H0 in GET1. ss.
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss.
    }
Qed.

Lemma program_step_cap_prsv
      lang st lc sc mem_c mem st' lc' sc' mem_c' te lo
      (PROG_STEP: Thread.program_step te lo (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists mem', Thread.program_step te lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem') /\
          Memory.le mem' mem_c' /\
          (forall loc to from msg, Memory.get loc to mem' = None ->
                              Memory.get loc to mem_c' = Some (from, msg) ->
                              msg = Message.reserve) /\
          Memory.le (Local.promises lc') mem'.
Proof.
  inv PROG_STEP. inv LOCAL; ss.
  + (* tau step *)
    exists mem.
    split. econs; eauto.
    split; eauto.
  + (* read step *)
    exists mem.
    split; eauto.
    econs; eauto.
    econs. eapply Local_read_step_cap_prsv; eauto.
    split; eauto.
    split; eauto.
    inv LOCAL0; eauto.
  + (* write step *)
    exploit Local_write_step_cap_prsv; eauto. ii; des.
    eexists mem'.
    split.
    econs; eauto.
    split; eauto. 
  + (* update step *)
    inv LOCAL1.
    exploit memory_additional_rsv_concrete_prsv;
      [eapply MEM_LE | eapply MORE_RESERVE | eapply GET | eauto..]; eauto.
    introv READ_MEM.
    exploit Local_write_step_cap_prsv; eauto. ii; des.
    eexists mem'.
    split.
    econs; eauto.
    eauto.
  + (* fence *)
    exists mem.
    split. 
    econs; eauto.
    split; eauto.
    split; eauto.
    inv LOCAL0; ss; eauto.
  + (* out put *)
    exists mem.
    split.
    econs; eauto.
    split; eauto.
    split; eauto.
    inv LOCAL0; ss; eauto.
Qed.
  
Lemma step_cap_prsv
      lang lo st lc sc mem_c mem st' lc' sc' mem_c' te pf
      (STEP: Thread.step lo pf te (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists mem', Thread.step lo pf te (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem') /\
          Memory.le mem' mem_c' /\
          (forall loc to from msg, Memory.get loc to mem' = None ->
                              Memory.get loc to mem_c' = Some (from, msg) ->
                              msg = Message.reserve) /\
          Memory.le (Local.promises lc') mem'.
Proof.
  inv STEP.
  - exploit promise_step_cap_prsv; eauto. ii; des.
    eexists.
    split. econs; eauto.
    split; eauto.
  - eapply program_step_cap_prsv in STEP0; eauto. des.
    exists mem'.
    split.
    eapply Thread.step_program. eauto.
    split; eauto.
Qed.

Lemma tau_step_cap_prsv
      lang lo st lc sc mem_c mem st' lc' sc' mem_c'
      (STEP: Thread.tau_step lo (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists mem', Thread.tau_step lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem') /\
          Memory.le mem' mem_c' /\
          (forall loc to from msg, Memory.get loc to mem' = None ->
                              Memory.get loc to mem_c' = Some (from, msg) ->
                              msg = Message.reserve) /\
          Memory.le (Local.promises lc') mem'.
Proof.
  inv STEP. inv TSTEP.
  exploit step_cap_prsv; eauto. ii; des.
  eexists. split.
  econs. econs. eauto. eauto.
  split; eauto.
Qed.

Lemma all_step_cap_prsv
      lang lo st lc sc mem_c mem st' lc' sc' mem_c'
      (STEP: Thread.all_step lo (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists mem', Thread.all_step lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem') /\
          Memory.le mem' mem_c' /\
          (forall loc to from msg, Memory.get loc to mem' = None ->
                              Memory.get loc to mem_c' = Some (from, msg) ->
                              msg = Message.reserve) /\
          Memory.le (Local.promises lc') mem'.
Proof.
  inv STEP. inv USTEP.
  exploit step_cap_prsv; eauto. ii; des.
  eexists. split.
  econs. econs. eauto.
  split; eauto.
Qed.
  
Lemma fulfill_cap:
  forall n lang lo st lc sc mem_c mem e_c'
    (FULFILL: rtcn (@Thread.tau_step lang lo) n (Thread.mk lang st lc sc mem_c) e_c')
    (BOT: Local.promises (Thread.local e_c') = Memory.bot)
    (MEM_LE: Memory.le mem mem_c)
    (MORE_RESERVE: 
       forall loc to from msg, Memory.get loc to mem = None ->
                          Memory.get loc to mem_c = Some (from, msg) ->
                          msg = Message.reserve)
    (PRM_LE: Memory.le (Local.promises lc) mem),
  exists e',
    rtc (@Thread.tau_step lang lo) (Thread.mk lang st lc sc mem) e' /\
    Local.promises (Thread.local e') = Memory.bot.
Proof.
  induction n; ii; ss.
  - inv FULFILL; ss.
    eexists. split. eauto. ss.
  - inv FULFILL. destruct a2.
    eapply tau_step_cap_prsv in A12; eauto. des.
    eapply IHn in A23; eauto. ii; des.
    eexists.
    split.
    eapply Relation_Operators.rt1n_trans; [eapply A12 | eapply A23].
    eauto.
Qed. 

Lemma noscfence_steps_fulfill_cap:
  forall n lang lo st lc sc mem_c mem e_c'
    (FULFILL: rtcn (no_scfence_nprm_step lang lo) n (Thread.mk lang st lc sc mem_c) e_c')
    (BOT: Local.promises (Thread.local e_c') = Memory.bot)
    (MEM_LE: Memory.le mem mem_c)
    (MORE_RESERVE: 
       forall loc to from msg, Memory.get loc to mem = None ->
                          Memory.get loc to mem_c = Some (from, msg) ->
                          msg = Message.reserve)
    (PRM_LE: Memory.le (Local.promises lc) mem),
  exists e',
    rtc (no_scfence_nprm_step lang lo) (Thread.mk lang st lc sc mem) e' /\
    Local.promises (Thread.local e') = Memory.bot.
Proof.
  induction n; ii.
  - inv FULFILL; ss. eauto.
  - inv FULFILL. destruct a2. inv A12.
    + eapply program_step_cap_prsv in STEP; eauto.
      des.
      eapply IHn in A23; eauto. des.
      exists e'.
      split; eauto.
      eapply Relation_Operators.rt1n_trans.
      eapply no_scfence_nprm_step_intro1; eauto.
      eauto.
    + eapply promise_step_cap_prsv in STEP; eauto.
      des.
      eapply IHn in A23; eauto. des.
      exists e'.
      split; eauto.
      eapply Relation_Operators.rt1n_trans.
      eapply no_scfence_nprm_step_intro2; eauto.
      eauto.
Qed.

Lemma Thread_nprm_implies_fulfill
      lang st lc sc mem lo
      (CONSISTENT: Thread.consistent_nprm (Thread.mk lang st lc sc mem) lo)
      (LOCAL_WF: Local.wf lc mem)
      (MEM_CLOSED: Memory.closed mem):
  exists e,
    rtc (@Thread.nprm_step lang lo) (Thread.mk lang st lc sc mem) e /\
    Local.promises (Thread.local e) = Memory.bot.
Proof.
  unfold Thread.consistent_nprm in CONSISTENT; ss.
  exploit Memory.cap_exists; eauto. ii; des.
  exploit Memory.cap_closed; eauto. ii.
  exploit Memory.max_concrete_timemap_exists; [eapply x0 | eauto..].
  ii; des.
  exploit CONSISTENT; eauto.
  ii; des.
  eapply rtc_rtcn in STEPS. des.
  exploit nprm_steps_fulfill_implies_no_scfence_nprm_step_fulfill; [eapply STEPS | eapply PROMISES | eauto..].
  ii; des.
  destruct e0; ss.
  eapply no_scfence_nprm_steps_not_care_sc with (sc0 := sc) in x2; eauto.
  eapply rtc_rtcn in x2. des. 
  eapply noscfence_steps_fulfill_cap with (mem_c := mem2) (mem := mem) in x2; eauto.
  des.
  eapply no_scfence_nprm_steps_is_nprm_steps in x2.
  eexists. split. eapply x2. eauto.
  inv CAP; eauto.
  ii. 
  eapply Memory.cap_inv with (mem1 := mem) in H0; eauto.
  des; eauto.
  rewrite H in H0; ss.
  inv LOCAL_WF; eauto.
Qed.
  
Lemma cap_abort_to_abort':
  forall n lang lo st lc sc mem_c mem e_srcc'
    (TO_CAP_ABORT: rtcn (@Thread.tau_step lang lo) n (Thread.mk lang st lc sc mem_c) e_srcc')
    (CAP_ABORT: Thread.is_abort e_srcc' lo)
    (MEM_LE: Memory.le mem mem_c)
    (MORE_RESERVE: 
       forall loc to from msg, Memory.get loc to mem = None ->
                          Memory.get loc to mem_c = Some (from, msg) ->
                          msg = Message.reserve)
    (PRM_LE: Memory.le (Local.promises lc) mem),
  exists e_src',
    rtc (@Thread.tau_step lang lo) (Thread.mk lang st lc sc mem) e_src' /\ Thread.is_abort e_src' lo.
Proof.
  induction n; ii.
  - inv TO_CAP_ABORT.
    eexists. split. eauto.
    inv CAP_ABORT; ss.
  - inv TO_CAP_ABORT.
    destruct a2.
    eapply tau_step_cap_prsv in A12; eauto. des.
    eapply IHn in A23; eauto. des.
    eexists.
    split.
    eapply Relation_Operators.rt1n_trans; [eapply A12 | eapply A23].
    eauto.
Qed.
  
Lemma cap_abort_to_abort
      lang lo st lc sc mem_c mem e_srcc'
      (TO_CAP_ABORT: rtc (@Thread.tau_step lang lo) (Thread.mk lang st lc sc mem_c) e_srcc')
      (CAP_ABORT: Thread.is_abort e_srcc' lo)
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem = None ->
                            Memory.get loc to mem_c = Some (from, msg) ->
                            msg = Message.reserve)
      (PRM_LE: Memory.le (Local.promises lc) mem):
  exists e_src',
    rtc (@Thread.tau_step lang lo) (Thread.mk lang st lc sc mem) e_src' /\ Thread.is_abort e_src' lo.
Proof.
  eapply rtc_rtcn in TO_CAP_ABORT. des.
  eapply cap_abort_to_abort'; eauto.
Qed.

Lemma memory_add_disj_loc_stable
      mem1 loc from to msg mem2 loc0
      (ADD: Memory.add mem1 loc from to msg mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  destruct (Memory.get loc0 ts mem2) eqn:GET; ss.
  lets GET': GET. unfold Memory.get in GET'. rewrite GET'.
  destruct p. destruct t0.
  erewrite Memory.add_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  erewrite Memory.add_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  destruct (Memory.get loc0 ts mem1) eqn:GET_o; eauto.
  erewrite Memory.add_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; tryfalse.
  unfold Memory.get in *.
  rewrite GET, GET_o. eauto.
Qed.

Lemma memory_split_disj_loc_stable
      mem1 loc from to ts msg msg' mem2 loc0
      (ADD: Memory.split mem1 loc from to ts msg msg' mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  destruct (Memory.get loc0 ts0 mem2) eqn:GET; ss.
  lets GET': GET. unfold Memory.get in GET'. rewrite GET'.
  destruct p. destruct t0.
  erewrite Memory.split_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  erewrite Memory.split_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  lets GET': GET. unfold Memory.get in GET'. rewrite GET'.
  erewrite Memory.split_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
  des_ifH GET; ss; des; subst; ss; eauto.
Qed.

Lemma memory_lower_disj_loc_stable
      mem1 loc from to msg msg' mem2 loc0
      (ADD: Memory.lower mem1 loc from to msg msg' mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  destruct (Memory.get loc0 ts mem2) eqn:GET; ss.
  lets GET': GET. unfold Memory.get in GET'. rewrite GET'.
  destruct p. destruct t0.
  erewrite Memory.lower_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss. 
  erewrite Memory.lower_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  destruct (Memory.get loc0 ts mem1) eqn:GET_o; eauto.
  erewrite Memory.lower_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; tryfalse.
  unfold Memory.get in *.
  rewrite GET, GET_o. eauto.
Qed.

Lemma memory_remove_disj_loc_stable
      mem1 loc from to msg mem2 loc0
      (ADD: Memory.remove mem1 loc from to msg mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  destruct (Memory.get loc0 ts mem2) eqn:GET; ss.
  lets GET': GET. unfold Memory.get in GET'. rewrite GET'.
  destruct p. destruct t0.
  erewrite Memory.remove_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss. 
  erewrite Memory.remove_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss.
  destruct (Memory.get loc0 ts mem1) eqn:GET_o; eauto.
  erewrite Memory.remove_o in GET; eauto.
  des_ifH GET; ss; des; subst; ss; tryfalse.
  unfold Memory.get in *.
  rewrite GET, GET_o. eauto.
Qed.

Lemma na_step_atomic_loc_stable
  lang lo st lc sc mem st' lc' sc' mem' loc
  (NA_STEPS: @Thread.na_step lang lo
                             (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
  (AT_LOC: lo loc = Ordering.atomic):
  mem loc = mem' loc.
Proof.
  inv NA_STEPS.
  - inv STEP. inv LOCAL; ss; eauto.
  - inv STEP. inv LOCAL; ss; eauto.
    inv LOCAL0.
    assert(DISJ_LOC: loc <> loc0).
    {
      ii; subst.
      rewrite AT_LOC in LO. ss. des; ss.
    } 
    inv WRITE. inv PROMISE; ss.
    + eapply memory_add_disj_loc_stable; eauto.
    + eapply memory_split_disj_loc_stable; eauto.
    + eapply memory_lower_disj_loc_stable; eauto.
  - inv STEP. inv LOCAL; ss.
Qed.
  
Lemma na_steps_atomic_loc_stable:
  forall n lang lo st lc sc mem st' lc' sc' mem' loc
    (NA_STEPS: rtcn (@Thread.na_step lang lo) n
                    (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (AT_LOC: lo loc = Ordering.atomic),
    mem loc = mem' loc.
Proof.
  induction n; ii.
  - inv NA_STEPS. eauto.
  - inv NA_STEPS. destruct a2.
    eapply na_step_atomic_loc_stable in A12; eauto.
    eapply IHn in A23; eauto. rewrite <- A12 in A23; eauto.
Qed.

Lemma na_steps_atomic_loc_stable_rtc
      lang lo st lc sc mem st' lc' sc' mem' loc
      (NA_STEPS: rtc (@Thread.na_step lang lo)
                     (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (AT_LOC: lo loc = Ordering.atomic):
  mem loc = mem' loc.
Proof.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply na_steps_atomic_loc_stable; eauto.
Qed.

Lemma Local_write_disj_loc_stable
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (DISJ_LOC: loc <> loc0):
  mem loc0 = mem' loc0.
Proof.
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  eapply memory_add_disj_loc_stable; eauto.
  des; subst. inv RESERVE.
  eapply memory_split_disj_loc_stable; eauto.
  des; subst.
  eapply memory_lower_disj_loc_stable; eauto.
Qed.

Lemma mem_add_loc_same_prsv
      mem1 mem2 mem1' loc from to msg
      (ADD: Memory.add mem1 loc from to msg mem2)
      (LOC_SAME: mem1 loc = mem1' loc):
  exists mem2',
    Memory.add mem1' loc from to msg mem2' /\
    mem2 loc = mem2' loc.
Proof.
  inv ADD.
  eexists.
  split.
  econs; eauto.
  rewrite <- LOC_SAME; eauto.
  rewrite Loc_add_eq.
  rewrite Loc_add_eq. eauto.
Qed.

Lemma mem_split_loc_same_prsv
      mem1 mem2 mem1' loc from to ts msg msg'
      (SPLIT: Memory.split mem1 loc from to ts msg msg' mem2)
      (LOC_SAME: mem1 loc = mem1' loc):
  exists mem2',
    Memory.split mem1' loc from to ts msg msg' mem2' /\
    mem2 loc = mem2' loc.
Proof.
  inv SPLIT.
  eexists.
  split.
  econs; eauto.
  rewrite <- LOC_SAME; eauto.
  rewrite Loc_add_eq.
  rewrite Loc_add_eq. eauto.
Qed.

Lemma mem_lower_loc_same_prsv
      mem1 mem2 mem1' loc from to msg msg'
      (LOWER: Memory.lower mem1 loc from to msg msg' mem2)
      (LOC_SAME: mem1 loc = mem1' loc):
  exists mem2',
    Memory.lower mem1' loc from to msg msg' mem2' /\
    mem2 loc = mem2' loc.
Proof.
  inv LOWER.
  eexists.
  split.
  econs; eauto.
  rewrite <- LOC_SAME; eauto.
  rewrite Loc_add_eq.
  rewrite Loc_add_eq. eauto.
Qed.

Lemma mem_lower_same_loc_same_prsv
      mem1 mem2 mem1' mem2' loc from to msg msg'
      (LOWER1: Memory.lower mem1 loc from to msg msg' mem2)
      (LOWER2: Memory.lower mem1' loc from to msg msg' mem2')
      (LOC_SAME: mem1 loc = mem1' loc):
  mem2 loc = mem2' loc.
Proof.
  inv LOWER1. inv LOWER2.
  rewrite Loc_add_eq; eauto.
  rewrite Loc_add_eq; eauto.
  rewrite <- LOC_SAME in LOWER0.
  eapply Cell.ext. ii.
  eapply Cell.lower_o with (t := ts) in LOWER.
  eapply Cell.lower_o with (t := ts) in LOWER0.
  des_ifH LOWER; subst.
  rewrite LOWER, LOWER0. eauto.
  rewrite LOWER, LOWER0; eauto.
Qed.

Lemma mem_cancel_loc_same_prsv
      mem1 mem2 mem1' loc from to msg 
      (CANCEL: Memory.remove mem1 loc from to msg mem2)
      (LOC_SAME: mem1 loc = mem1' loc):
  exists mem2',
    Memory.remove mem1' loc from to msg mem2' /\
    mem2 loc = mem2' loc.
Proof.
  inv CANCEL.
  eexists.
  split.
  econs; eauto.
  rewrite <- LOC_SAME; eauto.
  rewrite Loc_add_eq.
  rewrite Loc_add_eq. eauto.
Qed.

Lemma mem_cancel_same_loc_same_prsv
      mem1 mem2 mem1' mem2' loc from to msg
      (CANCEL1: Memory.remove mem1 loc from to msg mem2)
      (CANCEL2: Memory.remove mem1' loc from to msg mem2')
      (LOC_SAME: mem1 loc = mem1' loc):
  mem2 loc = mem2' loc.
Proof.
  inv CANCEL1. inv CANCEL2.
  rewrite Loc_add_eq; eauto.
  rewrite Loc_add_eq; eauto.
  eapply Cell.ext. ii.
  eapply Cell.remove_o with (t := ts) in REMOVE.
  eapply Cell.remove_o with (t := ts) in REMOVE0.
  des_ifH REMOVE.
  rewrite REMOVE, REMOVE0; eauto.
  rewrite REMOVE, REMOVE0; eauto.
  rewrite <- LOC_SAME; eauto.
Qed.
  
Lemma na_step_na_loc_same_prsv
      lang lo st lc sc mem st' lc' sc' mem' mem_c
      (NA_STEP: @Thread.na_step lang lo (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc):
  exists mem_c',
    <<NA_STEP_CAP: @Thread.na_step lang lo (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c')>> /\
    <<NA_SAME_PRSV: forall loc, lo loc = Ordering.nonatomic -> mem' loc = mem_c' loc>>.
Proof.
  inv NA_STEP.
  - (* na read step *)
    inv STEP. inv LOCAL.
    exists mem_c.
    split.
    eapply Thread.na_plain_read_step_intro; eauto.
    econs; eauto. econs; eauto.
    inv LOCAL0.
    unfold Ordering.mem_ord_match in *. destruct (lo loc) eqn:lo_loc; des; ss.
    exploit NA_SAME; eauto. ii.
    assert(GET': Memory.get loc ts mem_c = Some (from, Message.concrete v R)).
    {
      unfold Memory.get in *.
      rewrite <- x; eauto.
    }
    econs; eauto. rewrite lo_loc. ss.
    eauto.
  - (* na write step *)
    inv STEP. inv LOCAL. inv LOCAL0.
    unfold Ordering.mem_ord_match in *. destruct (lo loc) eqn:lo_loc; des; ss.
    assert(MEM_LOC_SAME: mem loc = mem_c loc).
    {
      eauto.
    }
    inv WRITE. inv PROMISE; ss.
    + (* add *)
      exploit mem_add_loc_same_prsv; [eapply MEM | eapply MEM_LOC_SAME | eauto..]; eauto. ii; des.
      exists mem2'.
      split.
      eapply Thread.na_plain_write_step_intro; eauto.
      econs; eauto.
      econs; eauto.
      econs; eauto.
      rewrite lo_loc; ss.
      econs; eauto.
      econs; eauto.
      ii.
      inv MSG. unfold Memory.get in GET.
      exploit ATTACH; eauto.
      rewrite <- MEM_LOC_SAME in GET.
      unfold Memory.get; eauto.
      ii.
      destruct(Loc.eq_dec loc0 loc); subst; eauto.
      eapply memory_add_disj_loc_stable in MEM; eauto.
      eapply memory_add_disj_loc_stable in x0; eauto.
      rewrite <- MEM. rewrite <- x0. eauto.
    + (* split *)
      des; subst. inv RESERVE.
      exploit mem_split_loc_same_prsv; [eapply MEM | eapply MEM_LOC_SAME | eauto..]; eauto. ii; des.
      exists mem2'.
      split.
      eapply Thread.na_plain_write_step_intro; eauto.
      econs; eauto.
      econs; eauto.
      econs; eauto.
      rewrite lo_loc; ss.
      econs; eauto.
      eapply Memory.promise_split; eauto.
      ii.
      destruct(Loc.eq_dec loc0 loc); subst; eauto.
      eapply memory_split_disj_loc_stable in MEM; eauto.
      eapply memory_split_disj_loc_stable in x0; eauto.
      rewrite <- MEM. rewrite <- x0. eauto.
    + (* lower *)
      des; subst.
      exploit mem_lower_loc_same_prsv; [eapply MEM | eapply MEM_LOC_SAME | eauto..]; eauto. ii; des.
      exists mem2'.
      split.
      eapply Thread.na_plain_write_step_intro; eauto.
      econs; eauto.
      econs; eauto.
      econs; eauto.
      rewrite lo_loc; ss.
      ii.
      destruct(Loc.eq_dec loc0 loc); subst; eauto.
      eapply memory_lower_disj_loc_stable in MEM; eauto.
      eapply memory_lower_disj_loc_stable in x0; eauto.
      rewrite <- MEM. rewrite <- x0. eauto.
  - (* na silent step *)
    inv STEP. inv LOCAL.
    exists mem_c.
    split. 
    eapply Thread.na_tau_step_intro; eauto.
    eauto.
Qed.

Lemma na_steps_na_loc_same_prsv':
  forall n lang lo st lc sc mem st' lc' sc' mem' mem_c
    (NA_STEPS: rtcn (@Thread.na_step lang lo) n
                    (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc),
  exists mem_c',
    <<NA_STEP_CAP: rtc (@Thread.na_step lang lo)
                       (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c')>> /\
    <<NA_SAME_PRSV: forall loc, lo loc = Ordering.nonatomic -> mem' loc = mem_c' loc>>.
Proof.
  induction n; ii.
  - inv NA_STEPS. eexists. split. eauto. eauto.
  - inv NA_STEPS.
    destruct a2.
    exploit na_step_na_loc_same_prsv; [eapply A12 | eauto..]. ii; des.
    eapply IHn in A23; eauto. des.
    eexists.
    split.
    eapply Relation_Operators.rt1n_trans; [eapply NA_STEP_CAP | eapply NA_STEP_CAP0 | eauto..].
    eauto.
Qed.

Lemma na_steps_na_loc_same_prsv
      lang lo st lc sc mem st' lc' sc' mem' mem_c
      (NA_STEPS: rtc (@Thread.na_step lang lo)
                      (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc):
  exists mem_c',
    <<NA_STEP_CAP: rtc (@Thread.na_step lang lo)
                       (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c')>> /\
    <<NA_SAME_PRSV: forall loc, lo loc = Ordering.nonatomic -> mem' loc = mem_c' loc>>.
Proof.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply na_steps_na_loc_same_prsv'; eauto.
Qed.

Lemma pf_promise_step_cap
      lang st lc sc mem st' lc' sc' mem' mem_c lo
      (PF_PS: @Thread.pf_promise_step lang (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: forall loc to from msg,
          Memory.get loc to mem = None -> Memory.get loc to mem_c = Some (from, msg) -> msg = Message.reserve)
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc):
  exists mem_c',
    <<PF_PS': @Thread.pf_promise_step lang
                                      (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c')>> /\
    <<MEM_LE': Memory.le mem' mem_c'>> /\
    <<MORE_RESERVE: forall loc to from msg,
        Memory.get loc to mem' = None -> Memory.get loc to mem_c' = Some (from, msg) -> msg = Message.reserve>> /\   
    <<NA_SAME': forall loc, lo loc = Ordering.nonatomic -> mem' loc = mem_c' loc>> /\
    <<FRAME: forall loc to from msg,
            Memory.get loc to mem_c' = Some (from, msg) -> Memory.get loc to mem' = None ->
            (Memory.get loc to mem_c = Some (from, msg) /\ Memory.get loc to mem = None)>>.
Proof.
  inv PF_PS. inv PF_STEP.
  destruct kind; ss.
  - (* lower to none *)
    destruct msg1; ss.
    inv LOCAL. inv PROMISE. des; subst. inv RESERVE.
    exploit lower_succeed_wf; [eapply MEM | eauto..]. ii; des.
    exploit MEM_LE; [eapply GET | eauto..]. ii. inv MSG_LE.
    exploit Memory.lower_exists; [eapply x | eauto..]. ii; des.
    exists mem2.
    split.
    econs; eauto.
    econs; eauto.
    econs.
    eapply Memory.promise_lower; eauto.
    ss. destruct released; ss. econs. econs.
    eauto.
    ss; eauto.
    split.
    {
      unfold Memory.le; ii.
      erewrite Memory.lower_o in LHS; eauto.
      des_ifH LHS; ss; des; subst; ss.
      inv LHS.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss; eauto.
    }
    split.
    {
      ii.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; tryfalse.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; tryfalse; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; tryfalse; eauto.
    }
    split.
    {
      ii.
      destruct (Loc.eq_dec loc loc0); subst.
      eapply mem_lower_same_loc_same_prsv; eauto.
      eapply memory_lower_disj_loc_stable in MEM; eauto.
      eapply memory_lower_disj_loc_stable in x1; eauto.
      rewrite <- x1. rewrite <- MEM. eauto.
    }
    {
      ii.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss. inv H.
      split.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss.
      exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
      rewrite GET1 in H0; ss.
      split; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss.
      split; eauto.
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss.
    }
  - (* cancel *)
    inv LOCAL. inv PROMISE.
    exploit Memory.remove_get0; [eapply MEM | eauto..]. ii; des. 
    exploit MEM_LE; [eapply GET | eauto..]. ii.
    exploit Memory.remove_exists; [eapply x | eauto..]. ii; des.
    exists mem2.
    split.
    econs; eauto.
    econs; eauto.
    split.
    {
      unfold Memory.le; ii.
      erewrite Memory.remove_o in LHS; eauto.
      des_ifH LHS; ss; des; subst; ss; eauto.
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      erewrite Memory.remove_o; eauto.
      des_if; ss; des; subst; ss; eauto.
    }
    split.
    {
      ii.
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; tryfalse.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; tryfalse; eauto.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; tryfalse; eauto.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; tryfalse; eauto.
    }
    split.
    {
      ii.
      destruct (Loc.eq_dec loc loc0); subst.
      eapply mem_cancel_same_loc_same_prsv; eauto.
      eapply memory_remove_disj_loc_stable in MEM; eauto.
      eapply memory_remove_disj_loc_stable in x1; eauto.
      rewrite <- x1. rewrite <- MEM. eauto.
    }
    {
      ii.
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss.
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss; des; subst; ss.
    }
Qed.

Lemma pf_promise_steps_cap':
  forall n lang st lc sc mem st' lc' sc' mem' mem_c lo
    (PF_PS: rtcn (@Thread.pf_promise_step lang) n
                 (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MEM_LE: Memory.le mem mem_c)
    (MORE_RESERVE: forall loc to from msg,
        Memory.get loc to mem = None -> Memory.get loc to mem_c = Some (from, msg) -> msg = Message.reserve)
    (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc),
  exists mem_c',
    <<PF_PS': rtc (@Thread.pf_promise_step lang)
                  (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c')>> /\
    <<MEM_LE': Memory.le mem' mem_c'>> /\
    <<MORE_RESERVE: forall loc to from msg,
        Memory.get loc to mem' = None -> Memory.get loc to mem_c' = Some (from, msg) -> msg = Message.reserve>> /\   
    <<NA_SAME': forall loc, lo loc = Ordering.nonatomic -> mem' loc = mem_c' loc>> /\
    <<FRAME: forall loc to from msg,
            Memory.get loc to mem_c' = Some (from, msg) -> Memory.get loc to mem' = None ->
            (Memory.get loc to mem_c = Some (from, msg) /\ Memory.get loc to mem = None)>>.
Proof.
  induction n; ii.
  - inv PF_PS. eexists. split; eauto.
    split; eauto.
  - inv PF_PS. destruct a2.
    eapply pf_promise_step_cap in A12; eauto. des.
    eapply IHn in A23; eauto.
    des.
    exists mem_c'0.
    split.
    eapply Relation_Operators.rt1n_trans; [eapply PF_PS' | eapply PF_PS'0 | eauto..].
    split; eauto.
    split; eauto. 
    split; eauto.
    ii.
    exploit FRAME0; [eapply H | eapply H0 | eauto..]. ii; des.
    eauto.
Qed.

Lemma pf_promise_steps_cap
      lang st lc sc mem st' lc' sc' mem' mem_c lo
      (PF_PS: rtc (@Thread.pf_promise_step lang)
                   (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
      (MEM_LE: Memory.le mem mem_c)
      (MORE_RESERVE: forall loc to from msg,
          Memory.get loc to mem = None -> Memory.get loc to mem_c = Some (from, msg) -> msg = Message.reserve)
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem loc = mem_c loc):
  exists mem_c',
    <<PF_PS': rtc (@Thread.pf_promise_step lang)
                  (Thread.mk lang st lc sc mem_c) (Thread.mk lang st' lc' sc' mem_c')>> /\
    <<MEM_LE': Memory.le mem' mem_c'>> /\
    <<MORE_RESERVE: forall loc to from msg,
        Memory.get loc to mem' = None -> Memory.get loc to mem_c' = Some (from, msg) -> msg = Message.reserve>> /\   
    <<NA_SAME': forall loc, lo loc = Ordering.nonatomic -> mem' loc = mem_c' loc>> /\
    <<FRAME: forall loc to from msg,
            Memory.get loc to mem_c' = Some (from, msg) -> Memory.get loc to mem' = None ->
            (Memory.get loc to mem_c = Some (from, msg) /\ Memory.get loc to mem = None)>>.
Proof.
  eapply rtc_rtcn in PF_PS. des.
  eapply pf_promise_steps_cap'; eauto.
Qed.

Lemma Local_write_rsv_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo):
  (forall loc0 to0 from0, Memory.get loc0 to0 mem = Some (from0, Message.reserve)
                     <-> Memory.get loc0 to0 mem' = Some (from0, Message.reserve)).
Proof.
  ii. split; ii.
  - inv WRITE. inv WRITE0. inv PROMISE; ss.
    + exploit Memory.add_get0; eauto. ii; des.
      erewrite Memory.add_o; eauto. des_if; ss; des; subst; ss.
      rewrite H in GET. inv GET.
    + des; subst; ss. inv RESERVE.
      exploit Memory.split_get0; eauto. ii; des.
      erewrite Memory.split_o; eauto. des_if; ss; des; subst; ss.
      rewrite H in GET; ss.
      des_if; ss; des; subst; ss.
      des_if; ss; des; subst; ss.
      rewrite H in GET0; ss.
    + des; subst.
      exploit Memory.lower_get0; [eapply MEM | eauto..]. ii; des.
      erewrite Memory.lower_o; eauto.
      des_if; ss; des; subst; ss.
      rewrite H in GET; ss.
  - inv WRITE. inv WRITE0. inv PROMISE; ss.
    + erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
    + des; subst. inv RESERVE.
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
      des_ifH H; ss; des; subst; ss.
      des_ifH H; ss; des; subst; ss.
    + des; subst.
      erewrite Memory.lower_o in H; eauto.
      des_ifH H; ss; des; subst; ss.
Qed.

Lemma Local_write_success
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0 to0 from0 msg0
      (LOCAL_WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (GET: Memory.get loc0 to0 mem' = Some (from0, msg0)):
  (loc0 = loc /\ to0 = to /\ from0 = from) \/
  (exists from0' msg0', Memory.get loc0 to0 mem = Some (from0', msg0') /\
                   (msg0 = Message.reserve -> msg0' = Message.reserve) /\
                   (forall val R, msg0 = Message.concrete val R -> exists R', msg0' = Message.concrete val R')).
Proof.
  inv LOCAL_WRITE. inv WRITE. inv PROMISE; ss.
  - (* add *)
    erewrite Memory.add_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    inv GET. eauto.
    right. do 2 eexists. split; eauto.
    right. do 2 eexists. split; eauto.
  - (* split *)
    des; subst. inv RESERVE.
    erewrite Memory.split_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    inv GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    right. do 2 eexists. split; eauto.
    right. do 2 eexists. split; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    inv GET.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des; eauto.
    right. do 2 eexists. split; eauto.
    right. do 2 eexists. split; eauto.
    right. do 2 eexists. split; eauto.
  - (* lower *)
    des; subst.
    erewrite Memory.lower_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    inv GET; eauto.
    right. do 2 eexists. split; eauto.
    right. do 2 eexists. split; eauto.
Qed.

Lemma Local_write_none
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo loc0 to0
      (LOCAL_WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (GET: Memory.get loc0 to0 mem' = None):
  Memory.get loc0 to0 mem = None.
Proof.
  inv LOCAL_WRITE. inv WRITE. inv PROMISE; ss.
  - (* add *)
    erewrite Memory.add_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
  - (* split *)
    erewrite Memory.split_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
  - (* lower *)
    erewrite Memory.lower_o in GET; eauto.
    des_ifH GET; ss; des; subst; ss; eauto.
Qed. 

Lemma Local_write_succeed
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo
      (LOCAL_WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo):
  Memory.get loc to mem' =
  Some (from, Message.concrete val (TView.write_released (Local.tview lc) sc loc to releasedr ord)).
Proof.
  inv LOCAL_WRITE. inv WRITE. inv PROMISE; ss.
  - (* add *)
    erewrite Memory.add_o; eauto. des_if; ss; des; subst; ss.
  - (* split *)
    des; subst. inv RESERVE.
    exploit split_succeed_wf; eauto. ii; des.
    erewrite Memory.split_o; eauto. des_if; ss; des; subst; ss.
  - (* lower  *)
    des; subst.
    erewrite Memory.lower_o; eauto. des_if; ss; des; subst; ss.
Qed.
    
(** abort step *)
Lemma atm_match_step_prsv
      n lang lo e1 b1 e2 b2 b1'
      (STEPS: rtcn (NPAuxThread.tau_step lang lo) n (NPAuxThread.mk lang e1 b1) (NPAuxThread.mk lang e2 b2))
      (ATM_MATCH: b1 = true -> b1' = true):
  exists b2',
    rtc (NPAuxThread.tau_step lang lo) (NPAuxThread.mk lang e1 b1') (NPAuxThread.mk lang e2 b2') /\
    (b2 = true -> b2' = true).
Proof.
  ginduction n; ii.
  - inv STEPS. eauto.
  - inv STEPS. 
    unfold NPAuxThread.tau_step in A12. destruct a2. des.
    + inv A12.
      assert(NPAuxThread.na_step lang lo (NPAuxThread.mk lang e1 b1) (NPAuxThread.mk lang state false)).
      {
        econs; ss; eauto.
      }
      eapply IHn in A23; eauto. des.
      exists b2'.
      split; eauto.
      eapply Relation_Operators.rt1n_trans.
      econs. eapply H1.
      ss. subst.
      eauto.
    + inv A12. ss; subst. 
      assert(NPAuxThread.at_step lang lo (NPAuxThread.mk lang e1 b1) (NPAuxThread.mk lang state true)).
      {
        econs; eauto.
      }
      eapply IHn in A23; eauto. des.
      exists b2'.
      split; eauto.
      eapply Relation_Operators.rt1n_trans.
      unfold NPAuxThread.tau_step. right. left.
      eauto.
      eauto.
    + inv A12. ss; subst. des; subst.
      assert(NPAuxThread.prc_step lang lo (NPAuxThread.mk lang e1 true) (NPAuxThread.mk lang state true)).
      {
        econs; eauto; ss. 
      }
      exists b2.
      split; eauto.
      eapply Relation_Operators.rt1n_trans.
      unfold NPAuxThread.tau_step. right. right.
      exploit ATM_MATCH; eauto. ii; subst.
      eauto.
      exploit ATM_MATCH; eauto. ii; subst.
      eapply rtcn_rtc in A23; eauto.
      Unshelve.
      eauto.
Qed.

Lemma thread_at_step_implies_at_lang_step
      lang lo e e'
      (AT_STEP: @Thread.at_step lang lo e e'):
  exists pe, Language.step lang pe (Thread.state e) (Thread.state e') /\ state_at_out_step pe.
Proof.
  inv AT_STEP. des; inv AT_STEP0; inv STEP; inv LOCAL; ss.
  - eexists. split; eauto. ss. destruct o; ss.
  - eexists. split; eauto. ss. destruct o; ss.
  - eexists. split; eauto. ss.
  - eexists. split; eauto. ss.
Qed.
  
(** Tau step sim **)
Lemma sim_tau_step
      lang index index_order I lo inj dset b_tgt b_src e_tgt e_src b_tgt' e_tgt'
      (T_STEP: NPAuxThread.tau_step lang lo (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
      (ATM_MATCH: b_tgt = true -> b_src = true)
      (ATM_DSET_EMP: b_tgt = true -> dset = dset_init)
      (WF_I: wf_I I)
      (MONOTONIC_INJ: monotonic_inj inj)
      (LOCAL_WF: Local.promise_consistent (Thread.local e_tgt))
      (LOCAL_WF': Local.promise_consistent (Thread.local e_tgt')):
  (exists b_src' e_src' dset' inj',
      <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                     (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
      <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset' b_tgt' e_tgt' e_src'>> /\
      <<ATM_MATCH_PSV: b_tgt' = true -> b_src' = true>> /\
      <<INJ_INCR: incr_inj inj inj'>> /\
      <<ATM_DSET_EMP_PRSV: b_tgt' = true -> dset' = dset_init>> /\           
      <<MONOTONIC_INJ: monotonic_inj inj'>>
  ) \/
  (exists b_src' e_src',
      <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                     (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
      <<ABORT: Thread.is_abort e_src' lo>>).
Proof.
  inv LOCAL_SIM; ss. 
  - (* abort *)
    right.
    eapply rtc_rtcn in NP_STEPS. des.
    eapply atm_match_step_prsv in NP_STEPS; eauto. des.
    do 2 eexists.
    split; eauto.
  - (* sim *)
    unfold NPAuxThread.tau_step in T_STEP.
    destruct T_STEP as [T_NA_STEP | [T_AT_STEP | T_PRC_STEP]].
    + clear RELY_STEP THRD_DONE THRD_ABORT.
      inv T_NA_STEP; ss.
      exploit na_step_to_thread_step; eauto.
      ii; des.
      exploit THRD_STEP; eauto. ii; des. 
      clear x x3 x4 THRD_STEP. 
      exploit x2; eauto. clear x2. ii; des; subst.
      left; subst.
      exploit na_steps_dset_to_NPThread_tau_steps; [eapply x2 | eauto..].
      instantiate (1 := b_src).
      ii; des.
      do 4 eexists.
      split; eauto.
      split; eauto.
      split. ii; ss.
      split. unfold incr_inj. ii; eauto.
      ii; ss.
    + clear RELY_STEP THRD_DONE THRD_ABORT.
      inv T_AT_STEP; ss; subst; ss.
      exploit at_step_to_thread_step; eauto.
      ii; des.
      exploit THRD_STEP; eauto. ii; des.
      clear x3 x4 x5 THRD_STEP.
      exploit x; eauto. clear x. ii; des. 
      assert(MONOTONIC_INJ'_OR_ABORT: 
              monotonic_inj inj' \/
                (exists e_src'' b_src'',
                    rtc (NPAuxThread.tau_step lang lo)
                        (NPAuxThread.mk lang e_src' true)
                        (NPAuxThread.mk lang e_src'' b_src'') /\
                      Thread.is_abort e_src'' lo)).
      { 
        clear - WF_I x6 x4 LOCAL_WF'. inv x6; ss.
        right.
        eapply rtc_rtcn in x4. des.
        eapply rtc_na_p_to_np in x4; eauto.
        clear - RELY_STEP WF_I.
        exploit RELY_STEP; eauto. clear RELY_STEP; introv RELY_STEP. des.
        unfold wf_I in WF_I.
        eapply WF_I in RELY_STEP; ss. inv RELY_STEP; eauto.
      }
      destruct MONOTONIC_INJ'_OR_ABORT as [MONOTONIC_INJ' | ABORT].
      left; subst.
      eapply rtc_rtcn in x4. des.
      eapply rtc_na_p_to_np with (b := b_src) in x4; eauto. des.
      exploit program_step_to_NPThread_tau_step; [eapply x3 | eauto..].
      clear - x2 PROG_EVENT_EQ. ii. des. contradiction x2; eauto.
      destruct te, te'; ss; eauto.
      ii; des.
      eapply np_na_steps_is_tau_steps in x4.
      do 4 eexists. 
      split.
      {
        eapply rtc_n1; [eapply x4 | eapply x7].
      }
      split; eauto.
      split.
      {
        clear - x1 PROG_EVENT_EQ x9. destruct te, te'; ss; des; subst; ss; eauto.
      }
      split; eauto.
      right.
      eapply rtc_rtcn in x4. des.
      eapply rtc_na_p_to_np in x4. des.
      eapply np_na_steps_is_tau_steps in x4.
      exploit program_step_to_NPThread_tau_step; [eapply x3 | eauto..].
      ii; des. clear - H0 PROG_EVENT_EQ x2. subst; ss. destruct te; ss.
      contradiction x2; eauto. ii; des.
      do 2 eexists. split. 2: eapply ABORT0.
      eapply rtc_compose; [ | eapply ABORT].
      exploit x9; eauto.
      clear - x1 PROG_EVENT_EQ. destruct te, te'; ss; des; subst; ss; eauto.
      ii; subst.
      eapply rtc_n1; [eapply x4 | eapply x7].      
    + clear RELY_STEP THRD_DONE THRD_ABORT.
      inv T_PRC_STEP; ss. des; subst.
      exploit prc_step_to_thread_step; eauto. ii; des.
      exploit THRD_STEP; eauto. ii; des.
      clear x x2 THRD_STEP.
      destruct pf.
      {
        clear x3.
        exploit ATM_MATCH; eauto. ii; subst.
        exploit x4; eauto. clear x4. ii; des.
        left.
        eapply pf_promise_steps_to_np in x.
        eapply np_prc_steps_is_tau_steps in x.
        do 4 eexists.
        split. eauto.
        split; eauto.
        split; eauto.
        split; eauto.
        unfold incr_inj. ii; eauto.
      }
      { 
        clear x4.
        exploit x3; eauto. clear x3. ii; des.
        eapply rtc_rtcn in x. des.
        eapply rtc_prc_p_to_np in x; ss.
        eapply np_prc_steps_is_tau_steps in x. 
        exploit ATM_MATCH; eauto. ii. subst b_src.
        assert(MONOTONIC_INJ'_OR_ABORT: 
                monotonic_inj inj' \/
                  (exists e_src'' b_src'',
                      rtc (NPAuxThread.tau_step lang lo)
                          (NPAuxThread.mk lang e_src' true)
                          (NPAuxThread.mk lang e_src'' b_src'') /\
                        Thread.is_abort e_src'' lo)).
        { 
          clear - WF_I x3 x LOCAL_WF'. inv x3; ss.
          right.
          do 2 eexists; eauto.
          left.
          clear - RELY_STEP WF_I.
          exploit RELY_STEP; eauto. clear RELY_STEP; introv RELY_STEP. des.
          unfold wf_I in WF_I.
          eapply WF_I in RELY_STEP; ss. inv RELY_STEP; eauto.
        } 
        destruct MONOTONIC_INJ'_OR_ABORT as [MONOTONIC_INJ' | ABORT].
        left.
        do 4 eexists.
        split. eapply x.
        split; eauto.
        right.
        des. exists b_src'' e_src''.
        split; eauto.
        eapply rtc_compose; [eapply x | eapply ABORT].
      }
      Unshelve.
      exact true.
Qed. 
  
Lemma sim_tau_steps:
  forall n lang index index_order I lo inj dset b_tgt b_src e_tgt e_src b_tgt' e_tgt'
    (T_STEPS: rtcn (@NPAuxThread.tau_step lang lo) n
                   (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
    (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
    (ATM_MATCH: b_tgt = true -> b_src = true)
    (ATM_DSET_EMP: b_tgt = true -> dset = dset_init)
    (WF_I: wf_I I)
    (MONOTONIC_INJ: monotonic_inj inj)
    (LOCAL_WF: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
    (MEM_CLOSED: Memory.closed (Thread.memory e_tgt))
    (SC_CLOSED: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
    (PROM_CONS: Local.promise_consistent (Thread.local e_tgt')),
    (exists b_src' e_src' dset' inj',
        <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                       (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
        <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset' b_tgt' e_tgt' e_src'>> /\
        <<ATM_MATCH_PSV: b_tgt' = true -> b_src' = true>> /\ 
        <<INJ_INCR: incr_inj inj inj'>> /\ 
        <<ATM_DSET_EMP_PSV: b_tgt' = true -> dset' = dset_init>> /\
        <<MONOTONIC_INJ': monotonic_inj inj'>>
    ) \/
    (exists b_src' e_src',
        <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                       (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
        <<ABORT: Thread.is_abort e_src' lo>>).
Proof.
  induction n; ii; ss.
  - inv T_STEPS.
    left.
    do 4 eexists.
    split; eauto.
    split; eauto.
    split; eauto.
    unfold incr_inj. ii; eauto.
  - inv T_STEPS; ss. destruct a2. 
    exploit Thread.rtc_all_step_future. 
    {
      eapply NPThread_tau_step_to_thread_all_step in A12.
      solve_one_step. eauto.
    }
    eauto. eauto. eauto.
    ii; des.
    
    assert (PROM_CONS'': Local.promise_consistent (Thread.local state)).
    {
      eapply rtcn_rtc in A23.
      eapply NPThread_tau_steps_to_thread_all_steps in A23.
      eapply rtc_all_step_promise_consistent; eauto.
    }
    assert (PROM_CONS': Local.promise_consistent (Thread.local e_tgt)).
    {
      eapply rtcn_rtc in A23.
      eapply NPThread_tau_step_to_thread_all_step in A12.
      eapply rtc_all_step_promise_consistent.
      solve_one_step. eauto. eauto. eauto. eauto. eauto.
    }
    renames state to e_tgt0, preempt to b_tgt0.
    exploit sim_tau_step; eauto. ii; des.
    + eapply NPThread_tau_step_to_thread_all_step in A12.
      exploit Thread.rtc_all_step_future.
      eapply Operators_Properties.clos_rt1n_step. eauto. eauto. eauto. eauto.
      ii; des; eauto.
      eapply IHn in LOCAL_SIM_PSV; eauto.
      des.
      {
        left.
        do 4 eexists. split.
        eapply rtc_compose; [eapply S_STEPS | eapply S_STEPS0].
        split; eauto.
        split; eauto.
        split.
        eapply incr_inj_transitivity; eauto.
        eauto.
      }
      {
        right.
        do 2 eexists. split.
        eapply rtc_compose; [eapply S_STEPS | eapply S_STEPS0].
        eauto.
      }      
    + right.
      do 2 eexists.
      split; [eapply S_STEPS | eapply ABORT].
Qed.

Lemma sim_tau_steps_aux
      lang index index_order I lo inj dset b_tgt b_src e_tgt e_src b_tgt' e_tgt'
      (T_STEPS: rtc (@NPAuxThread.tau_step lang lo) 
                     (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
      (ATM_MATCH: b_tgt = true -> b_src = true)
      (ATM_DSET_EMP: b_tgt = true -> dset = dset_init)
      (WF_I: wf_I I)
      (MONOTONIC_INJ: monotonic_inj inj)
      (LOCAL_WF: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
      (MEM_CLOSED: Memory.closed (Thread.memory e_tgt))
      (SC_CLOSED: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
      (PROM_CONS: Local.promise_consistent (Thread.local e_tgt'))
      (SAFE: ~ (exists e_src' b_src',
                   rtc (NPAuxThread.tau_step lang lo)
                       (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src') /\
                   Thread.is_abort e_src' lo)):
  exists b_src' e_src' dset' inj',
      <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                     (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
      <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset' b_tgt' e_tgt' e_src'>> /\
      <<ATM_MATCH_PSV: b_tgt' = true -> b_src' = true>> /\ 
      <<INJ_INCR: incr_inj inj inj'>> /\ 
      <<ATM_DSET_EMP_PSV: b_tgt' = true -> dset' = dset_init>> /\
      <<MONOTONIC_INJ': monotonic_inj inj'>>.
Proof.
  eapply rtc_rtcn in T_STEPS. des.
  exploit sim_tau_steps; eauto. ii; des.
  - exists b_src' e_src' dset' inj'.
    split; eauto.
  - contradiction SAFE.
    exists e_src' b_src'.
    split; eauto.
Qed.

Lemma sim_output_steps
      lang index index_order I lo inj dset b_tgt e_tgt b_tgt' e_tgt' e_src b_src e
      (T_OUT: NPAuxThread.out_step lang lo e
                                   (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
      (ATM_MATCH: b_tgt = true -> b_src = true):
  (exists e_src0 b_src0 e_src' inj',
      <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                   (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src0 b_src0)>> /\
      <<S_OUT: NPAuxThread.out_step lang lo e
                                    (NPAuxThread.mk lang e_src0 b_src0) (NPAuxThread.mk lang e_src' true)>> /\
      <<OUT_ATM: b_tgt' = true>> /\ 
      <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset_init b_tgt' e_tgt' e_src'>> /\ 
      <<INJ_INCR: incr_inj inj inj'>>
  ) \/
  (exists b_src' e_src',
        <<S_STEPS: rtc (NPAuxThread.tau_step lang lo)
                       (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
        <<ABORT: Thread.is_abort e_src' lo>>).
Proof.
  inv LOCAL_SIM.
  - right.
    eapply rtc_rtcn in NP_STEPS. des.
    eapply atm_match_step_prsv in NP_STEPS; eauto; des.
    do 2 eexists.
    split; eauto.
  - contradiction NOT_PRM_CONS_T.
    inv T_OUT; ss. inv H; ss. inv OUT; ss. inv LOCAL; ss. inv LOCAL0; ss.
    exploit PROMISES; eauto. ii.
    rewrite x in PROMISE. rewrite Memory.bot_get in PROMISE. ss.
  - clear RELY_STEP THRD_DONE THRD_ABORT.
    inv T_OUT; ss. inv H; ss.
    exploit THRD_STEP; eauto.
    ii; des. clear x0 x1 x2.
    exploit x; eauto. ss; eauto. clear x; ii. des. clear THRD_STEP.
    eapply rtc_rtcn in x1. des.
    eapply rtc_na_p_to_np in x1; eauto. des.
    eapply np_na_steps_is_tau_steps in x1.
    left.
    do 4 eexists.
    split. eauto.
    split.
    ss. destruct te'; ss. inv PROG_EVENT_EQ.
    econs; ss. econs. eauto.
    split; eauto.
Qed.

Lemma sim_all_step
  lang index index_order I lo inj dset b_tgt b_src e_tgt e_src b_tgt' e_tgt'
  (T_STEP: @NPAuxThread.all_step lang lo
                                  (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
  (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
  (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) e_src e_src' /\ Thread.is_abort e_src' lo))
  (ATM_MATCH: b_tgt = true -> b_src = true)
  (ATM_DSET_EMP: b_tgt = true -> dset = dset_init)
  (WF_I: wf_I I)
  (MONOTONIC_INJ: monotonic_inj inj)
  (LOCAL_WF: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
  (MEM_CLOSED: Memory.closed (Thread.memory e_tgt))
  (SC_CLOSED: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
  (PROM_CONS: Local.promise_consistent (Thread.local e_tgt')):
  exists b_src' e_src' dset' inj',
    <<S_STEPS: rtc (NPAuxThread.all_step lang lo)
                   (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
    <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset' b_tgt' e_tgt' e_src'>> /\
    <<ATM_MATCH_PSV: b_tgt' = true -> b_src' = true>> /\ 
    <<INJ_INCR: incr_inj inj inj'>> /\ 
    <<ATM_DSET_EMP_PSV: b_tgt' = true -> dset' = dset_init>> /\
    <<MONOTONIC_INJ': monotonic_inj inj'>>.
Proof.
  unfold NPAuxThread.all_step in T_STEP.
  destruct T_STEP as [TAU_STEP | OUT_STEP].
  - eapply sim_tau_step in TAU_STEP; eauto.
    des.
    {
      do 4 eexists.
      split.
      eapply NPThread_tau_steps_is_NPThread_all_steps; eauto.
      split; eauto.
    }
    {
      contradiction SAFE.
      exists e_src'.
      eapply NPThread_tau_steps_to_thread_all_steps in S_STEPS.
      eauto.
    }
    eapply NPThread_tau_step_to_thread_all_step in TAU_STEP.
    eapply rtc_all_step_promise_consistent.
    eapply Operators_Properties.clos_rt1n_step. eauto. eauto. eauto. eauto. eauto.
  - des.
    eapply sim_output_steps in OUT_STEP; eauto. des.
    {
      do 4 eexists.
      split.
      eapply rtc_n1.
      eapply NPThread_tau_steps_is_NPThread_all_steps; eauto.
      inv S_OUT.
      unfold NPAuxThread.all_step. right.
      eexists.
      econs; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split. ii; eauto.

      inv LOCAL_SIM_PSV.
      contradiction SAFE.
      eapply NPThread_tau_steps_to_thread_all_steps in NP_STEPS.
      eapply NPThread_tau_steps_to_thread_all_steps in S_STEPS.
      eapply NPAuxThread_out_step_is_Thread_program_step in S_OUT; ss.
      eexists.
      split.
      eapply rtc_compose.
      eapply rtc_n1. eapply S_STEPS. eapply S_OUT.
      eapply NP_STEPS.
      eauto. 
      inv S_OUT; ss.
      clear THRD_STEP THRD_DONE THRD_ABORT.
      exploit RELY_STEP; eauto. intros; des.
      clear RELY_STEP x0.
      unfold wf_I in WF_I.
      eapply WF_I in x. ss. inv x. eauto.
    }
    {
      contradiction SAFE.
      eapply NPThread_tau_steps_to_thread_all_steps in S_STEPS. eauto.
    }
Qed.
    
Lemma sim_all_steps':
  forall n lang index index_order I lo inj dset b_tgt b_src e_tgt e_src b_tgt' e_tgt'
    (T_STEPS: rtcn (@NPAuxThread.all_step lang lo) n
                   (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
    (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
    (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) e_src e_src' /\ Thread.is_abort e_src' lo))
    (ATM_MATCH: b_tgt = true -> b_src = true)
    (ATM_DSET_EMP: b_tgt = true -> dset = dset_init)
    (WF_I: wf_I I)
    (MONOTONIC_INJ: monotonic_inj inj)
    (LOCAL_WF: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
    (MEM_CLOSED: Memory.closed (Thread.memory e_tgt))
    (SC_CLOSED: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
    (PROM_CONS: Local.promise_consistent (Thread.local e_tgt')),
    exists b_src' e_src' dset' inj',
      <<S_STEPS: rtc (NPAuxThread.all_step lang lo)
                     (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
      <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset' b_tgt' e_tgt' e_src'>> /\
      <<ATM_MATCH_PSV: b_tgt' = true -> b_src' = true>> /\ 
      <<INJ_INCR: incr_inj inj inj'>> /\ 
      <<ATM_DSET_EMP_PSV: b_tgt' = true -> dset' = dset_init>> /\
      <<MONOTONIC_INJ': monotonic_inj inj'>>.
Proof.
  induction n; ii.
  - inv T_STEPS.
    do 4 eexists.
    split. eauto. split. eauto. split. eauto.
    split. unfold incr_inj. ii; eauto.
    split; eauto.
  - inv T_STEPS.
    destruct a2.
    exploit Thread.rtc_all_step_future.
    eapply Operators_Properties.clos_rt1n_step.
    eapply NPThread_all_step_to_Thread_all_step; eauto.
    eauto. eauto. eauto.
    ii; des.
    eapply sim_all_step in A12; eauto.
    des. 
    eapply IHn in LOCAL_SIM_PSV; eauto; ss.
    des.
    do 4 eexists.
    split.
    eapply rtc_compose; [eapply S_STEPS | eapply S_STEPS0].
    split. eauto.
    split; eauto.
    split.
    clear - INJ_INCR INJ_INCR0.
    unfold incr_inj in *; ii.
    eapply INJ_INCR in H. eauto.
    ii; eauto.
    ii. des.
    contradiction SAFE.
    eexists.
    split.
    eapply NPThread_all_steps_to_Thread_all_steps in S_STEPS.
    eapply rtc_compose. eapply S_STEPS. eapply H.
    eauto.
    eapply rtcn_rtc in A23.
    eapply NPThread_all_steps_to_Thread_all_steps in A23; eauto.
    eapply rtc_all_step_promise_consistent; eauto.
Qed.

Lemma sim_all_steps
      lang index index_order I lo inj dset b_tgt b_src e_tgt e_src b_tgt' e_tgt'
      (T_STEPS: rtc (@NPAuxThread.all_step lang lo)
                    (NPAuxThread.mk lang e_tgt b_tgt) (NPAuxThread.mk lang e_tgt' b_tgt'))
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b_tgt e_tgt e_src)
      (SAFE: ~ (exists e_src', rtc (Thread.all_step lo) e_src e_src' /\ Thread.is_abort e_src' lo))
      (ATM_MATCH: b_tgt = true -> b_src = true)
      (ATM_DSET_EMP: b_tgt = true -> dset = dset_init)
      (WF_I: wf_I I)
      (MONOTONIC_INJ: monotonic_inj inj)
      (LOCAL_WF: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
      (MEM_CLOSED: Memory.closed (Thread.memory e_tgt))
      (SC_CLOSED: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
      (PROM_CONS: Local.promise_consistent (Thread.local e_tgt')):
  exists b_src' e_src' dset' inj',
    <<S_STEPS: rtc (NPAuxThread.all_step lang lo)
                   (NPAuxThread.mk lang e_src b_src) (NPAuxThread.mk lang e_src' b_src')>> /\
    <<LOCAL_SIM_PSV: @local_sim_state index index_order lang I lo inj' dset' b_tgt' e_tgt' e_src'>> /\
    <<ATM_MATCH_PSV: b_tgt' = true -> b_src' = true>> /\ 
    <<INJ_INCR: incr_inj inj inj'>> /\ 
    <<ATM_DSET_EMP_PSV: b_tgt' = true -> dset' = dset_init>> /\
    <<MONOTONIC_INJ': monotonic_inj inj'>>.
Proof.
  eapply rtc_rtcn in T_STEPS. des.
  eapply sim_all_steps'; eauto.
Qed. 

Lemma out_atmblk_I_inj_hold
      lang index index_order I lo inj dset
      st_tgt lc_tgt sc_tgt mem_tgt
      st_src lc_src sc_src mem_src
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset true
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (WF_I: wf_I I)
      (T_PROM_CONS: Local.promise_consistent lc_tgt):
  (monotonic_inj inj /\ I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src) /\
   Mem_at_eq lo mem_tgt mem_src) \/
  (exists e_src' b_src',
      rtc (NPAuxThread.tau_step lang lo)
          (NPAuxThread.mk lang (Thread.mk lang st_src lc_src sc_src mem_src) true)
          (NPAuxThread.mk lang e_src' b_src') /\
      Thread.is_abort e_src' lo).
Proof.
  inv LOCAL_SIM; eauto; ss.
  clear THRD_STEP THRD_DONE THRD_ABORT.
  exploit RELY_STEP; eauto. clear RELY_STEP.
  ii; des.
  unfold wf_I in WF_I.
  exploit WF_I; eauto. ii; ss.
  left.
  inv x1.
  inv STEP_INV.
  split; eauto.
Qed.
  
Lemma Local_write_cap_conditional_prsv
      lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo sc_c mem_c
      (WRITE: Local.write_step lc sc mem loc from to val releasedr released ord lc' sc' mem' kind lo)
      (PRM_LE: Memory.le (Local.promises lc) mem)
      (MEM_LE: Memory.le mem mem_c)
      (ADD_RSV: kind = Memory.op_kind_add ->
                (forall t : Time.t, Cover.covered loc t mem_c -> ~ Interval.mem (from, to) t))
      (ADD_NO_ATTACH: kind = Memory.op_kind_add -> ~ attatched_time mem_c loc to):
  exists mem_c',
    Local.write_step lc sc_c mem_c loc from to val releasedr released ord lc' sc_c mem_c' kind lo /\
    Memory.le mem' mem_c'.
Proof.
  assert(PRM_LE': Memory.le (Local.promises lc) mem_c).
  {
    clear - PRM_LE MEM_LE.
    unfold Memory.le in *; ii; eauto.
  }
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  - (* add *)
    exploit add_succeed_wf; [eapply MEM | eauto..]. ii; des.
    inv TS.
    exploit write_succeed_valid; [eapply PRM_LE' | | eapply TS0 | eapply TO1 | | eapply MSG_WF | eauto..].
    eapply ADD_RSV; eauto.
    eapply ADD_NO_ATTACH; eauto.
    ii; des.
    exists mem2. split.
    econs; eauto.
    inv WRITABLE. econs; eauto.
    exploit MemoryMerge.MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
    ii; subst. eauto.
    unfold Memory.le; ii. inv WRITE. inv PROMISE.
    erewrite Memory.add_o in LHS; eauto. des_ifH LHS; ss; des; subst; ss.
    inv LHS.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  - (* split *)
    des; subst. inv RESERVE.
    exploit Memory.split_exists_le; [eapply PRM_LE' | eapply PROMISES | eauto..].
    ii; des.
    exists mem2. split.
    econs; eauto.
    inv WRITABLE. econs; eauto.
    econs; eauto.
    econs; eauto.
    unfold Memory.le; ii. 
    erewrite Memory.split_o in LHS; eauto. des_ifH LHS; ss; des; subst; ss.
    inv LHS.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_ifH LHS; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_ifH LHS; ss; des; subst; ss; eauto. inv LHS.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
  - (* lower *)
    des; subst.
    exploit Memory.lower_exists_le; [eapply PRM_LE' | eapply PROMISES | eauto..].
    ii; des.
    exists mem2. split.
    econs; eauto.
    inv WRITABLE. econs; eauto.
    unfold Memory.le; ii.
    erewrite Memory.lower_o in LHS; eauto.
    des_ifH LHS; ss; des; subst; ss; eauto.
    inv LHS.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
Qed.

Lemma tgt_no_scfence_program_step_cap_sim
      lang e index index_order I lo inj dset b
      st_tgt lc_tgt sc_tgtc mem_tgtc sc_tgt mem_tgt st_tgt' lc_tgt' sc_tgtc' mem_tgtc'
      st_src lc_src sc_srcc mem_srcc sc_src mem_src
      (STEP: Thread.program_step e lo
                                 (Thread.mk lang st_tgt lc_tgt sc_tgtc mem_tgtc)
                                 (Thread.mk lang st_tgt' lc_tgt' sc_tgtc' mem_tgtc'))
      (TAU: ThreadEvent.get_machine_event e = MachineEvent.silent)
      (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
      (MEM_CLOSED: Memory.closed mem_tgt)
      (NOT_SC_FENCE: ~ (exists ordr, e = ThreadEvent.fence ordr Ordering.seqcst))
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (MEM_LE: Memory.le mem_tgt mem_tgtc)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem_tgt = None ->
                            Memory.get loc to mem_tgtc = Some (from, msg) ->
                            msg = Message.reserve)
      (SAFE_S: ~ (exists e_src', rtc (@Thread.tau_step lang lo)
                                 (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                             Thread.is_abort e_src' lo))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem_src loc = mem_srcc loc)
      (AT_COVER: forall loc, lo loc = Ordering.atomic ->
                        (forall from to, Memory.get loc to mem_srcc = Some (from, Message.reserve) ->
                                    Memory.get loc to mem_tgtc = Some (from, Message.reserve)))
      (MEM_LE_SRC: Memory.le mem_src mem_srcc)
      (MORE_RESERVE_SRC: 
         forall loc to from msg, Memory.get loc to mem_src = None ->
                            Memory.get loc to mem_srcc = Some (from, msg) ->
                            msg = Message.reserve)
      (LOCAL_WF_S: Local.wf lc_src mem_src)
      (MEMORY_CLOSED: Memory.closed mem_src)
      (WF_I: wf_I I)
      (MONOTONIC_INJ: monotonic_inj inj)
      (TGT_PROM_CONS: Local.promise_consistent lc_tgt)
      (TGT_PROM_CONS': Local.promise_consistent lc_tgt')
  :
    exists st_src' lc_src' mem_srcc' mem_src' inj' dset' b' mem_tgt',
      <<S_STEPS: rtc (Thread.nprm_step lo)
                     (Thread.mk lang st_src lc_src sc_srcc mem_srcc)
                     (Thread.mk lang st_src' lc_src' sc_srcc mem_srcc')>> /\
      <<S_STEPS': rtc (Thread.nprm_step lo)
                      (Thread.mk lang st_src lc_src sc_src mem_src)
                      (Thread.mk lang st_src' lc_src' sc_src mem_src')>> /\
      <<LOCAL_SIM': @local_sim_state index index_order lang I lo inj' dset' b'               
                                     (Thread.mk lang st_tgt' lc_tgt' sc_tgt mem_tgt')
                                     (Thread.mk lang st_src' lc_src' sc_src mem_src')>> /\
      <<NA_SAME': forall loc, lo loc = Ordering.nonatomic -> mem_src' loc = mem_srcc' loc>> /\ 
      <<AT_COVER': forall loc, lo loc = Ordering.atomic ->
                          (forall from to, Memory.get loc to mem_srcc' = Some (from, Message.reserve) ->
                                      Memory.get loc to mem_tgtc' = Some (from, Message.reserve))>> /\ 
      <<LOCAL_WF_S': Local.wf lc_src' mem_src'>> /\
      <<MEMORY_CLOSED: Memory.closed mem_src'>> /\
      <<MEM_LE_T': Memory.le mem_tgt' mem_tgtc'>> /\
      <<MORE_RESERVE_TGT':
          forall loc to from msg, Memory.get loc to mem_tgt' = None ->
                             Memory.get loc to mem_tgtc' = Some (from, msg) ->
                             msg = Message.reserve>> /\
      <<MEM_LE_S': Memory.le mem_src' mem_srcc'>> /\
      <<MORE_RESERVE_S':
          forall loc to from msg, Memory.get loc to mem_src' = None ->
                             Memory.get loc to mem_srcc' = Some (from, msg) ->
                             msg = Message.reserve>> /\
      <<LOCAL_WF_T': Local.wf lc_tgt' mem_tgt'>> /\
      <<MEM_CLOSEd_T': Memory.closed mem_tgt'>> /\ 
      <<MONOTONIC_INJ': monotonic_inj inj'>>.
Proof.
  inv LOCAL_SIM; ss.
  (* abort *)
  contradiction SAFE_S.
  eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss. eauto.
  (* not abort *)
  inv STEP. inv LOCAL; ss.
  - (* silent step *)
    clear THRD_ABORT THRD_DONE RELY_STEP.
    assert(TGT_TAU: Thread.step lo true ThreadEvent.silent
                                (Thread.mk lang st_tgt lc_tgt' sc_tgt mem_tgt)
                                (Thread.mk lang st_tgt' lc_tgt' sc_tgt mem_tgt)).
    {
      eapply Thread.step_program; eauto.
    }
    exploit THRD_STEP; [eapply TGT_TAU | eauto..]; eauto; clear THRD_STEP.
    ii. des. clear x x1 x2. ss.
    exploit x0; eauto. clear x0; ii. des.
    exploit na_steps_dset_to_Thread_na_steps; [eapply x0 | eauto..]. introv NA_STEPS.
    destruct e_src'.
    exploit na_steps_na_loc_same_prsv; [eapply NA_STEPS | eauto..]. ii; des.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEPS | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S_CAP.
    assert (SC_SAME: sc_src = sc).
    {
      exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
    }
    subst.
    do 8 eexists.
    split. eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
    eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
    split. eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
    eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
    split.
    eauto.
    split; eauto.
    split; eauto.
    introv ATM_LOC RSV_MEM_SRC_CAP.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..].
    introv AT_MEM_LOC_EQ.
    unfold Memory.get in RSV_MEM_SRC_CAP. rewrite <- AT_MEM_LOC_EQ in RSV_MEM_SRC_CAP.
    eauto.
    eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
    split.
    eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; eauto.
    split.
    eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    unfold Memory.le; ii.
    destruct (lo loc) eqn:AT_NA_LOC.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS | eauto..]. ii.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
    unfold Memory.get in *. rewrite <- x5. rewrite <- x4 in LHS. eauto.
    unfold Memory.get in *. rewrite <- NA_SAME_PRSV; eauto.
    split; eauto.
    ii. destruct msg; eauto.
    destruct (lo loc) eqn:AT_NA_LOC.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS | eauto..]. ii.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
    unfold Memory.get in *.
    rewrite <- x4 in H. rewrite <- x5 in H0. eauto.
    unfold Memory.get in *.
    erewrite <- NA_SAME_PRSV in H0; eauto. tryfalse.
  - (* read step *)
    clear THRD_ABORT THRD_DONE RELY_STEP.
    exploit Local_read_step_cap_prsv; [eapply LOCAL0 | eapply MEM_LE | eauto..].
    introv TGT_LOCAL_READ.
    assert(TGT_READ: Thread.step lo true (ThreadEvent.read loc ts val released ord)
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                 (Thread.mk lang st_tgt' lc_tgt' sc_tgt mem_tgt)).
    {
      eapply Thread.step_program; eauto. 
    }
    destruct (lo loc) eqn: AT_NA_LOC.
    {
      (* read atomic location *)
      exploit THRD_STEP; [eapply TGT_READ | eauto..].
      clear THRD_STEP. ii; des. clear x0 x1 x2.
      exploit x. clear - AT_NA_LOC LOCAL0. inv LOCAL0; ss.
      rewrite AT_NA_LOC in LO. ss.
      des; subst; ss.
      clear x. introv SRC_STEPS.
      destruct SRC_STEPS as (e_src & e_src' & inj' & te' & NA_STEPS_S & AT_READ_STEP & INCR_INJ & LOCAL_SIM').
      destruct e_src.
      exploit na_steps_na_loc_same_prsv; [eapply NA_STEPS_S | eauto..]. ii; des.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEPS_S | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S_CAP.
      assert (SC_SAME: sc_src = sc).
      {
        exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
      }
      subst.
      assert(AT_LOC_STABLE1: forall loc, lo loc = Ordering.atomic -> mem_src loc = memory loc).
      {
        ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
      }
      assert(AT_LOC_STABLE2: forall loc, lo loc = Ordering.atomic -> mem_srcc loc = mem_c' loc).
      {
        ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
      }
      inv AT_READ_STEP. inv LOCAL; ss. des; subst; ss. 
      assert(SRC_AT_READ: Local.read_step local mem_c' loc ts val released0 ord lc2 lo).
      { 
        inv LOCAL1. econs; eauto.
        unfold Memory.get in GET. rewrite <- AT_LOC_STABLE1 in GET; eauto.
        unfold Memory.get. erewrite <- AT_LOC_STABLE2; eauto.
      }
      do 8 eexists.
      split. eapply rtc_n1.
      eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      econs. econs.
      Focus 2. eapply Local.step_read; eauto. ss. eauto. ss; eauto.
      split. eapply rtc_n1.
      eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      econs. econs.
      Focus 2. eapply Local.step_read; eauto. ss. eauto.
      split.
      eauto.
      split; eauto.
      split.
      introv ATM_LOC GET_MEM_C'.
      unfold Memory.get in GET_MEM_C'. erewrite <- AT_LOC_STABLE2 in GET_MEM_C'; eauto.
      eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
      split.
      eapply local_wf_read; eauto. 
      eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
      eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; eauto.
      split.
      eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unfold Memory.le; ii.
      destruct (lo loc0) eqn:AT_NA_LOC0.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS_S | eauto..]. ii.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
      unfold Memory.get in *. rewrite <- x1. rewrite <- x0 in LHS. eauto.
      unfold Memory.get in *. rewrite <- NA_SAME_PRSV; eauto.
      split; eauto. ii. destruct msg; eauto. 
      destruct (lo loc0) eqn:AT_NA_LOC0.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS_S | eauto..]. ii.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
      unfold Memory.get in *.
      rewrite <- x0 in H. rewrite <- x1 in H0. eauto.
      unfold Memory.get in *.
      erewrite <- NA_SAME_PRSV in H0; eauto. tryfalse.
      split. inv TGT_LOCAL_READ; eauto.
      eapply local_wf_read; eauto.
      split. eauto.
      inv LOCAL_SIM'; ss.
      contradiction SAFE_S.
      eapply rtcn_rtc in NO_SC_FENCE_NPRM_STEP_S.
      eapply no_scfence_nprm_steps_is_nprm_steps in NO_SC_FENCE_NPRM_STEP_S.
      eapply Thread_nprm_step_is_tau_step in NO_SC_FENCE_NPRM_STEP_S.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      exists e_src. split; eauto. eapply rtc_compose.
      eapply rtc_n1. eapply NO_SC_FENCE_NPRM_STEP_S.
      econs. econs. eapply Thread.step_program. econs. 
      Focus 2. eapply Local.step_read; eauto. ss. eauto. eauto. eauto.
      clear - RELY_STEP WF_I. exploit RELY_STEP; eauto. intros. des.
      clear x0 RELY_STEP. 
      unfold wf_I in *.
      eapply WF_I in x; eauto; ss. inv x; eauto.
    }
    {
      (* read non atomic location *)
      exploit THRD_STEP; [eapply TGT_READ | eauto..].
      clear THRD_STEP. ii; des. clear x x1 x2.
      exploit x0; eauto.
      clear - LOCAL0 AT_NA_LOC. inv LOCAL0.
      rewrite AT_NA_LOC in LO. ss; subst; ss. clear x0.
      introv SRC_STEPS; des. 
      exploit na_steps_dset_to_Thread_na_steps; [eapply SRC_STEPS0 | eauto..]. introv NA_STEPS.
      destruct e_src'.
      exploit na_steps_na_loc_same_prsv; [eapply NA_STEPS | eauto..]. ii; des.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEPS | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S_CAP.
      assert (SC_SAME: sc_src = sc).
      {
        exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
      }
      subst.
      do 8 eexists.
      split. eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      split. eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      split.
      eauto.
      split; eauto.
      split; eauto.
      introv ATM_LOC RSV_MEM_SRC_CAP.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..].
      introv AT_MEM_LOC_EQ.
      unfold Memory.get in RSV_MEM_SRC_CAP. rewrite <- AT_MEM_LOC_EQ in RSV_MEM_SRC_CAP.
      eauto.
      eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
      split.
      eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; eauto.
      split.
      eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unfold Memory.le; ii.
      destruct (lo loc0) eqn:AT_NA_LOC0.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS | eauto..]. ii.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
      unfold Memory.get in *. rewrite <- x1. rewrite <- x0 in LHS. eauto.
      unfold Memory.get in *. rewrite <- NA_SAME_PRSV; eauto.
      split; eauto. ii. destruct msg; eauto.
      destruct (lo loc0) eqn:AT_NA_LOC0.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS | eauto..]. ii.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
      unfold Memory.get in *.
      rewrite <- x0 in H. rewrite <- x1 in H0. eauto.
      unfold Memory.get in *.
      erewrite <- NA_SAME_PRSV in H0; eauto. tryfalse.
      split; eauto.
      eapply local_wf_read; eauto.
    }
  - (* write step *) 
    exploit Local_write_step_cap_prsv; [eapply LOCAL0 | eauto..].
    inv LOCAL_WF_T; eauto. ii; des.
    eapply Local_write_not_care_sc with (sc0 := sc_tgt) in x0.
    clear THRD_ABORT THRD_DONE RELY_STEP. 
    assert(TGT_WRITE: Thread.step lo true (ThreadEvent.write loc from to val released ord)
                                  (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                  (Thread.mk lang st_tgt' lc_tgt' sc_tgt mem')).
    {
      eapply Thread.step_program; eauto. 
    }
    destruct (lo loc) eqn: AT_NA_LOC.
    {
      (* write atomic location *)
      exploit THRD_STEP; eauto. ii; des. clear THRD_STEP x4 x5 x6.
      exploit x; eauto. clear - AT_NA_LOC x0. inv x0; ss.
      rewrite AT_NA_LOC in LO. ss. des; subst; ss.
      clear x; introv SRC_STEPS. des.
      destruct e_src, e_src'. ss. destruct te'; ss. des; subst; ss.
      exploit na_steps_na_loc_same_prsv; [eapply SRC_STEPS | eauto..]. ii; des.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply SRC_STEPS | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S_CAP.
      assert (SC_SAME: sc_src = sc).
      {
        exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
      }
      subst.
      assert(AT_LOC_STABLE1: forall loc, lo loc = Ordering.atomic -> mem_src loc = memory loc).
      {
        ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
      }
      assert(AT_LOC_STABLE2: forall loc, lo loc = Ordering.atomic -> mem_srcc loc = mem_c' loc).
      {
        ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
      }
      assert(MEM_AT_EQ': Mem_at_eq lo mem' memory0).
      {
        inv SRC_STEPS2; ss.
        contradiction SAFE_S.
        eapply na_steps_is_tau_steps in SRC_STEPS.
        eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
        exists e_src. split. 2: eauto.
        eapply rtc_compose; [ | eapply NP_STEPS].
        eapply rtc_n1. eapply SRC_STEPS.
        econs. econs. eapply Thread.step_program; eauto. ss.
        inv STEP_INV0; eauto.
      }
      inv SRC_STEPS0. inv LOCAL.
      assert(MEM_AT_EQ: Mem_at_eq lo mem_tgt memory).
      {
        inv STEP_INV.
        eapply Mem_at_eq_na_steps_prsv in SRC_STEPS; eauto; ss.
        eapply Mem_at_eq_reflexive; eauto.
        eapply Mem_at_eq_reflexive; eauto.
      }
      assert(KIND_MATCH: kind_match kind kind0).
      {
        eapply local_write_Mem_at_eq_prsv_kind_match;
          [eapply MEM_AT_EQ | eapply x0 | eapply LOCAL1 | eapply MEM_AT_EQ' | eauto..].
      }
      exploit Local_write_cap_conditional_prsv; [eapply LOCAL1 | eauto..].
      {
        eapply Thread_na_steps_is_no_scfence_nprm_steps in SRC_STEPS.
        eapply rtc_rtcn in SRC_STEPS. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in SRC_STEPS; eauto; ss.
        inv SRC_STEPS; eauto.
      }
      {
        instantiate (1 := mem_c'). 
        clear - NA_SAME_PRSV AT_LOC_STABLE1 AT_LOC_STABLE2 MEM_LE_SRC.
        unfold Memory.le. introv GET.
        destruct (lo loc) eqn:NA_AT_LOC.
        unfold Memory.get in *.
        erewrite <- AT_LOC_STABLE2; eauto.
        erewrite <- AT_LOC_STABLE1 in GET; eauto.
        unfold Memory.get in *.
        erewrite <- NA_SAME_PRSV; eauto.
      }
      { 
        ii; subst. destruct kind; ss.
        inv H1; ss. inv H0. inv ITV; ss. 
        assert(Memory.get loc to0 mem_srcc = Some (from0, msg)).
        {
          unfold Memory.get. erewrite AT_LOC_STABLE2; eauto.
        }
        destruct msg.
        exploit memory_additional_rsv_concrete_prsv; [| | eapply H | eauto..]; eauto. ii.
        inv STEP_INV.
        unfold Mem_at_eq in ATOMIC_COVER.
        exploit ATOMIC_COVER; [eapply AT_NA_LOC | eauto..]. introv MEM_APPROXEQ_LOC.
        unfold Mem_approxEq_loc in MEM_APPROXEQ_LOC. des.
        specialize (MEM_APPROXEQ_LOC from0 to0 val0). des.
        exploit MEM_APPROXEQ_LOC1; eauto. ii; des.
        inv x0. inv WRITE. inv PROMISE.
        exploit add_succeed_wf; [eapply MEM | eauto..]. ii. des.
        eapply DISJOINT in x; eauto.
        unfold Interval.disjoint in *.
        clear - FROM TO FROM0 TO0 x.
        specialize (x t). eapply x; eauto.
        econs; ss; eauto.
        econs; ss; eauto.
        exploit AT_COVER; [eapply AT_NA_LOC | eapply H | eauto..]. ii.
        inv LOCAL0. inv WRITE. inv PROMISE; ss.
        exploit add_succeed_wf; [eapply MEM | eauto..]. ii. des.
        eapply DISJOINT in x; eauto.
        unfold Interval.disjoint in *.
        specialize (x t). eapply x.
        econs; ss; eauto.
        econs; ss; eauto.
        destruct msg3; ss.
        destruct msg1; ss.
      }
      {
        ii; subst. inv H0. des.
        destruct kind; ss.
        assert(Memory.get loc x mem_srcc = Some (to, msg)).
        {
          unfold Memory.get. erewrite AT_LOC_STABLE2; eauto.
        }
        destruct msg.
        exploit memory_additional_rsv_concrete_prsv; [| | eapply H | eauto..]; eauto. ii.
        inv STEP_INV.
        unfold Mem_at_eq in ATOMIC_COVER.
        exploit ATOMIC_COVER; [eapply AT_NA_LOC | eauto..]. introv MEM_APPROXEQ_LOC.
        unfold Mem_approxEq_loc in MEM_APPROXEQ_LOC. des.
        specialize (MEM_APPROXEQ_LOC to x val0). des.
        exploit MEM_APPROXEQ_LOC1; eauto. ii; des.
        clear - x4 x0. inv x0. inv WRITE. inv PROMISE.
        exploit ATTACH; [ | eapply x4 | eauto..]. eauto.
        exploit AT_COVER; [eapply AT_NA_LOC | eapply H | eauto..]. ii.
        clear - LOCAL0 x4.
        inv LOCAL0. inv WRITE. inv PROMISE.
        exploit ATTACH; [ | eapply x4 | eauto..]. eauto.
        destruct msg3; ss.
        destruct msg1; ss.
      }
      instantiate (1 := sc_srcc). ii; des.
      assert(sc = sc0). inv LOCAL1; eauto. subst. 
      do 8 eexists.
      split.
      {
        eapply rtc_n1.
        eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
        eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
        econs. econs.
        Focus 2. eapply Local.step_write; eauto.
        ss; eauto. ss; eauto.
      }
      split.
      {
        eapply rtc_n1.
        eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
        eapply no_scfence_nprm_steps_is_nprm_steps; eauto.   
        econs. econs.
        Focus 2. eapply Local.step_write; eauto.
        ss. ss.
      }
      split. eauto.
      split.
      {
        introv NA_LOC.
        assert(loc <> loc0). ii; subst.
        rewrite AT_NA_LOC in NA_LOC; ss.
        eapply Local_write_disj_loc_stable in x4; eauto.
        eapply Local_write_disj_loc_stable in LOCAL1; eauto.
        rewrite <- LOCAL1. rewrite <- x4. eauto.
      }
      split.
      {
        ii.
        exploit Local_write_rsv_prsv; [eapply x4 | eauto..]. ii.
        des. eapply x7 in H0. clear x6 x7.
        exploit Local_write_rsv_prsv; [eapply LOCAL0 | eauto..]. ii.
        des. eapply x6. clear x6 x7.
        unfold Memory.get in H0. erewrite <- AT_LOC_STABLE2 in H0; eauto.
      }
      split.
      {
        eapply local_wf_write; eauto.
        eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; ss.
        eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; ss.
      }
      split.
      {
        eapply write_step_closed_mem; eauto.
        eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
        eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; ss.
        eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; ss.
      }
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto. ii. destruct msg; eauto.
      eapply Local_write_success in H0; eauto.
      exploit Local_write_none; [ | eapply H | eauto..]; eauto. ii.
      des; subst.
      exploit Local_write_succeed; [eapply LOCAL1 | eauto..]. ii.
      rewrite H in x7; ss.
      destruct (lo loc0) eqn:GET; ss.
      unfold Memory.get in *. 
      erewrite <- AT_LOC_STABLE2 in H0; eauto.
      erewrite <- AT_LOC_STABLE1 in x6; eauto. 
      exploit MORE_RESERVE_SRC; eauto. ii; subst.
      exploit H2; eauto. ii; des; ss.
      unfold Memory.get in *.
      erewrite <- NA_SAME_PRSV in H0; eauto.
      rewrite H0 in x6; ss.
      split; eauto.
      eapply local_wf_write; eauto.
      split; eauto.
      eapply write_step_closed_mem; eauto.
      inv SRC_STEPS2; ss.
      contradiction SAFE_S.
      eapply no_scfence_nprm_steps_is_nprm_steps in NO_SC_FENCE_NPRM_STEP_S.
      eapply Thread_nprm_step_is_tau_step in NO_SC_FENCE_NPRM_STEP_S.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      exists e_src. split; eauto. eapply rtc_compose.
      eapply rtc_n1. eapply NO_SC_FENCE_NPRM_STEP_S.
      econs. econs. eapply Thread.step_program. econs.
      Focus 2. eapply Local.step_write; eauto. ss. eauto. eauto. eauto.
      clear - RELY_STEP WF_I. exploit RELY_STEP; eauto. intros. des.
      clear x0 RELY_STEP.
      unfold wf_I in *.
      eapply WF_I in x; eauto; ss. inv x; eauto.
    }
    {
      (* write non-atomic location *)
      exploit THRD_STEP; [eapply TGT_WRITE | eauto..].
      clear THRD_STEP. ii; des. clear x x5 x6.
      exploit x4; eauto.
      clear - LOCAL0 AT_NA_LOC. inv LOCAL0.
      rewrite AT_NA_LOC in LO. ss; subst; ss. clear x4.
      introv SRC_STEPS; des.
      exploit na_steps_dset_to_Thread_na_steps; [eapply SRC_STEPS0 | eauto..]. introv NA_STEPS.
      destruct e_src'.
      exploit na_steps_na_loc_same_prsv; [eapply NA_STEPS | eauto..]. ii; des.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEPS | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S.
      exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
      introv NO_SC_FENCE_NPRM_STEP_S_CAP.
      assert (SC_SAME: sc_src = sc).
      {
        exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
      }
      subst.
      do 8 eexists.
      split. eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      split. eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      split.
      eauto.
      split; eauto.
      split; eauto.
      introv ATM_LOC RSV_MEM_SRC_CAP.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..].
      introv AT_MEM_LOC_EQ.
      unfold Memory.get in RSV_MEM_SRC_CAP. rewrite <- AT_MEM_LOC_EQ in RSV_MEM_SRC_CAP.
      assert (loc <> loc0). ii; subst. rewrite AT_NA_LOC in ATM_LOC. ss.
      exploit Local_write_disj_loc_stable; [eapply LOCAL0 | eauto..]. ii.
      unfold Memory.get. rewrite <- x4.
      eauto.
      eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
      split.
      eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; eauto.
      split.
      eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      unfold Memory.le; ii.
      destruct (lo loc0) eqn:AT_NA_LOC0.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS | eauto..]. ii.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
      unfold Memory.get in *. rewrite <- x5. rewrite <- x4 in LHS. eauto.
      unfold Memory.get in *. rewrite <- NA_SAME_PRSV; eauto.
      split; eauto. ii. destruct msg; eauto.
      destruct (lo loc0) eqn:AT_NA_LOC0.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEPS | eauto..]. ii.
      exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
      unfold Memory.get in *.
      rewrite <- x4 in H. rewrite <- x5 in H0. eauto.
      unfold Memory.get in *.
      erewrite <- NA_SAME_PRSV in H0; eauto. tryfalse.
      split; eauto.
      eapply local_wf_write; eauto.
      split; eauto.
      eapply write_step_closed_mem; eauto.
    }
  - (* update step *)
    exploit Local_read_step_cap_prsv; [eapply LOCAL1 | eapply MEM_LE | eauto..].
    introv LOCAL_READ.
    exploit Local_write_step_cap_prsv; [eapply LOCAL2 | eauto..].
    inv LOCAL_WF_T; eauto. inv LOCAL_READ; eauto.
    inv LOCAL1; eauto. ii; des.
    clear THRD_ABORT THRD_DONE RELY_STEP. 
    eapply Local_write_not_care_sc with (sc0 := sc_tgt) in x0. 
    assert(TGT_UPD: Thread.step lo true (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)
                                (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                (Thread.mk lang st_tgt' lc_tgt' sc_tgt mem')).
    {
      eapply Thread.step_program. econs; eauto.
    }
    exploit THRD_STEP; eauto. ii; des. clear THRD_STEP x4 x5 x6.
    exploit x; eauto. ss.
    clear x; introv SRC_STEPS. des.
    destruct e_src, e_src'.
    exploit na_steps_na_loc_same_prsv; [eapply SRC_STEPS | eauto..]. ii; des.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply SRC_STEPS | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S_CAP.
    assert (SC_SAME: sc_src = sc).
    {
      exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
    }
    subst.
    assert(AT_LOC_STABLE1: forall loc, lo loc = Ordering.atomic -> mem_src loc = memory loc).
    {
      ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
    }
    assert(AT_LOC_STABLE2: forall loc, lo loc = Ordering.atomic -> mem_srcc loc = mem_c' loc).
    {
      ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
    } 
    assert(MEM_AT_EQ': Mem_at_eq lo mem' memory0).
    {
      inv SRC_STEPS2; ss.
      contradiction SAFE_S.
      eapply na_steps_is_tau_steps in SRC_STEPS.
      eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
      exists e_src. split. 2: eauto.
      eapply rtc_compose; [ | eapply NP_STEPS].
      eapply rtc_n1. eapply SRC_STEPS. 
      econs. econs. eapply Thread.step_program; eauto.
      destruct te'; ss.
      inv STEP_INV0; eauto.
    }
    inv SRC_STEPS0. destruct te'; ss. des; subst; ss.
    inv LOCAL.
    assert(MEM_AT_EQ: Mem_at_eq lo mem_tgt memory).
    {
      inv STEP_INV.
      eapply Mem_at_eq_na_steps_prsv in SRC_STEPS; eauto; ss.
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    }
    assert(KIND_MATCH: kind_match kind kind0).
    {
      eapply local_write_Mem_at_eq_prsv_kind_match;
        [eapply MEM_AT_EQ | eapply x0 | eapply LOCAL0 | eapply MEM_AT_EQ' | eauto..].
    } 
    assert(SRC_AT_READ: Local.read_step local mem_c' loc tsr valr releasedr0 ordr lc2 lo).
    {
      inv LOCAL1. econs; eauto.
      unfold Memory.get in GET0. rewrite <- AT_LOC_STABLE1 in GET0; eauto.
      unfold Memory.get. erewrite <- AT_LOC_STABLE2; eauto.      
    }
    exploit Local_write_cap_conditional_prsv; [eapply LOCAL0 | eauto..].
    { 
      eapply Thread_na_steps_is_no_scfence_nprm_steps in SRC_STEPS.
      eapply rtc_rtcn in SRC_STEPS. des.
      eapply no_scfence_nprm_steps_prsv_local_wf in SRC_STEPS; eauto; ss.
      inv SRC_STEPS; eauto.
      inv LOCAL1; eauto.
    }
    {
      instantiate (1 := mem_c'). 
      clear - NA_SAME_PRSV AT_LOC_STABLE1 AT_LOC_STABLE2 MEM_LE_SRC.
      unfold Memory.le. introv GET.
      destruct (lo loc) eqn:NA_AT_LOC.
      unfold Memory.get in *.
      erewrite <- AT_LOC_STABLE2; eauto.
      erewrite <- AT_LOC_STABLE1 in GET; eauto.
      unfold Memory.get in *.
      erewrite <- NA_SAME_PRSV; eauto.
    }
    { 
      ii; subst. destruct kind; ss.
      inv H1; ss. inv H0. inv ITV; ss. 
      assert(Memory.get loc to mem_srcc = Some (from0, msg)).
      {
        unfold Memory.get. erewrite AT_LOC_STABLE2; eauto.
      }
      destruct msg.
      exploit memory_additional_rsv_concrete_prsv; [| | eapply H | eauto..]; eauto. ii.
      inv STEP_INV.
      unfold Mem_at_eq in ATOMIC_COVER.
      exploit ATOMIC_COVER; [eapply AT | eauto..]. introv MEM_APPROXEQ_LOC.
      unfold Mem_approxEq_loc in MEM_APPROXEQ_LOC. des.
      specialize (MEM_APPROXEQ_LOC from0 to val). des.
      exploit MEM_APPROXEQ_LOC1; eauto. ii; des.
      inv x0. inv WRITE. inv PROMISE.
      exploit add_succeed_wf; [eapply MEM | eauto..]. ii. des.
      eapply DISJOINT in x; eauto.
      unfold Interval.disjoint in *.
      clear - FROM TO FROM0 TO0 x.
      specialize (x t). eapply x; eauto.
      econs; ss; eauto.
      econs; ss; eauto. 
      exploit AT_COVER; [eapply AT | eapply H | eauto..]. ii.
      inv LOCAL2. inv WRITE. inv PROMISE; ss.
      exploit add_succeed_wf; [eapply MEM | eauto..]. ii. des.
      eapply DISJOINT in x; eauto.
      unfold Interval.disjoint in *.
      specialize (x t). eapply x.
      econs; ss; eauto.
      econs; ss; eauto.
      destruct msg3; ss.
      destruct msg1; ss.
    }
    {
      ii; subst. inv H0. des.
      destruct kind; ss.
      assert(Memory.get loc x mem_srcc = Some (tsw, msg)).
      {
        unfold Memory.get. erewrite AT_LOC_STABLE2; eauto.
      }
      destruct msg.
      exploit memory_additional_rsv_concrete_prsv; [| | eapply H | eauto..]; eauto. ii.
      inv STEP_INV.
      unfold Mem_at_eq in ATOMIC_COVER.
      exploit ATOMIC_COVER; [eapply AT | eauto..]. introv MEM_APPROXEQ_LOC.
      unfold Mem_approxEq_loc in MEM_APPROXEQ_LOC. des.
      specialize (MEM_APPROXEQ_LOC tsw x val). des.
      exploit MEM_APPROXEQ_LOC1; eauto. ii; des.
      clear - x4 x0. inv x0. inv WRITE. inv PROMISE.
      exploit ATTACH; [ | eapply x4 | eauto..]. eauto.
      exploit AT_COVER; [eapply AT | eapply H | eauto..]. ii.
      clear - LOCAL2 x4.
      inv LOCAL2. inv WRITE. inv PROMISE.
      exploit ATTACH; [ | eapply x4 | eauto..]. eauto.
      destruct msg3; ss.
      destruct msg1; ss.
    }
    instantiate (1 := sc_srcc). ii; des.
    assert(sc = sc0). inv LOCAL0; ss. subst.
    do 8 eexists.
    split.
    {
      eapply rtc_n1.
      eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      econs. econs.
      Focus 2. eapply Local.step_update; eauto.
      ss; eauto. ss; eauto.
    }
    split.
    {
      eapply rtc_n1.
      eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.   
      econs. econs.
      Focus 2. eapply Local.step_update; eauto.
      ss. ss.
    }
    split. eauto.
    split.
    {
      introv NA_LOC.
      assert(loc <> loc0). ii; subst.
      rewrite AT in NA_LOC; ss.
      eapply Local_write_disj_loc_stable in x4; eauto.
      eapply Local_write_disj_loc_stable in LOCAL0; eauto.
      rewrite <- LOCAL0. rewrite <- x4. eauto.
    }
    split.
    {
      ii.
      exploit Local_write_rsv_prsv; [eapply x4 | eauto..]. ii.
      des. eapply x7 in H0. clear x6 x7.
      exploit Local_write_rsv_prsv; [eapply LOCAL2 | eauto..]. ii.
      des. eapply x6. clear x6 x7.
      unfold Memory.get in H0. erewrite <- AT_LOC_STABLE2 in H0; eauto.
    }
    split.
    {
      eapply local_wf_write; eauto.
      eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
      eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; ss.
      eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
      exploit no_scfence_nprm_steps_prsv_local_wf; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..]; ss.
      ii.
      eapply local_wf_read; eauto.
      eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; ss.
    }
    split.
    {
      assert(CLOSED_MEM_TEMP: Memory.closed memory).
      {
        eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
        eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; ss.
      }
      eapply write_step_closed_mem; [ | eapply LOCAL0 | eauto..]; eauto.
      clear - LOCAL1 CLOSED_MEM_TEMP.
      inv LOCAL1. inv CLOSED_MEM_TEMP.
      eapply CLOSED in GET; eauto. des. inv MSG_CLOSED; eauto.       
      eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
      exploit no_scfence_nprm_steps_prsv_local_wf; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..]; ss.
      ii.
      eapply local_wf_read; eauto.
    }
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto. ii. destruct msg; eauto.
    eapply Local_write_success in H0; eauto.
    exploit Local_write_none; [ | eapply H | eauto..]; eauto. ii.
    des; subst.
    exploit Local_write_succeed; [eapply LOCAL0 | eauto..]. ii.
    rewrite H in x7; ss.
    destruct (lo loc0) eqn:GET'; ss.
    unfold Memory.get in *. 
    erewrite <- AT_LOC_STABLE2 in H0; eauto.
    erewrite <- AT_LOC_STABLE1 in x6; eauto. 
    exploit MORE_RESERVE_SRC; eauto. ii; subst.
    exploit H2; eauto. ii; des; ss.
    unfold Memory.get in *.
    erewrite <- NA_SAME_PRSV in H0; eauto.
    rewrite H0 in x6; ss.
    split; eauto.
    eapply local_wf_write; eauto.
    eapply local_wf_read; eauto.
    split.
    eapply write_step_closed_mem; [ | eapply x0 | eauto..]; eauto.
    clear - MEM_CLOSED LOCAL_READ.
    inv LOCAL_READ; ss. inv LC2. inv MEM_CLOSED.
    exploit CLOSED; eauto. ii; des.
    inv MSG_CLOSED. eauto.
    eapply local_wf_read; eauto.
    inv SRC_STEPS2; ss.
    contradiction SAFE_S.
    eapply no_scfence_nprm_steps_is_nprm_steps in NO_SC_FENCE_NPRM_STEP_S.
    eapply Thread_nprm_step_is_tau_step in NO_SC_FENCE_NPRM_STEP_S.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
    exists e_src. split; eauto. eapply rtc_compose.
    eapply rtc_n1. eapply NO_SC_FENCE_NPRM_STEP_S.
    econs. econs. eapply Thread.step_program. econs.
    Focus 2. eapply Local.step_update; eauto. ss. eauto. eauto. eauto.
    clear - RELY_STEP WF_I. exploit RELY_STEP; eauto. intros. des.
    clear x0 RELY_STEP.
    unfold wf_I in *.
    eapply WF_I in x; eauto; ss. inv x; eauto.
  - (* fence *)
    clear RELY_STEP THRD_DONE THRD_ABORT.
    assert(TGT_FENCE: Local.fence_step lc_tgt sc_tgt ordr ordw lc_tgt' sc_tgt).
    {
      clear - NOT_SC_FENCE LOCAL0.
      inv LOCAL0.
      econs; eauto.
      destruct ordw; ss; tryfalse.
      contradiction NOT_SC_FENCE; eauto.
      destruct ordw; ss; tryfalse.
      contradiction NOT_SC_FENCE; eauto.
    }
    exploit THRD_STEP; eauto.
    eapply Thread.step_program; eauto.
    econs. Focus 2. eapply Local.step_fence; eauto.
    ss; eauto.
    clear THRD_STEP. ii; des. clear x0 x1 x2.
    exploit x; eauto. ss.
    clear x. introv SRC_STEPS. des.
    destruct e_src, e_src'.
    exploit na_steps_na_loc_same_prsv; [eapply SRC_STEPS | eauto..]. ii; des.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply SRC_STEPS | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S.
    exploit Thread_na_steps_is_no_scfence_nprm_steps; [eapply NA_STEP_CAP | eauto..].
    introv NO_SC_FENCE_NPRM_STEP_S_CAP.
    assert (SC_SAME: sc_src = sc).
    {
      exploit no_scfence_nprm_steps_sc_same; [eapply NO_SC_FENCE_NPRM_STEP_S | eauto..].
    }
    subst.
    assert(AT_LOC_STABLE1: forall loc, lo loc = Ordering.atomic -> mem_src loc = memory loc).
    {
      ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
    }
    assert(AT_LOC_STABLE2: forall loc, lo loc = Ordering.atomic -> mem_srcc loc = mem_c' loc).
    {
      ii. eapply na_steps_atomic_loc_stable_rtc; eauto.
    }
    inv SRC_STEPS0. destruct te'; ss; subst; ss. inv LOCAL.
    inv PROG_EVENT_EQ.
    assert(SRC_CAP_FENCE: Local.fence_step local sc_srcc ordr ordw local0 sc_srcc).
    {
      clear - LOCAL1 NOT_SC_FENCE.
      inv LOCAL1. econs; eauto. 
      destruct ordw; ss.
      contradiction NOT_SC_FENCE; eauto.
      destruct ordw; ss.
      contradiction NOT_SC_FENCE; eauto.
    }
    assert(sc = sc0).
    {
      clear - LOCAL1 NOT_SC_FENCE.
      inv LOCAL1; eauto. destruct ordw; ss.
      contradiction NOT_SC_FENCE; eauto.
    }
    subst.
    assert(FENCE_STEP: no_scfence_nprm_step lang lo
                                            (Thread.mk lang state local sc0 memory0)
                                            (Thread.mk lang state0 local0 sc0 memory0)).
    {
      econs. econs.
      Focus 2. eapply Local.step_fence; eauto.
      ss. ss. eauto.
    }
    do 8 eexists.
    split.
    {
      eapply rtc_n1.
      eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S_CAP.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.
      econs. econs.
      Focus 2. eapply Local.step_fence; eauto.
      ss; eauto. ss; eauto.
    }
    split.
    {
      eapply rtc_n1.
      eapply no_scfence_nprm_steps_not_care_sc in NO_SC_FENCE_NPRM_STEP_S.
      eapply no_scfence_nprm_steps_is_nprm_steps; eauto.   
      econs. econs.
      Focus 2. eapply Local.step_fence; eauto.
      ss. ss.
    }
    split. eauto.
    split; eauto.
    split.
    introv ATM_LOC GET_MEM_C'.
    unfold Memory.get in GET_MEM_C'. erewrite <- AT_LOC_STABLE2 in GET_MEM_C'; eauto.
    eapply rtc_rtcn in NO_SC_FENCE_NPRM_STEP_S. des.
    split.
    eapply no_scfence_nprm_step_prsv_local_wf in FENCE_STEP; eauto; ss.
    eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
    eapply no_scfence_nprm_steps_prsv_local_wf in NO_SC_FENCE_NPRM_STEP_S; eauto.
    split.
    eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SC_FENCE_NPRM_STEP_S; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    unfold Memory.le; ii.
    destruct (lo loc) eqn:AT_NA_LOC.
    exploit na_steps_atomic_loc_stable_rtc; [eapply SRC_STEPS | eauto..]. ii.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
    unfold Memory.get in *. rewrite <- x1. rewrite <- x0 in LHS. eauto.
    unfold Memory.get in *. rewrite <- NA_SAME_PRSV; eauto.
    split; eauto. ii. destruct msg; eauto.
    destruct (lo loc) eqn:AT_NA_LOC.
    exploit na_steps_atomic_loc_stable_rtc; [eapply SRC_STEPS | eauto..]. ii.
    exploit na_steps_atomic_loc_stable_rtc; [eapply NA_STEP_CAP | eauto..]. ii.
    unfold Memory.get in *.
    rewrite <- x0 in H. rewrite <- x1 in H0. eauto.
    unfold Memory.get in *.
    erewrite <- NA_SAME_PRSV in H0; eauto. tryfalse.
    split. inv TGT_FENCE; eauto.
    exploit no_scfence_nprm_step_prsv_local_wf.
    econs. econs.
    Focus 2. eapply Local.step_fence. eapply LOCAL0. eauto. eauto. eauto.
    ss. eapply MEM_CLOSED. ss.
    ss.
    split; eauto.
    inv SRC_STEPS2; ss.
    contradiction SAFE_S.
    eapply rtcn_rtc in NO_SC_FENCE_NPRM_STEP_S.
    eapply no_scfence_nprm_steps_is_nprm_steps in NO_SC_FENCE_NPRM_STEP_S.
    eapply Thread_nprm_step_is_tau_step in NO_SC_FENCE_NPRM_STEP_S.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss.
    exists e_src. split; eauto. eapply rtc_compose.
    eapply rtc_n1. eapply NO_SC_FENCE_NPRM_STEP_S.
    econs. econs. eapply Thread.step_program. econs.
    Focus 2. eapply Local.step_fence; eauto. ss. eauto. eauto. eauto.
    clear - RELY_STEP WF_I. exploit RELY_STEP; eauto. intros. des.
    clear x0 RELY_STEP.
    unfold wf_I in *.
    eapply WF_I in x; eauto; ss. inv x; eauto.
    Unshelve.
    exact lo.
Qed.

Lemma promise_step_not_care_sc
      lang pf te st lc sc mem st' lc' sc' mem' sc0
      (PROM_STEP: Thread.promise_step pf te (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem')):
 Thread.promise_step pf te (Thread.mk lang st lc sc0 mem) (Thread.mk lang st' lc' sc0 mem').
Proof.
  inv PROM_STEP.
  econs; eauto.
Qed.

Lemma tgt_pf_promise_step_cap_sim
      lang e index index_order I lo inj dset b
      st_tgt lc_tgt sc_tgtc mem_tgtc sc_tgt mem_tgt st_tgt' lc_tgt' sc_tgtc' mem_tgtc'
      st_src lc_src sc_srcc mem_srcc sc_src mem_src
      (STEP: Thread.promise_step true e
                                 (Thread.mk lang st_tgt lc_tgt sc_tgtc mem_tgtc)
                                 (Thread.mk lang st_tgt' lc_tgt' sc_tgtc' mem_tgtc'))
      (LOCAL_WF_T: Local.wf lc_tgt mem_tgt)
      (MEM_CLOSED: Memory.closed mem_tgt)
      (LOCAL_SIM: @local_sim_state index index_order lang I lo inj dset b
                                   (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk lang st_src lc_src sc_src mem_src))
      (MEM_LE: Memory.le mem_tgt mem_tgtc)
      (MORE_RESERVE: 
         forall loc to from msg, Memory.get loc to mem_tgt = None ->
                            Memory.get loc to mem_tgtc = Some (from, msg) ->
                            msg = Message.reserve)
      (SAFE_S: ~ (exists e_src', rtc (@Thread.tau_step lang lo)
                                 (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
                             Thread.is_abort e_src' lo))
      (NA_SAME: forall loc, lo loc = Ordering.nonatomic -> mem_src loc = mem_srcc loc)
      (AT_COVER: forall loc, lo loc = Ordering.atomic ->
                        (forall from to, Memory.get loc to mem_srcc = Some (from, Message.reserve) ->
                                    Memory.get loc to mem_tgtc = Some (from, Message.reserve)))
      (MEM_LE_SRC: Memory.le mem_src mem_srcc)
      (MORE_RESERVE_SRC: 
         forall loc to from msg, Memory.get loc to mem_src = None ->
                            Memory.get loc to mem_srcc = Some (from, msg) ->
                            msg = Message.reserve)
      (LOCAL_WF_S: Local.wf lc_src mem_src)
      (MEMORY_CLOSED: Memory.closed mem_src)
      (WF_I: wf_I I)
      (MONOTONIC_INJ: monotonic_inj inj)
      (TGT_PROM_CONS: Local.promise_consistent lc_tgt)
      (TGT_PROM_CONS': Local.promise_consistent lc_tgt')
  :
    exists st_src' lc_src' mem_srcc' mem_src' inj' dset' b' mem_tgt',
      <<S_STEPS: rtc (Thread.nprm_step lo)
                     (Thread.mk lang st_src lc_src sc_srcc mem_srcc)
                     (Thread.mk lang st_src' lc_src' sc_srcc mem_srcc')>> /\
      <<S_STEPS': rtc (Thread.nprm_step lo)
                      (Thread.mk lang st_src lc_src sc_src mem_src)
                      (Thread.mk lang st_src' lc_src' sc_src mem_src')>> /\
      <<LOCAL_SIM': @local_sim_state index index_order lang I lo inj' dset' b'               
                                     (Thread.mk lang st_tgt' lc_tgt' sc_tgt mem_tgt')
                                     (Thread.mk lang st_src' lc_src' sc_src mem_src')>> /\
      <<NA_SAME': forall loc, lo loc = Ordering.nonatomic -> mem_src' loc = mem_srcc' loc>> /\ 
      <<AT_COVER': forall loc, lo loc = Ordering.atomic ->
                          (forall from to, Memory.get loc to mem_srcc' = Some (from, Message.reserve) ->
                                      Memory.get loc to mem_tgtc' = Some (from, Message.reserve))>> /\ 
      <<LOCAL_WF_S': Local.wf lc_src' mem_src'>> /\
      <<MEMORY_CLOSED: Memory.closed mem_src'>> /\
      <<MEM_LE_T': Memory.le mem_tgt' mem_tgtc'>> /\
      <<MORE_RESERVE_TGT':
          forall loc to from msg, Memory.get loc to mem_tgt' = None ->
                             Memory.get loc to mem_tgtc' = Some (from, msg) ->
                             msg = Message.reserve>> /\
      <<MEM_LE_S': Memory.le mem_src' mem_srcc'>> /\
      <<MORE_RESERVE_S':
          forall loc to from msg, Memory.get loc to mem_src' = None ->
                             Memory.get loc to mem_srcc' = Some (from, msg) ->
                             msg = Message.reserve>> /\
      <<LOCAL_WF_TGT': Local.wf  lc_tgt' mem_tgt'>> /\
      <<MEMORY_CLOSED_T: Memory.closed mem_tgt'>> /\
      <<MONOTONIC_INJ': monotonic_inj inj'>>.
Proof.
  exploit promise_step_cap_prsv; [eapply STEP | eauto..].
  inv LOCAL_WF_T; eauto.
  ii; des.
  eapply promise_step_not_care_sc with (sc0 := sc_tgt) in x0; eauto.
  inv LOCAL_SIM; ss.
  (* abort *)
  contradiction SAFE_S.
  eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS; ss. eauto.
  (* not abort *)
  rename x4 into FRAME_T.
  clear RELY_STEP THRD_DONE THRD_ABORT.
  exploit THRD_STEP.
  econs. eapply x0. 
  clear THRD_STEP. ii; des. clear x x4 x5.
  exploit x6; eauto.
  inv x0. ss. eauto.
  clear x6. ii; des.
  destruct e_src'.
  exploit pf_promise_steps_cap; [eapply x | eapply MEM_LE_SRC | eauto..]. ii; des.
  exploit pf_promise_steps_is_no_scfence_nprm_steps; [eapply x | eauto..].
  instantiate (1 := lo). introv NO_SCFENCE_SRC.
  exploit pf_promise_steps_is_no_scfence_nprm_steps; [eapply PF_PS' | eauto..].
  instantiate (1 := lo). introv NO_SCFENCE_SRCC.
  eapply no_scfence_nprm_steps_not_care_sc with (sc0 := sc_srcc) in NO_SCFENCE_SRCC.
  assert(sc_src = sc).
  {
    eapply no_scfence_nprm_steps_sc_same in NO_SCFENCE_SRC; ss.
  }
  subst.
  do 8 eexists.
  split.
  eapply no_scfence_nprm_steps_is_nprm_steps; [eapply NO_SCFENCE_SRCC | eauto..].
  split.
  eapply no_scfence_nprm_steps_is_nprm_steps; [eapply NO_SCFENCE_SRC | eauto..].
  split. eauto. 
  split; eauto.
  split.
  {
    introv AT GET_MEMC'.
    inv x4; ss.
    contradiction SAFE_S.
    eapply NPAuxThread_tau_steps_2_Thread_tau_steps in NP_STEPS. ss.
    exists e_src. split; eauto.
    eapply no_scfence_nprm_steps_is_nprm_steps in NO_SCFENCE_SRC.
    eapply Thread_nprm_step_is_tau_step in NO_SCFENCE_SRC.
    eapply rtc_compose; [eapply NO_SCFENCE_SRC | eapply NP_STEPS].
    clear THRD_STEP RELY_STEP THRD_DONE THRD_ABORT.
    destruct (Memory.get loc to memory) eqn:GET.
    {
      destruct p.
      exploit MEM_LE'; [eapply GET | eauto..]. ii.
      rewrite GET_MEMC' in x4. inv x4.
      inv STEP_INV0.
      unfold Mem_at_eq in ATOMIC_COVER.
      eapply ATOMIC_COVER in AT; eauto.
      unfold Mem_approxEq_loc in AT. des.
      specialize (AT0 t to). des. eapply AT1 in GET. eauto.
    }
    {
      exploit FRAME; [eapply GET_MEMC' | eapply GET | eauto..]. ii; des.
      exploit AT_COVER; [eapply AT | eapply x4 | eauto..]. ii.
      destruct (Memory.get loc to mem_tgt) eqn:GET_MEMT. destruct p.
      exploit MEM_LE; [eapply GET_MEMT | eauto..]. ii.
      rewrite x6 in x7. inv x7.
      clear - STEP_INV x5 GET_MEMT AT.
      inv STEP_INV. unfold Mem_at_eq in ATOMIC_COVER.
      eapply ATOMIC_COVER in AT; eauto.
      unfold Mem_approxEq_loc in AT. des.
      specialize (AT0 t to). des.
      eapply AT0 in GET_MEMT. rewrite x5 in GET_MEMT; ss.
      exploit FRAME_T; [eapply x6 | eapply GET_MEMT | eauto..]. ii; des; eauto.
    }
  }
  eapply rtc_rtcn in NO_SCFENCE_SRC. des.
  split.
  {
    eapply no_scfence_nprm_steps_prsv_local_wf in NO_SCFENCE_SRC; ss.
  }
  split.
  {
    eapply no_scfence_nprm_steps_prsv_memory_closed in NO_SCFENCE_SRC; ss.
  }
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  exploit no_scfence_nprm_step_prsv_local_wf.
  eapply no_scfence_nprm_step_intro2. eapply x0.
  ss. ss. ss.
  split; eauto.
  exploit no_scfence_nprm_step_prsv_memory_closed.
  eapply no_scfence_nprm_step_intro2. eapply x0.
  ss. ss. ss.
  Unshelve.
  exact lo.
  exact lo.
Qed.
