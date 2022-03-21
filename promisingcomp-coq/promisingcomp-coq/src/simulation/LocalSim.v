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
Require Import Cover.

Set Implicit Arguments.

(** * Thread-local simulation *)

(** This file defines the thread-local simulation (Section 4 in paper) *)

(** [local_sim] in this file (Definition 4.4 in paper) is the definition of the thread-local upward simulation *)

(** The main definition includes:
    - [Invariant]: invariant parameter for shared state (in Figure 8 in paper) ;
    - [SI]: step invariant that holds at every simulation step (Definition 4.3 in paper);
    - [Rely]: rely condition (Definition 4.2 in paper);
    - [local_sim_state]: thread-local upward simulation on thread states (Definition 4.5 in paper);
    - [local_sim]: thread-local upward simulation (Definition 4.4 in paper).  *)

Definition Mem_approxEq_loc (loc: Loc.t) (mem_tgt mem_src: Memory.t): Prop :=
    (forall f t val, (exists R, Memory.get loc t mem_tgt = Some (f, Message.concrete val R))
                <-> (exists R', Memory.get loc t mem_src = Some (f, Message.concrete val R'))) /\
    (forall f t, Memory.get loc t mem_tgt = Some (f, Message.reserve)
            <-> Memory.get loc t mem_src = Some (f, Message.reserve)).

(** Memory atomic part equal *)
Definition Mem_at_eq (lo: Ordering.LocOrdMap) (mem_tgt mem_src: Memory.t) : Prop :=
  forall loc, lo loc = Ordering.atomic -> Mem_approxEq_loc loc mem_tgt mem_src.

(** ** Shared resource (defined as 'Sst' in paper) *)
(** It includes:
   - [T_SC]: timemap for SC fence in the target level;
   - [T_MEM]: memory in the target level;
   - [S_SC]: timemap for SC fence in the source level;
   - [S_MEM]: memory in the source level *)
Structure Rss := {T_SC: TimeMap.t; T_MEM: Memory.t;
   S_SC: TimeMap.t; S_MEM: Memory.t}.

(** ** Invariant for shared state *)
Definition Invariant := Ordering.LocOrdMap -> Mapping -> Rss -> Prop. 

(** ** Well-defined invariant for shared resource *)
(** [weak_MsgInj]: the well-formed message mapping (Definition 4.1 in paper). It requires:
    - each message in the target level has a related message in the source level;
    - the mapping [inj] is monotonic *)
Definition wf_I (I: Invariant) : Prop :=
  forall lo inj S,
    I lo inj S -> weak_MsgInj inj S.(T_MEM) S.(S_MEM).

(** ** Relation between target promises and source promises *)
Inductive rel_promises {index: Type} (inj: Mapping) (pdset: @DelaySet index) (prm_tgt prm_src: Memory.t) :=
| rel_promises_intro
    (SOUND1: forall loc t i,
        dset_get loc t pdset = Some i ->
        (exists t' f' val' R',
            inj loc t = Some t' /\  Memory.get loc t' prm_src = Some (f', Message.concrete val' R')))
    (SOUND2: forall loc t f val R,
        Memory.get loc t prm_tgt = Some (f, Message.concrete val R) ->
        (exists t' f' val' R',
            inj loc t = Some t' /\ Memory.get loc t' prm_src = Some (f', Message.concrete val' R')))
    (COMPLETE: forall loc f' t' val' R',
        Memory.get loc t' prm_src = Some (f', Message.concrete val' R') ->
        (exists t, inj loc t = Some t' /\ 
                   ((exists i, dset_get loc t pdset = Some  i) \/
                    (exists f val R, Memory.get loc t prm_tgt = Some (f, Message.concrete val R))))).

Definition state_at_out_step (e: ProgramEvent.t) :=
  match e with
  | ProgramEvent.silent => False
  | ProgramEvent.read _ _ Ordering.plain => False
  | ProgramEvent.write _ _ Ordering.plain => False
  | _ => True
  end.

Definition state_in_step (e: ProgramEvent.t) :=
  match e with
  | ProgramEvent.silent => True
  | ProgramEvent.read _ _ Ordering.plain => True
  | ProgramEvent.write _ _ Ordering.plain => True
  | _ => False
  end.

Lemma state_in_or_out
      e:
  state_at_out_step e \/ state_in_step e.
Proof.
  destruct e; ss; eauto.
  destruct ord; ss; eauto.
  destruct ord; ss; eauto.
Qed.

Lemma state_at_out_step_implies_threadEvt_is_at_or_at_step
      e
      (STATE_OUT: state_at_out_step (ThreadEvent.get_program_event e)):
  ThreadEvent.is_at_or_out_step e.
Proof.
  destruct e; ss.
Qed. 

Lemma state_in_step_implies_threadEvt_is_na_step
      te lang (e e': Thread.t lang) lo
      (PROG_STEP: Thread.program_step te lo e e')
      (STATE_OUT: state_in_step (ThreadEvent.get_program_event te)):
  ThreadEvent.is_na_step te.
Proof.
  destruct te; ss.
  inv PROG_STEP; ss. inv LOCAL; ss.
Qed.

(** ** Step invariant [SI] between target and source thread configuraitons (Definition 4.3 in paper) *)
(** [SI] includes four items:
    - [VIEW_LE]: an unobserved messge in the target level has a related unobserved message in the source level;
    - [REL_PROMISES]: a one-to-one mapping between the target and source threads' promises (including this in delayed write set [dset]);
    - [DSET_EMPTY]: If the current instruction is an atomic memory access, the delayed write set should be empty
    - [ATOMIC_COVER]: The sub-memory for atomic variables in the target and source levels must be strictly equal, except for the message view *)
Inductive SI {lang: language} {index: Type}:
  Mapping -> Ordering.LocOrdMap ->
  ((Language.state lang) * Local.t * Memory.t) ->
  ((Language.state lang) * Local.t * Memory.t) -> (@DelaySet index) -> Prop :=
| SI_intro
    inj lo st_tgt lc_tgt mem_tgt st_src lc_src mem_src dset
    (* target view and source view relation *)
    (VIEW_LE: forall loc t t',
        inj loc t = Some t' -> 
        Time.lt (View.rlx (TView.cur (Local.tview lc_tgt)) loc) t -> 
        Time.lt (View.rlx (TView.cur (Local.tview lc_src)) loc) t')
    (* relation between target promises and source promises *)
    (REL_PROMISES: exists pdset, dset_subset pdset dset /\
                            rel_promises inj pdset (Local.promises lc_tgt) (Local.promises lc_src))
    (* dset empty if the next step is atomic or output step *)
    (DSET_EMP: forall st_tgt' e,
        (Language.step lang) e st_tgt st_tgt' -> state_at_out_step e ->
                                 dset = dset_init)
    (* atomic memory cover same *)
    (ATOMIC_COVER: Mem_at_eq lo mem_tgt mem_src)
  :
    SI inj lo (st_tgt, lc_tgt, mem_tgt) (st_src, lc_src, mem_src) dset. 

(* Concrete coverd *) 
Inductive concrete_covered (loc: Loc.t) (ts: Time.t) (mem: Memory.t): Prop :=
| concrete_covered_intro
    from to val R
    (CONCRETE_MSG: Memory.get loc to mem = Some (from, Message.concrete val R))
    (ITV: Interval.mem (from, to) ts):
    concrete_covered loc ts mem.

(** ** Concrete memory increasing *)
Definition concrete_mem_incr (mem1 mem2: Memory.t): Prop :=
  forall loc f t val R,
    Memory.get loc t mem1 = Some (f, Message.concrete val R) ->
    exists f' R',
      View.opt_le R' R /\ Time.le f f' /\ 
      Memory.get loc t mem2 = Some (f', Message.concrete val R') /\
      (forall ts, Interval.mem (f, f') ts -> concrete_covered loc ts mem2).

(** [env steps], describing the program configuration transition in interaction:
    - [MEM_TGT_INCR] and [MEM_SRC_INCR]: increasing of the concrete messages in the target and source levels;
    - [SC_TGT_INCR] and [SC_SRC_INCR]: increasing of the timemap for SC fence in the target and source levels;
    - [CLOSED_SC]: closed timemap for SC
    - [CLOSED_MEM]: memory closed
    - [PRM_TGT_IN] and [PRM_SRC_IN]: Promises are stable during interaction *)

Inductive env_steps (S S': Rss) (p_tgt p_src: Memory.t) :=
| env_steps_intro
    (MEM_TGT_INCR: concrete_mem_incr S.(T_MEM) S'.(T_MEM))
    (MEM_SRC_INCR: concrete_mem_incr S.(S_MEM) S'.(S_MEM))
    (SC_TGT_INCR: TimeMap.le S.(T_SC) S'.(T_SC))
    (SC_SRC_INCR: TimeMap.le S.(S_SC) S'.(S_SC))
    (CLOSED_SC: Memory.closed_timemap S'.(T_SC) S'.(T_MEM))
    (CLOSED_MEM: Memory.closed S'.(T_MEM))
    (PRM_TGT_IN: Memory.le p_tgt S'.(T_MEM))
    (PRM_SRC_IN: Memory.le p_src S'.(S_MEM)).

(** ** Rely condition (Definition 4.2 in paper) **)
(** [Rely] includes:
    - [ENV_STEPS]: transitions guaranteed by the non-preemptive semantics;
    - [INJ_INCR]: message injection increasing;
    - [ATOMIC_COVER]: the sub-memory for atomic variables in the target and source levels
                      must be strictly equal, except for the message views *)
Inductive Rely inj S inj' S' p_tgt p_src lo :=
| Rely_intro
    (ENV_STEPS: env_steps S S' p_tgt p_src)
    (INJ_INCR: incr_inj inj inj')
    (ATOMIC_COVER: Mem_at_eq lo S'.(T_MEM) S'.(S_MEM)).

Definition thrdevt_eq (te1 te2: ThreadEvent.t) :=
  match te1, te2 with
  | ThreadEvent.read loc1 to1 val1 _ ord1, ThreadEvent.read loc2 to2 val2 _ ord2 =>
    loc2 = loc1 /\ to2 = to1 /\ val2 = val1 /\ ord2 = ord1
  | ThreadEvent.write loc1 from1 to1 val1 _ ord1, ThreadEvent.write loc2 from2 to2 val2 _ ord2 =>
    loc2 = loc1 /\ from2 = from1 /\ to2 = to1 /\ val2 = val1 /\ ord2 = ord1
  | ThreadEvent.update loc1 from1 to1 valr1 valw1 _ _ ordr1 ordw1,
    ThreadEvent.update loc2 from2 to2 valr2 valw2 _ _ ordr2 ordw2 =>
    loc2 = loc1 /\ from2 = from1 /\ to2 = to1 /\ valr2 = valr1 /\ valw2 = valw1 /\ ordr2 = ordr1 /\ ordw2 = ordw1
  | _, _ => te2 = te1
  end.

(** ** Simulation on state (definition 4.5 in paper) *)
CoInductive local_sim_state {index: Type} {index_order: index -> index -> Prop} {lang: language}:
  Invariant -> Ordering.LocOrdMap -> Mapping -> @DelaySet index -> bool ->
  Thread.t lang -> Thread.t lang -> Prop :=
| local_sim_state_abort_intro
    I lo inj dset b st_tgt lc_tgt sc_tgt mem_tgt st_src lc_src sc_src mem_src e_src b'
    (NP_STEPS: rtc (@NPAuxThread.tau_step lang lo)
                   (NPAuxThread.mk lang ((Thread.mk lang) st_src lc_src sc_src mem_src) b)
                   (NPAuxThread.mk lang e_src b'))
    (ABORT_STEP: Thread.is_abort e_src lo):
    local_sim_state I lo inj dset b
                    (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                    (Thread.mk lang st_src lc_src sc_src mem_src)
| local_sim_state_tgt_not_prm_consistent_intro
    I lo inj dset b st_tgt lc_tgt sc_tgt mem_tgt st_src lc_src sc_src mem_src
    (NOT_PRM_CONS_T: ~ (Local.promise_consistent lc_tgt)):
    local_sim_state I lo inj dset b
                    (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                    (Thread.mk lang st_src lc_src sc_src mem_src)
| local_sim_state_step_intro
    I lo inj dset b st_tgt lc_tgt sc_tgt mem_tgt st_src lc_src sc_src mem_src
    (STEP_INV: SI inj lo (st_tgt, lc_tgt, mem_tgt) (st_src, lc_src, mem_src) dset)
    (THRD_STEP: 
       forall e_tgt' te pf
         (STEP: Thread.step lo pf te (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) e_tgt'),
    (** Atomic step *)
         (forall (AT_OUT_STEP: ThreadEvent.is_at_or_out_step te),
             exists e_src e_src' inj' te',
               rtc (Thread.na_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src /\
               Thread.program_step te' lo e_src e_src' /\
               incr_inj inj inj' /\
               local_sim_state I lo inj' (@dset_init index) true e_tgt' e_src' /\
               <<PROG_EVENT_EQ: thrdevt_eq te te'>>
         ) /\
    (** Non-atomic step *)
         (forall (NA_STEP: ThreadEvent.is_na_step te),
             exists e_src' dset1 dset2 dset2',
               (** Target write step may add new delayed item in the delayed write set *)
               dset_after_na_step te dset dset1 /\
               (** The source steps will catch up some delayed items in the delayed write set. *)
               (** The definition [na_step_dset] encapsulates
                   - thread step of the source thread;
                   - modification of the delayed write set by the source thread step;
                   - restriction for memory reads, if such memory read reads a location recorded in the delayed write set  *)
               rtc (na_step_dset lo) ((Thread.mk lang st_src lc_src sc_src mem_src), dset1) (e_src', dset2) /\
               (** reducing the indexes of the delayed items in the delayed write set *)
               reduce_dset index_order dset2' dset2 /\ 
               local_sim_state I lo inj dset2' false e_tgt' e_src'
         ) /\
    (** Promise step *)
         (forall (PRM_STEP: (exists loc t, ThreadEvent.is_promising te = Some (loc, t)))
                 (OUT_ATMBLK: b = true)
                 (PROMISE: pf = false),
             exists e_src' inj',
               rtc (Thread.prc_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
               incr_inj inj inj' /\
               local_sim_state I lo inj' (@dset_init index) true e_tgt' e_src'
         ) /\
    (** Cancel step (pf = true) *)
         (forall (PRM_STEP: (exists loc t, ThreadEvent.is_promising te = Some (loc, t)))
                 (PF: pf = true),
             exists e_src',
               rtc (@Thread.pf_promise_step lang) (Thread.mk lang st_src lc_src sc_src mem_src) e_src' /\
               local_sim_state I lo inj dset b e_tgt' e_src')
    )
    (** Rely step *)
    (RELY_STEP: 
       forall (OUT_ATMBLK: b = true),
         (I lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)) /\
         (forall inj' sc_tgt' mem_tgt' sc_src' mem_src'
            (* rely condition holds *)
            (RELY: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                        inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')
                        (Local.promises lc_tgt) (Local.promises lc_src) lo)
            (* invariant for shared state holds after interaction *)
            (INV: I lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')),
             local_sim_state I lo inj' (@dset_init index) true
                             (Thread.mk lang st_tgt lc_tgt sc_tgt' mem_tgt')
                             (Thread.mk lang st_src lc_src sc_src' mem_src')))
    (** Thread done *)
    (THRD_DONE: 
       forall (DONE: Thread.is_done (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)),
       exists e_src inj',
         rtc (na_step_dset lo) ((Thread.mk lang st_src lc_src sc_src mem_src), dset) (e_src, @dset_init index) /\
         Thread.is_done e_src /\
         (incr_inj inj inj') /\
         I lo inj' (Build_Rss sc_tgt mem_tgt (Thread.sc e_src) (Thread.memory e_src)))
    (** Thread abort *)
    (THRD_ABORT: 
       forall (ABORT: Thread.is_abort (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt) lo),
       exists e_src,
         rtc (Thread.na_step lo) (Thread.mk lang st_src lc_src sc_src mem_src) e_src /\
         Thread.is_abort e_src lo)
  :
     local_sim_state I lo inj dset b
                     (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)
                     (Thread.mk lang st_src lc_src sc_src mem_src).

(** ** Message mapping in the initial state [inj_init] *)
Definition inj_init (loc: Loc.t) (t: Time.t) :=
  if Time.eq_dec t Time.bot then Some Time.bot else None.

(** ** Thread-local simulation [local_sim] (Definition 4.4 in paper) *)
(** [local_sim] takes 7 parameters:
    - [index]: the type of the index in the delayed write set;
    - [index_order]: the order of the index, such as '<' for natural numbers;
    - [lang]: the definition of the language of code;
    - [I]: invariant for shared state;
    - [code_t]: target code;
    - [code_s]: source code *)
Record local_sim (index: Type) (index_order: index -> index -> Prop) (lang: language)
       (I: Invariant) (lo: Ordering.LocOrdMap) (code_t code_s: Language.syntax lang): Prop :=
  {
  (** index order is well-founded *)
  index_wf: well_founded index_order;

  (** well-formed invariant *)
  invariant_wf: wf_I I;

  (** invariant holds in initial state *)
  invariant_init: I lo inj_init (Build_Rss TimeMap.bot Memory.init TimeMap.bot Memory.init);
  
  (** local sim state holds in initial state *)
  initial_sim:
    forall (st_tgt: Language.state lang) (fid: Language.fid)
      (INIT_STATE: (Language.init lang) code_t fid = Some st_tgt),
    exists st_src,
      (Language.init lang) code_s fid = Some st_src /\
      @local_sim_state index index_order lang I lo inj_init (@dset_init index) true
                       (Thread.mk lang st_tgt Local.init TimeMap.bot Memory.init)
                       (Thread.mk lang st_src Local.init TimeMap.bot Memory.init)
  }.


Require Import Wf_nat.

Theorem nat_lt_is_well_founded:
  well_founded lt.
Proof.
  eapply lt_wf.
Qed.
