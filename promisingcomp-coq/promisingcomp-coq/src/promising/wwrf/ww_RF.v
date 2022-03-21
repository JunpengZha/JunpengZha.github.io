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

Set Implicit Arguments.

(** * Write-write race freedom *)

(** This file defines the write-write race freedom.

    A program contains write-write race,
    if its execution can reach a promise certified state
    and does a non-atomic write on some location x at this moment
    with an unobserved message on the location x
 
    A program is write-write race free, if it does not contain write-write race
 *)

(** [ww_rf] in this file defines the write-write race freedom in promising semantics (PS2.1)
    and corresponds to the definition in Figure 15 in our paper *)
(** [ww_rf_np] in this file defines the write-write race freedom in the non-preemptive semantics *)

(** ** A configuration contains ww-race *) 
Inductive ww_race: forall (lo: Ordering.LocOrdMap) (c: Configuration.t), Prop :=
| ww_race_intro
    lang lo ths tid sc mem st lc st' loc val val' to from released
    (CTID: IdentMap.find tid ths =
             Some (existT (fun lang : language => Language.state lang) lang st, lc))
    (NA_STATE: (Language.step lang) (ProgramEvent.write loc val Ordering.plain) st st')
    (RC_MSG: Memory.get loc to mem = Some (from, Message.concrete val' released)
             /\ Memory.get loc to (Local.promises lc) = None)
    (WWRC: Time.lt (View.rlx (TView.cur (Local.tview lc)) loc) to):
    ww_race lo (Configuration.mk ths tid sc mem).

(** ** Program contains ww-race on promising semantics *)
Inductive ww_race_p {lang: language}:
  forall (lo: Ordering.LocOrdMap) (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key), Prop :=
| ww_race_p_intro
    lo fs code ctid c c'
    (LOAD: Configuration.init fs code ctid = Some c)
    (STEPS: rtc (Configuration.all_step lo) c c')
    (WWRC: ww_race lo c'):
    ww_race_p lo fs code ctid.

(** ** The ww-race free program on promising semantics *)
Definition ww_rf {lang: language}
           (lo: Ordering.LocOrdMap) (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key) :=
  ~(ww_race_p lo fs code ctid).

(** ** Program contains ww-race on non-preemptive semantics  *)
Inductive ww_race_np {lang: language}:
  forall (lo: Ordering.LocOrdMap) (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key), Prop :=
| ww_race_np_intro
    lo fs code ctid npc npc'
    (NPLOAD: NPConfiguration.init fs code ctid = Some npc)
    (STEPS: rtc (NPConfiguration.all_step lo) npc npc')
    (WWRC: ww_race lo (NPConfiguration.cfg npc')):
    ww_race_np lo fs code ctid.

(** ** The ww-race free program on non-preemptive semantics *)
Definition ww_rf_np {lang: language}
           (lo: Ordering.LocOrdMap) (fs: list Language.fid) (code: Language.syntax lang) (ctid: IdentMap.key) :=
  ~(ww_race_np lo fs code ctid).

Inductive thrd_ww_race {lang: language} {lo: Ordering.LocOrdMap}: Thread.t lang -> Prop :=
| thrd_ww_race_intro
    st lc sc mem st' lc' sc' mem' loc val stw to from val' released e''
    (STEPS: rtc (@Thread.all_step lang lo)
                (@Thread.mk lang st lc sc mem) (@Thread.mk lang st' lc' sc' mem'))
    (WRITE: Language.step lang (ProgramEvent.write loc val Ordering.plain) st' stw)
    (RACE_MSG: Memory.get loc to mem' = Some (from, Message.concrete val' released))
    (NOT_PROM: Memory.get loc to (Local.promises lc') = None)
    (RACE: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (FULFILL: rtc (@Thread.tau_step lang lo)
                  (@Thread.mk lang st' lc' sc' mem') e'')
    (BOT: Local.promises (Thread.local e'') = Memory.bot):
    thrd_ww_race (@Thread.mk lang st lc sc mem).
