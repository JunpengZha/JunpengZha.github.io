Require Import Basic.
Set Implicit Arguments.

Require Import Event.

Module Language.
  Section Language.
  Definition fid: Type := IdentMap.key.

    Structure t := mk {
      syntax: Type;
      state: Type;

      init: syntax -> fid -> option state;
      is_terminal: state -> Prop; 
      step: forall (e: ProgramEvent.t) (s1: state) (s2: state), Prop;

      (** rtl is deterministic in itself, until it trys to read something from memory pool *)
      deterministic:  
        forall (st st1 st2: state) (e1 e2: ProgramEvent.t)
               (STEP1: step e1 st st1)
               (STEP2: step e2 st st2),
          (e1 = e2 /\ st1 = st2) \/
          (exists or loc val1 val2, e1 = ProgramEvent.read loc val1 or /\ e2 = ProgramEvent.read loc val2 or) \/
          (exists or ow loc valr valw valr', e1 = ProgramEvent.update loc valr valw or ow /\
                                             e2 = ProgramEvent.read loc valr' or) \/
          (exists or ow loc valr valw valr', e2 = ProgramEvent.update loc valr valw or ow /\
                                             e1 = ProgramEvent.read loc valr' or);

      read_abitrary_1:
        forall (st1 st2: state) (val val': Const.t) loc ord
               (READ: step (ProgramEvent.read loc val ord) st1 st2),
        exists st2',
          step (ProgramEvent.read loc val' ord) st1 st2' \/
          (exists valw ordw, step (ProgramEvent.update loc val' valw ord ordw) st1 st2');

      read_abitrary_2:
        forall (st1 st2: state) (val val' valw: Const.t) loc ordr ordw
               (UPDATE: step (ProgramEvent.update loc val valw ordr ordw) st1 st2),
        exists st2',
          step (ProgramEvent.read loc val' ordr) st1 st2' \/
          step (ProgramEvent.update loc val' valw ordr ordw) st1 st2'
    }.
  End Language.  
End Language.

Definition language: Type := Language.t.
