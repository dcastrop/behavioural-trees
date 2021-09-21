Require Import mathcomp.ssreflect.all_ssreflect.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Import Prenex Implicits.

Section ETree.
  Variable E : Type -> Type.
  Variable R : Type.
  Variable VAR : Type.
  Inductive gtree : Type :=
  | Vis {A} (e : E A) (k : A -> gtree)
  | Ret (r : R)
  | Fix (k : VAR -> gtree)
  | Var (v : VAR)
  .

End ETree.

Arguments Vis [_ _ _ _] e k.
Arguments Ret [_ _ _] r.
Arguments Fix [_ _ _] k.
Arguments Var [_ _ _] v.
Definition etree E T := forall var, gtree E T var.
Definition etree1 E T := forall var, var -> gtree E T var.

Section Flatten.
  Variable E : Type -> Type.
  Variable R : Type.
  Variable VAR : Type.

  Fixpoint flatten (e : gtree E R (gtree E R VAR)) : gtree E R VAR :=
    match e with
    | Vis _ e k => Vis e (fun x => flatten (k x))
    | Ret r => Ret r
    | Fix k => Fix (fun x => flatten (k (Var x)))
    | Var v => v
    end.

  Fixpoint ntree (n : nat) : Type :=
    match n with
    | 0 => gtree E R VAR
    | n.+1 => gtree E R (ntree n)
    end.

  Fixpoint nvar (n : nat) (v : VAR) : ntree n :=
    match n return ntree n with
    | 0 => Var v
    | m.+1 => Var (nvar m v)
    end.

  Fixpoint flatten_n n : gtree E R (ntree n) -> gtree E R VAR :=
    (fix traverse e :=
       match e with
       | Vis _ e k => Vis e (fun x => traverse (k x))
       | Ret r => Ret r
       | Fix k => Fix (fun x => traverse (k (nvar _ x)))
       | Var v => match n return ntree n -> gtree E R VAR with
                  | 0 => fun v => v
                  | m.+1 => fun v => flatten_n v
                  end v
       end).
End Flatten.

Arguments nvar [E R VAR] n v.


Section Unroll.
  Variable E : Type -> Type.
  Variable R : Type.
  Variable VAR : Type.

  Fixpoint unroll1 (e : gtree E R (gtree E R VAR)) : gtree E R VAR :=
    match e with
    | Vis _ e k => Vis e (fun x => unroll1 (k x))
    | Ret r => Ret r
    | Fix k => flatten (k (Fix (fun x => unroll1 (k (Var x)))))
    | Var v => v
    end.

End Unroll.

Definition unroll {E R} (e : etree E R) : etree E R := fun _ => unroll1 (e _).

Module Examples.

Inductive LTy : Type -> Type :=
| LSend A : LTy A
| LRecv A : LTy A.

Definition always_send1 : etree LTy unit :=
  fun _ =>
    Fix (fun k =>
           Vis (LSend nat) (fun _ => Var k)).

Eval compute in (unroll always_send1 _).
End Examples.

Section StateM.
  Variable E : Type -> Type.
  Variable R : Type.
  Variable VAR : Type.

  (* QUESTION: Does it need to be finite? *)
  (* Definition has_next (l : etree E R) : Type := *)
  (*     match unroll l VAR with *)
  (*     | Vis A e k => A *)
  (*     | _ => False *)
  (*     end. *)

  (* Definition next_type (l : etree E R) : Type := *)
  (*     match unroll l VAR with *)
  (*     | Vis A e k => A *)
  (*     | _ => False *)
  (*     end. *)

  (* Definition run_event (l : etree E R) := *)
  (*   match unroll l VAR *)
  (*         as U *)
  (*         return match U with *)
  (*                | Vis A _ _ => E A *)
  (*                | _ => True *)
  (*                end *)
  (*   with *)
  (*     | Vis A e k => e *)
  (*     | _ => I *)
  (*     end. *)

  (* Definition next_type (l : etree E R) : E (next_type l) *)


  (* Definition swap_v (f : forall V, option ({A & (E A * (A -> gtree E R V))%type})) *)
  (*   : option ({A & (E A * (A -> etree E R))%type}) *)
  (*   := *)
  (*     match f _ with *)
  (*     | None => None *)
  (*     | Some (existT _ (e, k)) => Some (existT _ _ (e, fun x => fun _ => k x))  *)
  (*     end. *)

  (* Definition next_event (l : etree E R) : option (E (next_type l)) *)
  (*   := match unroll l True with *)
  (*      | Vis _ e _ => Some e *)
  (*      | _ => None *)
  (*      end. *)

End StateM.

Module ITree.
  Section Syntax.
    Context (E : Type -> Type).
    Context (R : Type).

    Inductive itreeF (itree : Type) : Type :=
    | Vis {A} (e : E A) (k : A -> itree)
    | Tau (i : itree)
    | Ret (r : R)
    .

    Set Primitive Projections.
    CoInductive itree := go { observe : itreeF itree }.
    Unset Primitive Projections.
  End Syntax.

  Arguments Vis [E R itree A] e k.
  Arguments Tau [E R itree] i.
  Arguments Ret [E R itree] r.

  Section Peek.
    Context (E : Type -> Type).
    Context (R : Type).

    Inductive etree : Type :=
    | eVis {A} (e : E A) (k : A -> etree)
    | eRec (i : itree E R)
    | eRet (r : R)
    .
    Arguments eVis [_] e k.
    Arguments eRec i : clear implicits.
    Arguments eRet r : clear implicits.


    Definition run (i : itree E R) : itreeF E R (itree E R) :=
      match observe i with
      | Vis _ e k => Vis e k
      | Tau t => observe t
      | Ret r => Ret r
      end.

    Definition event_type (i : itree E R) : Type :=
      match run i with
      | Vis A _ _ => A
      | Tau t => False
      | Ret r => False
      end.

    Definition run_cont (i : itree E R) : event_type i -> itree E R
      :=
        match run i as ri
              return match ri with
                     | Vis A _ _ => A
                     | Tau _ => False
                     | Ret _ => False
                     end -> itree E R
        with
      | Vis B e k => k
      | Tau _ => fun x => match x with end
      | Ret _ => fun x => match x with end
      end.

    (* Fixpoint observe_n (n : nat) (i : itree E R) : etree := *)
    (*   match n with *)
    (*   | 0 => eRec i *)
    (*   | m.+1 => *)
    (*     match observe i with *)
    (*     | Vis _ e k => eVis e (fun x => observe_n m (k x)) *)
    (*     | Tau t => observe_n m t *)
    (*     | Ret r => eRet r *)
    (*     end *)
    (*   end. *)

    (* Fixpoint unroll (n : nat) (i : etree) : etree := *)
    (*     match i with *)
    (*     | eVis _ e k => eVis e (fun x => unroll n (k x)) *)
    (*     | eRec t => observe_n n t *)
    (*     | eRet r => eRet r *)
    (*     end. *)
  End Peek.
  Arguments run_cont [E R] i _.

  Section Constraint.
    Variable P : Type.

    Inductive LTy (A : Type) := | LSend (p : P) | LRecv (p : P).

    Inductive Proc : Type -> Type :=
    | Send (p : P) {A} (x : A) : Proc unit
    | Recv (p : P) A : Proc A.

    Definition type_of {A} (p : Proc A) : Type :=
      match p with
      | Send _ A _ => A
      | Recv _ A => A
      end.

    Definition erase {A} (l : Proc A) : LTy (type_of l) :=
      match l with
      | Send p A _ => LSend A p
      | Recv p A => LRecv A p
      end.

    Definition down {A} (l : Proc A) : A -> type_of l
      := match l in Proc A return A -> type_of l with
         | Send _ _ x => fun _ => x
         | Recv _ _ => fun x => x
         end.

    Definition up {A} (l : Proc A) : type_of l -> A
      := match l in Proc A return type_of l -> A with
         | Send _ _ _ => fun _ => tt
         | Recv _ _ => fun x => x
         end.

    CoFixpoint erasure {A} (t : itree Proc A) : itree LTy A :=
      go match observe t with
         | Vis _ e k => Vis (erase e) (fun x => erasure (k (up x)))
         | Tau k => Tau (erasure k)
         | Ret x => Ret x
         end.

    Inductive event : Type -> Type :=
    | p_snd (p : P) (A : Type) (x : A) : event unit
    | p_rcv (p : P) (A : Type) : event A.

    Definition ety {A} (e : event A) : Type :=
      match e with
      | p_snd _ A _ => A
      | p_rcv _ A => A
      end.

    Definition ev_lt {A} (e : event A) : LTy (ety e)
      := match e with
         | p_snd p A _ => LSend A p
         | p_rcv p A => LRecv A p
         end.

    Definition cont {A} (e : event A) : A -> ety e
      :=
      match e in event A return A -> ety e with
      | p_snd _ _ x => fun=>x
      | p_rcv _ _ => fun x=>x
      end.

    Definition recv_type (l : itreeF LTy Set (itree LTy Set)) : Type :=
      match l with
      | Vis A (LRecv p) _ => A
      | _ => False
      end.

    Definition run_recv (l : itree LTy Set) : recv_type (run l) -> itree LTy Set :=
      match run l
            as rl
            return recv_type rl -> itree LTy Set
      with
      | Vis _ (LRecv _) k => fun x => k x
      | _ => fun f => match f with end
      end.

    (** no Tau so far **)
    Inductive procF (proc : itree LTy Set -> Type) : itree LTy Set -> Type :=
    | p_event {A} (e : event A) kl l (_ : Vis (ev_lt e) kl = run l)
      : (forall (x : A), proc (kl (cont e x))) -> procF proc l
    (* | p_tau {l} : procF proc l -> procF proc l *)
    | p_end (A : Set) l2 (_ : Ret A = run l2) : A -> procF proc l2.

    Arguments p_event [proc A] e {kl l} _ _.
    Arguments p_end [proc A l2] _ _.

    CoInductive proc (l : itree LTy Set) : Type :=
      goP { observeP : procF proc l }.

    Definition part_of (l : itreeF LTy Set (itree LTy Set)) :=
      match l with
      | Vis _ (LSend p') _ => {p | p = p'}
      | Vis _ (LRecv p') _ => {p | p = p'}
      | _ => False
      end.

    Definition send_type (l : itreeF LTy Set (itree LTy Set)) :=
      match l with
      | Vis A (LSend p) _ => A
      | _ => False
      end.

    Inductive ret_lty (l : itree LTy Set) : Type := | lty_sing.

    Definition part_send (l : itreeF LTy Set (itree LTy Set)) :=
      match l with
      | Vis _ (LSend p') _ => {p | p = p'}
      | _ => False
      end.

    Definition part_recv (l : itreeF LTy Set (itree LTy Set)) : Type :=
      match l with
      | Vis _ (LRecv p') _ => {p | p = p'}
      | _ => False
      end.

    Lemma rename_part T (e : P -> LTy T) p k (l : itree LTy Set) :
      Vis (e p) k = run l ->
      forall pp : {p' | p' = p},
      Vis (e (sval pp)) k = run l.
    Proof. by move=>EQ [p' /=->]. Qed.


    (* Definition send (l : itree LTy Set) : *)
    (*   part_send (run l) -> send_type (run l) -> procF ret_lty l  *)
    (*   := match run l as rl return *)
    (*            rl = run l -> *)
    (*                 part_send rl -> *)
    (*                 send_type rl -> *)
    (*                 procF ret_lty l *)
    (*      with *)
    (*           | Vis _ (LSend _) k => *)
    (*             fun EQ pp x => *)
    (*               let EQ' := rename_part EQ pp in *)
    (*               p_event (p_snd (sval pp) x) EQ' (fun=>lty_sing (k x)) *)
    (*           | _ => fun _ F=>match F with end *)
    (*      end erefl. *)

    Definition send_lty (l : itreeF LTy Set (itree LTy Set)) :
      part_send l -> send_type l -> itree LTy Set
      := match l as rl return
               part_send rl ->
               send_type rl ->
               itree LTy Set
         with
         | Vis _ (LSend _) k => fun _ x => k x
         | _ => fun _ F=>match F with end
         end.

    Definition recv_lty (l : itreeF LTy Set (itree LTy Set)) :
      part_recv l -> recv_type l -> itree LTy Set
      := match l as rl return
               part_recv rl ->
               recv_type rl ->
               itree LTy Set
         with
         | Vis _ (LRecv _) k => fun _ x => k x
         | _ => fun _ F=>match F with end
         end.

    Definition _send (l : itree LTy Set)  :
      forall p x, proc (@send_lty (run l) p x) -> proc l :=
      match run l as rl return
            rl = run l ->
            forall (p : part_send rl)
                   (x : send_type rl),
              proc (send_lty p x) ->
              proc l
      with
      | Vis _ (LSend _) k =>
        fun EQ pp x K => let EQ' := rename_part EQ pp in
                         goP (p_event (p_snd (sval pp) x) EQ' (fun=>K))
      | _ => fun _ F=>match F with end
      end erefl.

    Definition _cont_type (l : itreeF LTy Set (itree LTy Set)) l0 :=
      match l with
      | Vis T (LSend p) k => {p0 | p0 = p} -> forall x : T, {l' & proc l' -> proc l0}
      (* | Vis T (LRecv p) k => {p0 | p0 = p} -> {k' & (forall (x : T), proc (k' x)) -> proc l0} *)
      | _ => False -> proc l0
      end.

    Definition _step (l : itree LTy Set) : _cont_type (run l) l
      :=
        match run l as rl
              return
              rl = run l ->
              _cont_type rl l
        with
        | Vis T (LSend p) k => fun EQ ep x =>
                                 let EQ' := rename_part EQ ep in
                                 existT (fun l' => proc l' -> proc l) (k x) (fun (kp : proc (k x)) =>
                                               goP (p_event (p_snd (sval ep) x) EQ' (fun=> kp)))
        | _ => fun _ F => match F with end
        end erefl.

    Definition _seq l l' (f : proc l' -> proc l) : _cont_type (run l') l
      := match run l' as rl
               return
               _cont_type rl l' ->
               _cont_type rl l

         with
         | Vis _ (LSend _) kl =>
           fun k p x =>
             let r := k p x in
             existT (fun l1 => proc l1 -> proc l)
                    (projT1 r)
                    (fun kp => f (projT2 r kp))
              | _ => fun _ F => match F with end
              end (_step l').

      Variable p : P.

    (* CoFixpoint lt : itree LTy Set := *)
    (*   go (Vis (LSend nat p) (fun=> go (Vis (LSend bool p) (fun=>lt)))). *)

    CoFixpoint lt : itree LTy Set :=
      go (Vis (LSend nat p) (fun=> go (Vis (LSend bool p) (fun=>lt)))).

    CoFixpoint prog1 : proc lt :=
      projT2 (_seq (projT2 (_step lt (exist _ p erefl) 1)) (exist _ p erefl) true) prog1.

    (* Extraction is awful*)
    (* I need to go back to the original idea, a*)

  End Constraint.
    Require Extraction.
    Require Import ExtrOcamlIntConv.

    Extraction Inline _seq.
    Extraction Inline _step.
    Extraction Inline run.
    Extraction Inline projT1.
    Extraction Inline projT2.
    Recursive Extraction prog1.



    Definition _run_type (l : itree LTy Set) : _cont_type (run l) (itree LTy Set)
      := match run l as rl return _cont_type rl (itree LTy Set) with
         | Vis T (LSend p) k => fun _ x => k x
         | _ => fun F => match F with end
         end.

    Definition _run_seq (l : itree LTy Set) : _cont_type (run l) ()
      := match run l as rl return _cont_type rl (itree LTy Set) with
         | Vis T (LSend p) k => fun _ x => k x
         | _ => fun F => match F with end
         end.

    Definition seq l (m : {l' & proc l' -> proc l}) : _cont_type (run (projT1 m)) -> proc l.

    Definition send (l : itree LTy Set)
               (p : part_send (run l)) (x : send_type (run l))
      : {l' & proc l' -> proc l}
      := existT _ (@send_lty (run l) p x) (@_send l p x).

    Definition recv (l : itree LTy Set) :
      forall p, (forall x, proc (@recv_lty (run l) p x)) -> proc l
      := match run l as rl return
               rl = run l ->
               forall p, (forall x, proc (@recv_lty rl p x)) -> proc l
         with
         | Vis T (LRecv _) k =>
           fun EQ pp K => let EQ' := rename_part EQ pp in
                          goP (p_event (p_rcv (sval pp) T) EQ' K)
         | _ => fun _ F=>match F with end
         end erefl.

    Definition comp l
               (f1 : {l1 & proc l1 -> proc l})
               (f2 : {l2 & proc l2 -> proc (projT1 f1)}) :
      {l2 & proc l2 -> proc l} :=
      existT (fun l2 => proc l2 -> proc l) (projT1 f2) (fun f => projT2 f1 (projT2 f2 f)).

    (* Sequencing has to "peek" into the continuation of l' *)
    Definition seq l (m : {l' & proc l' -> proc l}) (f : proc (projT1 m)) : proc l
      := projT2 m f.
    Arguments seq [l] m f.
    About comp.
    Arguments comp [l] f1 f2.

    Definition inact (A : Set) (x : A) : proc (go (Ret A))
      := goP (p_end (erefl (run (go (Ret A)))) x).

    CoFixpoint lt1 : itree LTy Set :=
      go (Vis (LSend (nat + bool) p)
              (fun nb =>
                 match nb with
                 | inl _ => go (Ret nat)
                 | inr _ => lt1
                 end)).

    CoFixpoint prog1 (n : nat) : proc lt1 :=
      if n > 27 then
        seq (@send lt1 (exist _ p erefl) (inl n)) (inact n)
      else
        seq (@send lt1 (exist _ p erefl) (inl n)) (inact n)


  End Constraint.
    Require Extraction.
    Require Import ExtrOcamlIntConv.

    Recursive Extraction prog1.


    Definition bnd_type (l : itreeF LTy Set (itree LTy Set)) R :=
      match l with
      | Vis _ (LSend _) _ => part_send l -> send_type l -> R
      | Vis _ (LRecv _) _ => part_recv l -> R
      | Ret T => T -> R
      | Tau _ => False
      end.

    Definition continuation (l : itree LTy Set) (e : procF ret_lty l) : Type.

      refine (match e in procF _ l
              with
              | p_event T e kl l EQ K =>
                _
                (* match esym EQ in *)
                (*       run i Vis _ (LSend p A) k *)
                (*       return *)
              | _ => _
              end)=>/=.

    Definition bind (l : itree LTy Set) (e : procF ret_lty l) :
      bnd_type (run l) (proc l) -> proc l.
      refine (match e in procF _ l
                    return
                    bnd_type (run l) (proc l) -> proc l
              with
              | p_event T e kl l EQ K =>
                _
                (* match esym EQ in *)
                (*       run i Vis _ (LSend p A) k *)
                (*       return *)
              | _ => _
              end)=>/=.

      refine (match e in event T return
                    forall (kl : ety e -> itree LTy Set)
                           (EQ : Vis (ev_lt e) kl = run l)
                           (K : forall x : T, ret_lty (kl (cont e x))),
                           bnd_type (run l) (proc l) -> proc l
              with
              | p_snd p T x => fun kl EQ _ =>
                                 match EQ
                                       in (_ = i)
                                       return bnd_type i (proc l) -> proc l
                                 with
                                 | erefl => fun F => F (exist _ _ erefl) x
                                 end
              | p_rcv p _ => fun kl EQ _ =>
                                 match EQ
                                       in (_ = i)
                                       return bnd_type i (proc l) -> proc l
                                 with
                                 | erefl => _
                                 end
              end kl EQ K).




    Definition run_send (l : itree LTy Set) : send_type l -> itree LTy Set :=
      match run l
            as rl
            return
            match rl with
            | Vis A (LSend _) _ => A
            | _ => False
            end -> itree LTy Set
      with
      | Vis _ (LSend _) k => fun x => k x
      | _ => fun f => match f with end
      end.


    (** Examples **)
    Variable p : P.

    CoFixpoint lt1 : itree LTy Set :=
      go (Vis (LSend nat p) (fun _ => lt1)).

    CoFixpoint always_send1 : proc lt1 :=
      goP (p_event (p_snd p 1) (erefl (run lt1)) (fun=>always_send1)).

    Definition always_send2 : proc lt1 :=
      goP (p_event (p_snd p 2) (erefl (run lt1)) (fun=>always_send1)).

    CoFixpoint always_send3 : proc lt1 :=
      goP (p_event (p_snd p 1) (erefl (run lt1))
          (fun=>goP (
                p_event (p_snd p 2) (erefl (run lt1)) (fun=>always_send3)))).

    CoFixpoint ping_pong_lt : itree LTy Set :=
      go (Vis (LSend nat p)
              (fun=>go (Vis (LRecv nat p)
                            (fun n =>
                               if n >= 10
                               then go (Ret nat)
                               else ping_pong_lt)))).

    CoFixpoint ping_pong (n : nat) : proc ping_pong_lt :=
      goP (p_event (p_snd p n) (erefl (run ping_pong_lt))
                  (fun=>goP (p_event (p_rcv p nat)
                               (erefl (run (run_cont ping_pong_lt n)))
                               (fun m : nat =>
                                  match
                                    ifP (9 < m) _ _ in (if_spec _ _ _ _ _ y)
                                    return proc y
                                  with
                                  | IfSpecTrue x => goP (p_end (erefl (run (go (Ret nat)))) m)
                                  | IfSpecFalse x => ping_pong m.+1
                                  end
                               )
          ))).

  End Constraint.
    Require Extraction.
    Require Import ExtrOcamlIntConv.


    Extraction Implicit p_send [proc A k1 l2].
    Extraction Implicit p_recv [proc A k1 l2].
    Recursive Extraction ping_pong.
    (* Inductive procF (proc : itree LTy Set -> Type) : itree LTy Set -> Type := *)
    (* | p_send (p : P) (A : Type) (x : A) k1 l2 *)
    (*          (_ : Vis (LSend A p) k1 = run l2) : proc (k1 x) -> procF proc l2 *)
    (* | p_recv (p : P) (A : Type) k1 l2 *)
    (*          (_ : Vis (LRecv A p) k1 = run l2) : (forall x, proc (k1 x)) -> procF proc l2 *)
    (* | p_end (A : Set) l2 *)
    (*          (_ : Ret A = run l2) : A -> procF proc l2 *)


End ITree.
