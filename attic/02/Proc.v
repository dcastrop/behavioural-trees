Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Import Prenex Implicits.

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

    Inductive ftree := fgo { fobserve : itreeF ftree }.
  End Syntax.

  Arguments Vis {E R itree A} e k.
  Arguments Tau {E R itree} i.
  Arguments Ret {E R itree} r.

  Section Peek.
    Context (E : Type -> Type).
    Context (R : Type).

  Definition inf_run (i : itree E R) : itreeF E R (itree E R) :=
    match observe i with
    | Vis _ e k => Vis e k
    | Tau t => observe t
    | Ret r => Ret r
    end.

  Definition fin_run (i : ftree E R) : itreeF E R (ftree E R) :=
    fobserve i.

  End Peek.

  Module LocalTypes.
    Definition P := nat.

    Inductive LTy (A : Type) := | LSend (p : P) | LRecv (p : P).

    Record class (T : Type) :=
      Class {
          t_run : T -> itreeF LTy Type T;
          mk_send : forall A, P -> (A -> T) -> T;
          mk_recv : forall A, P -> (A -> T) -> T;
          mk_end : Type -> T;
          mk_impossible : Type -> T;
        }.

    Structure type : Type := Pack { tree :> Type; class_of : class tree }.
    Definition run (t : type) : tree t -> itreeF LTy Type (tree t)
      := let 'Pack _ (Class the_op _ _ _ _) := t in the_op.
    Definition send (t : type) : forall A, P -> (A -> tree t) -> tree t
      := let 'Pack _ (Class _ the_op _ _ _) := t in the_op.
    Definition recv (t : type) : forall A, P -> (A -> tree t) -> tree t
      := let 'Pack _ (Class _ _ the_op _ _) := t in the_op.
    Definition stop (t : type) : Type -> tree t
      := let 'Pack _ (Class _ _ _ the_op _) := t in the_op.
    Definition impossible (t : type) : Type -> tree t
      := let 'Pack _ (Class _ _ _ _ the_op) := t in the_op.

    Definition inf_ltyC : class (itree LTy Type) :=
      {|
        t_run := @inf_run LTy Type;
        mk_impossible := fun _ => cofix spin := go (Tau spin);
        mk_send := fun A p f => go (Vis (LSend A p) f);
        mk_recv := fun A p f => go (Vis (LRecv A p) f);
        mk_end := fun (x : Type) => go (Ret x);
      |}.

    Canonical Structure inf_lty : type := @Pack (itree LTy Type) inf_ltyC.

    Definition fin_ltyC : class (ftree LTy Type) :=
      {|
        t_run := @fin_run LTy Type;
        mk_impossible := fun x => fgo (Tau (fgo (Ret x)));
        mk_send := fun A p f => fgo (Vis (LSend A p) f);
        mk_recv := fun A p f => fgo (Vis (LRecv A p) f);
        mk_end := fun (x : Type) => fgo (Ret x);
      |}.

    Canonical Structure fin_lty : type := @Pack (ftree LTy Type) fin_ltyC.

    Arguments send [t] A _ _.
    Arguments recv [t] A _ _.
    Arguments stop [t] A.
    Arguments impossible [t] A.

    Declare Scope lty_scope.
    Delimit Scope lty_scope with lty.
    Notation "X '<-' p '!!' e ';;' K" :=
      (send e p (fun X => K))
        (at level 60, right associativity) : lty_scope.
    Notation "X '@@' P '<-' p '!!' e ';;' K" :=
      (send e p (fun X =>
                   match X with
                   | P => K
                   | _ => impossible unit
                   end))
        (at level 60, P pattern, right associativity) : lty_scope.
    Notation "X '<-' p '??' e ';;' K" :=
      (recv e p (fun X => K))
        (at level 60, right associativity) : lty_scope.
    Notation "X '@@' P '<-' p '??' e ';;' K" :=
      (recv e p (fun X =>
                   match X with
                   | P => K
                   | _ => impossible unit
                   end))
        (at level 60, P pattern, right associativity) : lty_scope.

    Definition lty := type.
    About run.
  End LocalTypes.

  Section WellTypedProcesses.
    Import LocalTypes.

    Variable E : Type -> Type.
    Variable T : lty.

    Inductive ev (l : T) : forall A, (A -> T) -> Type :=
    | E_send {A} x p k (H : Vis (LSend A p) k = run l) : @ev l unit (fun _ => k x)
    | E_recv {A} p k (H : Vis (LRecv A p) k = run l) : @ev l A k
    | E_run {A} (e : E A) : @ev l A (fun _ =>l).
    Arguments E_send & [l A] x p [k] H.
    Arguments E_recv & [l A] p [k] H.
    Arguments E_run & [l A] e.

    Inductive procF (proc : T -> Type) : T -> Type :=
    | P_ev {A k l} (e : @ev l A k) (kp : forall x, proc (k x)) : procF proc l
    | P_call {l1} (k : proc l1) {l2} (_ : run l1 = run l2) : procF proc l2
    | P_end {A : Type} (x : A) l (_ : Ret A = run l) : procF proc l.
    Arguments P_ev [proc A k] & {l} e kp.
    Arguments P_call [proc l1] k & {l2} H.
    Arguments P_end [proc A] x & [l] _.

    CoInductive proc (l : T) : Type :=
      Go { observeP : procF proc l }.
    Arguments Go & [l].

    Definition p_send {A} (x : A) (p : P)
               l kl (H : Vis (LSend A p) kl = run l)
               (k : unit -> proc (kl x))
      : proc l := Go (P_ev (E_send x p H) k).
    Arguments p_send [A] x p & [l kl] H.

    Definition p_recv {A} (p : P)
               l kl (H : Vis (LRecv A p) kl = run l)
               (k : forall x, proc (kl x))
      : proc l := Go (P_ev (E_recv p H) k).
    Arguments p_recv [A] p & [l kl] H k.

    Definition p_call {l1} (k : proc l1) {l2} (H : run l1 = run l2) : proc l2
      := Go (P_call k H).
    Arguments p_call [l1] k & {l2} H.

    Definition pure [A : Type] (x : A) l (H : Ret A = run l) : proc l :=
      Go (P_end x H).
    Arguments pure [A] x & [l] _.

    Definition ifB {l1 l2} (b : bool) (p1 : proc l1) (p2 : proc l2)
      : proc (if b then l1 else l2)
      := match b as b0 return proc (if b0 then _ else _)
         with
         | true => p1
         | false => p2
         end.
    Arguments ifB & [l1 l2] b p1 p2.
  End WellTypedProcesses.

  Section Testing.
    Import LocalTypes.
    Definition runs_ok (l : itree LTy Type) : Prop :=
      match inf_run l with
      | Vis _ _ _ => True
      | Ret _ => True
      | Tau _ => False
      end.

    Lemma wrap_unwrap (t : itree LTy Type) (H : runs_ok t) :
      inf_run t = inf_run (go (inf_run t)).
    Proof. by move: H; rewrite /runs_ok; case: (inf_run t). Qed.

    Variable E : Type -> Type.

    CoFixpoint run_lty {l} (P : proc E l) : proc E (go (run l)).
    move: P => /observeP; case.
    - move=>A k {}l []/=.
      + move=> {}A x p {}k <- kp; apply/Go/(P_ev _ kp).
        by apply/(E_send (l := go (Vis (LSend A p) k)) E x Logic.eq_refl).
      + move=> {}A   p {}k <- kp; apply/Go/(P_ev _ kp).
        by apply/(E_recv (l := go (Vis (LRecv A p) k)) E   Logic.eq_refl).
      + move=> {k}A e kp; apply/Go/(P_ev _ (fun x => run_lty _ (kp x))).
        by apply/(E_run _ e).
    - move=>{l}l1 pl l2 Heq.
      move: (run_lty _ pl)=>{}pl.
      apply/Go/(P_call E pl).
      by rewrite Heq.
    - move=>{}A x {}l Heq.
      apply/Go/(P_end E (@proc E inf_lty) x).
      by rewrite -Heq.
    Defined.

  End Testing.

  Arguments E_send & [E T l A] x p [k] H.
  Arguments E_recv & [E T l A] p [k] H.
  Arguments E_run & [E T l A] e.
  Arguments P_ev [E T proc A k] & [l] e kp.
  Arguments P_end [E T proc A] x & [l] _.
  Arguments Go & [E T l].
  Arguments p_send [E T A] x p & [l kl] H k.
  Arguments p_recv [E T A] p & [l kl] H k.
  Arguments p_call [E T l1] k & {l2} H.
  Arguments pure [E T A] x & [l] _.
  Arguments ifB & [E T l1 l2] b p1 p2.

  Declare Scope expr_scope.
  Bind Scope expr_scope with proc.
  Delimit Scope expr_scope with expr.
  Notation "'RET' x" := (pure x Logic.eq_refl) (at level 60) : expr_scope.
  Notation "'CALL' x" := (p_call x Logic.eq_refl) (at level 60) : expr_scope.
  Notation "p '!' e ';;' K" :=
    (p_send e p Logic.eq_refl (fun _ =>K))
      (right associativity, at level 60) : expr_scope.
  Notation "x '<-' p '?' ';;' K" :=
    (p_recv p Logic.eq_refl (fun x => K))
      (right associativity, at level 60) : expr_scope.
  Notation "'if' b 'then' p1 'else' p2" := (ifB b p1 p2) : expr_scope.
End ITree.

Module EraseExtract.
  Require Extraction.
  Require Import ExtrOcamlBigIntConv.
  Import ITree.
  Extraction Implicit ev [l].
  Extraction Implicit E_send [E A l k H].
  Extraction Implicit E_recv [E A l k H].
  Extraction Implicit P_ev [E A l k].
  Extraction Implicit P_end [E A l].
  Extraction Implicit ifB [E l1 l2].
  Extraction Inline ifB.
  Extraction Implicit p_send [E l kl].
  Extraction Inline p_send.
  Extraction Implicit p_recv [E l kl].
  Extraction Inline p_recv.
  Extraction Implicit p_recv [E l kl].
  Extraction Inline pure.
  Extraction Implicit Go [E l].
End EraseExtract.

Module Examples.
  Import ITree.
  Import LocalTypes.
  Definition p := 0.
  Open Scope lty_scope.
  CoFixpoint example : itree LTy Type :=
    n <- p !! nat ;;
      match n  with
      | 0 => stop bool
      | m.+1 => b <- p !! bool ;; example
      end.

  Fixpoint fexample (r : nat) : ftree LTy Type :=
    n <- p !! nat ;;
      match n with
      | 0 => stop bool
      | m.+1 => b <- p !! bool ;;
                  match r with
                  | 0 => stop nat
                  | r.+1 => fexample r
                  end
      end.
  Close Scope lty_scope.

  Open Scope expr_scope.
  Definition pure_proc := proc (fun _ => False).

  Fail CoFixpoint prog1 : pure_proc example
    := p ! 1 ;; p ! true ;; RET 1.

  Fail CoFixpoint prog1 : pure_proc example
    := p ! 1 ;; p ! true ;; p ! true ;; RET 1.

  Fail CoFixpoint prog1 : pure_proc example
    := p ! false ;; p ! 1 ;; p ! true ;; RET 1.

  CoFixpoint prog1 : pure_proc example
    := p ! 1 ;; p ! true ;; prog1.

  Fail CoFixpoint prog2 : pure_proc example
    := p ! 1 ;; p ! 1 ;; p ! true ;; p ! false ;; prog2.
  CoFixpoint prog2 : pure_proc example
    := p ! 1 ;; p ! true ;; p ! 2 ;; p ! false ;; prog2.
  Definition prog3 : pure_proc example
    := p ! 1 ;;
         (cofix cont :=
            p ! true ;; p ! 2 ;; cont).
  CoFixpoint prog4 (n : nat) : pure_proc example :=
    match n with
    | 0 => p ! 0 ;; RET true
    | m.+1 => p ! m.+1 ;; p ! false ;; prog4 m
    end.
  CoFixpoint prog5 (n : nat) : pure_proc example :=
    p ! n ;;
      match n with
      | 0 => RET true
      | m.+1 => p ! false ;; prog5 m
      end.

  Open Scope lty_scope.
  CoFixpoint example2 : itree LTy Type :=
    n <- p ?? nat ;;
      match n with
      | 0 => stop bool
      | m.+1 => b <- p !! bool ;; example2
      end.
  CoFixpoint prog21 : pure_proc example2 :=
    n <- p ? ;;
      match n with
      | 0 => RET true
      | m.+1 => p ! false ;; prog21
      end.
  Close Scope expr_scope.

  Open Scope lty_scope.
  CoFixpoint example3 : itree LTy Type :=
    n <- p ?? nat ;;
      if n > 27
      then stop bool
      else b <- p !! bool ;; example3.
  Close Scope lty_scope.

  Open Scope expr_scope.
  CoFixpoint prog31 : pure_proc example3
    := n <- p ? ;;
         if (n > 27)
         then RET true
         else p ! false ;; prog31.
  CoFixpoint prog32 : pure_proc example3
    := n <- p ? ;;
         if (n > 27)
         then RET true
         else p ! false ;;
                match (n > 28) with
                | true => prog31
                | false => prog32
                end.
  Close Scope expr_scope.
End Examples.

Module IOProc.
  Variant IO (A : Type) : Type :=
  | Read : IO A
  | Write (x : A) : IO A.

  Import ITree.

  Definition io_proc := proc IO.

  Notation "'write' e ';;' K" :=
    (Go (P_ev (E_run (Write e)) (fun _ => K)))
      (right associativity, at level 60) : expr_scope.
  Notation "X '<-' 'read' T ';;' K" :=
    (Go (P_ev (E_run (Read T)) (fun (X : T) => K)))
      (right associativity, at level 60) : expr_scope.
End IOProc.

Module PingPong.
  Import ITree.
  Import IOProc.
  Import LocalTypes.

  Open Scope lty_scope.
  CoFixpoint pp_client (p : P) : itree LTy Type :=
    n <- p !! option nat ;;
      match n with
      | None => stop unit
      | Some n => _ <- p ?? nat ;; pp_client p
      end.

  CoFixpoint pp_server (p : P) : itree LTy Type :=
    n <- p ?? option nat ;;
      match n with
      | None => stop unit
      | Some n => _ <- p !! nat ;; pp_server p
      end.

  Inductive PingTy := Ping (n : nat) | Close.

  Open Scope expr_scope.
  CoFixpoint some_client (p : P) : io_proc (pp_client p) :=
    n <- read PingTy ;;
    match n with
    | Ping n =>
      p ! Some n ;;
      x <- p ? ;;
      write (Ping n);;
      some_client p
    | Close => p ! None ;; write Close ;; RET tt
    end.

  Fixpoint weird_client (n : nat) (p : P) : io_proc (pp_client p) :=
    match n with
    | 0 => some_client p
    | m.+1 =>
      p ! Some m ;;
      _ <- p ? ;;
      weird_client m p
    end.

  Definition weirder_client (n : nat) (p : P) : io_proc (pp_client p) :=
      p ! Some 0 ;;
        cofix repeat_cli :=
          n <- p ? ;;
            match n < 42 with
            | true => p ! None ;; RET tt
            | false => p ! Some n ;;
                         repeat_cli
            end.

  CoFixpoint some_server (p : P) : io_proc (pp_server p) :=
    n <- p ? ;;
    match n with
    | Some x =>
      p ! x ;;
      some_server p
    | None => RET tt
    end.
  Close Scope expr_scope.

  Fixpoint fin_client (n : nat) (p : P) : ftree LTy Type :=
    match n with
    | 0    => x @@ None <- p !! option nat;; stop unit
    | m.+1 => x <- p !! option nat;;
                match x with
                | None => stop unit
                | Some _ => x <- p ?? nat;;
                              fin_client m p
                end
    end.

  (** One annoyance of protocols like below is that they MUST inspect
   * [n], othewise the protocol will not reduce. E.g. it is clear that
   * sending None ends the protocol. But due to [fix], Coq will not know
   * that unless it is applied to a constructor
   *)
  Definition fin_client_alt (n : nat) (p : P) : ftree LTy Type :=
    x  <- p !! option nat;;
       (fix rec (x : option nat) (n : nat) :=
          match x with
          | None => stop unit
          | Some _ =>
            match n with
            | 0 => impossible unit
            | m.+1 => x <- p ?? nat;;
                      x <- p !! option nat ;;
                      rec x m
            end
          end) x n.
  Close Scope lty_scope.
  Open Scope expr_scope.

  Inductive Option := Continue | Stop.
  Fixpoint weirdest_client (n : nat) (p : P) : io_proc (fin_client n p) :=
    match n with
    | 0 => p ! None ;; RET tt
    | m.+1 => a <- read Option;;
                match a with
                | Continue =>
                  p ! Some n ;;
                  _ <- p ? ;;
                  weirdest_client m p
                | Stop => p ! None ;; RET tt
                end
    end.
  Fixpoint weirdestest_client (n : nat) (p : P) : io_proc (fin_client_alt n p) :=
    match n with
    | 0 => p ! None ;; RET tt
    | m.+1 => a <- read Option;;
                match a with
                | Continue =>
                  p ! Some n ;;
                  _ <- p ? ;;
                  weirdestest_client m p
                | Stop => p ! None ;; RET tt
                end
    end.

  Fail Fixpoint weirdest_client1 (n : nat) (p : P) : io_proc (fin_client n p) :=
    match n with
    | 0 => p ! Some 0 ;; _ <- p ? ;; RET tt
    | m.+1 => p ! Some n ;; _ <- p ? ;; weirdest_client1 m p
    end.
  Fixpoint weirdest_client2 (n : nat) (p : P) : io_proc (fin_client n p) :=
    match n with
    | 0 => p ! None ;; RET tt
    | m.+1 => p ! None ;; RET tt
    end.

  Fixpoint weirdestest_client1 (n : nat) (p : P) : io_proc (fin_client_alt n p) :=
    p ! None ;;
      match n with
      | 0 => RET tt
      | m.+1 => RET tt
      end.
  Fail CoFixpoint weirdestest_client1 (n : nat) (p : P) : io_proc (fin_client_alt n p) :=
    p ! Some n ;;
      match n with
      | 0 => weirdestest_client1 0 p
      | m.+1 => _ <- p ? ;; weirdestest_client1 m p
      end.
End PingPong.

Module DependentProtocols.
  Import ITree.
  Import LocalTypes.
  Import IOProc.

  Open Scope lty_scope.
  Definition repeat_send (p : P) k : nat -> itree LTy Type :=
    cofix repeat_n n :=
      match n with
      | 0 => k
      | m.+1 => x <- p !! nat;; repeat_n m
      end.
  CoFixpoint request_n_tasks (p : P) : itree LTy Type :=
    n <- p ?? nat ;;
      repeat_send p (request_n_tasks p) n.
  Close Scope lty_scope.

  Definition Task := nat.
  Open Scope expr_scope.

  CoFixpoint example_server (p : P) : io_proc (request_n_tasks p)
    := n <- p ? ;;
         ((cofix rec n : io_proc (repeat_send p (request_n_tasks p) n) :=
             match n with
             | 0 => CALL (example_server p)
             | m.+1 => x <- read Task;; p ! x ;; rec m
             end) n).
End DependentProtocols.

Module Global.

  (* This attempt failed because of the impossibility of projecting
     behaviours to individual participants. This is because not all
     participants can observe the exchanged messages.
   *)
  Module FailedAttempt1.
    Import ITree.
    Inductive Global (A : Type) : Type := | Msg (p q : P).

    Inductive Prefix : Type -> Type :=
    | Last {A} : Global A -> Prefix A
    | And {A B} : Global A -> Prefix B -> Prefix (A * B).

    Definition gty := itree Prefix Set.

    CoFixpoint bottom {E} : itree E Set := go (Tau bottom).

    CoFixpoint pp p q :=
      go (Vis (Last (Msg (option nat) p q))
              (fun n =>
                 match n with
                 | Some x =>go (Vis (Last (Msg nat q p)) (fun _ => pp p q))
                 | None => go (Ret unit)
                 end)).

    (* I cannot project this *)
    CoFixpoint pipeline p q r :=
      go (Vis (And (Msg (option nat) p q) (Last (Msg bool q r)))
              (fun n =>
                 match n with
                 | (Some x, true) => pipeline p q r
                 | (None, false) => go (Ret unit)
                 | (_, _) => bottom
                 end)).

    (* I need the continuation to depend on the *observations* of each participant.
       E.g. p 'observes' [option nat]
       q 'observes' [option nat] and [bool]
       r 'observes' [bool]
       Maybe the global types should encode the projections themselves??
     *)
  End FailedAttempt1.

  Module Attempt2.
  (* Vis [:: Msg p q (option nat); Msg q r bool] *)
  (*     (fun pk => *)
  (*        match pk with *)
  (*        | Some n => Vis [:: ; ... ] *)
  (*        | None => Vis [Msg q r bool] *)
  (*                      fun k => *)
  (*                        match k with *)
  (*                        |  *)
  (*     ) *)

  (*     E (P -> Type) *)
  (*     fun k => *)
  (*       match k p with *)
  (*       | p1 => G1 *)
  (*       | ... *)
  (*       | pn => Gn *)
  (*       end *)

  End Attempt2.




End Global.

Extract Constant leq => "(<=)".
Extraction Inline leq.
Recursive Extraction Examples.prog31.
Recursive Extraction PingPong.some_client.
