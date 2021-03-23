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
  End Syntax.

  Arguments Vis {E R itree A} e k.
  Arguments Tau {E R itree} i.
  Arguments Ret {E R itree} r.

  Section Peek.
    Context (E : Type -> Type).
    Context (R : Type).

  Definition run (i : itree E R) : itreeF E R (itree E R) :=
    match observe i with
    | Vis _ e k => Vis e k
    | Tau t => observe t
    | Ret r => Ret r
    end.

  End Peek.

  Section LocalTypes.

    Definition P := nat.

    Inductive LTy (A : Type) := | LSend (p : P) | LRecv (p : P).

    Definition lty := itree LTy Set.
    Definition lty' := itreeF LTy Set (itree LTy Set).
    Definition p_lty := lty -> Prop.
    Definition p_lty' := lty' -> Prop.

  End LocalTypes.

  Declare Scope lty_scope.
  Bind Scope lty_scope with lty.
  Delimit Scope lty_scope with lty.
  Notation "X '<-' p '!!' e ';;' K" :=
    (go (Vis (LSend e p) (fun X=>K)))
      (at level 60, right associativity) : lty_scope.
  Notation "X '<-' p '??' e ';;' K" :=
    (go (Vis (LRecv e p) (fun X=>K)))
      (at level 60, right associativity) : lty_scope.
  Definition inact A : lty := go (Ret A).

  Section WellTypedProcesses.

    Variable E : Type -> Type.

    Inductive ev l : forall A, (A -> lty) -> Type :=
    | E_send {A} x p k (H : Vis (LSend A p) k = run l) : @ev l unit (fun _ => k x)
    | E_recv {A} p k (H : Vis (LRecv A p) k = run l) : @ev l A k
    | E_run {A} (e : E A) : @ev l A (fun _ =>l).
    Arguments E_send & [l A] x p [k] H.
    Arguments E_recv & [l A] p [k] H.
    Arguments E_run & [l A] e.

    Inductive procF (proc : lty -> Type) : lty -> Type :=
    | P_ev {A k l} (e : @ev l A k) (kp : forall x, proc (k x)) : procF proc l
    | P_end {A : Set} (x : A) l (_ : Ret A = run l) : procF proc l.
    Arguments P_ev [proc A k] & [l] e kp.
    Arguments P_end [proc A] x & [l] _.

    CoInductive proc (l : lty) : Type :=
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

    Definition pure [A : Set] (x : A) l (H : Ret A = run l) : proc l :=
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

  Arguments E_send & [E l A] x p [k] H.
  Arguments E_recv & [E l A] p [k] H.
  Arguments E_run & [E l A] e.
  Arguments P_ev [E proc A k] & [l] e kp.
  Arguments P_end [E proc A] x & [l] _.
  Arguments Go & [E l].
  Arguments p_send [E A] x p & [l kl] H k.
  Arguments p_recv [E A] p & [l kl] H k.
  Arguments pure [E A] x & [l] _.
  Arguments ifB [E] & [l1 l2] b p1 p2.

  Declare Scope expr_scope.
  Bind Scope expr_scope with proc.
  Delimit Scope expr_scope with expr.
  Notation "'RET' x" := (pure x Logic.eq_refl) (at level 60) : expr_scope.
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
  Definition p := 0.
  CoFixpoint example : lty :=
    n <- p !! nat ;;
      match n with
      | 0 => inact bool
      | m.+1 => b <- p !! bool ;; example
      end
      % lty.

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

  CoFixpoint example2 : lty :=
    n <- p ?? nat ;;
      match n with
      | 0 => inact bool
      | m.+1 => b <- p !! bool ;; example2
      end % lty.
  CoFixpoint prog21 : pure_proc example2 :=
    n <- p ? ;;
      match n with
      | 0 => RET true
      | m.+1 => p ! false ;; prog21
      end.
  Close Scope expr_scope.

  Open Scope lty_scope.
  CoFixpoint example3 : lty :=
    n <- p ?? nat ;;
      if n > 27
      then inact bool
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
  Print E_send.

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

  CoFixpoint pp_client (p : P) : lty :=
    n <- p !! option nat ;;
      match n with
      | None => inact unit
      | Some n => _ <- p ?? nat ;; pp_client p
      end
      % lty.

  CoFixpoint pp_server (p : P) : lty :=
    n <- p ?? option nat ;;
      match n with
      | None => inact unit
      | Some n => _ <- p !! nat ;; pp_server p
      end
      % lty.

  Inductive PingTy := Ping (n : nat) | Close.
  Inductive PongTy := Pong (n : nat).

  Open Scope expr_scope.
  CoFixpoint some_client (p : P) : io_proc (pp_client p) :=
    n <- read PingTy ;;
    match n with
    | Ping n =>
      p ! Some n ;;
      x <- p ? ;;
      write (Pong x);;
      some_client p
    | Close => p ! None ;; RET tt
    end.

End PingPong.

Extract Constant leq => "(<=)".
Extraction Inline leq.
Recursive Extraction Examples.prog31.
