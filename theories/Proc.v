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

  End Peek.

  Section LocalTypes.

    Definition P := nat.

    Inductive LTy (A : Type) := | LSend (p : P) | LRecv (p : P).

    Definition lty := itree LTy Set.
    Definition lty' := itreeF LTy Set (itree LTy Set).
    Definition p_lty := lty -> Prop.
    Definition p_lty' := lty' -> Prop.

    Definition _can_send (r : P) : p_lty' :=
      fun l => match l with
               | Vis _ (LSend s) _ => s = r
               | _ => False
               end.

    Definition _can_recv (r : P) : p_lty' :=
      fun l => match l with
               | Vis _ (LRecv s) _ => s = r
               | _ => False
               end.

    Definition _type_ev A : p_lty' :=
      fun l => match l with
               | Vis B _ _ => B = A
               | _ => False
               end.

    Definition can_send (r : P) : p_lty :=
      fun l => _can_send r (run l).

    Definition can_recv (r : P) : p_lty :=
      fun l => _can_recv r (run l).

    Definition type_ev A : p_lty :=
      fun l => _type_ev A (run l).

    Definition run_send A (r : P) (x : A) (l : lty)
      : can_send r l -> type_ev A l -> lty :=
      match run l as rl
            return _can_send r rl -> _type_ev A rl -> lty
      with
      | Vis T (LSend p) k =>
        fun _ EQ => match EQ in _ = T
                          return T -> lty
                    with
                    | eq_refl => k
                    end x
      | _ => fun F => match F with end
      end.

    Definition run_recv A (r : P) (l : lty)
      : can_recv r l -> type_ev A l -> A -> lty :=
      match run l as rl
            return _can_recv r rl -> _type_ev A rl -> A -> lty
      with
      | Vis T (LRecv p) k =>
        fun _ EQ => match EQ in _ = T
                          return T -> lty
                    with
                    | eq_refl => k
                    end
      | _ => fun F => match F with end
      end.

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

    Definition ev_ty : Type := forall A, lty -> (A -> lty) -> Type.

    Inductive ev : ev_ty :=
    | E_send {A} (x : A) p l (H1 : can_send p l) (H2 : type_ev A l)
      : @ev unit l (fun y =>run_send x H1 H2)
    | E_recv {A} p l (H1 : can_recv p l) (H2 : type_ev A l)
      : @ev A l (run_recv H1 H2).
    Arguments E_send [A] x p & [l] H1 H2.
    Arguments E_recv [A] p & [l] H1 H2.

    Inductive procF (proc : lty -> Type) : lty -> Type :=
    | P_ev {A k l} (e : @ev A l k) (kp : forall x, proc (k x)) : procF proc l
    | P_end {A : Set} (x : A) l (_ : Ret A = run l) : procF proc l.
    Arguments P_ev [proc A k] & [l] e kp.
    Arguments P_end [proc A] x & [l] _.

    CoInductive proc (l : lty) : Type :=
      Go { observeP : procF proc l }.
    Arguments Go & [l].

    Definition p_send {A} (x : A) (p : P)
               l (H1 : can_send p l) (H2 : type_ev A l)
               (k : unit -> proc (run_send x H1 H2))
      : proc l := Go (P_ev (E_send x p H1 H2) k).
    Arguments p_send [A] x p & [l] H1 H2 k.

    Definition p_recv {A} (p : P)
               l (H1 : can_recv p l) (H2 : type_ev A l)
               (k : forall x, proc (run_recv H1 H2 x))
      : proc l := Go (P_ev (E_recv p H1 H2) k).
    Arguments p_recv [A] p & [l] H1 H2 k.

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
    Notation "'if' b 'then' p1 'else' p2" := (ifB b p1 p2) : expr_scope.
  End WellTypedProcesses.

  Arguments E_send [A] x p & [l] H1 H2.
  Arguments E_recv [A] p & [l] H1 H2.
  Arguments P_ev [proc A k] & [l] e kp.
  Arguments P_end [proc A] x & [l] _.
  Arguments Go & [l].
  Arguments p_send [A] x p & [l] H1 H2 k.
  Arguments p_recv [A] p & [l] H1 H2 k.
  Arguments pure [A] x & [l] _.
  Arguments ifB & [l1 l2] b p1 p2.

  Declare Scope expr_scope.
  Bind Scope expr_scope with proc.
  Delimit Scope expr_scope with expr.
  Notation "'RET' x" := (pure x Logic.eq_refl) (at level 60) : expr_scope.
  Notation "p '!' e ';;' K" :=
    (p_send e p Logic.eq_refl Logic.eq_refl (fun _ =>K))
      (right associativity, at level 60) : expr_scope.
  Notation "x '<-' p '?' ';;' K" :=
    (p_recv p Logic.eq_refl Logic.eq_refl (fun x => K))
      (right associativity, at level 60) : expr_scope.
  Notation "'if' b 'then' p1 'else' p2" := (ifB b p1 p2) : expr_scope.

  Section Examples.
    Definition p := 0.
    CoFixpoint example : lty :=
      n <- p !! nat ;;
        match n with
        | 0 => inact bool
        | m.+1 => b <- p !! bool ;; example
        end
        % lty.

    Open Scope expr_scope.
    CoFixpoint prog1 : proc example
      := p ! 1 ;; p ! true ;; prog1.
    CoFixpoint prog2 : proc example
      := p ! 1 ;; p ! true ;; p ! 2 ;; p ! false ;; prog2.
    Definition prog3 : proc example
      := p ! 1 ;;
           (cofix cont :=
              p ! true ;; p ! 2 ;; cont).
    CoFixpoint prog4 (n : nat) : proc example :=
      match n with
      | 0 => p ! 0 ;; RET true
      | m.+1 => p ! m.+1 ;; p ! false ;; prog4 m
      end.
    CoFixpoint prog5 (n : nat) : proc example :=
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
    CoFixpoint prog21 : proc example2 :=
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
    CoFixpoint prog31 : proc example3
      := n <- p ? ;;
           if (n > 27)
           then RET true
           else p ! false ;; prog31.
    CoFixpoint prog32 : proc example3
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
End ITree.

Require Extraction.
Require Import ExtrOcamlBigIntConv.
Import ITree.
Extraction Implicit E_send [A l H1 H2].
Extraction Implicit E_recv [A l H1 H2].
Extraction Implicit P_ev [A l k].
Extraction Implicit P_end [A l].
Extraction Implicit ifB [l1 l2].
Extraction Inline ifB.
Extraction Implicit p_send [l].
Extraction Inline p_send.
Extraction Implicit p_recv [l].
Extraction Inline p_recv.
Extraction Implicit p_recv [l].
Extraction Inline pure.
Extraction Implicit Go [l].

Extract Constant leq => "(<=)".
Extraction Inline leq.
Recursive Extraction prog31.
