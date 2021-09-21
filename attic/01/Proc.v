Require Import mathcomp.ssreflect.all_ssreflect.
Require Import mathcomp.finmap.set.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Import Prenex Implicits.

Require Import Setoid.

(** Utility for testing multiple conditions **)
Fixpoint mif_args (n : nat) (A : Type) : Type :=
  match n with
  | 0 => A -> A
  | n.+1 => bool * A -> mif_args n A
  end.

Fixpoint mif_return A (n : nat) (a : A) : mif_args n A :=
  match n with
  | 0 => fun _ => a
  | n.+1 => fun _ => mif_return n a
  end.

Fixpoint mif A (n : nat) : mif_args n A :=
  match n return mif_args n A with
  | 0 => fun x => x
  | n.+1 => fun c1 =>
              let: (b, a) := c1 in
              if b then mif_return n a
              else mif A n
  end.

Definition mif3 {A} := @mif A 3.

Definition lbl (A : nat -> Type) : Type := {n & A n}.

Definition zero (A : Type) :=
  fun n =>
    match n with
    | 0 => A
    | _ => False
    end.

Definition unpack A (x : lbl (zero A)) : A :=
  match x with
  | existT 0 a => a
  | existT n.+1 F => match F with end
  end.

Definition Sum (A B : Type) :=
  lbl (fun n =>
         match n with
         | 0 => A
         | 1 => B
         | _ => False
         end).

Definition from_sum {A B} (x : A + B) : Sum A B
    := match x with
       | inl y => existT _ 0 y
       | inr y => existT _ 1 y
       end.

Definition to_sum {A B} (x : Sum A B) : A + B
  := match x with
     | existT 0 y => inl y
     | existT 1 y => inr y
     | existT n.+2 y => match y with end
     end.

Lemma Sum_sum_iso A B (x : A + B) (y : Sum A B)
  : y = from_sum x <-> to_sum y = x.
Proof. by split=>[->|<-]; [case: x|case: y=>[[|[]]]]. Qed.

Corollary Sum_sum_iso_l A B (x : A + B) : to_sum (from_sum x) = x.
Proof. by apply/Sum_sum_iso. Qed.

Corollary Sum_sum_iso_r A B (x : Sum A B) : from_sum (to_sum x) = x.
Proof. by symmetry; apply/Sum_sum_iso. Qed.

(** Coinductive interaction trees (copy of simplification) **)
CoInductive itree (E : Type -> Type) (R : Type) : Type :=
| Ret (r : R)
| Tau (t : itree E R)
| Vis {A} (e : E A) (l : A -> itree E R).

Arguments Ret [E R] _.
Arguments Tau [E R] _.
Arguments Vis [E R A] _ _.


Definition peek_itree E R (t : itree E R) :=
  match t with
  | Ret x => Ret x
  | Tau t => Tau t
  | Vis _ e k => Vis e k
  end.

Lemma unfold_itree E R (t : itree E R) : peek_itree t = t.
Proof. by case: t. Qed.


Inductive Ev (E : Type -> Type) : Type -> Type :=
| Ev_some {A} (e : E A) : Ev E unit
| Ev_none {A} (e : E A) (f : A -> False) : Ev E False.

Definition itrace E A := itree (Ev E) A.

Module MPST.
  Context (P : eqType).

  Inductive GActs : seq Type -> Type :=
  | GEnd : GActs [::]
  | GMsg (p q : P) A B (G : GActs B) : GActs (A :: B).

  Inductive OneOf (T : seq Type) : Type := | Sel.

  Inductive GProtocol : Type -> Type :=
  | GNext T (a : GActs T) : GProtocol (OneOf T).

  (* Inductive LProtocol : Type -> Type := *)
  (* | LSend (p : P) (A : nat -> Type) : LProtocol nat *)
  (* | LRecv (p : P) (A : nat -> Type) : LProtocol nat. *)

  Inductive LProtocol : Type -> Type :=
  | LSend (p : P) (A : Type) : LProtocol A
  | LRecv (p : P) (A : Type) : LProtocol A.

  Inductive Comm : Type -> Type :=
  | Send (p : P) A (a : A) : Comm unit
  | Recv (p : P) A : Comm A.

  Definition typeOf A (c : Comm A) : Type :=
    match c with
    | @Send _ A _ => A
    | @Recv _ A => A
    end.

  Definition erase A (c : Comm A) : LProtocol (typeOf c) :=
    match c with
    | @Send p A _ => LSend p A
    | @Recv p A => LRecv p A
    end.

  (** Hint, this is "simulation?", just as with traces? *)
  CoInductive OfLt A : itree Comm A -> itree LProtocol A -> Prop :=
  | LT_Ret  x   : OfLt (Ret x) (Ret x)
  | LT_TauL a b : OfLt a b -> OfLt (Tau a) b
  | LT_TauR a b : OfLt a b -> OfLt a (Tau b)
  | LT_Send S a b p (x : S) :
      OfLt (a tt) (b x) -> OfLt (Vis (Send p x) a) (Vis (LSend p S) b)
  | LT_Recv S a b p :
      (forall x, OfLt (a x) (b x)) -> OfLt (Vis (Recv p S) a) (Vis (LRecv p S) b)
  .

  (** Examples **)
  Variable (p q : P).

  Inductive NatOrBool := | Nat (n : nat) | Bool (b : bool).

  Definition example1 :=
    Vis (Recv p nat)
        (fun k =>
           if k == 3 then
             Vis (Send p (Nat 1)) (fun _ => Ret true)
           else
             Vis (Send p (Bool true)) (fun _ => Ret false)
        ).

  (* L = p?nat . p ! { Nat. end ; Bool. end } *)

  Definition lt1 :=
    Vis (LRecv p nat) (fun _ => Vis (LSend p NatOrBool) (fun x =>
                                                           match x with
                                                           | Nat _ => Ret true
                                                           | Bool _ => Ret false
                                                           end)).

  Goal OfLt example1 lt1.
    constructor=>[]x; case: ifP; constructor; constructor.
  Qed.

  (** Problem: Unclear how to produce "well-typed terms" by construction, without
      such proofs *)

End MPST.

Module Attempt2.
Section ConstrainedITrees.

  Set Primitive Projections.

  Inductive ITreeType  : Type :=
  | vis (A : Type)
  | tau
  | ret.

  Definition continuation (ev : ITreeType) :=
    match ev with
    | vis A => A
    | tau => unit
    | ret => False
    end.

  Definition itreeEvent (E : Type -> Type) (R : Type) (it : ITreeType) :=
    match it with
    | vis A => E A
    | tau => unit
    | ret => R
    end.

  Set Primitive Projections.
  CoInductive ctree (E : Type -> Type) (R : Type) : Type :=
    { ctype : ITreeType;
      event : itreeEvent E R ctype;
      continue : continuation ctype -> ctree E R
    }.
  Unset Primitive Projections.
  Arguments continue [E R] _.

  (* All events are internal *)
  CoFixpoint cspin E R : ctree E R :=
    {| ctype := tau;
       event := tt;
       continue := fun _ => cspin E R
    |}.

  Definition skip E R (t : ctree E R) : ctree E R :=
    {| ctype := tau;
       event := tt;
       continue := fun _ => t
    |}.

  Definition pure E R (r : R) : ctree E R :=
    {| ctype := ret;
       event := r;
       continue := fun f => match f with end
    |}.
  Arguments pure {E} [R] r.

  Definition cast_event E R R' A (x : itreeEvent E R (vis A))
    : itreeEvent E R' (vis A) := x.
  Arguments cast_event [E R R' A] _.

  Definition bind E R R' (m : ctree E R) (f : R -> ctree E R') : ctree E R' :=
    (cofix bind_f (m : ctree E R) :=
      match ctype m as Ty
            return itreeEvent E R Ty -> (continuation Ty -> ctree E R) -> ctree E R'
      with
      | ret => fun ev _ => f ev
      | tau => fun ev k => {| ctype := tau;
                              event := tt;
                              continue := fun _ => bind_f (k tt)
                           |}
      | vis A => fun ev k => {| ctype := vis A;
                                event := cast_event ev;
                                continue := fun x => bind_f (k x)
                             |}
      end (event m) (continue m)) m.
  Arguments bind [E R R'] _ _.

  Context (P : Type) (p : P).
  Inductive LProtocol : Type -> Type :=
  | LSend (p : P) (A : Type) : LProtocol A
  | LRecv (p : P) (A : Type) : LProtocol A.

  Definition l_send (p : P) A : ctree LProtocol A :=
    {| ctype := vis A;
       event := LSend p A;
       continue := fun k => pure k
    |}.
  Definition l_recv (p : P) A : ctree LProtocol A :=
    {| ctype := vis A;
       event := LRecv p A;
       continue := fun k => pure k
    |}.
  Notation "A >>= F" := (bind A F) (at level 42, left associativity).
  Notation "'do' X <- A ; B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

  Inductive NatOrBool := | End (n : nat) | Continue (b : bool).

  Definition rec {E R} (t : ctree E R) :=
    {| ctype := tau;
       event := tt;
       continue := fun _ => t
    |}.

  (** This "naive" way of writing recursion does not work *)
  CoFixpoint example1 : ctree LProtocol unit :=
    do _ <- l_recv p nat;
    do c <- l_send p NatOrBool;
       match c with
       | End _ => do _ <- l_send p bool; pure tt
       | Continue _ => rec example1
       end.



End ConstrainedITrees.
