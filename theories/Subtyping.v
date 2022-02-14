Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.

Require Import Utils.ZooidTac.
Require Import Zooid2.Types.

Set Implicit Arguments.
Set Primitive Projections.

(*Inductive subT : Type -> Type -> Prop :=
| subT_eq T : subT T T
| subT_sumL T S1 S2 : subT T S1 -> subT T (S1 + S2)
| subT_sumR T S1 S2 : subT T S2 -> subT T (S1 + S2)
| subT_sumLR T1 T2 S1 S2 :
  subT T1 S1 -> subT T2 S2 -> subT (T1 + T2) (S1 + S2)
| subT_sumRL T1 T2 S1 S2 :
  subT T1 S1 -> subT T2 S2 -> subT (T2 + T1) (S1 + S2)
.

Definition sum_map {A B C : Type} (f1 : A -> C) (f2 : B -> C)
  : A + B -> C :=
  fun s =>
    match s with
    | inl a => f1 a
    | inr b => f2 b
    end.

Inductive subTf : forall (T S: Type), ((T -> nat) -> (S -> nat) -> Prop) :=
| subTf_eq T f: @subTf T T f f
| subTf_sumL T S1 S2 f g1 g2:
  subT T S1 ->
  @subTf T S1 f g1 ->
  @subTf T (S1 + S2) f (sum_map g1 g2)
| subTf_sumR T S1 S2 f g1 g2:
  subT T S2 ->
  @subTf T S2 f g2 ->
  @subTf T (S1 + S2) f (sum_map g1 g2)
| subTf_sumLR T1 T2 S1 S2 f1 f2 g1 g2:
  subT T1 S1 -> subT T2 S2 ->
  @subTf T1 S1 f1 g1 -> @subTf T2 S2 f2 g2 ->
  @subTf (T1 + T2) (S1 + S2) (sum_map f1 f2) (sum_map g1 g2)
| subTf_sumRL T1 T2 S1 S2 f1 f2 g1 g2:
  subT T1 S1 -> subT T2 S2 ->
  @subTf T1 S1 f1 g1 -> @subTf T2 S2 f2 g2 ->
  @subTf (T2 + T1) (S1 + S2) (sum_map f2 f1) (sum_map g1 g2)
.

Definition sub_altT (AT1 AT2 : AltT) :=
  subT AT1.(sumT) AT2.(sumT) /\ subTf AT1.(sumT_alt) AT2.(sumT_alt).*)

Definition find_k_bot {A} n k :=
  match @find_k A n k with
  | b_bot => true
  | _ => false
  end.

Inductive subtype_ (S : LocalType -> LocalType -> Prop)
  : LocalType -> LocalType -> Prop :=
| sub_bot: @subtype_ S b_bot b_bot
| sub_end: @subtype_ S b_end b_end
| sub_send L1 L2 AT a k1 k2:
  b_unroll L1 = b_act AT a k1 -> (*maybe use the b_run and iff*)
  b_unroll L2 = b_act AT a k2 ->
  lact a = a_send ->
  (forall n, find_k_bot n k1 == find_k_bot n k2)->
  (forall n, S (find_k n k1) (find_k n k2)) ->
  @subtype_ S L1 L2
| sub_recv L1 L2 AT a k1 k2:
  b_unroll L1 = b_act AT a k1 ->
  b_unroll L2 = b_act AT a k2 ->
  lact a = a_recv ->
  (forall n, find_k_bot n k1 -> find_k_bot n k2)->
  (forall n, S (find_k n k1) (find_k n k2)) ->
  @subtype_ S L1 L2
.

Derive Inversion subtype_inv with
    (forall S L1 L2, @subtype_ S L1 L2) Sort Prop.
Definition subtype := paco2 (subtype_) bot2.

Lemma subtype_monotone: monotone2 (subtype_).
Proof.
  move=> L1 L2 r r' H0 H1;  case: H0.
  - by constructor.
  - by constructor.
  - move=> {}L1 {}L2 AT a k1 k2 u1 u2 aeq sd hp.
    by apply: (sub_send r' _ _ u1 u2 aeq sd)=>n; apply H1, hp.
  - move=> {}L1 {}L2 AT a k1 k2 u1 u2 aimp sd hp.
    by apply: (sub_recv r' _ _ u1 u2 aimp sd)=>n; apply H1, hp.
Qed.

Check subtype.
Check lty_accepts.

Lemma subtype_trace (L1 L2: LocalType) p TRC:
  @subtype L1 L2 -> @lty_accepts p TRC L1 -> @lty_accepts p TRC L2.
  Admitted.
