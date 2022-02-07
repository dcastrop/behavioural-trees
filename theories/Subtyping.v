Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.

Require Import Utils.ZooidTac.
Require Import Zooid2.Types.

Set Implicit Arguments.
Set Primitive Projections.

Inductive subT : Type -> Type -> Prop :=
| subT_eq T : subT T T
| subT_sumL T S1 S2 : subT T S1 -> subT T (S1 + S2)
| subT_sumR T S1 S2 : subT T S2 -> subT T (S1 + S2)
.

Inductive subTf : forall (T1 T2: Type), ((T1 -> nat) -> (T2 -> nat) -> Prop) :=
| subTf_eq T f: @subTf T T f f.

Inductive subTalt : (T1 -> nat) -> (Type -> nat) -> Prop :=
| subTalt_eq f : subTalt f f
| subTalt_sumL f1 f2 T1 T2: subTalt f1 f2

Inductive subtype_ (S : LocalType -> LocalType -> Prop)
  : LocalType -> LocalType -> Prop :=
| sub_end : @subtype_ S b_end b_end
| sub_send L1 L2 AT p k1 k2:
  b_unroll L1 = b_act AT  k1 ->
  b_unroll L2 = b_act AT l_send k2 ->
  (forall @subtype_ S Lk1 Lk2) -> @subtype_ S L1 L2

| sub_recv :
.

(*
Inductive lty_lts_ (p : participant) (G : ty_trace -> LocalType -> Prop)
    : ty_trace -> LocalType -> Prop :=
  | ty_end TRC L :
      b_unroll L = b_end ->
      unroll TRC = tr_end -> @lty_lts_ p G TRC L
  | ty_next E TRC0 TRC1 L0 L1 :
      unroll TRC0 = tr_next E TRC1 ->
      @lty_step p (b_unroll L0) E L1 -> G TRC1 L1 -> @lty_lts_ p G TRC0 L0
.

Derive Inversion lty_lts_inv with
    (forall p G TRC L, @lty_lts_ p G TRC L) Sort Prop.
Definition lty_accepts p := paco2 (lty_lts_ p) bot2.

Lemma lty_lts_monotone p : monotone2 (lty_lts_ p).
Proof.
  move=>TRC L r r' H0 H1;  case: H0.
  - by move=> TRC0 U0; constructor.
    - by move=> E0 TRC0 TRC1 L0 L1 U0 ST /H1; apply (ty_next _ _ _ U0).
Qed.*)
