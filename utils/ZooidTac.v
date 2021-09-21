Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.

Inductive _co_marker := _co_marker_constr.

Ltac co_move :=
  let M := fresh "M" in
  move: _co_marker_constr => M;
  repeat
    match goal with
    | [|- forall nm : ?P, _] =>
      let H := fresh nm in
      move=> H
    end
.

Ltac co_revert :=
  match goal with
  | [x : ?T |- _] =>
    match T with
    | _co_marker => move=>{x}
    | _ => move: x; co_revert
    end
  end.

Ltac pack :=
  repeat
    match goal with
    | [|- forall (a : ?P) (b : ?Q), _ ] =>
      let X := fresh a in
      let Y := fresh b in
      move=>X Y; move: {X Y} (conj X Y)
    | [x : ?A |- forall a : ?P,_] =>
      let Px := fresh a in
      move=> Px; move: {x Px} (ex_intro (fun=>_) x Px)
    end.

Ltac float_hyp :=
  match goal with
  | [x : ?T |- forall a : ?P, _] =>
    let H := fresh a in
    match T with
    | _co_marker =>
      move=> H {x}; co_move
    | _ =>
      move=> H; move: H x; float_hyp
    end
  end.

Ltac add_equalities :=
  repeat
    match goal with
    | [|- context [ ?P (?f ?x) ]] =>
      move: {-1}(f x) (@erefl _ (f x)); float_hyp
    end.

Ltac co_gen :=
  repeat
    match goal with
    | [|- ?P -> ?Q ?x] => move: x
    | [x : ?A|- forall y, ?P -> ?Q ?x y] => move: x
    end.

Ltac simpl_ch CH :=
  let rr := fresh "rr" in
  move=>rr _;
  repeat
    match goal with
    | [|- forall x : ?A, _] =>
      match A with
      | (forall a, (exists _, _) -> _) => move=>/(_ _ (ex_intro _ _ _))
      | (forall a b, (exists _, _) -> _) => move=>/(_ _ _ (ex_intro _ _ _))
      | (forall a b c, (exists _, _) -> _) => move=>/(_ _ _ _ (ex_intro _ _ _))
      | (forall a b c d, (exists _, _) -> _) => move=>/(_ _ _ _ _ (ex_intro _ _ _))
      | (forall a b c d e, (exists _, _) -> _) => move=>/(_ _ _ _ _ _ (ex_intro _ _ _))
      | (forall a b c d e f, (exists _, _) -> _) => move=>/(_ _ _ _ _ _ _ (ex_intro _ _ _))
      | (forall a,           _ /\ _ -> _) => move=>/(_ _           (conj _ _))
      | (forall a b,         _ /\ _ -> _) => move=>/(_ _ _         (conj _ _))
      | (forall a b c,       _ /\ _ -> _) => move=>/(_ _ _ _       (conj _ _))
      | (forall a b c d,     _ /\ _ -> _) => move=>/(_ _ _ _ _     (conj _ _))
      | (forall a b c d e  , _ /\ _ -> _) => move=>/(_ _ _ _ _ _   (conj _ _))
      | (forall a b c d e f, _ /\ _ -> _) => move=>/(_ _ _ _ _ _ _ (conj _ _))
      | (forall a,           _ = _ -> _) => move=>/(_ _           erefl)
      | (forall a b,         _ = _ -> _) => move=>/(_ _ _         erefl)
      | (forall a b c,       _ = _ -> _) => move=>/(_ _ _ _       erefl)
      | (forall a b c d,     _ = _ -> _) => move=>/(_ _ _ _ _     erefl)
      | (forall a b c d e  , _ = _ -> _) => move=>/(_ _ _ _ _ _   erefl)
      | (forall a b c d e f, _ = _ -> _) => move=>/(_ _ _ _ _ _ _ erefl)
      end
    end;
  move=> CH
.

Ltac cleanup :=
  let X := fresh "M" in
  move: _co_marker_constr=>X;
  repeat
    match goal with
    | [|- forall a : ?T, _] =>
      let X := fresh a in
      match T with
      | _ /\ _ => case
      | exists _, _ => case
      | ?x = _ => move=>->{x}
      | _ = ?x => move=><-{x}
      | _ => move=> X
      end
    end;
  co_revert.

Ltac post_coind CH :=
  simpl_ch CH; cleanup.

Ltac pre_coind :=
  co_move; add_equalities; co_revert; pack; co_gen.


Ltac coind CH :=
  pre_coind;
  match goal with
  | [|- _] => apply/paco1_acc
  | [|- _] => apply/paco2_acc
  | [|- _] => apply/paco3_acc
  | [|- _] => apply/paco4_acc
  | [|- _] => apply/paco5_acc
  end;
  post_coind CH.
