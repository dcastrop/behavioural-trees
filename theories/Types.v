Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.

Set Implicit Arguments.
Set Primitive Projections.

(* begin details: participant identifiers are natural numbers *)

Definition participant := Int63.int.

Lemma int_eqP : Equality.axiom Int63.eqb.
Proof.
  move=>x y; case: (boolP (x =? y)%int63).
  - by move=>/eqb_correct->; constructor.
  - by move=>/negP-H; constructor=>/eqb_complete/H.
Qed.

Definition int_eqMixin := EqMixin int_eqP.
Canonical int_eqType := Eval hnf in EqType participant int_eqMixin.

(* end details *)

Record AltT := MkAltT { sumT :> Type; sumT_alt : sumT -> nat }.

Unset Elimination Schemes.
Inductive Behav A :=
| b_bot
| b_end
| b_var (t : nat)
| b_rec (G : Behav A)
| b_act (AT : AltT) (a : A) (k : seq (nat * Behav A)).
Set Elimination Schemes.

Arguments b_end & {A}.
Arguments b_bot & {A}.
Arguments b_var & {A} t.
Arguments b_rec & {A} G.
Arguments b_act & {A} AT a k.

Fixpoint Member A (x : A) s : Type :=
  match s with
  | [::] => False
  | h :: t => (x = h) + Member x t
  end.

Fixpoint AllT A (P : A -> Type) s : Type :=
  match s with
  | [::] => True
  | h :: t => P h * AllT P t
  end.

Lemma Behav_rect A (P : Behav A -> Type)
      (P_bot : P b_bot)
      (P_end : P b_end)
      (P_var : forall t, P (b_var t))
      (P_rec : forall G, P G -> P (b_rec G))
      (P_msg : forall AT a k,
          AllT P [seq x.2 | x <- k] ->
          P (@b_act _ AT a k))
  : forall G, P G.
Proof.
  fix Ih 1.
  move=>[||t|G|AT a k].
  - by apply/P_bot.
  - by apply/P_end.
  - by apply/P_var.
  - by apply/P_rec.
  - apply/P_msg.
    by elim: k=>[//|[n G'] k' IHk]/=; split.
Defined.

Lemma Behav_ind A (P : Behav A -> Prop)
      (P_bot : P b_bot)
      (P_end : P b_end)
      (P_var : forall t, P (b_var t))
      (P_rec : forall G, P G -> P (b_rec G))
      (P_msg : forall AT a k,
          AllT P [seq x.2 | x <- k] ->
          P (@b_act _ AT a k))
  : forall G, P G.
Proof.
    by elim/Behav_rect.
Qed.

Definition is_rec A (B : Behav A) :=
  match B with
  | b_rec _ => true
  | _ => false
  end.

Fixpoint behav_closed A d (B : Behav A) :=
  match B with
  | b_bot => false
  | b_end => true
  | b_var t => t < d
  | b_rec B => ~~ is_rec B && behav_closed d.+1 B
  | b_act AT a k => all (fun x => behav_closed d x.2) k
  end.

Definition all_eq A f :=
  fix allEq (k1 k2 : seq (nat * Behav A)) :=
    match k1, k2 with
    | [::], [::] => true
    | h1 :: t1, h2 :: t2 =>
      (h1.1 == h2.1) && f h1.2 h2.2 && allEq t1 t2
    | _, _ => false
    end.

Fixpoint eq_Behav (A : eqType) (B1 B2 : Behav A) :=
  match B1, B2 with
  | b_bot, b_bot => true
  | b_end, b_end => true
  | b_var t1, b_var t2 => t1 == t2
  | b_rec B1, b_rec B2 => @eq_Behav A B1 B2
  | b_act _ a1 k1, b_act _ a2 k2 => (a1 == a2) && all_eq (@eq_Behav A) k1 k2
  | _, _ => false
  end.

(** Check if this is needed **)
(* Fixpoint b_fvars_aux A c (B : Behav A) := *)
(*   match B with *)
(*   | b_bot => [::] *)
(*   | b_end => [::] *)
(*   | b_var t => if c <= t then [:: t] else [::] *)
(*   | b_rec B1 => b_fvars_aux (c.+1) B1 *)
(*   | b_act A a k => flatten (map (fun x=> b_fvars_aux c x.2) k) *)
(*   end. *)

(* Definition b_fvars A (B : Behav A) := b_fvars_aux 0 B. *)

(* Definition b_closed A (B : Behav A) := b_fvars B == [::]. *)

Fixpoint no_bot A (B : Behav A):=
  match B with
  | b_bot => false
  | b_end => true
  | b_var t => true
  | b_rec B1 => no_bot B1
  | b_act _ a k => all (fun x => no_bot (x.2)) k
  end.

Fixpoint b_shift A c (B : Behav A) :=
  match B with
  | b_var t => if t < c then B else b_var t.+1
  | b_act A a k => b_act A a [seq (x.1, b_shift c x.2) | x <- k]
  | b_rec G => b_rec (b_shift c.+1 G)
  | b_end => B
  | b_bot => B
  end.

Fixpoint b_subst A v (B' B : Behav A) :=
  match B with
  | b_var t => if v == t then B' else B
  | b_act A a k => b_act A a [seq (x.1, b_subst v B' x.2) | x <- k]
  | b_rec G => b_rec (b_subst v.+1 (b_shift 0 B') G)
  | b_end => B
  | b_bot => B
  end.

Definition b_unroll A (B : Behav A) :=
  match B with
  | b_rec B' =>
    match b_subst 0 B B' with
    | b_rec _ => b_end
    | b_var _ => b_end
    | B => B
    end
  | _ => B
  end.

Record gprefix :=
  mk_gprefix { gfrom : participant;
               gto : participant
             }.

Definition gprefix_eq g1 g2 :=
  (gfrom g1 == gfrom g2) && (gto g1 == gto g2).

Lemma gprefix_eqP : Equality.axiom gprefix_eq.
Proof with try (by constructor); try (by constructor=>[[]]).
  move=>[f1 t1] [f2 t2]; rewrite /gprefix_eq/=.
  do ! case: eqP=>[->|F]...
Qed.
Definition gprefix_eqMixin := EqMixin gprefix_eqP.
Canonical gprefix_eqType := Eval hnf in EqType gprefix gprefix_eqMixin.

Definition GlobalType := Behav gprefix.

Inductive action := a_send | a_recv.
Definition eq_action a1 a2 :=
  match a1, a2 with
  | a_send, a_send => true
  | a_recv, a_recv => true
  | _, _ => false
  end.

Lemma action_eqP : Equality.axiom eq_action.
Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed.

Definition action_eqMixin := EqMixin action_eqP.
Canonical action_eqType := Eval hnf in EqType action action_eqMixin.

Record lprefix :=
  mk_lprefix { lact : action;
               lsubj : participant
             }.
Definition lprefix_eq l1 l2 :=
  (lsubj l1 == lsubj l2) && (lact l1 == lact l2).

Lemma lprefix_eqP : Equality.axiom lprefix_eq.
Proof with try (by constructor); try (by constructor=>[[]]).
  move=>[f1 t1] [f2 t2]; rewrite /lprefix_eq/=.
  do ! case: eqP=>[->|F]...
Qed.
Definition lprefix_eqMixin := EqMixin lprefix_eqP.
Canonical lprefix_eqType := Eval hnf in EqType lprefix lprefix_eqMixin.

Definition LocalType := Behav lprefix.

(*participants of a global type*)

Fixpoint g_part G :=
  match G with
  | b_end => [::]
  | b_bot => [::]
  | b_var t => [::]
  | b_rec G1 => g_part G1
  | b_act _ a1 k1 =>
    (gfrom a1) :: ((gto a1) :: flatten (map (fun x => (g_part x.2)) k1) )
  end.

Definition guard b (L : LocalType) :=
  if b then L else b_bot.

Definition labels A B  (k : seq (A * B)) := [seq x.1 | x <- k].

Fixpoint remove n (k : seq (nat * LocalType)) :=
  match k with
  | [::] => [::]
  | h :: t => if h.1 == n then t else h :: remove n t
  end.

Fixpoint find n (k : seq (nat * LocalType)) : option LocalType :=
  match k with
  | [::] => None
  | h :: t => if h.1 == n then Some h.2 else find n t
  end.

Definition merge_recv (M : LocalType -> LocalType -> LocalType) :=
  fix mergeAll k1 k2 :=
    match k1 with
    | [::]  => k2
    | h1 :: t1 =>
      match find h1.1 k2 with
      | Some L => (h1.1, (M h1.2 L)) :: mergeAll t1 (remove h1.1 k2)
      | None => h1 :: mergeAll t1 k2
      end
    end.

Fixpoint merge (L1 L2 : LocalType) : LocalType :=
  match L1, L2 with
  | b_bot, _ => b_bot
  | _, b_bot => b_bot
  | b_rec L1, b_rec L2 => b_rec (merge L1 L2)
  | b_act AT (mk_lprefix a_recv p1) k1, b_act _ (mk_lprefix a_recv p2) k2 =>
    guard (p1 == p2) (b_act AT (mk_lprefix a_recv p1) (merge_recv merge k1 k2))
  | L1, L2 => guard (eq_Behav _ L1 L2) L1
  end.

Definition merge_all (K : seq LocalType) :=
  match K with
  | [::] => b_bot
  | h :: K => foldl merge h K
  end.

Definition proj_prefix (g : gprefix) r S k : LocalType :=
  match Int63.eqb (gfrom g) r, Int63.eqb (gto g) r with
  | true , false => @b_act _ S (mk_lprefix a_send (gto g)) k
  | false, true  => @b_act _ S (mk_lprefix a_recv (gfrom g)) k
  | _    , _     => merge_all [seq x.2 | x <- k]
  end.

Definition projects_to_end r G1 :=
  (r \notin (g_part G1)) && (behav_closed 0 (b_rec G1)) && (no_bot G1).

Fixpoint project (G : GlobalType) r : LocalType :=
  match G with
  | b_end => b_end
  | b_bot => b_bot
  | b_var t1 => b_var t1
  | b_rec G1 => if projects_to_end r G1 then b_end else b_rec (project G1 r)
  | b_act A1 a1 k1 =>
    proj_prefix a1 r A1 [seq (x.1, project x.2 r) | x <- k1]
  end.

(* Open Scope lty_scope. *)
(*   CoFixpoint unravel (L : LocalType) : lty *)
(*     := match b_unroll L with *)
(*        | b_end => END *)
(*        | b_act _ A a k => *)
(*          match lact a with *)
(*          | a_send => *)
(*            X <- lsubj a !! sumT A;; *)
(*            match find (sumT_alt A X) k with *)
(*            | Some LT => unravel LT *)
(*            | None => IMPOSSIBLE *)
(*            end *)
(*          | a_recv => *)
(*            X <- lsubj a ?? sumT A;; *)
(*            match find (sumT_alt A X) k with *)
(*            | Some LT => unravel LT *)
(*            | None => IMPOSSIBLE *)
(*            end *)
(*          end *)
(*        | _ => IMPOSSIBLE *)
(*        end. *)
(*   Close Scope lty_scope. *)


Definition single_choice (n : nat) T (x : T) := n.
Definition altT n (T : Type) : AltT := @MkAltT T (@single_choice n T).

Declare Scope gty_scope.
Delimit Scope gty_scope with gty.
Bind Scope gty_scope with GlobalType.
Notation "'END'" := (@b_end gprefix) : gty_scope.
Notation "'JUMP'" := (@b_var gprefix) : gty_scope.
Notation "'REC' '{' G '}'" := (@b_rec gprefix G) (at level 60, right associativity): gty_scope.
(* Notation "p '->' q '[' T ']' ';;' k" := *)
(*   (@b_act _ _ T (mk_gprefix p q) k) *)
(*         (at level 60, right associativity) : gty_scope. *)

Definition b_msg p q T G :=
  @b_act _ (altT 0 T) (mk_gprefix p q) [:: (0, G)].
Notation "p '~>' q '$(' T ')' ';;' k" :=
  (b_msg p q T k)
        (at level 60, right associativity) : gty_scope.
Notation "p '~>' q '${' T '}' ';;' k" :=
  (@b_act _ T (mk_gprefix p q) k)
        (at level 60, right associativity) : gty_scope.

(* Notation "n ':.' G" := *)
(*   (n, G) (at level 60, right associativity) : gty_scope. *)

(* Notation "'{{' A1 '|' .. '|' An '}}'" := *)
(*   (A1 :: (.. (An :: nil) ..)) *)
(*         (at level 60, right associativity) : gty_scope. *)

Module GTYExamples.
  Definition Alice := 1%int63.
  Definition Bob := 2%int63.

  Open Scope gty_scope.
  Example PP :=
    Alice ~> Bob $( nat ) ;;
    Bob ~> Alice $( bool ) ;;
    END.

  Example PPRec :=
    REC {
      Alice ~> Bob $( nat ) ;;
      Bob ~> Alice $( bool ) ;;
      JUMP 0
      }.

  Inductive MyChoice := Case1 (n : nat) | Case2 (b : bool).

  Definition lbl1 := 0.
  Definition lbl2 := 1.

  Definition MyChoiceT : AltT
    := @MkAltT MyChoice (fun x=>
                           match x with
                           | Case1 _ => lbl1
                           | Case2 _ => lbl2
                           end).

  Example CH1 :=
    REC {
      Alice ~> Bob ${ MyChoiceT } ;;
      [:: (lbl1, Bob ~> Alice $( bool );; JUMP 0);
          (lbl2, END)
      ]
      }.
  Close Scope gty_scope.
End GTYExamples.

(** ** Semantics of Local Types *)

(** *** Actions **)

(** Actions capture the kind of event that happened (send/receive), and the
necessary information about who performed the action, the other party, and the
payload type. **)

Record event :=
  mk_ev { action_type : action;
          subj : participant;
          part : participant;
          payload_type : Type;
        }.

(** *** Traces **)
(** Traces are (potentially infinite) streams of events. They are parameterised
 by the type of events. **)

Inductive traceF act G :=
| tr_end : traceF act G
| tr_next : act -> G -> traceF act G.
(* begin hide *)
Arguments tr_next & {act G}.
Arguments tr_end & {act G}.
(* end hide *)

CoInductive trace act := roll { unroll : traceF act (trace act) }.

Definition ty_trace := trace event.

(* begin details:  *)

Definition trace_mapF {A B : Type} (f : A -> B) X Y G (trc : traceF A X)
  : traceF B Y :=
  match trc with
  | tr_end => tr_end
  | tr_next a trc => tr_next (f a) (G trc)
  end.
CoFixpoint trace_map {A B : Type} (f : A -> B) (trc : trace A) : trace B :=
  roll (trace_mapF f (trace_map f) (unroll trc)).
(* end details *)

Fixpoint find_k A n (k : seq (nat * Behav A)) : Behav A :=
  match k with
  | [::] => b_bot
  | h :: t => if h.1 == n then h.2 else find_k n t
  end.

Inductive b_prefix A :=
| p_act (a : A) T (K : T -> Behav A)
| p_end.

Definition b_run A (b : Behav A) : b_prefix A :=
  match b_unroll b with
  | b_act AT a kL => @p_act _ a (sumT AT) (fun x => find_k (sumT_alt AT x) kL)
  | _ => p_end A
  end.

Inductive lty_step p : LocalType -> event -> LocalType -> Prop :=
| lt_send a kL (T : AltT) (x : T) :
    lact a == a_send ->
    lty_step p (b_act T a kL) (mk_ev a_send p (lsubj a) T) (find_k (sumT_alt T x) kL)
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
| lt_recv a kL (T : AltT) (x : T) :
    lact a == a_recv ->
    lty_step p (b_act T a kL) (mk_ev a_recv (lsubj a) p T) (find_k (sumT_alt T x) kL)
=======
.
| lt_recv q T x kL :
    lty_step p (l_recv q T kL) (mk_ev a_recv q p T) (kL x)
>>>>>>> prova
=======
.
| lt_recv q T x kL :
    lty_step p (l_recv q T kL) (mk_ev a_recv q p T) (kL x)
=======
| lt_recv a kL (T : AltT) (x : T) :
    lact a == a_recv ->
    lty_step p (b_act T a kL) (mk_ev a_recv (lsubj a) p T) (find_k (sumT_alt T x) kL)
>>>>>>> Fixes to types/zooid
>>>>>>> CONFLICT NOT FIXED
=======
| lt_recv a kL (T : AltT) (x : T) :
    lact a == a_recv ->
    lty_step p (b_act T a kL) (mk_ev a_recv (lsubj a) p T) (find_k (sumT_alt T x) kL)
>>>>>>> more
.

Derive Inversion lty_step_inv with
    (forall p L0 Ev L1, @lty_step p L0 Ev L1) Sort Prop.

Inductive lty_lts_ (p : participant) (G : ty_trace -> LocalType -> Prop)
    : ty_trace -> LocalType -> Prop :=
  | ty_end TRC L :
      b_unroll L = b_end ->
      unroll TRC = tr_end -> @lty_lts_ p G TRC L
  | ty_next E TRC0 TRC1 L0 L1 :
      unroll TRC0 = tr_next E TRC1 ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      @lty_step p (b_unroll L0) E L1 -> G TRC1 L1 -> @lty_lts_ p G TRC0 L0
.

Derive Inversion lty_lts_inv with
    (forall p G TRC L, @lty_lts_ p G TRC L) Sort Prop.
Definition lty_accepts p := paco2 (lty_lts_ p) bot2.

<<<<<<< HEAD
Lemma lty_lts_monotone p : monotone2 (lty_lts_ p).
Proof.
  move=>TRC L r r' H0 H1;  case: H0.
  - by move=> TRC0 U0; constructor.
<<<<<<< HEAD
  - by move=> E0 TRC0 TRC1 L0 L1 U0 ST /H1; apply (ty_next _ _ _ U0).
=======
    - by move=> E0 TRC0 TRC1 L0 L1 U0 ST /H1; apply (ty_next _ _ _ U0).
>>>>>>> Fixes to types/zooid
Qed.
=======
(*LG: comment to try out git.*)
>>>>>>> prova
=======
=======
>>>>>>> CONFLICT NOT FIXED
      @lty_step p (run_lty L0) E L1 -> G TRC1 L1 -> @lty_lts_ p G TRC0 L0
  .
  Derive Inversion lty_lts_inv with
      (forall p G TRC L, @lty_lts_ p G TRC L) Sort Prop.
  Definition lty_accepts p := paco2 (lty_lts_ p) bot2.

  Lemma lty_lts_monotone p : monotone2 (lty_lts_ p).
  Proof.
    move=>TRC L r r' H0 H1;  case: H0.
    - by move=> TRC0 U0; constructor.
    - by move=> E0 TRC0 TRC1 L0 L1 U0 ST /H1; apply (ty_next _ _ _ U0).
  Qed.
<<<<<<< HEAD
>>>>>>> git works
=======
=======
=======
>>>>>>> more
      @lty_step p (b_unroll L0) E L1 -> G TRC1 L1 -> @lty_lts_ p G TRC0 L0
.
Derive Inversion lty_lts_inv with
    (forall p G TRC L, @lty_lts_ p G TRC L) Sort Prop.
Definition lty_accepts p := paco2 (lty_lts_ p) bot2.

(* Proof that LTS_ is monotone *)
Lemma lty_lts_monotone p : monotone2 (lty_lts_ p).
Proof.
  move=>TRC L r r' H0 H1;  case: H0.
  - by move=> TRC0 U0; constructor.
    - by move=> E0 TRC0 TRC1 L0 L1 U0 ST /H1; apply (ty_next _ _ _ U0).
Qed.
<<<<<<< HEAD
>>>>>>> Fixes to types/zooid
>>>>>>> CONFLICT NOT FIXED
=======
>>>>>>> more
