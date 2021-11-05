Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.


Require Import Utils.ZooidTac.
Require Export Zooid2.Zooid.

Set Implicit Arguments.
Set Primitive Projections.

Section SumTypes.
  Definition smap T := seq (nat * T).
  Definition lookupF T Lfp (L : smap T) (n : nat) : seq T :=
    match L with
    | [::] => [::]
    | h :: t => if h.1 == n then h.2 :: Lfp t n else Lfp t n
    end.
  Fixpoint slookup {T} L := @lookupF T (@slookup T) L.

  Definition T_of_seq A (x : A) (s : seq A) : A :=
    match s with
    | [:: h] => h
    | _ => x
    end.

  Definition lookup L n : Type := @T_of_seq Type False (slookup L n).

  Unset Primitive Projections.
  Record SumT L : Type :=
    MkSum
      { inj_n : nat;
        ty_n : lookup L inj_n;
      }.

  Record Sum :=
    { S :> Type;
      Alts : smap Type;
      S_from : SumT Alts -> S;
      S_to : S -> SumT Alts;
      S_ft : S_from \o S_to =1 id;
      S_tf : S_to \o S_from =1 id
    }.

  Definition alt_f K (f : nat -> option K) {X : Sum} (x : X) : option K
    := (f (inj_n (@S_to _ x))).
End SumTypes.

Arguments MkSum & {L} inj_n ty_n.

Definition Asum_from A B (k : SumT [:: (0, A); (1, B)]) : A + B :=
  match k with
  | MkSum 0 x => inl x
  | MkSum 1 x => inr x
  | MkSum _ x => match x with end
  end.

Definition Asum_to A B (k : A + B) : SumT [:: (0, A); (1, B)] :=
  match k with
  | inl x => MkSum 0 x
  | inr x => MkSum 1 x
  end.

Lemma Asum_ft A B (x : A + B) : Asum_from (Asum_to x) = x.
Proof. by case: x. Qed.

Lemma Asum_tf A B (x : SumT [:: (0, A); (1, B)]) : Asum_to (Asum_from x) = x.
Proof. by move: x; do ! case=>//. Qed.

Definition ISum A B : Sum :=
  {| S := A + B;
     Alts := [:: (0, A); (1, B)];
     S_from := @Asum_from A B;
     S_to := @Asum_to A B;
     S_ft := @Asum_ft A B;
     S_tf := @Asum_tf A B;
   |}.

Record AltT (altsT : seq nat) :=
  MkAltT
    { sumT  :> Type;
      sumT_alt : sumT -> nat;
      _ : forall x, sumT_alt x \in altsT;
    }.

Section StandardGlobalTypes.

  Unset Elimination Schemes.
  Inductive Behav A :=
  | b_bot
  | b_end
  | b_var (t : nat)
  | b_rec (G : Behav A)
  | b_act L (AT : AltT L) (a : A) (k : seq (nat * Behav A))
  .
  Set Elimination Schemes.
  Arguments b_end & {A}.
  Arguments b_bot & {A}.
  Arguments b_var & {A} t.
  Arguments b_rec & {A} G.
  Arguments b_act & {A L} AT a k.

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
        (P_msg : forall L AT a k,
            AllT P [seq x.2 | x <- k] ->
            P (@b_act _ L AT a k))
    : forall G, P G.
  Proof.
    fix Ih 1.
    move=>[||t|G|L AT a k].
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
        (P_msg : forall L AT a k,
            AllT P [seq x.2 | x <- k] ->
            P (@b_act _ L AT a k))
    : forall G, P G.
  Proof.
    by elim/Behav_rect.
  Qed.

  Fixpoint choice_wf b T L (S : AltT L) (k : seq (nat * T)) :=
    match k with
    | [::] => b
    | h :: t => (h.1 \in L) && (h.1 \notin [seq x.1 | x <- t]) && choice_wf true S t
    end.

  Definition is_rec A (B : Behav A) :=
    match B with
    | b_rec _ => true
    | _ => false
    end.

  Fixpoint behav_wf A d (B : Behav A) :=
    match B with
    | b_bot => false
    | b_end => true
    | b_var t => t < d
    | b_rec B => ~~ is_rec B && behav_wf d.+1 B
    | b_act L AT a k =>
      choice_wf false AT k &&
      all (fun x => behav_wf d x.2) k
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
    | b_act S1 _ a1 k1, b_act S2 _ a2 k2 =>
      (S1 == S2) && (a1 == a2) && all_eq (@eq_Behav A) k1 k2
    | _, _ => false
    end.

  (* Lemma Behav_eqP A : Equality.axiom (@eq_Behav A). *)
  (* Proof with try (by []); try (by constructor); try (by constructor=>[][]). *)
  (*   elim=>[||t1|G1 Ih|S1 a1 k1 Ih] [||t2|G2|S2 a2 k2]/=... *)
  (*   - case: eqP=>[->|F]... *)
  (*   - case: Ih=>[->|F]... *)
  (*   - do ! (case: eqP=>[->|F]/=)... *)
  (*     elim: k1 k2 Ih =>[|[l1 G1] t1 IHk] [|[l2 G2] t2]/=... *)
  (*     move=>[Ih1 /IHk-Ih2]. *)
  (*     case: eqP=>[->|F]/=... *)
  (*     case: Ih1=>[->|F]/=... *)
  (*     case: Ih2=>[[->]|F]/=... *)
  (*     by constructor=>[[F']]; move: F' F=>->. *)
  (* Qed. *)

  (* Definition Behav_eqMixin A := EqMixin (@Behav_eqP A). *)
  (* Canonical Behav_eqType (A : eqType) := *)
  (*   Eval hnf in EqType (Behav A) (Behav_eqMixin A). *)

  (*free vars and closedness*)

  Fixpoint b_fvars_aux A c (B : Behav A) :=
    match B with
    | b_bot => [::]
    | b_end => [::]
    | b_var t => if c <= t then [:: t] else [::]
    | b_rec B1 => b_fvars_aux (c.+1) B1
    | b_act _ S a k => flatten (map (fun x=> b_fvars_aux c x.2) k)
    end.

  Definition b_fvars A (B : Behav A) := b_fvars_aux 0 B.

  Definition b_closed A (B : Behav A) := b_fvars B == [::].

  (*free from bot*)

  Fixpoint no_bot A (B : Behav A):=
    match B with
    | b_bot => false
    | b_end => true
    | b_var t => true
    | b_rec B1 => no_bot B1
    | b_act _ S a k => all (fun x => no_bot (x.2)) k
    end.


  Fixpoint b_shift A c (B : Behav A) :=
    match B with
    | b_var t => if t < c then B else b_var t.+1
    | b_act _ S a k => b_act S a [seq (x.1, b_shift c x.2) | x <- k]
    | b_rec G => b_rec (b_shift c.+1 G)
    | b_end => B
    | b_bot => B
    end.

  Fixpoint b_subst A v (B' B : Behav A) :=
    match B with
    | b_var t => if v == t then B' else B
    | b_act _ S a k => b_act S a [seq (x.1, b_subst v B' x.2) | x <- k]
    | b_rec G => b_rec (b_subst v.+1 (b_shift 0 B') G)
    | b_end => B
    | b_bot => B
    end.

  Definition b_unroll A (B : Behav A) :=
    match B with
    | b_rec B' => b_subst 0 B B'
    | _ => B
    end.

  Record gprefix :=
    mk_gprefix { gfrom : participant;
                 gto : participant
               }.

  Definition gprefix_eq g1 g2 :=
    Int63.eqb (gfrom g1) (gfrom g2) &&
    Int63.eqb (gto g1) (gto g2).

  Lemma gprefix_eqP : Equality.axiom gprefix_eq.
  Proof with try (by constructor); try (by constructor=>[[]]).
    move=>[f1 t1] [f2 t2]; rewrite /gprefix_eq/=.
    do ! case: int_eqP=>[->|F]...
  Qed.
  Definition gprefix_eqMixin := EqMixin gprefix_eqP.
  Canonical gprefix_eqType := Eval hnf in EqType gprefix gprefix_eqMixin.

  Definition GlobalType := Behav gprefix.

  Record lprefix :=
    mk_lprefix { lact : action;
                 lsubj : participant
               }.
  Definition lprefix_eq l1 l2 :=
    Int63.eqb (lsubj l1) (lsubj l2) &&
    (lact l1 == lact l2).

  Lemma lprefix_eqP : Equality.axiom lprefix_eq.
  Proof with try (by constructor); try (by constructor=>[[]]).
    move=>[f1 t1] [f2 t2]; rewrite /lprefix_eq/=.
    case: int_eqP=>[->|F]...
    case: eqP=>[->|F]...
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
    | b_act _ S1 a1 k1 =>
      (gfrom a1) :: ((gto a1) :: flatten (map (fun x => (g_part x.2)) k1) )
    end.



  Definition guard b (L : LocalType) :=
    if b then L else b_bot.

  Definition labels (k : seq (nat * LocalType)) := [seq x.1 | x <- k].


  Fixpoint remove n (k : seq (nat * LocalType)) :=
    match k with
    | [::] => [::]
    | h :: t => if h.1 == n then t
                else h :: remove n t
    end.

  Fixpoint find n (k : seq (nat * LocalType)) :=
    match k with
    | [::] => None
    | h :: t => if h.1 == n then Some h.2
                else find n t
    end.

  Definition merge_recv M :=
    fix mergeAll k1 k2 :=
      match k1 with
      | [::]  => k2
      | h1 :: t1 =>
        match find h1.1 k2 with
        | Some h2 => (h1.1, (M h1.2 h2)) :: mergeAll t1 (remove h1.1 k2)
        | None => h1 :: mergeAll t1 k2
        end
      end.

  Fixpoint merge (L1 L2 : LocalType) : LocalType :=
    match L1, L2 with
    | b_bot, _ => b_bot
    | _, b_bot => b_bot
    | b_rec L1, b_rec L2 => b_rec (merge L1 L2)
    | b_act S1 AT1 a1 k1, b_act S2 _ a2 k2 =>
      guard ((S1 == S2) && (a1 == a2))
            (if lact a1 == a_recv
             then b_act AT1 a1 (merge_recv merge k1 k2)
             else guard (all_eq (eq_Behav lprefix_eqType) k1 k2) (b_act AT1 a1 k1))
    | L1, L2 => guard (eq_Behav _ L1 L2) L1
    end.

  Definition merge_all (K : seq LocalType) :=
    match K with
    | [::] => b_bot
    | h :: K => foldl merge h K
    end.

  Definition proj_prefix (g : gprefix) r L S k : LocalType :=
    match Int63.eqb (gfrom g) r, Int63.eqb (gto g) r with
    | true , false => @b_act _ L S (mk_lprefix a_send (gto g)) k
    | false, true  => @b_act _ L S (mk_lprefix a_recv (gfrom g)) k
    | _    , _     => merge_all [seq x.2 | x <- k]
    end.

  (*Definition mk_rec A (B : Behav A) :=
    match B with
    | b_end => b_end
    | b_var 0 => b_end
    | _ => b_rec B
    end.*)

  Definition mk_rec A r (M: GlobalType -> participant -> Behav A) G:=
    if ((r \in (g_part G)) && (b_closed (b_rec G)) && (no_bot G))
    then b_end
    else b_rec (M G r).

  (*change boolean below*)

  Fixpoint project (G : GlobalType) r : LocalType :=
    match G with
    | b_end => b_end
    | b_bot => b_bot
    | b_var t1 => b_var t1
    | b_rec G1 => if ((r \notin (g_part G1)) && (b_closed (b_rec G1)) && (no_bot G1))
                  then b_end
                  else b_rec (project G1 r)
    | b_act _ S1 a1 k1 =>
      proj_prefix a1 r S1 [seq (x.1, project x.2 r) | x <- k1]
    end.

  Open Scope lty_scope.
  CoFixpoint unravel (L : LocalType) : lty
    := match b_unroll L with
       | b_end => END
       | b_act _ A a k =>
         match lact a with
         | a_send =>
           X <- lsubj a !! sumT A;;
           match find (sumT_alt A X) k with
           | Some LT => unravel LT
           | None => IMPOSSIBLE
           end
         | a_recv =>
           X <- lsubj a ?? sumT A;;
           match find (sumT_alt A X) k with
           | Some LT => unravel LT
           | None => IMPOSSIBLE
           end
         end
       | _ => IMPOSSIBLE
       end.
  Close Scope lty_scope.
End StandardGlobalTypes.


Definition single_choice (n : nat) T (x : T) := n.
Lemma single_choice_in n T : forall x : T, single_choice n x \in [:: n].
Proof.
  by rewrite /single_choice/=in_cons eq_refl.
Qed.

Definition altT n (T : Type) : AltT [:: n]
  := @MkAltT _ T (@single_choice n T) (@single_choice_in n T).

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
  @b_act _ _ (altT 0 T) (mk_gprefix p q) [:: (0, G)].
Notation "p '~>' q '$(' T ')' ';;' k" :=
  (b_msg p q T k)
        (at level 60, right associativity) : gty_scope.
Notation "p '~>' q '${' T '}' ';;' k" :=
  (@b_act _ _ T (mk_gprefix p q) k)
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

  Definition MyChoiceT : AltT [:: lbl1; lbl2].
    refine (@MkAltT _ MyChoice (fun x=>
                                  match x with
                                  | Case1 _ => lbl1
                                  | Case2 _ => lbl2
                                  end) _).
    case=>_.
    by rewrite in_cons eq_refl.
    by rewrite in_cons orbC in_cons eq_refl.
  Defined.

  Example CH1 :=
    REC {
      Alice ~> Bob ${ MyChoiceT } ;;
      [:: (lbl1, Bob ~> Alice $( bool );; JUMP 0);
          (lbl2, END)
      ]
      }.
  Close Scope gty_scope.

  Context (E : Type -> Type).
  Notation process G r := (proc E (unravel (project G r))).

  Example ended_proc : process END Alice := stop.

  Open Scope proc_scope.

  Definition proc_rec A E L (f : A -> proc E L) : A -> proc E L := f.
  Arguments proc_rec & {A E L} f.

  Set Contextual Implicit.

  Example ch_Bob0 : process CH1 Bob :=
    n : MyChoice ::= <~ Alice;;
    match n with
    | Case1 c =>
      proc_rec
        (cofix pingpong c :=
         Alice <~ Nat.even c;;
         n : MyChoice ::= <~ Alice;;
         match n with
         | Case1 c =>
           pingpong c
         | Case2 _ => stop
         end) c
    | Case2 _ =>
      stop
    end.
  Example ping_Bob : process PP Bob :=
      _ : nat ::= <~ Alice;;
    Alice <~ true;;
    stop.
  Example ping_Alice n : process PP Alice :=
    Bob <~ n ;;
    n : bool ::= <~ Bob ;;
    stop.

  Example infinite_ping_Alice : nat -> process PPRec Alice :=
    cofix pingpong x :=
      Bob <~ x;;
      _ : bool ::= <~ Bob;;
      pingpong x.+1.

  Example infinite_ping_Bob : process PPRec Bob :=
    cofix pingpong :=
      n : nat ::= <~ Alice;;
      Alice <~ Nat.even n ;;
      pingpong.

  Example infinite_ping_Bob0 : process PPRec Bob :=
    n : nat ::= <~ Alice;;
    cofix pingpong :=
      Alice <~ Nat.even n;;
      n : nat ::= <~ Alice;;
      pingpong.
  Close Scope proc_scope.
End GTYExamples.
