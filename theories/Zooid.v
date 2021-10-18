(** printing nat %\ensuremath{\mathbb{N}}% #&#8469;# *)
(** printing -> %\ensuremath{\to}% #&#8594;$ *)

(* begin hide *)
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.


Require Import Utils.ZooidTac.

Set Implicit Arguments.
Set Primitive Projections.
(* end hide *)

(** * Act II: Smol-Zooid: multiparty with shallower embedding  *)



(** ** Preliminaries

Deep embeddings lead to complex complex binder mechanisations. Can shallow
embeddings of binders help mechanising a small process language?

*)


(** ** Smol Zooid *)

(** This is a small process language *)

(* begin details: participant identifiers are natural numbers *)

Definition participant := Int63.int.

Lemma int_eqP : Equality.axiom Int63.eqb.
Proof.
  move=>x y; case: (boolP (x =? y)%int63).
  - by move=>/eqb_correct->; constructor.
  - by move=>/negP-H; constructor=>/eqb_complete/H.
Qed.

(* end details *)

(** We introduce a typing discipline for [proc], to constraint the kinds of
 traces that are allowed by the process. This typing discipline uses *local
 types* from Multiparty Session Types to categorise processes according to the
 set of traces that they accept. For this tutorial, we simplified the local
 types so they do not accept choices. **)

(** The typing system relates [proc] with [lty] so [proc] can only take a
communication type, if the specification allows it: **)

Section LocalTypes.
  Inductive ltyF G :=
  | l_end
  | l_bot
  | l_send (p : participant) T (kL : T -> G)
  | l_recv (p : participant) T (kL : T -> G)
  .

  CoInductive lty := mk_lty { run_lty : ltyF lty }.
End LocalTypes.

Arguments l_end {G}.
Arguments l_bot {G}.
Arguments l_send {G}.
Arguments l_recv {G}.
Declare Scope lty_scope.
Delimit Scope lty_scope with lty.
Bind Scope lty_scope with lty.
Notation END := (mk_lty l_end).
Notation IMPOSSIBLE := (mk_lty l_bot).
Notation "X '<-' p '!!' T ';;' k" := (mk_lty (l_send p T (fun X => k)))
        (at level 60, right associativity) : lty_scope.
Notation "X '@@' P '<-' p '!!' T ';;' K" :=
  (mk_lty
      (l_send p T (fun X =>
                     match X with
                     | P => K
                     | _ => mk_lty l_bot
                     end)))
    (at level 60, P pattern, right associativity) : lty_scope.
Notation "X '<-' p '??' T ';;' K" :=
  (mk_lty
     (l_recv p T (fun X => K)))
    (at level 60, right associativity) : lty_scope.

Section Processes.
  Context (E : Type -> Type).

  Notation CAN_SEND p T kL L := (run_lty L = l_send p T kL).
  Notation CAN_RECV p T kL L := (run_lty L = l_recv p T kL).

  Notation IS_SEND := (@erefl _ (l_send _ _ _)).
  Notation IS_RECV := (@erefl _ (l_recv _ _ _)).

  Inductive msg L : forall T, (T -> lty) -> Type :=
  | Send p T  (x : T) kL (H : CAN_SEND p T kL L) : @msg L unit (fun=>kL x)
  | Recv p T          kL (H : CAN_RECV p T kL L) : @msg L T    kL
  (* Silent action *)
  | Eff T (e : E T) : @msg L T (fun=> L)
  .

  Notation CAN_END L := (run_lty L = l_end).
  Notation IS_END := (@erefl _ l_end).

  Inductive procF (X : lty -> Type) (L : lty) :=
  | Inact (_ : CAN_END L)
  | Tau (k : X L)
  | Do {T kL} (e : @msg L T kL) (k : forall x, X (kL x))
  .
End Processes.

Notation CAN_SEND p T kL L := (run_lty L = l_send p T kL).
Notation CAN_RECV p T kL L := (run_lty L = l_recv p T kL).
Notation IS_SEND := (@erefl _ (l_send _ _ _)).
Notation IS_RECV := (@erefl _ (l_recv _ _ _)).
Notation CAN_END L := (run_lty L = l_end).
Notation IS_END := (@erefl _ l_end).

CoInductive proc E L := mk_proc { observe : @procF E (proc E) L }.
Definition iproc E L := procF E (proc E) L.

Arguments mk_proc & [E L] observe.
Arguments Send & {E L} p {T} x {kL} H.
Arguments Recv & {E L} p {T kL} H.
Arguments Eff & {E L T} e.
Arguments Inact & {E X L}.
Arguments Tau & {E X L } k.
Arguments Do & {E X L T kL} e k.

(** This defines processes ([proc]) with _shallow_ embeddings of binders.
Particularly, this uses regular Coq binders and functions for expressions, and
requires building greatest fixpoints for recursion. *)

Coercion mkProc E L (x : iproc E L) := mk_proc x.

Definition pInact E L (H : CAN_END L) : proc E L := mk_proc (Inact H).
Definition pTau E L (k : proc E L) : proc E L := mk_proc (Tau k).
Definition pDo E L T kL (e : @msg E L T kL) k : proc E L := mk_proc (Do e k).
Definition pSend E L p T x kL (H : CAN_SEND p T kL L) k : proc E L := pDo (Send p x H) k.
Definition pRecv E L p T kL (H : CAN_RECV p T kL L) k : proc E L := pDo (Recv p H) k.
Arguments pInact & {E L}.
Arguments pTau & {E L} k.
Arguments pDo & {E L T kL} e k.
Arguments pSend & {E L} p {T} x {kL} H k.
Arguments pRecv & {E L} p T {kL} H k.

Declare Scope proc_scope.
Notation stop := (pInact erefl).
Notation "'call' K" := (pTau K) (at level 60, no associativity).
Notation "p '<~' x ';;' k" :=
  (pSend p x IS_SEND (fun=> k))
    (at level 60, right associativity) : proc_scope.
Notation "x ':' T '::=' '<~' p ';;' k" :=
  (pRecv p T IS_RECV (fun x => k))
    (at level 60, right associativity) : proc_scope.
Notation "x ':' T '::=' 'lift' e ';;' k" :=
  (pDo (Eff e) (fun (x : T) => k))
    (at level 60, right associativity) : proc_scope.

Section ProcExamples.
  Context (E : Type -> Type).
  Notation process := (proc E).
  Example ended_proc : process END := stop.

  (* begin hide *)
  Definition Alice := 0%int63.
  Definition Bob := 1%int63.
  (* end hide *)

  (* begin details: here we define the specifications that ALICE and BOB
  must satisfy *)

  Open Scope lty_scope.
  Example NRAlice : lty :=
    _ <- Bob !! nat ;;
    _ <- Bob ?? nat ;;
    END.

  Example NRBob : lty :=
    _ <- Alice ?? nat ;;
    _ <- Alice !! nat ;;
    END.

  Example AliceSpec : lty :=
    cofix X :=
      _ <- Bob !! nat ;;
      _ <- Bob ?? nat ;;
      X.

  Example BobSpec : lty :=
    cofix X :=
      _ <- Alice ?? nat ;;
      _ <- Alice !! nat ;;
      X.
  Close Scope lty_scope.

  Open Scope proc_scope.
  Example ping_Alice : process NRAlice :=
    Bob <~ 0;;
      _ : nat ::= <~ Bob;;
    stop.
  Example ping_Bob : process NRBob :=
    n : nat ::= <~ Alice ;;
    Alice <~ n ;;
    stop.

  Example infinite_ping_Alice : nat -> process AliceSpec :=
    cofix pingpong x :=
      Bob <~ x;;
      _ : nat ::= <~ Bob;;
      pingpong x.+1.

  Example infinite_ping_Bob : process BobSpec :=
    cofix pingpong :=
      n : nat ::= <~ Alice;;
      Alice <~ n;;
      pingpong.

  Example infinite_ping_Bob0 : process BobSpec :=
    n : nat ::= <~ Alice;;
    cofix pingpong :=
      Alice <~ n;;
      n : nat ::= <~ Alice;;
      pingpong.
  Close Scope proc_scope.
End ProcExamples.

(** ** Semantics of Smol Zooid *)

(** *** Actions **)

(** Actions capture the kind of event that happened (send/receive), and the
necessary information about who performed the action, the other party, and the
payload type. **)


Inductive action := a_send | a_recv.
Record event :=
  mk_ev { action_type : action;
          from : participant;
          to : participant;
          payload_type : Type;
        }.
Inductive rt_event :=
  Obs { event_type : event;
        payload : payload_type event_type
      }.
Definition mk_obs a p q T x := Obs (mk_ev a p q T) x.


(* begin hide *)
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
(* end hide *)


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
Definition rt_trace := trace rt_event.

(* begin details:  *)

Definition trace_mapF {A B : Type} (f : A -> B) X Y G (trc : traceF A X)
  : traceF B Y :=
  match trc with
  | tr_end => tr_end
  | tr_next a trc => tr_next (f a) (G trc)
  end.
CoFixpoint trace_map {A B : Type} (f : A -> B) (trc : trace A) : trace B :=
  roll (trace_mapF f (trace_map f) (unroll trc)).

Definition erase := trace_map event_type.
(* end details *)



(** *** Labelled State Transition System **)

(** We define the steps as functions that take a process, an action, and
attepmpts to run it, returning the continuation. Since we only care about
communication, we define a function that exposes the firsst communication
action: [p_unroll]. This function requires two parameters, [readIO : forall T :
type, unit -> interp_type T] and [writeIO : forall T, T -> unit]. We will use
these functions later for code extraction. **)

Section ProcLTS.
  (** begin details: **)
  Variable (E : Type -> Type)
           (run_eff : forall T, E T -> T).
  (** end details **)

  Inductive proc_step (p : participant) L :
    iproc E L -> option rt_event -> forall L', proc E L' -> Prop
    :=
    (* Observable actions *)
    | step_send q T (x : T) kL (WT : CAN_SEND q T kL L) k :
        proc_step p (Do (Send q x WT) k) (Some (mk_obs a_send p q x)) (k tt)
    | step_recv q T (x : T) kL (WT : CAN_RECV q T kL L) k :
        proc_step p (Do (Recv q WT  ) k) (Some (mk_obs a_recv q p x)) (k x )

    (* Silent actions *)
    | step_eff T a k : proc_step p (Do (Eff a) k) None (k (@run_eff T a))
    | step_unroll e0 : proc_step p (Tau e0)       None e0
  .

  Derive Inversion proc_step_inv
    with (forall p L0 e0 ev L1 e1, @proc_step p L0 e0 ev L1 e1)
         Sort Prop.

  Definition R_trace := rt_trace -> forall L, proc E L -> Prop.
  Inductive proc_lts_ (p : participant) (G : R_trace) : R_trace :=
  | p_end TRC e H :
      unroll TRC = tr_end ->
      observe e = Inact H ->
      @proc_lts_ p G TRC END e
  | p_skip TRC L0 e0 L1 e1 :
      @proc_step p L0 (observe e0) None L1 e1 ->
      @proc_lts_ p G TRC L1 e1 ->
      @proc_lts_ p G TRC L0 e0
  | p_next E TRC0 TRC1 L0 e0 L1 e1 :
      unroll TRC0 = tr_next E TRC1 ->
      @proc_step p L0 (observe e0) (Some E) L1 e1 ->
      G TRC1 L1 e1 ->
      @proc_lts_ p G TRC0 L0 e0
  .
  Arguments p_end {p G}.
  Arguments p_skip [p G TRC L0 e0 L1 e1].
  Arguments p_next [p G E TRC0 TRC1 L0 e0 L1 e1].
  Derive Inversion proc_lts_inv
    with (forall p G TRC L e, @proc_lts_ p G TRC L e) Sort Prop.

  Lemma proc_lts_monotone p : monotone3 (proc_lts_ p).
  (* begin details: [proc_lts_] is monotone *)
  Proof.
    move=> TRC L e R R'.
    elim=>
    [ {}TRC {}e EQ H0 H1 _
    | {}TRC L0 e0 L1 e1 STEP H IH F
    | ev TRC0 TRC1 L0 e0 L1 e1 EQ STEP H F].
    - by apply/p_end.
    - by apply/(p_skip STEP)/IH.
    - by apply/(p_next EQ STEP)/F.
  Qed.
  (* end details *)

  (** [proc_accepts] encodes the property of a process accepting a trace, and it
 is the greatest fixpoint of [proc_lts_]. **)

  Definition proc_accepts p TR L P := paco3 (proc_lts_ p) bot3 TR L P.

  (** ** Preservation **)

  (** We want to make sure that types indeed characterise the traces according to
the allowed traces. We build a semantics for local types, and prove that, given
[p : SZooid L], if [p] transitions to [p'] with some event [E], then [L] also
transitions to [L'] with the "same" event. But, since processes contain payloads
and local types do not, we must first erase these payloads from the trace
events. **)

  Inductive lty_step p : ltyF lty -> event -> lty -> Prop :=
  | lt_send q T x kL :
      lty_step p (l_send q T kL) (mk_ev a_send p q T) (kL x)
  | lt_recv q T x kL :
      lty_step p (l_recv q T kL) (mk_ev a_recv q p T) (kL x)
  .
  Derive Inversion lty_step_inv with
      (forall p L0 Ev L1, @lty_step p L0 Ev L1) Sort Prop.

  Inductive lty_lts_ (p : participant) (G : ty_trace -> lty -> Prop)
    : ty_trace -> lty -> Prop :=
  | ty_end TRC L :
      run_lty L = l_end ->
      unroll TRC = tr_end -> @lty_lts_ p G TRC L
  | ty_next E TRC0 TRC1 L0 L1 :
      unroll TRC0 = tr_next E TRC1 ->
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

  Lemma subject_reduction p L0 (e0 : iproc E L0) L1 (e1 : proc E L1) ev :
    proc_step p e0 (Some ev) e1 -> lty_step p (run_lty L0) (event_type ev) L1.
  Proof.
    (* Generalize [Some ev] and remember that [EQ : mev = Some ev] in [St] *)
    move EQ: (Some ev)=> mev St.

    (* By case analysis on the process step *)
    by case: St EQ=>//= q T x kL -> _ [->]; constructor.
  Qed.

  Lemma step_silent p L0 (e0 : iproc E L0) L1 (e1 : proc E L1) :
    proc_step p e0 None e1 -> L0 = L1.
  Proof. by case EQ: _ _ _ /.  Qed.

  Theorem trace_soundness p RT_TRC L (e : proc E L) :
    proc_accepts p RT_TRC         e ->
    @lty_accepts p (erase RT_TRC) L.
  Proof.
    (* By (parametric) coinduction (i.e. paco2_acc) *)
    coind CH=> L RT_TRC e Acc.

    (* unfold proc_accepts proc_accepts = \mu proc_lts_ ==> proc_lts_ (\mu proc_lts) *)
    move: Acc => /(paco3_unfold (@proc_lts_monotone p))-Acc.

    (* generalize Acc *)
    move EQ: (upaco3 _ _) Acc=> RR.

    (* by induction on Acc *)
    elim=>/=
        [ TRC0 e0 H0 U0 Oe
        | TRC L0 e0 L1 e1 STEP _ IH
        | E0 T0 T1 L0 e0 L1 e1 U0 St Acc {e}
        ].
    { (* Case: process trace is ended *)

      (* apply G f -> f (G f), followed by the empty trace constructor *)
      apply/paco2_fold; constructor=>//.

      (* reduce [unroll (erase TRC0)], and rewrite [unroll TRC0 = tr_end] *)
      by cbv; rewrite U0.
    }
    { (* Case: the process takes a silent step *)

      (* Straightforward application of the IH, since
         a silent step does not progress the local type *)
      by move: STEP=>/step_silent->.
    }
    { (* Case: process trace contains one element *)

      (* By applying the constructor for the step trace, we
       then need to prove 3 properties: *)
      apply/paco2_fold/ty_next.

      { (* Property 1: the erasure of the runtime trace contains 1 element *)

        (* Straightforward: if the trace contains one element, so does the erasure *)
        by cbv; rewrite U0 -/(trace_map _ _) -/(erase _).
      }
      { (* Property 2: the local type of [e0] steps to some continuation local type *)

        (* Straightforward by subject reduction *)
        by apply: (subject_reduction St).

      }
      { (* Property 3: the continuation of the local type accepts the remainder
           of the erasure of the trace *)

        (* Straightforward by applying the coinduction hypothesis *)

        (* First rewrite [Acc] so it states that [e1] accepts the remainder of
           the trace [T1]*)
        move: EQ Acc=><-[Acc|//] {RR}.

        (* Then apply the coinduction hypothesis to [Acc] *)
        by right; apply/CH/Acc.
      }
    }
    Qed.
End ProcLTS.

(** ** Extraction **)

(** The main goal of defining a simple process language, with a mixture of deep
and shallow embedded binders is to simplify *certified code extraction*. To
extract [proc], we need an interpretation of its constructs. We do this in a way
that somewhat resembles that of _effect handlers_, by assigning to each
construct an **interpretation** as an OCaml function. **)

Require Extraction ExtrOCamlInt63.
Extraction Implicit Send [ L kL ].
Extraction Implicit Recv [ L kL ].
Extraction Implicit Eff [ L ].
Extraction Implicit Do [ L kL ].
Extraction Implicit Tau [ L ].
Extraction Implicit Inact [ L ].

Extraction Implicit pSend [ L kL ].
Extraction Implicit pRecv [ L kL ].
Extraction Implicit pDo [ L kL ].
Extraction Implicit pTau [ L ].
Extraction Implicit pInact [ L ].

Module ProcExtraction.
  Extract Inductive proc => "Proc.t" [ "" ].
  Extract Inlined Constant pSend => "(fun p t k -> let* _ = Proc.send p (Obj.magic t) in (Obj.magic k tt))".
  Extract Inlined Constant pRecv => "(fun p k -> let* x = Proc.recv p in (Obj.magic k))".
End ProcExtraction.

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

  Definition mk_rec A (B : Behav A) :=
    match B with
    | b_end => b_end
    | b_var 0 => b_end
    | _ => b_rec B
    end.

  Fixpoint project (G : GlobalType) r : LocalType :=
    match G with
    | b_end => b_end
    | b_bot => b_bot
    | b_var t1 => b_var t1
    | b_rec G1 => mk_rec (project G1 r)
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


