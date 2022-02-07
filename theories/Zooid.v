(** printing nat %\ensuremath{\mathbb{N}}% #&#8469;# *)
(** printing -> %\ensuremath{\to}% #&#8594;$ *)

(* begin hide *)
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.


Require Import Utils.ZooidTac.
Require Import Zooid2.Types.


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


(** We introduce a typing discipline for [proc], to constraint the kinds of
 traces that are allowed by the process. This typing discipline uses *local
 types* from Multiparty Session Types to categorise processes according to the
 set of traces that they accept. For this tutorial, we simplified the local
 types so they do not accept choices. **)

(** The typing system relates [proc] with [lty] so [proc] can only take a
communication type, if the specification allows it: **)

Section Processes.
  Context (E : Type -> Type).

  Notation CAN_SEND p T kL L := (b_run L = @p_act lprefix (mk_lprefix a_send p) T kL).
  Notation CAN_RECV p T kL L := (b_run L = @p_act lprefix (mk_lprefix a_recv p) T kL).

  Notation IS_SEND := (@erefl _ (@p_act _ (mk_lprefix a_send _) _ _)).
  Notation IS_RECV := (@erefl _ (@p_act _ (mk_lprefix a_recv _) _ _)).

  Inductive msg L : forall T, (T -> LocalType) -> Type :=
  | Send p A  (x : A) kL (H : CAN_SEND p A kL L) : @msg L unit (fun=> kL x)
  | Recv p A          kL (H : CAN_RECV p A kL L) : @msg L A    kL
  (* Silent action *)
  | Eff T (e : E T) : @msg L T (fun=> L)
  .

  Notation CAN_END L := (b_run L = p_end _).
  Notation IS_END := (@erefl _ (p_end _)).

  Inductive procF (X : LocalType -> Type) (L : LocalType) :=
  | Inact (_ : CAN_END L)
  | Tau (k : X L)
  | Do {T kL} (e : @msg L T kL) (k : forall x, X (kL x))
  .
End Processes.

Notation CAN_SEND p T kL L := (b_run L = @p_act lprefix (mk_lprefix a_send p) T kL).
Notation CAN_RECV p T kL L := (b_run L = @p_act lprefix (mk_lprefix a_recv p) T kL).

Notation IS_SEND := (@erefl _ (@p_act _ (mk_lprefix a_send _) _ _)).
Notation IS_RECV := (@erefl _ (@p_act _ (mk_lprefix a_recv _) _ _)).

Notation CAN_END L := (b_run L = p_end _).
Notation IS_END := (@erefl _ (p_end _)).

CoInductive proc E L := mk_proc { observe : @procF E (proc E) L }.
Definition iproc E L := procF E (proc E) L.

Arguments mk_proc & [E L] observe.
Arguments Send & {E L} p {A} x {kL} H.
Arguments Recv & {E L} p {A kL} H.
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
  Eval compute in b_unroll (b_rec (b_var 1)).
  Example ended_proc : process (b_rec b_end) := stop.

  (* begin hide *)
  (* Definition Alice := 0%int63. *)
  (* Definition Bob := 1%int63. *)
  (* end hide *)

  (* begin details: here we define the specifications that ALICE and BOB
  must satisfy *)
  Definition NRAlice := project GTYExamples.PP GTYExamples.Alice.
  Definition NRBob := project GTYExamples.PP GTYExamples.Bob.

  Open Scope proc_scope.
  Example ping_Alice : process NRAlice
    := GTYExamples.Bob <~ 0;;
       _ : bool ::= <~ GTYExamples.Bob;;
       stop.

  Example ping_Bob : process NRBob :=
    n : nat ::= <~ GTYExamples.Alice ;;
    GTYExamples.Alice <~ true ;;
    stop.

  (* Example NRAlice : lty := *)
  (*   _ <- Bob !! nat ;; *)
  (*   _ <- Bob ?? nat ;; *)
  (*   END. *)

  (* Example NRBob : lty := *)
  (*   _ <- Alice ?? nat ;; *)
  (*   _ <- Alice !! nat ;; *)
  (*   END. *)

  (* Example AliceSpec : lty := *)
  (*   cofix X := *)
  (*     _ <- Bob !! nat ;; *)
  (*     _ <- Bob ?? nat ;; *)
  (*     X. *)

  (* Example BobSpec : lty := *)
  (*   cofix X := *)
  (*     _ <- Alice ?? nat ;; *)
  (*     _ <- Alice !! nat ;; *)
  (*     X. *)
  (* Close Scope lty_scope. *)

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

Section GTYExamples.
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
