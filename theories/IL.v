From ILAL Require Import language tactics.
From Stdlib Require Import FunctionalExtensionality.

(** Triple definitions *)

(* There exists a starting state s satisfying P such that executing
   c under exit condition ex reaches s' *)
Definition post (ex : ExitCondition) (c : stmt) (P : prop) : prop :=
  (fun s' : state =>
    exists (s : state),
      P s /\ s =[ c ]=> ex | s').

Declare Scope ilogic_scope.
Open Scope ilogic_scope.

(* Every state satisfying Q is reachable from some state satisfying
   P by executing c under exit condition ex *)
Definition itriple (ex : ExitCondition) (P : prop) (c : stmt) (Q : prop) : Prop :=
  forall (s : state),
    Q s ->
    post ex c P s.
Notation "[[ P ]] c [[ ex | Q ]]" :=
  (itriple ex P c Q) (at level 90, c custom stmt at level 99) : ilogic_scope.
Notation "[[ P ]] c [[ ok | Q ]] [[ er | R ]]" :=
  (itriple ok P c Q /\ itriple er P c R) (at level 90, c custom stmt at level 99) : ilogic_scope.

Definition prop_impl (P Q : prop) : Prop :=
  forall (s : state), P s -> Q s.
Notation "P ->> Q" := (prop_impl P Q) (at level 80).

(** Generic Proof Rules of Incorrectness Logic *)
(* Fig. 2 *)

Theorem empty_under_approximates_inf :
  forall P C ex,
    [[P]] C [[ex | False]].
Proof.
  intros P C ex s Contra. contradiction.
Qed.

Theorem consequence_inf :
  forall P P' Q Q' C ex,
    P ->> P' ->
    [[P]]  C [[ex | Q]] ->
    Q' ->> Q ->
    [[P']] C [[ex | Q']].
Proof.
  intros P P' Q Q' C ex Impl1 Trip Impl2 s Q's.
  specialize (Impl2 s Q's).
  specialize (Trip s Impl2).
  destruct Trip as (s' & Ps' & Step).
  exists s'. split.
  - apply Impl1. assumption.
  - assumption.
Qed.

Theorem disjunction_inf :
  forall P1 P2 Q1 Q2 ex C,
    [[P1]] C [[ex | Q1]] ->
    [[P2]] C [[ex | Q2]] ->
    [[P1 \/ P2]] C [[ex | Q1 \/ Q2]].
Proof.
  intros P1 P2 Q1 Q2 ex C Left Right s [Q1s|Q2s].
  - (* Left *)
    specialize (Left s Q1s).
    destruct Left as (s' & P1s' & Step).
    exists s'. split.
    -- left. assumption.
    -- assumption.
  - (* Right *)
    specialize (Right s Q2s).
    destruct Right as (s' & P2s' & Step).
    exists s'. split.
    -- right. assumption.
    -- assumption.
Qed.

Theorem unit_ok_inf :
  forall P,
    [[P]] skip [[ok | P]].
Proof.
  intros P s Ps. exists s.
  split.
  - assumption.
  - constructor.
Qed.

Theorem unit_er_inf :
  forall P,
    [[P]] skip [[er | False]].
Proof.
  intros P s Contra. contradiction.
Qed.

Theorem unit_inf :
  forall P,
    [[P]] skip [[ok | P]][[er | False]].
Proof.
  intros. split.
  - apply unit_ok_inf.
  - apply unit_er_inf.
Qed.

Theorem seq_short_circuit_inf :
  forall P R C1 C2,
    [[P]] C1 [[er | R]] ->
    [[P]] C1 ;; C2 [[ er | R]].
Proof.
  intros P R C1 C2 Trip s Rs.
  specialize (Trip s Rs).
  destruct Trip as (s' & Ps' & Step).
  exists s'. split.
  - assumption.
  - constructor. assumption.
Qed.

Theorem seq_inf :
  forall P Q R C1 C2 ex,
    [[P]] C1 [[ok | Q]] ->
    [[Q]] C2 [[ex | R]] ->
    [[P]] C1 ;; C2 [[ex | R]].
Proof.
  intros P Q R C1 C2 ex Left Right s Rs.
  specialize (Right s Rs).
  destruct Right as (s' & Qs' & Rstep).
  specialize (Left s' Qs').
  destruct Left as (s'' & Ps'' & Lstep).
  exists s''. split.
  - assumption.
  - econstructor; eassumption.
Qed.

Theorem star_zero_inf :
  forall P C,
    [[P]] C** [[ok | P]].
Proof.
  intros P C s Ps.
  exists s. split.
  - assumption.
  - constructor.
Qed.

Theorem star_nonzero_inf :
  forall P Q C ex,
    [[P]] C** ;; C [[ex | Q]] ->
    [[P]] C** [[ex | Q]].
Proof.
  intros P Q C ex Trip s Qs.
  specialize (Trip s Qs).
  destruct Trip as (s' & Ps' & Step).
  exists s'. split.
  - assumption.
  - constructor. assumption.
Qed.

Theorem backwards_variant_inf :
  forall P C,
    (forall n, [[P n]] C [[ok | P (N.succ n)]]) ->
    [[P 0]] C** [[ok | (fun s => exists n, P n s)]].
Proof.
  intros P C Forward s [n' Ex]. revert s Ex.
  induction n' using N.peano_ind; intros.
  - (* n = 0 *)
    exists s. split.
    -- assumption.
    -- constructor.
  - (* n = S k *)
    eapply star_nonzero_inf.
    eapply seq_inf.
      intros s' Qs'. eapply IHn', Qs'.
    apply Forward. assumption.
Qed.

Theorem choice_left_inf :
  forall P Q C1 C2 ex,
    [[P]] C1 [[ex | Q]] ->
    [[P]] C1 <+> C2 [[ex | Q]].
Proof.
  intros P Q C1 C2 ex Left s Qs.
  specialize (Left s Qs).
  destruct Left as (s' & Ps' & Step).
  exists s'. split.
  - assumption.
  - econstructor. assumption.
Qed.

Theorem choice_right_inf :
  forall P Q C1 C2 ex,
    [[P]] C2 [[ex | Q]] ->
    [[P]] C1 <+> C2 [[ex | Q]].
Proof.
  intros P Q C1 C2 ex Right s Qs.
  specialize (Right s Qs).
  destruct Right as (s' & Ps' & Step).
  exists s'. split.
  - assumption.
  - apply SChoiceR. assumption.
Qed.

Theorem error_inf :
  forall P,
    [[P]] error() [[ok | False]][[er | P]].
Proof.
  intros P. split.
  - intros s Contra. contradiction.
  - intros s Ps. exists s. split.
    -- assumption.
    -- constructor.
Qed.

Theorem assume_inf :
  forall P B,
    [[P]] assumes(B) [[ok | P /\ B]][[er | False]].
Proof.
  intros P B. split.
  - intros s (Ps & Bs).
    exists s. split.
    -- assumption.
    -- constructor. assumption.
  - intros s Contra. contradiction.
Qed.

(** Rules for Variables and Mutation *)
(* Fig. 3 *)

Theorem assignment_inf :
  forall P x e,
    [[P]] x := e
    [[ok | (fun s => exists x', P (s[x := s x']) /\
                     s x = e (s[x := s x'])) ]]
    [[er | False]].
Proof.
  intros P x e. split.
  - intros s (x' & Pupd & Supd).
    exists (s [x := s x']). split.
    -- assumption.
    -- assert (s = s[x := s x'][x := e (s[x := s x'])]).
         extensionality i.
         destruct (x =? i)%string eqn:E.
           apply String.eqb_eq in E; subst.
           rewrite update_eq. assumption.
         repeat rewrite update_neq by
           now apply String.eqb_neq.
         reflexivity.
       rewrite H at 3.
       constructor.
  - intros s [].
Qed.

Theorem nondet_assignment_inf :
  forall P x,
    [[P]] x := nondet()
    [[ok | (fun s => exists x', P (s[x := x'])) ]]
    [[er | False]].
Proof.
  intros P x. split.
  - intros s (x' & Px').
    exists (s[x := x']).
    split. assumption.
    assert (s = s[x := x'][x := s x]).
      extensionality i.
      destruct (x =? i)%string eqn:E.
        apply String.eqb_eq in E; subst.
        rewrite update_eq. reflexivity.
      repeat rewrite update_neq by
        now apply String.eqb_neq.
      reflexivity.
    rewrite H at 2.
    constructor.
  - intros s [].
Qed.

(* To prove this rule would be a massive undertaking.
   It's unnecessary for proving IL's completeness,
   and only serves to aid interprocedural analysis
   (as far as I can tell). Proving this might even
   require classical logic (if following strictly with
   the paper's set-theoretical approach ) or otherwise
   a very careful constructivist re-interpretation of
   free and modified variables. *)
Theorem constancy_inf :
  forall P Q f C ex,
    (forall x, mod_stmt x C <-> ~ free_prop x f) ->
    [[P]] C [[ex | Q]] ->
    [[P /\ f]] C [[ex | Q /\ f]].
Proof.
  intros P Q f C ex Free Trip s (Qs & fs).
  specialize (Trip s Qs).
  destruct Trip as (s' & Ps' & Step).
  exists s'. split.
  - split. assumption.
      admit.
  - assumption.
Abort.

(* The same goes for substitution_1 and substitution_2 *)

(** Denotational Relational Semantics *)
(* Fig. 4 *)

Close Scope ilogic_scope.
Declare Scope ds_scope.
Open Scope ds_scope.

Definition evaluation : Type := state -> state -> Prop.

Reserved Notation
         "[ c ] ec |=> eval"
         (at level 40, c custom stmt at level 99,
          ec constr, eval constr).
Inductive ds : stmt -> ExitCondition -> evaluation -> Prop :=
| ESkipOk (s : state) :
    [ skip ] ok |=> (fun s1 s2 => s1 = s2)
| EErrorEr (s : state) :
    [ error() ] er |=> (fun s1 s2 => s1 = s2)
| EAssumeOk (B : prop) (s : state) :
    B s ->
    [ assumes(B) ] ok |=> (fun s1 s2 => s1 = s2)
| EStar0 C :
    [ C** ] ok |=> (fun s1 s2 => s1 = s2)
| EStarOk C R1 R2 :
    [ C ] ok |=> R1 ->
    [ C** ] ok |=> R2 ->
    [ C** ] ok |=> (fun s1 s3 =>
        exists s2, R1 s1 s2 /\ R2 s2 s2)
| EStarEr C R :
    [ C ] er |=> R ->
    [ C** ] er |=> R
| EPlus C1 C2 ex R1 R2 :
    [ C1 ] ex |=> R1 ->
    [ C2 ] ex |=> R2 ->
    [ C1 <+> C2 ] ex |=> (fun s1 s2 => R1 s1 s2 \/ R2 s1 s2)
| ESeqEr C1 C2 R :
    [ C1 ] er |=> R ->
    [ C1 ;; C2 ] er |=> R
| ESeqOk C1 C2 ex R1 R2 :
    [ C1 ] ok |=> R1 ->
    [ C2 ] ex |=> R2 ->
    [ C1 ;; C2 ] ex |=> (fun s1 s3 => exists s2, R1 s1 s2 /\ R2 s2 s3)

| EAsgnOk x e :
    [ x := e ] ok |=> (fun s s' => s' = s[x := e s])
| EAsgnNondetOk x (v : N) :
    [ x := v ] ok |=> (fun s s' => s' = s[x := v])

where "[ c ] ec |=> eval" := (ds c ec eval).

(* Definition 1 *)
Definition ds_post (R : evaluation) (P : prop) (s : state) :=
  exists s', P s' /\ R s' s.

Definition under_approximate (P Q : prop) (R : evaluation) : Prop :=
  forall s,
    Q s ->
    ds_post R P s.
Notation "{{ p }} c {{ q }}" := (under_approximate p q c)
      (at level 90, c constr at level 99) : ds_scope.

Definition over_approximate (P Q : prop) (R : evaluation) : Prop :=
  forall s,
    ds_post R P s ->
    Q s.
Notation "<| p |> c <| q |>" := (over_approximate p q c)
      (at level 90, c constr at level 99) : ds_scope.

Theorem and_or_symmetry : forall P Q1 Q2 c,
  ({{ P }} c {{ Q1 }} /\ {{ P }} c {{ Q2 }}) <->
  {{ P }} c {{ Q1 \/ Q2 }}.
Proof.
  intros. split; intro.
  - destruct H. intros s [Q1s|Q2s].
      apply H, Q1s.
      apply H0, Q2s.
  - split; intros s Qs.
      apply H. now left.
      apply H. now right.
Qed.

Theorem impl_symmetry : forall P P' Q Q' c,
  P ->> P' ->
  {{P}}c{{Q}} ->
  Q' ->> Q ->
  {{P'}}c{{Q'}}.
Proof.
  intros P P' Q Q' c PP' Trip Q'Q s Q's.
  apply Q'Q in Q's.
  specialize (Trip s Q's).
  destruct Trip as (s' & Ps' & Step).
  exists s'. split. apply PP', Ps'.
  assumption.
Qed.

Theorem principle_of_agreement : forall u u' c o o',
  {{u}}c{{u'}} ->
  (u ->> o) ->
  <| o |> c <| o' |> ->
  u' ->> o'.
Proof.
  intros u u' c o o' Trip uo oco' s u's.
  apply oco'. specialize (Trip s u's).
  destruct Trip as (s' & us' & Step).
  exists s'. split.
    apply uo. assumption.
  assumption.
Qed.

Theorem principle_of_denial : forall u u' c o o',
  {{u}}c{{u'}} ->
  u ->> o ->
  ~ (u' ->> o') ->
  ~ (<| o |> c <| o' |>).
Proof.
  intros u u' c o o' ucu' uo u'o' oco'.
  apply u'o'. intros s u's.
  specialize (ucu' s u's).
  destruct ucu' as (s' & us' & Step).
  apply oco'. exists s'. split.
    apply uo. assumption.
  assumption.
Qed.






















