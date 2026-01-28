From ILAL Require Import language.

(** Triple definitions *)

(* There exists a starting state s satisfying P such that executing
   c under exit condition ex reaches s' *)
Definition post (ex : ExitCondition) (c : stmt) (P : prop) : prop :=
  (fun s' : state =>
    exists (s : state),
      P s /\ s =[ c ]=> ex | s').

(* Every state satisfying Q is reachable from some state satisfying
   P by executing c under exit condition ex *)
Definition itriple (ex : ExitCondition) (P : prop) (c : stmt) (Q : prop) : Prop :=
  forall (s : state),
    Q s ->
    post ex c P s.
Notation "[[ P ]] c [[ ex | Q ]]" :=
  (itriple ex P c Q) (at level 90, c custom stmt at level 99).
Notation "[[ P ]] c [[ ok | Q ]] [[ er | R ]]" :=
  (itriple ok P c Q /\ itriple er P c R) (at level 90, c custom stmt at level 99).

(* For every final state s that can result from executing c
   from some state satisfying P, s satisfies Q *)
Definition htriple (ex : ExitCondition) (P : prop) (c : stmt) (Q : prop) : Prop :=
  forall (s : state),
    post ex c P s ->
    Q s.
Notation "{{ P }} c {{ ex | Q }}" :=
  (htriple ex P c Q) (at level 90, c custom stmt at level 99).

Definition prop_impl (P Q : prop) : Prop :=
  forall (s : state), P s -> Q s.
Notation "P ->> Q" := (prop_impl P Q) (at level 80).

(** Incorrectness logic inference rules *)

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
    (forall n, [[P n]] C [[ok | P (1 + n)]]) ->
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
    apply Forward. rewrite <- N.add_1_r, N.add_comm in Ex.
    assumption.
Qed.