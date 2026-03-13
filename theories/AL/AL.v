From Stdlib Require Export NArith String.
From ILAL Require Export AL.language state.
From Stdlib Require Import List.
Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.

Definition aprop : Type := estate -> Prop.

Definition aprop_impl (P Q : aprop) : Prop :=
  forall s, P s -> Q s.
Notation "P ->> Q" := (aprop_impl P Q) (at level 80).

(** Denotational Relational Semantics *)
(* Table 8 *)

Declare Scope al_ds_scope.
Open Scope al_ds_scope.

Definition evaluation : Type := (estate * estate) -> Prop.

Inductive mode : Set := Ok | Ad.

Reserved Notation
  "[[ c ]] m |=> ( s , s' )"
  (at level 40, c custom al_stmt at level 99,
   m constr, s constr, s' constr).

Open Scope al_scope.
Inductive ds : astmt -> mode -> (estate * estate) -> Prop :=
| EDSkip m (s : estate) :
    [[ skip ]] m |=> (s, s)
| EDAssignV x e (st : estate) :
    [[ x := e ]] Ok |=> (st, st[[ x :=v e (st.(vstate).(s)) ]])
| EDAssignA x e (st : estate) :
    [[ x := e ]] Ad |=> (st, st[[ x :=a e (st.(astate).(s)) ]])
| EDRandV x (v : N) (s : estate) :
    [[ x := rand() ]] Ok |=> (s, s[[ x :=v v ]])
| EDRandA x (v : N) (s : estate) :
    [[ x := rand() ]] Ad |=> (s, s[[ x :=a v ]])
| EDSeq c1 c2 m s1 s2 s3 :
    [[ c1 ]] m |=> (s1, s2) ->
    [[ c2 ]] m |=> (s2, s3) ->
    [[ c1 ;; c2 ]] m |=> (s1, s3)
(** read(s, x): consume head of channel s into var x *)
| EDReadV (s x : id) (v : N) (l : channel) (sig : estate) :
    sig.(vstate).(ch) s = v :: l ->
    [[ read(s, x) ]] Ok |=> (sig, (sig[[ x :=v v ]])[[ s :=vch l ]])
| EDReadA (s x : id) (v : N) (l : channel) (sig : estate) :
    sig.(astate).(ch) s = v :: l ->
    [[ read(s, x) ]] Ad |=> (sig, (sig[[ x :=a v ]])[[ s :=ach l ]])
(** write(s, x): append var x to channel s *)
| EDWriteV (ch_id x : id) (sig : estate) :
    [[ write(ch_id, x) ]] Ok |=>
      (sig, sig[[ ch_id :=vch sig.(vstate).(s) x :: sig.(vstate).(ch) ch_id ]])
| EDWriteA (ch_id x : id) (sig : estate) :
    [[ write(ch_id, x) ]] Ad |=>
      (sig, sig[[ ch_id :=ach sig.(astate).(s) x :: sig.(astate).(ch) ch_id ]])
(** adv_assert(P): adversarial assert *)
| EDAdvAssertSuccess P (sig : estate) :
    P sig.(astate).(s) ->
    [[ adv_assert(P) ]] Ad |=> (sig, sig)
| EDAdvAssertFailure P (sig : estate) :
    ~ P sig.(astate).(s) ->
    [[ adv_assert(P) ]] Ad |=> (sig, sig)
(** c1 || c2 *)
| EDParL c1 c2 m s1 s2 :
    [[ c1 ]] m |=> (s1, s2) ->
    [[ c1 <||> c2 ]] m |=> (s1, s2)
| EDParR c1 c2 m s1 s2 :
    [[ c2 ]] m |=> (s1, s2) ->
    [[ c1 <||> c2 ]] m |=> (s1, s2)
(** Com(c1, c2) *)
| EDComVA c1 c2 m ch_id sig v l :
    sig.(vstate).(ch) ch_id = v :: l ->
    [[ Com(c1, c2) ]] m |=> (sig, sig[[ch_id :=vch l]][[ch_id :=ach v :: l]])
| EDComAV c1 c2 m ch_id sig v l :
    sig.(astate).(ch) ch_id = v :: l ->
    [[ Com(c1, c2) ]] m |=> (sig, sig[[ch_id :=ach l]][[ch_id :=vch v :: l]])
where "[[ c ]] m |=> ( s , s' )" := (ds c m (s, s')).
Close Scope al_scope.

(* Definition 1 *)

Definition post (R : evaluation) (P : aprop) :=
  fun s' => exists s, P s /\ R (s, s').

Definition under_approximate (P : aprop) (c : astmt) (m : mode) (Q : aprop) : Prop :=
  forall s, Q s -> post (ds c m) P s.

Notation "{{ P }} c [[ m ]] {{ Q }}" :=
  (under_approximate P c m Q)
  (at level 90, c custom al_stmt at level 99, m constr) : al_ds_scope.

Definition over_approximate (P : aprop) (c : astmt) (m : mode) (Q : aprop) : Prop :=
  forall s, post (ds c m) P s -> Q s.

Notation "<| P |> c [[ m ]] <| Q |>" :=
  (over_approximate P c m Q)
  (at level 90, c custom al_stmt at level 99, m constr) : al_ds_scope.

Open Scope al_scope.

Theorem and_or_symmetry : forall P Q1 Q2 c m,
  ({{ P }} c [[m]] {{ Q1 }} /\ {{ P }} c [[m]] {{ Q2 }}) <->
  {{ P }} c [[m]] {{ fun s => Q1 s \/ Q2 s }}.
Proof.
  intros. split; intro H.
  - destruct H as [H1 H2]. intros s [HQ1 | HQ2].
    + apply H1, HQ1.
    + apply H2, HQ2.
  - split; intros s Hs.
    + apply H. now left.
    + apply H. now right.
Qed.

Theorem impl_symmetry : forall P P' Q Q' c m,
  P ->> P' ->
  {{ P }} c [[m]] {{ Q }} ->
  Q' ->> Q ->
  {{ P' }} c [[m]] {{ Q' }}.
Proof.
  intros P P' Q Q' c m HP HU HQ s Q's.
  specialize (HU s (HQ s Q's)).
  unfold post in *. destruct HU as (s' & Ps' & DS).
  specialize (HP s' Ps'). exists s'. now split.
Qed.

Theorem al_principle_of_agreement : forall u u' c m o o',
  {{ u }} c [[m]] {{ u' }} ->
  u ->> o ->
  <| o |> c [[m]] <| o' |> ->
  u' ->> o'.
Proof.
  intros u u' c m o o' HU HUO HO s Hu's.
  apply HO.
  destruct (HU s Hu's) as (s' & Hs' & Step).
  exists s'. split.
    apply HUO, Hs'.
    assumption.
Qed.

Theorem al_principle_of_denial : forall u u' c m o o',
  {{ u }} c [[m]] {{ u' }} ->
  u ->> o ->
  ~ (u' ->> o') ->
  ~ (<| o |> c [[m]] <| o' |>).
Proof.
  intros u u' c m o o' HU HUO HNO HO.
  apply HNO. intros s Hu's.
  destruct (HU s Hu's) as (s' & Hs' & Step).
  eapply HO. exists s'. split.
    apply HUO, Hs'.
    assumption.
Qed.