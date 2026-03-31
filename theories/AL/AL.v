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

Reserved Notation
  "P , [[ c ]] m , Q"
  (at level 40, c custom al_stmt at level 99).
Inductive derivable: aprop -> astmt -> mode -> aprop -> Prop :=
| Unit P m:
  P, [[skip]] m, P
| Consequence P P' Q Q' c m :
  P, [[c]] m, Q ->
  P ->> P' ->
  Q' ->> Q ->
  P', [[c]] m, Q'
(**  Not sure if assume should be B sig or B sig.(a/vstate).(s)**)
| AssumeOk P B :
  P, [[assume(B)]] Ok, (fun sig => P sig /\ B sig.(vstate).(s))
| AssumeAd P B :
  P, [[assume(B)]] Ad, (fun sig => P sig /\ B sig.(astate).(s))
| Disjunction P1 Q1 P2 Q2 c m :
  P1, [[c]] m, Q1 ->
  P2, [[c]] m, Q2 ->
  (fun s => P1 s \/ P2 s), [[c]] m, (fun s => Q1 s \/ Q2 s)
| Seq P Q R c1 c2 m :
  P, [[c1]] m, Q -> 
  Q, [[c2]] m, R ->
  P, [[c1 ;; c2]] m, R
| ChoiceLeft P Q c1 c2 m:
  P, [[c1]] m, Q ->
  P, [[c1 <+> c2]] m, Q
| ChoiceRight P Q c1 c2 m:
  P, [[c2]] m, Q ->
  P, [[c1 <+> c2]] m, Q
| IterateZero P c m:
  P, [[c**]] m, P
| IterateNonzero P Q c m :
  P, [[c** ;; c]] m, Q ->
  P, [[c**]] m, Q
| LocalOk P x (e : expression):
  P, [[x := e]] Ok, (fun sig => exists x', P (sig[[x :=v x' (sig.(vstate).(s))]]) /\ (sig.(vstate).(s) x) = e (sig[[x :=v x' (sig.(vstate).(s))]]).(vstate).(s))
| LocalAd P x (e : expression):
  P, [[x := e]] Ad, (fun sig => exists x', P (sig[[x :=a x' (sig.(astate).(s))]]) /\ (sig.(astate).(s) x) = e (sig[[x :=a x' (sig.(astate).(s))]]).(astate).(s))
| ReadV P (ss x : id):
  P, [[ read(ss, x) ]] Ok, (fun sig => exists (v : N) x' s', P ((sig[[x :=v x' (sig.(vstate).(s))]]) [[ss :=vch s' (sig.(vstate).(ch))]])
                                                            /\ s' (sig.(vstate).(ch)) = v :: sig.(vstate).(ch) ss
                                                            /\ sig.(vstate).(s) x = v)
| ReadA P (ss x : id):
  P, [[ read(ss, x) ]] Ad, (fun sig => exists (v : N) x' s', P ((sig[[x :=a x' (sig.(astate).(s))]]) [[ss :=ach s' (sig.(astate).(ch))]])
                                                            /\ s' (sig.(astate).(ch)) = v :: sig.(astate).(ch) ss
                                                            /\ sig.(astate).(s) x = v)
| WriteV P (ss x : id):
  P, [[ write(ss, x) ]] Ok, (fun sig => exists (v : N) s', P (sig[[ss :=vch s' (sig.(vstate).(ch))]])
                                                          /\ sig.(vstate).(ch) ss = v :: s' (sig.(vstate).(ch))
                                                          /\ sig.(vstate).(s) x = v)
| WriteA P (ss x : id):
  P, [[ write(ss, x) ]] Ok, (fun sig => exists (v : N) s', P (sig[[ss :=ach s' (sig.(astate).(ch))]])
                                                          /\ sig.(astate).(ch) ss = v :: s' (sig.(astate).(ch))
                                                          /\ sig.(astate).(s) x = v)
| ParL P1 c1 Q1 P2 c2 Q2 m1 m2:
  P1, [[c1]] m1, Q1 ->
  P2, [[c2]] m2, Q2 ->
  P1, [[c1 <||> c2]] m1, Q1 
| ParR P1 c1 Q1 P2 c2 Q2 m1 m2:
  P1, [[c1]] m1, Q1 ->
  P2, [[c2]] m2, Q2 ->
  P2, [[c1 <||> c2]] m2, Q2 
(** I think this is the literal interpretation from the paper (for ok->ad and ad->ok only) as [P][A] c1 || c2 [Q][B] is defined as [P] c1 || c2 [Q] /\ [A] c1 || c2 [B] **)
| ComVA_V P c1 A c2 (ss : id):
  P, [[c1 <||> c2]] Ok, (fun sig => exists v s', (P (sig[[ss :=vch s' (sig.(vstate).(ch))]]) /\ s' (sig.(vstate).(ch)) = v :: sig.(vstate).(ch) ss /\ A (sig[[ss :=ach s' (sig.(astate).(ch))]]) /\ sig.(astate).(ch) ss = v :: s' (sig.(astate).(ch))))



  
where "P , [[ c ]] m , Q" := (derivable P c m Q).