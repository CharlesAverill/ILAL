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

Lemma exists_or : forall (T : Type) (P R : T -> Prop),
  (exists Q, (P Q \/ R Q)) <-> ((exists Q, P Q) \/ (exists Q, R Q)).
Proof.
  intros. split; intro.
  - destruct H as (Q & [Pq | Rq]).
      left. eauto.
      right. eauto.
  - destruct H, H.
      exists x. now left.
      exists x. now right.
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

Declare Scope ds_scope.
Open Scope ds_scope.

Definition evaluation : Type := (state * state) -> Prop.

Reserved Notation
         "[ c ] ec |=> s"
         (at level 40, c custom stmt at level 99,
          ec constr, s constr).
Inductive ds : stmt -> ExitCondition -> (state * state) -> Prop :=
| ESkipOk (s : state) :
    [ skip ] ok |=> (s, s)
| EErrorEr (s : state) :
    [ error() ] er |=> (s, s)
| EAssumeOk (B : prop) (s : state) :
    B s ->
    [ assumes(B) ] ok |=> (s, s)
| EStar0 C (s : state) :
    [ C** ] ok |=> (s, s)
| EStarOk C s1 s2 s3 ex :
    [ C** ] ok |=> (s1, s2) ->
    [ C ] ex |=> (s2, s3) ->
    [ C** ] ex |=> (s1, s3)
| EStarEr C (s1 s2 : state) :
    [ C ] er |=> (s1, s2) ->
    [ C** ] er |=> (s1, s2)
| EPlusL C1 C2 ex s s1 :
    [ C1 ] ex |=> (s, s1) ->
    [ C1 <+> C2 ] ex |=> (s, s1)
| EPlusR C1 C2 ex s s1 :
    [ C2 ] ex |=> (s, s1) ->
    [ C1 <+> C2 ] ex |=> (s, s1)
| ESeqEr C1 C2 s1 s2 :
    [ C1 ] er |=> (s1, s2) ->
    [ C1 ;; C2 ] er |=> (s1, s2)
| ESeqOk C1 C2 ex s1 s2 s3 :
    [ C1 ] ok |=> (s1, s2) ->
    [ C2 ] ex |=> (s2, s3) ->
    [ C1 ;; C2 ] ex |=> (s1, s3)

| EAsgnOk x e s :
    [ x := e ] ok |=> (s, s[x := e s])
| EAsgnNondetOk x (v : N) s :
    [ x := nondet() ] ok |=> (s, s[x := v])

where "[ c ] ec |=> s" := (ds c ec s).

(* Definition 1 *)
Definition ds_post (R : evaluation) (P : prop) :=
  fun s' => exists s, P s /\ R (s, s').

Definition under_approximate (P : prop) (R : evaluation) (Q : prop) : Prop :=
  forall s, Q s -> ds_post R P s.
Notation "{{ p }} c {{ q }}" := (under_approximate p c q)
      (at level 90, c constr at level 99) : ds_scope.

Definition over_approximate (P : prop) (R : evaluation) (Q : prop) : Prop :=
  forall s, ds_post R P s -> Q s.
Notation "<| p |> c <| q |>" := (over_approximate p c q)
      (at level 90, c constr at level 99) : ds_scope.

(* Theorem 2 *)
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
  assert (ex : ExitCondition). constructor.
  eapply oco'. specialize (Trip s u's).
  destruct Trip as (s' & us' & Step).
  exists s'. split.
    apply uo. assumption.
  eassumption.
Qed.

Theorem principle_of_denial : forall u u' c o o',
  {{u}}c{{u'}} ->
  u ->> o ->
  ~ (u' ->> o') ->
  ~ (<| o |> c <| o' |>).
Proof.
  intros u u' c o o' ucu' uo u'o' oco'.
  apply u'o'. intros s u's.
  assert (ex : ExitCondition). constructor.
  specialize (ucu' s u's).
  destruct ucu' as (s' & us' & Step).
  eapply oco'. exists s'. split.
    apply uo. assumption.
  eassumption.
Qed.

(* Lemma 3 *)
Lemma characterization : forall P R Q,
  {{P}} R {{Q}} <->
  (forall sq, Q sq -> exists sp, P sp /\ R (sp, sq)).
Proof. reflexivity. Qed.

(* Definition 4 *)
Definition denote (c : stmt) (ex : ExitCondition) : evaluation :=
  fun '(s1, s2) => [c] ex |=> (s1, s2).

Definition interpret_spec (P Q : prop) (C : stmt) ex : Prop :=
  [[P]] C [[ex | Q]] <-> {{P}} denote C ex {{Q}}.

(* Theorem 5 *)
Lemma star_equiv : forall c s1 s2 ex,
  [(c **);; c] ex |=> (s1, s2) ->
  [c **] ex |=> (s1, s2).
Proof.
  intros. invs H.
    assumption.
  econstructor; eassumption.
Qed.

Theorem soundness :
  forall C P Q ex,
    [[P]] C [[ex | Q]] ->
    {{P}} denote C ex {{Q}}.
Proof.
  intros C P Q ex Htrip.
  rewrite characterization.
  intros sq Qsq.
  specialize (Htrip sq Qsq).
  unfold post in Htrip.
  destruct Htrip as (sp & Psp & Step).
  exists sp. split. assumption.
  unfold denote. revert Q P Psp Qsq.
  induction Step; intros;
    try solve [constructor].
  - (* sequence error *)
    constructor. eapply IHStep; eassumption.
  - (* sequence exit *)
    econstructor. eapply IHStep1.
      eassumption.
    2: eapply IHStep2; eauto.
    instantiate (1 := (fun _ => True)). exact I.
  - (* star *)
    eapply star_equiv, IHStep; eassumption.
  - (* plus left *)
    eapply EPlusL, IHStep; eassumption.
  - (* plus right *)
    eapply EPlusR, IHStep; eassumption.
  - (* assumes ok *)
    now constructor.
Qed.

Theorem completeness :
  forall C P Q ex,
    {{P}} denote C ex {{Q}} ->
    [[P]] C [[ex | Q]].
Proof.
  intros C P Q ex DS s Qs;
    specialize (DS s Qs);
    destruct DS as (s' & Ps' & DS); unfold denote in DS.
  revert P Q ex s s' Ps' Qs DS.
  induction C; intros;
    try solve [
      invs DS; eexists; split; eauto; constructor].
  - (* sequence *)
    invs DS.
    -- (* C1 error *)
       specialize (IHC1 P Q er s s' Ps' Qs H2).
       destruct IHC1 as (sx & Psx & Step).
       exists sx. split. assumption. now constructor.
    -- (* C2 ex *)
       specialize (IHC1 P (fun _ => True) ok s2 s' Ps' I H3).
       destruct IHC1 as (sx & Psx & Step).
       enough (sx = s'). subst.
       specialize (IHC2 (fun _ => True) Q ex s s2 I Qs H5).
       destruct IHC2 as (sx' & Psx' & Step').
       enough (sx' = s2). subst.

       exists s'. split. assumption.
         eapply SSeqOk; eassumption.

       admit.
       admit.
  - (* plus *)
    invs DS.
    -- (* left *)
       specialize (IHC1 _ _ ex _ _ Ps' Qs H2).
       destruct IHC1 as (sx' & Psx' & Step).
       exists sx'. split. assumption. now apply SChoiceL.
    -- (* right *)
       specialize (IHC2 _ _ ex _ _ Ps' Qs H2).
       destruct IHC2 as (sx' & Psx' & Step).
       exists sx'. split. assumption. now apply SChoiceR.
  - (* star *)
    invs DS.
    -- (* skip *)
       exists s. split. assumption. constructor.
    -- (* ok *)
       specialize (IHC _ _ ex _ _ Ps' Qs).
       admit.
    -- (* er *)
       specialize (IHC _ _ er _ _ Ps' Qs H2).
       destruct IHC as (sx' & Psx' & Step).
       admit.
  - (* assumes *)
    invs DS. exists s. split. assumption. now constructor.
Admitted.


















