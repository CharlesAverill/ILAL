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
    [[ok | (fun s => exists x', P (s[x := x']) /\
                     s x = e (s[x := x'])) ]]
    [[er | False]].
Proof.
  intros P x e. split.
  - intros s (x' & Pupd & Supd).
    exists (s [x := x']). split.
    -- assumption.
    -- assert (s = s[x := x'][x := e (s[x := x'])]).
         extensionality i.
         destruct (x =? i)%string eqn:E.
           apply String.eqb_eq in E; subst.
           rewrite update_eq. assumption.
         repeat rewrite update_neq by
           now apply String.eqb_neq.
         reflexivity.
       rewrite H at 2.
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

Lemma quadruple_left :
  forall P Q1 Q2 c,
    [[P]] c [[ok | Q1]][[er | Q2]] ->
    [[P]] c [[ok | Q1]].
Proof. intros. now destruct H. Qed.

Lemma quadruple_right :
  forall P Q1 Q2 c,
    [[P]] c [[ok | Q1]][[er | Q2]] ->
    [[P]] c [[er | Q2]].
Proof. intros. now destruct H. Qed.

(* The same goes for substitution_1 and substitution_2 *)

(** Proof Theory *)
(* This is a departure from the Incorrectness Logic paper.
   An attempt at formalizing IL's soundness and completeness
   with respect to the Denotational Relational Semantics
   in Fig. 4 is available on branch denotational_IL.

   This approach was sufficient to prove soundness, but
   completeness seems unprovable (not necessarily false).
   The incomplete proof is also available in the branch.

   Instead of proving soundness and completeness WRT DRS,
   we will prove it WRT an axiomatic, proof-theoretical
   encoding of the proof system rules shown in Figs. 2 and 3.

   Unfortunately, this means that Theorem 2 is unapproachable,
   as there is no 'post' relationship to construct under-
   and over-approximate triples from.

   This change also swaps the soundness and completeness
   directions. Now, we are proving that the logic is sound
   if derivable triples are valid via the above proof rules,
   and complete if valid triples are derivable via the axioms
   below. *)

Reserved Notation
         "P , [ c ] ec , Q"
         (at level 40, c custom stmt at level 99).
Inductive derivable : prop -> stmt -> ExitCondition -> prop -> Prop :=
| EmptyUnderApproximates P c e :
    P, [c] e, False
| Consequence P P' Q Q' c e :
    P, [c] e, Q ->
    P ->> P' ->
    Q' ->> Q ->
    P', [c] e, Q'
| Disjunction P1 Q1 P2 Q2 c e :
    P1, [c] e, Q1 ->
    P2, [c] e, Q2 ->
    (fun s => P1 s \/ P2 s), [c] e, (fun s => Q1 s \/ Q2 s)
| UnitOk P :
    P, [skip] ok, P
| UnitEr P :
    P, [skip] er, False
| SeqShortCircuit P R C1 C2 :
    P, [C1] er, R ->
    P, [C1 ;; C2] er, R
| SeqNormal P Q R C1 C2 e :
    P, [C1] ok, Q ->
    Q, [C2] e, R ->
    P, [C1 ;; C2] e, R
| IterateZero P C :
    P, [C**] ok, P
| IterateNonzero P Q C e :
    P, [C** ;; C] e, Q ->
    P, [C**] e, Q
| BackwardsVariant (P : N -> prop) C :
    (forall n, P n, [C] ok, P (N.succ n)) ->
    P 0, [C**] ok, (fun s => exists n', P n' s)
| ChoiceLeft P Q C1 C2 e:
    P, [C1] e, Q ->
    P, [C1 <+> C2] e, Q
| ChoiceRight P Q C1 C2 e:
    P, [C2] e, Q ->
    P, [C1 <+> C2] e, Q
| ErrorOk P :
    P, [error()] ok, False
| ErrorEr P :
    P, [error()] er, P
| AssumeOk P B :
    P, [assumes(B)] ok, (fun s => P s /\ B s)
| AssumeEr P B :
    P, [assumes(B)] er, False

| AssignmentOk P x (e : expression) :
    P, [x := e] ok, (fun s => exists x', P (s[x := x']) /\
                              s x = e (s[x := x']))
| AssignmentEr P x (e : expression) :
    P, [x := e] er, False
| NondetAssignmentOk P x :
    P, [x := nondet()] ok, (fun s => exists x', P (s[x := x']))
| NondetAssignmentEr P x :
    P, [x := nondet()] er, False

where "P , [ c ] ec , Q" := (derivable P c ec Q).

(* Theorem 5 *)
Theorem soundness :
  forall C P Q ex,
    P, [C] ex, Q ->
    [[P]] C [[ex | Q]].
Proof.
  intros. induction H.
  - apply empty_under_approximates_inf.
  - eapply consequence_inf; eauto.
  - now apply disjunction_inf.
  - apply unit_ok_inf.
  - apply unit_er_inf.
  - now apply seq_short_circuit_inf.
  - eapply seq_inf; eauto.
  - apply star_zero_inf.
  - now apply star_nonzero_inf.
  - now apply backwards_variant_inf.
  - now apply choice_left_inf.
  - now apply choice_right_inf.
  - apply (quadruple_left _ _ _ _ (error_inf P)).
  - apply (quadruple_right _ _ _ _ (error_inf P)).
  - apply (quadruple_left _ _ _ _ (assume_inf P B)).
  - apply (quadruple_right _ _ _ _ (assume_inf P B)).
  - apply (quadruple_left _ _ _ _ (assignment_inf P x e)).
  - apply (quadruple_right _ _ _ _ (assignment_inf P x e)).
  - apply (quadruple_left _ _ _ _ (nondet_assignment_inf P x)).
  - apply (quadruple_right _ _ _ _ (nondet_assignment_inf P x)).
Qed.

(* Theorem 6 *)
Lemma post_equiv :
  forall C1 C2 P s,
    post ok <{C1 ;; C2}> P s <->
    post ok C2 (fun s' => post ok C1 P s') s.
Proof.
  intros C1 C2 P s. split; intro.
  - destruct H as (s' & Ps' & Step).
    invs Step.
    exists s2. split.
      exists s'. now split.
    assumption.
  - destruct H as (s2 & Post & Step).
    destruct Post as (s' & Ps' & Step').
    exists s'.
    split. assumption.
    econstructor; eassumption.
Qed.

Lemma or_same :
  forall P, P \/ P <-> P.
Proof. intuition. Qed.

(* This pattern shows up a ton in completeness *)
Ltac tripspec Trip :=
  let s := fresh "s" in
  let Qs := fresh "Qs" in
  let s' := fresh "s'" in
  let Ps' := fresh "Ps'" in
  let Step := fresh "Step" in
  intros s Qs; specialize (Trip s Qs);
  destruct Trip as (s' & Ps' & Step);
  invs Step;
  try solve [now eauto].

Theorem completeness :
  forall C P Q ex,
    [[P]] C [[ex | Q]] ->
    P, [C] ex, Q.
Proof.
  induction C;
    intros P Q ex Trip.
  - (* skip *)
    destruct ex.
    -- (* er *)
      apply (Consequence P P False Q). constructor.
      now intro.
      tripspec Trip.
    -- (* ok *)
      apply (Consequence P P P Q). constructor.
      now intro.
      tripspec Trip.
  - (* assignment *)
    destruct ex.
    -- (* er *)
      apply (Consequence P P False Q). constructor.
      now intro.
      tripspec Trip.
    -- (* ok *)
      assert (forall s, Q s -> exists x', P (s[i := x']) /\
                               s i = exp (s[i := x'])). {
        tripspec Trip. exists (s' i).
        now rewrite update_shadow, update_eq, state_upd_eq.
      }

      eapply Consequence.
        apply AssignmentOk.
        intros s Ps. apply Ps.
        intros s Qs. now apply H.
  - (* nondet assignment *)
    destruct ex.
    -- (* er *)
      apply (Consequence P P False Q). constructor.
      now intro.
      tripspec Trip.
    -- (* ok *)
      assert (forall s, Q s -> exists v, P (s[i := v])). {
        tripspec Trip.
        exists (s' i). now rewrite update_shadow, state_upd_eq.
      }

      eapply Consequence.
        apply NondetAssignmentOk.
        intros s Ps. apply Ps.
        intros s Qs. now apply H.
  - (* sequence *)
    destruct ex.
    -- (* er *)
       assert (forall s, Q s -> post er C2 (fun s' => post ok C1 P s') s \/ post er C1 P s) as S. {
         tripspec Trip.
         + right. exists s'. now split.
         + left. exists s2. split. exists s'. now split. assumption.
       }

       assert (P, [C1 ;; C2] er, post er C2 (fun s' => post ok C1 P s')) as X1. {
         assert ([[P]] C1 [[ok | fun s => post ok C1 P s]]).
           intros sx Post. assumption.
         assert ([[fun s => post ok C1 P s]] C2 [[er | fun s => post er C2 (fun s' => post ok C1 P s') s]]).
           intros sx Post. assumption.
         eapply SeqNormal.
           apply IHC1, H.
         apply IHC2, H0.
       }

       assert (P, [C1 ;; C2] er, fun s => post er C1 P s) as X2. {
         assert ([[P]] C1 [[er | fun s => post er C1 P s]]).
           intros s Post. assumption.
         eapply SeqShortCircuit.
           apply IHC1, H.
       }

       assert (P, [C1 ;; C2] er, fun s => post er C2 (fun s' => post ok C1 P s') s \/ post er C1 P s) as X. {
         pose proof (Disjunction _ _ _ _ _ _ X1 X2).
         eapply Consequence.
         apply H.
         now intros s [Post|Post].
         now intro.
       }

       eapply (Consequence P P _ Q).
       apply X.
       now intro.
       intros s Qs. now apply S.
    -- (* ok *)
      assert (forall s, Q s -> post ok C2 (fun s' => post ok C1 P s') s). {
        tripspec Trip.
        exists s2. split.
          now exists s'.
          assumption.
      }

      assert ([[P]] C1 [[ok | fun s => post ok C1 P s]]) as HC1.
        intros s Post. assumption.
      assert ([[fun s => post ok C1 P s]] C2
              [[ok | fun s => post ok C2 (fun s' => post ok C1 P s') s]]) as HC2.
        intros s Post. assumption.

      specialize (IHC1 _ _ _ HC1).
      specialize (IHC2 _ _ _ HC2).
      pose proof (SeqNormal _ _ _ _ _ _ IHC1 IHC2).

      eapply (Consequence P P _ Q).
        apply H0.
        now intro.
        intros s Qs. now apply H.
  - (* choice *)
    assert (forall s, Q s -> post ex <{C1 <+> C2}> P s) as H. {
      tripspec Trip.
        exists s'. split. assumption. now constructor.
        exists s'. split. assumption. now constructor.
    }

    assert (forall s, post ex <{C1 <+> C2}> P s -> post ex C1 P s \/ post ex C2 P s) as hPost. {
      intros s Post.
      destruct Post as (s' & Ps' & Step).
      invs Step.
        left. exists s'. now split.
        right. exists s'. now split.
    }

    assert (forall s, Q s -> post ex C1 P s \/ post ex C2 P s). {
      intros s Qs.
      now apply hPost, H.
    }

    assert ([[P]] C1 [[ex | fun s => post ex C1 P s]]).
      intros s Ps. assumption.

    assert ([[P]] C2 [[ex | fun s => post ex C2 P s]]).
      intros s Ps. assumption.

    specialize (IHC1 _ _ _ H1).
    specialize (IHC2 _ _ _ H2).
    pose proof (ChoiceLeft _ _ _ C2 _ IHC1).
    pose proof (ChoiceRight _ _ C1 _ _ IHC2).

    pose proof (Disjunction _ _ _ _ _ _ H3 H4).
    eapply Consequence.
      apply H5.
      now intros s [Qs|Qs].
      intros s Qs. now apply H0.
  - (* iteration *) admit.
  - (* error *)
    destruct ex.
    -- (* er *)
       eapply Consequence.
         apply ErrorEr.
       intros s Ps. apply Ps.
       tripspec Trip.
    -- (* ok *)
       eapply Consequence.
         constructor.
       intros s Ps. apply Ps.
       tripspec Trip.
  - (* assumes *)
    destruct ex.
    -- (* er *)
       eapply Consequence.
         constructor.
       intros s Ps. apply Ps.
       tripspec Trip.
    -- (* ok *)
       eapply Consequence.
         apply AssumeOk.
       intros s Ps. apply Ps.
       tripspec Trip.
Abort.


















