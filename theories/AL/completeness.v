(** * Completeness of AL, tiers 1 and 2: statements and machinery

    Mirrors [IL.v]'s [interpret_spec] / [completeness] / [equivalence] for the
    single-thread system ([derivable] vs [under_approximate]) and for the
    composed one-step system ([derivable2] vs [al_underc_r]).

    The two completeness theorems are stated and left [Admitted]; the helper
    lemmas are proved. See Other/COMPLETENESS_GAPS.md for the proof plan. *)
From ILAL Require Import AL.AL AL.language state tactics.
From Stdlib Require Import NArith String List.
Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.
Open Scope al_scope.

(** ** Tier 1: single thread *)

Definition interpret_spec (P Q : aprop) (c : astmt) (m : mode) : Prop :=
  P, [c] m, Q <-> {{ P }} c [[m]] {{ Q }}.

(* [c**] unrolled [n] times, star-then-body as in [EDStarN] *)
Fixpoint aRepeat (c : astmt) (n : nat) : astmt :=
  match n with
  | O => ASkip
  | S n' => ASeq (aRepeat c n') c
  end.

Lemma arepeat_sound : forall n c m s s',
  ds (aRepeat c n) m (s, s') -> ds (AStar c) m (s, s').
Proof.
  induction n; intros c m s s' H; simpl in H; inversion H; subst.
  - constructor.
  - eapply EDStarN. eapply IHn. eassumption. assumption.
Qed.

(* Every [c**] run is some finite unrolling; the star case of completeness
   goes through [DBackwardVariant] with [P n := post (ds (aRepeat c n) m) P] *)
Lemma arepeat_is_star : forall c m P sig,
  post (ds (AStar c) m) P sig -> exists n, post (ds (aRepeat c n) m) P sig.
Proof.
  intros c m P sig (s0 & Ps0 & D).
  remember (AStar c) as sc eqn:E. remember (s0, sig) as pr eqn:Epr.
  revert s0 sig Ps0 Epr.
  induction D; intros s0 sf Ps0 Epr; try discriminate E;
    injection E as ->; injection Epr as -> ->.
  - exists 0%nat, sf. split. assumption. constructor.
  - destruct (IHD1 eq_refl s0 s2 Ps0 eq_refl) as (n & sn & Psn & Dn).
    exists (S n), sn. split. assumption. simpl. econstructor; eassumption.
Qed.

(* [adv_assert] only steps in [Ad]; in [Ok] the post is empty ([DEmpty]) *)
Lemma no_advassert_ok : forall B sig sig', ~ ds (AAdvAssert B) Ok (sig, sig').
Proof. intros B sig sig' H. inversion H. Qed.

Theorem completeness :
  forall c P Q m,
    {{ P }} c [[m]] {{ Q }} ->
    P, [c] m, Q.
Proof.
Admitted.

(* Depends on the admitted [completeness] *)
Theorem equivalence : forall P c Q m, interpret_spec P Q c m.
Proof.
  intros. split.
  - exact (soundness c P Q m).
  - exact (completeness c P Q m).
Qed.

(** ** Tier 2: one composed step *)

Definition interpret_spec2 (m1 m2 : mode) (PA : aprop2) (c1 c2 : astmt)
                           (QB : aprop2) : Prop :=
  AL m1 , m2 :: PA |- c1 // c2 ==> QB <-> al_underc_r m1 m2 PA c1 c2 QB.

Theorem completeness2 :
  forall m1 m2 PA c1 c2 QB,
    al_underc_r m1 m2 PA c1 c2 QB ->
    AL m1 , m2 :: PA |- c1 // c2 ==> QB.
Proof.
Admitted.

(* Depends on the admitted [completeness2] *)
Theorem equivalence2 : forall m1 m2 PA c1 c2 QB, interpret_spec2 m1 m2 PA c1 c2 QB.
Proof.
  intros. split.
  - exact (soundness2 m1 m2 PA c1 c2 QB).
  - exact (completeness2 m1 m2 PA c1 c2 QB).
Qed.
