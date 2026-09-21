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
induction c as [ | x e | x | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | B
               | c IH | c1 IH1 c2 IH2 | chn x | chn x | B
               | c1 IH1 c2 IH2 | x e c IH ];
  intros P Q m DS.
  - eapply DConsequence with (Q := P).
    -- intros s Ps. exact Ps.
    -- intros s Qs. destruct (DS s Qs). invs H. invs H1. assumption.
    -- constructor.
  - eapply DConsequence with  (P := P)
    (Q := fun sig => exists x', P (mode_upd m sig x x') /\
            mode_store m sig x = e (mode_store m (mode_upd m sig x x'))).
    -- intros s Ps. apply Ps.
    -- intros s Qs. destruct (DS s Qs) as (s' & HP & H). invs H.
       --- eexists. split. rewrite mode_upd_shadow, mode_upd_store_eq. exact HP.
          rewrite mode_store_upd_eq,  mode_upd_shadow, mode_upd_store_eq. reflexivity.  
       --- eexists. split. rewrite mode_upd_shadow, mode_upd_store_eq. exact HP.
          rewrite mode_store_upd_eq,  mode_upd_shadow, mode_upd_store_eq. reflexivity.  
    -- constructor.
  - eapply DConsequence with (P := P) (Q := fun sig => exists x', P (mode_upd m sig x x')).
    -- intros s Ps. exact Ps.  
    -- intros s Qs. destruct (DS s Qs) as (s' & HP & H). invs H.
      --- eexists. rewrite mode_upd_shadow, mode_upd_store_eq. exact HP.
      --- eexists. rewrite mode_upd_shadow, mode_upd_store_eq. exact HP.
    -- constructor.  
  - set (Mid := fun s2 => exists s1, P s1 /\ [[c1]] m |=> (s1, s2)).
    set (Qnm := fun s3 => Q s3 /\ exists s2, Mid s2 /\ [[c2]] m |=> (s2, s3)).

    assert (DS_C1_ok : {{P}} c1 [[m]] {{Mid}}).
      intros s2 (s & Ps & DS'). now exists s.
    
    assert (DS_C2_ok : {{Mid}} c2 [[m]] {{Qnm}}).
      intros s2 (Qs2 & s & Ps & DS'). now exists s.

    specialize (IH1 P Mid m DS_C1_ok).
    specialize (IH2 Mid Qnm m DS_C2_ok).

    pose proof (DSeq P Mid Qnm c1 c2 m IH1 IH2) as D_nm.
    eapply DConsequence with (P := P) (Q := fun s => Qnm s). 
    
    now intro.

    intros s HQ. destruct (DS s HQ) as (s1 & HP & Hseq). split. assumption. invs Hseq.   
    exists s2. split. exists s1. now split. assumption.
    
    assumption.
  -  






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
