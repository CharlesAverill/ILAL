(** * Completeness of AL, tiers 1 to 3: statements and machinery

    Mirrors [IL.v]'s [interpret_spec] / [completeness] / [equivalence] for the
    single-thread system ([derivable] vs [under_approximate]), the composed
    one-step system ([derivable2] vs [al_underc_r]), its iteration
    ([derivable_star] vs [al_underc_star]) and runs of a fixed system
    ([derivable_run] vs [al_underc_run]).

*)
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
  - set (Mid1 := fun s2 => exists s1, P s1 /\ [[c1]] m |=> (s1, s2)).
    set (Mid2 := fun s2 => exists s1, P s1 /\ [[c2]] m |=> (s1, s2)).
    set (Or := fun s2 => Mid1 s2 \/ Mid2 s2).

    eapply DConsequence with (Q := Or).
    
    -- shelve.
    -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & DS'). invs DS'.
      --- left. now exists s'.
      --- right. now exists s'.
    -- assert (DS_C1 : {{P}} c1  [[m]] {{Mid1}}).
         intros s (s' & Ps' & DS'). now exists s'.

        assert (DS_C2 : {{P}} c2  [[m]] {{Mid2}}).
         intros s (s' & Ps' & DS'). now exists s'.

       specialize (IH1 P Mid1 m DS_C1).
       specialize (IH2 P Mid2 m DS_C2).

       assert (A1 : P, [c1 <||> c2] m, Mid1) by now constructor.
       assert (A2 : P, [c1 <||> c2] m, Mid2) by now constructor.

      constructor; eassumption.

      Unshelve. intros s Ps. invs Ps; assumption.

    - eapply DConsequence with (Q := aand_lift m P B).
      -- intros s Ps. exact Ps.
      -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & DS'). invs DS'. now split.
      -- constructor.
    - set (Pn := fun n => post (ds (aRepeat c n) m) P).
      eapply DConsequence with (P := Pn O) (Q := fun sig => exists n, Pn n sig).
      -- intros s Ps. destruct Ps as (s0 & ps0 & D). now invs D.
      -- intros s Qs. apply (arepeat_is_star c m P s (DS s Qs)).
      -- apply DBackwardVariant. intros n. apply IH. intros s Ps. destruct Ps as (s0 & ps0 & D).
      invs D. exists s2. split. now exists s0. assumption.
    - set (Mid1 := fun s2 => exists s1, P s1 /\ [[c1]] m |=> (s1, s2)).
      set (Mid2 := fun s2 => exists s1, P s1 /\ [[c2]] m |=> (s1, s2)).
      set (Or := fun s2 => Mid1 s2 \/ Mid2 s2).

      eapply DConsequence with (Q := Or).
      
      -- shelve.
      -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & DS'). invs DS'.
        --- left. now exists s'.
        --- right. now exists s'.
      -- assert (DS_C1 : {{P}} c1  [[m]] {{Mid1}}).
          intros s (s' & Ps' & DS'). now exists s'.

          assert (DS_C2 : {{P}} c2  [[m]] {{Mid2}}).
          intros s (s' & Ps' & DS'). now exists s'.

        specialize (IH1 P Mid1 m DS_C1).
        specialize (IH2 P Mid2 m DS_C2).

        assert (A1 : P, [c1 <+> c2] m, Mid1) by now constructor.
        assert (A2 : P, [c1 <+> c2] m, Mid2) by now constructor.

        constructor; eassumption.

        Unshelve. intros s Ps. invs Ps; assumption.
    - eapply DConsequence with (Q := fun sig => exists v x' l,
            P (mode_chan_upd m (mode_upd m sig x x') chn (v :: l))
            /\ mode_chan m sig chn = l
            /\ mode_store m sig x = v).
      -- intros s Ps. exact Ps.
      -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & H). invs H. 
        --- exists v, (s'.(vstate).(s) x), l. destruct s' as [ [vs vc] a]. simpl in *.
        unfold update_vchannel, update_victim,
               update_achannel, update_adversary in *; simpl in *. split. rewrite !update_shadow, !state_upd_eq; auto. split; rewrite update_eq; reflexivity.
        --- exists v, (s'.(astate).(s) x), l. destruct s' as [ vs [as0 ac] ]. simpl in *.
        unfold update_vchannel, update_victim,
               update_achannel, update_adversary in *; simpl in *. split. rewrite !update_shadow, !state_upd_eq; auto. split; rewrite update_eq; reflexivity.
      -- constructor.
    - eapply DConsequence with (Q := (fun sig => exists l,
            P (mode_chan_upd m sig chn l)
            /\ mode_chan m sig chn = l ++ [mode_store m sig x])%list).
      -- intros s Ps. exact Ps.
      -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & H). invs H.
        --- exists (s'.(vstate).(ch) chn). destruct s' as [ [vs vc] a]. simpl in *. unfold update_vchannel, update_victim,
               update_achannel, update_adversary in *; simpl in *. split. rewrite !update_shadow, !state_upd_eq; auto. rewrite update_eq. reflexivity.
        ---  exists (s'.(astate).(ch) chn). destruct s' as [ vs [as0 ac] ]. simpl in *. unfold update_vchannel, update_victim,
               update_achannel, update_adversary in *; simpl in *. split. rewrite !update_shadow, !state_upd_eq; auto. rewrite update_eq. reflexivity.
      -- constructor. 
    - destruct m. 
      -- eapply DConsequence with (Q := fun _ => False).
        --- intros s Ps. exact Ps.
        --- intros s Qs. destruct (DS s Qs) as (s' & Ps' & H). invs H.
        --- apply DEmpty.
      -- eapply DConsequence with (P := aor P P) (Q := aor (aand_lift Ad P B) (aand P (anot (lift Ad B)))).
        --- intros s Ps. invs Ps; assumption.
        --- intros s Qs. destruct (DS s Qs) as (s' & Ps' & H). invs H. 
          left. split; assumption. 
          right. split; assumption.
        --- constructor; constructor.
    - eapply DConsequence with (Q := fun _ => False).
      -- intros s Ps. exact Ps.
      -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & H). invs H.
      -- apply DEmpty.
    - set (Entry := (fun sig => exists sig0, P sig0 /\ sig = mode_upd m sig0 x (e (mode_store m sig0)))). 
       eapply DConsequence with (Q := fun sig => exists (sb : estate) (x0 : N),
        (exists s0, Entry s0 /\ [[c]] m |=> (s0, sb)) /\ sig = mode_upd m sb x x0).
      -- intros s Ps. exact Ps.
      -- intros s Qs. destruct (DS s Qs) as (s' & Ps' & H). invs H. exists sig', x_out. split. 
        exists (mode_upd m s' x (e (mode_store m s'))). split. exists s'. now split. assumption.
        reflexivity.
      -- apply DLocal, IH.  
      intros s2 (s & Ps & DS'). now exists s.
    Qed.
     
 


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

Definition sing2 (X Y : estate) : aprop2 :=
  aprod (fun sp => sp = X) (fun sa => sa = Y).

Lemma derivable2_singleton : forall m1 m2 c1 c2 X Y,
  AL m1 , m2 :: (sing2 X Y) |- c1 // c2 ==> (al_postc_r m1 m2 c1 c2 (sing2 X Y)).
Proof.
  intros m1 m2 c1 c2 X Y.
  (* One index per kind of [cds] step: [CInd], or a transfer on channel [s] *)
  set (T := ((unit + string) + string)%type).
  set (Post := fun (t : T) => (
    match t with
    | inl (inl _) =>
        aprod (post (ds c1 m1) (fun sp => sp = X)) (post (ds c2 m2) (fun sa => sa = Y))
    | inl (inr s) => fun sq sb => exists v l1 l2,
        sing2 X Y (sq[[ s :=vch v :: l1 ]]) (sb[[ s :=ach l2 ]])
        /\ sq.(vstate).(ch) s = l1
        /\ sb.(astate).(ch) s = (l2 ++ [v])%list
    | inr s => fun sq sb => exists v l1 l2,
        sing2 X Y (sq[[ s :=vch l2 ]]) (sb[[ s :=ach v :: l1 ]])
        /\ sb.(astate).(ch) s = l1
        /\ sq.(vstate).(ch) s = (l2 ++ [v])%list
    end : aprop2)).
  eapply D2Consequence with
    (PA := fun sp sa => exists t : T, sing2 X Y sp sa)
    (QB := fun sq sb => exists t, Post t sq sb).
  - intros sp sa [_ H]. exact H.
  - intros sq sb (sp & sa & [-> ->] & Hcds). invs Hcds.
    -- exists (inl (inl tt)). split; [exists X | exists Y]; now split.
    -- exists (inl (inr s)), v, l1, (Y.(astate).(ch) s). repeat split.
       --- now rewrite vch_shadow, vch_eq.
       --- now rewrite ach_shadow, ach_eq.
       --- apply vch_get.
       --- apply ach_get.
    -- exists (inr s), v, l1, (X.(vstate).(ch) s). repeat split.
       --- now rewrite vch_shadow, vch_eq.
       --- now rewrite ach_shadow, ach_eq.
       --- apply ach_get.
       --- apply vch_get.
  - apply (D2DisjI m1 m2 T (fun _ => sing2 X Y) Post).
    intros [ [ [] | s ] | s ].
    -- apply D2Par; apply completeness; intros s H; exact H.
    -- exact (D2Com m1 m2 (sing2 X Y) c1 c2 s).
    -- exact (D2ComAP m1 m2 (sing2 X Y) c1 c2 s).
Qed.

Lemma derivable2_exact_post : forall m1 m2 PA c1 c2,
  AL m1 , m2 :: PA |- c1 // c2 ==> (al_postc_r m1 m2 c1 c2 PA).
Proof.
  intros m1 m2 PA c1 c2.
  (* One index per pair in [PA] *)
  set (I := { p : estate * estate | PA (fst p) (snd p) }).
  set (Pre := fun (i : I) => sing2 (fst (proj1_sig i)) (snd (proj1_sig i))).
  eapply D2Consequence with
    (PA := fun sp sa => exists i, Pre i sp sa)
    (QB := fun sq sb => exists i, al_postc_r m1 m2 c1 c2 (Pre i) sq sb).
  - intros sp sa [ [ [X Y] HXY ] [-> ->] ]. exact HXY.
  - intros sq sb (sp & sa & HPA & Hcds).
    exists (exist _ (sp, sa) HPA), sp, sa. split. now split. exact Hcds.
  - apply (D2DisjI m1 m2 I Pre (fun i => al_postc_r m1 m2 c1 c2 (Pre i))).
    intros [ [X Y] HXY ]. apply derivable2_singleton.
Qed.


Theorem completeness2 :
  forall m1 m2 PA c1 c2 QB,
    al_underc_r m1 m2 PA c1 c2 QB ->
    AL m1 , m2 :: PA |- c1 // c2 ==> QB.
Proof.
  intros m1 m2 PA c1 c2 QB H_AL.
  eapply D2Consequence with (PA := PA) (QB := al_postc_r m1 m2 c1 c2 PA).
  - now intros a b H. 
  - apply H_AL.
  - apply derivable2_exact_post.
Qed.

Theorem equivalence2 : forall m1 m2 PA c1 c2 QB, interpret_spec2 m1 m2 PA c1 c2 QB.
Proof.
  intros. split.
  - exact (soundness2 m1 m2 PA c1 c2 QB).
  - exact (completeness2 m1 m2 PA c1 c2 QB).
Qed.

(** ** Tier 3: iterated composed steps ([cds_star]) *)

Definition interpret_spec_star (m1 m2 : mode) (PA : aprop2) (c1 c2 : astmt)
                               (QB : aprop2) : Prop :=
  AL* m1 , m2 :: PA |- c1 // c2 ==> QB <-> al_underc_star m1 m2 PA c1 c2 QB.

(* [PA] after [n] composed steps *)
Fixpoint post_iter (m1 m2 : mode) (c1 c2 : astmt) (PA : aprop2) (n : nat) : aprop2 :=
  match n with
  | O => PA
  | S n' => al_postc_r m1 m2 c1 c2 (post_iter m1 m2 c1 c2 PA n')
  end.

Lemma star_is_iter : forall m1 m2 c1 c2 PA sq sb,
  al_postc_star m1 m2 c1 c2 PA sq sb -> exists n, post_iter m1 m2 c1 c2 PA n sq sb.
Proof.
  intros m1 m2 c1 c2 PA sq sb (sp & sa & HP & Hs).
  remember (sp, sa) as p eqn:Ep. remember (sq, sb) as r eqn:Er.
  revert sq sb Er. induction Hs as [ p | p [qp qa] r Hs IH Step ]; intros sq sb Er; subst.
  - injection Er as -> ->. now exists O.
  - destruct (IH eq_refl qp qa eq_refl) as (n & Hn).
    exists (S n), qp, qa. split. exact Hn. exact Step.
Qed.

Theorem completeness_star :
  forall m1 m2 PA c1 c2 QB,
    al_underc_star m1 m2 PA c1 c2 QB ->
    AL* m1 , m2 :: PA |- c1 // c2 ==> QB.
Proof.
  intros m1 m2 PA c1 c2 QB H.
  eapply DSConsequence with (PA := post_iter m1 m2 c1 c2 PA O).
  - now intros sp sa.
  - intros sq sb HQ. exact (star_is_iter _ _ _ _ _ _ _ (H sq sb HQ)).
  - apply DSVariant. intros n. apply derivable2_exact_post.
Qed.

Theorem equivalence_star : forall m1 m2 PA c1 c2 QB,
  interpret_spec_star m1 m2 PA c1 c2 QB.
Proof.
  intros. split.
  - exact (soundness_star m1 m2 PA c1 c2 QB).
  - exact (completeness_star m1 m2 PA c1 c2 QB).
Qed.

(** ** Runs of a fixed system ([cds_run]) *)

Definition interpret_spec_run (m1 m2 : mode) (PA : aprop2) (c1 c2 : astmt)
                              (QB : aprop2) : Prop :=
  derivable_run m1 m2 PA c1 c2 QB <-> al_underc_run m1 m2 PA c1 c2 QB.

Definition sing2p (p : estate * estate) : aprop2 := fun sp sa => (sp, sa) = p.

(* A run is derivable between singletons; each step reuses [completeness2] *)
Lemma run_derivable : forall m1 m2 c1 c2 p q,
  cds_run m1 m2 c1 c2 p q -> derivable_run m1 m2 (sing2p p) c1 c2 (sing2p q).
Proof.
  intros m1 m2 c1 c2 p q H. induction H.
  - apply DRDone.
  - eapply DRStep; [ | eassumption | eassumption | eassumption ].
    apply completeness2. intros sq sb E. exists (fst p), (snd p).
    split. now destruct p. rewrite E. now destruct p.
Qed.

Theorem completeness_run :
  forall m1 m2 PA c1 c2 QB,
    al_underc_run m1 m2 PA c1 c2 QB ->
    derivable_run m1 m2 PA c1 c2 QB.
Proof.
  intros m1 m2 PA c1 c2 QB H.
  (* One index per run from a [PA] pair *)
  set (I := { r : (estate * estate) * (estate * estate) |
              PA (fst (fst r)) (snd (fst r)) /\ cds_run m1 m2 c1 c2 (fst r) (snd r) }).
  eapply DRConsequence with
    (PA := fun sp sa => exists i : I, sing2p (fst (proj1_sig i)) sp sa)
    (QB := fun sq sb => exists i : I, sing2p (snd (proj1_sig i)) sq sb).
  - intros sp sa [ [r Hr] E ]. simpl in E. rewrite <- E in Hr. apply Hr.
  - intros sq sb HQ. destruct (H sq sb HQ) as (sp & sa & HP & Hs).
    now exists (exist _ ((sp, sa), (sq, sb)) (conj HP Hs)).
  - apply DRDisjI. intros [r Hr]. exact (run_derivable _ _ _ _ _ _ (proj2 Hr)).
Qed.

Theorem equivalence_run : forall m1 m2 PA c1 c2 QB,
  interpret_spec_run m1 m2 PA c1 c2 QB.
Proof.
  intros. split.
  - exact (soundness_run m1 m2 PA c1 c2 QB).
  - exact (completeness_run m1 m2 PA c1 c2 QB).
Qed.
