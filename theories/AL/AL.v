From Stdlib Require Export NArith String.
From ILAL Require Export AL.language state tactics.
From Stdlib Require Import List.
Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.

(** Denotational Relational Semantics *)
(* Table 8 *)

Declare Scope al_ds_scope.
Open Scope al_ds_scope.

Definition evaluation : Type := (estate * estate) -> Prop.

Inductive mode : Set := Ok | Ad.

Reserved Notation
  "[[ c ]] m |=> ( s , s' )"
  (at level 0, c custom al_stmt at level 99,
   m constr, s constr, s' constr).

Open Scope al_scope.

Definition mode_store (m : mode) (sig : estate) : state :=
  match m with
  | Ok => sig.(vstate).(s)
  | Ad => sig.(astate).(s)
  end.

(* Mode-aware update *)
Definition mode_upd (m : mode) (sig : estate) (x : id) (v : N) : estate :=
  match m with
  | Ok => sig[[ x :=v v ]]
  | Ad => sig[[ x :=a v ]]
  end.

(* Channel [k]'s contents in [m]'s store *)
Definition mode_chan (m : mode) (sig : estate) (k : id) : channel :=
  match m with
  | Ok => sig.(vstate).(ch) k
  | Ad => sig.(astate).(ch) k
  end.

(* [k] :=m [l] *)
Definition mode_chan_upd (m : mode) (sig : estate) (k : id) (l : channel) : estate :=
  match m with
  | Ok => sig[[ k :=vch l ]]
  | Ad => sig[[ k :=ach l ]]
  end.

Inductive ds : astmt -> mode -> (estate * estate) -> Prop :=
| EDSkip m (s : estate) :
    [[ skip ]] m |=> (s, s)
| EDAssume (B : prop) m (sig : estate) :
    B (mode_store m sig) ->
    [[ assume(B) ]] m |=> (sig, sig)
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
      (sig, sig[[ ch_id :=vch (sig.(vstate).(ch) ch_id ++ [sig.(vstate).(s) x]) ]])%list
| EDWriteA (ch_id x : id) (sig : estate) :
    [[ write(ch_id, x) ]] Ad |=>
      (sig, sig[[ ch_id :=ach (sig.(astate).(ch) ch_id ++ [sig.(astate).(s) x]) ]])%list
(** adv_assert(P): adversarial assert *)
| EDAdvAssertSuccess P (sig : estate) :
    P sig.(astate).(s) ->
    [[ adv_assert(P) ]] Ad |=> (sig, sig)
| EDAdvAssertFailure P (sig : estate) :
    ~ P sig.(astate).(s) ->
    [[ adv_assert(P) ]] Ad |=> (sig, sig)
(** C1 + C2: nondeterministic choice *)
| EDChoiceL c1 c2 m s1 s2 :
    [[ c1 ]] m |=> (s1, s2) ->
    [[ c1 <+> c2 ]] m |=> (s1, s2)
| EDChoiceR c1 c2 m s1 s2 :
    [[ c2 ]] m |=> (s1, s2) ->
    [[ c1 <+> c2 ]] m |=> (s1, s2)
(** C*: Kleene iteration *)
| EDStar0 c m (s : estate) :
    [[ c** ]] m |=> (s, s)
| EDStarN c m s1 s2 s3 :
    [[ c** ]] m |=> (s1, s2) ->
    [[ c ]] m |=> (s2, s3) ->
    [[ c** ]] m |=> (s1, s3)
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
  (at level 90, c custom al_stmt at level 99, m constr) : al_scope.

Definition over_approximate (P : aprop) (c : astmt) (m : mode) (Q : aprop) : Prop :=
  forall s, post (ds c m) P s -> Q s.

Notation "<| P |> c [[ m ]] <| Q |>" :=
  (over_approximate P c m Q)
  (at level 0, c custom al_stmt at level 99, m constr) : al_scope.

(** Lifting predicates into adversarial predicates  *)
Definition lift (m : mode) (B : prop) : aprop :=
  fun sig => B (mode_store m sig).

Definition aand (P : aprop) (Q : aprop) : aprop :=
  fun sig => P sig /\ Q sig.

Definition aor (P : aprop) (Q : aprop) : aprop :=
  fun sig => P sig \/ Q sig.

Definition anot (P : aprop) : aprop :=
  fun sig => ~ P sig.

(* [P /\ B[m]] *)
Definition aand_lift (m : mode) (P : aprop) (B : prop) : aprop :=
  aand P (lift m B).

(** Definition 2 *)

Definition aprop2 : Type := estate -> estate -> Prop.

Definition al_post2 (c1 c2 : astmt) (P A : aprop) : aprop2 :=
  fun sq sb =>
    exists sp sa, P sp /\ A sa /\
      ds c1 Ok (sp, sq) /\ ds c2 Ad (sa, sb).

(* The under-approximate adversarial triple [p][a] c1 || c2 [q][b] *)
Definition al_under2 (P A : aprop) (c1 c2 : astmt) (Q B : aprop) : Prop :=
  forall sq sb, Q sq /\ B sb ->
    al_post2 c1 c2 P A sq sb.

Notation "<[[ P ]][[ A ]] c1 || c2 [[ Q ]][[ B ]]>" :=
  (al_under2 P A c1 c2 Q B)
  (at level 0, c1 custom al_stmt at level 99, c2 custom al_stmt at level 99) : al_scope.

Open Scope al_scope.

(** Definition 3 *)

Theorem and_or_symmetry : forall P Q1 Q2 c m,
  ({{ P }} c [[m]] {{ Q1 }} /\ {{ P }} c [[m]] {{ Q2 }}) <->
  {{ P }} c [[m]] {{ fun s => Q1 s \/ Q2 s }}.
Proof.
  intros. split; intros.
  - destruct H as [H1 H2]. intros s [HQ1 | HQ2]; auto.
  - split; intros s Hs; auto.
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
  exists s'. auto.
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
  eapply HO. exists s'. auto.
Qed.

(** Lemma 1 *)

Lemma characterization :
  forall P Q A B C1 C2,
  <[[P]][[A]] C1 || C2 [[Q]][[B]]> <->
  (forall sq sb, Q sq -> B sb ->
    exists sp sa, P sp /\ A sa /\
     ds C1 Ok (sp, sq) /\ ds C2 Ad (sa, sb)).
Proof.
  intros. unfold al_under2, al_post2. split; intro; intros.
  - specialize (H _ _ (conj H0 H1)). destruct H as (sq' & sb' & HQ & HB & DS1 & DS2).
    exists sq', sb'. auto.
  - destruct H0. specialize (H _ _ H0 H1). destruct H as (sq' & sb' & HQ & HB & DS1 & DS2).
    exists sq', sb'. auto.
Qed.

(** Proof rules *)
(* Page 9 *)

Reserved Notation
         "P , [ c ] m , Q"
         (at level 40, c custom al_stmt at level 99, P constr, Q constr).
Inductive derivable : aprop -> astmt -> mode -> aprop -> Prop :=
(* The empty postcondition is always under-approximate *)
| DEmpty : forall P c m,
    P, [c] m, (fun _ => False)
(* Unit *)
| DUnit : forall m P,
    P, [skip] m, P
(* Consequence *)
| DConsequence : forall P P' Q Q' c m
    (L: P ->> P')
    (R: Q' ->> Q)
    (Cons: P, [c] m, Q),
    P', [c] m, Q'
(* Disjunction *)
| DDisj : forall P1 Q1 P2 Q2 c m,
    P1, [c] m, Q1 ->
    P2, [c] m, Q2 ->
    (aor P1 P2), [c] m, (aor Q1 Q2)
(* Sequencing *)
| DSeq : forall P Q R c1 c2 m,
    P, [c1] m, Q ->
    Q, [c2] m, R ->
    P, [c1 ;; c2] m, R
(* Choice *)
| DChoiceL : forall P Q c1 c2 m,
    P, [c1] m, Q ->
    P, [c1 <+> c2] m, Q
| DChoiceR : forall P Q c1 c2 m,
    P, [c2] m, Q ->
    P, [c1 <+> c2] m, Q
(* Iterate Zero *)
| DIterZero : forall P c m,
    P, [c**] m, P
(* Iterate non-zero *)
| DIterNonzero : forall P Q c m,
    P, [c** ;; c] m, Q ->
    P, [c**] m, Q
(* Backward variant: a varying invariant [P n] preserved by one
   iteration witnesses the iterated postcondition [exists n, P n] *)
| DBackwardVariant : forall (P : nat -> aprop) c m,
    (forall n, (P n), [c] m, (P (S n))) ->
    (P O), [c**] m, (fun sig => exists n, P n sig)
(* Assume: [eps: P] assume(B) [eps: P /\ B] *)
| DAssume : forall P B m,
    P, [assume(B)] m, (aand_lift m P B)
(* Assignment *)
| DAssign : forall P x (e : expression) m,
    P, [x := e] m,
       (fun sig => exists x', P (mode_upd m sig x x') /\
                   mode_store m sig x = e (mode_store m (mode_upd m sig x x')))
(* Rand *)
| DRand : forall P x m,
    P, [x := rand()] m,
       (fun sig => exists x', P (mode_upd m sig x x'))
(* Read(s,x): consume the head [v] of channel [s] into [x] *)
| DRead : forall P (s x : id) m,
    P, [read(s, x)] m,
       (fun sig => exists v x' l,
            P (mode_chan_upd m (mode_upd m sig x x') s (v :: l))
            /\ mode_chan m sig s = l
            /\ mode_store m sig x = v)
(* Write(s,x): append the value of [x] to the end of channel [s] *)
| DWrite : forall P (s x : id) m,
    P, [write(s, x)] m,
       (fun sig => exists l,
            P (mode_chan_upd m sig s l)
            /\ mode_chan m sig s = l ++ [mode_store m sig x])%list
(* Adversarial assertion, success branch *)
| DAdvAssertSuccess : forall Q B,
    Q, [adv_assert(B)] Ad, (aand_lift Ad Q B)
(* Adversarial assertion, failure branch *)
| DAdvAssertFailure : forall Q B,
    Q, [adv_assert(B)] Ad, (aand Q (anot (lift Ad B)))
where "P , [ c ] m , Q" := (derivable P c m Q).

Definition denote (c : astmt) (m : mode) : evaluation :=
  fun '(s1, s2) => [[ c ]] m |=> (s1, s2).

Definition interpret_spec (P Q : aprop) (c : astmt) m : Prop :=
  P, [c] m, Q <-> {{P}} c [[m]] {{Q}}.

Fixpoint nRepeat (c : astmt) (n : nat) : astmt :=
  match n with
  | O => ASkip
  | S n' => ASeq (nRepeat c n') c
  end.

Lemma star_equiv : forall c m s1 s2,
  [[ c** ;; c ]] m |=> (s1, s2) ->
  [[ c** ]] m |=> (s1, s2).
Proof.
  intros c m s1 s2 H. invs H. econstructor; eassumption.
Qed.

Lemma nRepeat_star : forall c m n s1 s2,
  ds (nRepeat c n) m (s1, s2) ->
  [[ c** ]] m |=> (s1, s2).
Proof.
  intros c m n. induction n; intros s1 s2 H.
  - simpl in H. invs H. constructor.
  - simpl in H. invs H. econstructor; eauto.
Qed.

(* Conversely, every star execution is some finite [n]-fold repetition *)
Lemma star_nRepeat : forall c m s1 s2,
  [[ c** ]] m |=> (s1, s2) ->
  exists n, ds (nRepeat c n) m (s1, s2).
Proof.
  intros c m s1 s2 H.
  remember <{ c** }> as cs eqn:E.
  induction H; invs E.
  - exists O. constructor.
  - destruct (IHds1 eq_refl) as (n & Hn).
    exists (S n). econstructor; eauto.
Qed.

Lemma repeat_is_star : forall c m P s,
  post (denote <{ c** }> m) P s ->
  exists n, post (denote (nRepeat c n) m) P s.
Proof.
  intros c m P s (s' & Ps' & DS). unfold denote in DS.
  apply star_nRepeat in DS. destruct DS as (n & Hn).
  exists n, s'. now split.
Qed.

Lemma step_assign_ok : forall sig x (e : expression) x',
  sig.(vstate).(s) x = e ((sig[[ x :=v x' ]]).(vstate).(s)) ->
  [[ x := e ]] Ok |=> (sig[[ x :=v x' ]], sig).
Proof.
  intros [(vs & vc) (as_  & ac)] x e x' Eq. simpl in *.
  replace ({| vstate := {| s := vs; ch := vc |};
              astate := {| s := as_; ch := ac |} |})
    with ((({| vstate := {| s := vs; ch := vc |};
               astate := {| s := as_; ch := ac |} |})[[ x :=v x' ]])
            [[ x :=v e (({| vstate := {| s := vs; ch := vc |};
                           astate := {| s := as_; ch := ac |} |})[[ x :=v x' ]]).(vstate).(s) ]])
    at 2.
    apply EDAssignV.
  unfold update_victim. simpl. f_equal. f_equal.
  now rewrite update_shadow, <- Eq, state_upd_eq.
Qed.

Lemma step_assign_ad : forall sig x (e : expression) x',
  sig.(astate).(s) x = e ((sig[[ x :=a x' ]]).(astate).(s)) ->
  [[ x := e ]] Ad |=> (sig[[ x :=a x' ]], sig).
Proof.
  intros [(vs & vc) (as_  & ac)] x e x' Eq. simpl in *.
  replace ({| vstate := {| s := vs; ch := vc |};
              astate := {| s := as_; ch := ac |} |})
    with ((({| vstate := {| s := vs; ch := vc |};
               astate := {| s := as_; ch := ac |} |})[[ x :=a x' ]])
            [[ x :=a e (({| vstate := {| s := vs; ch := vc |};
                           astate := {| s := as_; ch := ac |} |})[[ x :=a x' ]]).(astate).(s) ]])
    at 2.
    apply EDAssignA.
  unfold update_adversary. simpl. f_equal. f_equal.
  now rewrite update_shadow, <- Eq, state_upd_eq.
Qed.

Lemma step_rand_ok : forall sig x x',
  [[ x := rand() ]] Ok |=> (sig[[ x :=v x' ]], sig).
Proof.
  intros [(vs & vc) (as_ & ac)] x x'.
  assert (E : (({| vstate := {| s := vs; ch := vc |};
                   astate := {| s := as_; ch := ac |} |})[[ x :=v x' ]])
                [[ x :=v vs x ]]
              = {| vstate := {| s := vs; ch := vc |};
                   astate := {| s := as_; ch := ac |} |}).
  { unfold update_victim. simpl. f_equal. f_equal.
    now rewrite update_shadow, state_upd_eq. }
  rewrite <- E at 2. apply EDRandV.
Qed.
 
Lemma step_rand_ad : forall sig x x',
  [[ x := rand() ]] Ad |=> (sig[[ x :=a x' ]], sig).
Proof.
  intros [(vs & vc) (as_ & ac)] x x'.
  assert (E : (({| vstate := {| s := vs; ch := vc |};
                   astate := {| s := as_; ch := ac |} |})[[ x :=a x' ]])
                [[ x :=a as_ x ]]
              = {| vstate := {| s := vs; ch := vc |};
                   astate := {| s := as_; ch := ac |} |}).
  { unfold update_adversary. simpl. f_equal. f_equal.
    now rewrite update_shadow, state_upd_eq. }
  rewrite <- E at 2. apply EDRandA.
Qed.

Lemma step_read_ok : forall sig (s_ x : id) v x' l,
  sig.(vstate).(ch) s_ = l ->
  sig.(vstate).(s) x = v ->
  [[ read(s_, x) ]] Ok |=> ((sig[[ x :=v x' ]])[[ s_ :=vch v :: l ]], sig).
Proof.
  intros [(vs & vc) (as_ & ac)] s x v x' l Hl Hx. simpl in *.
  replace ({| vstate := {| s := vs; ch := vc |};
              astate := {| s := as_; ch := ac |} |})
    with ((((({| vstate := {| s := vs; ch := vc |};
                 astate := {| s := as_; ch := ac |} |})[[ x :=v x' ]])
              [[ s :=vch v :: l ]])[[ x :=v v ]])[[ s :=vch l ]])
    at 2.
  - apply EDReadV. unfold update_vchannel, update_victim.
    simpl. now rewrite update_eq.
  - unfold update_vchannel, update_victim. simpl. f_equal.
    f_equal; rewrite update_shadow.
    now rewrite <- Hx, state_upd_eq.
    now rewrite <- Hl, state_upd_eq.
Qed.

Lemma step_read_ad : forall sig (s_ x : id) v x' l,
  sig.(astate).(ch) s_ = l ->
  sig.(astate).(s) x = v ->
  [[ read(s_, x) ]] Ad |=> ((sig[[ x :=a x' ]])[[ s_ :=ach v :: l ]], sig).
Proof.
  intros [(vs & vc) (as_ & ac)] s x v x' l Hl Hx. simpl in *.
  replace ({| vstate := {| s := vs; ch := vc |};
              astate := {| s := as_; ch := ac |} |})
    with ((((({| vstate := {| s := vs; ch := vc |};
                 astate := {| s := as_; ch := ac |} |})[[ x :=a x' ]])
              [[ s :=ach v :: l ]])[[ x :=a v ]])[[ s :=ach l ]])
    at 2.
  - apply EDReadA. unfold update_achannel, update_adversary.
    simpl. now rewrite update_eq.
  - unfold update_achannel, update_adversary. simpl. f_equal.
    f_equal; rewrite update_shadow.
    now rewrite <- Hx, state_upd_eq.
    now rewrite <- Hl, state_upd_eq.
Qed.

Lemma step_write_ok : forall sig (s_ x : id) l,
  sig.(vstate).(ch) s_ = (l ++ [sig.(vstate).(s) x])%list ->
  [[ write(s_, x) ]] Ok |=> (sig[[ s_ :=vch l ]], sig).
Proof.
  intros [(vs & vc) (as_ & ac)] s x l Hl. simpl in *.
  assert (E : ({| vstate := {| s := vs; ch := vc |};
                  astate := {| s := as_; ch := ac |} |})
              = (({| vstate := {| s := vs; ch := update vc s l |};
                     astate := {| s := as_; ch := ac |} |})
                 [[ s :=vch ((update vc s l) s ++ [vs x]) ]])%list).
  { unfold update_vchannel. simpl. rewrite update_eq.
    f_equal. f_equal. now rewrite update_shadow, <- Hl, state_upd_eq. }
  unfold update_vchannel. simpl. rewrite E. apply EDWriteV.
Qed.

Lemma step_write_ad : forall sig (s_ x : id) l,
  sig.(astate).(ch) s_ = (l ++ [sig.(astate).(s) x])%list ->
  [[ write(s_, x) ]] Ad |=> (sig[[ s_ :=ach l ]], sig).
Proof.
  intros [(vs & vc) (as_ & ac)] s x l Hl. simpl in *.
  assert (E : ({| vstate := {| s := vs; ch := vc |};
                  astate := {| s := as_; ch := ac |} |})
              = (({| vstate := {| s := vs; ch := vc |};
                     astate := {| s := as_; ch := (update ac s l) |} |})
                 [[ s :=ach ((update ac s l) s ++ [as_ x]) ]])%list).
  { unfold update_achannel. simpl. rewrite update_eq.
    f_equal. f_equal. now rewrite update_shadow, <- Hl, state_upd_eq. }
  unfold update_achannel. simpl. rewrite E. apply EDWriteA.
Qed.

Theorem soundness :
  forall c P Q m,
    P, [c] m, Q ->
    {{P}} c [[m]] {{Q}}.
Proof.
  intros c P Q m H. induction H.
  - (* DEmpty *) intros s Fs. contradiction.
  - (* DUnit *) intros s Ps. exists s. split. assumption. constructor.
  - (* DConsequence *) intros s Q's. apply R in Q's.
    destruct (IHderivable s Q's) as (s' & Qs' & DS).
    exists s'. auto.
  - (* DDisj *) intros s [Q1s | Q2s].
    + destruct (IHderivable1 s Q1s) as (s' & P1s' & DS).
      exists s'. split. now left. assumption.
    + destruct (IHderivable2 s Q2s) as (s' & P2s' & DS).
      exists s'. split. now right. assumption.
  - (* DSeq *) intros s Rs.
    destruct (IHderivable2 s Rs) as (s2 & Qs2 & DS2).
    destruct (IHderivable1 s2 Qs2) as (s1 & Ps1 & DS1).
    exists s1. split. assumption. econstructor; eassumption.
  - (* DChoiceL *) intros s Qs. destruct (IHderivable s Qs) as (s' & Ps' & DS).
    exists s'. auto using EDChoiceL.
  - (* DChoiceR *) intros s Qs. destruct (IHderivable s Qs) as (s' & Ps' & DS).
    exists s'. auto using EDChoiceR.
  - (* DIterZero *) intros s Ps. exists s. split. assumption. constructor.
  - (* DIterNonzero *) intros s Qs. destruct (IHderivable s Qs) as (s' & Ps' & DS).
    exists s'. auto using star_equiv.
  - (* DBackwardVariant *)
    assert (Aux : forall n sig, P n sig ->
              exists sig', P O sig' /\ [[ c** ]] m |=> (sig', sig)). {
      induction n; intros sig Pnsig.
      - exists sig. split. assumption. constructor.
      - destruct (H0 n sig Pnsig) as (sig' & Pn'sig' & DS).
        destruct (IHn sig' Pn'sig') as (sig0 & P0 & DStar).
        exists sig0. split. assumption. econstructor; eassumption.
    }
    intros sig (n & Pnsig). destruct (Aux n sig Pnsig) as (sig' & P0 & DStar).
    exists sig'. auto.
  - (* DAssume *) intros sig (Psig & Bsig).
    exists sig. split. assumption. constructor. apply Bsig.
  - (* DAssign *) intros sig (x' & Psig & Eq).
    exists (mode_upd m sig x x'). split. assumption.
    destruct m; unfold mode_store, mode_upd in *; simpl in *.
      now apply step_assign_ok.
      now apply step_assign_ad.
  - (* DRand *) intros sig (x' & Psig).
    exists (mode_upd m sig x x'). split. assumption.
    destruct m; unfold mode_upd in *; simpl in *.
      apply step_rand_ok.
      apply step_rand_ad.
  - (* DRead *) intros sig (v & x' & l & Psig & Hl & Hx).
    exists (mode_chan_upd m (mode_upd m sig x x') s (v :: l)). split. assumption.
    destruct m; unfold mode_chan_upd, mode_upd, mode_chan, mode_store in *; simpl in *.
      now apply step_read_ok.
      now apply step_read_ad.
  - (* DWrite *) intros sig (l & Psig & Hl).
    exists (mode_chan_upd m sig s l). split. assumption.
    destruct m; unfold mode_chan_upd, mode_chan, mode_store in *; simpl in *.
      now apply step_write_ok.
      now apply step_write_ad.
  - (* DAdvAssertSuccess *) intros sig (Qsig & Bsig).
    exists sig. auto using EDAdvAssertSuccess.
  - (* DAdvAssertFailure *) intros sig (Qsig & nBsig).
    exists sig. auto using EDAdvAssertFailure.
Qed.
