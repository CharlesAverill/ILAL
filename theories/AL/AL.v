From Stdlib Require Export NArith String.
From ILAL Require Export AL.language state tactics.
From Stdlib Require Import List.
From Stdlib Require Import Lia PeanoNat.
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

Lemma mode_upd_shadow : forall m sig x v v',
  mode_upd m (mode_upd m sig x v) x v' = mode_upd m sig x v'.
Proof.
  intros m ((vs & vc) & (as_ & ac)) x v v'. destruct m; simpl;
    unfold update_victim, update_adversary; simpl;
    now rewrite update_shadow.
Qed.

Lemma mode_store_upd_eq : forall m sig x v,
  mode_store m (mode_upd m sig x v) x = v.
Proof.
  intros m ((vs & vc) & (as_ & ac)) x v. destruct m; simpl; now rewrite update_eq.
Qed.

Lemma mode_upd_store_eq : forall m sig x,
  mode_upd m sig x (mode_store m sig x) = sig.
Proof.
  intros m ((vs & vc) & (as_ & ac)) x. destruct m; simpl;
    unfold update_victim, update_adversary; simpl; f_equal; f_equal;
    now rewrite state_upd_eq.
Qed.

(** Single-thread semantics

    [ [[ c ]] m |=> (s, s') ] : running command [c] in mode [m] can take the
    single [estate] [s] to [s']. *)
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
(** C1 || C2: parallel composition for independent reduction *)
| EDParL c1 c2 m s1 s2 :
    [[ c1 ]] m |=> (s1, s2) ->
    [[ c1 <||> c2 ]] m |=> (s1, s2)
| EDParR c1 c2 m s1 s2 :
    [[ c2 ]] m |=> (s1, s2) ->
    [[ c1 <||> c2 ]] m |=> (s1, s2)
(** Com(c1, c2): move the head [v] of the sender's channel to the tail of the receiver's *)
| EDComVA c1 c2 m ch_id sig v l1 l2 :
    sig.(vstate).(ch) ch_id = v :: l1 ->
    sig.(astate).(ch) ch_id = l2 ->
    [[ Com(c1, c2) ]] m |=>
      (sig, sig[[ch_id :=vch l1]] [[ch_id :=ach (l2 ++ [v])%list]])
| EDComAV c1 c2 m ch_id sig v l1 l2 :
    sig.(astate).(ch) ch_id = v :: l1 ->
    sig.(vstate).(ch) ch_id = l2 ->
    [[ Com(c1, c2) ]] m |=>
      (sig, sig[[ch_id :=ach l1]] [[ch_id :=vch (l2 ++ [v])%list]])
| EDLocal x e c m sig sig' (x_out : N) :
    [[ c ]] m |=> (mode_upd m sig x (e (mode_store m sig)), sig') ->
    [[ local x = e in c ]] m |=>
      (sig, mode_upd m sig' x x_out)
where "[[ c ]] m |=> ( s , s' )" := (ds c m (s, s')).
Close Scope al_scope.

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

Section PredicateCombinators.

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

End PredicateCombinators.

Open Scope al_scope.

Section Tier1MetaTheorems.

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

End Tier1MetaTheorems.

(** Composed, independent triples *)

Definition aprop2 : Type := estate -> estate -> Prop.

Definition al_post2 (c1 c2 : astmt) (P A : aprop) : aprop2 :=
  fun sq sb =>
    exists sp sa, P sp /\ A sa /\
      ds c1 Ok (sp, sq) /\ ds c2 Ad (sa, sb).

(* The under-approximate adversarial triple [p][a] c1 || c2 [q][b] *)
Definition al_under2 (P A : aprop) (c1 c2 : astmt) (Q B : aprop) : Prop :=
  forall sq sb, Q sq /\ B sb ->
    al_post2 c1 c2 P A sq sb.

Notation "'<[[' P ']]' '[[' A ']]' c1 '||' c2 '[[' Q ']]' '[[' B ']]>'" :=
  (al_under2 P A c1 c2 Q B)
  (at level 0, c1 custom al_stmt at level 99, c2 custom al_stmt at level 99,
  format "<[[  P  ]] [[  A  ]]  c1  ||  c2  [[  Q  ]] [[  B  ]]>") : al_scope.

Lemma characterization :
  forall P Q A B C1 C2,
  <[[P]] [[A]] C1 || C2 [[Q]] [[B]]> <->
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

(** Single-threaded Hoare-style proof rules *)
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
(* Adversarial assertion *)
| DAdvAssertSuccess : forall Q B,
    Q, [adv_assert(B)] Ad, (aand_lift Ad Q B)
| DAdvAssertFailure : forall Q B,
    Q, [adv_assert(B)] Ad, (aand Q (anot (lift Ad B)))
(* Locals *)
| DLocal : forall P Q x (e : expression) m c,
    (fun sig => P (mode_upd m sig x (e (mode_store m sig)))
                /\ mode_store m sig x = e (mode_store m sig)),
      [c] m, Q ->
    P, [local x = e in c] m,
       (fun sig => exists (sb : estate) (x0 : N),
            Q sb /\ sig = mode_upd m sb x x0)
where "P , [ c ] m , Q" := (derivable P c m Q).

Lemma star_equiv : forall c m s1 s2,
  [[ c** ;; c ]] m |=> (s1, s2) ->
  [[ c** ]] m |=> (s1, s2).
Proof.
  intros c m s1 s2 H. invs H. econstructor; eassumption.
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

(* individual thread rule soundness *)
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
  - (* DLocal *) intros sig (sb & x0 & Qsb & Hsig).
    destruct (IHderivable sb Qsb) as (sp & (Psp & Hsp_x) & DSbody).
    assert (Hsp_entry : mode_upd m sp x (e (mode_store m sp)) = sp).
    { rewrite <- Hsp_x. now rewrite mode_upd_store_eq. }
    exists sp. split.
    + rewrite Hsp_entry in Psp. exact Psp.
    + subst sig.
      apply (EDLocal x e c m sp sb x0).
      rewrite Hsp_entry. exact DSbody.
Qed.

(** Composed semantics and proof system

    The adversarial judgment relates terms [c1] in mode [m1], [c2] in mode [m2],
    executing in parallel:
        [m1: P][m2: A]  c1 || c2  [m1: Q][m2: B].
    Membership of a composed transition [((sp,sa),(sq,sb))] has two cases:
    1. No interaction between threads
    2. Victim and adversary step together, sharing information over a channel

    [cds m1 m2 c1 c2 (sp,sa) (sq,sb)] : the composed system [c1||c2] takes one
    step from [(sp,sa)] to [(sq,sb)] *)

Inductive cds : mode -> mode -> astmt -> astmt ->
                (estate * estate) -> (estate * estate) -> Prop :=
(* case 1: independent reduction*)
| CInd : forall m1 m2 c1 c2 sp sa sq sb,
    ds c1 m1 (sp, sq) ->
    ds c2 m2 (sa, sb) ->
    cds m1 m2 c1 c2 (sp, sa) (sq, sb)
(* case 2 (Com): a value [v] moves from the head of the program-side channel
   [s] to the tail of the adversary-side channel [s] *)
| CComPA : forall m1 m2 c1 c2 (s : id) sp sa v l1 l2,
    sp.(vstate).(ch) s = v :: l1 ->
    sa.(astate).(ch) s = l2 ->
    cds m1 m2 c1 c2 (sp, sa)
        (sp[[ s :=vch l1 ]], sa[[ s :=ach (l2 ++ [v])%list ]])
(* vice versa *)
| CComAP : forall m1 m2 c1 c2 (s : id) sp sa v l1 l2,
    sa.(astate).(ch) s = v :: l1 ->
    sp.(vstate).(ch) s = l2 ->
    cds m1 m2 c1 c2 (sp, sa)
        (sp[[ s :=vch (l2 ++ [v])%list ]], sa[[ s :=ach l1 ]]).

(* Many steps of [cds], giving the PBV.

   [cds_star m1 m2 c1 c2 p q] : [q] is reachable from [p] by finitely many
   composed [cds] steps of [c1||c2]. *)
Inductive cds_star (m1 m2 : mode) (c1 c2 : astmt) :
  (estate * estate) -> (estate * estate) -> Prop :=
| CS0 : forall p, cds_star m1 m2 c1 c2 p p
| CSN : forall p q r,
    cds_star m1 m2 c1 c2 p q ->
    cds m1 m2 c1 c2 q r ->
    cds_star m1 m2 c1 c2 p r.

(** Generalization of [cds_star] to arbitrary [c1,c2] at each
    step, allowing for proof walkthroughs like we see in the paper *)
Inductive cds_star_hetero (m1 m2 : mode) :
  (estate * estate) -> (estate * estate) -> Prop :=
| CSH0 : forall p, cds_star_hetero m1 m2 p p
| CSHN : forall c1 c2 p q r,
    cds_star_hetero m1 m2 p q ->
    cds m1 m2 c1 c2 q r ->
    cds_star_hetero m1 m2 p r.

Definition al_postc_star (m1 m2 : mode) (c1 c2 : astmt) (PA : aprop2) : aprop2 :=
  fun sq sb =>
    exists sp sa, PA sp sa /\ cds_star m1 m2 c1 c2 (sp, sa) (sq, sb).

Definition al_underc_star (m1 m2 : mode) (PA : aprop2)
                          (c1 c2 : astmt) (QB : aprop2) : Prop :=
  forall sq sb, QB sq sb -> al_postc_star m1 m2 c1 c2 PA sq sb.

(** Composed proof system *)

Definition aprod (P A : aprop) : aprop2 := fun sp sa => P sp /\ A sa.

Definition al_postc_r (m1 m2 : mode) (c1 c2 : astmt) (PA : aprop2) : aprop2 :=
  fun sq sb =>
    exists sp sa, PA sp sa /\ cds m1 m2 c1 c2 (sp, sa) (sq, sb).

Definition al_underc_r (m1 m2 : mode) (PA : aprop2)
                       (c1 c2 : astmt) (QB : aprop2) : Prop :=
  forall sq sb, QB sq sb -> al_postc_r m1 m2 c1 c2 PA sq sb.

Definition aprop2_impl (P Q : aprop2) : Prop := forall sp sa, P sp sa -> Q sp sa.
Notation "P ==>> Q" := (aprop2_impl P Q) (at level 80).

Reserved Notation
  "'AL' m1 ',' m2 :: PA |- c1 '//' c2 ==> QB"
  (at level 90, c1 custom al_stmt at level 99, c2 custom al_stmt at level 99,
   m1 constr at level 0, m2 constr at level 0,
   PA constr at level 0, QB constr at level 0).

(** Composed hoare-style proof system *)
Inductive derivable2 :
  mode -> mode -> aprop2 -> astmt -> astmt -> aprop2 -> Prop :=
| D2Par : forall m1 m2 P A c1 c2 Q B,
    P, [c1] m1, Q ->
    A, [c2] m2, B ->
    AL m1 , m2 :: (aprod P A) |- c1 // c2 ==> (aprod Q B)
| D2Dup : forall P c Q,
    P, [c] Ok, Q ->
    AL Ok , Ok :: (aprod P P) |- c // c ==> (aprod Q Q)
| D2Consequence : forall m1 m2 PA PA' c1 c2 QB QB',
    PA ==>> PA' ->
    QB' ==>> QB ->
    AL m1 , m2 :: PA |- c1 // c2 ==> QB ->
    AL m1 , m2 :: PA' |- c1 // c2 ==> QB'
| D2Com : forall m1 m2 (PA : aprop2) c1 c2 (s : id),
    AL m1 , m2 :: PA |- c1 // c2 ==>
      (fun sq sb => exists v l1 l2,
         PA (sq[[ s :=vch v :: l1 ]]) (sb[[ s :=ach l2 ]])
         /\ sq.(vstate).(ch) s = l1
         /\ sb.(astate).(ch) s = (l2 ++ [v])%list)
| D2ComAP : forall m1 m2 (PA : aprop2) c1 c2 (s : id),
    AL m1 , m2 :: PA |- c1 // c2 ==>
      (fun sq sb => exists v l1 l2,
         PA (sq[[ s :=vch l2 ]]) (sb[[ s :=ach v :: l1 ]])
         /\ sb.(astate).(ch) s = l1
         /\ sq.(vstate).(ch) s = (l2 ++ [v])%list)
| D2AdvCons : forall m1 m2 PA c1 c2 (QB extra : aprop2),
    AL m1 , m2 :: PA |- c1 // c2 ==> QB ->
    AL m1 , m2 :: PA |- c1 // c2 ==> (fun sq sb => QB sq sb /\ extra sq sb)
| D2StepL : forall m1 m2 P c1 Q (K : aprop),
    P, [c1] m1, Q ->
    AL m1 , m2 :: (fun sp sa => P sp /\ K sa) |- c1 // skip
              ==> (fun sq sb => Q sq /\ K sb)
| D2StepR : forall m1 m2 (K : aprop) A c2 B,
    A, [c2] m2, B ->
    AL m1 , m2 :: (fun sp sa => K sp /\ A sa) |- skip // c2
              ==> (fun sq sb => K sq /\ B sb)
where "'AL' m1 ',' m2 :: PA |- c1 '//' c2 ==> QB" :=
  (derivable2 m1 m2 PA c1 c2 QB).

Lemma vch_shadow : forall sig s l l',
  sig[[ s :=vch l ]] [[ s :=vch l' ]] = sig[[ s :=vch l' ]].
Proof.
  intros ((vs & vc) & (as_ & ac)) s l l'. unfold update_vchannel. simpl.
  now rewrite update_shadow.
Qed.

Lemma ach_shadow : forall sig s l l',
  sig[[ s :=ach l ]] [[ s :=ach l' ]] = sig[[ s :=ach l' ]].
Proof.
  intros ((vs & vc) & (as_ & ac)) s l l'. unfold update_achannel. simpl.
  now rewrite update_shadow.
Qed.

Lemma vch_eq : forall sig s l,
  sig.(vstate).(ch) s = l -> sig[[ s :=vch l ]] = sig.
Proof.
  intros ((vs & vc) & (as_ & ac)) s l H. unfold update_vchannel. simpl in *.
  now rewrite (state_upd_eq _ vc s l H).
Qed.

Lemma ach_eq : forall sig s l,
  sig.(astate).(ch) s = l -> sig[[ s :=ach l ]] = sig.
Proof.
  intros ((vs & vc) & (as_ & ac)) s l H. unfold update_achannel. simpl in *.
  now rewrite (state_upd_eq _ ac s l H).
Qed.

Lemma vch_get : forall sig s l, (sig[[ s :=vch l ]]).(vstate).(ch) s = l.
Proof.
  intros ((vs & vc) & (as_ & ac)) s l. unfold update_vchannel. simpl. now rewrite update_eq.
Qed.
Lemma ach_get : forall sig s l, (sig[[ s :=ach l ]]).(astate).(ch) s = l.
Proof.
  intros ((vs & vc) & (as_ & ac)) s l. unfold update_achannel. simpl. now rewrite update_eq.
Qed.

Lemma vch_neq : forall sig j k l,
  j <> k -> (sig[[ j :=vch l ]]).(vstate).(ch) k = sig.(vstate).(ch) k.
Proof.
  intros ((vs & vc) & (as_ & ac)) j k l Hneq. unfold update_vchannel. simpl.
  now apply update_neq.
Qed.
Lemma ach_neq : forall sig j k l,
  j <> k -> (sig[[ j :=ach l ]]).(astate).(ch) k = sig.(astate).(ch) k.
Proof.
  intros ((vs & vc) & (as_ & ac)) j k l Hneq. unfold update_achannel. simpl.
  now apply update_neq.
Qed.

Lemma vch_vstore_upd : forall sig x v k,
  (sig[[ x :=v v ]]).(vstate).(ch) k = sig.(vstate).(ch) k.
Proof. intros. reflexivity. Qed.
Lemma ach_vstore_upd : forall sig x v k,
  (sig[[ x :=v v ]]).(astate).(ch) k = sig.(astate).(ch) k.
Proof. intros. reflexivity. Qed.
Lemma vch_astore_upd : forall sig x v k,
  (sig[[ x :=a v ]]).(vstate).(ch) k = sig.(vstate).(ch) k.
Proof. intros. reflexivity. Qed.
Lemma ach_astore_upd : forall sig x v k,
  (sig[[ x :=a v ]]).(astate).(ch) k = sig.(astate).(ch) k.
Proof. intros. reflexivity. Qed.
Lemma ach_vchan_upd : forall sig j l k,
  (sig[[ j :=vch l ]]).(astate).(ch) k = sig.(astate).(ch) k.
Proof. intros. reflexivity. Qed.
Lemma vch_achan_upd : forall sig j l k,
  (sig[[ j :=ach l ]]).(vstate).(ch) k = sig.(vstate).(ch) k.
Proof. intros. reflexivity. Qed.
(* store read is unaffected by channel updates on the same side *)
Lemma astore_achan_upd : forall sig j l k,
  (sig[[ j :=ach l ]]).(astate).(s) k = sig.(astate).(s) k.
Proof. intros. reflexivity. Qed.
Lemma vstore_vchan_upd : forall sig j l k,
  (sig[[ j :=vch l ]]).(vstate).(s) k = sig.(vstate).(s) k.
Proof. intros. reflexivity. Qed.

Lemma mode_chan_upd_Ok : forall sig k l, mode_chan_upd Ok sig k l = sig[[ k :=vch l ]].
Proof. reflexivity. Qed.
Lemma mode_chan_upd_Ad : forall sig k l, mode_chan_upd Ad sig k l = sig[[ k :=ach l ]].
Proof. reflexivity. Qed.
Lemma mode_upd_Ok : forall sig x v, mode_upd Ok sig x v = sig[[ x :=v v ]].
Proof. reflexivity. Qed.
Lemma mode_upd_Ad : forall sig x v, mode_upd Ad sig x v = sig[[ x :=a v ]].
Proof. reflexivity. Qed.
Lemma mode_chan_Ok : forall sig k, mode_chan Ok sig k = sig.(vstate).(ch) k.
Proof. reflexivity. Qed.
Lemma mode_chan_Ad : forall sig k, mode_chan Ad sig k = sig.(astate).(ch) k.
Proof. reflexivity. Qed.
Lemma mode_store_Ok : forall sig, mode_store Ok sig = sig.(vstate).(s).
Proof. reflexivity. Qed.
Lemma mode_store_Ad : forall sig, mode_store Ad sig = sig.(astate).(s).
Proof. reflexivity. Qed.
Lemma astore_aupd_eq : forall sig x v, (sig[[ x :=a v ]]).(astate).(s) x = v.
Proof. intros. apply update_eq. Qed.
Lemma vstore_vupd_eq : forall sig x v, (sig[[ x :=v v ]]).(vstate).(s) x = v.
Proof. intros. apply update_eq. Qed.

(* Raw-notation "different key"/"other record" store-read independence
   lemmas, completing the cross-product ({vstate,astate}.s reads against
   {[[:=v]],[[:=a]],[[:=vch]],[[:=ach]]} raw updates) that [vch_neq]/[ach_neq]
   and [vstore_vchan_upd]/[astore_achan_upd] leave uncovered.  Needed once a
   store read has to be traced back through a MIX of raw-notation updates
   (as produced by chaining [D2Com]/[D2ComAP] postconditions without a [set]
   to name each intermediate state) rather than the [mode_upd]/[mode_chan_upd]
   function forms the [astore_mode_upd_Ok]-family already covers. *)
Lemma vstore_vupd_neq : forall sig x y v,
  y <> x -> (sig[[ y :=v v ]]).(vstate).(s) x = sig.(vstate).(s) x.
Proof.
  intros ((vs & vc) & (as_ & ac)) x y v Hneq. unfold update_victim. simpl.
  now apply update_neq.
Qed.
Lemma astore_aupd_neq : forall sig x y v,
  y <> x -> (sig[[ y :=a v ]]).(astate).(s) x = sig.(astate).(s) x.
Proof.
  intros ((vs & vc) & (as_ & ac)) x y v Hneq. unfold update_adversary. simpl.
  now apply update_neq.
Qed.
Lemma vstore_aupd_upd : forall sig x y v,
  (sig[[ y :=a v ]]).(vstate).(s) x = sig.(vstate).(s) x.
Proof. intros. reflexivity. Qed.
Lemma astore_vupd_upd : forall sig x y v,
  (sig[[ y :=v v ]]).(astate).(s) x = sig.(astate).(s) x.
Proof. intros. reflexivity. Qed.
Lemma vstore_achan_upd : forall sig j l x,
  (sig[[ j :=ach l ]]).(vstate).(s) x = sig.(vstate).(s) x.
Proof. intros. reflexivity. Qed.
Lemma astore_vchan_upd : forall sig j l x,
  (sig[[ j :=vch l ]]).(astate).(s) x = sig.(astate).(s) x.
Proof. intros. reflexivity. Qed.

Lemma mode_chan_mode_upd : forall m sig x v k,
  mode_chan m (mode_upd m sig x v) k = mode_chan m sig k.
Proof. intros. destruct m; [apply vch_vstore_upd | apply ach_astore_upd]. Qed.

Lemma mode_store_mode_chan_upd : forall m sig k l x,
  mode_store m (mode_chan_upd m sig k l) x = mode_store m sig x.
Proof. intros. destruct m; [apply vstore_vchan_upd | apply astore_achan_upd]. Qed.

Lemma mode_store_mode_upd_neq : forall m sig y v x,
  y <> x -> mode_store m (mode_upd m sig y v) x = mode_store m sig x.
Proof. intros m sig y v x Hneq. destruct m; simpl; now apply update_neq. Qed.

Lemma mode_chan_get : forall m sig k l,
  mode_chan m (mode_chan_upd m sig k l) k = l.
Proof. intros. destruct m; [apply vch_get | apply ach_get]. Qed.

Lemma mode_chan_upd_shadow : forall m sig k l l',
  mode_chan_upd m (mode_chan_upd m sig k l) k l' = mode_chan_upd m sig k l'.
Proof. intros. destruct m; [apply vch_shadow | apply ach_shadow]. Qed.

Lemma mode_chan_upd_eq : forall m sig k,
  mode_chan_upd m sig k (mode_chan m sig k) = sig.
Proof. intros. destruct m; [apply vch_eq | apply ach_eq]; reflexivity. Qed.

(** Lemmas to concretize the application of DRS rules *)
Section ConcreteStepHelpers.

Lemma DAssign_concrete : forall m x (e : expression) X,
  (fun sig => sig = X), [x := e] m,
    (fun sig => sig = mode_upd m X x (e (mode_store m X))).
Proof.
  intros m x e X. eapply DConsequence with (P := fun sig => sig = X).
  3: apply DAssign.
  - intros sig ->. reflexivity.
  - intros sig ->.
    exists (mode_store m X x).
    rewrite mode_upd_shadow, mode_upd_store_eq.
    split. reflexivity.
    now rewrite mode_store_upd_eq.
Qed.

Lemma DRead_concrete : forall m (chn x : id) X v l,
  mode_chan m X chn = v :: l ->
  (fun sig => sig = X), [read(chn, x)] m,
    (fun sig => sig = mode_chan_upd m (mode_upd m X x v) chn l).
Proof.
  intros m chn x X v l Hchan. eapply DConsequence with (P := fun sig => sig = X).
  3: apply DRead.
  - intros sig ->. reflexivity.
  - intros sig ->.
    exists v, (mode_store m X x), l.
    assert (Hundo :
      mode_chan_upd m (mode_upd m (mode_chan_upd m (mode_upd m X x v) chn l)
                          x (mode_store m X x)) chn (v :: l) = X).
    { revert Hchan. destruct m; destruct X as [(vs & vc) (as_ & ac)]; intros Hchan;
        simpl in *;
        unfold update_vchannel, update_victim,
               update_achannel, update_adversary in *; simpl in *;
        f_equal; f_equal;
        first [ reflexivity
              | now rewrite update_shadow, state_upd_eq
              | now rewrite update_shadow, <- Hchan, state_upd_eq ]. }
    repeat split.
    + exact Hundo.
    + rewrite mode_chan_get. reflexivity.
    + rewrite mode_store_mode_chan_upd. now rewrite mode_store_upd_eq.
Qed.

Lemma DWrite_concrete : forall m (chn x : id) X,
  (fun sig => sig = X), [write(chn, x)] m,
    (fun sig => sig = mode_chan_upd m X chn
                  (mode_chan m X chn ++ [mode_store m X x])%list).
Proof.
  intros m chn x X. eapply DConsequence with (P := fun sig => sig = X).
  3: apply DWrite.
  - intros sig ->. reflexivity.
  - intros sig ->.
    exists (mode_chan m X chn). split.
    + rewrite mode_chan_upd_shadow. apply mode_chan_upd_eq.
    + rewrite mode_chan_get, mode_store_mode_chan_upd. reflexivity.
Qed.

Lemma DAssume_concrete : forall m (B : prop) X,
  B (mode_store m X) ->
  (fun sig => sig = X), [assume(B)] m, (fun sig => sig = X).
Proof.
  intros m B X HB. eapply DConsequence with (P := fun sig => sig = X).
  3: apply DAssume.
  - intros sig ->. reflexivity.
  - intros sig ->. split. reflexivity. exact HB.
Qed.

Lemma astore_mode_upd_Ok : forall sig y v x,
  mode_store Ad (mode_upd Ok sig y v) x = mode_store Ad sig x.
Proof. reflexivity. Qed.
Lemma astore_mode_chan_upd_Ok : forall sig k l x,
  mode_store Ad (mode_chan_upd Ok sig k l) x = mode_store Ad sig x.
Proof. reflexivity. Qed.
Lemma vstore_mode_upd_Ad : forall sig y v x,
  mode_store Ok (mode_upd Ad sig y v) x = mode_store Ok sig x.
Proof. reflexivity. Qed.
Lemma vstore_mode_chan_upd_Ad : forall sig k l x,
  mode_store Ok (mode_chan_upd Ad sig k l) x = mode_store Ok sig x.
Proof. reflexivity. Qed.

End ConcreteStepHelpers.

(** Soundness of the composed system with respect to the composed semantics [al_underc_r]. *)
Section Tier2Soundness.

Theorem soundness2 :
  forall m1 m2 PA c1 c2 QB,
    AL m1 , m2 :: PA |- c1 // c2 ==> QB ->
    al_underc_r m1 m2 PA c1 c2 QB.
Proof.
  intros m1 m2 PA c1 c2 QB H. induction H.
  - (* D2Par *)
    apply soundness in H. apply soundness in H0.
    intros sq sb (Qsq & Bsb).
    destruct (H sq Qsq) as (sp & Psp & DS1).
    destruct (H0 sb Bsb) as (sa & Asa & DS2).
    exists sp, sa. split. split; assumption. now apply CInd.
  - (* D2Dup *)
    apply soundness in H.
    intros sq sb (Qsq & Qsb).
    destruct (H sq Qsq) as (sp & Psp & DS1).
    destruct (H sb Qsb) as (sa & Psa & DS2).
    exists sp, sa. split. split; assumption. now apply CInd.
  - (* D2Consequence *)
    intros sq sb QB'sq. apply H0 in QB'sq.
    destruct (IHderivable2 sq sb QB'sq) as (sp & sa & PAsp & DS).
    exists sp, sa. split. now apply H. assumption.
  - (* D2Com *)
    intros sq sb (v & l1 & l2 & PApre & Hq & Hb).
    exists (sq[[ s :=vch v :: l1 ]]), (sb[[ s :=ach l2 ]]).
    split. assumption.
    replace sq with ((sq[[ s :=vch v :: l1 ]])[[ s :=vch l1 ]]) at 2
      by (rewrite vch_shadow; now apply vch_eq).
    replace sb with ((sb[[ s :=ach l2 ]])[[ s :=ach (l2 ++ [v])%list ]]) at 2
      by (rewrite ach_shadow; apply ach_eq; now rewrite Hb).
    apply CComPA.
    + now rewrite vch_get.
    + now rewrite ach_get.
  - (* D2ComAP *)
    intros sq sb (v & l1 & l2 & PApre & Hb & Hq).
    exists (sq[[ s :=vch l2 ]]), (sb[[ s :=ach v :: l1 ]]).
    split. assumption.
    replace sq with ((sq[[ s :=vch l2 ]])[[ s :=vch (l2 ++ [v])%list ]]) at 2
      by (rewrite vch_shadow; apply vch_eq; now rewrite Hq).
    replace sb with ((sb[[ s :=ach v :: l1 ]])[[ s :=ach l1 ]]) at 2
      by (rewrite ach_shadow; now apply ach_eq).
    apply CComAP.
    + now rewrite ach_get.
    + now rewrite vch_get.
  - (* D2AdvCons *)
    intros sq sb (QBsq & extrasq).
    destruct (IHderivable2 sq sb QBsq) as (sp & sa & PAsp & DS).
    exists sp, sa. split; assumption.
  - (* D2StepL *)
    apply soundness in H.
    intros sq sb (Qsq & Ksb).
    destruct (H sq Qsq) as (sp & Psp & DS1).
    exists sp, sb. split. split; assumption.
    apply CInd. exact DS1. apply EDSkip.
  - (* D2StepR *)
    apply soundness in H.
    intros sq sb (Ksq & Bsb).
    destruct (H sb Bsb) as (sa & Asa & DS2).
    exists sq, sa. split. split; assumption.
    apply CInd. apply EDSkip. exact DS2.
Qed.

Lemma derivable2_cds_step : forall m1 m2 c1 c2 X Y X' Y' QB,
  QB X' Y' ->
  AL m1 , m2 :: (fun sp sa => sp = X /\ sa = Y) |- c1 // c2 ==> QB ->
  cds m1 m2 c1 c2 (X, Y) (X', Y').
Proof.
  intros m1 m2 c1 c2 X Y X' Y' QB HQB Hderiv.
  apply soundness2 in Hderiv.
  destruct (Hderiv X' Y' HQB) as (sp & sa & (-> & ->) & Hcds).
  exact Hcds.
Qed.

End Tier2Soundness.

(** Adversarial Consequence *)

Section AdversarialConsequence.

Definition closed_aprop (Q : aprop) : Prop :=
  forall sig sig', Q sig <-> Q sig'.

(* The closed program fact [Q] holds and the adversary-side variable [v2] equals
   some witnessed [v1]. *)
Definition advcons_payload (Q : aprop) (v2 : id) : aprop2 :=
  fun _sq sb => exists v1, Q sb /\ mode_store Ad sb v2 = v1.

(* Derived Adversarial Consequence *)
Theorem D2AdvCons_payload :
  forall m1 m2 PA c1 c2 QB (Q : aprop) (v2 : id),
    closed_aprop Q ->
    AL m1 , m2 :: PA |- c1 // c2 ==> QB ->
    AL m1 , m2 :: PA |- c1 // c2 ==>
      (fun sq sb => QB sq sb /\ advcons_payload Q v2 sq sb).
Proof.
  intros m1 m2 PA c1 c2 QB Q v2 _Hclosed Hd.
  apply (D2AdvCons m1 m2 PA c1 c2 QB (advcons_payload Q v2)). exact Hd.
Qed.

End AdversarialConsequence.

(** Parallel Backward Variant *)
Section PBV.

Lemma cds_star_trans : forall m1 m2 c1 c2 p q r,
  cds_star m1 m2 c1 c2 p q ->
  cds_star m1 m2 c1 c2 q r ->
  cds_star m1 m2 c1 c2 p r.
Proof.
  intros m1 m2 c1 c2 p q r Hpq Hqr. induction Hqr.
  - assumption.
  - eapply CSN; [ apply IHHqr; assumption | assumption ].
Qed.

Lemma cds_cds_star : forall m1 m2 c1 c2 p q,
  cds m1 m2 c1 c2 p q -> cds_star m1 m2 c1 c2 p q.
Proof. intros. eapply CSN. apply CS0. assumption. Qed.

Lemma cds_star_hetero_trans : forall m1 m2 p q r,
  cds_star_hetero m1 m2 p q ->
  cds_star_hetero m1 m2 q r ->
  cds_star_hetero m1 m2 p r.
Proof.
  intros m1 m2 p q r Hpq Hqr. revert p Hpq. induction Hqr; intros p1 Hp1.
  - assumption.
  - eapply CSHN. apply IHHqr. exact Hp1. exact H.
Qed.

Lemma cds_cds_star_hetero : forall m1 m2 c1 c2 p q,
  cds m1 m2 c1 c2 p q -> cds_star_hetero m1 m2 p q.
Proof. intros m1 m2 c1 c2 p q H. eapply CSHN. apply CSH0. exact H. Qed.

Definition PBV_premise (m1 m2 : mode) (P A : nat -> aprop) (c1 c2 : astmt)
           (pred : nat -> nat -> (nat * nat)) : Prop :=
  forall n' m', (n' + m' > 0)%nat ->
    let (n, m) := pred n' m' in
    (n + m < n' + m')%nat /\
    al_underc_r m1 m2 (aprod (P n) (A m)) c1 c2 (aprod (P n') (A m')).

(* Every [(P n', A m')] post-pair is reachable by [cds_star] from a [(P 0, A 0)] pre-pair. *)
Lemma PBV_reach :
  forall m1 m2 (P A : nat -> aprop) c1 c2 pred,
    PBV_premise m1 m2 P A c1 c2 pred ->
    forall k n' m', (n' + m' <= k)%nat ->
      forall sq sb, P n' sq -> A m' sb ->
        exists sp sa, P 0%nat sp /\ A 0%nat sa /\
                      cds_star m1 m2 c1 c2 (sp, sa) (sq, sb).
Proof.
  intros m1 m2 P A c1 c2 pred Hprem k.
  induction k as [ | k IH ]; intros n' m' Hle sq sb HP HA.
  - assert (n' = 0 /\ m' = 0)%nat as [-> ->] by (split; lia).
    exists sq, sb. repeat split; try assumption. apply CS0.
  - (* k = S k *)
    destruct (Nat.eq_dec (n' + m')%nat 0) as [E0 | Epos].
    + assert (n' = 0 /\ m' = 0)%nat as [-> ->] by (split; lia).
      exists sq, sb. repeat split; try assumption. apply CS0.
    + assert (Hpos : (n' + m' > 0)%nat) by lia.
      specialize (Hprem n' m' Hpos).
      destruct (pred n' m') as (n, m).
      destruct Hprem as (Hlt & Htriple).
      destruct (Htriple sq sb (conj HP HA)) as (sp & sa & (Psp & Asa) & DS).
      assert (Hsmaller : (n + m <= k)%nat) by lia.
      destruct (IH n m Hsmaller sp sa Psp Asa)
        as (sp0 & sa0 & P0 & A0 & Star0).
      exists sp0, sa0. repeat split; try assumption.
      eapply cds_star_trans. apply Star0. now apply cds_cds_star.
Qed.

Theorem PBV_sound :
  forall m1 m2 (P A : nat -> aprop) c1 c2 pred,
    PBV_premise m1 m2 P A c1 c2 pred ->
    al_underc_star m1 m2 (aprod (P 0%nat) (A 0%nat)) c1 c2
      (fun sq sb => (exists n, P n sq) /\ (exists m, A m sb)).
Proof.
  intros m1 m2 P A c1 c2 pred Hprem sq sb ((n' & HP) & (m' & HA)).
  destruct (PBV_reach m1 m2 P A c1 c2 pred Hprem (n' + m')%nat n' m'
              (le_n _) sq sb HP HA)
    as (sp & sa & P0 & A0 & Star).
  exists sp, sa. split; [ split; assumption | assumption ].
Qed.

End PBV.

(** PBV over a multi-step round *)
Section PBVMultiStep.

Definition PBV_premise_star (m1 m2 : mode) (P A : nat -> aprop) (c1 c2 : astmt)
           (pred : nat -> nat -> (nat * nat)) : Prop :=
  forall n' m', (n' + m' > 0)%nat ->
    let (n, m) := pred n' m' in
    (n + m < n' + m')%nat /\
    al_underc_star m1 m2 (aprod (P n) (A m)) c1 c2 (aprod (P n') (A m')).

Lemma PBV_reach_star :
  forall m1 m2 (P A : nat -> aprop) c1 c2 pred,
    PBV_premise_star m1 m2 P A c1 c2 pred ->
    forall k n' m', (n' + m' <= k)%nat ->
      forall sq sb, P n' sq -> A m' sb ->
        exists sp sa, P 0%nat sp /\ A 0%nat sa /\
                      cds_star m1 m2 c1 c2 (sp, sa) (sq, sb).
Proof.
  intros m1 m2 P A c1 c2 pred Hprem k.
  induction k as [ | k IH ]; intros n' m' Hle sq sb HP HA.
  - assert (n' = 0 /\ m' = 0)%nat as [-> ->] by (split; lia).
    exists sq, sb. repeat split; try assumption. apply CS0.
  - destruct (Nat.eq_dec (n' + m')%nat 0) as [E0 | Epos].
    + assert (n' = 0 /\ m' = 0)%nat as [-> ->] by (split; lia).
      exists sq, sb. repeat split; try assumption. apply CS0.
    + assert (Hpos : (n' + m' > 0)%nat) by lia.
      specialize (Hprem n' m' Hpos).
      destruct (pred n' m') as (n, m).
      destruct Hprem as (Hlt & Htriple).
      destruct (Htriple sq sb (conj HP HA)) as (sp & sa & (Psp & Asa) & Star).
      assert (Hsmaller : (n + m <= k)%nat) by lia.
      destruct (IH n m Hsmaller sp sa Psp Asa)
        as (sp0 & sa0 & P0 & A0 & Star0).
      exists sp0, sa0. repeat split; try assumption.
      eapply cds_star_trans. apply Star0. exact Star.
Qed.

Theorem PBV_sound_star :
  forall m1 m2 (P A : nat -> aprop) c1 c2 pred,
    PBV_premise_star m1 m2 P A c1 c2 pred ->
    al_underc_star m1 m2 (aprod (P 0%nat) (A 0%nat)) c1 c2
      (fun sq sb => (exists n, P n sq) /\ (exists m, A m sb)).
Proof.
  intros m1 m2 P A c1 c2 pred Hprem sq sb ((n' & HP) & (m' & HA)).
  destruct (PBV_reach_star m1 m2 P A c1 c2 pred Hprem (n' + m')%nat n' m'
              (le_n _) sq sb HP HA)
    as (sp & sa & P0 & A0 & Star).
  exists sp, sa. split; [ split; assumption | assumption ].
Qed.

End PBVMultiStep.

(* Frame rule / constancy *)
Section Framing.

(* Variables a command may write to *)
Fixpoint Mod (c : astmt) : list id :=
  match c with
  | ASkip => nil
  | AAssign x _ => x :: nil
  | ARand x => x :: nil
  | ASeq c1 c2 => Mod c1 ++ Mod c2
  | APar c1 c2 => Mod c1 ++ Mod c2
  | AAssume _ => nil
  | AStar c => Mod c
  | AChoice c1 c2 => Mod c1 ++ Mod c2
  | ARead _ x => x :: nil
  | AWrite _ _ => nil
  | AAdvAssert _ => nil
  | ACom c1 c2 => nil
  | ALocal _ _ c => Mod c
  end.

(* Channels a command may write to *)
Fixpoint ModCh (c : astmt) : list id :=
  match c with
  | ASkip => nil
  | AAssign _ _ => nil
  | ARand _ => nil
  | ASeq c1 c2 => ModCh c1 ++ ModCh c2
  | APar c1 c2 => ModCh c1 ++ ModCh c2
  | AAssume _ => nil
  | AStar c => ModCh c
  | AChoice c1 c2 => ModCh c1 ++ ModCh c2
  | ARead s _ => s :: nil
  | AWrite s _ => s :: nil
  | AAdvAssert _ => nil
  | ACom c1 c2 => nil
  | ALocal _ _ c => ModCh c
  end.

(* [F] does not depend, in mode [m]'s store, on any variable in [V] or any channel in [C]. *)
Definition indep (m : mode) (V C : list id) (F : aprop) : Prop :=
  (forall sig x v, In x V -> (F (mode_upd m sig x v) <-> F sig))
  /\ (forall sig k l, In k C -> (F (mode_chan_upd m sig k l) <-> F sig)).

Lemma in_app_l : forall (x:id) l1 l2, In x l1 -> In x (l1 ++ l2).
Proof. intros. apply in_or_app. now left. Qed.
Lemma in_app_r : forall (x:id) l1 l2, In x l2 -> In x (l1 ++ l2).
Proof. intros. apply in_or_app. now right. Qed.

Lemma indep_sub : forall m V V' C C' F,
  (forall x, In x V -> In x V') ->
  (forall k, In k C -> In k C') ->
  indep m V' C' F -> indep m V C F.
Proof.
  intros m V V' C C' F HV HC [Hv Hc]. split; intros.
  - apply Hv. now apply HV.
  - apply Hc. now apply HC.
Qed.

(* NOTE : give a very simple explanation for this *)
Fixpoint ComFree (c : astmt) : Prop :=
  match c with
  | ASkip | AAssign _ _ | ARand _ | AAssume _ | ARead _ _ | AWrite _ _
  | AAdvAssert _ => True
  | ASeq c1 c2 | APar c1 c2 | AChoice c1 c2 => ComFree c1 /\ ComFree c2
  | AStar c => ComFree c
  | ALocal _ _ c => False
  | ACom _ _ => False
  end.

(* A [ds] step of a [Com]-free command changes only [Mod c] variables and
   [ModCh c] channels of the active store *)
Lemma frame_ds : forall c m sig sig',
  ds c m (sig, sig') ->
  ComFree c ->
  forall F, indep m (Mod c) (ModCh c) F -> (F sig <-> F sig').
Proof.
  intros c m sig sig' H.
  remember (sig, sig') as pr eqn:E.
  revert sig sig' E.
  induction H; intros sig0 sig0' E CF F Hindep;
    inversion E; subst; clear E; try tauto.
  - inversion Hindep; subst; clear Hindep.
    rewrite H. reflexivity. simpl. now left.
  - destruct Hindep as [Hv _]. simpl in Hv.
    specialize (Hv sig0 x (e (sig0.(astate).(s))) (or_introl eq_refl)).
    simpl in Hv. symmetry. exact Hv.
  - destruct Hindep as [Hv _]. simpl in Hv.
    specialize (Hv sig0 x v (or_introl eq_refl)). simpl in Hv. symmetry. exact Hv.
  - destruct Hindep as [Hv _]. simpl in Hv.
    specialize (Hv sig0 x v (or_introl eq_refl)). simpl in Hv. symmetry. exact Hv.
  - destruct CF as [CF1 CF2].
    assert (I1 : indep m (Mod c1) (ModCh c1) F).
    { apply (indep_sub m (Mod c1) (Mod c1 ++ Mod c2)
                         (ModCh c1) (ModCh c1 ++ ModCh c2));
        [ intros; now apply in_app_l | intros; now apply in_app_l | exact Hindep ]. }
    assert (I2 : indep m (Mod c2) (ModCh c2) F).
    { apply (indep_sub m (Mod c2) (Mod c1 ++ Mod c2)
                         (ModCh c2) (ModCh c1 ++ ModCh c2));
        [ intros; now apply in_app_r | intros; now apply in_app_r | exact Hindep ]. }
    rewrite (IHds1 _ _ eq_refl CF1 F I1).
    now apply (IHds2 _ _ eq_refl CF2 F I2).
  - destruct Hindep as [Hv Hc]. simpl in Hv, Hc.
    specialize (Hv sig0 x v (or_introl eq_refl)). simpl in Hv.
    specialize (Hc (sig0[[ x :=v v ]]) s l (or_introl eq_refl)). simpl in Hc.
    now rewrite Hc, Hv.
  - destruct Hindep as [Hv Hc]. simpl in Hv, Hc.
    rewrite Hc, Hv; intuition.
  - destruct Hindep as [_ Hc]. simpl in Hc.
    rewrite Hc; intuition.
  - destruct Hindep as [_ Hc]. simpl in Hc.
    rewrite Hc; intuition.
  - apply IHds; eauto.
      apply CF.
    eapply indep_sub; [| |eassumption];
      intros; now apply in_app_l.
  - apply IHds; eauto.
      apply CF.
    eapply indep_sub; [| |eassumption];
      intros; now apply in_app_r.
  - rewrite IHds1. apply IHds2. all: intuition.
  - destruct CF as [CF1 CF2].
    apply IHds; intuition.
    eapply indep_sub; [| |eassumption];
      intros; simpl; now apply in_app_l.
  - destruct CF as [CF1 CF2].
    apply IHds; intuition.
    eapply indep_sub; [| |eassumption];
      intros; simpl; now apply in_app_r.
  - destruct CF.
  - destruct CF.
  - destruct CF.
Qed.

Theorem constancy :
  forall P Q c m F,
    ComFree c ->
    indep m (Mod c) (ModCh c) F ->
    {{ P }} c [[m]] {{ Q }} ->
    {{ aand P F }} c [[m]] {{ aand Q F }}.
Proof.
  intros P Q c m F CF Hindep HU sig (Qsig & Fsig).
  destruct (HU sig Qsig) as (sig0 & Psig0 & DS).
  exists sig0. split.
  - split. assumption.
    apply (frame_ds c m sig0 sig DS CF F Hindep). exact Fsig.
  - assumption.
Qed.

End Framing.

(** Small-step interleaving semantics to represent paper examples

    [sstep m c sig c' sig'] : in mode [m], command [c] in state [sig] takes one
    step to [c'] and [sig']. *)

Section SmallStepSemantics.

Inductive sstep : mode -> astmt -> estate -> astmt -> estate -> Prop :=
| SAssign : forall m x e sig,
    sstep m (AAssign x e) sig ASkip (mode_upd m sig x (e (mode_store m sig)))
| SRand : forall m x v sig,
    sstep m (ARand x) sig ASkip (mode_upd m sig x v)
| SAssume : forall m (B : prop) sig,
    B (mode_store m sig) ->
    sstep m (AAssume B) sig ASkip sig
| SRead : forall m s x v l sig,
    mode_chan m sig s = v :: l ->
    sstep m (ARead s x) sig ASkip (mode_chan_upd m (mode_upd m sig x v) s l)
| SWrite : forall m s x sig,
    sstep m (AWrite s x) sig ASkip
          (mode_chan_upd m sig s (mode_chan m sig s ++ [mode_store m sig x])%list)
| SAdvAssertS : forall (P : prop) sig,
    P (sig.(astate).(s)) ->
    sstep Ad (AAdvAssert P) sig ASkip sig
| SAdvAssertF : forall (P : prop) sig,
    ~ P (sig.(astate).(s)) ->
    sstep Ad (AAdvAssert P) sig ASkip sig
| SSeqSkip : forall m c2 sig,
    sstep m (ASeq ASkip c2) sig c2 sig
| SSeqStep : forall m c1 c1' c2 sig sig',
    sstep m c1 sig c1' sig' ->
    sstep m (ASeq c1 c2) sig (ASeq c1' c2) sig'
| SChoiceL : forall m c1 c2 sig, sstep m (AChoice c1 c2) sig c1 sig
| SChoiceR : forall m c1 c2 sig, sstep m (AChoice c1 c2) sig c2 sig
| SStar0 : forall m c sig, sstep m (AStar c) sig ASkip sig
| SStarN : forall m c sig, sstep m (AStar c) sig (ASeq c (AStar c)) sig
| SLocalEnter : forall m x e c sig,
    sstep m (ALocal x e c) sig
          (ASeq (AAssign x e)
                (ASeq c (AAssign x (fun _ => mode_store m sig x)))) sig.

Inductive sstep_star (m : mode) : astmt -> estate -> astmt -> estate -> Prop :=
| SS0 : forall c sig, sstep_star m c sig c sig
| SSN : forall c sig c' sig' c'' sig'',
    sstep m c sig c' sig' ->
    sstep_star m c' sig' c'' sig'' ->
    sstep_star m c sig c'' sig''.

Lemma sstep_star_trans : forall m c1 s1 c2 s2 c3 s3,
  sstep_star m c1 s1 c2 s2 -> sstep_star m c2 s2 c3 s3 ->
  sstep_star m c1 s1 c3 s3.
Proof.
  intros m c1 s1 c2 s2 c3 s3 H1 H2. induction H1.
  - exact H2.
  - eapply SSN. exact H. apply IHsstep_star. exact H2.
Qed.

(** Small-step runs are valid big-step executions *)
Section Adequacy.

Lemma ds_star_left : forall c m a b d,
  ds c m (a, b) -> ds (AStar c) m (b, d) -> ds (AStar c) m (a, d).
Proof.
  intros c m a b d Hc Hstar.
  remember (AStar c) as sc eqn:E. remember (b, d) as bd eqn:Ebd.
  revert c a b d Hc E Ebd. induction Hstar; intros c0 a0 b0 d0 Hc E Ebd;
    try discriminate E.
  - injection E as ->. injection Ebd as -> ->.
    eapply EDStarN. apply EDStar0. exact Hc.
  - injection E as ->. injection Ebd as <- <-.
    eapply EDStarN.
    + eapply IHHstar1. exact Hc. reflexivity. reflexivity.
    + exact Hstar2.
Qed.

Lemma ds_local_desugar : forall m x e c sig sig'',
  ds (ASeq (AAssign x e)
           (ASeq c (AAssign x (fun _ => mode_store m sig x)))) m (sig, sig'') ->
  ds (ALocal x e c) m (sig, sig'').
Proof.
  intros m x e c sig sig'' H.
  inversion H; subst; clear H.
  inversion H6; subst; clear H6.
  destruct m; simpl in *.
  - inversion H4; subst; clear H4. inversion H7; subst; clear H7.
    eauto using EDLocal.
  - inversion H4; subst. inversion H7; subst.
    eauto using EDLocal.
Qed.

Lemma sstep_expansion : forall m c sig c' sig',
  sstep m c sig c' sig' ->
  forall sig'', ds c' m (sig', sig'') -> ds c m (sig, sig'').
Proof.
  intros m c sig c' sig' Hstep. induction Hstep; intros sig'' Hds.
  - (* SAssign *) inversion Hds; subst. destruct m; simpl;
      [ apply EDAssignV | apply EDAssignA ].
  - (* SRand *) inversion Hds; subst. destruct m; simpl;
      [ apply EDRandV | apply EDRandA ].
  - (* SAssume *) inversion Hds; subst. apply EDAssume. exact H.
  - (* SRead *) inversion Hds; subst. destruct m; simpl in *;
      [ apply EDReadV | apply EDReadA ]; exact H.
  - (* SWrite *) inversion Hds; subst. destruct m; simpl in *;
      [ apply EDWriteV | apply EDWriteA ].
  - (* SAdvAssertS *)
    inversion Hds; subst; clear Hds. eauto using EDAdvAssertSuccess.
  - (* SAdvAssertF *)
    inversion Hds; subst; clear Hds. eauto using EDAdvAssertFailure.
  - (* SSeqSkip *) eapply EDSeq. apply EDSkip. exact Hds.
  - (* SSeqStep *) inversion Hds; subst.
    eapply EDSeq; eauto.
  - (* SChoiceL *) apply EDChoiceL. exact Hds.
  - (* SChoiceR *) apply EDChoiceR. exact Hds.
  - (* SStar0 *) inversion Hds; subst. apply EDStar0.
  - (* SStarN *) inversion Hds; subst; eauto using ds_star_left.
  - (* SLocalEnter *) apply ds_local_desugar. exact Hds.
Qed.

Lemma sstep_star_ds : forall m c sig c' sig',
  sstep_star m c sig c' sig' ->
  forall sig'', ds c' m (sig', sig'') -> ds c m (sig, sig'').
Proof.
  intros m c sig c' sig' H. induction H; intros sig0' Hds.
  - exact Hds.
  - eapply sstep_expansion. exact H. apply IHsstep_star. exact Hds.
Qed.

Theorem sstep_star_sound : forall m c sig sig',
  sstep_star m c sig ASkip sig' -> ds c m (sig, sig').
Proof.
  intros m c sig sig' H. eapply sstep_star_ds. exact H. apply EDSkip.
Qed.

End Adequacy.

(** Composed interleaving semantics *)
Section ComposedInterleaving.

Inductive cstep :
  astmt -> astmt -> estate -> astmt -> astmt -> estate -> Prop :=
| CStepP : forall cp ca cp' sig sig',
    sstep Ok cp sig cp' sig' ->
    cstep cp ca sig cp' ca sig'
| CStepA : forall cp ca ca' sig sig',
    sstep Ad ca sig ca' sig' ->
    cstep cp ca sig cp ca' sig'
| CStepComPA : forall cp ca (s : id) sig v l1 l2,
    sig.(vstate).(ch) s = v :: l1 ->
    sig.(astate).(ch) s = l2 ->
    cstep cp ca sig cp ca
          (sig[[ s :=vch l1 ]] [[ s :=ach (l2 ++ [v])%list ]])
| CStepComAP : forall cp ca (s : id) sig v l1 l2,
    sig.(astate).(ch) s = v :: l1 ->
    sig.(vstate).(ch) s = l2 ->
    cstep cp ca sig cp ca
          (sig[[ s :=ach l1 ]] [[ s :=vch (l2 ++ [v])%list ]]).

Inductive cstep_star :
  astmt -> astmt -> estate -> astmt -> astmt -> estate -> Prop :=
| CST0 : forall cp ca sig, cstep_star cp ca sig cp ca sig
| CSTN : forall cp ca sig cp' ca' sig' cp'' ca'' sig'',
    cstep cp ca sig cp' ca' sig' ->
    cstep_star cp' ca' sig' cp'' ca'' sig'' ->
    cstep_star cp ca sig cp'' ca'' sig''.

Lemma cstep_star_trans : forall cp1 ca1 s1 cp2 ca2 s2 cp3 ca3 s3,
  cstep_star cp1 ca1 s1 cp2 ca2 s2 ->
  cstep_star cp2 ca2 s2 cp3 ca3 s3 ->
  cstep_star cp1 ca1 s1 cp3 ca3 s3.
Proof.
  intros. induction H.
  - assumption.
  - eapply CSTN. exact H. apply IHcstep_star. assumption.
Qed.

(* Lift a single-threaded small-step run into the composed relation *)
Lemma cstep_star_progL : forall cp ca sig cp' sig',
  sstep_star Ok cp sig cp' sig' ->
  cstep_star cp ca sig cp' ca sig'.
Proof.
  intros cp ca sig cp' sig' H. induction H.
  - apply CST0.
  - eapply CSTN. apply CStepP. exact H. exact IHsstep_star.
Qed.

Lemma cstep_star_progR : forall cp ca sig ca' sig',
  sstep_star Ad ca sig ca' sig' ->
  cstep_star cp ca sig cp ca' sig'.
Proof.
  intros cp ca sig ca' sig' H. induction H.
  - apply CST0.
  - eapply CSTN. apply CStepA. exact H. exact IHsstep_star.
Qed.

(** An attack is a terminating composed run that ends with both
    sides finished and the adversary's assertion satisfied. *)
Definition attack_reaches (cp ca : astmt) (sig0 : estate) (Post : aprop) : Prop :=
  exists sigf, cstep_star cp ca sig0 ASkip ASkip sigf /\ Post sigf.

(** [attack_reaches] for a full run of a multi-threaded system *)
Definition attack_reaches_AL (m1 m2 : mode) (sp0 sa0 : estate) (Post : aprop) : Prop :=
  exists sq sb, cds_star_hetero m1 m2 (sp0, sa0) (sq, sb) /\ Post sb.

End ComposedInterleaving.

Lemma sstep_star_under_seq : forall m c1 sig c1' sig' c2,
  sstep_star m c1 sig c1' sig' ->
  sstep_star m (ASeq c1 c2) sig (ASeq c1' c2) sig'.
Proof.
  intros m c1 sig c1' sig' c2 H. induction H.
  - apply SS0.
  - eapply SSN. apply SSeqStep. exact H. exact IHsstep_star.
Qed.

Lemma sstep_seq_run : forall m c1 sig sig' c2,
  sstep_star m c1 sig ASkip sig' ->
  sstep_star m (ASeq c1 c2) sig c2 sig'.
Proof.
  intros m c1 sig sig' c2 H.
  eapply sstep_star_trans.
  - apply (sstep_star_under_seq m c1 sig ASkip sig' c2). exact H.
  - eapply SSN. apply SSeqSkip. apply SS0.
Qed.

Lemma sstep_one : forall m c sig sig',
  sstep m c sig ASkip sig' -> sstep_star m c sig ASkip sig'.
Proof. intros. eapply SSN. exact H. apply SS0. Qed.

End SmallStepSemantics.
