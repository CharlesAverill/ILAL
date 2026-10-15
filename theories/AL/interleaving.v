(** * Interleaving semantics of [c1 || c2]: soundness and completeness

    A configuration pairs the residual commands with the state pair. A step
    runs one small step ([sstep]) of either side, or one [Com] transfer. The
    judgement [PA |- (c1, c2) ~> (d1, d2) QB] says every [QB] pair is reached
    from some [PA] pair by a run from residuals [(c1, c2)] to [(d1, d2)];
    a triple about [c1 || c2] is the case [d1 = d2 = skip]. *)
From ILAL Require Import AL.AL AL.language AL.completeness state tactics.
From Stdlib Require Import Relations.
Open Scope al_scope.

Definition config : Type := (astmt * astmt) * (estate * estate).

Inductive istep (m1 m2 : mode) : config -> config -> Prop :=
| IStepL : forall c1 c1' c2 sp sq sa,
    sstep m1 c1 sp c1' sq ->
    istep m1 m2 ((c1, c2), (sp, sa)) ((c1', c2), (sq, sa))
| IStepR : forall c1 c2 c2' sp sa sb,
    sstep m2 c2 sa c2' sb ->
    istep m1 m2 ((c1, c2), (sp, sa)) ((c1, c2'), (sp, sb))
(* A [cds] step of [skip || skip]: a [Com] transfer, or a stutter *)
| IStepCom : forall c1 c2 p q,
    cds m1 m2 ASkip ASkip p q ->
    istep m1 m2 ((c1, c2), p) ((c1, c2), q).

Definition istep_star (m1 m2 : mode) := clos_refl_trans config (istep m1 m2).

Definition ipost (m1 m2 : mode) (c1 c2 d1 d2 : astmt) (PA : aprop2) : aprop2 :=
  fun sq sb => exists sp sa, PA sp sa /\
    istep_star m1 m2 ((c1, c2), (sp, sa)) ((d1, d2), (sq, sb)).

Definition iunder (m1 m2 : mode) (PA : aprop2) (c1 c2 d1 d2 : astmt)
                  (QB : aprop2) : Prop :=
  forall sq sb, QB sq sb -> ipost m1 m2 c1 c2 d1 d2 PA sq sb.

(** ** Single-thread small-step rules *)

(* Commands that finish in one [sstep]; their rules come from tier 1 *)
Definition atomic (c : astmt) : Prop :=
  match c with
  | AAssign _ _ | ARand _ | AAssume _ | ARead _ _ | AWrite _ _ | AAdvAssert _ => True
  | _ => False
  end.

(* [sderiv m P c c' Q]: every [Q] state is one [sstep] from [c] to [c'] away
   from a [P] state *)
Inductive sderiv (m : mode) : aprop -> astmt -> astmt -> aprop -> Prop :=
| SDAtom : forall P a Q, atomic a -> P, [a] m, Q -> sderiv m P a ASkip Q
| SDSeqSkip : forall P c, sderiv m P (ASeq ASkip c) c P
| SDSeqStep : forall P Q c1 c1' c2,
    sderiv m P c1 c1' Q -> sderiv m P (ASeq c1 c2) (ASeq c1' c2) Q
| SDChoiceL : forall P c1 c2, sderiv m P (AChoice c1 c2) c1 P
| SDChoiceR : forall P c1 c2, sderiv m P (AChoice c1 c2) c2 P
| SDParL : forall P c1 c2, sderiv m P (APar c1 c2) c1 P
| SDParR : forall P c1 c2, sderiv m P (APar c1 c2) c2 P
| SDStar0 : forall P c, sderiv m P (AStar c) ASkip P
| SDStarN : forall P c, sderiv m P (AStar c) (ASeq c (AStar c)) P
(* [SLocalEnter] restores [x] to its entry value [v] *)
| SDLocal : forall P x e c (v : N),
    (forall sig, P sig -> mode_store m sig x = v) ->
    sderiv m P (ALocal x e c) (ASeq (AAssign x e) (ASeq c (AAssign x (fun _ => v)))) P.

(** ** Interleaved proof system *)

Inductive iderivable (m1 m2 : mode) :
  aprop2 -> astmt -> astmt -> astmt -> astmt -> aprop2 -> Prop :=
| IRefl : forall PA c1 c2, iderivable m1 m2 PA c1 c2 c1 c2 PA
| ITrans : forall PA QB RB c1 c2 d1 d2 e1 e2,
    iderivable m1 m2 PA c1 c2 d1 d2 QB ->
    iderivable m1 m2 QB d1 d2 e1 e2 RB ->
    iderivable m1 m2 PA c1 c2 e1 e2 RB
| IConsequence : forall PA PA' QB QB' c1 c2 d1 d2,
    PA ==>> PA' -> QB' ==>> QB ->
    iderivable m1 m2 PA c1 c2 d1 d2 QB ->
    iderivable m1 m2 PA' c1 c2 d1 d2 QB'
| IDisjI : forall (I : Type) (PA QB : I -> aprop2) c1 c2 d1 d2,
    (forall i, iderivable m1 m2 (PA i) c1 c2 d1 d2 (QB i)) ->
    iderivable m1 m2 (fun sp sa => exists i, PA i sp sa) c1 c2 d1 d2
                     (fun sq sb => exists i, QB i sq sb)
| IStepLeft : forall P Q (K : aprop) c1 c1' c2,
    sderiv m1 P c1 c1' Q ->
    iderivable m1 m2 (aprod P K) c1 c2 c1' c2 (aprod Q K)
| IStepRight : forall (K : aprop) A B c1 c2 c2',
    sderiv m2 A c2 c2' B ->
    iderivable m1 m2 (aprod K A) c1 c2 c1 c2' (aprod K B)
(* [Com] reuses the one-step system on [skip || skip] ([D2Com], [D2ComAP]) *)
| ICom : forall PA QB c1 c2,
    AL m1 , m2 :: PA |- skip // skip ==> QB ->
    iderivable m1 m2 PA c1 c2 c1 c2 QB.

(** ** Soundness *)

Lemma atomic_sstep : forall a m sig sig',
  atomic a -> ds a m (sig, sig') -> sstep m a sig ASkip sig'.
Proof.
  intros a m sig sig' Ha H.
  destruct a; try contradiction; inversion H; subst.
  all: first [ exact (SAssign Ok _ _ _) | exact (SAssign Ad _ _ _)
             | exact (SRand Ok _ _ _) | exact (SRand Ad _ _ _)
             | exact (SWrite Ok _ _ _) | exact (SWrite Ad _ _ _)
             | now apply SAssume | now apply SAdvAssertS | now apply SAdvAssertF
             | now apply (SRead Ok) | now apply (SRead Ad) ].
Qed.

Lemma sderiv_sound : forall m P c c' Q,
  sderiv m P c c' Q -> forall sq, Q sq -> exists sp, P sp /\ sstep m c sp c' sq.
Proof.
  intros m P c c' Q H. induction H; intros sq Hq;
    try (exists sq; split; [ exact Hq | constructor ]).
  - destruct (soundness _ _ _ _ H0 sq Hq) as (sp & Hp & Hds).
    exists sp. split. exact Hp. now apply atomic_sstep.
  - destruct (IHsderiv sq Hq) as (sp & Hp & Hs).
    exists sp. split. exact Hp. now constructor.
  - exists sq. split. exact Hq. rewrite <- (H sq Hq). constructor.
Qed.

Theorem isoundness : forall m1 m2 PA c1 c2 d1 d2 QB,
  iderivable m1 m2 PA c1 c2 d1 d2 QB -> iunder m1 m2 PA c1 c2 d1 d2 QB.
Proof.
  intros m1 m2 PA c1 c2 d1 d2 QB H. induction H; intros sq sb HQ.
  - exists sq, sb. split. exact HQ. apply rt_refl.
  - destruct (IHiderivable2 sq sb HQ) as (sp & sa & HQ' & S2).
    destruct (IHiderivable1 sp sa HQ') as (s0 & a0 & HP & S1).
    exists s0, a0. split. exact HP. eapply rt_trans; eassumption.
  - destruct (IHiderivable sq sb (H0 sq sb HQ)) as (sp & sa & HP & Hs).
    exists sp, sa. split. now apply H. exact Hs.
  - destruct HQ as (i & HQ). destruct (H0 i sq sb HQ) as (sp & sa & HP & Hs).
    exists sp, sa. split. now exists i. exact Hs.
  - destruct HQ as (Hq & Hk). destruct (sderiv_sound _ _ _ _ _ H sq Hq) as (sp & Hp & Hs).
    exists sp, sb. split. now split. apply rt_step. now constructor.
  - destruct HQ as (Hk & Hb). destruct (sderiv_sound _ _ _ _ _ H sb Hb) as (sa & Ha & Hs).
    exists sq, sa. split. now split. apply rt_step. now constructor.
  - destruct (soundness2 _ _ _ _ _ _ H sq sb HQ) as (sp & sa & HP & Hc).
    exists sp, sa. split. exact HP. apply rt_step. now constructor.
Qed.

(** ** Completeness *)

Definition sing (X : estate) : aprop := fun sig => sig = X.

(* Atomic steps reuse tier-1 [completeness] *)
Lemma sderiv_atom : forall m c sig sig',
  atomic c -> sstep m c sig ASkip sig' -> sderiv m (sing sig) c ASkip (sing sig').
Proof.
  intros m c sig sig' Ha H. apply SDAtom. exact Ha.
  apply completeness. intros ? ->. exists sig.
  split. reflexivity. now apply sstep_star_sound, sstep_one.
Qed.

Lemma sstep_sderiv : forall m c sig c' sig',
  sstep m c sig c' sig' -> sderiv m (sing sig) c c' (sing sig').
Proof.
  intros m c sig c' sig' H. induction H;
    try (apply sderiv_atom; [ exact I | now constructor ]);
    try (constructor; reflexivity).
  - (* SSeqStep *) now constructor.
  - (* SLocalEnter *) apply SDLocal. now intros ? ->.
Qed.

(* A one-step run is derivable between singletons *)
Lemma istep_iderivable : forall m1 m2 x y,
  istep m1 m2 x y ->
  iderivable m1 m2 (sing2p (snd x)) (fst (fst x)) (snd (fst x))
                   (fst (fst y)) (snd (fst y)) (sing2p (snd y)).
Proof.
  intros m1 m2 x y H. destruct H; simpl.
  - (* IStepL *)
    eapply IConsequence with (PA := aprod (sing sp) (sing sa)) (QB := aprod (sing sq) (sing sa)).
    + intros p a [-> ->]. reflexivity.
    + intros p a E. injection E as -> ->. now split.
    + apply IStepLeft. now apply sstep_sderiv.
  - (* IStepR *)
    eapply IConsequence with (PA := aprod (sing sp) (sing sa)) (QB := aprod (sing sp) (sing sb)).
    + intros p a [-> ->]. reflexivity.
    + intros p a E. injection E as -> ->. now split.
    + apply IStepRight. now apply sstep_sderiv.
  - (* IStepCom *)
    apply ICom, completeness2. intros sq sb E. exists (fst p), (snd p).
    rewrite E. now destruct p.
Qed.

Lemma istep_star_iderivable : forall m1 m2 x y,
  istep_star m1 m2 x y ->
  iderivable m1 m2 (sing2p (snd x)) (fst (fst x)) (snd (fst x))
                   (fst (fst y)) (snd (fst y)) (sing2p (snd y)).
Proof.
  intros m1 m2 x y H. induction H.
  - now apply istep_iderivable.
  - apply IRefl.
  - eapply ITrans; eassumption.
Qed.

Theorem icompleteness : forall m1 m2 PA c1 c2 d1 d2 QB,
  iunder m1 m2 PA c1 c2 d1 d2 QB -> iderivable m1 m2 PA c1 c2 d1 d2 QB.
Proof.
  intros m1 m2 PA c1 c2 d1 d2 QB H.
  (* One index per run from a [PA] pair *)
  set (I := { r : (estate * estate) * (estate * estate) |
              PA (fst (fst r)) (snd (fst r))
              /\ istep_star m1 m2 ((c1, c2), fst r) ((d1, d2), snd r) }).
  eapply IConsequence with
    (PA := fun sp sa => exists i : I, sing2p (fst (proj1_sig i)) sp sa)
    (QB := fun sq sb => exists i : I, sing2p (snd (proj1_sig i)) sq sb).
  - intros sp sa [ [r Hr] E ]. simpl in E. rewrite <- E in Hr. apply Hr.
  - intros sq sb HQ. destruct (H sq sb HQ) as (sp & sa & HP & Hs).
    now exists (exist _ ((sp, sa), (sq, sb)) (conj HP Hs)).
  - apply IDisjI. intros [r Hr]. exact (istep_star_iderivable _ _ _ _ (proj2 Hr)).
Qed.

(** A triple about [c1 || c2]: every [QB] pair ends a terminating run *)
Theorem iequivalence : forall m1 m2 PA c1 c2 QB,
  iderivable m1 m2 PA c1 c2 ASkip ASkip QB <-> iunder m1 m2 PA c1 c2 ASkip ASkip QB.
Proof.
  intros. split. apply isoundness. apply icompleteness.
Qed.
