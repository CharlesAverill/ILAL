From ILAL Require Import language tactics.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import NArith.

Require Import Stdlib.Program.Equality.


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
| ESeqOk C1 C2 ex s1 s3 :
    (exists s2,
      [ C1 ] ok |=> (s1, s2) /\
      [ C2 ] ex |=> (s2, s3)) ->
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
  destruct H3 as (s1' & CStar & C).
  econstructor; eassumption.
Qed.

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
| BackwardsVariant (P : nat -> prop) C :
    (forall n, P n, [C] ok, P (S n)) ->
    P O, [C**] ok, (fun s => exists n', P n' s)
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

Fixpoint nRepeat (s : stmt) (n : nat) :=
match n with
| O => Skip
| S n' => <{ (nRepeat s n') ;; s }>
end.

Lemma repeat_is_star (C : stmt) : forall P ex s, ds_post (denote <{ C** }> ex) P s -> (exists n, ds_post (denote (nRepeat C n) ex) P s). 
Proof.
  intros P ex s H.
  unfold ds_post in H.
  destruct H.
  unfold denote in H.
  destruct H.


  assert (Hexec : exists n, [nRepeat C n] ex |=> (x, s)).
  {
    dependent induction H0.
    - (* EStar0: 0 iterations *)
      exists 0%nat. simpl. constructor.
    - assert (eq_cstar :  <{ C ** }> = <{ C ** }>). { reflexivity. }
    assert (eq_s:  (x, s2) = (x, s2)). { reflexivity. }
    specialize (IHds1 C s2 x H eq_cstar eq_s). invs IHds1.
    exists (S x0).
    simpl. apply ESeqOk. exists s2.
    split ; assumption.      
    - (* EStarEr: error happens (possibly after 0 ok-iterations; this constructor is “immediate”) *)
      exists 1%nat. simpl.
      (* nRepeat C 1 = Skip ;; C *)
      apply ESeqOk.
      exists x. split.
      + constructor.  (* ESkipOk *)
      + assumption.
  }

  destruct Hexec as [n Hn].
  exists n.
  unfold ds_post.
  exists x. split. exact H.
  unfold denote. exact Hn.
Qed.

Theorem soundness :
  forall C P Q ex,
    P, [C] ex, Q ->
    {{P}} denote C ex {{Q}}.
Proof.
  intros. induction H;
    try solve [
      (intros s Qs; contradiction)
    ];
    try rename IHderivable1 into IH1;
    try rename IHderivable2 into IH2;
    try rename IHderivable into IH.
  - now apply (impl_symmetry P P' Q Q').
  - intros s Qs. destruct Qs.
    -- (* Q1 s *)
       destruct (IH1 _ H1) as (s' & P1s' & DS).
       exists s'. split. now left. assumption.
    -- (* Q2 s *)
       destruct (IH2 _ H1) as (s' & P2s' & DS).
       exists s'. split. now right. assumption.
  - intros s Qs. exists s. split. assumption. constructor.
  - intros s Rs. destruct (IH _ Rs) as (s' & Ps' & DS).
    exists s'. split. assumption. now constructor.
  - intros s Rs. destruct (IH2 _ Rs) as (s' & Qs' & DS).
    destruct (IH1 _ Qs') as (s'' & Ps'' & DS').
    exists s''. split. assumption. constructor.
    exists s'. split. assumption. assumption.
  - intros s Ps. exists s. split. assumption. constructor.
  - intros s Ps. destruct (IH _ Ps) as (s' & Qs' & DS). invs DS.
    exists s'. split. assumption. assumption.
    destruct H3 as (s'' & DS1 & DS2). exists s'. split. assumption.
    econstructor; eassumption.
  - admit.
  - intros s Qs. destruct (IH _ Qs) as (s' & Ps' & DS). exists s'.
    split. assumption. now constructor.
  - intros s Qs. destruct (IH _ Qs) as (s' & Ps' & DS). exists s'.
    split. assumption. now constructor.
  - intros s Qs. exists s. split. assumption. constructor.
  - intros s (Ps & Bs). exists s. split. assumption. now constructor.
  - intros s (x' & Ps & Eq). eexists. split. eassumption.
    unfold denote. admit. (* Wrong direction? *)
  - intros s (x' & Ps). eexists. split. eassumption.
    unfold denote. admit. (* Wrong direction again *)
Abort.

Theorem completeness :
  forall C P Q ex,
    {{P}} denote C ex {{Q}} ->
    P, [C] ex, Q.
    Proof. 
    induction C ; intros P Q ex DS.
    - destruct ex.
      -- eapply Consequence with (Q := (fun s => False)).
        --- apply UnitEr.
        --- intros s Hp. exact Hp.
        --- intros s HQ. destruct (DS s HQ). inversion H. inversion H1.
      -- eapply Consequence with (Q := P).
        --- apply UnitOk.
        --- intros s Hp. exact Hp.
        --- intros s Hq. destruct (DS s Hq) as (s1 & HP & Hstep). invs Hstep. exact HP.
   - destruct ex.
    -- eapply Consequence with (Q := (fun s => False)).
      --- apply AssignmentEr.
      --- intros s Hp. exact Hp. 
      --- intros s Hq. destruct (DS s Hq). invs H. inversion H1.
    -- eapply Consequence with (Q := (fun s => exists i', P (s[i := i']) /\
                              s i = exp (s[i := i']))).
      --- apply AssignmentOk.
      --- intros s Hp. exact Hp.
      --- intros s Hq. destruct (DS s Hq). invs H. invs H1. admit. (** confused about definition for AssignmentOK **)
  - destruct ex.
  -- eapply Consequence with (Q := (fun s => False)).
  --- apply NondetAssignmentEr.
  --- intros s Hp. exact Hp.
  --- intros s Hq. destruct (DS s Hq). destruct H. invs H0.
  -- eapply Consequence with (Q := (fun s => exists x', P (s[i := x']))).
  --- apply NondetAssignmentOk.
  --- intros s Hp. exact Hp.
  --- intros s Hq. destruct (DS s Hq). destruct H. invs H0. admit. 
  - destruct ex.
  -- set (Mid := fun s2 => exists s1, P s1 /\ [C1] ok |=> (s1, s2)).
  set (Qsc := fun s3 => Q s3 /\ exists s1, P s1 /\ [C1] er |=> (s1, s3)).
  set (Qnm := fun s3 => Q s3 /\ exists s2, Mid s2 /\ [C2] er |=> (s2, s3)).
  
  assert (DS_C1_er : {{P}} denote C1 er {{Qsc}}).
  {
    intros s3 HQsc.
    destruct HQsc. destruct H0. destruct H0. 
    exists x. split; assumption.
  } 
  
  pose proof (IHC1 P Qsc er DS_C1_er) as D_C1_er.
  pose proof (SeqShortCircuit P Qsc C1 C2 D_C1_er) as D_sc.

  assert (DS_C1_ok : {{P}} denote C1 ok {{Mid}}).
  {
    intros s2 Hmid.
    destruct Hmid. destruct H.
    exists x. split; assumption. 
  }  
   
  pose proof (IHC1 P Mid ok DS_C1_ok) as D_C1_ok.
  
  assert (DS_C2_er : {{Mid}} denote C2 er {{Qnm}}).
  {
    intros s3 HQnm.
    destruct HQnm. destruct H0. destruct H0.
    exists x. split; assumption.
  }
  
  pose proof (IHC2 Mid Qnm er DS_C2_er) as D_C2_er.
  
  pose proof (SeqNormal P Mid Qnm C1 C2 er D_C1_ok D_C2_er) as D_nm.
  
  pose proof (Disjunction P Qsc P Qnm <{ C1;; C2 }> er D_sc D_nm) as D_or.
  
  eapply Consequence with
  (P  := fun s => P s \/ P s)
  (Q  := fun s => Qsc s \/ Qnm s).
  
  --- exact D_or.
  --- intros s [Hp|Hp]; assumption.
  --- intros s3 HQ.   destruct (DS s3 HQ) as (s1 & HP & Hseq). inversion Hseq; subst.
  ---- left. split ; [exact HQ|]. exists s1. split; [exact HP | assumption]. 
  ---- right. split; [exact HQ|]. destruct H2 as (s2 & Hc1ok & Hc2er). exists s2. split.  exists s1. split; assumption. exact Hc2er.
  
  -- set (Mid := fun s2 => exists s1, P s1 /\ [C1] ok |=> (s1, s2)).
    set (Qnm := fun s3 => Q s3 /\ exists s2, Mid s2 /\ [C2] ok |=> (s2, s3)).
  
   assert (DS_C1_ok : {{P}} denote C1 ok {{Mid}}).
  {
    intros s2 Hmid.
    destruct Hmid. destruct H.
    exists x. split; assumption. 
  }  
  
  assert (DS_C2_ok : {{Mid}} denote C2 ok {{Qnm}}).
  {
  intros s2 Hmid. 
  destruct Hmid. destruct H0. destruct H0.
  exists x. split. assumption.
  auto.
  }
  
  specialize (IHC1 P Mid ok DS_C1_ok).
  specialize (IHC2 Mid Qnm ok DS_C2_ok).
  pose proof (SeqNormal P Mid Qnm C1 C2 ok IHC1 IHC2) as D_nm.
  eapply Consequence with (Q := fun s => Qnm s).
  --- exact D_nm. 
  --- intro. trivial.
  --- intros s3 HQ. destruct (DS s3 HQ). destruct H. unfold Qnm. split. auto. unfold Mid. invs H0. destruct H4. exists x0. split.
  ---- destruct H0. exists x. split; assumption.
  ---- destruct H0. assumption.
  - set (Mid1 := fun s2 => exists s1, P s1 /\ [C1] ex |=> (s1, s2)).
  set (Mid2 := fun s2 => exists s1, P s1 /\ [C2] ex |=> (s1, s2)).
  set (Or := fun s2 => Mid1 s2 \/ Mid2 s2).
  
  eapply Consequence with (Q := Or).
  -- assert (DS_C1 : {{P}} denote <{ C1 }> ex {{Mid1}}). {
    intros s H. destruct H. destruct H. unfold ds_post. exists x. split.
    - assumption.
    - unfold denote. exact H0.
  }
  assert (DS_C2 : {{P}} denote <{ C2 }> ex {{Mid2}}). {
    intros s H. destruct H. destruct H. unfold ds_post. exists x. split.
    - assumption.
    - unfold denote. exact H0.
  }
  
  specialize (IHC1 P Mid1 ex DS_C1).
  specialize (IHC2 P Mid2 ex DS_C2).
  assert (A1 : P, [C1 <+> C2] ex, Mid1). {
    apply ChoiceLeft. assumption.
  }
  assert (A2 : P, [C1 <+> C2] ex, Mid2). {
    apply ChoiceRight. assumption.
  }
  apply Disjunction.
  --- exact A1.
  --- exact A2.
  -- intros s Hp. destruct Hp; assumption.
  -- intros s Hq. destruct (DS s Hq). destruct H. invs H0; unfold Or.
  --- left. unfold Mid1. exists x. split; assumption.
  --- right. unfold Mid2. exists x. split; assumption.
  - set (p := fun n => ((ds_post (denote (nRepeat C n) ex) P))). 
  eapply Consequence with (Q := fun s => exists n, (p n) s). 
  -- destruct ex. 
  --- admit.
  --- eapply BackwardsVariant with (P := p).
  intro n.
  assert (DS_C : {{p n}} denote C ok {{p (S n)}}).
  {
  intros x Hp.
  invs Hp. destruct H. invs H0. invs H4. destruct H0. destruct n.
  - simpl in H0. invs H0. unfold p. simpl. unfold ds_post. exists x1. split. 
  -- exists x1. split. assumption. simpl. constructor.
  -- unfold denote. assumption.
  - simpl in H0. unfold p. simpl. unfold ds_post. exists x1. split.
  -- exists x0. split. assumption. simpl. exact H0.
  -- simpl. exact H1.
  } 
  
  specialize (IHC (p n) (p (S n)) ok DS_C).
  assumption.
  -- intros s H. destruct H. destruct H. invs H0. assumption.
  -- intros s H.
  unfold under_approximate in DS. specialize (DS s H). invs DS. invs H0.
  unfold p. apply repeat_is_star. unfold ds_post. exists x ; auto.
 
  - destruct ex.
  -- eapply Consequence with (Q := P).
  --- apply ErrorEr.
  --- intros s Hp. exact Hp.
  ---  intros s Hq. destruct (DS s Hq). destruct H. invs H0. exact H.
  -- eapply Consequence with (Q := (fun s => False)). 
  --- apply ErrorOk.
  --- intros s Hp. exact Hp.
  --- intros s Hq. destruct (DS s Hq). destruct H. inversion H0.
  - destruct ex.
  -- eapply Consequence with (Q := (fun s => False)).
  --- apply AssumeEr.
  --- intros s Hp. exact Hp.
  --- intros s Hq. destruct (DS s Hq). destruct H. inversion H0.
  -- eapply Consequence with (Q := (fun s => P s /\ p s)). 
  --- apply AssumeOk.
  --- intros s Hp. exact Hp.
  --- intros s Hq. destruct (DS s Hq). destruct H. invs H0. auto.
Abort.