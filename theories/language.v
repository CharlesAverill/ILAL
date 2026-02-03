From Stdlib Require Export NArith String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Decidable.
Open Scope N_scope.
Open Scope string_scope.

(** Language used in Incorrectness Logic paper *)
Declare Scope simpl_scope.
Open Scope simpl_scope.

(** Basic definitions of state and updates *)

Definition id : Set := string.
Definition state : Type := id -> N.

Definition update {V : Type} (s : id -> V) (k : id) (v : V) :=
    fun k' => if String.eqb k k' then v else s k'.
Notation "s [ k ':=' v ]" := (update s k v)
                             (at level 50, left associativity) : simpl_scope.

Definition empty {V : Type} : id -> option V := fun _ => None.

Theorem update_eq : forall V s k (v : V),
    s[k := v] k = v.
Proof.
    intros. unfold update. now rewrite String.eqb_refl.
Qed.

Theorem update_neq : forall V s k k' (v : V),
    k <> k' ->
    s[k := v] k' = s k'.
Proof.
    intros. unfold update. apply String.eqb_neq in H.
    now rewrite H.
Qed.

Theorem update_shadow : forall V s k (v v' : V),
    s[k := v][k := v'] = s[k := v'].
Proof.
    intros. unfold update. extensionality x.
    now destruct (k =? x)%string.
Qed.

Theorem update_swap : forall V s k k' (v v' : V),
    k <> k' ->
    s[k := v][k' := v'] = s[k' := v'][k := v].
Proof.
    intros. unfold update. extensionality x.
    destruct (k =? x)%string eqn:E, (k' =? x)%string eqn:E0;
        try rewrite String.eqb_eq in *; now subst.
Qed.

Theorem state_upd_eq : forall V s k (v : V),
    s k = v ->
    s[k := v] = s.
Proof.
    intros. unfold update. extensionality x.
    destruct (k =? x)%string eqn:E.
        rewrite String.eqb_eq in E. now subst.
    reflexivity.
Qed.

(** Language syntax *)

Definition prop : Type := state -> Prop.

Definition prop_of_Prop (p : Prop) : prop :=
  fun _ => p.
Coercion prop_of_Prop : Sortclass >-> prop.

Definition expression : Type := state -> N.

Definition exp_of_N (n : N) : expression :=
  fun _ => n.
Coercion exp_of_N : N >-> expression.

Declare Custom Entry stmt.
Declare Custom Entry stmt_aux.
Inductive stmt : Type :=
| Skip
| Assign (i : id) (exp : expression)
| NondetAssign (i : id)
| Seq (s1 s2 : stmt)
| Choice (s1 s2 : stmt)
| Star (s : stmt)
| Error
| Assumes (p : prop).

Notation "<{ e }>" := e (e custom stmt_aux) : simpl_scope.
Notation "e" := e (in custom stmt_aux at level 0, e custom stmt) : simpl_scope.
Notation "x" := x (in custom stmt at level 0, x constr at level 0) : simpl_scope.
Notation "( x )" := x (in custom stmt, x at level 99) : simpl_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom stmt at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : simpl_scope.
Notation "'fun' s '=>' e" := (fun s => e) (in custom stmt at level 0, only parsing, s constr, e constr) : simpl_scope.

Notation "'skip'" := Skip (in custom stmt at level 0).
Notation "i := e" := (Assign i e)
        (in custom stmt at level 0, i constr at level 0,
         e at level 85, no associativity) : simpl_scope.
Notation "i := 'nondet()'" := (NondetAssign i)
        (in custom stmt at level 0, i constr at level 0,
         no associativity) : simpl_scope.
Infix ";;" := Seq
      (in custom stmt at level 90,
            right associativity) : simpl_scope.
Infix "<+>" := Choice
      (in custom stmt at level 90,
            right associativity) : simpl_scope.
Notation "c '**'" := (Star c)
      (in custom stmt at level 90,
            c custom stmt,
            right associativity) : simpl_scope.
Notation "'error()'" := Error (in custom stmt at level 0).
Notation "'assumes(' e ')'" := (Assumes e)
         (in custom stmt at level 0,
          e at level 85, no associativity) : simpl_scope.

Declare Scope prop_scope.
Bind Scope prop_scope with prop.
Delimit Scope prop_scope with prop.
Open Scope prop_scope.

Notation assert P := (P%prop : prop).

Notation "~ P" := (fun st => ~ assert P st) (in custom stmt at level 0, P constr at level 0) : prop_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : prop_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : prop_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : prop_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : prop_scope.
Notation "a = b" := (fun st => st a = st b) : prop_scope.
Notation "a <> b" := (fun st => st a <> st b) : prop_scope.
Notation "a <= b" := (fun st => st a <= st b) : prop_scope.
Notation "a < b" := (fun st => st a < st b) : prop_scope.
Notation "a >= b" := (fun st => st a >= st b) : prop_scope.
Notation "a > b" := (fun st => st a > st b) : prop_scope.
Notation "a + b" := (fun st => st a + st b) : prop_scope.
Notation "a - b" := (fun st => st a - st b) : prop_scope.
Notation "a * b" := (fun st => st a * st b) : prop_scope.

Notation "'while' B 'do' C 'done'" :=
        <{((assumes(B) ;; C) **) ;; assumes(~ B)}>
        (in custom stmt at level 0, B constr, C custom stmt at level 99, no associativity) : simpl_scope.
Notation "'If' B 'Then' C1 'Else' C2 'Done'" :=
        <{(assumes(B) ;; C1) <+> (assumes(~ B) ;; C2)}>
        (in custom stmt at level 0, B constr, C1 custom stmt at level 99, C2 custom stmt at level 99, no associativity) : simpl_scope.
Notation "'assert(' B ')'" :=
        <{assumes(B) <+> (assumes(~ B) ;; error()) }>
        (in custom stmt at level 0, B constr, no associativity) : simpl_scope.
Close Scope prop_scope.

(** Language semantics *)

Inductive ExitCondition : Set :=
| er
| ok.

Fixpoint repeat (n : nat) (s : stmt) : stmt :=
    match n with
    | O => Skip
    | S n' => Seq (repeat n' s) s
    end.

Reserved Notation
         "st '=[' c ']=>' ec '|' st'"
         (at level 40, c custom stmt at level 99,
          ec constr, st constr, st' constr at next level).
Inductive step : state -> stmt -> ExitCondition -> state -> Prop :=
| SSkip (s : state) :
    s =[ skip ]=> ok | s
| SAssign (s : state) (x : id) (e : expression) :
    s =[ x := e ]=> ok | (s[x := e s])
| SNondetAssign (s : state) (x : id) (v : N) :
    s =[ x := nondet() ]=> ok | (s[x := v])
| SSeqErr (s1 s2 : state) (c1 c2 : stmt) :
    s1 =[ c1 ]=> er | s2 ->
    s1 =[ c1 ;; c2 ]=> er | s2
| SSeqOk (s1 s2 s3 : state) (c1 c2 : stmt) (ex : ExitCondition) :
    s1 =[ c1 ]=> ok | s2 ->
    s2 =[ c2 ]=> ex | s3 ->
    s1 =[ c1 ;; c2 ]=> ex | s3
| SStar0 (s : state) (c : stmt) :
    s =[ c** ]=> ok | s
| SStarN (s1 s2 : state) (c : stmt) (ex : ExitCondition) :
    s1 =[ c** ;; c ]=> ex | s2 ->
    s1 =[ c** ]=> ex | s2
| SChoiceL (s1 s2 : state) (c1 c2 : stmt) (ex : ExitCondition) :
    s1 =[ c1 ]=> ex | s2 ->
    s1 =[ c1 <+> c2 ]=> ex | s2
| SChoiceR (s1 s2 : state) (c1 c2 : stmt) (ex : ExitCondition) :
    s1 =[ c2 ]=> ex | s2 ->
    s1 =[ c1 <+> c2 ]=> ex | s2
| SError (s : state) :
    s =[ error() ]=> er | s
| SAssumesOk (s : state) (P : prop) :
    P s ->
    s =[ assumes(P) ]=> ok | s

where "st '=[' c ']=>' ec '|' st'" := (step st c ec st').

Theorem nondeterminism :
  ~ (forall s s1' s2' c ex,
      s =[ c ]=> ex | s1' ->
      s =[ c ]=> ex | s2' ->
      s1' = s2').
Proof.
  intro Contra.
  set (empty := fun (_ : id) => 0).
  specialize (Contra empty (empty["x" := 5]) (empty["x" := 6])
    <{"x" := nondet()}> ok).
  assert (empty =[ "x" := nondet() ]=> ok | (empty ["x" := 5])).
    constructor.
  assert (empty =[ "x" := nondet() ]=> ok | (empty ["x" := 6])).
    constructor.
  specialize (Contra H H0).
  assert (empty ["x" := 5] "x" = empty ["x" := 6] "x").
    now rewrite Contra.
  repeat rewrite update_eq in H1.
  discriminate.
Qed.

(** Free variables *)

(* i is free in prop P *)
(* This is what the text describes as free. It seems
   like the opposite *)
Definition free_prop (i : id) (P : prop) : Prop :=
  (forall s,
      P s <-> forall v, P (s[i := v])).

(** Modified variables *)

(* i is modified by command C *)
Fixpoint mod_stmt (i : id) (s : stmt) : Prop :=
  match s with
  | <{ c1 ;; c2 }> => mod_stmt i c1 \/ mod_stmt i c2
  | <{ c1 <+> c2 }> => mod_stmt i c1 \/ mod_stmt i c2
  | <{ c** }> => mod_stmt i c
  | <{ x := v }> => True
  | <{ x := nondet() }> => True
  | <{ _ }> => False
  end.

