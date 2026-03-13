From Stdlib Require Export NArith String.
From Stdlib Require Import FunctionalExtensionality.
Open Scope N_scope.
Open Scope string_scope.

(** Basic definitions of state and updates *)

Definition id : Set := string.
Definition state : Type := id -> N.

Definition update {V : Type} (s : id -> V) (k : id) (v : V) :=
    fun k' => if String.eqb k k' then v else s k'.
Notation "s [ k ':=' v ]" := (update s k v)
                             (at level 50, left associativity).

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

(* State assertions *)
Definition prop : Type := state -> Prop.

Definition prop_of_Prop (p : Prop) : prop :=
  fun _ => p.
Coercion prop_of_Prop : Sortclass >-> prop.

Close Scope N.
Close Scope string_scope.