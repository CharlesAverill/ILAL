From Stdlib Require Export NArith.
From ILAL Require Export state.
From Stdlib Require Import List.
Open Scope N_scope.

(** Language used in Adversarial Logic paper *)
Declare Scope al_scope.
Open Scope al_scope.

(* Channels *)
Definition channel : Set := list N.
Definition chan_env : Set := id -> channel.

Record cstate : Type := {
  s : state;
  ch : chan_env
}.

(* Full environment state *)
Record estate : Type := {
  vstate : cstate;
  astate : cstate
}.

Definition update_victim (sig : estate) (x : id) (v : N) : estate :=
  {| vstate   := {| s := sig.(vstate).(s)[x := v]; ch := sig.(vstate).(ch)|};
     astate   := sig.(astate)|}.

Definition update_adversary (sig : estate) (x : id) (v : N) : estate :=
  {| vstate   := sig.(vstate);
     astate   := {| s := sig.(astate).(s)[x := v]; ch := sig.(astate).(ch)|} |}.

Definition update_vchannel (sig : estate) (x : id) (v : channel) : estate :=
  {| vstate   := {| s := sig.(vstate).(s); ch := sig.(vstate).(ch)[x := v]|};
     astate   := sig.(astate)|}.

Definition update_achannel (sig : estate) (x : id) (v : channel) : estate :=
  {| vstate   := sig.(vstate);
     astate   := {| s := sig.(astate).(s); ch := sig.(astate).(ch)[x := v]|} |}.

Notation "sig [[ x :=v v ]]"  := (update_victim sig x v)
  (at level 10, x at next level, v at next level).
Notation "sig [[ x :=a v ]]"  := (update_adversary sig x v)
  (at level 10, x at next level, v at next level).
Notation "sig [[ s :=ach l ]]" := (update_achannel sig s l)
  (at level 10, s at next level, l at next level).
Notation "sig [[ s :=vch l ]]" := (update_vchannel sig s l)
  (at level 10, s at next level, l at next level).

(* Stateful expressions *)
Definition expression : Type := state -> N.

Definition exp_of_N (n : N) : expression := fun _ => n.
Coercion exp_of_N : N >-> expression.

(** Language syntax *)

Declare Custom Entry al_stmt.
Declare Custom Entry al_stmt_aux.

Inductive astmt : Type :=
  | ASkip
  | AAssign (x : id) (e : expression)
  | ARand (x : id)
  | ASeq (c1 c2 : astmt)
  | APar (c1 c2 : astmt)
  | AAssume (P : prop)
  | AStar (c : astmt)
  | AChoice (c1 c2 : astmt)
  | ARead (s x : id)
  | AWrite (s x : id)
  | AAdvAssert (P : prop)
  | ACom (c1 c2 : astmt).

Open Scope al_scope.

Notation "<{ e }>" := e (e custom al_stmt_aux) : al_scope.
Notation "e" := e
  (in custom al_stmt_aux at level 0, e custom al_stmt) : al_scope.
Notation "x" := x
  (in custom al_stmt at level 0, x constr at level 0) : al_scope.
Notation "( x )" := x
  (in custom al_stmt, x at level 99) : al_scope.

Notation "'skip'" := ASkip
  (in custom al_stmt at level 0) : al_scope.

Notation "x ':=' e" := (AAssign x e)
  (in custom al_stmt at level 0,
   x constr at level 0, e at level 85, no associativity) : al_scope.
Notation "x ':=' 'rand()'" := (ARand x)
  (in custom al_stmt at level 0,
   x constr at level 0, no associativity) : al_scope.

Infix ";;" := ASeq
  (in custom al_stmt at level 90, right associativity) : al_scope.
Infix "<||>" := APar
  (in custom al_stmt at level 90, right associativity) : al_scope.
Infix "<+>" := AChoice
  (in custom al_stmt at level 90, right associativity) : al_scope.
Notation "C '**'" := (AStar C)
  (in custom al_stmt at level 80, left associativity) : al_scope.

Notation "'assume' '(' P ')'" := (AAssume P)
  (in custom al_stmt at level 50) : al_scope.

Notation "'read(' s ',' x ')'" := (ARead s x)
  (in custom al_stmt at level 0,
   s constr at level 0, x constr at level 0, no associativity) : al_scope.
Notation "'write(' s ',' x ')'" := (AWrite s x)
  (in custom al_stmt at level 0,
   s constr at level 0, x constr at level 0, no associativity) : al_scope.

Notation "'adv_assert(' P ')'" := (AAdvAssert P)
  (in custom al_stmt at level 0,
   P at level 85, no associativity) : al_scope.

Notation "'Com(' c1 ',' c2 ')'" := (ACom c1 c2)
  (in custom al_stmt at level 0,
   c1 custom al_stmt at level 99,
   c2 custom al_stmt at level 99, no associativity) : al_scope.

Declare Scope prop_scope.
Bind Scope prop_scope with prop.
Delimit Scope prop_scope with prop.
Open Scope prop_scope.

Notation assert P := (P%prop : prop).

Notation "~ P" := (fun st => ~ assert P st) (in custom al_stmt at level 0, P constr at level 0) : prop_scope.
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

Notation "'if' B 'then' C1 'else' C2" := <{(assume(B) ;; C1) <+> (assume(~B) ;; C2)}>
  (in custom al_stmt at level 0,
   B constr,
   C1 custom al_stmt at level 99,
   C2 custom al_stmt at level 99, no associativity) : al_scope.

Notation "'while' B 'do' C 'done'" := <{(assume(B) ;; C) ** ;; assume(~B) }>
  (in custom al_stmt at level 0,
   B constr, C custom al_stmt at level 99, no associativity) : al_scope.

Close Scope prop_scope.
Close Scope al_scope.