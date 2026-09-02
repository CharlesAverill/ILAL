(** * Semi-automated proof search for the [derivable]/[derivable2] framework

    The worked examples in [examples.v] were built by hand: for each phase,
    pick [D2StepL]/[D2StepR]/[D2Com]/[D2ComAP], walk the command's syntax
    tree applying [DSeq]/[DChoiceL]/[DChoiceR]/[DAssume_concrete]/
    [DAssign_concrete]/[DRead_concrete]/[DWrite_concrete]/[DUnit], and close
    the resulting state-equality/guard goals by rewriting through a small,
    fixed family of algebra lemmas about [mode_store]/[mode_chan]. All three
    of that is mechanical -- this file factors it into reusable tactics. *)

From ILAL Require Import AL.AL AL.language state tactics.
From Stdlib Require Import NArith List Lia String.
Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.
Open Scope al_scope.

(** ** [msimpl] : normalize [mode_store]/[mode_chan] through update chains

    Repeatedly rewrites a [mode_store m (mode_upd m sig y v) x]/
    [mode_chan m (mode_chan_upd m sig k l) k]-shaped subterm using whichever
    of the "same key" or "different key" algebra lemmas applies, closing
    the "different key" side condition (always a fact about two distinct
    string literals here) with [discriminate].  Leaves a fully-reduced goal
    mentioning only the ORIGINAL (un-updated) state, for the caller to
    close with [assumption]/[exact]/[lia] against whatever hypotheses
    describe that base state. *)

Ltac key_neq := let H := fresh in intro H; discriminate H.

(* Generically discharge a field access against whatever hypothesis of shape
   [x = _] the caller happens to have proved about it (e.g. a [round_entry]
   destructuring giving [Hsecret : sig0.(vstate).(s) "secret" = v]).  This is
   what lets [msimpl] bottom out at the CALLER's own facts about the
   untouched base state, without [automation.v] having to know their names:
   once the other [msimpl_step] rules have peeled a [mode_upd]/[mode_chan_upd]
   chain down to a bare field access on the original state, this picks up
   whatever equation the caller already has about exactly that access. *)
Ltac rewrite_local_hyp :=
  match goal with H : ?x = _ |- context [?x] => rewrite H end.

Ltac msimpl_step :=
  first
    [ rewrite mode_store_upd_eq
    | rewrite mode_chan_get
    | rewrite mode_store_mode_chan_upd
    | rewrite mode_chan_mode_upd
    | rewrite mode_store_mode_upd_neq by key_neq
    | rewrite vch_get
    | rewrite ach_get
    | rewrite vch_achan_upd
    | rewrite ach_vchan_upd
    | rewrite vch_vstore_upd
    | rewrite ach_astore_upd
    | rewrite vch_astore_upd
    | rewrite ach_vstore_upd
    | rewrite vch_neq by key_neq
    | rewrite ach_neq by key_neq
    (* Raw-notation store-read independence, completing the cross-product
       [vch_neq]/[ach_neq] and [vstore_vchan_upd]/[astore_achan_upd] only
       cover part of: needed once a store read must be traced back through a
       MIX of raw-notation updates (e.g. a [D2Com]/[D2ComAP] postcondition
       chained without a [set] naming each intermediate state) rather than
       the [mode_upd]/[mode_chan_upd] function forms. *)
    | rewrite vstore_vupd_neq by key_neq
    | rewrite astore_aupd_neq by key_neq
    | rewrite vstore_aupd_upd
    | rewrite astore_vupd_upd
    | rewrite vstore_achan_upd
    | rewrite astore_vchan_upd
    | rewrite astore_mode_upd_Ok
    | rewrite astore_mode_chan_upd_Ok
    | rewrite vstore_mode_upd_Ad
    | rewrite vstore_mode_chan_upd_Ad
    | rewrite mode_store_Ok
    | rewrite mode_store_Ad
    | rewrite mode_chan_Ok
    | rewrite mode_chan_Ad
    (* Convert the [mode_chan_upd]/[mode_upd] FUNCTION form to the raw
       [[[ :=vch/ach/v/a ]]] notation form, so a term built with one and
       compared against a term built with the other (as happens once a
       [D2Com]/[D2ComAP] postcondition is checked against a [set]-free
       chain of prior updates) normalize to the SAME shape for
       [vch_shadow]/[ach_shadow]/[vch_get]/[ach_get] to then fire on. *)
    | rewrite mode_chan_upd_Ok
    | rewrite mode_chan_upd_Ad
    | rewrite mode_upd_Ok
    | rewrite mode_upd_Ad
    | rewrite_local_hyp ].

Ltac msimpl := repeat msimpl_step.

(** Sanity check: [msimpl] alone reduces a store lookup through three
    unrelated updates down to the base fact, needing only [reflexivity]
    ([rewrite_local_hyp] picks up [H] once the chain is fully peeled, turning
    the goal into [v = v]; unlike [reflexivity] itself, [rewrite] does NOT
    auto-close a goal it reduces to [x = x]). *)
Goal forall sig v,
  sig.(vstate).(s) "secret" = v ->
  mode_store Ok (mode_chan_upd Ok (mode_upd Ok (mode_upd Ok sig "n" 7) "err" 0)
                   "sock" []) "secret" = v.
Proof. intros sig v H. msimpl. reflexivity. Qed.

(** ** [deriv_tac] : build a Tier 1 [derivable] proof by walking the syntax

    Given a goal [(eq X), [c] m, ?Q] for a CONCRETE command [c] (no evars in
    its constructors) and a concrete precondition state [X], recurses on
    [c]'s shape, applying the matching rule from [DSeq]/[DChoiceL]/
    [DChoiceR]/[DAssume_concrete]/[DAssign_concrete]/[DRead_concrete]/
    [DWrite_concrete]/[DUnit]/[DAdvAssertSuccess]/[DAdvAssertFailure].  The
    postcondition [Q] is left as a metavariable throughout and gets
    COMPUTED by unification as each [D*_concrete] lemma's own conclusion
    resolves it -- the caller never has to write [X'] out by hand.

    [AChoice] tries both branches ([first]); [ARead]'s channel-nonempty
    obligation and [AAssume]'s guard are closed by [msimpl] followed by
    whatever of [eassumption]/[reflexivity]/[lia]/[discriminate] applies.
    Falls through to [eassumption] for anything left over (e.g. an [ASkip]
    fact already in context from an earlier step). *)

(* NOTE: deliberately no trailing [idtac] fallback.  [deriv_tac]'s [AChoice]
   case picks a branch via [first [ apply DChoiceL; deriv_tac | apply
   DChoiceR; deriv_tac ]], and [first] only backtracks into the second
   alternative if the first one FAILS.  If [solve_side] papered over an
   unprovable side condition by succeeding via [idtac], the wrong branch's
   residual goal would silently stick around as an unprovable obligation
   instead of triggering backtracking to the correct branch -- exactly the
   case a 3-way guarded [AChoice] needs (e.g. [err_branch]/[guess_branch] in
   [examples.v], where the branch actually taken is not always the first
   syntactic one). *)
(* [DAssume_concrete]'s side goal is [B (mode_store m X)] for whatever named
   [prop] [B] the source [AAssume] uses.  When [B] is an inline lambda (as in
   [examples.v]'s Example 1), the application is already a beta-redex and
   [msimpl]'s rewrites can reach the field projections underneath directly.
   But a NAMED [B] (e.g. [secret_eq_cred], [ret_other]) is an opaque constant
   application, not a redex: [mode_store m X] then sits unapplied to any
   field, so the field-indexed lemmas in [msimpl_step] (which all pattern on
   [mode_store m (...) field]) have nothing to match and only the
   field-agnostic [mode_store_Ok]/[mode_store_Ad] could fire -- prematurely
   collapsing to a raw projection and getting stuck before the [mode_upd]
   chain is peeled.  Unfolding whatever constant heads the goal first
   exposes the field name(s) (and, for a conjunction/negation like
   [ret_other], the shape [repeat split] can then take apart), letting
   [msimpl] do its job either way. *)
Ltac unfold_named_prop := try (match goal with |- ?B _ => unfold B end).

(* [DAdvAssertSuccess]'s conclusion wraps the asserted predicate in
   [aand_lift]/[aand]/[lift] (Table 8's framework combinators, defined in
   [AL.v] itself -- generic across every example, unlike a source-specific
   [B]).  [unfold_named_prop] can't peel these: its goal head there is the
   COMPOUND term [aand_lift Ad Q guess_eq] (an application, not a bare
   reference), which [unfold] rejects.  Unfolding the combinators by name
   first exposes the real conjunction for [repeat split] to take apart, and
   the caller's own [B] (e.g. [guess_eq]) to unfold_named_prop next.

   NOTE: these must be unfolded ONE AT A TIME (chained by [;], not listed
   together in a single [unfold a, b, c]).  A single [unfold] call resolves
   every name it's given against occurrences already present in the goal
   BEFORE any of them fire; since [aand]/[lift] only appear once [aand_lift]
   has been expanded, listing all three together finds [aand_lift] but finds
   NO occurrence of [aand] or [lift] to replace (they aren't there yet) and
   silently drops them, leaving the goal only half-unfolded. *)
Ltac unfold_framework_combinators :=
  try unfold aand_lift; try unfold aand; try unfold lift;
  try unfold anot; try unfold aor.

(* [next_pre_L]/[next_pre_R]/[next_pre_at] name each phase's resolved
   successor state via [evar]-introduced LOCAL DEFINITIONS (e.g. [Y0 := ...
   : estate]) rather than plain metavariables, so that later phases can cite
   a short name instead of the ever-growing raw update chain.  [rewrite]
   treats such a name as opaque -- e.g. [astore_vchan_upd]'s pattern
   [(sig[[j:=vch l]]).(astate).(s) x] cannot match [s (astate Y0) x] no
   matter how many times [msimpl] runs, because [Y0] itself is never
   examined, only substituted for as a whole.  A goal comparing two fields
   that were set on DIFFERENT sides of one such chased-back chain (e.g.
   [guess1] vs [guess2] in Example 3, each traced back through a different
   local) needs [Y0] actually unfolded before [msimpl]'s algebra can see
   through it.  [subst] alone does not do this: it only eliminates
   [x = t]-shaped hypotheses, not [x := t] local definitions. *)
(* NOT wired into [solve_side]: eliminating a shared local [estate] let
   (e.g. an earlier phase's already-resolved successor state) changes the
   term every OTHER goal built from the same [derivable2_cds_step] call
   sees it through, and if a SIBLING goal still has its own [evar]-backed
   successor state relying on that local staying in its recorded context,
   substituting it out from under it breaks that evar's instantiation with
   an opaque "Unable to unify"/"No applicable tactic" failure unrelated to
   the actual side condition -- observed breaking Examples 1/2's otherwise
   generic phases when tried unconditionally.  It can also blow up: fully
   unfolding every prior phase's state before [msimpl] runs turns a modest
   goal into one [msimpl]/[lia]/[eassumption] must search over a much larger
   term, slow enough to be impractical as a blanket default.  Useful only as
   an explicit, LOCAL step a specific proof reaches for on the one goal that
   actually needs it (e.g. Example 3's final [guess1 = guess2], which
   compares two fields chased back through different prior states) --
   never as part of the generic pipeline every phase runs through. *)
Ltac subst_states := repeat match goal with x := _ : estate |- _ => subst x end.

Ltac solve_side :=
  repeat eexists;
  unfold_framework_combinators;
  repeat split;
  repeat (try rewrite vch_shadow; try rewrite ach_shadow);
  unfold_named_prop;
  repeat split;
  msimpl;
  first
    [ eassumption
    | reflexivity
    | lia
    | apply vch_eq; msimpl; (eassumption || reflexivity)
    | apply ach_eq; msimpl; (eassumption || reflexivity)
    | (split; key_neq)
    | key_neq ].

Ltac deriv_tac :=
  match goal with
  | |- derivable _ (ASeq _ _) _ _ => eapply DSeq; [ deriv_tac | deriv_tac ]
  | |- derivable _ (AChoice _ _) _ _ =>
      first [ apply DChoiceL; deriv_tac | apply DChoiceR; deriv_tac ]
  | |- derivable _ (AAssume _) _ _ => apply DAssume_concrete; solve_side
  | |- derivable _ (AAssign _ _) _ _ => apply DAssign_concrete
  | |- derivable _ (ARand _) _ _ => apply DRand
  | |- derivable _ (ARead _ _) _ _ => eapply DRead_concrete; solve_side
  | |- derivable _ (AWrite _ _) _ _ => apply DWrite_concrete
  | |- derivable _ ASkip _ _ => apply DUnit
  | |- derivable _ (AAdvAssert _) _ _ =>
      first [ apply DAdvAssertSuccess; solve_side
            | apply DAdvAssertFailure; solve_side ]
  (* [c] is a named Definition (e.g. [prog_body], [cp_round]) rather than a
     literal constructor application -- unfold it and retry. Must come
     after all the syntactic cases above (so it never shadows them) and
     before the final catch-all (so it doesn't loop unfolding forever). *)
  | |- derivable _ ?c _ _ => progress (unfold c); deriv_tac
  | |- _ => solve_side
  end.

(** ** Tier 2 phase tactics

    Each closes one [cds m1 m2 c1 c2 (X, Y) (X', Y')] goal for a KNOWN
    starting pair [(X, Y)]; the successor pair may be left as metavariables
    ([_, _] or a fresh [evar]) and gets COMPUTED by [deriv_tac] resolving
    the underlying [D*_concrete] chain -- the caller never writes the
    resulting state out by hand, only the starting one. *)

(* One side idle (ASkip), the other runs a Tier-1 command.  Write the goal
   with the unchanging side repeated literally (e.g. [(X', Y)] with the SAME
   [Y] on both sides) and [_] for the side that's being computed -- Coq's
   own elaborator turns that [_] into a fresh evar in the right position,
   which [deriv_tac] then resolves. *)
(* NOTE the bracket order: [derivable2_cds_step]'s FIRST premise ([QB X' Y'])
   mentions the metavariable [QB], which is only PINNED by solving the
   SECOND premise (the actual rule application).  So the second branch runs
   first (branch 1 is left as [idtac], i.e. untouched) and the trailing
   [solve_side] -- which closes what's left after the bracket, i.e. branch
   1 -- runs only once QB is concrete.  Getting this order backwards is
   exactly the "evar not yet resolved" trap the hand-written proofs kept
   hitting. *)
(* NOTE: [D2StepL]/[D2StepR]'s precondition-splitting arguments ([P]/[K] resp.
   [K]/[A]) each appear only inside a lambda-conjunction (e.g.
   [fun sp sa => K sp /\ A sa]), so leaving them for [eapply] to infer from
   the surrounding [derivable2_cds_step] goal is a genuine higher-order
   pattern-unification problem, which Coq is free to POSTPONE rather than
   solve on the spot. If [deriv_tac] then needs the precondition state
   concretely (e.g. a [DRead_concrete] side condition), it isn't resolved
   yet, [reflexivity] can't fire, and [solve_side]'s [vch_eq]/[ach_eq]
   fallback mis-fires by flex-flex imitation, leaving a permanently dangling
   evar. Passing [X]/[Y] explicitly (already bound by the match below) makes
   this a trivial first-order unification instead. *)
Ltac stepL_tac :=
  match goal with
  | |- cds ?m1 ?m2 ?c1 ASkip (?X, ?Y) (?X2, ?Y) =>
      eapply derivable2_cds_step;
      [ | eapply (D2StepL m1 m2 (fun sig => sig = X) c1 _ (fun sig => sig = Y));
          deriv_tac ];
      solve_side
  end.

Ltac stepR_tac :=
  match goal with
  | |- cds ?m1 ?m2 ASkip ?c2 (?X, ?Y) (?X, ?Y2) =>
      eapply derivable2_cds_step;
      [ | eapply (D2StepR m1 m2 (fun sig => sig = X) (fun sig => sig = Y) c2 _);
          deriv_tac ];
      solve_side
  end.

(* A bare Com transfer: [c1 = c2 = ASkip], channel [ch] named explicitly
   (there is no way to infer WHICH channel is being synchronised from the
   goal alone, or what the resulting channel contents are from the goal
   alone -- unlike [stepL_tac]/[stepR_tac], the successor pair CANNOT be
   left as bare metavariables here: proving [QB X' Y'] needs to show
   [X'[[ch :=vch l2]] = X] for the ORIGINAL [X], which requires actually
   CONSTRUCTING [X'] as [X] with the transferred value re-attached -- Coq's
   unifier will not instantiate an already-existing goal evar that way, only
   solve for a genuinely fresh one.  So the caller writes [X'] and [Y'] out
   explicitly (still short: just the one channel-update expression each),
   and [com_tac]/[comAP_tac] automate the [vch_shadow]/[vch_eq] rewrite
   dance and the search for the transferred value/tail that this needs.
   [com_tac ch] is program -> adversary ([D2Com]/[CComPA]); [comAP_tac ch]
   is adversary -> program ([D2ComAP]/[CComAP]). *)
Ltac com_tac ch :=
  match goal with
  | |- cds ?m1 ?m2 ASkip ASkip (?X, ?Y) (?X2, ?Y2) =>
      eapply derivable2_cds_step;
      [ | eapply (D2Com m1 m2 _ ASkip ASkip ch) ];
      solve_side
  end.

Ltac comAP_tac ch :=
  match goal with
  | |- cds ?m1 ?m2 ASkip ASkip (?X, ?Y) (?X2, ?Y2) =>
      eapply derivable2_cds_step;
      [ | eapply (D2ComAP m1 m2 _ ASkip ASkip ch) ];
      solve_side
  end.

(** Pull the (fully computed, evar-free) successor pair out of an already
    proved [cds] fact, so the next phase's precondition never has to be
    typed out by hand.  [next_pre_L]/[next_pre_R] open (do not close) the
    goal for a [stepL_tac]/[stepR_tac] phase; follow with [{ tac. }] to
    discharge it.  No state, not even the starting one, is ever written out
    by the caller past the very first phase.

    NOTE: [stepL_tac]'s (resp. [stepR_tac]'s) own pattern needs the
    UNCHANGING side of the successor pair to be LITERALLY the same term as
    the precondition's -- not merely another [estate], which is all two
    independently-created evars would give it.  So these are split by which
    side changes (rather than one [next_pre] with two fresh evars): the
    unchanged component is copied over verbatim, and only the changing side
    gets a fresh evar for [deriv_tac] to resolve. *)
Ltac next_pre_L H c1 name :=
  lazymatch type of H with
  | cds ?m1 ?m2 _ _ _ (?PreX, ?PreY) =>
      let X' := fresh "X" in
      evar (X' : estate);
      assert (name : cds m1 m2 c1 ASkip (PreX, PreY) (X', PreY))
  end.

Ltac next_pre_R H c2 name :=
  lazymatch type of H with
  | cds ?m1 ?m2 _ _ _ (?PreX, ?PreY) =>
      let Y' := fresh "Y" in
      evar (Y' : estate);
      assert (name : cds m1 m2 ASkip c2 (PreX, PreY) (PreX, Y'))
  end.

(** The Com-phase counterpart of [next_pre]: the successor pair must be
    given EXPLICITLY (see [com_tac]/[comAP_tac]'s comment for why), so this
    just threads [PrevH]'s successor pair into the precondition slot and
    opens the goal for [c1]/[c2]/[X2]/[Y2] as given. *)
Ltac next_pre_at H c1 c2 X2 Y2 name :=
  lazymatch type of H with
  | cds ?m1 ?m2 _ _ _ ?q => assert (name : cds m1 m2 c1 c2 q (X2, Y2))
  end.

(** ** Chaining

    [chain_tac] threads a list of already-proved [cds] phase facts into one
    [cds_star_hetero] witness via [cds_cds_star_hetero]/
    [cds_star_hetero_trans], so the caller doesn't have to hand-nest
    [eapply cds_star_hetero_trans] once per phase. *)
Ltac chain1 H := exact (cds_cds_star_hetero _ _ _ _ _ _ H).
Ltac chain_tac Hs :=
  match Hs with
  | (?Hs', ?H) =>
      eapply cds_star_hetero_trans; [ chain_tac Hs' | chain1 H ]
  | ?H => chain1 H
  end.
