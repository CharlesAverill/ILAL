From ILAL Require Import AL.AL AL.language AL.automation state tactics.
From Stdlib Require Import NArith List Lia.
Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.
Open Scope al_scope.

(** * Example 1 from Vanegue's Adversarial Logic (Table 3, "Trivial Case")

    Program:                        Adversary:
      local n in                      local val = alpha in
      local win in                    local res = 0 in
        read(s, n);                     write(s, val);
        if (n > 10M) win := 1           read(s, res);
        else win := 0;                  adv_assert(res == 1)
        write(s, win)

    The adversary introduces the symbolic value [alpha] (here: an arbitrary
    concrete value chosen by the adversary), sends it, reads the program's
    reply, and asserts the flag [res == 1].

    Below we (a) encode the two terms, (b) exercise the base transitions, and
    (c) prove the ATTACK: under the small-step interleaving semantics the
    adversary can drive [program || adversary] to a final state where its
    assertion [res == 1] holds -- i.e. the adversarial-success postcondition is
    reachable.  We use the FLAT programs (fresh globals, no [local] wrapping);
    the semantics supports [local] via [SLocalEnter], and wrapping is an
    instance, but flattening keeps the reachability trace manageable. *)

Definition TEN_M : N := 10000000.

(* Program body (channel "s", vars "n","win").  Built with raw constructors so
   that sub-definitions compose without relying on an application form inside
   the [<{ }>] custom entry. *)
Definition prog_body : astmt :=
  ASeq (ARead "s" "n")
  (ASeq
    (AChoice
      (ASeq (AAssume (fun st => st "n" > TEN_M)) (AAssign "win" (1%N)))
      (ASeq (AAssume (fun st => ~ st "n" > TEN_M)) (AAssign "win" (0%N))))
    (AWrite "s" "win")).

Definition program : astmt :=
  ALocal "n" (0%N) (ALocal "win" (0%N) prog_body).

(* Adversary body: choose [alpha], send it, read reply, assert. *)
Definition adv_body (alpha : N) : astmt :=
  ASeq (AAssign "val" (alpha))
  (ASeq (AWrite "s" "val")
  (ASeq (ARead "s" "res")
        (AAdvAssert (fun st => st "res" = 1%N)))).

Definition adversary (alpha : N) : astmt :=
  ALocal "val" (0%N) (ALocal "res" (0%N) (adv_body alpha)).

(** A concrete initial environment: both stores 0 everywhere, channel "s"
    empty on both sides. *)
Definition zero_store : state := fun _ => 0%N.
Definition empty_chan : chan_env := fun _ => [].

Definition init : estate :=
  {| vstate := {| s := zero_store; ch := empty_chan |};
     astate := {| s := zero_store; ch := empty_chan |} |}.

(** Sanity 1: the [write] step fires on the adversary side, appending the value
    of [val] to the tail of channel "s".  Exercises [EDWriteA].  Stated over a
    general [sig] to avoid brittle nested [init[[...]]] channel notation. *)
Lemma adv_write_fires : forall (sig : estate),
  [[ write("s", "val") ]] Ad
    |=> (sig, sig[[ "s" :=ach
          ((sig.(astate).(ch) "s" ++ [sig.(astate).(s) "val"])%list) ]]).
Proof.
  intro sig. apply EDWriteA.
Qed.

(** Sanity 2: the program's [read] consumes a value [v] published on its
    channel, binding it to [n].  Exercises [EDReadV]. *)
Lemma prog_read_fires : forall (sig : estate) v l,
  sig.(vstate).(ch) "s" = v :: l ->
  [[ read("s", "n") ]] Ok
    |=> (sig, (sig[[ "n" :=v v ]])[[ "s" :=vch l ]]).
Proof.
  intros sig v l H. now apply EDReadV.
Qed.

(** Sanity 3: the adversarial assertion [res == 1] succeeds exactly when the
    adversary store has [res = 1], via [EDAdvAssertSuccess].  Uses the raw
    [AAdvAssert] constructor to sidestep the custom-entry parser (the [<{ }>]
    sugar expects an [al_stmt] argument, not a raw [constr] predicate). *)
Lemma adv_assert_success : forall (sig : estate),
  sig.(astate).(s) "res" = 1%N ->
  ds (AAdvAssert (fun st => st "res" = 1%N)) Ad (sig, sig).
Proof.
  intros sig H. apply EDAdvAssertSuccess. exact H.
Qed.

(** Sanity 4: a [local] block fires end-to-end.  Running [local n = 0 in skip]
    steps from [sig] to [sig] with [n] re-bound to an arbitrary exit value
    [x_out] (entry havoc of [n] to 0, body [skip], exit restores [n] to
    [x_out]). *)
Lemma local_skip_fires : forall (sig : estate) (x_out : N),
  [[ local "n" = (0%N) in skip ]] Ok
    |=> (sig, mode_upd Ok (mode_upd Ok sig "n" (0%N)) "n" x_out).
Proof.
  intros sig x_out.
  apply (EDLocal "n" (fun _ => 0) ASkip Ok sig
                 (mode_upd Ok sig "n" (0%N)) x_out).
  simpl. apply EDSkip.
Qed.

(** ** The attack, under the small-step interleaving semantics.

    Flat program and adversary (fresh globals "n","win","val","res"). *)

Definition prog_flat : astmt := prog_body.

Definition adv_flat (alpha : N) : astmt := adv_body alpha.

(* Convenience: value of channel "s" on each side is empty in [init]. *)
Lemma init_vch : init.(vstate).(ch) "s" = []. Proof. reflexivity. Qed.
Lemma init_ach : init.(astate).(ch) "s" = []. Proof. reflexivity. Qed.

(** The attack theorem.  If the adversary chooses [alpha > TEN_M], then the
    interleaved composition reaches a final state in which [res = 1] on the
    adversary side -- the [adv_assert(res == 1)] fired successfully.

    Proof structure (five phases, chained by [cstep_star_trans]):
      1. adversary runs [val := alpha ; write(s,val)] up to its blocking [read]
         (via [cstep_star_progR]); adversary channel "s" now holds [alpha];
      2. a [Com] (adversary -> program) moves [alpha] onto the program channel;
      3. program runs to completion: [read] gets [alpha], the guard [n > TEN_M]
         holds so [win := 1], then [write(s,win)] (via [cstep_star_progL]);
      4. a [Com] (program -> adversary) moves [win = 1] onto the adv channel;
      5. adversary runs [read(s,res) ; adv_assert(res == 1)]: [res] becomes 1 and
         the assertion SUCCEEDS via [SAdvAssertS]. *)
Theorem example1_attack : forall alpha,
  (alpha > TEN_M)%N ->
  attack_reaches prog_flat (adv_flat alpha) init
                 (fun sig => sig.(astate).(s) "res" = 1%N).
Proof.
  intros alpha Hbig.
  unfold attack_reaches, prog_flat, adv_flat, adv_body, prog_body.

  (* --- Phase 1: adversary sends alpha, stops at read(s,res). --- *)
  (* s1 : state after [val := alpha] then [write(s,"val")]. *)
  set (s0 := init).
  set (s0a := mode_upd Ad s0 "val" alpha).                 (* val := alpha *)
  set (s1 := mode_chan_upd Ad s0a "s"
              (mode_chan Ad s0a "s" ++ [mode_store Ad s0a "val"])%list). (* write *)
  assert (Phase1 :
    cstep_star prog_body (ASeq (AAssign "val" alpha)
                 (ASeq (AWrite "s" "val")
                   (ASeq (ARead "s" "res")
                         (AAdvAssert (fun st => st "res" = 1%N)))))
               init
               prog_body
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s1).
  { apply cstep_star_progR.
    eapply sstep_star_trans.
    - apply (sstep_seq_run Ad (AAssign "val" alpha) s0 s0a).
      apply sstep_one. apply SAssign.
    - apply (sstep_seq_run Ad (AWrite "s" "val") s0a s1).
      apply sstep_one. unfold s1. apply SWrite. }

  (* --- Phase 2: Com adversary -> program delivers alpha to prog channel. --- *)
  (* adversary channel "s" of s1 is [alpha]; program channel "s" is []. *)
  set (s2 := s1[[ "s" :=ach [] ]] [[ "s" :=vch ([] ++ [alpha])%list ]]).
  assert (Hs1_ach : s1.(astate).(ch) "s" = [alpha]).
  { unfold s1. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, mode_store_Ad.
    unfold s0a. rewrite mode_upd_Ad, ach_astore_upd, astore_aupd_eq.
    unfold s0. rewrite init_ach. reflexivity. }
  assert (Hs1_vch : s1.(vstate).(ch) "s" = []).
  { unfold s1. rewrite mode_chan_upd_Ad, vch_achan_upd.
    unfold s0a. rewrite mode_upd_Ad, vch_astore_upd.
    unfold s0. rewrite init_vch. reflexivity. }
  assert (Phase2 :
    cstep_star prog_body
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s1
               prog_body
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s2).
  { eapply CSTN.
    - apply (CStepComAP prog_body _ "s" s1 alpha [] []).
      + rewrite Hs1_ach. reflexivity.
      + exact Hs1_vch.
    - apply CST0. }

  (* --- Phase 3: program reads alpha, computes win := 1, writes it. --- *)
  (* In s2: program channel "s" = [alpha]; run prog_body to completion. *)
  set (s2n := mode_chan_upd Ok (mode_upd Ok s2 "n" alpha) "s" []).   (* read *)
  set (s2w := mode_upd Ok s2n "win" 1).                              (* win := 1 *)
  set (s3 := mode_chan_upd Ok s2w "s"
              (mode_chan Ok s2w "s" ++ [mode_store Ok s2w "win"])%list).  (* write *)
  assert (Hs2_vch : s2.(vstate).(ch) "s" = [alpha]).
  { unfold s2. rewrite vch_get. reflexivity. }
  assert (Hn_big : mode_store Ok (mode_upd Ok s2 "n" alpha) "n" > TEN_M).
  { rewrite mode_store_upd_eq. exact Hbig. }
  assert (Phase3 :
    cstep_star prog_body
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s2
               ASkip
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s3).
  { apply cstep_star_progL.
    (* read(s,n) *)
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok (ARead "s" "n") s2 s2n).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs2_vch. }
    (* choice -> left branch (guard holds), win := 1 *)
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok
               (AChoice
                 (ASeq (AAssume (fun st => st "n" > TEN_M)) (AAssign "win" 1))
                 (ASeq (AAssume (fun st => ~ st "n" > TEN_M)) (AAssign "win" 0)))
               s2n s2w).
      eapply SSN. apply SChoiceL.
      eapply SSN. apply SSeqStep. apply SAssume.
      { (* guard [n > TEN_M] at s2n, where n was just set to alpha *)
        cbn beta. rewrite mode_store_Ok.
        unfold s2n. rewrite mode_chan_upd_Ok, vstore_vchan_upd.
        rewrite mode_upd_Ok, vstore_vupd_eq. exact Hbig. }
      eapply SSN. apply SSeqSkip.
      apply sstep_one. unfold s2w. apply SAssign. }
    (* write(s,win) *)
    apply sstep_one. unfold s3. apply SWrite. }

  (* --- Phase 4: Com program -> adversary delivers win = 1. --- *)
  set (s4 := s3[[ "s" :=vch [] ]] [[ "s" :=ach ([] ++ [1])%list ]]).
  assert (Hs2n_vch : mode_chan Ok s2n "s" = []).
  { unfold s2n. now rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get. }
  assert (Hs3_vch : s3.(vstate).(ch) "s" = [1%N]).
  { unfold s3. rewrite vch_get.
    unfold s2w. now rewrite mode_chan_mode_upd, mode_store_upd_eq, Hs2n_vch. }
  assert (Hs3_ach : s3.(astate).(ch) "s" = []).
  { unfold s3, s2w, s2n, s2.
    (* all program-side channel/store updates leave the adversary channel alone *)
    repeat (rewrite ach_get_vupd || rewrite ach_get_store || idtac).
    reflexivity. }
  assert (Phase4 :
    cstep_star ASkip
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s3
               ASkip
               (ASeq (ARead "s" "res")
                     (AAdvAssert (fun st => st "res" = 1%N)))
               s4).
  { eapply CSTN.
    - apply (CStepComPA ASkip _ "s" s3 1%N [] []).
      + rewrite Hs3_vch. reflexivity.
      + exact Hs3_ach.
    - apply CST0. }

  (* --- Phase 5: adversary reads res = 1, assertion succeeds. --- *)
  set (s4r := mode_chan_upd Ad (mode_upd Ad s4 "res" 1) "s" []).  (* read *)
  assert (Hs4_ach : s4.(astate).(ch) "s" = [1%N]).
  { unfold s4. rewrite ach_get. reflexivity. }
  assert (Hres1 : s4r.(astate).(s) "res" = 1%N).
  { unfold s4r. unfold mode_chan_upd, mode_upd; simpl.
    unfold update_achannel, update_adversary; simpl.
    rewrite update_eq. reflexivity. }
  exists s4r. split.
  - (* the composed run: chain all five phases *)
    eapply cstep_star_trans. exact Phase1.
    eapply cstep_star_trans. exact Phase2.
    eapply cstep_star_trans. exact Phase3.
    eapply cstep_star_trans. exact Phase4.
    (* Phase 5 *)
    apply cstep_star_progR.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ad (ARead "s" "res") s4 s4r).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs4_ach. }
    apply sstep_one. apply SAdvAssertS. exact Hres1.
  - exact Hres1.
Qed.

(** ** Example 1, rebuilt on the derivable/derivable2 proof framework

    [example1_attack] above proves the same scenario entirely over the
    small-step operational semantics -- it never touches [derivable],
    [derivable2], [soundness], [soundness2], or any named AL rule.  This
    theorem instead builds the SAME attack out of the actual rules,
    matching Table 4's own derivation: [DAssign]/[DWrite] (adversary sends
    alpha), [D2ComAP] (delivered to the program), [DRead]/[DChoiceL]/
    [DAssume]/[DAssign]/[DWrite] (program reads, branches, replies),
    [D2Com] (delivered to the adversary), [DRead]/[DAdvAssertSuccess]
    (adversary reads, asserts, succeeds) -- glued phase by phase via
    [derivable2_cds_step] and [cds_star_hetero].

    [cds]'s composed pair keeps the program's and the adversary's views as
    TWO SEPARATE evolving states (see [cds]'s own comments), synchronised
    only by Com steps -- unlike [attack_reaches]'s single shared state.  So
    [sp_i] (program's own view) and [sa_i] (adversary's own view) are
    tracked separately below, both starting at [init] and diverging until
    a Com step re-synchronises the relevant channel.

    Uses the flat [prog_body]/[adv_body alpha] (no [ALocal] wrapping), for
    the same reason [example1_attack] does: [DLocal] needs the ENTIRE
    local scope proved as one Tier-1 fact in one go (it's a single [ds]
    step), which cannot have a Com step interleaved partway through it --
    exactly the row-by-row granularity this proof needs. *)
Theorem example1_attack_via_AL : forall alpha,
  (alpha > TEN_M)%N ->
  attack_reaches_AL Ok Ad init init
    (fun sig => sig.(astate).(s) "res" = 1%N).
Proof.
  intros alpha Hbig. unfold attack_reaches_AL.
  set (sp0 := init). set (sa0 := init).

  (* --- Phase 1: adversary computes val := alpha and sends it (D2StepR). --- *)
  set (val_st := mode_upd Ad sa0 "val" alpha).
  set (sa1 := mode_chan_upd Ad val_st "s"
                (mode_chan Ad val_st "s" ++ [mode_store Ad val_st "val"])%list).
  assert (Phase1 : cds Ok Ad ASkip (ASeq (AAssign "val" alpha) (AWrite "s" "val"))
                       (sp0, sa0) (sp0, sa1)).
  { eapply (derivable2_cds_step Ok Ad ASkip (ASeq (AAssign "val" alpha) (AWrite "s" "val"))
              sp0 sa0 sp0 sa1).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp0) (fun sig => sig = sa0)
               (ASeq (AAssign "val" alpha) (AWrite "s" "val")) (fun sig => sig = sa1)).
    2: { eapply DSeq.
         - apply DAssign_concrete.
         - apply DWrite_concrete. }
    split; reflexivity. }

  (* --- Phase 2: Com adversary -> program delivers alpha (D2ComAP). --- *)
  set (sp1 := sp0).
  assert (Hsa1_ach : sa1.(astate).(ch) "s" = [alpha]).
  { unfold sa1. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, mode_store_Ad.
    unfold val_st. now rewrite mode_upd_Ad, astore_aupd_eq. }
  set (sp2 := sp1[[ "s" :=vch ([] ++ [alpha])%list ]]).
  set (sa2 := sa1[[ "s" :=ach [] ]]).
  assert (Phase2 : cds Ok Ad ASkip ASkip (sp1, sa1) (sp2, sa2)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp1 sa1 sp2 sa2).
    2: apply (D2ComAP Ok Ad (fun sig sig' => sig = sp1 /\ sig' = sa1) ASkip ASkip "s").
    exists alpha, (@nil N), (@nil N). repeat split.
    - unfold sp2. rewrite vch_shadow. apply vch_eq. unfold sp1, sp0, init. reflexivity.
    - unfold sa2. rewrite ach_shadow. apply ach_eq. exact Hsa1_ach. }

  (* --- Phase 3: program reads alpha, computes win := 1, writes it (D2StepL). --- *)
  set (sp2n := mode_chan_upd Ok (mode_upd Ok sp2 "n" alpha) "s" []).
  set (sp2w := mode_upd Ok sp2n "win" 1).
  set (sp3 := mode_chan_upd Ok sp2w "s"
                (mode_chan Ok sp2w "s" ++ [mode_store Ok sp2w "win"])%list).
  set (sa3 := sa2).
  assert (Hsp2_vch : sp2.(vstate).(ch) "s" = [alpha]).
  { unfold sp2. now rewrite vch_get. }
  assert (Hsp2n_n : mode_store Ok sp2n "n" = alpha).
  { unfold sp2n. rewrite mode_store_mode_chan_upd. now rewrite mode_store_upd_eq. }
  assert (Phase3 : cds Ok Ad prog_body ASkip (sp2, sa2) (sp3, sa3)).
  { eapply (derivable2_cds_step Ok Ad prog_body ASkip sp2 sa2 sp3 sa3).
    2: apply (D2StepL Ok Ad (fun sig => sig = sp2) prog_body (fun sig => sig = sp3)
               (fun sig => sig = sa2)).
    2: { unfold prog_body.
         eapply DSeq. { apply (DRead_concrete Ok "s" "n" sp2 alpha [] Hsp2_vch). }
         eapply DSeq.
         - apply DChoiceL. eapply DSeq.
           + apply DAssume_concrete. exact Hbig.
           + apply DAssign_concrete.
         - apply DWrite_concrete. }
    split; reflexivity. }

  (* --- Phase 4: Com program -> adversary delivers win = 1 (D2Com). --- *)
  assert (Hsp2w_win : mode_store Ok sp2w "win" = 1).
  { unfold sp2w. now rewrite mode_store_upd_eq. }
  assert (Hsp3_vch : sp3.(vstate).(ch) "s" = [1%N]).
  { unfold sp3. rewrite vch_get, Hsp2w_win.
    unfold sp2w. rewrite mode_chan_mode_upd.
    unfold sp2n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get. reflexivity. }
  assert (Hsa3_ach : sa3.(astate).(ch) "s" = []).
  { unfold sa3, sa2. rewrite ach_get. reflexivity. }
  set (sp4 := sp3[[ "s" :=vch [] ]]).
  set (sa4 := sa3[[ "s" :=ach ([] ++ [1])%list ]]).
  assert (Phase4 : cds Ok Ad ASkip ASkip (sp3, sa3) (sp4, sa4)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp3 sa3 sp4 sa4).
    2: apply (D2Com Ok Ad (fun sig sig' => sig = sp3 /\ sig' = sa3) ASkip ASkip "s").
    exists 1%N, (@nil N), (@nil N). repeat split.
    + unfold sp4. rewrite vch_shadow. apply vch_eq. exact Hsp3_vch.
    + unfold sa4. rewrite ach_shadow. apply ach_eq. exact Hsa3_ach. }

  (* --- Phase 5: adversary reads res := 1, adv_assert(res == 1) succeeds
     (D2StepR + DAdvAssertSuccess). --- *)
  set (sp5 := sp4).
  assert (Hsa4_ach : sa4.(astate).(ch) "s" = [1%N]).
  { unfold sa4. now rewrite ach_get. }
  set (sa4r := mode_chan_upd Ad (mode_upd Ad sa4 "res" 1) "s" []).
  assert (Hsa4r_res : sa4r.(astate).(s) "res" = 1%N).
  { unfold sa4r. rewrite <- mode_store_Ad, mode_store_mode_chan_upd, mode_store_upd_eq.
    reflexivity. }
  assert (Phase5 : cds Ok Ad ASkip
                       (ASeq (ARead "s" "res") (AAdvAssert (fun st => st "res" = 1%N)))
                       (sp4, sa4) (sp5, sa4r)).
  { eapply (derivable2_cds_step Ok Ad ASkip
              (ASeq (ARead "s" "res") (AAdvAssert (fun st => st "res" = 1%N)))
              sp4 sa4 sp5 sa4r).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp4) (fun sig => sig = sa4)
               (ASeq (ARead "s" "res") (AAdvAssert (fun st => st "res" = 1%N)))
               (fun sig => sig = sa4r /\ (fun st => st "res" = 1%N) (mode_store Ad sig))).
    2: { eapply DSeq. { apply (DRead_concrete Ad "s" "res" sa4 1%N [] Hsa4_ach). }
         apply DAdvAssertSuccess. }
    split. reflexivity. split. reflexivity.
    unfold mode_store. exact Hsa4r_res. }

  (* --- Chain all five phases and conclude. --- *)
  exists sp5, sa4r. split.
  - chain_tac (((( Phase1, Phase2), Phase3), Phase4), Phase5).
  - exact Hsa4r_res.
Qed.

(** ** Example 1, semi-automated (see AL.automation)

    Same theorem as [example1_attack_via_AL], but each phase is discharged
    by [stepL_tac]/[stepR_tac]/[com_tac]/[comAP_tac] instead of by hand: no
    state is written out (Coq's [_] elaborates to the metavariable the
    tactics resolve via unification), and no D*_concrete/DSeq/DChoiceL
    bookkeeping is spelled out. *)
Theorem example1_attack_via_AL_auto : forall alpha,
  (alpha > TEN_M)%N ->
  attack_reaches_AL Ok Ad init init
    (fun sig => sig.(astate).(s) "res" = 1%N).
Proof.
  intros alpha Hbig. unfold attack_reaches_AL.
  assert (Phase1 : cds Ok Ad ASkip (ASeq (AAssign "val" alpha) (AWrite "s" "val"))
                       (init, init) (init, _)) by stepR_tac.
  match type of Phase1 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase1 ASkip ASkip
        (PreX[[ "s" :=vch ([] ++ [alpha])%list ]])
        (PreY[[ "s" :=ach [] ]])
        Phase2
  end.
  { comAP_tac "s". }
  next_pre_L Phase2 prog_body Phase3. { stepL_tac. }
  match type of Phase3 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase3 ASkip ASkip
        (PreX[[ "s" :=vch [] ]])
        (PreY[[ "s" :=ach (mode_chan Ad PreY "s" ++ [mode_store Ok PreX "win"])%list ]])
        Phase4
  end.
  { com_tac "s". }
  next_pre_R Phase4
    (ASeq (ARead "s" "res") (AAdvAssert (fun st => st "res" = 1%N))) Phase5.
  { stepR_tac. }
  match type of Phase5 with
  | cds _ _ _ _ _ (?sq, ?sb) => exists sq, sb
  end.
  split.
  - chain_tac (((( Phase1, Phase2), Phase3), Phase4), Phase5).
  - solve_side.
    Unshelve. all: exact "".
Qed.

(** * Example 2 from Vanegue's Adversarial Logic (Table 1/5, "Oscillating Bit
    Protocol")

    Program:                              Adversary:
      secret := rand();                     ret := 1;
      loop:                                 guess := UINT8_MAX;
        read(sock, cred);                   step := guess/2 + 1;
        if secret == cred then err := 0     loop:
        else if secret < cred then err := 1   write(sock, guess);
        else err := 2;                        read(sock, ret);
        write(sock, err);                     if ret == 1 then guess -= step
                                               else if ret == 2 then guess += step;
                                               step := step/2 + 1;
                                               adv_assert(ret == 0);

    The adversary performs a binary search on [secret] via the 3-valued
    [err]/[ret] oracle.  Below we encode ONE loop round ([cp_round]/
    [ca_round]) and prove: from any round-entry state where the adversary's
    current guess already equals the program's secret ([round_entry]), that
    round's execution reaches [ret == 0], i.e. [adv_assert(ret == 0)]
    succeeds -- the round is a self-sustaining fixed point of the search.

    Matching the paper's own Table 5 derivation (which does not itself prove
    that the halving search reaches [guess = secret] within a bounded number
    of rounds -- it treats existence of such a round as given, via its PBV
    application's implicit [∃n]), we likewise take "the guess has converged"
    as a hypothesis rather than separately proving bisection-search
    convergence, a general numeric fact orthogonal to the adversarial-logic
    content being demonstrated here. *)

(* Program-side 3-way branch selecting [err] from comparing [secret]/[cred]. *)
Definition secret_eq_cred : prop := fun st => st "secret" = st "cred".
Definition secret_lt_cred : prop := fun st => st "secret" < st "cred".
Definition secret_gt_cred : prop := fun st => st "secret" > st "cred".

Definition err_branch : astmt :=
  AChoice (ASeq (AAssume secret_eq_cred) (AAssign "err" (0%N)))
  (AChoice (ASeq (AAssume secret_lt_cred) (AAssign "err" (1%N)))
           (ASeq (AAssume secret_gt_cred) (AAssign "err" (2%N)))).

Definition cp_round : astmt :=
  ASeq (ARead "sock" "cred")
  (ASeq err_branch
        (AWrite "sock" "err")).

(* Adversary-side 3-way branch adjusting [guess] from [ret]. *)
Definition ret_eq0 : prop := fun st => st "ret" = 0.
Definition ret_eq1 : prop := fun st => st "ret" = 1.
Definition ret_eq2 : prop := fun st => st "ret" = 2.
Definition ret_other : prop := fun st => st "ret" <> 1 /\ st "ret" <> 2.

Definition guess_branch : astmt :=
  AChoice (ASeq (AAssume ret_eq1) (AAssign "guess" (fun st => st "guess" - st "step")))
  (AChoice (ASeq (AAssume ret_eq2) (AAssign "guess" (fun st => st "guess" + st "step")))
           (ASeq (AAssume ret_other) ASkip)).

Definition ca_round : astmt :=
  ASeq (AWrite "sock" "guess")
  (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0)))).

(* Round-entry hypothesis: the adversary's current [guess] already equals the
   program's [secret], and the shared channel is quiescent (empty on both
   sides) at the start of this round -- a fresh round boundary. *)
Definition round_entry (sig0 : estate) (v : N) : Prop :=
  sig0.(vstate).(s) "secret" = v /\
  sig0.(astate).(s) "guess" = v /\
  sig0.(vstate).(ch) "sock" = [] /\
  sig0.(astate).(ch) "sock" = [].

(** The round theorem: once the guess has converged to the secret, the round
    reaches an assertion-success state ([ret = 0]). *)
Theorem obt_round_success : forall sig0 v,
  round_entry sig0 v ->
  attack_reaches cp_round ca_round sig0
    (fun sig => sig.(astate).(s) "ret" = 0%N).
Proof.
  intros sig0 v (Hsecret & Hguess & Hvch & Hach).
  unfold attack_reaches, cp_round, ca_round.

  (* --- Phase 1: adversary writes [guess] (= v) to the channel. --- *)
  set (s0 := sig0) in *.
  set (s1 := mode_chan_upd Ad s0 "sock"
              (mode_chan Ad s0 "sock" ++ [mode_store Ad s0 "guess"])%list).
  assert (Phase1 :
    cstep_star
      (ASeq (ARead "sock" "cred") (ASeq err_branch (AWrite "sock" "err")))
      (ASeq (AWrite "sock" "guess")
        (ASeq (ARead "sock" "ret")
          (ASeq guess_branch
                (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                      (AAdvAssert ret_eq0)))))
      s0
      (ASeq (ARead "sock" "cred") (ASeq err_branch (AWrite "sock" "err")))
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s1).
  { apply cstep_star_progR.
    apply (sstep_seq_run Ad (AWrite "sock" "guess") s0 s1
             (ASeq (ARead "sock" "ret")
               (ASeq guess_branch
                     (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                           (AAdvAssert ret_eq0))))).
    apply sstep_one. unfold s1. apply SWrite. }

  (* --- Phase 2: Com adversary -> program delivers [guess] (= v). --- *)
  set (s2 := s1[[ "sock" :=ach [] ]] [[ "sock" :=vch ([] ++ [v])%list ]]).
  assert (Hs1_ach : s1.(astate).(ch) "sock" = [v]).
  { unfold s1. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, mode_store_Ad, Hach, Hguess.
    reflexivity. }
  assert (Hs1_vch : s1.(vstate).(ch) "sock" = []).
  { unfold s1. now rewrite mode_chan_upd_Ad, vch_achan_upd. }
  assert (Phase2 :
    cstep_star
      (ASeq (ARead "sock" "cred") (ASeq err_branch (AWrite "sock" "err")))
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s1
      (ASeq (ARead "sock" "cred") (ASeq err_branch (AWrite "sock" "err")))
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s2).
  { eapply CSTN.
    - apply (CStepComAP _ _ "sock" s1 v [] []); [rewrite Hs1_ach | exact Hs1_vch]; reflexivity.
    - apply CST0. }

  (* --- Phase 3: program reads [cred] (= v), takes [secret == cred], writes
     [err = 0]. --- *)
  set (s2n := mode_chan_upd Ok (mode_upd Ok s2 "cred" v) "sock" []).
  set (s2e := mode_upd Ok s2n "err" 0).
  set (s3 := mode_chan_upd Ok s2e "sock"
              (mode_chan Ok s2e "sock" ++ [mode_store Ok s2e "err"])%list).
  assert (Hs2_vch : s2.(vstate).(ch) "sock" = [v]).
  { unfold s2. rewrite vch_get. reflexivity. }
  assert (Hs2n_secret : mode_store Ok s2n "secret" = v).
  { unfold s2n. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ok s2 "cred" v "secret");
      [ | intro Heq; discriminate Heq ].
    unfold s2, s1. rewrite mode_store_Ok. exact Hsecret. }
  assert (Hs2n_cred : mode_store Ok s2n "cred" = v).
  { unfold s2n. rewrite mode_store_mode_chan_upd, mode_store_upd_eq. reflexivity. }
  assert (Phase3 :
    cstep_star
      (ASeq (ARead "sock" "cred") (ASeq err_branch (AWrite "sock" "err")))
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s2
      ASkip
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s3).
  { apply cstep_star_progL.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok (ARead "sock" "cred") s2 s2n).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs2_vch. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok err_branch s2n s2e).
      unfold err_branch.
      eapply SSN. apply SChoiceL.
      eapply SSN. apply SSeqStep. apply SAssume.
      { cbn beta. unfold secret_eq_cred. now rewrite Hs2n_secret, Hs2n_cred. }
      eapply SSN. apply SSeqSkip.
      apply sstep_one. unfold s2e. apply SAssign. }
    apply sstep_one. unfold s3. apply SWrite. }

  (* --- Phase 4: Com program -> adversary delivers [err = 0] as [ret]. --- *)
  set (s4 := s3[[ "sock" :=vch [] ]] [[ "sock" :=ach ([] ++ [0])%list ]]).
  assert (Hs2e_err : mode_store Ok s2e "err" = 0).
  { unfold s2e. now rewrite mode_store_upd_eq. }
  assert (Hs3_vch : s3.(vstate).(ch) "sock" = [0%N]).
  { unfold s3. rewrite vch_get, Hs2e_err.
    unfold s2e. rewrite mode_chan_mode_upd.
    unfold s2n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get.
    reflexivity. }
  assert (Hs3_ach : s3.(astate).(ch) "sock" = []).
  { unfold s3, s2e, s2n, s2. reflexivity. }
  assert (Phase4 :
    cstep_star
      ASkip
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s3
      ASkip
      (ASeq (ARead "sock" "ret")
        (ASeq guess_branch
              (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                    (AAdvAssert ret_eq0))))
      s4).
  { eapply CSTN.
    - apply (CStepComPA _ _ "sock" s3 0%N [] []); [exact Hs3_vch | exact Hs3_ach].
    - apply CST0. }

  (* --- Phase 5: adversary reads [ret = 0], the no-adjustment branch fires,
     [step] updates, [adv_assert(ret == 0)] succeeds. --- *)
  set (s4r := mode_chan_upd Ad (mode_upd Ad s4 "ret" 0) "sock" []).
  set (s4s := mode_upd Ad s4r "step" (mode_store Ad s4r "step" / 2 + 1)).
  assert (Hs4_ach : s4.(astate).(ch) "sock" = [0%N]).
  { unfold s4. rewrite ach_get. reflexivity. }
  assert (Hs4r_ret : mode_store Ad s4r "ret" = 0).
  { unfold s4r. rewrite mode_store_mode_chan_upd, mode_store_upd_eq. reflexivity. }
  assert (Hs4s_ret : s4s.(astate).(s) "ret" = 0).
  { unfold s4s. rewrite <- mode_store_Ad.
    rewrite (mode_store_mode_upd_neq Ad s4r "step" _ "ret");
      [ exact Hs4r_ret | intro Heq; discriminate Heq ]. }
  exists s4s. split.
  - eapply cstep_star_trans. exact Phase1.
    eapply cstep_star_trans. exact Phase2.
    eapply cstep_star_trans. exact Phase3.
    eapply cstep_star_trans. exact Phase4.
    apply cstep_star_progR.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ad (ARead "sock" "ret") s4 s4r).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs4_ach. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ad guess_branch s4r s4r).
      unfold guess_branch.
      eapply SSN. apply SChoiceR.
      eapply SSN. apply SChoiceR.
      eapply SSN. apply SSeqStep. apply SAssume.
      { cbn beta. unfold ret_other. rewrite Hs4r_ret. split; discriminate. }
      eapply SSN. apply SSeqSkip.
      apply SS0. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ad (AAssign "step" (fun st => st "step" / 2 + 1)) s4r s4s).
      apply sstep_one. unfold s4s. apply SAssign. }
    apply sstep_one. apply SAdvAssertS. exact Hs4s_ret.
  - exact Hs4s_ret.
Qed.

(** ** Example 2, rebuilt on the derivable/derivable2 proof framework

    Same scenario and hypothesis as [obt_round_success] (convergence of the
    guess taken as given, matching the paper's own level of rigor for this
    example), but the round is now driven entirely by the rules: [DWrite]
    (adversary sends its guess), [D2ComAP] (delivered to the program),
    [DRead]/[DChoiceL]/[DAssume]/[DAssign]/[DWrite] (program reads, takes
    the [secret == cred] branch, replies), [D2Com] (delivered to the
    adversary as [ret]), [DRead]/[DChoiceR]/[DChoiceR]/[DAssume]/[DUnit]/
    [DAssign]/[DAdvAssertSuccess] (adversary reads, takes the "no
    adjustment" branch, updates [step], asserts -- succeeds).  As in
    [example1_attack_via_AL], the program's and adversary's views are
    tracked as two separate states [sp_i]/[sa_i], synchronised only at the
    Com phases. *)
Theorem obt_round_success_via_AL : forall sig0 v,
  round_entry sig0 v ->
  attack_reaches_AL Ok Ad sig0 sig0
    (fun sig => sig.(astate).(s) "ret" = 0%N).
Proof.
  intros sig0 v (Hsecret & Hguess & Hvch & Hach). unfold attack_reaches_AL.
  set (sp0 := sig0) in *. set (sa0 := sp0).

  (* --- Phase 1: adversary writes [guess] (= v) (D2StepR). --- *)
  set (sa1 := mode_chan_upd Ad sa0 "sock"
                (mode_chan Ad sa0 "sock" ++ [mode_store Ad sa0 "guess"])%list).
  assert (Phase1 : cds Ok Ad ASkip (AWrite "sock" "guess") (sp0, sa0) (sp0, sa1)).
  { eapply (derivable2_cds_step Ok Ad ASkip (AWrite "sock" "guess") sp0 sa0 sp0 sa1).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp0) (fun sig => sig = sa0)
               (AWrite "sock" "guess") (fun sig => sig = sa1)).
    2: apply DWrite_concrete.
    split; reflexivity. }

  (* --- Phase 2: Com adversary -> program delivers [guess] (= v) (D2ComAP). --- *)
  set (sp1 := sp0).
  assert (Hsa1_ach : sa1.(astate).(ch) "sock" = [v]).
  { unfold sa1, sa0. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, mode_store_Ad, Hach, Hguess.
    reflexivity. }
  set (sp2 := sp1[[ "sock" :=vch ([] ++ [v])%list ]]).
  set (sa2 := sa1[[ "sock" :=ach [] ]]).
  assert (Phase2 : cds Ok Ad ASkip ASkip (sp1, sa1) (sp2, sa2)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp1 sa1 sp2 sa2).
    2: apply (D2ComAP Ok Ad (fun sig sig' => sig = sp1 /\ sig' = sa1) ASkip ASkip "sock").
    exists v, (@nil N), (@nil N). repeat split.
    - unfold sp2. rewrite vch_shadow. apply vch_eq. unfold sp1, sp0. exact Hvch.
    - unfold sa2. rewrite ach_shadow. apply ach_eq. exact Hsa1_ach. }

  (* --- Phase 3: program reads [cred] (= v), takes [secret == cred], writes
     [err = 0] (D2StepL). --- *)
  set (sp2n := mode_chan_upd Ok (mode_upd Ok sp2 "cred" v) "sock" []).
  set (sp2e := mode_upd Ok sp2n "err" 0).
  set (sp3 := mode_chan_upd Ok sp2e "sock"
                (mode_chan Ok sp2e "sock" ++ [mode_store Ok sp2e "err"])%list).
  set (sa3 := sa2).
  assert (Hsp2_vch : sp2.(vstate).(ch) "sock" = [v]).
  { unfold sp2. apply vch_get. }
  assert (Hsp2n_secret : mode_store Ok sp2n "secret" = v).
  { unfold sp2n. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ok sp2 "cred" v "secret");
      [ | intro Heq; discriminate Heq ].
    unfold sp2, sp1, sp0. exact Hsecret. }
  assert (Hsp2n_cred : mode_store Ok sp2n "cred" = v).
  { unfold sp2n. rewrite mode_store_mode_chan_upd. apply mode_store_upd_eq. }
  assert (Phase3 : cds Ok Ad cp_round ASkip (sp2, sa2) (sp3, sa3)).
  { eapply (derivable2_cds_step Ok Ad cp_round ASkip sp2 sa2 sp3 sa3).
    2: apply (D2StepL Ok Ad (fun sig => sig = sp2) cp_round (fun sig => sig = sp3)
               (fun sig => sig = sa2)).
    2: { unfold cp_round.
         eapply DSeq. { apply (DRead_concrete Ok "sock" "cred" sp2 v [] Hsp2_vch). }
         eapply DSeq.
         - unfold err_branch. apply DChoiceL. eapply DSeq.
           + apply DAssume_concrete.
             change (mode_store Ok sp2n "secret" = mode_store Ok sp2n "cred").
             rewrite Hsp2n_secret, Hsp2n_cred. reflexivity.
           + apply DAssign_concrete.
         - apply DWrite_concrete. }
    split; reflexivity. }

  (* --- Phase 4: Com program -> adversary delivers [err = 0] as [ret] (D2Com). --- *)
  assert (Hsp2e_err : mode_store Ok sp2e "err" = 0).
  { unfold sp2e. apply mode_store_upd_eq. }
  assert (Hsp3_vch : sp3.(vstate).(ch) "sock" = [0%N]).
  { unfold sp3. rewrite vch_get, Hsp2e_err.
    unfold sp2e. rewrite mode_chan_mode_upd.
    unfold sp2n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get. reflexivity. }
  assert (Hsa3_ach : sa3.(astate).(ch) "sock" = []).
  { unfold sa3, sa2. apply ach_get. }
  set (sp4 := sp3[[ "sock" :=vch [] ]]).
  set (sa4 := sa3[[ "sock" :=ach ([] ++ [0])%list ]]).
  assert (Phase4 : cds Ok Ad ASkip ASkip (sp3, sa3) (sp4, sa4)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp3 sa3 sp4 sa4).
    2: apply (D2Com Ok Ad (fun sig sig' => sig = sp3 /\ sig' = sa3) ASkip ASkip "sock").
    exists 0%N, (@nil N), (@nil N). repeat split.
    - unfold sp4. rewrite vch_shadow. apply vch_eq. exact Hsp3_vch.
    - unfold sa4. rewrite ach_shadow. apply ach_eq. exact Hsa3_ach. }

  (* --- Phase 5: adversary reads [ret = 0], the no-adjustment branch fires,
     [step] updates, [adv_assert(ret == 0)] succeeds (D2StepR). --- *)
  set (sp5 := sp4).
  assert (Hsa4_ach : sa4.(astate).(ch) "sock" = [0%N]).
  { unfold sa4. apply ach_get. }
  set (sa4r := mode_chan_upd Ad (mode_upd Ad sa4 "ret" 0) "sock" []).
  assert (Hsa4r_ret : mode_store Ad sa4r "ret" = 0).
  { unfold sa4r. rewrite mode_store_mode_chan_upd. apply mode_store_upd_eq. }
  set (sa4s := mode_upd Ad sa4r "step" (mode_store Ad sa4r "step" / 2 + 1)).
  assert (Hsa4s_ret : mode_store Ad sa4s "ret" = 0).
  { unfold sa4s. rewrite (mode_store_mode_upd_neq Ad sa4r "step"
               (mode_store Ad sa4r "step" / 2 + 1)%N "ret");
      [ | intro Heq; discriminate Heq ].
    exact Hsa4r_ret. }
  set (ca_tail := ASeq (ARead "sock" "ret")
                    (ASeq guess_branch
                          (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                                (AAdvAssert ret_eq0)))).
  assert (Phase5 : cds Ok Ad ASkip ca_tail (sp4, sa4) (sp5, sa4s)).
  { eapply (derivable2_cds_step Ok Ad ASkip ca_tail sp4 sa4 sp5 sa4s).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp4) (fun sig => sig = sa4)
               ca_tail
               (fun sig => sig = sa4s /\ ret_eq0 (mode_store Ad sig))).
    2: { unfold ca_tail.
         eapply DSeq. { apply (DRead_concrete Ad "sock" "ret" sa4 0%N [] Hsa4_ach). }
         eapply DSeq.
         - unfold guess_branch. apply DChoiceR. apply DChoiceR. eapply DSeq.
           + apply DAssume_concrete.
             change (mode_store Ad sa4r "ret" <> 1 /\ mode_store Ad sa4r "ret" <> 2).
             rewrite Hsa4r_ret. split; discriminate.
           + apply DUnit.
         - eapply DSeq. { apply DAssign_concrete. }
           apply DAdvAssertSuccess. }
    split. reflexivity. split. reflexivity. unfold ret_eq0. exact Hsa4s_ret. }

  (* --- Chain all five phases and conclude. --- *)
  exists sp5, sa4s. split.
  - chain_tac (((( Phase1, Phase2), Phase3), Phase4), Phase5).
  - exact Hsa4s_ret.
Qed.

(** ** Example 2, semi-automated (see AL.automation)

    Same theorem as [obt_round_success_via_AL], automated the same way as
    [example1_attack_via_AL_auto]. *)
Theorem obt_round_success_via_AL_auto : forall sig0 v,
  round_entry sig0 v ->
  attack_reaches_AL Ok Ad sig0 sig0
    (fun sig => sig.(astate).(s) "ret" = 0%N).
Proof.
  intros sig0 v (Hsecret & Hguess & Hvch & Hach). unfold attack_reaches_AL.
  assert (Phase1 : cds Ok Ad ASkip (AWrite "sock" "guess")
                       (sig0, sig0) (sig0, _)) by stepR_tac.
  match type of Phase1 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase1 ASkip ASkip
        (PreX[[ "sock" :=vch ([] ++ [v])%list ]])
        (PreY[[ "sock" :=ach [] ]])
        Phase2
  end.
  { comAP_tac "sock". }
  next_pre_L Phase2 cp_round Phase3. { stepL_tac. }
  match type of Phase3 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase3 ASkip ASkip
        (PreX[[ "sock" :=vch [] ]])
        (PreY[[ "sock" :=ach (mode_chan Ad PreY "sock" ++ [mode_store Ok PreX "err"])%list ]])
        Phase4
  end.
  { com_tac "sock". }
  next_pre_R Phase4
    (ASeq (ARead "sock" "ret")
      (ASeq guess_branch
            (ASeq (AAssign "step" (fun st => st "step" / 2 + 1))
                  (AAdvAssert ret_eq0)))) Phase5.
  { stepR_tac. }
  match type of Phase5 with
  | cds _ _ _ _ _ (?sq, ?sb) => exists sq, sb
  end.
  split.
  - chain_tac (((( Phase1, Phase2), Phase3), Phase4), Phase5).
  - solve_side.
Qed.

(** * Example 3 from Vanegue's Adversarial Logic (Table 6/7, "Equivalence
    Testing")

    Two pricing services, [GetPrice]/[GetPrice2], compute a price from an
    order size; each has a fast-converging "large order" branch that ignores
    the fractional decay term and simply returns [initp / 10].  An adversary
    queries both services with the SAME order value [num] and asserts their
    replies agree.  Below we combine the two services into one sequential
    program term [program3] (they never interact except by both reading the
    shared [initp], so running them one after another is behaviourally
    equivalent to the paper's two-copy/[Dup] presentation) and prove: for any
    [num] large enough to land BOTH services in their "large order" branch,
    the adversary's [guess1 == guess2] assertion succeeds -- both equal
    [initp / 10].  As with Example 2, the "small order" fractional branch is
    kept in the program text (for fidelity, exactly as the paper's own proof
    leaves it an unresolved [Disj] alternative) but never exercised by this
    attack. *)

Definition V9MIL : N := 9000000.
Definition V18MIL : N := 18000000.
Definition V10MIL : N := 10000000.
Definition V20MIL : N := 20000000.

(* Service 1 (GetPrice), channel "s1". *)
Definition ord_le_9M : prop := fun st => st "ord" <= V9MIL.
Definition ord_gt_9M : prop := fun st => st "ord" > V9MIL.

Definition curp_branch : astmt :=
  AChoice
    (ASeq (AAssume ord_le_9M)
          (AAssign "curp" (fun st => st "initp" * (1 - st "dec"))))
    (ASeq (AAssume ord_gt_9M)
          (AAssign "curp" (fun st => st "initp" / 10))).

Definition getprice_round : astmt :=
  ASeq (ARead "s1" "ord")
  (ASeq (AAssign "dec" (fun st => st "ord" / V10MIL))
        (ASeq curp_branch
              (AWrite "s1" "curp"))).

(* Service 2 (GetPrice2), channel "s2". *)
Definition ord2_le_18M : prop := fun st => st "ord2" <= V18MIL.
Definition ord2_gt_18M : prop := fun st => st "ord2" > V18MIL.

Definition curp2_branch : astmt :=
  AChoice
    (ASeq (AAssume ord2_le_18M)
          (AAssign "curp2" (fun st => st "initp" * (1 - st "dec2"))))
    (ASeq (AAssume ord2_gt_18M)
          (AAssign "curp2" (fun st => st "initp" / 10))).

Definition getprice2_round : astmt :=
  ASeq (ARead "s2" "ord2")
  (ASeq (AAssign "dec2" (fun st => st "ord2" / V20MIL))
        (ASeq curp2_branch
              (AWrite "s2" "curp2"))).

Definition program3 : astmt := ASeq getprice_round getprice2_round.

(* Adversary: query service 1, then service 2, with the same [num]. *)
Definition guess_eq : prop := fun st => st "guess1" = st "guess2".

Definition adv3_round : astmt :=
  ASeq (AWrite "s1" "num")
  (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2")
                    (AAdvAssert guess_eq)))).

Definition eqtest_entry (sig0 : estate) (initp0 num0 : N) : Prop :=
  sig0.(vstate).(s) "initp" = initp0 /\
  sig0.(astate).(s) "num" = num0 /\
  (num0 > V18MIL)%N /\
  sig0.(vstate).(ch) "s1" = [] /\ sig0.(astate).(ch) "s1" = [] /\
  sig0.(vstate).(ch) "s2" = [] /\ sig0.(astate).(ch) "s2" = [].

Theorem eqtest_attack : forall sig0 initp0 num0,
  eqtest_entry sig0 initp0 num0 ->
  attack_reaches program3 adv3_round sig0
    (fun sig => sig.(astate).(s) "guess1" = sig.(astate).(s) "guess2").
Proof.
  intros sig0 initp0 num0 (Hinitp & Hnum & Hbig & Hv1 & Ha1 & Hv2 & Ha2).
  assert (Hbig9 : (num0 > V9MIL)%N) by (unfold V9MIL, V18MIL in *; lia).
  unfold attack_reaches, program3, adv3_round.

  (* --- Phase 1: adversary writes [num] to s1. --- *)
  set (s0 := sig0) in *. clearbody s0.
  set (s1 := mode_chan_upd Ad s0 "s1"
              (mode_chan Ad s0 "s1" ++ [mode_store Ad s0 "num"])%list).
  assert (Phase1 :
    cstep_star (ASeq getprice_round getprice2_round)
      (ASeq (AWrite "s1" "num")
        (ASeq (ARead "s1" "guess1")
          (ASeq (AWrite "s2" "num")
                (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq)))))
      s0
      (ASeq getprice_round getprice2_round)
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s1).
  { apply cstep_star_progR.
    apply (sstep_seq_run Ad (AWrite "s1" "num") s0 s1
             (ASeq (ARead "s1" "guess1")
               (ASeq (AWrite "s2" "num")
                     (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))).
    apply sstep_one. unfold s1. apply SWrite. }

  (* --- Phase 2: Com adversary -> program delivers [num] on s1. --- *)
  set (s2 := s1[[ "s1" :=ach [] ]] [[ "s1" :=vch ([] ++ [num0])%list ]]).
  assert (Hs1_ach1 : s1.(astate).(ch) "s1" = [num0]).
  { unfold s1. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, mode_store_Ad, Ha1, Hnum.
    reflexivity. }
  assert (Hs1_vch1 : s1.(vstate).(ch) "s1" = []).
  { unfold s1. now rewrite mode_chan_upd_Ad, vch_achan_upd. }
  assert (Phase2 :
    cstep_star (ASeq getprice_round getprice2_round)
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s1
      (ASeq getprice_round getprice2_round)
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s2).
  { eapply CSTN.
    - apply (CStepComAP _ _ "s1" s1 num0 [] []); [rewrite Hs1_ach1 | exact Hs1_vch1]; reflexivity.
    - apply CST0. }

  (* --- Phase 3: program (service 1) reads [ord := num0], takes the "large
     order" branch, writes [curp = initp0 / 10]. --- *)
  set (s2n := mode_chan_upd Ok (mode_upd Ok s2 "ord" num0) "s1" []).
  set (s2d := mode_upd Ok s2n "dec" (mode_store Ok s2n "ord" / V10MIL)).
  set (s2c := mode_upd Ok s2d "curp" (mode_store Ok s2d "initp" / 10)).
  set (s3 := mode_chan_upd Ok s2c "s1"
              (mode_chan Ok s2c "s1" ++ [mode_store Ok s2c "curp"])%list).
  assert (Hs2_vch1 : s2.(vstate).(ch) "s1" = [num0]).
  { unfold s2. rewrite vch_get. reflexivity. }
  assert (Hs2n_ord : mode_store Ok s2n "ord" = num0).
  { unfold s2n. rewrite mode_store_mode_chan_upd, mode_store_upd_eq. reflexivity. }
  assert (Hs2d_initp : mode_store Ok s2d "initp" = initp0).
  { unfold s2d. rewrite (mode_store_mode_upd_neq Ok s2n "dec" _ "initp");
      [ | intro Heq; discriminate Heq ].
    unfold s2n. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ok s2 "ord" num0 "initp");
      [ | intro Heq; discriminate Heq ].
    unfold s2, s1. rewrite mode_store_Ok. exact Hinitp. }
  assert (Hs2c_curp : mode_store Ok s2c "curp" = (initp0 / 10)%N).
  { unfold s2c. rewrite mode_store_upd_eq, Hs2d_initp. reflexivity. }
  assert (Phase3 :
    cstep_star (ASeq getprice_round getprice2_round)
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s2
      getprice2_round
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s3).
  { apply cstep_star_progL.
    apply (sstep_seq_run Ok getprice_round s2 s3 getprice2_round).
    unfold getprice_round.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok (ARead "s1" "ord") s2 s2n).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs2_vch1. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok (AAssign "dec" (fun st => st "ord" / V10MIL)) s2n s2d).
      apply sstep_one. unfold s2d. apply SAssign. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok curp_branch s2d s2c).
      unfold curp_branch.
      eapply SSN. apply SChoiceR.
      eapply SSN. apply SSeqStep. apply SAssume.
      { cbn beta. unfold ord_gt_9M. unfold s2d.
        rewrite (mode_store_mode_upd_neq Ok s2n "dec"
                   (mode_store Ok s2n "ord" / V10MIL)%N "ord");
          [ | intro Heq; discriminate Heq ].
        rewrite Hs2n_ord. exact Hbig9. }
      eapply SSN. apply SSeqSkip.
      apply sstep_one. unfold s2c. apply SAssign. }
    apply sstep_one. unfold s3. apply SWrite. }

  (* --- Phase 4: Com program -> adversary delivers [curp = initp0/10] as
     [guess1]. --- *)
  set (s4 := s3[[ "s1" :=vch [] ]] [[ "s1" :=ach ([] ++ [initp0 / 10])%list ]]).
  assert (Hs3_vch1 : s3.(vstate).(ch) "s1" = [(initp0 / 10)%N]).
  { unfold s3. rewrite vch_get, Hs2c_curp.
    unfold s2c. rewrite mode_chan_mode_upd.
    unfold s2d. rewrite mode_chan_mode_upd.
    unfold s2n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get.
    reflexivity. }
  assert (Hs3_ach1 : s3.(astate).(ch) "s1" = []).
  { unfold s3, s2c, s2d, s2n, s2. reflexivity. }
  assert (Phase4 :
    cstep_star getprice2_round
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s3
      getprice2_round
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s4).
  { eapply CSTN.
    - apply (CStepComPA _ _ "s1" s3 (initp0 / 10)%N [] []); [exact Hs3_vch1 | exact Hs3_ach1].
    - apply CST0. }

  (* --- Phase 5: adversary reads [guess1 = initp0/10], writes [num] to s2. --- *)
  set (s4g := mode_chan_upd Ad (mode_upd Ad s4 "guess1" (initp0 / 10)) "s1" []).
  set (s5 := mode_chan_upd Ad s4g "s2"
              (mode_chan Ad s4g "s2" ++ [mode_store Ad s4g "num"])%list).
  assert (Hs4_ach1 : s4.(astate).(ch) "s1" = [(initp0 / 10)%N]).
  { unfold s4. rewrite ach_get. reflexivity. }
  assert (Hs4g_guess1 : mode_store Ad s4g "guess1" = (initp0 / 10)%N).
  { unfold s4g. rewrite mode_store_mode_chan_upd, mode_store_upd_eq. reflexivity. }
  assert (Hs4g_num : mode_store Ad s4g "num" = num0).
  { unfold s4g. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ad s4 "guess1" _ "num");
      [ | intro Heq; discriminate Heq ].
    unfold s4, s3, s2c, s2d, s2n, s2, s1. rewrite mode_store_Ad. exact Hnum. }
  assert (Phase5 :
    cstep_star getprice2_round
      (ASeq (ARead "s1" "guess1")
        (ASeq (AWrite "s2" "num")
              (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))))
      s4
      getprice2_round
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s5).
  { apply cstep_star_progR.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ad (ARead "s1" "guess1") s4 s4g
               (ASeq (AWrite "s2" "num")
                     (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq)))).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs4_ach1. }
    apply (sstep_seq_run Ad (AWrite "s2" "num") s4g s5
             (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))).
    apply sstep_one. unfold s5. apply SWrite. }

  (* --- Phase 6: Com adversary -> program delivers [num] on s2. --- *)
  set (s6 := s5[[ "s2" :=ach [] ]] [[ "s2" :=vch ([] ++ [num0])%list ]]).
  assert (Hs5_ach2 : s5.(astate).(ch) "s2" = [num0]).
  { unfold s5. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, Hs4g_num.
    unfold s4g. rewrite mode_chan_upd_Ad.
    rewrite (ach_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    rewrite mode_upd_Ad, ach_astore_upd.
    unfold s4.
    rewrite (ach_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    rewrite ach_vchan_upd.
    unfold s3. rewrite mode_chan_upd_Ok, ach_vchan_upd.
    unfold s2c. rewrite mode_upd_Ok, ach_vstore_upd.
    unfold s2d. rewrite mode_upd_Ok, ach_vstore_upd.
    unfold s2n. rewrite mode_chan_upd_Ok, ach_vchan_upd.
    rewrite mode_upd_Ok, ach_vstore_upd.
    unfold s2. rewrite ach_vchan_upd.
    rewrite (ach_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold s1.
    rewrite (ach_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    rewrite Ha2. reflexivity. }
  assert (Hs5_vch2 : s5.(vstate).(ch) "s2" = []).
  { unfold s5. rewrite mode_chan_upd_Ad, vch_achan_upd.
    unfold s4g. rewrite mode_chan_upd_Ad, vch_achan_upd, mode_upd_Ad, vch_astore_upd.
    unfold s4. rewrite vch_achan_upd.
    rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold s3. rewrite mode_chan_upd_Ok.
    rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold s2c. rewrite mode_upd_Ok, vch_vstore_upd.
    unfold s2d. rewrite mode_upd_Ok, vch_vstore_upd.
    unfold s2n. rewrite mode_chan_upd_Ok.
    rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    rewrite mode_upd_Ok, vch_vstore_upd.
    unfold s2. rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    rewrite vch_achan_upd.
    unfold s1. rewrite vch_achan_upd.
    exact Hv2. }
  assert (Phase6 :
    cstep_star getprice2_round
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s5
      getprice2_round
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s6).
  { eapply CSTN.
    - apply (CStepComAP _ _ "s2" s5 num0 [] []); [rewrite Hs5_ach2 | exact Hs5_vch2]; reflexivity.
    - apply CST0. }

  (* --- Phase 7: program (service 2) reads [ord2 := num0], takes the "large
     order" branch, writes [curp2 = initp0 / 10]. --- *)
  set (s6n := mode_chan_upd Ok (mode_upd Ok s6 "ord2" num0) "s2" []).
  set (s6d := mode_upd Ok s6n "dec2" (mode_store Ok s6n "ord2" / V20MIL)).
  set (s6c := mode_upd Ok s6d "curp2" (mode_store Ok s6d "initp" / 10)).
  set (s7 := mode_chan_upd Ok s6c "s2"
              (mode_chan Ok s6c "s2" ++ [mode_store Ok s6c "curp2"])%list).
  assert (Hs6_vch2 : s6.(vstate).(ch) "s2" = [num0]).
  { unfold s6. rewrite vch_get. reflexivity. }
  assert (Hs6n_ord2 : mode_store Ok s6n "ord2" = num0).
  { unfold s6n. rewrite mode_store_mode_chan_upd, mode_store_upd_eq. reflexivity. }
  assert (Hs6d_initp : mode_store Ok s6d "initp" = initp0).
  { unfold s6d. rewrite (mode_store_mode_upd_neq Ok s6n "dec2" _ "initp");
      [ | intro Heq; discriminate Heq ].
    unfold s6n. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ok s6 "ord2" num0 "initp");
      [ | intro Heq; discriminate Heq ].
    unfold s6, s5, s4g, s4, s3, s2c, s2d, s2n, s2, s1.
    rewrite mode_store_Ok. exact Hinitp. }
  assert (Hs6c_curp2 : mode_store Ok s6c "curp2" = (initp0 / 10)%N).
  { unfold s6c. rewrite mode_store_upd_eq, Hs6d_initp. reflexivity. }
  assert (Phase7 :
    cstep_star getprice2_round
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s6
      ASkip
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s7).
  { apply cstep_star_progL.
    unfold getprice2_round.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok (ARead "s2" "ord2") s6 s6n).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs6_vch2. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok (AAssign "dec2" (fun st => st "ord2" / V20MIL)) s6n s6d).
      apply sstep_one. unfold s6d. apply SAssign. }
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ok curp2_branch s6d s6c).
      unfold curp2_branch.
      eapply SSN. apply SChoiceR.
      eapply SSN. apply SSeqStep. apply SAssume.
      { cbn beta. unfold ord2_gt_18M. unfold s6d.
        rewrite (mode_store_mode_upd_neq Ok s6n "dec2"
                   (mode_store Ok s6n "ord2" / V20MIL)%N "ord2");
          [ | intro Heq; discriminate Heq ].
        rewrite Hs6n_ord2. exact Hbig. }
      eapply SSN. apply SSeqSkip.
      apply sstep_one. unfold s6c. apply SAssign. }
    apply sstep_one. unfold s7. apply SWrite. }

  (* --- Phase 8: Com program -> adversary delivers [curp2 = initp0/10] as
     [guess2]. --- *)
  set (s8 := s7[[ "s2" :=vch [] ]] [[ "s2" :=ach ([] ++ [initp0 / 10])%list ]]).
  assert (Hs7_vch2 : s7.(vstate).(ch) "s2" = [(initp0 / 10)%N]).
  { unfold s7. rewrite vch_get, Hs6c_curp2.
    unfold s6c. rewrite mode_chan_mode_upd.
    unfold s6d. rewrite mode_chan_mode_upd.
    unfold s6n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get.
    reflexivity. }
  assert (Hs7_ach2 : s7.(astate).(ch) "s2" = []).
  { unfold s7, s6c, s6d, s6n, s6. reflexivity. }
  assert (Phase8 :
    cstep_star ASkip
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s7
      ASkip
      (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
      s8).
  { eapply CSTN.
    - apply (CStepComPA _ _ "s2" s7 (initp0 / 10)%N [] []); [exact Hs7_vch2 | exact Hs7_ach2].
    - apply CST0. }

  (* --- Phase 9: adversary reads [guess2 = initp0/10]; assertion succeeds. --- *)
  set (s8g := mode_chan_upd Ad (mode_upd Ad s8 "guess2" (initp0 / 10)) "s2" []).
  assert (Hs8_ach2 : s8.(astate).(ch) "s2" = [(initp0 / 10)%N]).
  { unfold s8. rewrite ach_get. reflexivity. }
  assert (Hs8g_guess1 : s8g.(astate).(s) "guess1" = (initp0 / 10)%N).
  { unfold s8g, s8, s7, s6c, s6d, s6n, s6.
    change (s5.(astate).(s) "guess1" = initp0 / 10).
    rewrite <- mode_store_Ad. exact Hs4g_guess1. }
  assert (Hs8g_guess2 : s8g.(astate).(s) "guess2" = (initp0 / 10)%N).
  { unfold s8g. rewrite <- mode_store_Ad, mode_store_mode_chan_upd, mode_store_upd_eq.
    reflexivity. }
  exists s8g. split.
  - eapply cstep_star_trans. exact Phase1.
    eapply cstep_star_trans. exact Phase2.
    eapply cstep_star_trans. exact Phase3.
    eapply cstep_star_trans. exact Phase4.
    eapply cstep_star_trans. exact Phase5.
    eapply cstep_star_trans. exact Phase6.
    eapply cstep_star_trans. exact Phase7.
    eapply cstep_star_trans. exact Phase8.
    apply cstep_star_progR.
    eapply sstep_star_trans.
    { apply (sstep_seq_run Ad (ARead "s2" "guess2") s8 s8g).
      apply sstep_one. apply SRead. unfold mode_chan. exact Hs8_ach2. }
    apply sstep_one. apply SAdvAssertS. unfold guess_eq.
    rewrite Hs8g_guess1, Hs8g_guess2. reflexivity.
  - rewrite Hs8g_guess1, Hs8g_guess2. reflexivity.
Qed.

(** ** Example 3, rebuilt on the derivable/derivable2 proof framework

    Same scenario and hypotheses as [eqtest_attack], driven by the rules:
    [DWrite]/[D2ComAP] deliver [num] to service 1, [DRead]/[DChoiceR]/
    [DAssume]/[DAssign]/[DWrite] compute and reply [curp = initp0/10],
    [D2Com] delivers it back as [guess1]; the same shape repeats for
    service 2 via [D2StepR]'s residual-command threading; finally
    [DAdvAssertSuccess] closes the assertion.  No [D2Dup]/[D2Par] is
    needed: [program3] is a single sequential Tier-1 term (as decided with
    the user, since [D2Dup] cannot literally apply to two syntactically
    different services), so this is the same phase-by-phase [D2StepL]/
    [D2StepR]/[D2Com]/[D2ComAP] pattern as the other two examples, just
    with twice as many local-computation phases. *)
Theorem eqtest_attack_via_AL : forall sig0 initp0 num0,
  eqtest_entry sig0 initp0 num0 ->
  attack_reaches_AL Ok Ad sig0 sig0
    (fun sig => sig.(astate).(s) "guess1" = sig.(astate).(s) "guess2").
Proof.
  intros sig0 initp0 num0 (Hinitp & Hnum & Hbig & Hv1 & Ha1 & Hv2 & Ha2).
  unfold attack_reaches_AL.
  assert (Hbig9 : (num0 > V9MIL)%N) by (unfold V9MIL, V18MIL in *; lia).
  set (sp0 := sig0) in *. set (sa0 := sp0).

  (* --- Phase 1: adversary writes [num] to s1 (D2StepR). --- *)
  set (sa1 := mode_chan_upd Ad sa0 "s1"
                (mode_chan Ad sa0 "s1" ++ [mode_store Ad sa0 "num"])%list).
  assert (Phase1 : cds Ok Ad ASkip (AWrite "s1" "num") (sp0, sa0) (sp0, sa1)).
  { eapply (derivable2_cds_step Ok Ad ASkip (AWrite "s1" "num") sp0 sa0 sp0 sa1).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp0) (fun sig => sig = sa0)
               (AWrite "s1" "num") (fun sig => sig = sa1)).
    2: apply DWrite_concrete.
    split; reflexivity. }

  (* --- Phase 2: Com adversary -> program delivers [num] on s1 (D2ComAP). --- *)
  set (sp1 := sp0).
  assert (Hsa1_ach1 : sa1.(astate).(ch) "s1" = [num0]).
  { unfold sa1, sa0. rewrite mode_chan_upd_Ad, ach_get, mode_chan_Ad, mode_store_Ad, Ha1, Hnum.
    reflexivity. }
  set (sp2 := sp1[[ "s1" :=vch ([] ++ [num0])%list ]]).
  set (sa2 := sa1[[ "s1" :=ach [] ]]).
  assert (Phase2 : cds Ok Ad ASkip ASkip (sp1, sa1) (sp2, sa2)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp1 sa1 sp2 sa2).
    2: apply (D2ComAP Ok Ad (fun sig sig' => sig = sp1 /\ sig' = sa1) ASkip ASkip "s1").
    exists num0, (@nil N), (@nil N). repeat split.
    - unfold sp2. rewrite vch_shadow. apply vch_eq. unfold sp1, sp0. exact Hv1.
    - unfold sa2. rewrite ach_shadow. apply ach_eq. exact Hsa1_ach1. }

  (* --- Phase 3: program (service 1) reads [ord := num0], takes the "large
     order" branch, writes [curp = initp0/10] (D2StepL). --- *)
  set (sp2n := mode_chan_upd Ok (mode_upd Ok sp2 "ord" num0) "s1" []).
  set (sp2d := mode_upd Ok sp2n "dec" (mode_store Ok sp2n "ord" / V10MIL)).
  set (sp2c := mode_upd Ok sp2d "curp" (mode_store Ok sp2d "initp" / 10)).
  set (sp3 := mode_chan_upd Ok sp2c "s1"
                (mode_chan Ok sp2c "s1" ++ [mode_store Ok sp2c "curp"])%list).
  set (sa3 := sa2).
  assert (Hsp2_vch1 : sp2.(vstate).(ch) "s1" = [num0]).
  { unfold sp2. apply vch_get. }
  assert (Hsp2n_ord : mode_store Ok sp2n "ord" = num0).
  { unfold sp2n. rewrite mode_store_mode_chan_upd. apply mode_store_upd_eq. }
  assert (Hsp2d_initp : mode_store Ok sp2d "initp" = initp0).
  { unfold sp2d. rewrite (mode_store_mode_upd_neq Ok sp2n "dec"
               (mode_store Ok sp2n "ord" / V10MIL)%N "initp");
      [ | intro Heq; discriminate Heq ].
    unfold sp2n. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ok sp2 "ord" num0 "initp");
      [ | intro Heq; discriminate Heq ].
    unfold sp2, sp1, sp0. exact Hinitp. }
  assert (Hsp2c_curp : mode_store Ok sp2c "curp" = (initp0 / 10)%N).
  { unfold sp2c. rewrite mode_store_upd_eq, Hsp2d_initp. reflexivity. }
  assert (Phase3 : cds Ok Ad getprice_round ASkip (sp2, sa2) (sp3, sa3)).
  { eapply (derivable2_cds_step Ok Ad getprice_round ASkip sp2 sa2 sp3 sa3).
    2: apply (D2StepL Ok Ad (fun sig => sig = sp2) getprice_round (fun sig => sig = sp3)
               (fun sig => sig = sa2)).
    2: { unfold getprice_round.
         eapply DSeq. { apply (DRead_concrete Ok "s1" "ord" sp2 num0 [] Hsp2_vch1). }
         eapply DSeq. { apply DAssign_concrete. }
         eapply DSeq.
         - unfold curp_branch. apply DChoiceR. eapply DSeq.
           + apply DAssume_concrete.
             change (mode_store Ok sp2d "ord" > V9MIL).
             unfold sp2d.
             rewrite (mode_store_mode_upd_neq Ok sp2n "dec"
                        (mode_store Ok sp2n "ord" / V10MIL)%N "ord");
               [ | intro Heq; discriminate Heq ].
             rewrite Hsp2n_ord. exact Hbig9.
           + apply DAssign_concrete.
         - apply DWrite_concrete. }
    split; reflexivity. }

  (* --- Phase 4: Com program -> adversary delivers [curp = initp0/10] as
     [guess1] (D2Com). --- *)
  assert (Hsp3_vch1 : sp3.(vstate).(ch) "s1" = [(initp0 / 10)%N]).
  { unfold sp3. rewrite vch_get, Hsp2c_curp.
    unfold sp2c. rewrite mode_chan_mode_upd.
    unfold sp2d. rewrite mode_chan_mode_upd.
    unfold sp2n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get. reflexivity. }
  assert (Hsa3_ach1 : sa3.(astate).(ch) "s1" = []).
  { unfold sa3, sa2. apply ach_get. }
  set (sp4 := sp3[[ "s1" :=vch [] ]]).
  set (sa4 := sa3[[ "s1" :=ach ([] ++ [initp0 / 10])%list ]]).
  assert (Phase4 : cds Ok Ad ASkip ASkip (sp3, sa3) (sp4, sa4)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp3 sa3 sp4 sa4).
    2: apply (D2Com Ok Ad (fun sig sig' => sig = sp3 /\ sig' = sa3) ASkip ASkip "s1").
    exists (initp0 / 10)%N, (@nil N), (@nil N). repeat split.
    - unfold sp4. rewrite vch_shadow. apply vch_eq. exact Hsp3_vch1.
    - unfold sa4. rewrite ach_shadow. apply ach_eq. exact Hsa3_ach1. }

  (* --- Phase 5: adversary reads [guess1 = initp0/10], writes [num] to s2
     (D2StepR). --- *)
  set (sp5 := sp4).
  assert (Hsa4_ach1 : sa4.(astate).(ch) "s1" = [(initp0 / 10)%N]).
  { unfold sa4. apply ach_get. }
  set (sa4g := mode_chan_upd Ad (mode_upd Ad sa4 "guess1" (initp0 / 10)) "s1" []).
  assert (Hsa4g_guess1 : mode_store Ad sa4g "guess1" = (initp0 / 10)%N).
  { unfold sa4g. rewrite mode_store_mode_chan_upd. apply mode_store_upd_eq. }
  assert (Hsa4g_num : mode_store Ad sa4g "num" = num0).
  { unfold sa4g. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ad sa4 "guess1" (initp0 / 10)%N "num");
      [ | intro Heq; discriminate Heq ].
    unfold sa4, sa3, sa2, sa1, sa0. exact Hnum. }
  set (sa5 := mode_chan_upd Ad sa4g "s2"
                (mode_chan Ad sa4g "s2" ++ [mode_store Ad sa4g "num"])%list).
  set (ca_tail1 := ASeq (ARead "s1" "guess1") (AWrite "s2" "num")).
  assert (Phase5 : cds Ok Ad ASkip ca_tail1 (sp4, sa4) (sp5, sa5)).
  { eapply (derivable2_cds_step Ok Ad ASkip ca_tail1 sp4 sa4 sp5 sa5).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp4) (fun sig => sig = sa4)
               ca_tail1 (fun sig => sig = sa5)).
    2: { unfold ca_tail1.
         eapply DSeq. { apply (DRead_concrete Ad "s1" "guess1" sa4 (initp0 / 10)%N []
                                  Hsa4_ach1). }
         apply DWrite_concrete. }
    split; reflexivity. }

  (* --- Phase 6: Com adversary -> program delivers [num] on s2 (D2ComAP). --- *)
  assert (Hsa4g_ach2 : mode_chan Ad sa4g "s2" = []).
  { unfold sa4g. rewrite mode_chan_Ad, (ach_neq _ "s1" "s2");
      [ | intro Heq; discriminate Heq ].
    rewrite ach_astore_upd.
    unfold sa4. rewrite (ach_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold sa3, sa2. rewrite (ach_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold sa1, sa0, sp0. exact Ha2. }
  assert (Hsa5_ach2 : sa5.(astate).(ch) "s2" = [num0]).
  { unfold sa5. rewrite ach_get, Hsa4g_num, Hsa4g_ach2. reflexivity. }
  assert (Hsa5_vch2 : sa5.(vstate).(ch) "s2" = []).
  { unfold sa5, sa4g, sa4, sa3, sa2, sa1, sa0, sp0.
    repeat rewrite vch_achan_upd. rewrite vch_astore_upd.
    repeat rewrite vch_achan_upd. exact Hv2. }
  assert (Hsp5_vch2 : sp5.(vstate).(ch) "s2" = []).
  { unfold sp5, sp4. rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold sp3. rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold sp2c. rewrite vch_vstore_upd.
    unfold sp2d. rewrite vch_vstore_upd.
    unfold sp2n. rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    rewrite vch_vstore_upd.
    unfold sp2. rewrite (vch_neq _ "s1" "s2"); [ | intro Heq; discriminate Heq ].
    unfold sp1, sp0. exact Hv2. }
  set (sp6 := sp5[[ "s2" :=vch ([] ++ [num0])%list ]]).
  set (sa6 := sa5[[ "s2" :=ach [] ]]).
  assert (Phase6 : cds Ok Ad ASkip ASkip (sp5, sa5) (sp6, sa6)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp5 sa5 sp6 sa6).
    2: apply (D2ComAP Ok Ad (fun sig sig' => sig = sp5 /\ sig' = sa5) ASkip ASkip "s2").
    exists num0, (@nil N), (@nil N). repeat split.
    - unfold sp6. rewrite vch_shadow. apply vch_eq. exact Hsp5_vch2.
    - unfold sa6. rewrite ach_shadow. apply ach_eq. exact Hsa5_ach2. }

  (* --- Phase 7: program (service 2) reads [ord2 := num0], takes the "large
     order" branch, writes [curp2 = initp0/10] (D2StepL). --- *)
  set (sp6n := mode_chan_upd Ok (mode_upd Ok sp6 "ord2" num0) "s2" []).
  set (sp6d := mode_upd Ok sp6n "dec2" (mode_store Ok sp6n "ord2" / V20MIL)).
  set (sp6c := mode_upd Ok sp6d "curp2" (mode_store Ok sp6d "initp" / 10)).
  set (sp7 := mode_chan_upd Ok sp6c "s2"
                (mode_chan Ok sp6c "s2" ++ [mode_store Ok sp6c "curp2"])%list).
  set (sa7 := sa6).
  assert (Hsp6_vch2 : sp6.(vstate).(ch) "s2" = [num0]).
  { unfold sp6. apply vch_get. }
  assert (Hsp6n_ord2 : mode_store Ok sp6n "ord2" = num0).
  { unfold sp6n. rewrite mode_store_mode_chan_upd. apply mode_store_upd_eq. }
  assert (Hsp6_initp : mode_store Ok sp6 "initp" = initp0).
  { unfold sp6. rewrite mode_store_mode_chan_upd.
    unfold sp5, sp4. rewrite mode_store_mode_chan_upd.
    unfold sp3. rewrite mode_store_mode_chan_upd.
    unfold sp2c. rewrite (mode_store_mode_upd_neq Ok sp2d "curp"
               (mode_store Ok sp2d "initp" / 10)%N "initp");
      [ | intro Heq; discriminate Heq ].
    exact Hsp2d_initp. }
  assert (Hsp6d_initp : mode_store Ok sp6d "initp" = initp0).
  { unfold sp6d. rewrite (mode_store_mode_upd_neq Ok sp6n "dec2"
               (mode_store Ok sp6n "ord2" / V20MIL)%N "initp");
      [ | intro Heq; discriminate Heq ].
    unfold sp6n. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ok sp6 "ord2" num0 "initp");
      [ | intro Heq; discriminate Heq ].
    exact Hsp6_initp. }
  assert (Hsp6c_curp2 : mode_store Ok sp6c "curp2" = (initp0 / 10)%N).
  { unfold sp6c. rewrite mode_store_upd_eq, Hsp6d_initp. reflexivity. }
  assert (Phase7 : cds Ok Ad getprice2_round ASkip (sp6, sa6) (sp7, sa7)).
  { eapply (derivable2_cds_step Ok Ad getprice2_round ASkip sp6 sa6 sp7 sa7).
    2: apply (D2StepL Ok Ad (fun sig => sig = sp6) getprice2_round (fun sig => sig = sp7)
               (fun sig => sig = sa6)).
    2: { unfold getprice2_round.
         eapply DSeq. { apply (DRead_concrete Ok "s2" "ord2" sp6 num0 [] Hsp6_vch2). }
         eapply DSeq. { apply DAssign_concrete. }
         eapply DSeq.
         - unfold curp2_branch. apply DChoiceR. eapply DSeq.
           + apply DAssume_concrete.
             change (mode_store Ok sp6d "ord2" > V18MIL).
             unfold sp6d.
             rewrite (mode_store_mode_upd_neq Ok sp6n "dec2"
                        (mode_store Ok sp6n "ord2" / V20MIL)%N "ord2");
               [ | intro Heq; discriminate Heq ].
             rewrite Hsp6n_ord2. exact Hbig.
           + apply DAssign_concrete.
         - apply DWrite_concrete. }
    split; reflexivity. }

  (* --- Phase 8: Com program -> adversary delivers [curp2 = initp0/10] as
     [guess2] (D2Com). --- *)
  assert (Hsp7_vch2 : sp7.(vstate).(ch) "s2" = [(initp0 / 10)%N]).
  { unfold sp7. rewrite vch_get, Hsp6c_curp2.
    unfold sp6c. rewrite mode_chan_mode_upd.
    unfold sp6d. rewrite mode_chan_mode_upd.
    unfold sp6n. rewrite mode_chan_upd_Ok, mode_chan_Ok, vch_get. reflexivity. }
  assert (Hsa7_ach2 : sa7.(astate).(ch) "s2" = []).
  { unfold sa7, sa6. apply ach_get. }
  set (sp8 := sp7[[ "s2" :=vch [] ]]).
  set (sa8 := sa7[[ "s2" :=ach ([] ++ [initp0 / 10])%list ]]).
  assert (Phase8 : cds Ok Ad ASkip ASkip (sp7, sa7) (sp8, sa8)).
  { eapply (derivable2_cds_step Ok Ad ASkip ASkip sp7 sa7 sp8 sa8).
    2: apply (D2Com Ok Ad (fun sig sig' => sig = sp7 /\ sig' = sa7) ASkip ASkip "s2").
    exists (initp0 / 10)%N, (@nil N), (@nil N). repeat split.
    - unfold sp8. rewrite vch_shadow. apply vch_eq. exact Hsp7_vch2.
    - unfold sa8. rewrite ach_shadow. apply ach_eq. exact Hsa7_ach2. }

  (* --- Phase 9: adversary reads [guess2 = initp0/10]; assertion succeeds
     (D2StepR). --- *)
  set (sp9 := sp8).
  assert (Hsa8_ach2 : sa8.(astate).(ch) "s2" = [(initp0 / 10)%N]).
  { unfold sa8. apply ach_get. }
  set (sa8g := mode_chan_upd Ad (mode_upd Ad sa8 "guess2" (initp0 / 10)) "s2" []).
  assert (Hsa8g_guess2 : mode_store Ad sa8g "guess2" = (initp0 / 10)%N).
  { unfold sa8g. rewrite mode_store_mode_chan_upd. apply mode_store_upd_eq. }
  assert (Hsa8g_guess1 : mode_store Ad sa8g "guess1" = (initp0 / 10)%N).
  { unfold sa8g. rewrite mode_store_mode_chan_upd.
    rewrite (mode_store_mode_upd_neq Ad sa8 "guess2" (initp0 / 10)%N "guess1");
      [ | intro Heq; discriminate Heq ].
    unfold sa8, sa7, sa6. rewrite mode_store_mode_chan_upd.
    unfold sa5. rewrite mode_store_mode_chan_upd.
    exact Hsa4g_guess1. }
  set (ca_tail2 := ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq)).
  assert (Phase9 : cds Ok Ad ASkip ca_tail2 (sp8, sa8) (sp9, sa8g)).
  { eapply (derivable2_cds_step Ok Ad ASkip ca_tail2 sp8 sa8 sp9 sa8g).
    2: apply (D2StepR Ok Ad (fun sig => sig = sp8) (fun sig => sig = sa8)
               ca_tail2 (fun sig => sig = sa8g /\ guess_eq (mode_store Ad sig))).
    2: { unfold ca_tail2.
         eapply DSeq. { apply (DRead_concrete Ad "s2" "guess2" sa8 (initp0 / 10)%N []
                                  Hsa8_ach2). }
         apply DAdvAssertSuccess. }
    split. reflexivity. split. reflexivity.
    unfold guess_eq. rewrite Hsa8g_guess1, Hsa8g_guess2. reflexivity. }

  (* --- Chain all nine phases and conclude. --- *)
  exists sp9, sa8g. split.
  - chain_tac (((((((( Phase1, Phase2), Phase3), Phase4), Phase5), Phase6), Phase7),
                Phase8), Phase9).
  - change (mode_store Ad sa8g "guess1" = mode_store Ad sa8g "guess2").
    rewrite Hsa8g_guess1, Hsa8g_guess2. reflexivity.
Qed.

(** ** Example 3, semi-automated (see AL.automation)

    Same theorem as [eqtest_attack_via_AL], automated the same way as
    [example1_attack_via_AL_auto]/[obt_round_success_via_AL_auto]. *)
Theorem eqtest_attack_via_AL_auto : forall sig0 initp0 num0,
  eqtest_entry sig0 initp0 num0 ->
  attack_reaches_AL Ok Ad sig0 sig0
    (fun sig => sig.(astate).(s) "guess1" = sig.(astate).(s) "guess2").
Proof.
  intros sig0 initp0 num0 (Hinitp & Hnum & Hbig & Hv1 & Ha1 & Hv2 & Ha2).
  unfold attack_reaches_AL.
  assert (Hbig9 : (num0 > V9MIL)%N) by (unfold V9MIL, V18MIL in *; lia).
  assert (Phase1 : cds Ok Ad ASkip (AWrite "s1" "num")
                       (sig0, sig0) (sig0, _)) by stepR_tac.
  match type of Phase1 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase1 ASkip ASkip
        (PreX[[ "s1" :=vch ([] ++ [num0])%list ]])
        (PreY[[ "s1" :=ach [] ]])
        Phase2
  end.
  { comAP_tac "s1". }
  next_pre_L Phase2 getprice_round Phase3. { stepL_tac. }
  match type of Phase3 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase3 ASkip ASkip
        (PreX[[ "s1" :=vch [] ]])
        (PreY[[ "s1" :=ach (mode_chan Ad PreY "s1" ++ [mode_store Ok PreX "curp"])%list ]])
        Phase4
  end.
  { com_tac "s1". }
  next_pre_R Phase4 (ASeq (ARead "s1" "guess1") (AWrite "s2" "num")) Phase5.
  { stepR_tac. }
  match type of Phase5 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase5 ASkip ASkip
        (PreX[[ "s2" :=vch ([] ++ [num0])%list ]])
        (PreY[[ "s2" :=ach [] ]])
        Phase6
  end.
  { comAP_tac "s2". }
  next_pre_L Phase6 getprice2_round Phase7. { stepL_tac. }
  match type of Phase7 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      next_pre_at Phase7 ASkip ASkip
        (PreX[[ "s2" :=vch [] ]])
        (PreY[[ "s2" :=ach (mode_chan Ad PreY "s2" ++ [mode_store Ok PreX "curp2"])%list ]])
        Phase8
  end.
  { com_tac "s2". }

  (* --- Phase 9 is the one phase [stepR_tac] cannot close on its own. ---

     Every other phase's side condition is either about ONE field of ONE
     state ([ret = 0], [res = 1] -- both traced back to a literal the
     program assigned) or pure channel bookkeeping, which [msimpl]'s
     rewrite set normalizes directly.  This assertion instead compares TWO
     fields, [guess1] and [guess2], whose values were produced by two
     SEPARATE service computations several phases apart, so closing it means
     normalizing both sides independently all the way back to
     [sig0.(vstate).(s) "initp" / 10] and only then matching them.  Two
     things block [msimpl] from doing that:

     1. [next_pre_*] names each phase's successor state with an
        [evar]-introduced LOCAL DEFINITION, and [rewrite] treats such a name
        as opaque -- the update-algebra lemmas never see the chain inside it.
        [subst_states] fixes that, but only safely on a goal that is the sole
        remaining one (see its note in [AL.automation]); run as part of the
        generic pipeline it substitutes a local out from under a SIBLING
        goal whose own successor evar still depends on it, breaking phases
        that were previously fine.
     2. Even unfolded, the chain mixes raw [[[ :=v ]]] notation with
        [mode_upd]/[mode_chan_upd] function forms, and the rewrite set does
        not bridge every combination of the two, so it stalls partway.  Plain
        computation ([cbn]) gets through what the rewrites cannot, since all
        the update machinery is definitionally computational -- everything
        except [sig0] itself, which [Hinitp] then relates to [initp0].

     So the two facts are established with [subst_states; msimpl; cbn] plus
     [Hinitp], and the phase is assembled from the rules by hand, exactly as
     [eqtest_attack_via_AL] does. *)
  match type of Phase8 with
  | cds _ _ _ _ _ (?PreX, ?PreY) =>
      assert (Hg1 : mode_store Ad PreY "guess1" = (initp0 / 10)%N);
      [ | assert (Hch2 : mode_chan Ad PreY "s2" = [(initp0 / 10)%N]);
          [ | assert (Phase9 : cds Ok Ad ASkip
                        (ASeq (ARead "s2" "guess2") (AAdvAssert guess_eq))
                        (PreX, PreY)
                        (PreX, mode_chan_upd Ad
                                 (mode_upd Ad PreY "guess2" (initp0 / 10)%N)
                                 "s2" [])) ] ]
  end.
  { subst_states. msimpl. cbn. try rewrite Hinitp. reflexivity. }
  { subst_states. msimpl. cbn. try rewrite Hinitp. reflexivity. }
  { match goal with
    | |- cds ?m1 ?m2 ASkip ?c2 (?X, ?Y) (?X, ?Y2) =>
        eapply (derivable2_cds_step m1 m2 ASkip c2 X Y X Y2);
        [ | eapply (D2StepR m1 m2 (fun sig => sig = X) (fun sig => sig = Y) c2
                      (fun sig => sig = Y2 /\ guess_eq (mode_store Ad sig)));
            eapply DSeq;
            [ apply (DRead_concrete Ad "s2" "guess2" Y (initp0 / 10)%N [] Hch2)
            | apply DAdvAssertSuccess ] ]
    end.
    split. reflexivity. split. reflexivity.
    unfold guess_eq. msimpl. reflexivity. }

  match type of Phase9 with
  | cds _ _ _ _ _ (?sq, ?sb) => exists sq, sb
  end.
  split.
  - chain_tac (((((((( Phase1, Phase2), Phase3), Phase4), Phase5), Phase6), Phase7),
                Phase8), Phase9).
  - solve_side.
Qed.

Close Scope al_scope.