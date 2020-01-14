(* To compile this file, first follow the build instruction of iris/examples
   repository up to `make build-dep` part. *)
From iris.algebra Require Import cmra agree excl csum.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import proofmode notation lang.
From iris.heap_lang.lib Require Import assert.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.

Definition mk_oneshot : val :=
  λ: <>,
     let: "x" := ref NONE in
     ( λ: "n", CAS "x" NONE (SOME "n"),
       λ: <>,
          let: "y" := !"x" in
          λ: <>,
             match: "y" with
               NONE => #()
             | SOME "n" =>
               match: !"x" with
                 NONE => assert: #false
               | SOME "m" => assert: "n" = "m"
               end
             end
     ).


Section oneshot.
  Definition oneshotR  := csumR (exclR unitR) (agreeR ZO).
  Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
  Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
  Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
  Proof. solve_inG. Qed.

  Context `{oneshotG Σ}.

  Definition token γ := own γ (Cinl (Excl ())).
  Definition msg γ (v: Z) := own γ (Cinr (to_agree v)).

  Lemma new_token : (|==> ∃ γ, token γ)%I.
  Proof. by apply own_alloc. Qed.

  Lemma broadcast (v: Z) γ : token γ ==∗ msg γ v.
  Proof.
    apply own_update. by apply cmra_update_exclusive.
  Qed.

  Lemma msg_not_token γ v :
    msg γ v -∗ token γ -∗ False.
  Proof.
    iIntros "Hs Hp".
    iPoseProof (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.

  Lemma msg_agree γ (v w: Z) :
    msg γ v -∗ msg γ w -∗ ⌜v = w⌝.
  Proof.
    iIntros "Hs1 Hs2".
    iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
    iPureIntro. by apply agree_op_invL'.
  Qed.

  Lemma msg_copy (v: Z) γ : msg γ v ==∗ msg γ v ∗ msg γ v.
  Proof.
    iIntros "#Hmsg". iModIntro. iFrame "#".
  Qed.
End oneshot.

Section proof.
  Context `{!heapG Σ} `{!oneshotG Σ}.
  Context (N : namespace).

  Theorem mk_oneshot_spec :
    {{{ True }}}
      mk_oneshot #()
    {{{ (c : val), RET c; ∀ (v : Z),
        {{{ True }}} (Fst c) #v {{{ w, RET w; ⌜w = #true \/ w = #false⌝ }}} ∗
        {{{ True }}}
          (Snd c) #()
        {{{ f, RET f; {{{ True }}} App f #() {{{ RET #(); True }}} }}}
    }}}.
  Proof.
    iIntros (Φ) "_ Post".
    wp_lam. wp_pures. wp_alloc x as "Hx".
    iMod new_token as (γ) "Htoken".
    iMod (inv_alloc N _
                    ((x ↦ NONEV ∗ token γ) ∨ (∃ (n : Z), x ↦ SOMEV #n ∗ msg γ n))
            with "[Hx Htoken]") as "#HInv".
    { iNext; iLeft; iFrame. }
    wp_pures.
    iApply "Post". iIntros (v). iSplit.
    (* Proof of `tryset` *)
    - iModIntro. iIntros (Φ1) "_ Post". wp_pures. wp_bind (CmpXchg _ _ _).
      iInv N as "[NotSet | Set]" "Hclose".
      + iDestruct "NotSet" as "[Hx Htoken]".
        wp_cmpxchg_suc.
        iMod (broadcast with "Htoken") as "Hmsg".
        iMod ("Hclose" with "[Hx Hmsg]") as "_".
        { iNext; iRight; iExists v; iFrame. }
        iModIntro.
        wp_pures.
        iApply "Post". auto.
      + iDestruct "Set" as (n) "[Hx Hmsg]".
        wp_cmpxchg_fail.
        iMod ("Hclose" with "[Hx Hmsg]") as "_".
        { iNext; iRight; iExists n; iFrame. }
        iModIntro.
        wp_pures.
        iApply "Post". auto.
    (* Proof of `check` *)
    - iModIntro. iIntros (Φ2) "_ Post". wp_pures. wp_bind (! _)%E.
      iInv N as "[NotSet | Set]" "Hclose".
      + iDestruct "NotSet" as "[Hx Htoken]".
        wp_load.
        iMod ("Hclose" with "[Hx Htoken]") as "_".
        { iNext; iLeft; iFrame. }
        iModIntro. wp_pures.
        iApply "Post".
        iModIntro.
        iIntros (?) "_ Post".
        wp_pures.
        by iApply "Post".
      + iDestruct "Set" as (n) "[>Hx >Hmsg]".
        iMod (msg_copy with "Hmsg") as "[Hmsg #HSnapshotmsg]".
        wp_load.
        iMod ("Hclose" with "[Hx Hmsg]") as "_".
        { iNext; iRight; iExists n; iFrame. }
        iModIntro. wp_pures.
        iApply "Post".
        iModIntro.
        iIntros (Φ3) "_ Post".
        wp_pures. wp_bind (! _)%E.
        iInv N as "[NotSet | Set]" "Hclose".
        * iDestruct "NotSet" as "[_ >Htoken]".
          by iDestruct (msg_not_token with "HSnapshotmsg Htoken") as %?.
        * iDestruct "Set" as (m) "[Hx Hmsg]".
          wp_load.
          iDestruct (msg_agree with "HSnapshotmsg Hmsg") as %->.
          iMod ("Hclose" with "[Hx Hmsg]") as "_".
          { iNext; iRight; iExists m; iFrame. }
          iModIntro.
          wp_pures. wp_lam. wp_pures.
          case_bool_decide; [|done]. wp_if. by iApply "Post".
  Qed.
End proof.
