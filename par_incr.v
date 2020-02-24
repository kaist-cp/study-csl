From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl frac.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang lib.par lib.increment.
From iris.heap_lang Require Import proofmode notation.

Section store_atomic.
  Context `{!heapG Σ}.

  Lemma store_atomic_spec (l : loc) (v' : val) :
    <<< ∀ (v : val), l ↦ v >>> #l <- v' @ ⊤ <<< l ↦ v', RET #() >>>.
  Proof.
    iIntros (Φ) "AU".
    iMod "AU" as (v) "[Hl AbortorCommit]".
    iDestruct "AbortorCommit" as "[_ Commit]".
    wp_store.
    iMod ("Commit" with "Hl") as "HΦ". done.
  Qed.

  Lemma seq_from_atomic (v v' : val) (l : loc) :
    {{{ l ↦ v }}} (λ: "l", "l" <- v') #l {{{ RET #(); l ↦ v' }}}.
  Proof.
    iIntros (Φ) "Hl Post". wp_let.
    (* leave out non-laterable preconditions with [without] *)
    awp_apply store_atomic_spec without "Post".
    (* Logically atomic triples are basically [AU_{P,Q}(Φ) -∗ WP e {Φ}].
       So we need to prove the AU to use them. *)
    iAaccIntro with "Hl".
    - iIntros "Hl !>". iExact "Hl". (* abort case (return the precondition Hl) *)
    - (* commit and proceed *)
      iIntros "Hl !> Post". iApply ("Post" with "Hl").
  Qed.

  (* Lemma seq_from_atomic' (v v' : val) (l : loc) : *)
  (*   {{{ l ↦ v }}} (λ: "l", "l" <- v') #l {{{ RET #(); l ↦ v' }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "Hl Post". wp_let. *)
  (*   wp_apply (atomic_wp_seq $! (store_atomic_spec _ _) with "Hl"). *)
  (*   done. *)
  (* Qed. *)

End store_atomic.

Section incr.
  Context `{!heapG Σ}.

  Definition incr : val :=
    rec: "incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then "oldv"
         else "incr" "l".

  Lemma incr_spec (l: loc) :
    <<< ∀ (v : Z), l ↦ #v >>> incr #l @ ⊤ <<< l ↦ #(v + 1), RET #v >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam. wp_bind (!_)%E.

    (* Peek at the resource and return (abort). *)
    iMod "AU" as (v) "[Hl [Abort _]]".
    wp_load.
    iMod ("Abort" with "Hl") as "AU". iModIntro.

    wp_pures. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as (w) "[Hl AbortOrCommit]".
    destruct (decide (#v = #w)) as [[= ->]|Hx].
    - wp_cmpxchg_suc.
      iDestruct "AbortOrCommit" as "[_ Commit]".
      iMod ("Commit" with "Hl") as "HΦ".
      iModIntro. wp_pures. done.
    - wp_cmpxchg_fail.
      iDestruct "AbortOrCommit" as "[Abort _]".
      iMod ("Abort" with "Hl") as "AU".
      iModIntro. wp_pures. by iApply "IH".
  Qed.
End incr.

Section increment_client.
  Context `{!heapG Σ, !spawnG Σ, !(inG Σ (exclR unitR)), !(inG Σ fracR)}.

  (* Instead of gset_disj, we use two (Excl ())'s in two ghost locations for
     convenience. *)
  Definition receipt γ : iProp Σ := own γ (Excl ()).
  Lemma new_recept : (|==> ∃ γ, receipt γ)%I.
  Proof. by apply own_alloc. Qed.

  Definition coin γ (q : Qp) := own γ q.
  Lemma new_coin : (|==> ∃ γ, coin γ 1)%I.
  Proof. by apply own_alloc. Qed.

  Definition incr_inv γ0 γ1 γ l : iProp Σ :=
    (l ↦ #0 ∗ receipt γ0 ∗ receipt γ1) ∨
    (l ↦ #1 ∗ receipt γ1 ∗ coin γ (1 / 2)) ∨
    (l ↦ #2 ∗ coin γ 1).

  Lemma incr_thread γ0 γ1 γ l :
    inv nroot (incr_inv γ0 γ1 γ l) -∗ coin γ (1 / 2)%Qp -∗
        WP incr #l {{ v, (⌜v = #0⌝ ∗ receipt γ0) ∨
                         (⌜v = #1⌝ ∗ receipt γ1)}}.
  Proof.
    iIntros "#Hinv Hc".
    awp_apply incr_spec.
    (* "Hclose" doesn't work here. TODO: why? *)
    iInv nroot as ">[[Hl [Hr0 Hr1]] | [(Hl & Hr1 & Hc') | [Hl Hc']]]".
    - iAaccIntro with "Hl"; iIntros "Hl !>".
      + iSplitR "Hc"; [|iApply "Hc"]. iModIntro. iLeft. iFrame.
      + iSplitR "Hr0".
        { iModIntro. iRight; iLeft. iFrame. }
        iLeft. by iFrame.
    - iAaccIntro with "Hl"; iIntros "Hl !>".
      + iSplitR "Hc"; [|iApply "Hc"]. iModIntro. iRight; iLeft. iFrame.
      + iSplitR "Hr1".
        { iModIntro. iRight; iRight.
          iDestruct (own_op γ (1/2)%Qp (1/2)%Qp with "[Hc Hc']") as "?"; first iFrame.
          rewrite frac_op' Qp_half_half. iFrame. }
        iRight. by iFrame.
    - iDestruct (own_valid_2 γ with "Hc' Hc") as %H.
      rewrite frac_op' in H. rewrite ->frac_valid' in H. (* NOTE: https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#compatibility-issues *)
      by apply Qp_not_plus_q_ge_1 in H.
  Qed.

  Lemma incr2_spec :
    {{{ True }}}
       let: "l" := ref #0 in incr "l" ||| incr "l"
    {{{ v, RET v; ⌜v = (#0, #1)%V ∨ v = (#1, #0)%V⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    wp_alloc l as "Hl". wp_pures.
    iMod new_recept as (γ0) "Hr0".
    iMod new_recept as (γ1) "Hr1".
    iMod new_coin as (γ) "[Hc1 Hc2]".
    iMod (inv_alloc nroot _ (incr_inv γ0 γ1 γ l) with "[Hl Hr0 Hr1]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    wp_apply (wp_par with "[Hc1] [Hc2]").
    - iApply (incr_thread with "Hinv Hc1").
    - iApply (incr_thread with "Hinv Hc2").
    - iIntros (v1 v2) "[[[% Hl0]|[% Hl1]] [[% Hr0]|[% Hr1]]] !>"; iApply "Post".
      + iDestruct (own_valid_2 with "Hl0 Hr0") as %[].
      + iLeft. by simplify_eq.
      + iRight. by simplify_eq.
      + iDestruct (own_valid_2 with "Hl1 Hr1") as %[].
  Qed.

  Lemma incr2_eq_2 :
    {{{ True }}}
       let: "l" := ref #0 in (incr "l" ||| incr "l");; !"l"
    {{{ RET #2; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    wp_alloc l as "Hl". wp_pures.
    iMod new_recept as (γ0) "Hr0".
    iMod new_recept as (γ1) "Hr1".
    iMod new_coin as (γ) "[Hc1 Hc2]".
    iMod (inv_alloc nroot _ (incr_inv γ0 γ1 γ l) with "[Hl Hr0 Hr1]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    wp_apply (wp_par with "[Hc1] [Hc2]").
    - iApply (incr_thread with "Hinv Hc1").
    - iApply (incr_thread with "Hinv Hc2").
    - iIntros (v1 v2) "[[[_ Hl0]|[_ Hl1]] [[_ Hr0]|[_ Hr1]]] !>"; wp_seq.
      + iDestruct (own_valid_2 with "Hl0 Hr0") as %[].
      + iInv nroot as ">[[Hl [Hr0 Hr1']] | [(Hl & Hr1' & Hc) | [Hl Hc]]]" "Hclose".
        * iDestruct (own_valid_2 with "Hl0 Hr0") as %[].
        * iDestruct (own_valid_2 with "Hr1 Hr1'") as %[].
        * wp_load. iMod ("Hclose" with "[Hl Hc]") as "_".
          { iNext. iRight. iRight. iFrame. }
          iModIntro. by iApply "Post".
      + iInv nroot as ">[[Hl [Hr0' Hr1]] | [(Hl & Hr1 & Hc) | [Hl Hc]]]" "Hclose".
        * iDestruct (own_valid_2 with "Hr0 Hr0'") as %[].
        * iDestruct (own_valid_2 with "Hl1 Hr1") as %[].
        * wp_load. iMod ("Hclose" with "[Hl Hc]") as "_".
          { iNext. iRight. iRight. iFrame. }
          iModIntro. by iApply "Post".
      + iDestruct (own_valid_2 with "Hl1 Hr1") as %[].
  Qed.
End increment_client.
(* TODO: derive ccounter *)
