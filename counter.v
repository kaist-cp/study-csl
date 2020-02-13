(* This is slightly modified version of iris/theories/heap_lang/lib/counter.v
   and examples/theories/lecture_notes/coq_intro_example_2.v *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import lib.frac_auth auth.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang lib.par.
From iris.heap_lang Require Import proofmode notation.

Definition newcounter : val := λ: <>, ref #0.
Definition incr : val := rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "incr" "l".
Definition read : val := λ: "l", !"l".

Definition incr2 : val :=
  λ: <>,
     let: "c" := newcounter #() in
     (incr "c" ||| incr "c");;
     read "c".

Section auth_update.
  Context {U : ucmraT}.

  Lemma auth_update_add (x y z : U) :
    ✓ (x ⋅ z) → ● x ⋅ ◯ y ~~> ● (x ⋅ z) ⋅ ◯ (y ⋅ z).
  Proof.
    intros ?.
    apply auth_update.
    intros ? mz ? Heq.
    split.
    - apply cmra_valid_validN; auto.
    - simpl in *.
      rewrite Heq.
      destruct mz; simpl; auto.
      rewrite -assoc (comm _ _ z) assoc //.
  Qed.

  Lemma auth_update_add' (x y z w : U) :
    ✓ (x ⋅ z) → w ≼ z → ● x ⋅ ◯ y ~~> ● (x ⋅ z) ⋅ ◯ (y ⋅ w).
  Proof.
    intros Hv [? He].
    etransitivity.
    apply (auth_update_add x y z Hv).
    rewrite {2}He assoc auth_frag_op assoc.
    apply cmra_update_op_l.
  Qed.
End auth_update.


(** Monotone counter *)
Class mcounterG Σ := MCounterG { mcounter_inG :> inG Σ (authR mnatUR) }.
Definition mcounterΣ : gFunctors := #[GFunctor (authR mnatUR)].

Instance subG_mcounterΣ {Σ} : subG mcounterΣ Σ → mcounterG Σ.
Proof. solve_inG. Qed.

Section mono_proof.
  Context `{!heapG Σ, !mcounterG Σ} (N : namespace).

  Definition mcounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (● (n : mnat)) ∗ l ↦ #n).

  Definition mcounter (γ : gname) (l : loc) : iProp Σ :=
    inv N (mcounter_inv γ l).

  Definition msnapshot (γ : gname) (n : nat) : iProp Σ :=
    own γ (◯ (n : mnat)).

  Global Instance msnapshot_persistent γ n : Persistent (msnapshot γ n).
  Proof. apply _. Qed.

  Lemma mcounterRA_valid_auth_frag (m n : mnatUR): ✓ (● m ⋅ ◯ n) ↔ (n ≤ m)%nat.
  Proof.
    rewrite auth_both_valid.
    split.
    - intros [? _]; by apply mnat_included.
    - intros ?%mnat_included; done.
  Qed.

  Lemma mcounterRA_incr (m n : mnatUR): ● m ⋅ ◯ n ~~> ● (S m : mnatUR) ⋅ ◯ (S n : mnatUR).
  Proof.
    replace (S m) with (m ⋅ (S m)); last auto with arith.
    replace (S n) with (n ⋅ (S n)); last auto with arith.
    apply cmra_update_valid0; intros ?%cmra_discrete_valid%mcounterRA_valid_auth_frag.
    apply auth_update_add'; first reflexivity.
    exists (S m); symmetry; apply max_r; auto with arith.
  Qed.

  Lemma mcounterRA_update_frag (m n : mnatUR):  ● m ⋅ ◯ n ~~> ● m ⋅ ◯ m.
  Proof.
    (* "local update": refer to Iris formal doc Definition 18 *)
    apply auth_update, (mnat_local_update _ _ m); auto.
  Qed.

  Lemma newcounter_mono_spec :
    {{{ True }}} newcounter #() {{{ l, RET #l; ∃ γ, mcounter γ l ∗ msnapshot γ 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    (* You need to read ground-up section 7 to fully understand what wp_fupd does.
       For now, it's sufficient to know that iMod own_alloc fails without wp_fupd. *)
    iApply wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (● (O:mnat) ⋅ ◯ (O:mnat))) as (γ) "[Hauth Hauth']";
      first by apply auth_both_valid.
    iMod (inv_alloc N _ (mcounter_inv γ l) with "[Hl Hauth]").
    { iNext. iExists 0%nat. by iFrame. }
    iModIntro. iApply "HΦ".
    iExists γ. iFrame.
  Qed.

  Lemma incr_mono_spec γ l n :
    {{{ mcounter γ l ∗ msnapshot γ n }}}
      incr #l
    {{{ RET #();  mcounter γ l ∗ msnapshot γ (S n) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". iLöb as "IH". wp_rec.
    iDestruct "Hl" as "[#Hinv Hsnap]". wp_bind (! _)%E.
    iInv N as (c) ">[Hauth Hl]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl Hauth]") as "_".
    { iNext; iExists c; by iFrame. } iModIntro.
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hauth Hl]" "Hclose".
    destruct (decide (c' = c)) as [->|].
    - iDestruct (own_valid_2 with "Hauth Hsnap") as %?%mcounterRA_valid_auth_frag.
      iMod (own_update_2 with "Hauth Hsnap") as "[Hauth Hsnap]".
      { apply mcounterRA_incr. }
      wp_cmpxchg_suc.
      iMod ("Hclose" with "[Hl Hauth]") as "_".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      iModIntro. wp_pures. iApply "HΦ". iSplit; first done.
      by iApply (own_mono with "Hsnap").
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]).
      iMod ("Hclose" with "[Hl Hauth]") as "_".
      { iNext; iExists c'; by iFrame. } iModIntro.
      wp_pures. iApply ("IH" with "[Hsnap] [HΦ]"); last by auto.
      iFrame "# ∗".
  Qed.

  Lemma read_mono_spec γ l j :
    {{{ mcounter γ l ∗ msnapshot γ j }}}
      read #l
    {{{ i, RET #i; ⌜j ≤ i⌝%nat ∧  mcounter γ l ∗ msnapshot γ i }}}.
  Proof.
    iIntros (ϕ) "Hc HΦ". iDestruct "Hc" as "[#Hinv Hsnap]".
    wp_lam.
    iInv N as (c) ">[Hauth Hl]" "Hclose".
    wp_load.
    iDestruct (own_valid_2 with "Hauth Hsnap") as %?%mcounterRA_valid_auth_frag.
    iMod (own_update_2 with "Hauth Hsnap") as "[Hauth Hsnap]".
    { apply mcounterRA_update_frag. }
    iMod ("Hclose" with "[Hl Hauth]") as "_".
    { iNext; iExists c; iFrame. }
    iModIntro. iApply "HΦ". eauto 10.
  Qed.
End mono_proof.

Section mono_client.
  Context `{!heapG Σ, !mcounterG Σ, !spawnG Σ} (N : namespace).
  Lemma incr2_ge_1 :
    {{{ True }}} incr2 #() {{{ v, RET #v; ⌜v ≥ 1⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post". wp_lam.
    wp_apply (newcounter_mono_spec N); first done.
    iIntros (l) "H". iDestruct "H" as (γ) "[#Hinv #Hsnap0]".
    wp_let.
    wp_apply (wp_par (λ _, msnapshot γ 1) (λ _, msnapshot γ 1));
      try (wp_apply (incr_mono_spec with "[$Hinv $Hsnap0]");
             iIntros "[_ ?]"; iFrame).
    iIntros (v1 v2) "[Hsnap1 _]". iNext. wp_seq.
    wp_apply (read_mono_spec with "[$Hinv $Hsnap1]").
    iIntros (i) "(% & _ & Hsnapi)". by iApply "Post".
  Qed.
End mono_client.

(** Counter with contributions *)
Class ccounterG Σ := CCounterG { ccounter_inG :> inG Σ (frac_authR natR) }.
Definition ccounterΣ : gFunctors := #[GFunctor (frac_authR natR)].

Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Section contrib_spec.
  Context `{!heapG Σ, !ccounterG Σ} (N : namespace).

  Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (●F n) ∗ l ↦ #n).

  Definition ccounter (γ : gname) (l : loc) : iProp Σ :=
    inv N (ccounter_inv γ l).

  Definition ccontrib (γ : gname) (q : frac) (n : nat) : iProp Σ :=
    own γ (◯F{q} n).

  Lemma ccontrib_op γ q1 q2 n1 n2 :
    ccontrib γ (q1 + q2) (n1 + n2) ⊣⊢ ccontrib γ q1 n1 ∗ ccontrib γ q2 n2.
  (* rewrite /id = unfold id *)
  Proof. by rewrite /ccontrib frac_auth_frag_op -own_op. Qed.

  Lemma ccontrib_split γ q1 q2 n1 n2 :
    ccontrib γ (q1 + q2) (n1 + n2) -∗ ccontrib γ q1 n1 ∗ ccontrib γ q2 n2.
  Proof. by rewrite ccontrib_op. Qed.

  Lemma ccontrib_merge γ q1 q2 n1 n2 :
    ccontrib γ q1 n1 ∗ ccontrib γ q2 n2 -∗ ccontrib γ (q1 + q2) (n1 + n2).
  Proof. by rewrite ccontrib_op. Qed.

  Lemma ccounterRA_valid (m n : natR) (q : frac) :
    ✓ (●F m ⋅ ◯F{q} n) → (n ≤ m)%nat.
  Proof.
    intros ?. apply nat_included. by apply (frac_auth_included_total q) in H.
  Qed.

  Lemma ccounterRA_valid_full (m n : natR) :
    ✓ (●F m ⋅ ◯F n) → (n = m)%nat.
  Proof.
    by intros ?%frac_auth_agree.
  Qed.

  Lemma ccounterRA_update (m n : natR) (q : frac) :
    (●F m ⋅ ◯F{q} n) ~~> (●F (S m) ⋅ ◯F{q} (S n)).
  Proof.
    apply frac_auth_update, (nat_local_update _ _ (S _) (S _)). lia.
  Qed.

  Lemma newcounter_contrib_spec :
    {{{ True }}}
      newcounter #()
    {{{ γ l, RET #l; ccounter γ l ∗ ccontrib γ 1 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd. wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (●F O%nat ⋅ ◯F 0%nat)) as (γ) "[Hauth Hauth']";
      first by apply auth_both_valid.
    iMod (inv_alloc N _ (ccounter_inv γ l) with "[Hl Hauth]");
      [iNext; iExists 0%nat; by iFrame|].
    iModIntro. iApply "HΦ". auto.
  Qed.

  Lemma incr_contrib_spec γ l q n :
    {{{ ccounter γ l ∗ ccontrib γ q n }}}
      incr #l
    {{{ RET #(); ccontrib γ q (S n) }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hfrag] HΦ". iLöb as "IH".
    wp_rec. wp_bind (! _)%E.
    iInv N as (c) ">[Hauth Hl]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl Hauth]") as "_";
      [iNext; iExists c; by iFrame | iModIntro].
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hauth Hl]" "Hclose".
    destruct (decide (c' = c)) as [->|].
    - iMod (own_update_2 with "Hauth Hfrag") as "[Hauth Hfrag]".
      { apply ccounterRA_update. }
      wp_cmpxchg_suc.
      iMod ("Hclose" with "[Hl Hauth]") as "_".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      iModIntro. wp_pures. by iApply "HΦ".
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]).
      iMod ("Hclose" with "[Hl Hauth]") as "_".
      { iNext. iExists c'. by iFrame. } iModIntro.
      wp_pures. by iApply ("IH" with "[Hfrag] [HΦ]"); auto.
  Qed.

  Lemma read_contrib_spec γ l q n :
    {{{ ccounter γ l ∗ ccontrib γ q n }}}
      read #l
    {{{ c, RET #c; ⌜n ≤ c⌝%nat ∧ ccontrib γ q n }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hfrag] HΦ".
    wp_lam.
    iInv N as (c) ">[Hauth Hl]" "Hclose".
    wp_load.
    iDestruct (own_valid_2 with "Hauth Hfrag") as %?%ccounterRA_valid.
    iMod ("Hclose" with "[Hl Hauth]") as "_";
      [iNext; iExists c; by iFrame | iModIntro].
    iApply "HΦ". auto.
  Qed.

  Lemma read_contrib_spec_1 γ l n :
    {{{ ccounter γ l ∗ ccontrib γ 1 n }}}
      read #l
    {{{ RET #n; ccontrib γ 1 n }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hfrag] HΦ".
    wp_lam.
    iInv N as (c) ">[Hauth Hl]" "Hclose".
    wp_load.
    iDestruct (own_valid_2 with "Hauth Hfrag") as % ->%ccounterRA_valid_full.
    iMod ("Hclose" with "[Hl Hauth]") as "_";
      [iNext; iExists c; by iFrame | iModIntro].
    by iApply "HΦ".
  Qed.
End contrib_spec.

Section contrib_client.
  Context `{!heapG Σ, !ccounterG Σ, !spawnG Σ} (N : namespace).
  Lemma incr2_eq_2 :
    {{{ True }}} incr2 #() {{{ RET #2; True }}}.
  Proof.
    iIntros (Φ) "_ Post". wp_lam.
    wp_apply (newcounter_contrib_spec N); first done.
    iIntros (γ l) "[#Hinv Hfrag]".
    wp_let.
    rewrite <-Qp_half_half.
    iDestruct (ccontrib_split γ (1/2) (1/2) 0 0 with "Hfrag") as "[Hfrag1 Hfrag2]".
    wp_apply (wp_par (λ _, ccontrib γ (1/2) 1) (λ _, ccontrib γ (1/2) 1)
                with "[Hfrag1] [Hfrag2]").
    - wp_apply (incr_contrib_spec with "[$Hinv $Hfrag1]"); auto.
    - wp_apply (incr_contrib_spec with "[$Hinv $Hfrag2]"); auto.
    - iIntros (v1 v2) "[Hfrag1 Hfrag2]". iNext. wp_seq.
      iDestruct (ccontrib_merge with "[$Hfrag1 $Hfrag2]") as "Hfrag". simpl.
      rewrite Qp_half_half.
      wp_apply (read_contrib_spec_1 N γ l 2 with "[$Hinv $Hfrag]").
      iIntros "Hfrag". by iApply "Post".
  Qed.
End contrib_client.
