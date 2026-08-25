import Mathlib
import RequestProject.Selling
import RequestProject.TwoThirdsCanonical
import RequestProject.TwoThirdsProp6
import RequestProject.TwoThirdsGlue

/-!
# The descent of Lemma 9

This file formalizes the sequence of transformations that the manuscript performs between
Proposition 6 and the end of the proof of Lemma 9.

## The configuration

The data of the argument is, for a fixed agent with valuation `w`, prices `p` and maximin share
`μ = 3ε` (so that the threshold is `2ε = ρμ` for `ρ = 2/3`):

* a family `bg` of pairwise disjoint *bundles* of goods, each worth at most `μ`; these are the
  parts of an equi-valued MMS partition of the agent, and `J` is the set of bundles still in play;
* a set `Q` of *charged loss events*; the event `b` owns a *witness good* `wit b`, which lies in
  the bundle `bidx b` and is no longer available, and it carries a *credit* `cred b`, bounded both
  by `μ` and by `v̄(wit b) + ε`;
* a number `n₂` of *cheap loss events*, each carrying a credit of only `2ε` (these are the
  manuscript's `ℓ₂` events, whose loss is at most `ρ·MMSᵢ`);
* the number `k` of parts that still have to be built, tied to the rest by `k + n₂ + |Q| = |J|`;
* the accounting invariant

  `|J|·3ε ≤ (value of the available goods of the bundles of J) + (pool) + n₂·2ε + Σ_Q cred`,

  which says that the value lost inside the surviving bundles is covered by the credits of the
  events that are still charged.

## The transformations

Three transformations reduce `|J|`; each of them is an instance of the manuscript's list:

* a bundle carrying **two witness goods** is discarded and the corresponding events are replaced
  by cheap events (`n₂` grows by `|Qⱼ| − 1`); this is "removing redundant loss events";
* a bundle carrying **two large available goods** is turned into a pure acceptable part
  `{d₁, d₂}` and discarded, `k` drops by one; this is "handling pairs of goods from `L′`";
* **two** bundles each carrying a witness good *and* a large available good give one pure
  acceptable part made of their two large goods, and both are discarded; this is
  "mixed `L′` and `f` bundles".

When none of them applies, every surviving bundle holds at most one large available good and at
most one witness, and at most one holds both, so the number of large available goods is at most
`k + n₂ + 1`, while the invariant gives a budget of at least `k·μ + n₂·ε`.  Proposition 6 with
pairing (`exists_canonical_of_large_pairs`) then finishes the job.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G]

section Descent

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

omit [Fintype G] [DecidableEq κ] in
/-- The credits of the events charged to a single bundle are covered by the value that the bundle
has lost, up to `ε` per event. -/
lemma cred_bundle_le (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ}
    (bg : ι → Finset G) (wit : κ → G) (bidx : κ → ι) (cred : κ → ℝ)
    {R : Finset G} {Q : Finset κ}
    (hwit_mem : ∀ b ∈ Q, wit b ∈ bg (bidx b))
    (hcred_wit : ∀ b ∈ Q, cred b ≤ vbar w p (wit b) + ε)
    (hbval : ∀ j, vbarSum w p (bg j) ≤ 3 * ε)
    (hwit_out : ∀ b ∈ Q, wit b ∉ R)
    (hinj : Set.InjOn wit ↑Q) (j : ι) :
    ∑ b ∈ Q.filter (fun b => bidx b = j), cred b
      ≤ (3 * ε - vbarSum w p (bg j ∩ R))
          + ((Q.filter (fun b => bidx b = j)).card : ℝ) * ε := by
  classical
  have hv0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  set F : Finset κ := Q.filter (fun b => bidx b = j) with hF
  have hsub : F.image wit ⊆ bg j \ R := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hg
    have hbQ : b ∈ Q := (Finset.mem_filter.mp hb).1
    have hbj : bidx b = j := (Finset.mem_filter.mp hb).2
    exact Finset.mem_sdiff.mpr ⟨by rw [← hbj]; exact hwit_mem b hbQ, hwit_out b hbQ⟩
  have hinjF : Set.InjOn wit ↑F :=
    hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have h1 : ∑ b ∈ F, vbar w p (wit b) = ∑ g ∈ F.image wit, vbar w p g := by
    rw [Finset.sum_image (fun x hx y hy h => hinjF hx hy h)]
  have h2 : ∑ g ∈ F.image wit, vbar w p g ≤ ∑ g ∈ bg j \ R, vbar w p g :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hv0 g)
  have h3 : (∑ g ∈ bg j \ R, vbar w p g) + (∑ g ∈ bg j ∩ R, vbar w p g)
      = ∑ g ∈ bg j, vbar w p g := by
    rw [add_comm, Finset.sum_inter_add_sum_diff]
  have h4 : ∑ b ∈ F, cred b ≤ ∑ b ∈ F, (vbar w p (wit b) + ε) :=
    Finset.sum_le_sum (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1)
  have h5 : ∑ b ∈ F, (vbar w p (wit b) + ε) = (∑ b ∈ F, vbar w p (wit b)) + (F.card : ℝ) * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h6 := hbval j
  simp only [vbarSum] at h6 ⊢
  rw [h5] at h4
  rw [h1] at h4
  linarith

omit [Fintype G] in
/-- Each of the two goods of a pure part made of two large goods is worth at least `ε`, so the
part is acceptable. -/
lemma pair_acceptable (w p : G → ℝ) {ε : ℝ} {d₁ d₂ : G} (hne : d₁ ≠ d₂)
    (h₁ : ε ≤ vbar w p d₁) (h₂ : ε ≤ vbar w p d₂) :
    2 * ε ≤ vbarSum w p {d₁, d₂} := by
  rw [vbarSum, Finset.sum_pair hne]
  linarith

omit [Fintype G] in
/-- **The counting at the end of the descent.**  When every surviving bundle carries at most one
witness good and at most one large available good, and at most one bundle carries both, the large
available goods are at most `|J| − |Q| + 1` in number. -/
lemma exit_count (bg : ι → Finset G) (hbdisj : ∀ j j', j ≠ j' → Disjoint (bg j) (bg j'))
    (bidx : κ → ι) {J : Finset ι} {Q : Finset κ} {Lset : Finset G}
    (hQJ : ∀ b ∈ Q, bidx b ∈ J)
    (hLJ : ∀ g ∈ Lset, ∃ j ∈ J, g ∈ bg j)
    (h1 : ∀ j ∈ J, (Q.filter (fun b => bidx b = j)).card ≤ 1)
    (h2 : ∀ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card ≤ 1)
    (h3 : (J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
        (Lset.filter (fun g => g ∈ bg j)).Nonempty)).card ≤ 1) :
    Lset.card + Q.card ≤ J.card + 1 := by
  classical
  set Mixset : Finset ι := J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
      (Lset.filter (fun g => g ∈ bg j)).Nonempty) with hMixset
  have hQcard : Q.card = ∑ j ∈ J, (Q.filter (fun b => bidx b = j)).card := by
    have hQeq : Q = J.biUnion (fun j => Q.filter (fun b => bidx b = j)) := by
      ext b
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun hb => ⟨bidx b, hQJ b hb, hb, rfl⟩, fun ⟨_, _, hb, _⟩ => hb⟩
    conv_lhs => rw [hQeq]
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr (fun b hb hb' => absurd ?_ hxy)
    rw [← (Finset.mem_filter.mp hb).2, (Finset.mem_filter.mp hb').2]
  have hLcard : Lset.card = ∑ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card := by
    have hLeq : Lset = J.biUnion (fun j => Lset.filter (fun g => g ∈ bg j)) := by
      ext g
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hg
        obtain ⟨j, hj, hgj⟩ := hLJ g hg
        exact ⟨j, hj, hg, hgj⟩
      · rintro ⟨_, _, hg, _⟩; exact hg
    conv_lhs => rw [hLeq]
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    exact Finset.disjoint_left.mpr (fun g hg hg' =>
      Finset.disjoint_left.mp (hbdisj x y hxy) (Finset.mem_filter.mp hg).2
        (Finset.mem_filter.mp hg').2)
  have hbound : ∀ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card
      + (Q.filter (fun b => bidx b = j)).card ≤ 1 + (if j ∈ Mixset then 1 else 0) := by
    intro j hj
    by_cases hmem : j ∈ Mixset
    · rw [if_pos hmem]
      have := h1 j hj
      have := h2 j hj
      omega
    · rw [if_neg hmem]
      rw [hMixset] at hmem
      have hnot : ¬ ((Q.filter (fun b => bidx b = j)).Nonempty ∧
          (Lset.filter (fun g => g ∈ bg j)).Nonempty) := by
        intro hcon
        exact hmem (Finset.mem_filter.mpr ⟨hj, hcon⟩)
      rcases not_and_or.mp hnot with hcon | hcon
      · have : (Q.filter (fun b => bidx b = j)).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hcon)
        have := h2 j hj
        omega
      · have : (Lset.filter (fun g => g ∈ bg j)).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hcon)
        have := h1 j hj
        omega
  have hMixsub : Mixset ⊆ J := by rw [hMixset]; exact Finset.filter_subset _ _
  have hite : ∑ j ∈ J, (if j ∈ Mixset then 1 else 0) = Mixset.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hMixsub, Finset.card_eq_sum_ones]
  calc Lset.card + Q.card
      = ∑ j ∈ J, ((Lset.filter (fun g => g ∈ bg j)).card
          + (Q.filter (fun b => bidx b = j)).card) := by
        rw [Finset.sum_add_distrib, ← hLcard, ← hQcard]
    _ ≤ ∑ j ∈ J, (1 + (if j ∈ Mixset then 1 else 0)) := Finset.sum_le_sum hbound
    _ = J.card + Mixset.card := by rw [Finset.sum_add_distrib, hite]; simp
    _ ≤ J.card + 1 := by omega

/-- **The descent.**  See the module documentation for the meaning of the configuration.  The
conclusion is that a canonical `k`-partition of the available resources exists. -/
theorem descent (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε)
    (bg : ι → Finset G) (wit : κ → G) (bidx : κ → ι) (cred : κ → ℝ)
    (Sset : Finset G) (D : ℝ) (hD : 0 ≤ D)
    (hSwp : ∀ g ∈ Sset, w g ≤ p g)
    (hbdisj : ∀ j j', j ≠ j' → Disjoint (bg j) (bg j'))
    (hbS : ∀ j, Disjoint Sset (bg j))
    (hbval : ∀ j, vbarSum w p (bg j) ≤ 3 * ε) :
    ∀ (M : ℕ) (R : Finset G) (J : Finset ι) (Q : Finset κ) (k n₂ : ℕ),
      J.card = M →
      Sset ⊆ R →
      (∀ g ∈ R, vbar w p g ≤ 2 * ε) →
      (∀ b ∈ Q, wit b ∈ bg (bidx b)) →
      (∀ b ∈ Q, cred b ≤ 3 * ε) →
      (∀ b ∈ Q, cred b ≤ vbar w p (wit b) + ε) →
      (∀ b ∈ Q, wit b ∉ R) →
      Set.InjOn wit ↑Q →
      (∀ b ∈ Q, bidx b ∈ J) →
      k + n₂ + Q.card = J.card →
      ((J.card : ℝ) * (3 * ε)
        ≤ (∑ j ∈ J, vbarSum w p (bg j ∩ R)) + (∑ g ∈ Sset, p g) + D
            + (n₂ : ℝ) * (2 * ε) + ∑ b ∈ Q, cred b) →
      CanonExists w p (3 * ε) (2 * ε) k R D := by
  classical
  have hv0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro R J Q k n₂ hM hSR hsmall hwit_mem hcred_le hcred_wit hwout hinj hbQ hcount hbud
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0; exact canonExists_zero _ _ _ _ _ _
  -- the large goods that are still available and still lie in a surviving bundle
  set Lset : Finset G := (R ∩ J.biUnion bg).filter (fun g => ε ≤ vbar w p g) with hLset
  set Mix : Finset ι := J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
      (Lset.filter (fun g => g ∈ bg j)).Nonempty) with hMix
  rcases Classical.em (∃ j ∈ J, 2 ≤ (Q.filter (fun b => bidx b = j)).card) with
    hcase1 | hcase1
  · -- **first transformation**: a bundle carrying two witness goods is discarded
    obtain ⟨j, hjJ, hj2⟩ := hcase1
    have hcredj := cred_bundle_le w p hp bg wit bidx cred hwit_mem hcred_wit hbval hwout hinj j
    have hQcard : (Q.filter (fun b => bidx b = j)).card
        + (Q.filter (fun b => ¬ (bidx b = j))).card = Q.card :=
      Finset.card_filter_add_card_filter_not _
    have hsumQ : (∑ b ∈ Q, cred b)
        = (∑ b ∈ Q.filter (fun b => bidx b = j), cred b)
          + ∑ b ∈ Q.filter (fun b => ¬ (bidx b = j)), cred b :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hJcard : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
    have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr ⟨j, hjJ⟩
    have hsumJ : (∑ j' ∈ J, vbarSum w p (bg j' ∩ R))
        = vbarSum w p (bg j ∩ R) + ∑ j' ∈ J.erase j, vbarSum w p (bg j' ∩ R) :=
      (Finset.add_sum_erase _ _ hjJ).symm
    refine ih (J.card - 1) (by omega) R (J.erase j) (Q.filter (fun b => ¬ (bidx b = j))) k
      (n₂ + ((Q.filter (fun b => bidx b = j)).card - 1)) hJcard hSR hsmall
      (fun b hb => hwit_mem b (Finset.mem_filter.mp hb).1)
      (fun b hb => hcred_le b (Finset.mem_filter.mp hb).1)
      (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1)
      (fun b hb => hwout b (Finset.mem_filter.mp hb).1)
      (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))
      (fun b hb => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hb).2,
        hbQ b (Finset.mem_filter.mp hb).1⟩)
      (by rw [hJcard]; omega) ?_
    have hc1 : ((J.erase j).card : ℝ) = (J.card : ℝ) - 1 := by
      rw [hJcard, Nat.cast_sub hJ1]; norm_num
    have hc2 : ((n₂ + ((Q.filter (fun b => bidx b = j)).card - 1) : ℕ) : ℝ)
        = (n₂ : ℝ) + ((Q.filter (fun b => bidx b = j)).card : ℝ) - 1 := by
      have h1 : 1 ≤ (Q.filter (fun b => bidx b = j)).card := by omega
      rw [Nat.cast_add, Nat.cast_sub h1]; push_cast; ring
    have hq2 : (2 : ℝ) ≤ ((Q.filter (fun b => bidx b = j)).card : ℝ) := by exact_mod_cast hj2
    rw [hc1, hc2]
    rw [hsumJ, hsumQ] at hbud
    nlinarith [hcredj, mul_nonneg (by linarith :
      (0:ℝ) ≤ ((Q.filter (fun b => bidx b = j)).card : ℝ) - 2) hε]
  · rcases Classical.em (∃ j ∈ J, 2 ≤ (Lset.filter (fun g => g ∈ bg j)).card) with
      hcase2 | hcase2
    · -- **second transformation**: a bundle carrying two large available goods becomes a part
      obtain ⟨j, hjJ, hj2⟩ := hcase2
      obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ := Finset.one_lt_card.mp
        (by omega : 1 < (Lset.filter (fun g => g ∈ bg j)).card)
      have hd₁L : d₁ ∈ Lset := (Finset.mem_filter.mp hd₁).1
      have hd₂L : d₂ ∈ Lset := (Finset.mem_filter.mp hd₂).1
      have hd₁b : d₁ ∈ bg j := (Finset.mem_filter.mp hd₁).2
      have hd₂b : d₂ ∈ bg j := (Finset.mem_filter.mp hd₂).2
      have hd₁R : d₁ ∈ R := by
        have := (Finset.mem_filter.mp hd₁L).1; exact (Finset.mem_inter.mp this).1
      have hd₂R : d₂ ∈ R := by
        have := (Finset.mem_filter.mp hd₂L).1; exact (Finset.mem_inter.mp this).1
      have hd₁v : ε ≤ vbar w p d₁ := (Finset.mem_filter.mp hd₁L).2
      have hd₂v : ε ≤ vbar w p d₂ := (Finset.mem_filter.mp hd₂L).2
      have hcredj := cred_bundle_le w p hp bg wit bidx cred hwit_mem hcred_wit hbval hwout hinj j
      have hQcard : (Q.filter (fun b => bidx b = j)).card
          + (Q.filter (fun b => ¬ (bidx b = j))).card = Q.card :=
        Finset.card_filter_add_card_filter_not _
      have hsumQ : (∑ b ∈ Q, cred b)
          = (∑ b ∈ Q.filter (fun b => bidx b = j), cred b)
            + ∑ b ∈ Q.filter (fun b => ¬ (bidx b = j)), cred b :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hJcard : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
      have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr ⟨j, hjJ⟩
      have hsumJ : (∑ j' ∈ J, vbarSum w p (bg j' ∩ R))
          = vbarSum w p (bg j ∩ R) + ∑ j' ∈ J.erase j, vbarSum w p (bg j' ∩ R) :=
        (Finset.add_sum_erase _ _ hjJ).symm
      -- the two goods leave the pool with the bundle they came from
      have hdS : ∀ d ∈ bg j, d ∉ Sset := by
        intro d hd hdS
        exact Finset.disjoint_left.mp (hbS j) hdS hd
      have hRsub : R \ ({d₁, d₂} : Finset G) ⊆ R := Finset.sdiff_subset
      have hSR' : Sset ⊆ R \ ({d₁, d₂} : Finset G) := by
        intro x hx
        refine Finset.mem_sdiff.mpr ⟨hSR hx, ?_⟩
        intro hxd
        rcases Finset.mem_insert.mp hxd with h | h
        · rw [h] at hx; exact hdS d₁ hd₁b hx
        · rw [Finset.mem_singleton.mp h] at hx; exact hdS d₂ hd₂b hx
      have hbginter : ∀ j' ∈ J.erase j, bg j' ∩ (R \ ({d₁, d₂} : Finset G)) = bg j' ∩ R := by
        intro j' hj'
        have hjj : j' ≠ j := (Finset.mem_erase.mp hj').1
        have hdisj := hbdisj j' j hjj
        ext x
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, h2, ?_⟩
          rintro (rfl | rfl)
          · exact Finset.disjoint_left.mp hdisj h1 hd₁b
          · exact Finset.disjoint_left.mp hdisj h1 hd₂b
      have hrec := ih (J.card - 1) (by omega) (R \ ({d₁, d₂} : Finset G)) (J.erase j)
        (Q.filter (fun b => ¬ (bidx b = j))) (k - 1)
        (n₂ + (Q.filter (fun b => bidx b = j)).card) hJcard hSR'
        (fun g hg => hsmall g (hRsub hg))
        (fun b hb => hwit_mem b (Finset.mem_filter.mp hb).1)
        (fun b hb => hcred_le b (Finset.mem_filter.mp hb).1)
        (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1)
        (fun b hb => fun hmem => hwout b (Finset.mem_filter.mp hb).1 (hRsub hmem))
        (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))
        (fun b hb => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hb).2,
          hbQ b (Finset.mem_filter.mp hb).1⟩)
        (by rw [hJcard]; omega) ?_
      · have hres := canonical_cons hD hRsub
          (by
            intro x hx
            rcases Finset.mem_insert.mp hx with h | h
            · rw [h]; exact hd₁R
            · rw [Finset.mem_singleton.mp h]; exact hd₂R)
          (Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx))
          (pair_acceptable w p hne hd₁v hd₂v) hrec
        rwa [Nat.sub_add_cancel hk1] at hres
      · rw [Finset.sum_congr rfl (fun j' hj' => congrArg (vbarSum w p) (hbginter j' hj'))]
        have hc1 : ((J.erase j).card : ℝ) = (J.card : ℝ) - 1 := by
          rw [hJcard, Nat.cast_sub hJ1]; push_cast; ring
        have hqq : (0 : ℝ) ≤ ((Q.filter (fun b => bidx b = j)).card : ℝ) := Nat.cast_nonneg _
        rw [hc1]
        push_cast
        rw [hsumJ, hsumQ] at hbud
        nlinarith [hcredj, mul_nonneg hqq hε]
    · rcases Classical.em (2 ≤ Mix.card) with hcase3 | hcase3
      · -- **third transformation**: two mixed bundles give one pure part
        obtain ⟨j₁, hj₁M, j₂, hj₂M, hjne⟩ := Finset.one_lt_card.mp (by omega : 1 < Mix.card)
        have hj₁J : j₁ ∈ J := (Finset.mem_filter.mp hj₁M).1
        have hj₂J : j₂ ∈ J := (Finset.mem_filter.mp hj₂M).1
        obtain ⟨b₁, hb₁⟩ := (Finset.mem_filter.mp hj₁M).2.1
        obtain ⟨d₁, hd₁⟩ := (Finset.mem_filter.mp hj₁M).2.2
        obtain ⟨b₂, hb₂⟩ := (Finset.mem_filter.mp hj₂M).2.1
        obtain ⟨d₂, hd₂⟩ := (Finset.mem_filter.mp hj₂M).2.2
        have hd₁L : d₁ ∈ Lset := (Finset.mem_filter.mp hd₁).1
        have hd₂L : d₂ ∈ Lset := (Finset.mem_filter.mp hd₂).1
        have hd₁b : d₁ ∈ bg j₁ := (Finset.mem_filter.mp hd₁).2
        have hd₂b : d₂ ∈ bg j₂ := (Finset.mem_filter.mp hd₂).2
        have hne : d₁ ≠ d₂ := by
          intro h
          exact Finset.disjoint_left.mp (hbdisj j₁ j₂ hjne) hd₁b (h ▸ hd₂b)
        have hd₁R : d₁ ∈ R := (Finset.mem_inter.mp (Finset.mem_filter.mp hd₁L).1).1
        have hd₂R : d₂ ∈ R := (Finset.mem_inter.mp (Finset.mem_filter.mp hd₂L).1).1
        have hd₁v : ε ≤ vbar w p d₁ := (Finset.mem_filter.mp hd₁L).2
        have hd₂v : ε ≤ vbar w p d₂ := (Finset.mem_filter.mp hd₂L).2
        -- the two bundles and the events charged to them
        have hb₁Q : b₁ ∈ Q := (Finset.mem_filter.mp hb₁).1
        have hb₂Q : b₂ ∈ Q := (Finset.mem_filter.mp hb₂).1
        have hb₂j : bidx b₂ = j₂ := (Finset.mem_filter.mp hb₂).2
        have hq₁ : 1 ≤ (Q.filter (fun b => bidx b = j₁)).card :=
          Finset.card_pos.mpr ⟨b₁, hb₁⟩
        have hb₂mem : b₂ ∈ (Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hb₂Q, by rw [hb₂j]; exact hjne.symm⟩, hb₂j⟩
        have hq₂ : 1 ≤ ((Q.filter (fun b => ¬ (bidx b = j₁))).filter
            (fun b => bidx b = j₂)).card := Finset.card_pos.mpr ⟨b₂, hb₂mem⟩
        have hcred1 := cred_bundle_le w p hp bg wit bidx cred hwit_mem hcred_wit hbval hwout
          hinj j₁
        have hcred2 := cred_bundle_le w p hp bg wit bidx cred
          (R := R) (Q := Q.filter (fun b => ¬ (bidx b = j₁)))
          (fun b hb => hwit_mem b (Finset.mem_filter.mp hb).1)
          (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1) hbval
          (fun b hb => hwout b (Finset.mem_filter.mp hb).1)
          (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)) j₂
        have hQcard1 : (Q.filter (fun b => bidx b = j₁)).card
            + (Q.filter (fun b => ¬ (bidx b = j₁))).card = Q.card :=
          Finset.card_filter_add_card_filter_not _
        have hQcard2 : ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂)).card
            + ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => ¬ (bidx b = j₂))).card
              = (Q.filter (fun b => ¬ (bidx b = j₁))).card :=
          Finset.card_filter_add_card_filter_not _
        have hsumQ1 : (∑ b ∈ Q, cred b)
            = (∑ b ∈ Q.filter (fun b => bidx b = j₁), cred b)
              + ∑ b ∈ Q.filter (fun b => ¬ (bidx b = j₁)), cred b :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hsumQ2 : (∑ b ∈ Q.filter (fun b => ¬ (bidx b = j₁)), cred b)
            = (∑ b ∈ (Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂), cred b)
              + ∑ b ∈ (Q.filter (fun b => ¬ (bidx b = j₁))).filter
                  (fun b => ¬ (bidx b = j₂)), cred b :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hj₂erase : j₂ ∈ J.erase j₁ := Finset.mem_erase.mpr ⟨hjne.symm, hj₂J⟩
        have hJcard1 : (J.erase j₁).card = J.card - 1 := Finset.card_erase_of_mem hj₁J
        have hJcard2 : ((J.erase j₁).erase j₂).card = (J.erase j₁).card - 1 :=
          Finset.card_erase_of_mem hj₂erase
        have hJ2 : 2 ≤ J.card := by
          have : 1 ≤ (J.erase j₁).card := Finset.card_pos.mpr ⟨j₂, hj₂erase⟩
          omega
        have hsumJ1 : (∑ j' ∈ J, vbarSum w p (bg j' ∩ R))
            = vbarSum w p (bg j₁ ∩ R) + ∑ j' ∈ J.erase j₁, vbarSum w p (bg j' ∩ R) :=
          (Finset.add_sum_erase _ _ hj₁J).symm
        have hsumJ2 : (∑ j' ∈ J.erase j₁, vbarSum w p (bg j' ∩ R))
            = vbarSum w p (bg j₂ ∩ R)
              + ∑ j' ∈ (J.erase j₁).erase j₂, vbarSum w p (bg j' ∩ R) :=
          (Finset.add_sum_erase _ _ hj₂erase).symm
        have hRsub : R \ ({d₁, d₂} : Finset G) ⊆ R := Finset.sdiff_subset
        have hSR' : Sset ⊆ R \ ({d₁, d₂} : Finset G) := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨hSR hx, ?_⟩
          intro hxd
          rcases Finset.mem_insert.mp hxd with h | h
          · rw [h] at hx; exact Finset.disjoint_left.mp (hbS j₁) hx hd₁b
          · rw [Finset.mem_singleton.mp h] at hx
            exact Finset.disjoint_left.mp (hbS j₂) hx hd₂b
        have hbginter : ∀ j' ∈ (J.erase j₁).erase j₂,
            bg j' ∩ (R \ ({d₁, d₂} : Finset G)) = bg j' ∩ R := by
          intro j' hj'
          have hjj₂ : j' ≠ j₂ := (Finset.mem_erase.mp hj').1
          have hjj₁ : j' ≠ j₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj').2).1
          ext x
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, h2, ?_⟩
            rintro (rfl | rfl)
            · exact Finset.disjoint_left.mp (hbdisj j' j₁ hjj₁) h1 hd₁b
            · exact Finset.disjoint_left.mp (hbdisj j' j₂ hjj₂) h1 hd₂b
        have hrec := ih ((J.erase j₁).erase j₂).card (by omega)
          (R \ ({d₁, d₂} : Finset G)) ((J.erase j₁).erase j₂)
          ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => ¬ (bidx b = j₂))) (k - 1)
          (n₂ + ((Q.filter (fun b => bidx b = j₁)).card
            + ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂)).card - 1))
          rfl hSR' (fun g hg => hsmall g (hRsub hg))
          (fun b hb => hwit_mem b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1)
          (fun b hb => hcred_le b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1)
          (fun b hb => hcred_wit b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1)
          (fun b hb hmem => hwout b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
            (hRsub hmem))
          (hinj.mono (by
            intro x hx
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1))
          (fun b hb => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hb).2,
            Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2,
              hbQ b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1⟩⟩)
          (by omega) ?_
        · have hres := canonical_cons hD hRsub
            (by
              intro x hx
              rcases Finset.mem_insert.mp hx with h | h
              · rw [h]; exact hd₁R
              · rw [Finset.mem_singleton.mp h]; exact hd₂R)
            (Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx))
            (pair_acceptable w p hne hd₁v hd₂v) hrec
          rwa [Nat.sub_add_cancel hk1] at hres
        · rw [Finset.sum_congr rfl (fun j' hj' => congrArg (vbarSum w p) (hbginter j' hj'))]
          have hc1 : (((J.erase j₁).erase j₂).card : ℝ) = (J.card : ℝ) - 2 := by
            have : ((J.erase j₁).erase j₂).card = J.card - 2 := by omega
            rw [this, Nat.cast_sub (by omega : 2 ≤ J.card)]; push_cast; ring
          have hc2 : ((n₂ + ((Q.filter (fun b => bidx b = j₁)).card
                + ((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                    (fun b => bidx b = j₂)).card - 1) : ℕ) : ℝ)
              = (n₂ : ℝ) + (((Q.filter (fun b => bidx b = j₁)).card : ℝ)
                + (((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                    (fun b => bidx b = j₂)).card : ℝ)) - 1 := by
            rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
          have hqq : (2 : ℝ) ≤ ((Q.filter (fun b => bidx b = j₁)).card : ℝ)
              + (((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂)).card : ℝ) := by
            have h1 : (1 : ℝ) ≤ ((Q.filter (fun b => bidx b = j₁)).card : ℝ) := by
              exact_mod_cast hq₁
            have h2 : (1 : ℝ) ≤ (((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                (fun b => bidx b = j₂)).card : ℝ) := by exact_mod_cast hq₂
            linarith
          rw [hc1, hc2]
          rw [hsumJ1, hsumJ2, hsumQ1, hsumQ2] at hbud
          nlinarith [hcred1, hcred2, mul_nonneg (by linarith :
            (0:ℝ) ≤ ((Q.filter (fun b => bidx b = j₁)).card : ℝ)
              + (((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                  (fun b => bidx b = j₂)).card : ℝ) - 2) hε]
      · -- **exit**: Proposition 6 applies
        push_neg at hcase1 hcase2
        haveI : NeZero k := ⟨by omega⟩
        have hLsub : Lset ⊆ R ∩ J.biUnion bg := by rw [hLset]; exact Finset.filter_subset _ _
        have hBunR : R ∩ J.biUnion bg ⊆ R := Finset.inter_subset_left
        have hSBun : Disjoint Sset (R ∩ J.biUnion bg) := by
          refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx').2
          exact Finset.disjoint_left.mp (hbS j) hx hj
        have hvS : ∀ g ∈ Sset, vbar w p g = p g := fun g hg => max_eq_left (hSwp g hg)
        -- the counting
        have hcount' : Lset.card + Q.card ≤ J.card + 1 := by
          refine exit_count bg hbdisj bidx hbQ ?_ ?_ ?_ (by rw [← hMix]; omega)
          · intro g hg
            have := Finset.mem_inter.mp (hLsub hg)
            obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp this.2
            exact ⟨j, hj, hgj⟩
          · intro j hj
            by_contra hcon
            exact absurd (by omega : 2 ≤ (Q.filter (fun b => bidx b = j)).card) (by
              have := hcase1 j hj; omega)
          · intro j hj
            by_contra hcon
            exact absurd (by omega : 2 ≤ (Lset.filter (fun g => g ∈ bg j)).card) (by
              have := hcase2 j hj; omega)
        have hLk : Lset.card ≤ k + (n₂ + 1) := by omega
        -- the resources handed to Proposition 6
        set Ssel : Finset G := Sset.filter (fun g => ε ≤ p g) with hSsel
        set Scheap : Finset G := Sset.filter (fun g => ¬ (ε ≤ p g)) with hScheap
        set Cset : Finset G := ((R ∩ J.biUnion bg) \ Lset) ∪ Scheap with hCset
        have hCdisj : Disjoint ((R ∩ J.biUnion bg) \ Lset) Scheap :=
          Finset.disjoint_left.mpr (fun x hx hx' =>
            Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp hx').1
              (Finset.mem_sdiff.mp hx).1)
        have hAC : Disjoint Lset Cset := by
          refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          rcases Finset.mem_union.mp hx' with h | h
          · exact (Finset.mem_sdiff.mp h).2 hx
          · exact Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp h).1 (hLsub hx)
        have hAS : Disjoint Lset Ssel :=
          Finset.disjoint_left.mpr (fun x hx hx' =>
            Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp hx').1 (hLsub hx))
        have hCS : Disjoint Cset Ssel := by
          refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          rcases Finset.mem_union.mp hx with h | h
          · exact Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp hx').1
              (Finset.mem_sdiff.mp h).1
          · exact (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hx').2
        have hRsub'' : Lset ∪ Cset ∪ Ssel ⊆ R := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact hBunR (hLsub hx)
            · rcases Finset.mem_union.mp hx with hx | hx
              · exact hBunR (Finset.mem_sdiff.mp hx).1
              · exact hSR (Finset.mem_filter.mp hx).1
          · exact hSR (Finset.mem_filter.mp hx).1
        -- the value at our disposal
        have hBunsum : (∑ g ∈ R ∩ J.biUnion bg, vbar w p g)
            = ∑ j ∈ J, vbarSum w p (bg j ∩ R) := by
          have hBeq : R ∩ J.biUnion bg = J.biUnion (fun j => bg j ∩ R) := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_biUnion]
            constructor
            · rintro ⟨hxR, j, hj, hxj⟩; exact ⟨j, hj, hxj, hxR⟩
            · rintro ⟨j, hj, hxj, hxR⟩; exact ⟨hxR, j, hj, hxj⟩
          rw [hBeq, Finset.sum_biUnion]
          · rfl
          · intro x _ y _ hxy
            exact Finset.disjoint_of_subset_left Finset.inter_subset_left
              (Finset.disjoint_of_subset_right Finset.inter_subset_left (hbdisj x y hxy))
        have hsplitL : (∑ g ∈ (R ∩ J.biUnion bg) \ Lset, vbar w p g)
            + (∑ g ∈ Lset, vbar w p g) = ∑ g ∈ R ∩ J.biUnion bg, vbar w p g :=
          Finset.sum_sdiff hLsub
        have hCsum : (∑ g ∈ Cset, vbar w p g)
            = (∑ g ∈ (R ∩ J.biUnion bg) \ Lset, vbar w p g) + ∑ g ∈ Scheap, vbar w p g := by
          rw [hCset, Finset.sum_union hCdisj]
        have hScheapv : (∑ g ∈ Scheap, vbar w p g) = ∑ g ∈ Scheap, p g :=
          Finset.sum_congr rfl (fun g hg => hvS g (Finset.mem_filter.mp hg).1)
        have hSsum : (∑ g ∈ Ssel, p g) + (∑ g ∈ Scheap, p g) = ∑ g ∈ Sset, p g :=
          Finset.sum_filter_add_sum_filter_not _ _ _
        -- the budget available to Proposition 6
        have hcredsum : (∑ b ∈ Q, cred b) ≤ (Q.card : ℝ) * (3 * ε) := by
          calc (∑ b ∈ Q, cred b) ≤ ∑ _b ∈ Q, (3 * ε) := Finset.sum_le_sum (fun b hb => hcred_le b hb)
            _ = (Q.card : ℝ) * (3 * ε) := by rw [Finset.sum_const, nsmul_eq_mul]
        have hcast : (J.card : ℝ) = (k : ℝ) + (n₂ : ℝ) + (Q.card : ℝ) := by
          rw [← hcount]; push_cast; ring
        have hbudP : ((k : ℝ)) * (3 * ε) + (n₂ : ℝ) * ε
            ≤ (∑ g ∈ Lset, vbar w p g) + (∑ g ∈ Cset, vbar w p g) + D + ∑ g ∈ Ssel, p g := by
          rw [hCsum, hScheapv]
          rw [hcast] at hbud
          have h1 : (∑ g ∈ R ∩ J.biUnion bg, vbar w p g) = ∑ j ∈ J, vbarSum w p (bg j ∩ R) :=
            hBunsum
          nlinarith [hbud, hcredsum, hsplitL, hSsum, h1]
        have htle : (Lset.card - k : ℕ) ≤ n₂ + 1 := by omega
        have htler : ((Lset.card - k : ℕ) : ℝ) ≤ (n₂ : ℝ) + 1 := by exact_mod_cast htle
        have hmain := exists_canonical_of_large_pairs w p hp (μ := 3 * ε) (by linarith)
          (k := k) (R := Lset ∪ Cset ∪ Ssel) (D := D) hD (A := Lset) (C := Cset) (S := Ssel)
          rfl hAC hAS hCS
          (by
            intro g hg
            have := (Finset.mem_filter.mp (hLset ▸ hg : g ∈ (R ∩ J.biUnion bg).filter
              (fun g => ε ≤ vbar w p g))).2
            linarith)
          (by
            intro g hg
            have := hsmall g (hRsub'' hg)
            linarith)
          (by
            intro g hg
            rcases Finset.mem_union.mp hg with h | h
            · have hgB : g ∈ R ∩ J.biUnion bg := (Finset.mem_sdiff.mp h).1
              have hgL : g ∉ Lset := (Finset.mem_sdiff.mp h).2
              have : ¬ (ε ≤ vbar w p g) := by
                intro hcon
                exact hgL (by rw [hLset]; exact Finset.mem_filter.mpr ⟨hgB, hcon⟩)
              push_neg at this
              linarith
            · have h1 : ¬ (ε ≤ p g) := (Finset.mem_filter.mp h).2
              have h2 : vbar w p g = p g := hvS g (Finset.mem_filter.mp h).1
              push_neg at h1
              rw [h2]; linarith)
          (by
            intro g hg
            have := (Finset.mem_filter.mp hg).2
            linarith)
          (fun g hg => hSwp g (Finset.mem_filter.mp hg).1)
          (t := Lset.card - k) (by omega)
          (by
            have h3 : (3 : ℝ) * ε / 3 = ε := by ring
            rw [h3]
            have h4 : (2 : ℝ) * (3 * ε) / 3 = 2 * ε := by ring
            rw [h4]
            nlinarith [hbudP, htler, hε])
        have heq : (2 : ℝ) * (3 * ε) / 3 = 2 * ε := by ring
        rw [heq] at hmain
        exact (canonExists_of_nonempty hmain).mono hRsub'' le_rfl

end Descent

end FairSelling
