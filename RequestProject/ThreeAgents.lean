import Mathlib
import RequestProject.SmallN
import RequestProject.TwoAgents
import RequestProject.MMSPartition

/-!
# A `3/4`-MMS allocation for three agents

This file works towards the manuscript's Theorem 3 for the case `n = 3`: for three agents with
additive non-negative valuations and market prices, there is a valid outcome giving *every*
agent at least `3/4` of its maximin-share-with-selling.

## Strategy

The heart of the paper's `n = 3` argument is a *reduction to two agents*: one agent `a` is given
a bundle worth at least `3/4 · MMS_a`, and the remaining goods can be split by the two other
agents so that each of them can (on the remaining goods alone) still guarantee itself
`3/4 · MMS_i`.  Once such a reduction is available, the two-agent existence theorem
(`exists_MMS_two`) finishes the job.

This module proves the reduction plumbing and Main Lemma (2).  The final allocation/matching
assembly is in `RequestProject.ThreeAgentReduction`, after the canonical-partition and matching
modules are available without an import cycle.

## What is proved here

The declarations in this module are fully proved (no `sorry`), using only the standard axioms:

* `compose_three` / `finish_from_reduction` : the reduction plumbing turning the served agent's
  bundle plus a two-agent outcome on the remaining goods into a valid three-agent outcome, and
  invoking `exists_MMS_two` on the restricted sub-instance.
* `three_MMS_le_vbarSum_univ` : the total `v-bar`-value of all goods is at least `3 * MMS` (the
  value-counting inequality underlying the whole argument).
* `bagfill` : the bag-filling lemma (a sub-bundle of prescribed total weight exists when no item
  is too large).
* `restricted_MMS2_ge`, `restricted_MMS2_ge_of_slack`, `pure_reduction` : the two-agent
  guarantee obtained by splitting the remaining goods into two bundles.
* `untouched_mms_part_reduction` : the manuscript's `ℓ₁` case, preserving two MMS parts.
* `paired_loss_bagfill_reduction` : the numerical bag-filling core of `ℓ₃`/`ℓ₄`.
* `main_lemma_two` : Main Lemma (2), assembled from explicit loss certificates.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Restrict a real-valued good-function to a set `R` of goods, zeroing it outside `R`.
Used to phrase the two-agent sub-instance living on the goods that remain after one agent has
been served. -/
def restrictVal (R : Finset G) (w : G → ℝ) : G → ℝ := fun g => if g ∈ R then w g else 0

omit [Fintype G] in
@[simp] lemma restrictVal_mem (R : Finset G) (w : G → ℝ) {g : G} (hg : g ∈ R) :
    restrictVal R w g = w g := by simp [restrictVal, hg]

omit [Fintype G] in
lemma restrictVal_nonneg (R : Finset G) {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    0 ≤ restrictVal R w g := by
  unfold restrictVal; split <;> [exact hw g; rfl]

omit [Fintype G] in
/-- Summing a restricted function over a set is summing the original over the intersection. -/
lemma sum_restrictVal (R : Finset G) (w : G → ℝ) (s : Finset G) :
    ∑ g ∈ s, restrictVal R w g = ∑ g ∈ s ∩ R, w g := by
  classical
  unfold restrictVal
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]

omit [Fintype G] [DecidableEq G] in
/-- Three distinct elements of `Fin 3` exhaust `Fin 3`. -/
lemma fin3_cover {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 3) :
    i = a ∨ i = b ∨ i = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all

/-- Summing over `Fin 3` in terms of three distinct indices. -/
lemma fin3_sum {M : Type*} [AddCommMonoid M] {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Fin 3 → M) :
    ∑ i, f i = f a + f b + f c := by
  have h3 : ({a, b, c} : Finset (Fin 3)) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
    exact fin3_cover hab hac hbc x
  rw [← h3, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

/-- **Composition lemma.** Suppose agent `a` receives a bundle `Ka` (goods handed in full,
valued via `v̄`) plus force-sale money `ma` (backed by the proceeds of a disjoint sold set
`Sa`), worth at least `3/4 · MMS_a`.  Let `R` be the remaining goods.  If a valid two-agent
outcome on the *restricted* instance over `R` gives its two parts at least `3/4 · MMS_b` and
`3/4 · MMS_c` (measured with the restricted valuations), then there is a valid three-agent
outcome giving every agent at least `3/4` of its maximin share. -/
lemma compose_three (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ka Sa : Finset G) (ma : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hmaS : ma ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome G 2)
    (ho2 : o2.Valid (restrictVal (Finset.univ \ (Ka ∪ Sa)) p))
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hc : (3/4 : ℝ) * MMS 3 (v c) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v c)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  set R : Finset G := Finset.univ \ (Ka ∪ Sa) with hR
  obtain ⟨ho2_sold, ho2_disj, ho2_money, ho2_budget⟩ := ho2
  -- Disjointness of `Ka` and `Sa` with the remaining goods `R`.
  have hKaR : Disjoint Ka R := by
    rw [hR]
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxR
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_left _ hx)
  have hSaR : Disjoint Sa R := by
    rw [hR]
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxR
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_right _ hx)
  -- The three groups handed out in full.
  set Avec : Fin 3 → Finset G :=
    fun i => if i = a then Ka else if i = b then o2.kept 0 ∩ R else o2.kept 1 ∩ R with hAvec
  set F : Finset G := Sa ∪ (o2.sold ∩ R) with hF
  set q : Fin 3 → ℝ :=
    fun i => if i = a then ma else if i = b then o2.money 0 else o2.money 1 with hq
  -- Evaluations of `Avec` and `q`.
  have hAveca : Avec a = Ka := by simp [hAvec]
  have hAvecb : Avec b = o2.kept 0 ∩ R := by simp [hAvec, (Ne.symm hab)]
  have hAvecc : Avec c = o2.kept 1 ∩ R := by simp [hAvec, (Ne.symm hac), (Ne.symm hbc)]
  have hqa : q a = ma := by simp [hq]
  have hqb : q b = o2.money 0 := by simp [hq, (Ne.symm hab)]
  have hqc : q c = o2.money 1 := by simp [hq, (Ne.symm hac), (Ne.symm hbc)]
  refine ⟨unifiedOutcome v p Avec F q, ?_, ?_⟩
  · -- Validity.
    apply unifiedOutcome_valid v p hp Avec F q
    · -- pairwise disjoint groups
      intro i j hij
      rcases fin3_cover hab hac hbc i with hi | hi | hi <;>
        rcases fin3_cover hab hac hbc j with hj | hj | hj <;>
        subst hi <;> subst hj <;> first
          | exact absurd rfl hij
          | (rw [hAveca, hAvecb]; exact (hKaR.mono_right Finset.inter_subset_right))
          | (rw [hAveca, hAvecc]; exact (hKaR.mono_right Finset.inter_subset_right))
          | (rw [hAvecb, hAveca];
             exact ((hKaR.mono_right Finset.inter_subset_right).symm))
          | (rw [hAvecc, hAveca];
             exact ((hKaR.mono_right Finset.inter_subset_right).symm))
          | (rw [hAvecb, hAvecc];
             exact ((ho2_disj 0 1 (by decide)).mono
               Finset.inter_subset_left Finset.inter_subset_left))
          | (rw [hAvecc, hAvecb];
             exact ((ho2_disj 1 0 (by decide)).mono
               Finset.inter_subset_left Finset.inter_subset_left))
    · -- `F` disjoint from each group
      intro i
      rw [hF, Finset.disjoint_union_left]
      rcases fin3_cover hab hac hbc i with hi | hi | hi <;> subst hi
      · rw [hAveca]
        exact ⟨hKSa.symm, (hKaR.mono_right Finset.inter_subset_right).symm⟩
      · rw [hAvecb]
        refine ⟨hSaR.mono_right Finset.inter_subset_right, ?_⟩
        exact ((ho2_sold 0).mono Finset.inter_subset_left Finset.inter_subset_left)
      · rw [hAvecc]
        refine ⟨hSaR.mono_right Finset.inter_subset_right, ?_⟩
        exact ((ho2_sold 1).mono Finset.inter_subset_left Finset.inter_subset_left)
    · -- nonnegative money
      intro i
      rcases fin3_cover hab hac hbc i with hi | hi | hi <;> subst hi
      · rw [hqa]; exact hma0
      · rw [hqb]; exact ho2_money 0
      · rw [hqc]; exact ho2_money 1
    · -- budget
      rw [fin3_sum hab hac hbc q, hqa, hqb, hqc]
      have hFdisj : Disjoint Sa (o2.sold ∩ R) := hSaR.mono_right Finset.inter_subset_right
      have hFsum : ∑ g ∈ F, p g = (∑ g ∈ Sa, p g) + ∑ g ∈ o2.sold ∩ R, p g := by
        rw [hF, Finset.sum_union hFdisj]
      have hbudget2 : o2.money 0 + o2.money 1 ≤ ∑ g ∈ o2.sold ∩ R, p g := by
        have := ho2_budget
        rw [Fin.sum_univ_two] at this
        rwa [sum_restrictVal R p o2.sold] at this
      rw [hFsum]; linarith [hmaS]
  · -- Utilities.
    intro i
    rw [util_unifiedOutcome v p Avec F q i]
    rcases fin3_cover hab hac hbc i with hi | hi | hi
    · rw [hi, hAveca, hqa]; exact haU
    · rw [hi, hAvecb, hqb]
      have hutil : util (restrictVal R (v b)) o2 0
          = (∑ g ∈ o2.kept 0 ∩ R, v b g) + o2.money 0 := by
        rw [util, sum_restrictVal R (v b) (o2.kept 0)]
      have hge : (∑ g ∈ o2.kept 0 ∩ R, v b g) ≤ vbarSum (v b) p (o2.kept 0 ∩ R) :=
        sum_le_vbarSum (v b) p (o2.kept 0 ∩ R)
      have hbb := hb
      rw [hutil] at hbb
      linarith
    · rw [hi, hAvecc, hqc]
      have hutil : util (restrictVal R (v c)) o2 1
          = (∑ g ∈ o2.kept 1 ∩ R, v c g) + o2.money 1 := by
        rw [util, sum_restrictVal R (v c) (o2.kept 1)]
      have hge : (∑ g ∈ o2.kept 1 ∩ R, v c g) ≤ vbarSum (v c) p (o2.kept 1 ∩ R) :=
        sum_le_vbarSum (v c) p (o2.kept 1 ∩ R)
      have hcc := hc
      rw [hutil] at hcc
      linarith

/-- Given the reduction data for a *specific* choice of the served agent `a` and the two other
agents `b, c`, finish the argument by running the two-agent algorithm on the restricted
instance and composing. -/
lemma finish_from_reduction (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ka Sa : Finset G) (ma : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hmaS : ma ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (hRb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b))
        (restrictVal (Finset.univ \ (Ka ∪ Sa)) p))
    (hRc : (3/4 : ℝ) * MMS 3 (v c) p ≤
      MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v c))
        (restrictVal (Finset.univ \ (Ka ∪ Sa)) p)) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  set R : Finset G := Finset.univ \ (Ka ∪ Sa) with hR
  obtain ⟨o2, ho2, ho2util⟩ :=
    exists_MMS_two ![restrictVal R (v b), restrictVal R (v c)] (restrictVal R p)
      (by intro i g; fin_cases i <;> exact restrictVal_nonneg R (hv _) g)
      (restrictVal_nonneg R hp)
  have hb : (3/4 : ℝ) * MMS 3 (v b) p ≤ util (restrictVal R (v b)) o2 0 := by
    have h0 := ho2util 0
    simp only [Matrix.cons_val_zero] at h0
    exact le_trans hRb h0
  have hc : (3/4 : ℝ) * MMS 3 (v c) p ≤ util (restrictVal R (v c)) o2 1 := by
    have h1 := ho2util 1
    simp only [Matrix.cons_val_one] at h1
    exact le_trans hRc h1
  exact compose_three v p hp a b c hab hac hbc Ka Sa ma hKSa hma0 hmaS haU o2 ho2 hb hc

/-! ### Supporting lemmas for the reduction -/

/-- The set of guaranteeable values is bounded above (needed to compare with the supremum). -/
lemma MMSset_bddAbove_of (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSset n v p) := by
  obtain ⟨o, hovalid, _hcover, homax⟩ := exists_max_outcome v p hv hp hn
  refine ⟨minUtil v o, fun r hr => ?_⟩
  obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn v p r).mp hr
  exact hr'.trans (homax o' hv')

/-- If a valid outcome guarantees value `r` to every part, then `r ≤ MMS`. -/
lemma le_MMS_of_outcome (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    (o : Outcome G n) (ho : o.Valid p) (r : ℝ) (hr : ∀ j, r ≤ util v o j) :
    r ≤ MMS n v p :=
  le_csSup (MMSset_bddAbove_of hn v p hv hp) ⟨o, ho, hr⟩

omit [Fintype G] in
/-- On a bundle contained in `R`, the restricted `v̄`-value agrees with the unrestricted one. -/
lemma vbarSum_restrict_subset (w p : G → ℝ) (R B : Finset G) (hB : B ⊆ R) :
    vbarSum (restrictVal R w) (restrictVal R p) B = vbarSum w p B := by
  unfold vbarSum vbar
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [restrictVal_mem R w (hB hg), restrictVal_mem R p (hB hg)]

/-- **Restricted two-agent MMS lower bound.**  If the goods `R` can be split into two disjoint
sub-bundles `B1, B2 ⊆ R`, each of `v̄`-value at least `r`, then the two-agent maximin share of
the restricted instance is at least `r`. -/
lemma restricted_MMS2_ge (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R B1 B2 : Finset G) (r : ℝ)
    (hdisj : Disjoint B1 B2) (hB1 : B1 ⊆ R) (hB2 : B2 ⊆ R)
    (h1 : r ≤ vbarSum w p B1) (h2 : r ≤ vbarSum w p B2) :
    r ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by
  classical
  set o : Outcome G 2 :=
    unifiedOutcome (fun _ => restrictVal R w) (restrictVal R p) ![B1, B2] ∅ 0 with ho
  have hovalid : o.Valid (restrictVal R p) := by
    rw [ho]
    apply unifiedOutcome_valid _ _ (restrictVal_nonneg R hp)
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hdisj.symm]
    · intro i; simp
    · intro i; simp
    · simp
  refine le_MMS_of_outcome (by norm_num) (restrictVal R w) (restrictVal R p)
    (restrictVal_nonneg R hw) (restrictVal_nonneg R hp) o hovalid r (fun j => ?_)
  have hu : util (restrictVal R w)
      (unifiedOutcome (fun _ : Fin 2 => restrictVal R w) (restrictVal R p) ![B1, B2] ∅ 0) j
      = vbarSum (restrictVal R w) (restrictVal R p) (![B1, B2] j) + (0 : Fin 2 → ℝ) j :=
    util_unifiedOutcome (fun _ : Fin 2 => restrictVal R w) (restrictVal R p) ![B1, B2] ∅ 0 j
  rw [ho, hu, Pi.zero_apply, add_zero]
  fin_cases j
  · show r ≤ vbarSum (restrictVal R w) (restrictVal R p) B1
    rw [vbarSum_restrict_subset w p R B1 hB1]; exact h1
  · show r ≤ vbarSum (restrictVal R w) (restrictVal R p) B2
    rw [vbarSum_restrict_subset w p R B2 hB2]; exact h2

/-- **Total `v̄`-value bound.**  For three agents, the total `v̄`-value of all goods is at least
`3 · MMS`.  (Any maximin partition splits the goods into three parts of value `≥ MMS`, and the
sum of the parts' values never exceeds the total `v̄`-value.) -/
lemma three_MMS_le_vbarSum_univ (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    3 * MMS 3 w p ≤ vbarSum w p Finset.univ := by
  classical
  obtain ⟨o, hovalid, _hcover, hge⟩ := exists_MMS_partition (n := 3) (by norm_num) w p hw hp
  obtain ⟨hsold, hdisj, hmoney, hbudget⟩ := hovalid
  set U : Finset G := Finset.univ.biUnion o.kept with hU
  have hsum_ge : 3 * MMS 3 w p ≤ ∑ j, util w o j := by
    have hcst : ∑ _j : Fin 3, MMS 3 w p ≤ ∑ j, util w o j :=
      Finset.sum_le_sum (fun j _ => hge j)
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using hcst
  have hsum_eq : ∑ j, util w o j = (∑ g ∈ U, w g) + ∑ j, o.money j := by
    unfold util
    rw [Finset.sum_add_distrib]
    congr 1
    rw [hU, Finset.sum_biUnion]
    intro i _ j _ hij; exact hdisj i j hij
  have hUdisj : Disjoint U o.sold := by
    rw [hU, Finset.disjoint_biUnion_left]
    intro i _; exact (hsold i).symm
  have hbound : (∑ g ∈ U, w g) + ∑ j, o.money j ≤ vbarSum w p Finset.univ := by
    have h1 : (∑ g ∈ U, w g) ≤ ∑ g ∈ U, vbar w p g :=
      Finset.sum_le_sum (fun g _ => le_max_right _ _)
    have h2 : ∑ j, o.money j ≤ ∑ g ∈ o.sold, vbar w p g :=
      le_trans hbudget (Finset.sum_le_sum (fun g _ => le_max_left _ _))
    have h3 : (∑ g ∈ U, vbar w p g) + ∑ g ∈ o.sold, vbar w p g
        = ∑ g ∈ U ∪ o.sold, vbar w p g := (Finset.sum_union hUdisj).symm
    have h4 : ∑ g ∈ U ∪ o.sold, vbar w p g ≤ vbarSum w p Finset.univ := by
      unfold vbarSum
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => le_max_of_le_left (hp g))
    calc (∑ g ∈ U, w g) + ∑ j, o.money j
        ≤ (∑ g ∈ U, vbar w p g) + ∑ g ∈ o.sold, vbar w p g := by linarith
      _ = ∑ g ∈ U ∪ o.sold, vbar w p g := h3
      _ ≤ vbarSum w p Finset.univ := h4
  rw [hsum_eq] at hsum_ge
  exact le_trans hsum_ge hbound

omit [Fintype G] in
/-- **Bag-filling.**  If every item of `S` has weight at most the interval length `hi - lo`, and
the total weight of `S` is at least `lo`, then some sub-bundle `B ⊆ S` has total weight in the
interval `[lo, hi]`. -/
lemma bagfill (u : G → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ S : Finset G, (∀ g ∈ S, u g ≤ hi - lo) → lo ≤ ∑ g ∈ S, u g →
      ∃ B ⊆ S, lo ≤ ∑ g ∈ B, u g ∧ ∑ g ∈ B, u g ≤ hi := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro _ hsum
    refine ⟨∅, Finset.Subset.refl _, by simpa using hsum, ?_⟩
    simp only [Finset.sum_empty]; linarith
  | @insert g S' hg IH =>
    intro hbound hsum
    by_cases hcase : lo ≤ ∑ x ∈ S', u x
    · obtain ⟨B, hB, hB1, hB2⟩ :=
        IH (fun x hx => hbound x (Finset.mem_insert_of_mem hx)) hcase
      exact ⟨B, hB.trans (Finset.subset_insert _ _), hB1, hB2⟩
    · push_neg at hcase
      refine ⟨insert g S', Finset.Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert hg]
      have hug : u g ≤ hi - lo := hbound g (Finset.mem_insert_self _ _)
      linarith

/-- `MMS` is non-negative (the empty outcome guarantees `0`). -/
lemma MMS_nonneg (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    0 ≤ MMS n v p :=
  le_csSup (MMSset_bddAbove_of hn v p hv hp) (mem_MMSset_zero v p)

/-- **General two-agent bound.**  If the goods `R` have total `v̄`-value at least `2τ` and every
single good has `v̄`-value at most the slack `v̄(R) - 2τ`, then the goods `R` can be split into two
bundles each of `v̄`-value at least `τ`, so the restricted two-agent maximin share is at least
`τ`. -/
lemma restricted_MMS2_ge_of_slack (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R : Finset G) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 * τ ≤ vbarSum w p R)
    (hslack : ∀ g ∈ R, vbar w p g ≤ vbarSum w p R - 2 * τ) :
    τ ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by
  classical
  have hsumR : vbarSum w p R = ∑ g ∈ R, vbar w p g := rfl
  have hbnd : ∀ g ∈ R, vbar w p g ≤ (vbarSum w p R - τ) - τ := by
    intro g hg; have := hslack g hg; linarith
  have htot : τ ≤ ∑ g ∈ R, vbar w p g := by rw [← hsumR]; linarith
  obtain ⟨B1, hB1sub, hB1lo, hB1hi⟩ :=
    bagfill (fun g => vbar w p g) τ (vbarSum w p R - τ) hτ (by linarith) R hbnd htot
  refine restricted_MMS2_ge w p hw hp R B1 (R \ B1) τ
    (Finset.disjoint_sdiff) hB1sub (Finset.sdiff_subset) hB1lo ?_
  have hsdiff : vbarSum w p (R \ B1) = vbarSum w p R - vbarSum w p B1 :=
    vbarSum_sdiff w p hB1sub
  have hval : vbarSum w p B1 = ∑ g ∈ B1, vbar w p g := rfl
  rw [hsdiff]; linarith [hB1hi]

/-- **Clean case of Lemma 4 (pure bundle).**  For an agent `i` all of whose goods have
`v̄`-value below `3/4 · MMS_i`, if a bundle `B` of `v̄`-value at most `3/4 · MMS_i` is removed,
then the remaining goods can (as a two-agent instance) still guarantee `3/4 · MMS_i`. -/
lemma pure_reduction (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p)
    (B : Finset G) (hBrej : vbarSum w p B ≤ (3/4) * MMS 3 w p) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by
  classical
  set M : ℝ := MMS 3 w p with hM
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  set R : Finset G := Finset.univ \ B with hR
  -- Total `v̄`-value of the remaining goods.
  have hBsub : B ⊆ Finset.univ := Finset.subset_univ _
  have hRval : vbarSum w p R = vbarSum w p Finset.univ - vbarSum w p B := by
    rw [hR]; exact vbarSum_sdiff w p hBsub
  have hunivge : 3 * M ≤ vbarSum w p Finset.univ := three_MMS_le_vbarSum_univ w p hw hp
  have hRge : (9/4) * M ≤ vbarSum w p R := by rw [hRval]; linarith
  -- Bag-fill the first sub-bundle.
  have hsumR : vbarSum w p R = ∑ g ∈ R, vbar w p g := rfl
  have hlo0 : (0 : ℝ) ≤ (3/4) * M := by positivity
  have hlohi : (3/4) * M ≤ vbarSum w p R - (3/4) * M := by linarith
  have hbnd : ∀ g ∈ R, vbar w p g ≤ (vbarSum w p R - (3/4) * M) - (3/4) * M := by
    intro g _; have := hnobig g; linarith
  have htot : (3/4) * M ≤ ∑ g ∈ R, vbar w p g := by rw [← hsumR]; linarith
  obtain ⟨B1, hB1sub, hB1lo, hB1hi⟩ :=
    bagfill (fun g => vbar w p g) ((3/4) * M) (vbarSum w p R - (3/4) * M) hlo0 hlohi R hbnd htot
  -- The two sub-bundles.
  refine restricted_MMS2_ge w p hw hp R B1 (R \ B1) ((3/4) * M)
    (Finset.disjoint_sdiff) hB1sub (Finset.sdiff_subset) hB1lo ?_
  have hsdiff : vbarSum w p (R \ B1) = vbarSum w p R - vbarSum w p B1 :=
    vbarSum_sdiff w p hB1sub
  have hval : vbarSum w p B1 = ∑ g ∈ B1, vbar w p g := rfl
  rw [hsdiff]; linarith [hB1hi]

/-
A three-part unified MMS configuration yields a two-part restricted MMS guarantee whenever
one untouched kept part is removed.  This is the manuscript's loss case `ℓ₁`: the removed good
belongs in full to one MMS part, so the other two MMS parts (including their shares of proceeds
from the force-sold set) survive unchanged.
-/
lemma untouched_mms_part_reduction (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
    (hcfg : ConfigN 3 w p (MMS 3 w p) A s q)
    (lost j k : Fin 3) (hlj : lost ≠ j) (hlk : lost ≠ k) (hjk : j ≠ k)
    (g : G) (hg : g ∈ A lost) :
    MMS 3 w p ≤ MMS 2 (restrictVal (Finset.univ \ {g}) w)
      (restrictVal (Finset.univ \ {g}) p) := by
  apply le_MMS_of_outcome;
  bv_decide;
  exact fun _ => restrictVal_nonneg _ hw _;
  exact fun _ => restrictVal_nonneg _ hp _;
  rotate_right;
  exact unifiedOutcome ( fun i => restrictVal ( Finset.univ \ { g } ) w ) ( restrictVal ( Finset.univ \ { g } ) p ) ( fun i => if i = 0 then A j else A k ) s ( fun i => if i = 0 then q j else q k );
  · apply unifiedOutcome_valid;
    · exact fun _ => restrictVal_nonneg _ hp _;
    · have := hcfg.1;
      grind;
    · exact fun i => by fin_cases i <;> [ exact hcfg.2.1 j; exact hcfg.2.1 k ] ;
    · exact fun i => by split_ifs <;> [ exact hcfg.2.2.2.1 j; exact hcfg.2.2.2.1 k ] ;
    · have := hcfg.2.2.2.2.1; simp_all +decide [ Fin.sum_univ_three ] ;
      fin_cases lost <;> fin_cases j <;> fin_cases k <;> simp +decide at hlj hlk hjk hg ⊢;
      all_goals rw [ show ∑ g_1 ∈ s, restrictVal ( Finset.univ \ { g } ) p g_1 = ∑ g_1 ∈ s, p g_1 from ?_ ] ; linarith [ hcfg.2.2.2.1 0, hcfg.2.2.2.1 1, hcfg.2.2.2.1 2 ];
      all_goals refine' Finset.sum_congr rfl fun x hx => _; simp +decide [ restrictVal ] ;
      all_goals intro hx'; have := hcfg.2.1 0; have := hcfg.2.1 1; have := hcfg.2.1 2; simp_all +decide [ Finset.disjoint_left ] ;
  · intro i
    have h_util : util (restrictVal (Finset.univ \ {g}) w) (unifiedOutcome (fun i => restrictVal (Finset.univ \ {g}) w) (restrictVal (Finset.univ \ {g}) p) (fun i => if i = 0 then A j else A k) s (fun i => if i = 0 then q j else q k)) i = vbarSum w p (if i = 0 then A j else A k) + (if i = 0 then q j else q k) := by
      convert util_unifiedOutcome _ _ _ _ _ _ using 1;
      rw [ vbarSum_restrict_subset ];
      intro x hx; have := hcfg.1; simp_all +decide [ Finset.disjoint_left ] ;
      grind;
    fin_cases i <;> simp_all +decide [ ConfigN ]

/-
**Main Lemma (2), the two directly isolated loss cases.**  If the allocated bundle is a
rejected pure bundle (`ℓ₂`), or is a singleton good which occupied an untouched part of the
remaining agent's own MMS configuration (`ℓ₁`), then that agent can partition what remains into
two bundles worth at least `3/4` of its original MMS.  The first branch is the bag-filling argument
`pure_reduction`; the second preserves two complete parts of the MMS configuration.
-/
theorem main_lemma_two_basic_cases (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p) (B : Finset G)
    (hcase : vbarSum w p B ≤ (3/4) * MMS 3 w p ∨
      ∃ (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
        (lost j k : Fin 3) (g : G),
        B = {g} ∧ ConfigN 3 w p (MMS 3 w p) A s q ∧
        lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by
  obtain hcase | ⟨A, s, q, lost, j, k, g, hg⟩ := hcase;
  · exact pure_reduction w p hw hp hnobig B hcase;
  · obtain ⟨hB, hcfg, hlj, hlk, hjk, hg⟩ := hg;
    have := untouched_mms_part_reduction w p hw hp A s q hcfg lost j k hlj hlk hjk g hg;
    exact le_trans ( mul_le_of_le_one_left ( MMS_nonneg ( by decide ) _ _ hw hp ) ( by norm_num ) ) ( by simpa only [ hB ] using this )

/-
The numerical core of the manuscript's paired loss cases `ℓ₃` and `ℓ₄`.  The loss
bookkeeping in those cases preserves one revised MMS part `C`, worth between `3/4·MMS` and
`MMS`, while the total remaining value is at least `MMS + 3/4·MMS`.  Consequently `C` and its
complement are the required two bags.
-/
lemma paired_loss_bagfill_reduction (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C : Finset G) (hC : C ⊆ R)
    (hClo : (3/4) * MMS 3 w p ≤ vbarSum w p C)
    (hChi : vbarSum w p C ≤ MMS 3 w p)
    (hR : MMS 3 w p + (3/4) * MMS 3 w p ≤ vbarSum w p R) :
    (3/4) * MMS 3 w p ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by
  apply FairSelling.restricted_MMS2_ge;
  bv_omega;
  exact hp;
  convert Finset.disjoint_sdiff;
  exact inferInstance;
  exact C;
  exact R;
  · assumption;
  · grind;
  · exact hClo;
  · linarith [ vbarSum_sdiff w p hC ]

/-- The four loss types needed by Main Lemma (2), expressed by the invariant each case leaves
for one remaining agent.  `pure` is `ℓ₂`, `untouched` is `ℓ₁`, and `paired` packages the two
quantitative invariants established by the `ℓ₃`/`ℓ₄` bookkeeping in the manuscript. -/
inductive MainLemmaTwoLoss (w p : G → ℝ) (B : Finset G) : Prop
  | pure (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p)
      (hB : vbarSum w p B ≤ (3/4) * MMS 3 w p)
  | untouched (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
      (lost j k : Fin 3) (g : G) (hB : B = {g})
      (hcfg : ConfigN 3 w p (MMS 3 w p) A s q)
      (hlj : lost ≠ j) (hlk : lost ≠ k) (hjk : j ≠ k) (hg : g ∈ A lost)
  | paired (C : Finset G) (hC : C ⊆ Finset.univ \ B)
      (hClo : (3/4) * MMS 3 w p ≤ vbarSum w p C)
      (hChi : vbarSum w p C ≤ MMS 3 w p)
      (hR : MMS 3 w p + (3/4) * MMS 3 w p ≤ vbarSum w p (Finset.univ \ B))

/-
**Main Lemma (2).**  For every one of the manuscript's loss invariants, either two old MMS
parts survive, or bag filling splits the remainder into two `3/4`-MMS parts.
-/
theorem main_lemma_two (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (B : Finset G) (hloss : MainLemmaTwoLoss w p B) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by
  obtain ⟨hnobig, hcase⟩ | ⟨A, s, q, lost, j, k, g, hB, hcfg, hlj, hlk, hjk, hg⟩ | ⟨C, hC, hClo, hChi, hR⟩ := hloss;
  · exact pure_reduction w p hw hp hnobig B hcase;
  · have hfull := untouched_mms_part_reduction w p hw hp A s q hcfg lost j k hlj hlk hjk g hg
    have hM0 : 0 ≤ MMS 3 w p := MMS_nonneg (n := 3) (by decide) w p hw hp
    rw [hB]
    exact (by linarith : (3/4) * MMS 3 w p ≤ MMS 3 w p) |>.trans hfull;
  · exact paired_loss_bagfill_reduction w p hw hp _ _ hC hClo hChi hR

end FairSelling
