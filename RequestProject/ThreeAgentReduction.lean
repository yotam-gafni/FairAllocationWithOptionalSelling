import Mathlib
import RequestProject.CanonicalPartition
import RequestProject.Matching

/-!
# Assembly of the three-agent reduction

This module sits after the proved canonical-partition and finite matching modules.  Main Lemma (2)
is proved in `ThreeAgents`; this file uses it to turn explicit loss certificates into the reduction
needed by the final two-agent call.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-!
## Retired reduction interface

The earlier reduction below is retained as a comment for historical context.  Its conclusion
deletes every sold good together with all of its proceeds before the final two-agent call.
`ThreeAgentReductionCounterexample.no_discarding_cash_reduction_singleton` proves that this
interface is false, even for one valueless good of price one.  The cash-aware replacement
machinery is in `ThreeAgentCash` and `ThreeAgentCashComposition`.
-/

/-
/-- The remaining bookkeeping lemma.  Its hypotheses deliberately expose the two proved inputs
used by the allocation step: Lemma 3's canonical partition and the finite `3 × 3` matching theorem.
The conclusion stops at the exact loss certificates consumed by proved Main Lemma (2), rather than
assuming the entire end-to-end reduction. -/
lemma allocation_bookkeeping_from_canonical_and_matching
    (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hcanonical : ∀ i, (∀ g, vbar (v i) p g < (3/4) * MMS 3 (v i) p) →
      ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ)
        (leftover : Fin 3),
        IsCanonical (v i) p ((3/4) * MMS 3 (v i) p) kept sold money leftover)
    (hmatching : ∀ (acc : Fin 3 → Fin 3 → Bool) (pa : Fin 3),
      (∀ k, acc pa k = true) → (∀ j, ∃ k, acc j k = true) →
      (∃ σ : Equiv.Perm (Fin 3), ∀ j, acc j (σ j) = true) ∨
      (∃ k, acc pa k = true ∧ ∀ j, j ≠ pa → acc j k = false)) :
    ∃ (a : Fin 3) (Ka Sa : Finset G) (ma : ℝ),
      Disjoint Ka Sa ∧ 0 ≤ ma ∧ ma ≤ ∑ g ∈ Sa, p g ∧
      (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma ∧
      ∀ i, i ≠ a → MainLemmaTwoLoss (v i) p (Ka ∪ Sa) := by
  -- unproved placeholder from the earlier attempt

/-- The allocation step, now explicitly assembled from the proved canonical-partition lemma and
matching theorem. -/
lemma allocation_step_with_loss_certificates (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (a : Fin 3) (Ka Sa : Finset G) (ma : ℝ),
      Disjoint Ka Sa ∧ 0 ≤ ma ∧ ma ≤ ∑ g ∈ Sa, p g ∧
      (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma ∧
      ∀ i, i ≠ a → MainLemmaTwoLoss (v i) p (Ka ∪ Sa) := by
  apply allocation_bookkeeping_from_canonical_and_matching v p hv hp
  · intro i hsmall
    exact canonical_partition_three (v i) p (hv i) hp hsmall
  · exact matching_fin3

/-- **Key reduction.**  This is no longer an assumed monolithic combinatorial statement: it is
proved from the allocation/matching bookkeeping certificates and the proved Main Lemma (2). -/
lemma key_reduction (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (a : Fin 3) (Ka Sa : Finset G) (ma : ℝ),
      Disjoint Ka Sa ∧ 0 ≤ ma ∧ ma ≤ ∑ g ∈ Sa, p g ∧
      (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma ∧
      ∀ i, i ≠ a → (3/4 : ℝ) * MMS 3 (v i) p ≤
        MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v i))
          (restrictVal (Finset.univ \ (Ka ∪ Sa)) p) := by
  obtain ⟨a, Ka, Sa, ma, hdisj, hma, hbudget, ha, hloss⟩ :=
    allocation_step_with_loss_certificates v p hv hp
  exact ⟨a, Ka, Sa, ma, hdisj, hma, hbudget, ha,
    fun i hi => main_lemma_two (v i) p (hv i) hp (Ka ∪ Sa) (hloss i hi)⟩

/-- **A `3/4`-MMS allocation for three agents** (Theorem 3, case `n = 3`). -/
theorem exists_threequarter_MMS_three (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨a, Ka, Sa, ma, hKSa, hma0, hmaS, haU, hrest⟩ := key_reduction v p hv hp
  fin_cases a
  · exact finish_from_reduction v p hv hp 0 1 2 (by decide) (by decide) (by decide)
      Ka Sa ma hKSa hma0 hmaS haU (hrest 1 (by decide)) (hrest 2 (by decide))
  · exact finish_from_reduction v p hv hp 1 0 2 (by decide) (by decide) (by decide)
      Ka Sa ma hKSa hma0 hmaS haU (hrest 0 (by decide)) (hrest 2 (by decide))
  · exact finish_from_reduction v p hv hp 2 0 1 (by decide) (by decide) (by decide)
      Ka Sa ma hKSa hma0 hmaS haU (hrest 0 (by decide)) (hrest 1 (by decide))

-/

end FairSelling
