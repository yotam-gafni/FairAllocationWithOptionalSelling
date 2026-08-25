import Mathlib
import RequestProject.Selling

/-!
# Appendix H: the equal-proceeds case

This file sets up the *equal proceeds* restriction of the model of
`RequestProject.Selling`: the sale proceeds must be split equally between the agents,

`∀ i, P i = (1 / n) * ∑_{g ∈ S} p g`.

We define the corresponding maximin share `MMSEP` (the "equal-proceeds MMS": the best value
an agent can guarantee herself by partitioning into `n` bundles subject to the equal-proceeds
constraint) and record the elementary facts:

* `MMSEP_le_MMS` — the equal-proceeds MMS is at most the unconstrained MMS;
* `MMSEP_nonneg`, `le_MMSEP` — non-negativity and the way one certifies a lower bound;
* `MMSEP_le_PS` — the trivial upper bound by the proportional share.

The two examples of the appendix are in `RequestProject.EqualProceedsExamples`, and the
bag-filling algorithm (Theorem 7) is in `RequestProject.EqualProceedsBagFilling`.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-- The **equal proceeds** requirement of Appendix H: every agent receives exactly `1/n` of
the total sale proceeds. -/
def Outcome.EqualProceeds (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i, o.money i = (∑ g ∈ o.sold, p g) / n

/-- The set of values that some valid *equal-proceeds* outcome guarantees to every agent. -/
def MMSEPset (n : ℕ) (v p : G → ℝ) : Set ℝ :=
  {r | ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧ ∀ j, r ≤ util v o j}

/-- The **equal-proceeds maximin share**: the maximin share of an agent when the sale proceeds
must be divided equally between the `n` bundles. -/
noncomputable def MMSEP (n : ℕ) (v p : G → ℝ) : ℝ := sSup (MMSEPset n v p)

omit [Fintype G] [DecidableEq G] in
theorem MMSEPset_subset_MMSset (v p : G → ℝ) : MMSEPset n v p ⊆ MMSset n v p := by
  rintro r ⟨o, hvalid, -, hguar⟩
  exact ⟨o, hvalid, hguar⟩

omit [Fintype G] [DecidableEq G] in
theorem mem_MMSEPset_zero (v p : G → ℝ) : (0 : ℝ) ∈ MMSEPset n v p := by
  refine ⟨⟨∅, fun _ => ∅, fun _ => 0⟩, ?_, ?_, ?_⟩ <;>
    simp [Outcome.Valid, Outcome.EqualProceeds, util]

omit [Fintype G] [DecidableEq G] in
theorem MMSEPset_nonempty (v p : G → ℝ) : (MMSEPset n v p).Nonempty :=
  ⟨0, mem_MMSEPset_zero v p⟩

omit [DecidableEq G] in
theorem PS_nonneg (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ PS n v p :=
  div_nonneg (Finset.sum_nonneg fun g _ => le_trans (hp g) (le_max_left _ _))
    (Nat.cast_nonneg _)

/-- Every value guaranteeable by a valid outcome is at most the proportional share. -/
theorem MMSset_le_PS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {r : ℝ} (hr : r ∈ MMSset n v p) : r ≤ PS n v p := by
  rcases le_or_gt 0 r with hr0 | hr0
  · obtain ⟨o, hvalid, hguar⟩ := hr
    exact TPSset_le_PS v p (mem_TPSset_of_valid v p hn hv hp o hvalid r hr0 hguar)
  · exact le_trans hr0.le (PS_nonneg v p hp)

theorem MMSset_bddAbove (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSset n v p) :=
  ⟨PS n v p, fun _ hr => MMSset_le_PS v p hn hv hp hr⟩

theorem MMSEPset_bddAbove (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSEPset n v p) :=
  (MMSset_bddAbove v p hn hv hp).mono (MMSEPset_subset_MMSset v p)

/-- A lower bound on the equal-proceeds MMS is certified by exhibiting a valid equal-proceeds
outcome. -/
theorem le_MMSEP (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {r : ℝ} (hr : r ∈ MMSEPset n v p) : r ≤ MMSEP n v p :=
  le_csSup (MMSEPset_bddAbove v p hn hv hp) hr

omit [Fintype G] [DecidableEq G] in
/-- An upper bound on the equal-proceeds MMS is certified by bounding all valid equal-proceeds
outcomes. -/
theorem MMSEP_le (v p : G → ℝ) {c : ℝ} (h : ∀ r ∈ MMSEPset n v p, r ≤ c) :
    MMSEP n v p ≤ c :=
  csSup_le (MMSEPset_nonempty v p) h

theorem MMSEP_nonneg (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    0 ≤ MMSEP n v p :=
  le_MMSEP v p hn hv hp (mem_MMSEPset_zero v p)

/-- **The equal-proceeds MMS is at most the unconstrained MMS.**  ("Clearly, with this
requirement, the MMS value of agents is weakly smaller than without this requirement.") -/
theorem MMSEP_le_MMS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMSEP n v p ≤ MMS n v p :=
  csSup_le_csSup (MMSset_bddAbove v p hn hv hp) (MMSEPset_nonempty v p)
    (MMSEPset_subset_MMSset v p)

theorem MMSEP_le_PS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMSEP n v p ≤ PS n v p :=
  MMSEP_le v p fun _ hr => MMSset_le_PS v p hn hv hp (MMSEPset_subset_MMSset v p hr)

end FairSelling
