import Mathlib

/-!
# The counting of the `|L′| > n′ + 1` reduction

The last part of the proof of Lemma 9 reduces the case `|L′| > n′ + 1` (too many large goods) to
the case covered by Proposition 6.  After the three bundle transformations one is left with `n₀`
bundles still to be created, `n₂` loss events of type `ℓ₂`, `n₄` loss events of type `ℓ₄`, and a
set `L₀` of large goods lying in distinct bundles, with `|L₀| ≤ n₀ + n₂ + 1`.  Assuming
`n₀ + 1 < |L₀| < 2·n₀` (the two remaining cases being immediate), the manuscript pairs up large
goods into `t = |L₀| − n₀ − 1` acceptable pure bundles.

This file isolates the two arithmetic claims of that step, which are the only places where the
numbers are actually manipulated:

* `reduction_counts` — `t ≤ n₂`, and after the step the number `n̂ = n₀ − t` of bundles still to be
  created and the number `|L₀| − 2t` of remaining large goods satisfy `|L₀| − 2t = n̂ + 1`, so
  Proposition 6 applies;
* `reduction_budget` — the value left at our disposal is still at least `n̂ · MMSᵢ`, even though
  each of the `t` new pure bundles may be worth as much as `2ρ · MMSᵢ > MMSᵢ`.  This is the
  computation `(1 − ρ)·n₂ − 2ρ·t ≥ (1 − 3ρ)·t = −t`, valid because `ρ = 2/3` and `t ≤ n₂`.
-/

namespace FairSelling

/-- The counting of the pairing step: `t = |L₀| − n₀ − 1` pure bundles can be created out of the
large goods, and afterwards there is exactly one more large good than bundles still to create. -/
theorem reduction_counts {L n0 n2 : ℕ} (hlow : n0 + 1 < L) (hhigh : L < 2 * n0)
    (hcard : L ≤ n0 + n2 + 1) :
    (L - n0 - 1 ≤ n2) ∧ L - 2 * (L - n0 - 1) = (n0 - (L - n0 - 1)) + 1 := by
  omega

/-- The value accounting of the pairing step, for `ρ = 2/3`: starting from `n₀ + n₂ + n₄` bundles
of value `μ` each, discounting the `ℓ₂` losses (at most `ρ·μ` each), the `ℓ₄` losses (at most `μ`
each) and the `t` new pure bundles (at most `2ρ·μ` each), at least `(n₀ − t)·μ` of value is
left. -/
theorem reduction_budget (μ : ℝ) (hμ : 0 ≤ μ) (n0 n2 n4 t : ℕ) (ht : t ≤ n2) (Gval : ℝ)
    (hG : ((n0 : ℝ) + n2 + n4) * μ - (n2 : ℝ) * ((2 / 3) * μ) - (n4 : ℝ) * μ
        - 2 * (t : ℝ) * ((2 / 3) * μ) ≤ Gval) :
    ((n0 : ℝ) - t) * μ ≤ Gval := by
  have htn : (t : ℝ) ≤ (n2 : ℝ) := by exact_mod_cast ht
  nlinarith [hμ, htn]

end FairSelling
