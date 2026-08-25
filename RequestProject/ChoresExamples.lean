import Mathlib
import RequestProject.ChoresModel

/-!
# Chores with outsourcing: the failure of the "no chore costs more than the MMS" property

For indivisible chores *without* outsourcing, no chore costs more than the maximin share: if
it did, then in any partition — in particular in an MMS partition — the bundle containing it
would cost more than the MMS.  This is `cost_le_of_outsourced_empty` of
`RequestProject.ChoresModel`, and it is what makes the classical bag-filling algorithm
(Algorithm 12 of the manuscript) a `2`-approximation.

As the manuscript observes, the property fails once outsourcing is allowed, because the price
of an outsourced chore is shared among all the agents.  This file records the simplest
instance witnessing the failure: a single chore, three agents, an in-house cost of `10` and a
market price of `6`.  With three agents, outsourcing the chore and splitting the bill gives
every part a cost of `2`, so `MMS = 2`, while the effective cost of the chore is
`c̄(t) = min{10, 6} = 6 > 2 · 2`.
-/

open scoped BigOperators

namespace FairChores

/-- Total effective cost is a lower bound for `n` times the maximin share; this is the
manuscript's `n · MMSᵢ ≥ c̄ᵢ(M)`. -/
theorem cbarSum_univ_le_nsmul_MMS {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) :
    cbarSum c p Finset.univ ≤ n * MMS n c p :=
  le_trans (cbarSum_le_wtSum Finset.univ) (wtSum_univ_le_nsmul_MMS hc hn)

namespace ExpensiveChore

/-- One chore, costing `10` to the (two) agents. -/
def cc : Fin 1 → ℝ := fun _ => 10

/-- Its market price is `6`. -/
def pp : Fin 1 → ℝ := fun _ => 6

lemma cbar_eq : ∀ t, cbar cc pp t = 6 := by
  intro t; norm_num [cbar, cc, pp]

lemma cbarSum_univ : cbarSum cc pp Finset.univ = 6 := by
  simp [cbarSum, cbar_eq]

/-- Outsourcing the chore and splitting the bill equally among three agents costs each `2`. -/
def oo : Outcome (Fin 1) 3 :=
  { outsourced := Finset.univ
    kept := fun _ => ∅
    pay := fun _ => 2 }

lemma oo_valid : oo.Valid pp := by
  refine ⟨by simp [oo], by simp [oo], ?_, by simp [oo], ?_⟩
  · simp only [oo]
    decide
  · simp [oo, pp]
    norm_num

lemma two_mem : (2:ℝ) ∈ MMSset 3 cc pp :=
  ⟨oo, oo_valid, fun j => by simp [cost, oo]⟩

/-- The maximin share of the instance is `2`. -/
theorem MMS_eq : MMS 3 cc pp = 2 := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (MMSset_bddBelow (fun t => by norm_num [cc]) (by norm_num)) two_mem
  · refine le_csInf ⟨2, two_mem⟩ ?_
    rintro r ⟨o, hvalid, hle⟩
    have hsum : cbarSum cc pp Finset.univ ≤ ∑ j, cost cc o j := cbarSum_univ_le_sum_cost hvalid
    rw [cbarSum_univ] at hsum
    have h2 : ∑ j, cost cc o j ≤ 3 * r := by
      rw [Fin.sum_univ_three]
      linarith [hle 0, hle 1, hle 2]
    linarith

/-- The effective cost of the chore exceeds *twice* the maximin share: with outsourcing, the
property that no chore costs more than the MMS fails badly. -/
theorem cbar_gt_two_MMS : 2 * MMS 3 cc pp < cbar cc pp 0 := by
  rw [MMS_eq, cbar_eq]
  norm_num

/-- Summary of the counterexample. -/
theorem exists_chore_cbar_gt_two_MMS :
    ∃ (c p : Fin 1 → ℝ) (t : Fin 1), 2 * MMS 3 c p < cbar c p t :=
  ⟨cc, pp, 0, cbar_gt_two_MMS⟩

end ExpensiveChore

end FairChores
