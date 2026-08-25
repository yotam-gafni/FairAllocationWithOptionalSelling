import Mathlib
import RequestProject.PreliminaryPhase

/-!
# Three agents receive three quarters of their maximin share

End-to-end formalization of the `n = 3` case of the manuscript's `3/4`-MMS theorem
(Theorem 3 for `n = 3`).  The proof combines

* the preliminary phase (`PreliminaryPhase`), which disposes of instances containing a good that
  some agent values — or that the market prices — at `3/4 · MMS` or more;
* the canonical-partition construction, Lemma 3 (`CanonicalStrict`);
* the matching phase (`MatchingPhase`);
* Lemma 4 in full (`LemmaFourResidual`);
* and the cash-preserving reduction to the two-agent algorithm
  (`ThreeAgentCash`, `ThreeAgentCashComposition`, `TwoAgents`).

The statement carries no hypotheses beyond non-negativity of the valuations and prices.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- **The manuscript's `n = 3` theorem.** Every optional-selling instance with three agents and
non-negative additive values and prices admits a valid outcome (a selling decision, an allocation
of the kept goods, and a distribution of the sale proceeds) giving every agent at least `3/4` of
its maximin share with selling. -/
theorem exists_threequarter_MMS_three (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  by_cases hexp : ∃ (i : Fin 3) (g : G), (3 / 4 : ℝ) * MMS 3 (v i) p ≤ p g
  · -- Stage 1 of the preliminary phase: some good is expensive.
    obtain ⟨i0, e, he⟩ := hexp
    exact preliminary_stage_one v p hv hp i0 e he
  · push_neg at hexp
    by_cases hval : ∃ (i : Fin 3) (g : G), (3 / 4 : ℝ) * MMS 3 (v i) p ≤ v i g
    · -- Stage 2 of the preliminary phase: some agent values a good highly.
      obtain ⟨a, e, he⟩ := hval
      exact preliminary_stage_two v p hv hp (fun i g => hexp i g) a e he
    · -- After the preliminary phase: no big goods.
      push_neg at hval
      refine exists_threequarter_MMS_three_nobig' v p hv hp (fun i g => ?_)
      exact max_lt (hexp i g) (hval i g)

end FairSelling
