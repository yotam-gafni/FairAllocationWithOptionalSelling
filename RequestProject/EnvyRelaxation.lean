import Mathlib
import RequestProject.EpsEnvy
import RequestProject.LemmaTen

/-!
# `SEF1`/`SEFX` are relaxations of envy-freeness — and the literal definitions are not

Definition 4 of the manuscript presents `SEF1` and `SEFX` as *relaxations* of envy-freeness: an
envy-free allocation should satisfy both.  For the corrected notions this is exactly what happens,
and it is proved in `RequestProject.Selling`:

* `FairSelling.SEF1_of_EF` and `FairSelling.SEFX_of_EF` — envy-freeness implies `SEF1` and `SEFX`;
* `FairSelling.SEF1_of_SEFX` — `SEFX` implies `SEF1`.

This file shows that both corrections are *necessary* for that to be true, by exhibiting a single
instance and a **full**, envy-free allocation of it which satisfies neither of the literal
notions `SEF1lit`, `SEFXlit`:

* two goods, both priced `1`, both worthless to both agents;
* good `1` is sold, good `0` is kept by agent `1`, and the whole proceeds `1` go to agent `0`.

Agent `0` is not envious: its money `P₀ = 1` exactly matches the modified value `v̄₀({0}) = 1` of
agent `1`'s bundle.  But agent `1` holds no money, so the literal relaxed condition applies with
agent `0`'s own money *omitted* from the left-hand side, and it reads `0 ≥ 0 + p(0) = 1`.

Packaged statements: `not_SEF1lit_relaxation_of_EF`, `not_SEFXlit_relaxation_of_EF`, and
`SEF1_SEFX_relaxation_of_EF` for the positive direction.
-/

open scoped BigOperators

namespace FairSelling

namespace RelaxEx

/-- Both goods are priced `1`. -/
def p : Fin 2 → ℝ := ![1, 1]

/-- Both agents value both goods at `0`; only the market prices matter. -/
def v : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![0, 0]]

/-- Sell good `1`, give good `0` to agent `1`, and hand the whole proceeds to agent `0`. -/
def o : Outcome (Fin 2) 2 := ⟨{1}, ![∅, {0}], ![1, 0]⟩

theorem p_nonneg : ∀ g, 0 ≤ p g := by
  intro g; fin_cases g <;> norm_num [p]

theorem v_nonneg : ∀ i g, 0 ≤ v i g := by
  intro i g; fin_cases i <;> fin_cases g <;> norm_num [v]

theorem vbarSum_empty (i : Fin 2) : vbarSum (v i) p ∅ = 0 := by
  simp [vbarSum]

theorem vbarSum_singleton (i : Fin 2) : vbarSum (v i) p {0} = 1 := by
  fin_cases i <;> simp [vbarSum, vbar, p, v]

/-- The outcome is a full allocation: every good is sold or allocated, and the whole sale
proceeds are distributed. -/
theorem o_full : o.Full p Finset.univ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, Finset.subset_univ _, ?_, ?_⟩
  · intro j; fin_cases j <;> simp [o]
  · intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all [o]
  · intro j; fin_cases j <;> norm_num [o]
  · simp [o, Fin.sum_univ_two, p]
  · show ({1} : Finset (Fin 2)) ∪ Finset.univ.biUnion o.kept = Finset.univ
    ext x
    fin_cases x <;> simp [o, Finset.mem_biUnion, Fin.exists_fin_two]
  · simp [o, Fin.sum_univ_two, p]

theorem o_valid : o.Valid p := o_full.1

/-- The allocation is envy-free: agent `0`'s money exactly matches the modified value of
agent `1`'s bundle. -/
theorem o_EF : EF v p o := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [o, vbarSum, vbar, v, p]

/-- Yet it does **not** satisfy the literal transcription of Definition 4.1: agent `1` holds no
money, and the literal condition omits agent `0`'s money from the left-hand side. -/
theorem o_not_SEF1lit : ¬ SEF1lit v p o := by
  intro h
  obtain ⟨g, hg, hx⟩ := (h 0 1).2 (by norm_num [o])
  have hg0 : g = 0 := by
    have : g ∈ ({0} : Finset (Fin 2)) := hg
    simpa using this
  subst hg0
  have h1 : o.kept 0 = ∅ := by simp [o]
  have h2 : ({0} : Finset (Fin 2)) \ {0} = ∅ := by decide
  rw [h1, vbarSum_empty] at hx
  have h3 : o.kept 1 = ({0} : Finset (Fin 2)) := by simp [o]
  rw [h3, h2, vbarSum_empty] at hx
  norm_num [p] at hx

/-- The same allocation does not satisfy the literal transcription of Definition 4.2 either. -/
theorem o_not_SEFXlit : ¬ SEFXlit v p o := by
  intro h
  have hmem : (0 : Fin 2) ∈ o.kept 1 := by simp [o]
  have hx := (h 0 1).2 (by norm_num [o]) 0 hmem
  have h1 : o.kept 0 = ∅ := by simp [o]
  have h2 : ({0} : Finset (Fin 2)) \ {0} = ∅ := by decide
  have h3 : o.kept 1 = ({0} : Finset (Fin 2)) := by simp [o]
  rw [h1, vbarSum_empty, h3, h2, vbarSum_empty] at hx
  norm_num [p] at hx

/-- It does satisfy the corrected notions, since these are relaxations of envy-freeness. -/
theorem o_SEFX : SEFX v p o := SEFX_of_EF o_EF

theorem o_SEF1 : SEF1 v p o := SEF1_of_EF o_EF

end RelaxEx

/-- **The literal reading of Definition 4.1 is not a relaxation of envy-freeness.**  There is an
instance with non-negative valuations and prices and a *full* envy-free allocation of it that does
not satisfy `SEF1lit`. -/
theorem not_SEF1lit_relaxation_of_EF :
    ¬ ∀ (v : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
        (∀ i g, 0 ≤ v i g) → (∀ g, 0 ≤ p g) → o.Valid p → EF v p o → SEF1lit v p o := by
  intro h
  exact RelaxEx.o_not_SEF1lit
    (h RelaxEx.v RelaxEx.p RelaxEx.o RelaxEx.v_nonneg RelaxEx.p_nonneg RelaxEx.o_valid RelaxEx.o_EF)

/-- **The literal reading of Definition 4.2 is not a relaxation of envy-freeness** either. -/
theorem not_SEFXlit_relaxation_of_EF :
    ¬ ∀ (v : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
        (∀ i g, 0 ≤ v i g) → (∀ g, 0 ≤ p g) → o.Valid p → EF v p o → SEFXlit v p o := by
  intro h
  exact RelaxEx.o_not_SEFXlit
    (h RelaxEx.v RelaxEx.p RelaxEx.o RelaxEx.v_nonneg RelaxEx.p_nonneg RelaxEx.o_valid RelaxEx.o_EF)

/-- **The corrected notions are relaxations of envy-freeness**, as Definition 4 claims: every
envy-free allocation is `SEFX`, and every `SEFX` allocation is `SEF1`. -/
theorem SEF1_SEFX_relaxation_of_EF {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) (hv : ∀ i g, 0 ≤ v i g)
    (hvalid : o.Valid p) (hEF : EF v p o) :
    SEFX v p o ∧ SEF1 v p o :=
  ⟨SEFX_of_EF hEF, SEF1_of_SEFX hv hvalid (SEFX_of_EF hEF)⟩

end FairSelling
