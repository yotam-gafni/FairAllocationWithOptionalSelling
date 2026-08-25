import Mathlib
import RequestProject.Selling
import RequestProject.EpsEnvy
import RequestProject.TPSCompute
import RequestProject.TPSApprox

/-!
# A run of the manuscript's Algorithm 6 whose output is not SEFX

The manuscript proves the second half of Theorem 2 (an allocation that is simultaneously
`n/(2n−1)`-TPS and SEFX) with Algorithm 6: bag filling, plus a `Shrink` step that lets an agent
which *already holds a bundle* steal (a sub-bundle of) the bundle that is about to be handed
out, if it `ε`-SEFX-envies it.  The invariant that the manuscript maintains is that no agent
holding a bundle `ε`-SEFX-envies another agent holding a bundle.

The instance below shows that this invariant does not imply that the final allocation is SEFX:
an agent that is still *active* when a bundle is handed out is never consulted, and it may well
envy that bundle once it is served itself.

## The instance

Two agents with the same valuation, four goods:

| good | `g₀` | `g₁` | `g₂` | `g₃` |
|------|------|------|------|------|
| `v`  | `0`  | `18` | `19` | `5`  |
| `p`  | `18` | `0`  | `0`  | `0`  |

`exTPS`: the truncated proportional share of each agent is `30`, so the threshold used by the
algorithm is `τ = (2/3)·30 = 20`.

## The run

* No good has price at least `20`, and no good is worth `20` to an agent (`exNoLargeGood`), so
  the two `while` loops of Algorithm 6 that deal with large goods do not fire and the algorithm
  goes to bag filling.
* Bag filling adds `g₀` and then `g₁`; the bag `{g₀, g₁}` is worth `36 ≥ 20` to both agents, and
  it is a *minimal* bag: dropping either good leaves `18 < 20` (`exBagMinimal`).  It is handed to
  agent `0`.  No agent holds a bundle yet, so the `Shrink` step of the manuscript performs no
  shrinking (its stealing test quantifies over the agents that already hold a bundle) and the
  whole bag is handed over.
* The remaining goods `{g₂, g₃}` are then bag filled for agent `1`; the bag is again minimal, it
  is worth `24 ≥ 20` to agent `1`, and agent `0` does not `ε`-SEFX-envy it (`exSecondBagSafe`),
  so the manuscript's stealing test does not fire here either.

## The output

Agent `0` holds `{g₀, g₁}`, and since `v(g₀) = 0 < 18 = p(g₀)` it sells `g₀`: its bundle is
`({g₁}, 18)`, worth `36`.  Agent `1` holds `({g₂, g₃}, 0)`, worth `24`.  Both are above the
threshold `20` (`exOutcome_TPS`), but agent `1` envies agent `0` *outright*: agent `0` holds
money, so Definition 4 asks for the full envy-free condition, and `24 < 18 + 18 = 36`.  The
outcome is not `ε`-SEFX for any `ε < 12` (`exOutcome_not_epsSEFX`), in particular not SEFX
(`exOutcome_not_SEFX`).

The instance itself is not a counterexample to Theorem 2: `exGoodOutcome` is an outcome for the
same instance which is envy free (hence SEFX) and gives both agents `30`.

## What the fix has to be

The bundle handed out has to be shrunk *whether or not an agent that already holds a bundle
envies it*: it has to be minimal in the sub-bundle order (drop goods, and keep only part of the
proceeds of a sold good).  Minimality then gives SEFX for free towards every agent that ends up
at or above its own threshold: if `i` SEFX-envied a bundle `(B, 0)` through the good `g`, i.e.
`v̄ᵢ(B \ g) + p(g) > τᵢ`, then the strictly smaller sub-bundle `(B \ g, p(g))` would already have
met agent `i`'s threshold, contradicting minimality; and if a bundle `(B, m)` with `m > 0` were
envied outright by `i`, i.e. `v̄ᵢ(B) + m > τᵢ`, then a sub-bundle `(B, m')` with `m' < m` would
already have met it.  This is discussed in `ISSUES_TPS_SEFX.md`.
-/

open scoped BigOperators

namespace FairSelling

namespace TPSSefxCounterexample

/-- The four goods of the instance. -/
abbrev Gd := Fin 4

/-- The common valuation of the two agents. -/
def exv : Gd → ℝ := ![0, 18, 19, 5]

/-- The market prices. -/
def exp : Gd → ℝ := ![18, 0, 0, 0]

/-- Both agents have the valuation `exv`. -/
def exV : Fin 2 → Gd → ℝ := fun _ => exv

lemma exv_nonneg : ∀ g, 0 ≤ exv g := by
  intro g; fin_cases g <;> norm_num [exv]

lemma exp_nonneg : ∀ g, 0 ≤ exp g := by
  intro g; fin_cases g <;> norm_num [exp]

lemma exV_nonneg : ∀ i g, 0 ≤ exV i g := fun _ => exv_nonneg

@[simp] lemma exv_zero : exv 0 = 0 := rfl
@[simp] lemma exv_one : exv 1 = 18 := rfl
@[simp] lemma exv_two : exv 2 = 19 := rfl
@[simp] lemma exv_three : exv 3 = 5 := rfl
@[simp] lemma exp_zero : exp 0 = 18 := rfl
@[simp] lemma exp_one : exp 1 = 0 := rfl
@[simp] lemma exp_two : exp 2 = 0 := rfl
@[simp] lemma exp_three : exp 3 = 0 := rfl

/-- A sum over the pair `{g₂, g₃}`. -/
lemma sum23 (f : Gd → ℝ) : ∑ x ∈ ({2, 3} : Finset Gd), f x = f 2 + f 3 :=
  Finset.sum_pair (by decide)

/-- A sum over the pair `{g₀, g₁}`. -/
lemma sum01 (f : Gd → ℝ) : ∑ x ∈ ({0, 1} : Finset Gd), f x = f 0 + f 1 :=
  Finset.sum_pair (by decide)

/-- The proportional share of each agent is `30`. -/
lemma exPS : PS 2 exv exp = 30 := by
  unfold PS
  norm_num [Fin.sum_univ_four]

/-- **The truncated proportional share of each agent is `30`.**  Every value is at most `19`,
and the truncated proportional map already exceeds `19` there, so the share equals the
proportional share (the `k = 1` case of the manuscript's computation). -/
lemma exTPS : TPS 2 exv exp = 30 := by
  rw [TPS_eq_PS_of_top exv exp exp_nonneg (s := 19)
    (by intro g; fin_cases g <;> norm_num [exv]) ?_, exPS]
  unfold truncSum
  norm_num [Fin.sum_univ_four]

/-- The threshold used by the algorithm: `τ = (2/3)·TPS = 20`. -/
lemma exThreshold : ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp = 20 := by
  rw [exTPS]; norm_num

/-! ### The run of the algorithm -/

/-- No good is expensive enough or valuable enough to trigger the first two loops of the
algorithm: every price and every value is below the threshold `20`. -/
lemma exNoLargeGood : ∀ g : Gd, exp g < 20 ∧ exv g < 20 := by
  intro g; fin_cases g <;> constructor <;> norm_num [exv, exp]

/-- The bag `{g₀, g₁}` is worth `36` to each agent. -/
lemma exBagValue : vbarSum exv exp {0, 1} = 36 := by
  unfold vbarSum vbar
  rw [sum01]
  norm_num

/-- **The bag `{g₀, g₁}` is a minimal bag**: it meets the threshold `20`, and dropping either of
its two goods leaves a bundle below the threshold.  So bag filling stops exactly there. -/
lemma exBagMinimal :
    20 ≤ vbarSum exv exp {0, 1} ∧
      vbarSum exv exp ({0, 1} \ {0}) < 20 ∧ vbarSum exv exp ({0, 1} \ {1}) < 20 := by
  refine ⟨by rw [exBagValue]; norm_num, ?_, ?_⟩
  · rw [show ({0, 1} : Finset Gd) \ {0} = {1} by decide]
    unfold vbarSum vbar
    norm_num
  · rw [show ({0, 1} : Finset Gd) \ {1} = {0} by decide]
    unfold vbarSum vbar
    norm_num

/-- The second bag `{g₂, g₃}` is worth `24` to each agent, and dropping either of its goods
leaves it below the threshold: it too is a minimal bag. -/
lemma exSecondBagMinimal :
    vbarSum exv exp {2, 3} = 24 ∧
      vbarSum exv exp ({2, 3} \ {2}) < 20 ∧ vbarSum exv exp ({2, 3} \ {3}) < 20 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold vbarSum vbar
    rw [sum23]
    norm_num
  · rw [show ({2, 3} : Finset Gd) \ {2} = {3} by decide]
    unfold vbarSum vbar
    norm_num
  · rw [show ({2, 3} : Finset Gd) \ {3} = {2} by decide]
    unfold vbarSum vbar
    norm_num

/-! ### The output of the run -/

/-- The outcome produced by the run: agent `0` sells `g₀` and keeps `g₁`, agent `1` keeps
`g₂` and `g₃`. -/
def exOutcome : Outcome Gd 2 where
  sold := {0}
  kept := ![{1}, {2, 3}]
  money := ![18, 0]

lemma exOutcome_valid : exOutcome.Valid exp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> decide +kernel
  · intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all <;> decide +kernel
  · intro j; fin_cases j <;> norm_num [exOutcome]
  · norm_num [Fin.sum_univ_two, exOutcome, exp]

/-- Agent `0` gets `36` and agent `1` gets `24`. -/
lemma exOutcome_util : util exv exOutcome 0 = 36 ∧ util exv exOutcome 1 = 24 := by
  constructor
  · unfold util exOutcome
    norm_num
  · unfold util exOutcome
    show (∑ g ∈ ({2, 3} : Finset Gd), exv g) + 0 = 24
    rw [sum23]
    norm_num

/-- **The output does meet the share guarantee**: both agents are above `(2/3)·TPS = 20`. -/
lemma exOutcome_TPS :
    ∀ i, ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 (exV i) exp ≤ util (exV i) exOutcome i := by
  intro i
  have h := exOutcome_util
  fin_cases i
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exOutcome 0
    rw [exThreshold, h.1]; norm_num
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exOutcome 1
    rw [exThreshold, h.2]; norm_num

/-- **But agent `1` envies agent `0` outright.**  Agent `0` holds money, so Definition 4 asks
for the full envy-free condition; agent `1`'s bundle is worth `24` to it, while agent `0`'s is
worth `36`.  The outcome is therefore not `ε`-SEFX for any `ε` (the full envy-free condition
towards a money-holding agent carries no `ε`), in particular not SEFX. -/
lemma exOutcome_not_epsSEFX (eps : ℝ) : ¬ epsSEFX exV exp eps exOutcome := by
  intro h
  have h10 := (h 1 0).1 (by norm_num [exOutcome])
  have hlhs : vbarSum (exV 1) exp (exOutcome.kept 1) + exOutcome.money 1 = 24 := by
    show (∑ g ∈ ({2, 3} : Finset Gd), vbar exv exp g) + 0 = 24
    rw [sum23]
    unfold vbar
    norm_num
  have hrhs : vbarSum (exV 1) exp (exOutcome.kept 0) + exOutcome.money 0 = 36 := by
    show (∑ g ∈ ({1} : Finset Gd), vbar exv exp g) + 18 = 36
    unfold vbar
    norm_num
  rw [hlhs, hrhs] at h10
  norm_num at h10

lemma exOutcome_not_SEFX : ¬ SEFX exV exp exOutcome := by
  intro h
  exact exOutcome_not_epsSEFX 0 (epsSEFX_zero_iff.mpr h)

/-- Agent `0`, holding the first bag, does not `ε`-SEFX-envy the second bag: the manuscript's
stealing test does not fire, so the run really is a run of Algorithm 6. -/
lemma exSecondBagSafe :
    vbarSum (exV 0) exp (exOutcome.kept 1) + exOutcome.money 1
      ≤ vbarSum (exV 0) exp (exOutcome.kept 0) + exOutcome.money 0 := by
  show (∑ g ∈ ({2, 3} : Finset Gd), vbar exv exp g) + 0
      ≤ (∑ g ∈ ({1} : Finset Gd), vbar exv exp g) + 18
  rw [sum23]
  unfold vbar
  norm_num

/-! ### The instance itself has a good allocation -/

/-- Splitting the proceeds of `g₀` as `12` and `6` gives both agents `30` and is envy free. -/
def exGoodOutcome : Outcome Gd 2 where
  sold := {0}
  kept := ![{1}, {2, 3}]
  money := ![12, 6]

lemma exGoodOutcome_valid : exGoodOutcome.Valid exp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> decide +kernel
  · intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all <;> decide +kernel
  · intro j; fin_cases j <;> norm_num [exGoodOutcome]
  · norm_num [Fin.sum_univ_two, exGoodOutcome, exp]

lemma exGoodOutcome_EF : EF exV exp exGoodOutcome := by
  intro i j
  have h0 : vbarSum (exV i) exp (exGoodOutcome.kept 0) + exGoodOutcome.money 0 = 30 := by
    show (∑ g ∈ ({1} : Finset Gd), vbar exv exp g) + 12 = 30
    unfold vbar
    norm_num
  have h1 : vbarSum (exV i) exp (exGoodOutcome.kept 1) + exGoodOutcome.money 1 = 30 := by
    show (∑ g ∈ ({2, 3} : Finset Gd), vbar exv exp g) + 6 = 30
    rw [sum23]
    unfold vbar
    norm_num
  fin_cases j <;> fin_cases i <;> simp_all

/-- **The instance is not a counterexample to Theorem 2**: it admits an outcome that is envy
free — hence SEFX — and gives both agents `30 ≥ (2/3)·TPS`. -/
lemma exGoodOutcome_TPS_SEFX :
    exGoodOutcome.Valid exp ∧
      (∀ i, ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 (exV i) exp ≤ util (exV i) exGoodOutcome i) ∧
      SEFX exV exp exGoodOutcome := by
  refine ⟨exGoodOutcome_valid, ?_, SEFX_of_EF exGoodOutcome_EF⟩
  intro i
  fin_cases i
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exGoodOutcome 0
    rw [exThreshold]
    show (20 : ℝ) ≤ (∑ g ∈ ({1} : Finset Gd), exv g) + 12
    norm_num
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exGoodOutcome 1
    rw [exThreshold]
    show (20 : ℝ) ≤ (∑ g ∈ ({2, 3} : Finset Gd), exv g) + 6
    rw [sum23]
    norm_num

end TPSSefxCounterexample

end FairSelling
