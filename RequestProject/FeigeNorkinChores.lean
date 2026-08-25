import Mathlib

/-!
# The Feige–Norkin three-agent instance for chores

This file formalizes the purely combinatorial core of the negative example of Feige and
Norkin for **chores**, which underlies the manuscript's `19/18` impossibility bound for
chores with outsourcing (Theorem 5): an instance with three agents and nine chores in which,
in *every* allocation, some agent receives a bundle costing at least `19/18` of her target
value `18`.

The original instance has nine chores, the first of which costs `0` to everybody, so it is
dropped here; the eight remaining chores carry the costs

```
cR = 9,   9,    12,    3,    3, 4,    7,    7
cC = 8.5, 7.5,  12.75, 3.25, 3, 5.25, 6.25, 7.5
cU = 7.6, 7.6,  11.4,  4.6,  3.8, 3.8, 7.6,  7.6
```

each summing to `54`, so that the target of every agent (the maximin share for the first two,
the proportional share for the third) is `18`.  To stay inside exact integer arithmetic all
three cost vectors are scaled by `20`; the target then becomes `360` and the claim is that
some agent gets a bundle costing at least `380 = (19/18) * 360`.

Main results:

* `feigeNorkinChores_core` — for every assignment of the eight chores to the three agents,
  some agent `i` gets a bundle of cost at least `380`;
* `feigeNorkinChores_cover` — the same for any three pairwise disjoint bundles covering all
  the chores;
* `fcR_partition`, `fcC_partition`, `fcU_total` — the cost data: agents `R` and `C` can split
  the chores into three bundles of cost `360` each, and the total cost for `U` is
  `1080 = 3 * 360`.
-/

open scoped BigOperators

namespace FairChores

namespace FeigeNorkinChores

/-- Cost function of the first agent (`cR` of the construction), scaled by `20`. -/
def fcR : Fin 8 → ℕ := ![180, 180, 240, 60, 60, 80, 140, 140]

/-- Cost function of the second agent (`cC` of the construction), scaled by `20`. -/
def fcC : Fin 8 → ℕ := ![170, 150, 255, 65, 60, 105, 125, 150]

/-- Cost function of the third agent (`cU` of the construction), scaled by `20`. -/
def fcU : Fin 8 → ℕ := ![152, 152, 228, 92, 76, 76, 152, 152]

/-- The three cost functions of the Feige–Norkin chores instance, scaled by `20`. -/
def fcW : Fin 3 → Fin 8 → ℕ := ![fcR, fcC, fcU]

/-- The cost incurred by agent `i` under an assignment written out as eight explicit
choices. -/
def costOf (w : Fin 8 → ℕ) (i : Fin 3) (a b c d e f g h : Fin 3) : ℕ :=
  (if a = i then w 0 else 0) + (if b = i then w 1 else 0) + (if c = i then w 2 else 0) +
  (if d = i then w 3 else 0) + (if e = i then w 4 else 0) + (if f = i then w 5 else 0) +
  (if g = i then w 6 else 0) + (if h = i then w 7 else 0)

set_option maxRecDepth 40000 in
/-- The exhaustive check over all `3^8` assignments: in every assignment of the eight chores
to the three agents, one of them incurs a cost of at least `380` (i.e. `19` before the
scaling by `20`). -/
theorem core8C : ∀ a b c d e f g h : Fin 3,
    380 ≤ costOf fcR 0 a b c d e f g h ∨ 380 ≤ costOf fcC 1 a b c d e f g h ∨
      380 ≤ costOf fcU 2 a b c d e f g h := by decide

/-- **The Feige–Norkin negative example for chores.**  For every allocation of the eight
chores to the three agents, some agent `i` incurs a cost of at least `380`, that is, at least
`19/18` of her target `360`. -/
theorem feigeNorkinChores_core (f : Fin 8 → Fin 3) :
    ∃ i : Fin 3, 380 ≤ (∑ j, if f j = i then fcW i j else 0) := by
  have h := core8C (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  simp only [costOf] at h
  rcases h with h | h | h
  · exact ⟨0, by simpa [fcW, Fin.sum_univ_eight] using h⟩
  · exact ⟨1, by simpa [fcW, Fin.sum_univ_eight] using h⟩
  · exact ⟨2, by simpa [fcW, Fin.sum_univ_eight] using h⟩

/-- Version of `feigeNorkinChores_core` for three bundles covering all the chores (chores,
unlike goods, must all be allocated — collective outsourcing is accounted for in the third
bundle). -/
theorem feigeNorkinChores_cover (A : Fin 3 → Finset (Fin 8))
    (hcov : ∀ j : Fin 8, j ∈ A 0 ∨ j ∈ A 1 ∨ j ∈ A 2) :
    ∃ i : Fin 3, 380 ≤ ∑ j ∈ A i, fcW i j := by
  classical
  set f : Fin 8 → Fin 3 := fun j => if j ∈ A 0 then 0 else if j ∈ A 1 then 1 else 2 with hf
  have hsub : ∀ i, Finset.univ.filter (fun j => f j = i) ⊆ A i := by
    intro i j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases h0 : j ∈ A 0
    · have : f j = 0 := by simp [hf, h0]
      rw [this] at hj; rw [← hj]; exact h0
    · by_cases h1 : j ∈ A 1
      · have : f j = 1 := by simp [hf, h0, h1]
        rw [this] at hj; rw [← hj]; exact h1
      · have h2 : j ∈ A 2 := by rcases hcov j with h | h | h <;> tauto
        have : f j = 2 := by simp [hf, h0, h1]
        rw [this] at hj; rw [← hj]; exact h2
  obtain ⟨i, hi⟩ := feigeNorkinChores_core f
  refine ⟨i, le_trans hi ?_⟩
  have hrw : (∑ j, if f j = i then fcW i j else 0)
      = ∑ j ∈ Finset.univ.filter (fun j => f j = i), fcW i j := by
    rw [Finset.sum_filter]
  rw [hrw]
  exact Finset.sum_le_sum_of_subset (hsub i)

/-! ### The cost data of the instance -/

/-- Agent `R` can split the chores into three bundles costing `360` each, so her maximin
share is `360` (i.e. `18` before scaling). -/
theorem fcR_partition :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fcR j) = 360 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Agent `C` can split the chores into three bundles costing `360` each. -/
theorem fcC_partition :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fcC j) = 360 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The total cost of all chores for agent `U` is `1080`, so her proportional share is
`360`. -/
theorem fcU_total : (∑ j, fcU j) = 1080 := by decide

/-- The total cost of all chores for agent `R` is `1080`. -/
theorem fcR_total : (∑ j, fcR j) = 1080 := by decide

/-- The total cost of all chores for agent `C` is `1080`. -/
theorem fcC_total : (∑ j, fcC j) = 1080 := by decide

/-- Twice agent `U`'s cost dominates the costs of the two other agents, chore by chore: this
is what makes outsourcing at prices proportional to `cU` (with a large factor) useless for
agents `R` and `C`. -/
theorem two_fcU_dominates : ∀ j : Fin 8, fcR j ≤ 2 * fcU j ∧ fcC j ≤ 2 * fcU j := by decide

end FeigeNorkinChores

end FairChores
