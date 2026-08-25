import Mathlib

/-!
# The Feige–Norkin three-agent instance

This file formalizes the purely combinatorial core of the negative example of
Feige and Norkin that the manuscript invokes for its `11/12` gap for `n = 3`
(Proposition 1): an instance with three agents and eight indivisible goods in which,
in *every* allocation, some agent receives at most `11/12` of her target value.

The original instance has nine goods, the first of which is worth `0` to everybody, so
it is dropped here; the eight remaining goods carry the values

```
vR = 6, 6, 10, 1, 1, 4, 4, 4
vC = 7+1/3, 6+2/3, 8+1/3, 1, 1+2/3, 3+2/3, 3+2/3, 3+2/3
vU = 7+1/3, 7+1/3, 10+1/3, 0, 0, 3+2/3, 3+2/3, 3+2/3
```

each summing to `36`, so that the target value of every agent (the maximin share for the
first two, the proportional share for the third) is `12`.  To stay inside exact integer
arithmetic all three valuations are scaled by `3`; the target then becomes `36` and the
claim is that some agent gets at most `33 = (11/12) * 36`.

Main results:

* `feigeNorkin_core` — for every assignment of the eight goods to the three agents, some
  agent `i` gets a bundle of `fnW i`-value at most `33`;
* `feigeNorkin_disjoint` — the same for pairwise disjoint bundles (goods may be left out);
* `fnR_partition`, `fnC_partition`, `fnU_total` — the value data: agents `R` and `C` can
  split the goods into three bundles of value `36` each, and the total value for `U` is
  `108 = 3 * 36`.
-/

open scoped BigOperators

namespace FairSelling

namespace FeigeNorkin

/-- Valuation of the first agent (`vR` of the construction), scaled by `3`. -/
def fnR : Fin 8 → ℕ := ![18, 18, 30, 3, 3, 12, 12, 12]

/-- Valuation of the second agent (`vC` of the construction), scaled by `3`. -/
def fnC : Fin 8 → ℕ := ![22, 20, 25, 3, 5, 11, 11, 11]

/-- Valuation of the third agent (`vU` of the construction), scaled by `3`. -/
def fnU : Fin 8 → ℕ := ![22, 22, 31, 0, 0, 11, 11, 11]

/-- The three valuations of the Feige–Norkin instance, scaled by `3`. -/
def fnW : Fin 3 → Fin 8 → ℕ := ![fnR, fnC, fnU]

/-- The value that agent `i` gets from the goods assigned to her by an assignment written
out as eight explicit choices. -/
def valOf (w : Fin 8 → ℕ) (i : Fin 3) (a b c d e f g h : Fin 3) : ℕ :=
  (if a = i then w 0 else 0) + (if b = i then w 1 else 0) + (if c = i then w 2 else 0) +
  (if d = i then w 3 else 0) + (if e = i then w 4 else 0) + (if f = i then w 5 else 0) +
  (if g = i then w 6 else 0) + (if h = i then w 7 else 0)

set_option maxRecDepth 40000 in
/-- The exhaustive check over all `3^8` assignments: in every assignment of the eight goods
to the three agents, one of them receives at most `33` (i.e. `11` before the scaling by `3`). -/
theorem core8 : ∀ a b c d e f g h : Fin 3,
    valOf fnR 0 a b c d e f g h ≤ 33 ∨ valOf fnC 1 a b c d e f g h ≤ 33 ∨
      valOf fnU 2 a b c d e f g h ≤ 33 := by decide

/-- **The Feige–Norkin negative example.**  For every allocation of the eight goods to the
three agents, some agent `i` receives a bundle worth at most `33`, that is, at most `11/12`
of her target value `36`. -/
theorem feigeNorkin_core (f : Fin 8 → Fin 3) :
    ∃ i : Fin 3, (∑ j, if f j = i then fnW i j else 0) ≤ 33 := by
  have h := core8 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  simp only [valOf] at h
  rcases h with h | h | h
  · exact ⟨0, by simpa [fnW, Fin.sum_univ_eight] using h⟩
  · exact ⟨1, by simpa [fnW, Fin.sum_univ_eight] using h⟩
  · exact ⟨2, by simpa [fnW, Fin.sum_univ_eight] using h⟩

/-- Version of `feigeNorkin_core` for pairwise disjoint bundles: goods may also be left
unallocated (in the model with selling, sold). -/
theorem feigeNorkin_disjoint (A : Fin 3 → Finset (Fin 8))
    (hA : ∀ i k, i ≠ k → Disjoint (A i) (A k)) :
    ∃ i : Fin 3, (∑ j ∈ A i, fnW i j) ≤ 33 := by
  classical
  set f : Fin 8 → Fin 3 := fun j => if j ∈ A 1 then 1 else if j ∈ A 2 then 2 else 0 with hf
  have hsub : ∀ i, A i ⊆ Finset.univ.filter (fun j => f j = i) := by
    intro i j hj
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi3 with rfl | rfl | rfl
    · have h1 : j ∉ A 1 := Finset.disjoint_left.1 (hA 0 1 (by decide)) hj
      have h2 : j ∉ A 2 := Finset.disjoint_left.1 (hA 0 2 (by decide)) hj
      simp [hf, h1, h2]
    · simp [hf, hj]
    · have h1 : j ∉ A 1 := Finset.disjoint_left.1 (hA 2 1 (by decide)) hj
      simp [hf, h1, hj]
  obtain ⟨i, hi⟩ := feigeNorkin_core f
  refine ⟨i, le_trans ?_ hi⟩
  have : (∑ j, if f j = i then fnW i j else 0)
      = ∑ j ∈ Finset.univ.filter (fun j => f j = i), fnW i j := by
    rw [Finset.sum_filter]
  rw [this]
  exact Finset.sum_le_sum_of_subset (hsub i)

/-- **The Feige–Norkin gap, in real-valued form.**  For any three pairwise disjoint bundles,
one of the three agents receives at most `11/12` of the common target value `36`
(i.e. `11` out of `12` before the scaling by `3`). -/
theorem feigeNorkin_gap (A : Fin 3 → Finset (Fin 8))
    (hA : ∀ i k, i ≠ k → Disjoint (A i) (A k)) :
    (∑ g ∈ A 0, (fnR g : ℝ)) ≤ (11/12) * 36 ∨
    (∑ g ∈ A 1, (fnC g : ℝ)) ≤ (11/12) * 36 ∨
    (∑ g ∈ A 2, (fnU g : ℝ)) ≤ (11/12) * 36 := by
  obtain ⟨i, hi⟩ := feigeNorkin_disjoint A hA
  have hcast : ∀ (s : Finset (Fin 8)) (w : Fin 8 → ℕ), (∑ g ∈ s, w g) ≤ 33 →
      (∑ g ∈ s, (w g : ℝ)) ≤ (11/12) * 36 := by
    intro s w h
    have : (∑ g ∈ s, (w g : ℝ)) ≤ (33 : ℕ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h
    norm_num at this ⊢
    linarith
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl
  · exact Or.inl (hcast _ _ (by simpa [fnW] using hi))
  · exact Or.inr (Or.inl (hcast _ _ (by simpa [fnW] using hi)))
  · exact Or.inr (Or.inr (hcast _ _ (by simpa [fnW] using hi)))

/-! ### The value data of the instance -/

/-- Agent `R` can split the goods into three bundles worth `36` each, so her maximin share
is `36` (i.e. `12` before scaling). -/
theorem fnR_partition :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fnR j) = 36 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Agent `C` can split the goods into three bundles worth `36` each. -/
theorem fnC_partition :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fnC j) = 36 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The total value of all goods for agent `U` is `108`, so her proportional share is `36`. -/
theorem fnU_total : (∑ j, fnU j) = 108 := by decide

/-- The total value of all goods for agent `R` is `108`. -/
theorem fnR_total : (∑ j, fnR j) = 108 := by decide

/-- The total value of all goods for agent `C` is `108`. -/
theorem fnC_total : (∑ j, fnC j) = 108 := by decide

end FeigeNorkin

end FairSelling
