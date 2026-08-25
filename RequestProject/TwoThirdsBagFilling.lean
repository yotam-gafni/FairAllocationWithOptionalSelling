import Mathlib

/-!
# Bag filling with bounded items

The proof of Proposition 6 of the manuscript (the construction of a canonical partition when
`|L′| ≤ n′ + 1`) rests on a *bag filling* procedure: goods whose individual value is at most `ε`
are poured into a bag until the bag reaches the threshold `τ`, at which point the bag is closed
and the procedure moves on to the next bag.  Since the last good added is worth at most `ε`, a
closed bag is worth at most `τ + ε`, so each bag consumes at most `τ + ε` of the available value.
Consequently a supply of `k · (τ + ε)` suffices for `k` bags.

This file proves that statement in the abstract:

* `exists_minimal_subset_sum` — from any set whose total value reaches `τ` one can pass to a
  subset that reaches `τ` but drops below it as soon as any of its elements is removed;
* `exists_bags` — if every element of `A` is worth at most `ε` and `A` is worth at least
  `k · (τ + ε)`, then `A` contains `k` pairwise disjoint bags, each worth between `τ` and
  `τ + ε`.

With `τ = ρ · MMSᵢ` and `ε = (1 − ρ) · MMSᵢ` (so `τ + ε = MMSᵢ`) this is exactly the bag filling
step of Proposition 6 applied to the cheap goods `C′`.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [DecidableEq G]

/-- From any finite set whose total `f`-value reaches `τ`, one can pass to a subset that still
reaches `τ` but drops below `τ` as soon as any single element is removed. -/
theorem exists_minimal_subset_sum (f : G → ℝ) (τ : ℝ) :
    ∀ A : Finset G, τ ≤ ∑ g ∈ A, f g →
      ∃ B ⊆ A, τ ≤ ∑ g ∈ B, f g ∧ ∀ e ∈ B, ∑ g ∈ B.erase e, f g < τ := by
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro hA
    by_cases hex : ∃ e ∈ A, τ ≤ ∑ g ∈ A.erase e, f g
    · obtain ⟨e, he, hle⟩ := hex
      obtain ⟨B, hBsub, h1, h2⟩ := ih (A.erase e) (Finset.erase_ssubset he) hle
      exact ⟨B, hBsub.trans (Finset.erase_subset _ _), h1, h2⟩
    · push_neg at hex
      exact ⟨A, Finset.Subset.refl _, hA, hex⟩

/-- A minimal bag is worth at most `τ + ε` when every element is worth at most `ε`. -/
theorem minimal_bag_le {f : G → ℝ} {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) {B : Finset G}
    (hsmall : ∀ g ∈ B, f g ≤ ε) (hge : τ ≤ ∑ g ∈ B, f g)
    (hmin : ∀ e ∈ B, ∑ g ∈ B.erase e, f g < τ) :
    ∑ g ∈ B, f g ≤ τ + ε := by
  rcases Finset.eq_empty_or_nonempty B with rfl | ⟨e, he⟩
  · simp only [Finset.sum_empty] at hge ⊢
    linarith
  · have hsplit : ∑ g ∈ B, f g = f e + ∑ g ∈ B.erase e, f g := (Finset.add_sum_erase B f he).symm
    have h1 := hmin e he
    have h2 := hsmall e he
    linarith

/-- **Bag filling.**  If every good of `A` is worth at most `ε` and `A` is worth at least
`k · (τ + ε)`, then `A` contains `k` pairwise disjoint bags, each worth at least `τ` and at most
`τ + ε`. -/
theorem exists_bags (f : G → ℝ) (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    ∀ (k : ℕ) (A : Finset G), (∀ g ∈ A, f g ≤ ε) → (k : ℝ) * (τ + ε) ≤ ∑ g ∈ A, f g →
      ∃ B : Fin k → Finset G, (∀ j, B j ⊆ A) ∧
        (∀ j j', j ≠ j' → Disjoint (B j) (B j')) ∧
        (∀ j, τ ≤ ∑ g ∈ B j, f g) ∧ (∀ j, ∑ g ∈ B j, f g ≤ τ + ε) := by
  intro k
  induction k with
  | zero =>
    intro A _ _
    exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0⟩
  | succ k ih =>
    intro A hsmall htotal
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hτε : τ ≤ ∑ g ∈ A, f g := by
      have : (1 : ℝ) * (τ + ε) ≤ ((k : ℝ) + 1) * (τ + ε) := by
        have : (0 : ℝ) ≤ τ + ε := by linarith
        nlinarith
      push_cast at htotal
      linarith
    obtain ⟨B₀, hB₀sub, hB₀ge, hB₀min⟩ := exists_minimal_subset_sum f τ A hτε
    have hB₀le : ∑ g ∈ B₀, f g ≤ τ + ε :=
      minimal_bag_le hτ hε (fun g hg => hsmall g (hB₀sub hg)) hB₀ge hB₀min
    have hrest : ∑ g ∈ A \ B₀, f g = (∑ g ∈ A, f g) - ∑ g ∈ B₀, f g := by
      rw [Finset.sum_sdiff_eq_sub hB₀sub]
    have hrestge : (k : ℝ) * (τ + ε) ≤ ∑ g ∈ A \ B₀, f g := by
      push_cast at htotal
      rw [hrest]
      nlinarith
    obtain ⟨B, hBsub, hBdisj, hBge, hBle⟩ :=
      ih (A \ B₀) (fun g hg => hsmall g (Finset.mem_sdiff.mp hg).1) hrestge
    refine ⟨Fin.cases B₀ B, ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hB₀sub
      · intro j'
        simpa using (hBsub j').trans Finset.sdiff_subset
    · intro j j'
      refine Fin.cases ?_ ?_ j
      · refine Fin.cases ?_ ?_ j'
        · intro hne; exact absurd rfl hne
        · intro j₂ _
          simp only [Fin.cases_zero, Fin.cases_succ]
          exact Finset.disjoint_left.mpr (fun x hx hx' =>
            (Finset.mem_sdiff.mp (hBsub j₂ hx')).2 hx)
      · intro j₁
        refine Fin.cases ?_ ?_ j'
        · intro _
          simp only [Fin.cases_zero, Fin.cases_succ]
          exact Finset.disjoint_left.mpr (fun x hx hx' =>
            (Finset.mem_sdiff.mp (hBsub j₁ hx)).2 hx')
        · intro j₂ hne
          simp only [Fin.cases_succ]
          exact hBdisj j₁ j₂ (fun h => hne (congrArg Fin.succ h))
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hB₀ge
      · intro j'; simpa using hBge j'
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hB₀le
      · intro j'; simpa using hBle j'

end FairSelling
