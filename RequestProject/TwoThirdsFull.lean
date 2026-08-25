import Mathlib
import RequestProject.TwoThirds
import RequestProject.LemmaTen

/-!
# Theorem 3 with a full allocation

`RequestProject.TwoThirds` produces a *valid* outcome (conditions (1) and (2) of the model:
disjointness, and no more money handed out than the sale proceeds).  The manuscript's model also
asks for condition (3): every good is either sold or allocated, and the proceeds are distributed
in full.  This file supplies the (routine) completion step and restates Theorem 3 in that form.

* `exists_full_of_valid` — every valid outcome can be completed to a full one without lowering
  anybody's utility: the goods that are neither sold nor allocated, and the undistributed part of
  the proceeds, are handed to the first agent.
* `exists_twothirds_MMS_full` — **Theorem 3 (general `n`), full-allocation form**.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-- **Completion of a valid outcome.**  Given a valid outcome, handing the unallocated goods and
the undistributed proceeds to the first agent yields a full allocation (every good sold or
allocated, and the proceeds distributed exactly) in which nobody's utility has decreased. -/
theorem exists_full_of_valid (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (o : Outcome G n) (ho : o.Valid p) :
    ∃ o' : Outcome G n, o'.Full p Finset.univ ∧ o'.sold = o.sold ∧
      ∀ i, util (v i) o i ≤ util (v i) o' i := by
  classical
  obtain ⟨hsold, hkept, hmoney0, hmoneysum⟩ := ho
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set L : Finset G := Finset.univ \ (o.sold ∪ Finset.univ.biUnion o.kept) with hL
  set kept' : Fin n → Finset G := Function.update o.kept i0 (o.kept i0 ∪ L) with hkept'
  set d : ℝ := (∑ g ∈ o.sold, p g) - ∑ j, o.money j with hd
  set money' : Fin n → ℝ := Function.update o.money i0 (o.money i0 + d) with hmoney'
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hLsold : Disjoint L o.sold :=
    Finset.disjoint_left.mpr fun g hg hg' =>
      (Finset.mem_sdiff.mp hg).2 (Finset.mem_union_left _ hg')
  have hLkept : ∀ k, Disjoint L (o.kept k) := fun k =>
    Finset.disjoint_left.mpr fun g hg hg' =>
      (Finset.mem_sdiff.mp hg).2
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hg'⟩))
  have hkeptsub : ∀ k, o.kept k ⊆ kept' k := by
    intro k
    by_cases hk : k = i0
    · subst hk
      simp only [hkept', Function.update_self]
      exact Finset.subset_union_left
    · simp only [hkept', Function.update_of_ne hk]
      exact Finset.Subset.refl _
  have hmem : ∀ k g, g ∈ kept' k → g ∈ o.kept k ∨ g ∈ L := by
    intro k g hg
    by_cases hk : k = i0
    · subst hk
      simp only [hkept', Function.update_self] at hg
      exact Finset.mem_union.mp hg
    · simp only [hkept', Function.update_of_ne hk] at hg
      exact Or.inl hg
  have hmoneyle : ∀ k, o.money k ≤ money' k := by
    intro k
    by_cases hk : k = i0
    · subst hk; simp only [hmoney', Function.update_self]; linarith
    · simp only [hmoney', Function.update_of_ne hk]
      exact le_refl _
  refine ⟨⟨o.sold, kept', money'⟩, ⟨⟨?_, ?_, ?_, ?_⟩, Finset.subset_univ _, ?_, ?_⟩, rfl, ?_⟩
  · -- sold is disjoint from every kept bundle
    intro k
    refine Finset.disjoint_left.mpr fun g hg hg' => ?_
    rcases hmem k g hg' with h | h
    · exact Finset.disjoint_left.mp (hsold k) hg h
    · exact Finset.disjoint_left.mp hLsold h hg
  · -- the kept bundles are pairwise disjoint
    intro j k hjk
    refine Finset.disjoint_left.mpr fun g hg hg' => ?_
    rcases hmem j g hg with h | h
    · rcases hmem k g hg' with h' | h'
      · exact Finset.disjoint_left.mp (hkept j k hjk) h h'
      · exact Finset.disjoint_left.mp (hLkept j) h' h
    · -- `g ∈ L`, so `g` lies in no original bundle; but then `g ∈ L` forces `j = k = i0`
      have hj : j = i0 := by
        by_contra hj
        simp only [hkept', Function.update_of_ne hj] at hg
        exact Finset.disjoint_left.mp (hLkept j) h hg
      have hk : k = i0 := by
        by_contra hk
        simp only [hkept', Function.update_of_ne hk] at hg'
        exact Finset.disjoint_left.mp (hLkept k) h hg'
      exact hjk (hj.trans hk.symm)
  · intro k; exact le_trans (hmoney0 k) (hmoneyle k)
  · have : ∑ j, money' j = ∑ g ∈ o.sold, p g := by
      rw [hmoney', Finset.sum_update_of_mem (Finset.mem_univ i0)]
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ ({i0} : Finset (Fin n))),
        Finset.sum_singleton, hd]
      ring
    exact le_of_eq this
  · -- every good is sold or allocated
    refine Finset.eq_univ_of_forall fun g => ?_
    by_cases hg : g ∈ o.sold ∪ Finset.univ.biUnion o.kept
    · rcases Finset.mem_union.mp hg with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hkeptsub k hk⟩)
    · have hgL : g ∈ L := Finset.mem_sdiff.mpr ⟨Finset.mem_univ g, hg⟩
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, ?_⟩)
      simp only [hkept', Function.update_self]
      exact Finset.mem_union_right _ hgL
  · rw [hmoney', Finset.sum_update_of_mem (Finset.mem_univ i0)]
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ ({i0} : Finset (Fin n))),
      Finset.sum_singleton, hd]
    ring
  · intro i
    have h1 : ∑ g ∈ o.kept i, v i g ≤ ∑ g ∈ kept' i, v i g :=
      Finset.sum_le_sum_of_subset_of_nonneg (hkeptsub i) (fun g _ _ => hv i g)
    have h2 := hmoneyle i
    simp only [util]
    linarith

/-- **Theorem 3 (general `n`), full-allocation form.**  Every allocation instance with optional
selling admits a *full* allocation — every good is either sold or handed to an agent, and the
sale proceeds are distributed in full — giving every agent at least `2/3` of its maximin share. -/
theorem exists_twothirds_MMS_full (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Full p Finset.univ ∧
      ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by
  obtain ⟨o, hvalid, ho⟩ := exists_twothirds_MMS v p hn hv hp
  obtain ⟨o', hfull, _, hle⟩ := exists_full_of_valid v p hn hv o hvalid
  exact ⟨o', hfull, fun i => (ho i).trans (hle i)⟩

end FairSelling
