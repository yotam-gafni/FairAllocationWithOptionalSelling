import Mathlib
import RequestProject.LemmaFourResidual

/-!
# The preliminary phase, and the unconditional three-agent theorem

The manuscript's algorithm starts with a *preliminary phase* whose purpose is to remove the goods
that are too valuable, so that afterwards `v̄ᵢ(g) < 3/4 · MMSᵢ` holds for every remaining agent `i`
and good `g` (the manuscript's Proposition 4).  For `n = 3` a single round of the preliminary
phase already removes one agent, and the two survivors can be served by the two-agent algorithm:

* **Stage 1.**  Some good `e` has price `p e ≥ 3/4 · MMSᵢ` for some agent `i`.  The good is sold,
  the agent `j` of *lowest* maximin share is paid `3/4 · MMSⱼ` and leaves; the unused proceeds are
  banked.
* **Stage 2.**  No good is that expensive but some agent `i` values a good `e` at
  `v i e ≥ 3/4 · MMSᵢ`.  The good is handed to `i`, which leaves.

In both cases the two remaining agents lose access to a single good `e`, and possibly to at most
`3/4 · MMS` worth of sale proceeds.  `MMS2_cash_of_one_good_loss` shows that this is harmless:
each of them can still split what remains into two bundles worth `3/4 · MMS`.  This is the
manuscript's loss analysis for the loss types `ℓ₁` and `ℓ₂` in the preliminary phase.

Combining the two stages with the post-preliminary theorem
(`exists_threequarter_MMS_three_nobig'`) gives `exists_threequarter_MMS_three_final`: **every**
three-agent instance with non-negative additive valuations and non-negative prices admits a valid
outcome giving each agent at least `3/4` of its maximin share with selling.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- **A single good, and some money, taken out of the pool.**  Suppose one good `e` is removed
(sold or handed to somebody else), the cash `c` is banked, and the money `m ≤ p e` that has been
paid out is at most `3/4 · MMS`, the banked cash covering the rest of the price of `e`
(`p e ≤ c + m`).  Then the agent can still split the remaining goods and the banked cash into two
bundles worth `3/4 · MMS` each.

This covers both stages of the preliminary phase: stage 1 with `m = 3/4 · MMSⱼ` and
`c = p e - m`, and stage 2 with `m = p e` and `c = 0`. -/
theorem MMS2_cash_of_one_good_loss (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (e : G) (c m : ℝ) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hmτ : m ≤ (3 / 4 : ℝ) * MMS 3 w p) (hme : m ≤ p e) (hcm : p e ≤ c + m) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ {e}) w)
      (cashPrice (Finset.univ \ {e}) p c) := by
  classical
  set M : ℝ := MMS 3 w p with hM
  set τ : ℝ := (3 / 4 : ℝ) * M with hτ
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  set X : Finset G := {e} with hX
  obtain ⟨A, s, q, hcfg, -⟩ := exists_reduced_three w p hw hp
  have hq0 := hcfg.2.2.2.1
  have hqsum := hcfg.2.2.2.2.1
  have hT := config_sold_sdiff w p hcfg X
  by_cases hes : e ∈ s
  · -- The agent sells `e` itself: every part survives, only some proceeds are lost.
    have hXparts : ∀ k : Fin 3, A k ∩ X = ∅ := by
      intro k
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      obtain ⟨hxk, hxX⟩ := Finset.mem_inter.mp hx
      rw [hX, Finset.mem_singleton] at hxX
      exact (Finset.disjoint_left.mp (hcfg.2.1 k)) (hxX ▸ hes) hxk
    obtain ⟨j, -, hjmin⟩ :=
      Finset.exists_min_image (f := q) (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩
    obtain ⟨j', j'', hj', hj'', hj'j''⟩ := fin3_others j
    have hj1 : j ≠ j' := Ne.symm hj'
    have hj2 : j ≠ j'' := Ne.symm hj''
    have hPS : ∑ g ∈ s ∩ X, p g = p e := by
      have : s ∩ X = {e} := by
        rw [hX]
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hx⟩; exact hx
        · rintro rfl; exact ⟨hes, rfl⟩
      rw [this, Finset.sum_singleton]
    have hPSq : p e ≤ ∑ i, q i := by
      rw [hqsum]
      exact Finset.single_le_sum (f := p) (fun g _ => hp g) hes
    have hC := config_part_sdiff_ge w p hcfg X j
    have hD := config_two_parts_sdiff_ge w p hcfg X hj'j''
    have hLC : vbarSum w p (A j ∩ X) = 0 := by simp [hXparts j, vbarSum]
    have hLD : vbarSum w p ((A j' ∪ A j'') ∩ X) = 0 := by
      have : (A j' ∪ A j'') ∩ X = ∅ := by
        rw [Finset.union_inter_distrib_right, hXparts j', hXparts j'']
        simp
      simp [this, vbarSum]
    have hqj := hq0 j
    have hqj' := hq0 j'
    have hqj'' := hq0 j''
    have hmin' : q j ≤ q j' := hjmin j' (Finset.mem_univ j')
    have hmin'' : q j ≤ q j'' := hjmin j'' (Finset.mem_univ j'')
    have hsum3 : ∑ i, q i = q j + q j' + q j'' := fin3_sum hj1 hj2 hj'j'' q
    refine MMS2_cash_of_config_split w p hw hp hcfg X c τ hc hj1 hj2 ?_
    rw [hT, hPS]
    rcases le_or_gt τ (vbarSum w p (A j \ X)) with h1 | h1 <;>
      rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
  · -- The agent keeps `e` in one of its parts: the other two parts survive untouched.
    obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 3, e ∈ A i0 := by
      have he' : e ∈ s ∪ Finset.univ.biUnion A := by
        rw [hcfg.2.2.1]; exact Finset.mem_univ e
      rcases Finset.mem_union.mp he' with h | h
      · exact absurd h hes
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
        exact ⟨i, hi⟩
    have huntouched : ∀ k : Fin 3, k ≠ i0 → A k ∩ X = ∅ := by
      intro k hk
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      obtain ⟨hxk, hxX⟩ := Finset.mem_inter.mp hx
      rw [hX, Finset.mem_singleton] at hxX
      exact (Finset.disjoint_left.mp (hcfg.1 k i0 hk)) hxk (hxX ▸ hi0)
    obtain ⟨k1, k2, hk1, hk2, hk12⟩ := fin3_others i0
    obtain ⟨j', j'', hj', hj'', hj'j''⟩ := fin3_others k1
    have hj1 : k1 ≠ j' := Ne.symm hj'
    have hj2 : k1 ≠ j'' := Ne.symm hj''
    have hk2mem : k2 = j' ∨ k2 = j'' := by
      rcases fin3_cover hj1 hj2 hj'j'' k2 with h | h | h
      · exact absurd h (Ne.symm hk12)
      · exact Or.inl h
      · exact Or.inr h
    have hC := config_part_sdiff_ge w p hcfg X k1
    have hD := config_merged_ge_one w p hw hcfg X (j' := j') (j'' := j'') hk2mem
    have hLC : vbarSum w p (A k1 ∩ X) = 0 := by simp [huntouched k1 hk1, vbarSum]
    have hLD : vbarSum w p (A k2 ∩ X) = 0 := by simp [huntouched k2 hk2, vbarSum]
    have hPS : ∑ g ∈ s ∩ X, p g = 0 := by
      have : s ∩ X = ∅ := by
        rw [hX]
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
        obtain ⟨hxs, hxX⟩ := Finset.mem_inter.mp hx
        rw [Finset.mem_singleton] at hxX
        exact hes (hxX ▸ hxs)
      rw [this, Finset.sum_empty]
    have hqk1 := hq0 k1
    have hqk2 := hq0 k2
    have hqsum3 : q k1 + q k2 ≤ ∑ i, q i := by
      have hsum3 : ∑ i, q i = q i0 + q k1 + q k2 :=
        fin3_sum (Ne.symm hk1) (Ne.symm hk2) hk12 q
      have := hq0 i0
      linarith
    refine MMS2_cash_of_config_split w p hw hp hcfg X c τ hc hj1 hj2 ?_
    rw [hT, hPS]
    rcases le_or_gt τ (vbarSum w p (A k1 \ X)) with h1 | h1 <;>
      rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith

/-- Removing a single good, written with the `K ∪ S` shape used by the composition lemma. -/
lemma MMS2_cash_of_one_good_loss' (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (K S : Finset G) (e : G) (hKS : K ∪ S = {e}) (c m : ℝ) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hmτ : m ≤ (3 / 4 : ℝ) * MMS 3 w p) (hme : m ≤ p e) (hcm : p e ≤ c + m) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
      (cashPrice (Finset.univ \ (K ∪ S)) p c) := by
  rw [hKS]
  exact MMS2_cash_of_one_good_loss w p hw hp e c m hc hm0 hmτ hme hcm

/-! ## The two stages of the preliminary phase -/

/-- **Stage 1 of the preliminary phase.**  If some good is worth (in price!) at least
`3/4 · MMS` to some agent, then a complete `3/4`-MMS allocation exists: sell that good, pay the
agent of least maximin share, and let the other two agents share the rest. -/
theorem preliminary_stage_one (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (i0 : Fin 3) (e : G) (hbig : (3 / 4 : ℝ) * MMS 3 (v i0) p ≤ p e) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨a, -, hmin⟩ := Finset.exists_min_image (f := fun i => MMS 3 (v i) p)
    (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩
  obtain ⟨b, d, hba, hda, hbd⟩ := fin3_others a
  have hma0 : 0 ≤ (3 / 4 : ℝ) * MMS 3 (v a) p := by
    have := MMS_nonneg (n := 3) (by norm_num) (v a) p (hv a) hp
    linarith
  have hmae : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ p e := by
    have := hmin i0 (Finset.mem_univ i0)
    linarith
  have hunion : (∅ : Finset G) ∪ ({e} : Finset G) = {e} := Finset.empty_union _
  have hsum : ∑ g ∈ ({e} : Finset G), p g = p e := Finset.sum_singleton _ _
  refine finish_from_cash_reduction v p hv hp a b d (Ne.symm hba) (Ne.symm hda) hbd
    ∅ {e} ((3 / 4 : ℝ) * MMS 3 (v a) p) (p e - (3 / 4 : ℝ) * MMS 3 (v a) p)
    (Finset.disjoint_empty_left _) hma0 (by linarith) (by rw [hsum]; linarith) ?_ ?_ ?_
  · simp [vbarSum]
  · exact MMS2_cash_of_one_good_loss' (v b) p (hv b) hp ∅ {e} e hunion _ _
      (by linarith) hma0 (by linarith [hmin b (Finset.mem_univ b)]) hmae (by linarith)
  · exact MMS2_cash_of_one_good_loss' (v d) p (hv d) hp ∅ {e} e hunion _ _
      (by linarith) hma0 (by linarith [hmin d (Finset.mem_univ d)]) hmae (by linarith)

/-- **Stage 2 of the preliminary phase.**  If no good is expensive but some agent values a good at
`3/4 · MMS` or more, hand that good to that agent; the other two share the rest. -/
theorem preliminary_stage_two (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hcheap : ∀ i g, p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (e : G) (hbig : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ v a e) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨b, d, hba, hda, hbd⟩ := fin3_others a
  have hunion : ({e} : Finset G) ∪ (∅ : Finset G) = {e} := Finset.union_empty _
  refine finish_from_cash_reduction v p hv hp a b d (Ne.symm hba) (Ne.symm hda) hbd
    {e} ∅ 0 0 (Finset.disjoint_empty_right _) le_rfl le_rfl (by simp) ?_ ?_ ?_
  · simp only [vbarSum, Finset.sum_singleton, vbar, add_zero]
    exact le_trans hbig (le_max_right _ _)
  · exact MMS2_cash_of_one_good_loss' (v b) p (hv b) hp {e} ∅ e hunion 0 (p e) le_rfl (hp e)
      (hcheap b e).le le_rfl (by linarith)
  · exact MMS2_cash_of_one_good_loss' (v d) p (hv d) hp {e} ∅ e hunion 0 (p e) le_rfl (hp e)
      (hcheap d e).le le_rfl (by linarith)

end FairSelling
