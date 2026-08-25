import Mathlib
import RequestProject.MatchingPhase

/-!
# Splitting an MMS configuration after a few goods have been removed

The manuscript's loss analysis (Lemma 4 and the preliminary phase) always follows the same
pattern: the agent has a three-part MMS configuration `A₀, A₁, A₂` together with a force-sold set
`s` whose proceeds are split by `q`; a small set `X` of goods is taken away from the pool (and
possibly some cash `c` is banked in return); the agent then has to rebuild *two* bundles worth
`τ` from what is left.

This file isolates that pattern.  One part `A j` is kept on its own, the other two are merged, and
the force-sold goods that survive are sold again; the only thing that has to be checked in each
application is a *budget inequality* saying that the surviving money suffices to top both bundles
up to `τ`.  `MMS2_cash_of_config_split` performs the construction, and the accompanying bounds
lemmas express the value of the two bundles and of the surviving money in terms of the
configuration data, so that each application reduces to linear arithmetic.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] in
/-- Removing a set from a bundle removes exactly the value of the intersection. -/
lemma vbarSum_sdiff_inter (w p : G → ℝ) (Y X : Finset G) :
    vbarSum w p (Y \ X) = vbarSum w p Y - vbarSum w p (Y ∩ X) := by
  have h : Y \ X = Y \ (Y ∩ X) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [h, vbarSum_sdiff w p Finset.inter_subset_left]

omit [Fintype G] [DecidableEq G] in
/-- Prices are dominated by `v̄`. -/
lemma sum_price_le_vbarSum (w p : G → ℝ) (Y : Finset G) :
    ∑ g ∈ Y, p g ≤ vbarSum w p Y :=
  Finset.sum_le_sum (fun _ _ => le_max_left _ _)

omit [Fintype G] [DecidableEq G] in
/-- `v̄` of a bundle is non-negative. -/
lemma vbarSum_nonneg' (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (Y : Finset G) :
    0 ≤ vbarSum w p Y :=
  Finset.sum_nonneg (fun g _ => le_trans (hw g) (le_max_right _ _))

omit [Fintype G] in
/-- If at most two goods are removed, one of the three parts of a configuration is untouched. -/
lemma exists_part_disjoint (A : Fin 3 → Finset G)
    (hA : ∀ i j : Fin 3, i ≠ j → Disjoint (A i) (A j))
    (X : Finset G) (hX : X.card ≤ 2) : ∃ j : Fin 3, Disjoint (A j) X := by
  classical
  by_contra hcon
  push_neg at hcon
  choose g hg1 hg2 using fun j => Finset.not_disjoint_iff.mp (hcon j)
  have hinj : Set.InjOn g (Finset.univ : Finset (Fin 3)) := by
    intro i _ j _ hij
    by_contra hne
    exact (Finset.disjoint_left.mp (hA i j hne)) (hg1 i) (hij ▸ hg1 j)
  have hcard : (Finset.univ : Finset (Fin 3)).card ≤ X.card :=
    Finset.card_le_card_of_injOn g (fun j _ => hg2 j) hinj
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-! ## Bounds attached to a configuration split -/

variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

/-- The value of a single surviving part. -/
lemma config_part_sdiff_ge (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    (j : Fin 3) :
    r - q j - vbarSum w p (A j ∩ X) ≤ vbarSum w p (A j \ X) := by
  have h := hcfg.2.2.2.2.2 j
  rw [vbarSum_sdiff_inter]
  linarith

/-- The value of the two merged surviving parts. -/
lemma config_two_parts_sdiff_ge (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    {j' j'' : Fin 3} (h : j' ≠ j'') :
    2 * r - q j' - q j'' - vbarSum w p ((A j' ∪ A j'') ∩ X)
      ≤ vbarSum w p ((A j' ∪ A j'') \ X) := by
  have h1 := hcfg.2.2.2.2.2 j'
  have h2 := hcfg.2.2.2.2.2 j''
  have hu : vbarSum w p (A j' ∪ A j'') = vbarSum w p (A j') + vbarSum w p (A j'') :=
    vbarSum_union w p (hcfg.1 j' j'' h)
  rw [vbarSum_sdiff_inter, hu]
  linarith

/-- A cruder bound for the merged bundle: it contains one of the two parts. -/
lemma config_merged_ge_one (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hcfg : ConfigN 3 w p r A s q)
    (X : Finset G) {j' j'' k : Fin 3} (hk : k = j' ∨ k = j'') :
    r - q k - vbarSum w p (A k ∩ X) ≤ vbarSum w p ((A j' ∪ A j'') \ X) := by
  have hsub : A k \ X ⊆ (A j' ∪ A j'') \ X := by
    refine Finset.sdiff_subset_sdiff ?_ (le_refl X)
    rcases hk with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have hmono : vbarSum w p (A k \ X) ≤ vbarSum w p ((A j' ∪ A j'') \ X) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun g _ _ => le_trans (hw g) (le_max_right _ _))
  have := config_part_sdiff_ge w p hcfg X k
  linarith

/-- The proceeds of the force-sold goods that survive. -/
lemma config_sold_sdiff (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G) :
    ∑ g ∈ s \ X, p g = (∑ i, q i) - ∑ g ∈ s ∩ X, p g := by
  have h : s \ X = s \ (s ∩ X) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [h, Finset.sum_sdiff_eq_sub Finset.inter_subset_left, hcfg.2.2.2.2.1]

/-- The three parts and the force-sold set carve `X` up, so the losses they suffer add up to at
most the value of `X`. -/
lemma config_loss_le (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    {j j' j'' : Fin 3} (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j'') :
    vbarSum w p (A j ∩ X) + vbarSum w p ((A j' ∪ A j'') ∩ X) + ∑ g ∈ s ∩ X, p g
      ≤ vbarSum w p X := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, -⟩ := hcfg
  have hmem : ∀ x : G, x ∈ s ∨ x ∈ A j ∨ x ∈ A j' ∨ x ∈ A j'' := by
    intro x
    have hx : x ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with h | h
    · exact Or.inl h
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      rcases fin3_cover h1 h2 h3 i with rfl | rfl | rfl
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hi))
      · exact Or.inr (Or.inr (Or.inr hi))
  have hsplit : X = (A j ∩ X) ∪ ((A j' ∪ A j'') ∩ X) ∪ (s ∩ X) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hx
      rcases hmem x with h | h | h | h
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl (Or.inl ⟨h, hx⟩)
      · exact Or.inl (Or.inr ⟨Or.inl h, hx⟩)
      · exact Or.inl (Or.inr ⟨Or.inr h, hx⟩)
    · rintro ((⟨-, hx⟩ | ⟨-, hx⟩) | ⟨-, hx⟩) <;> exact hx
  have hd1 : Disjoint (A j ∩ X) ((A j' ∪ A j'') ∩ X) := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxj := (Finset.mem_inter.mp hx).1
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx').1 with h | h
    · exact (Finset.disjoint_left.mp (hdisjA j j' h1)) hxj h
    · exact (Finset.disjoint_left.mp (hdisjA j j'' h2)) hxj h
  have hd2 : Disjoint ((A j ∩ X) ∪ ((A j' ∪ A j'') ∩ X)) (s ∩ X) := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxs := (Finset.mem_inter.mp hx').1
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.disjoint_left.mp (hdisjs j)) hxs (Finset.mem_inter.mp h).1
    · rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with h' | h'
      · exact (Finset.disjoint_left.mp (hdisjs j')) hxs h'
      · exact (Finset.disjoint_left.mp (hdisjs j'')) hxs h'
  have hle := sum_price_le_vbarSum w p (s ∩ X)
  have hval : vbarSum w p X
      = vbarSum w p (A j ∩ X) + vbarSum w p ((A j' ∪ A j'') ∩ X) + vbarSum w p (s ∩ X) := by
    conv_lhs => rw [hsplit]
    rw [vbarSum_union w p hd2, vbarSum_union w p hd1]
  linarith

/-! ## The split construction -/

/-- **Rebuilding two bundles from a configuration.**  Keep the part `A j` on its own, merge the
other two parts, sell whatever survives of the force-sold set, and use the banked cash `c`
together with the proceeds to top both bundles up to `τ`.  The only thing to check is that the
money suffices. -/
lemma MMS2_cash_of_config_split (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hcfg : ConfigN 3 w p r A s q) (X : Finset G) (c τ : ℝ) (hc : 0 ≤ c)
    {j j' j'' : Fin 3} (h1 : j ≠ j') (h2 : j ≠ j'')
    (hbudget : max 0 (τ - vbarSum w p (A j \ X)) + max 0 (τ - vbarSum w p ((A j' ∪ A j'') \ X))
      ≤ c + ∑ g ∈ s \ X, p g) :
    τ ≤ MMS 2 (cashVal (Finset.univ \ X) w) (cashPrice (Finset.univ \ X) p c) := by
  classical
  obtain ⟨hdisjA, hdisjs, -⟩ := hcfg
  refine MMS2_cash_of_two_bundles_sell w p hw hp (Finset.univ \ X) (A j \ X)
    ((A j' ∪ A j'') \ X) (s \ X) c
    (max 0 (τ - vbarSum w p (A j \ X))) (max 0 (τ - vbarSum w p ((A j' ∪ A j'') \ X))) τ
    ?_ ?_ ?_ ?_ ?_ ?_ hc (le_max_left _ _) (le_max_left _ _) hbudget ?_ ?_
  · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxj := (Finset.mem_sdiff.mp hx).1
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx').1 with h | h
    · exact (Finset.disjoint_left.mp (hdisjA j j' h1)) hxj h
    · exact (Finset.disjoint_left.mp (hdisjA j j'' h2)) hxj h
  · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    exact (Finset.disjoint_left.mp (hdisjs j)) (Finset.mem_sdiff.mp hx').1
      (Finset.mem_sdiff.mp hx).1
  · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxs := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1 with h | h
    · exact (Finset.disjoint_left.mp (hdisjs j')) hxs h
    · exact (Finset.disjoint_left.mp (hdisjs j'')) hxs h
  · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl X)
  · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl X)
  · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl X)
  · rcases le_or_gt τ (vbarSum w p (A j \ X)) with h | h
    · linarith [le_max_left (0 : ℝ) (τ - vbarSum w p (A j \ X))]
    · rw [max_eq_right (by linarith)]; linarith
  · rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h | h
    · linarith [le_max_left (0 : ℝ) (τ - vbarSum w p ((A j' ∪ A j'') \ X))]
    · rw [max_eq_right (by linarith)]; linarith

end FairSelling
