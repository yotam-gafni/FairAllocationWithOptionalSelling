import Mathlib
import RequestProject.SmallN

/-!
# MMS existence for two agents

This file proves the manuscript's Theorem 1 (the MMS half): for two agents with additive
non-negative valuations and market prices, there is a valid outcome giving *every* agent at
least its maximin share (`exists_MMS_two`).

The proof follows the manuscript's *Cut & Give* strategy, formalised through the "unified"
picture developed in `RequestProject.SmallN` (`unifiedOutcome`): every agent has an MMS
partition of a canonical form in which at most one good is *split* (force-sold with its
proceeds shared between the two parts); all other goods are handed out in full and valued at
`v̄ = max p v`.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- A "unified" two-part configuration for a single valuation `w`: two disjoint groups `A 0`,
`A 1` of goods handed out in full (valued `v̄`), a set `s` of *split* (force-sold) goods with
their proceeds shared by the money vector `q`, covering all goods, and where every part is
worth at least `r`. -/
def Config (w p : G → ℝ) (r : ℝ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ) : Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint s (A i)) ∧
  (s ∪ Finset.univ.biUnion A = Finset.univ) ∧ (∀ i, 0 ≤ q i) ∧
  (∑ i, q i = ∑ g ∈ s, p g) ∧ (∀ i, r ≤ vbarSum w p (A i) + q i)

omit [Fintype G] [DecidableEq G] in
/-- Plain valuation of a bundle never exceeds its `v̄`-valuation. -/
lemma sum_le_vbarSum (w p : G → ℝ) (A : Finset G) : ∑ g ∈ A, w g ≤ vbarSum w p A :=
  Finset.sum_le_sum (fun _ _ => le_max_right _ _)

omit [Fintype G] in
lemma vbarSum_union (w p : G → ℝ) {A B : Finset G} (h : Disjoint A B) :
    vbarSum w p (A ∪ B) = vbarSum w p A + vbarSum w p B := by
  simp only [vbarSum]; rw [Finset.sum_union h]

/-- One reduction step: if the split set has at least two goods, we may move one of them into a
group, strictly decreasing the number of split goods while preserving all `Config` properties. -/
theorem reduce_step (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ)
    (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ)
    (hcfg : Config w p r A s q) (hcard : 2 ≤ s.card) :
    ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
      Config w p r A' s' q' ∧ s'.card < s.card := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hge⟩ := hcfg
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g, hgs, hgmin⟩ := s.exists_min_image p hne
  have hpg : 0 ≤ p g := hp g
  have hgA : ∀ k, g ∉ A k := fun k => Finset.disjoint_left.mp (hdisjs k) hgs
  have hsumbound : 2 * p g ≤ ∑ h ∈ s, p h := by
    calc 2 * p g ≤ (s.card : ℝ) * p g := by
          apply mul_le_mul_of_nonneg_right _ hpg; exact_mod_cast hcard
      _ = ∑ _h ∈ s, p g := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ h ∈ s, p h := Finset.sum_le_sum (fun h hh => hgmin h hh)
  have hq01 : q 0 + q 1 = ∑ h ∈ s, p h := by rw [← Fin.sum_univ_two q]; exact hsat
  have key : ∀ i j : Fin 2, i ≠ j → p g ≤ q i →
      ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
        Config w p r A' s' q' ∧ s'.card < s.card := by
    intro i j hij hqi
    have hk : ∀ k : Fin 2, k = i ∨ k = j := fun k => by omega
    refine ⟨Function.update A i (A i ∪ {g}), s.erase g, Function.update q i (q i - p g),
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Finset.card_erase_lt_of_mem hgs⟩
    · intro a b hab
      rcases hk a with ha | ha <;> rcases hk b with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · subst a; subst b
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Finset.disjoint_union_left]
        exact ⟨hdisjA i j hij, Finset.disjoint_singleton_left.mpr (hgA j)⟩
      · subst a; subst b
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Finset.disjoint_union_right]
        exact ⟨hdisjA j i (Ne.symm hij), Finset.disjoint_singleton_right.mpr (hgA j)⟩
      · exact absurd (ha.trans hb.symm) hab
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self, Finset.disjoint_union_right]
        refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) (hdisjs i), ?_⟩
        exact Finset.disjoint_singleton_right.mpr (fun h => (Finset.mem_erase.mp h).1 rfl)
      · rw [Function.update_of_ne hki]
        exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) (hdisjs k)
    · apply Finset.eq_univ_of_forall
      intro x
      have hx : x ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx ⊢
      rcases hx with hxs | ⟨k, hxk⟩
      · by_cases hxg : x = g
        · refine Or.inr ⟨i, ?_⟩
          rw [Function.update_self]
          exact Finset.mem_union_right _ (by rw [hxg]; exact Finset.mem_singleton_self g)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hxg, hxs⟩)
      · refine Or.inr ⟨k, ?_⟩
        by_cases hki : k = i
        · subst k; rw [Function.update_self]; exact Finset.mem_union_left _ hxk
        · rw [Function.update_of_ne hki]; exact hxk
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self]; linarith [hqi]
      · rw [Function.update_of_ne hki]; exact hq0 k
    · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_erase_eq_sub hgs]
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ ({i} : Finset (Fin 2))), Finset.sum_singleton]
      rw [hsat]; ring
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self, Function.update_self]
        have hvu : vbarSum w p (A i ∪ {g}) = vbarSum w p (A i) + vbarSum w p ({g} : Finset G) :=
          vbarSum_union w p (Finset.disjoint_singleton_right.mpr (hgA i))
        have hvg : vbarSum w p ({g} : Finset G) = max (p g) (w g) := by simp [vbarSum, vbar]
        rw [hvu, hvg]
        have hmax : p g ≤ max (p g) (w g) := le_max_left _ _
        have := hge i
        linarith
      · rw [Function.update_of_ne hki, Function.update_of_ne hki]
        exact hge k
  rcases (show p g ≤ q 0 ∨ p g ≤ q 1 by
      by_contra h; push_neg at h; obtain ⟨h0, h1⟩ := h; linarith [hsumbound, hq01]) with h0 | h1
  · exact key 0 1 (by decide) h0
  · exact key 1 0 (by decide) h1

/-- Iterating `reduce_step` we reach a configuration with at most one split good. -/
theorem reduce_to_one (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ),
      Config w p r A s q → s.card ≤ k →
      ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
        Config w p r A' s' q' ∧ s'.card ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro A s q hcfg hk
    exact ⟨A, s, q, hcfg, hk.trans (by norm_num)⟩
  | succ k ih =>
    intro A s q hcfg hk
    by_cases hc : s.card ≤ 1
    · exact ⟨A, s, q, hcfg, hc⟩
    · have h2 : 2 ≤ s.card := by omega
      obtain ⟨A', s', q', hcfg', hlt⟩ := reduce_step w p hp r A s q hcfg h2
      exact ih A' s' q' hcfg' (by omega)

/-- Existence of a canonical (at most one split good) MMS partition for one valuation. -/
theorem exists_reduced (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ),
      Config w p (MMS 2 w p) A s q ∧ s.card ≤ 1 := by
  obtain ⟨o, hovalid, hcover, hge⟩ := exists_MMS_partition (n := 2) (by norm_num) w p hw hp
  obtain ⟨hsold, hdisj, hmoney, hbudget⟩ := hovalid
  have hsum2 : ∑ j, o.money j = o.money 0 + o.money 1 := Fin.sum_univ_two _
  -- saturate the money: put the slack into part 0
  set slack : ℝ := (∑ g ∈ o.sold, p g) - o.money 0 - o.money 1 with hslack
  have hslack0 : 0 ≤ slack := by rw [hslack]; linarith [hbudget]
  have hcfg : Config w p (MMS 2 w p) o.kept o.sold ![o.money 0 + slack, o.money 1] := by
    refine ⟨fun i j hij => hdisj i j hij, fun i => hsold i, hcover, ?_, ?_, ?_⟩
    · rw [Fin.forall_fin_two]; constructor
      · simp only [Matrix.cons_val_zero]; linarith [hmoney 0]
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; exact hmoney 1
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hslack]; ring
    · rw [Fin.forall_fin_two]; constructor
      · simp only [Matrix.cons_val_zero]
        have h1 := hge 0; simp only [util] at h1
        linarith [sum_le_vbarSum w p (o.kept 0)]
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        have h1 := hge 1; simp only [util] at h1
        linarith [sum_le_vbarSum w p (o.kept 1)]
  exact reduce_to_one w p hp (MMS 2 w p) o.sold.card o.kept o.sold _ hcfg (le_refl _)

omit [Fintype G] in
lemma biU_two (A : Fin 2 → Finset G) : Finset.univ.biUnion A = A 0 ∪ A 1 := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Fin.exists_fin_two]

/-- From a two-part configuration in which both parts are worth at least `M`, twice `M` is
bounded by the total `v̄`-value of the kept goods plus the force-sale proceeds. -/
lemma config_sum_bound (w p : G → ℝ) (M : ℝ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ)
    (h : Config w p M A s q) : 2 * M ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g := by
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hge⟩ := h
  rw [biU_two A] at hcover
  have hAunion : A 0 ∪ A 1 = Finset.univ \ s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (hx | hx)
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 0) hxs hx
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 1) hxs hx
    · intro hxs
      have hmem : x ∈ s ∪ (A 0 ∪ A 1) := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hmem with h' | h'
      · exact absurd h' hxs
      · exact Finset.mem_union.mp h'
  have hvbar : vbarSum w p (A 0 ∪ A 1) = vbarSum w p (A 0) + vbarSum w p (A 1) :=
    vbarSum_union w p (hdisjA 0 1 (by decide))
  have hqsum : q 0 + q 1 = ∑ g ∈ s, p g := by rw [← Fin.sum_univ_two q]; exact hsat
  rw [← hAunion, hvbar]
  linarith [hge 0, hge 1, hqsum]

omit [Fintype G] in
lemma vbarSum_sdiff (w p : G → ℝ) {X Y : Finset G} (h : Y ⊆ X) :
    vbarSum w p (X \ Y) = vbarSum w p X - vbarSum w p Y := by
  simp only [vbarSum]; rw [Finset.sum_sdiff_eq_sub h]

/-- Swap the two parts of an outcome. -/
def swapOutcome (o : Outcome G 2) : Outcome G 2 where
  sold := o.sold
  kept := fun i => o.kept (Equiv.swap 0 1 i)
  money := fun i => o.money (Equiv.swap 0 1 i)

omit [Fintype G] [DecidableEq G] in
lemma util_swapOutcome (w : G → ℝ) (o : Outcome G 2) (j : Fin 2) :
    util w (swapOutcome o) j = util w o (Equiv.swap 0 1 j) := rfl

omit [Fintype G] [DecidableEq G] in
lemma swapOutcome_valid (p : G → ℝ) (o : Outcome G 2) (h : o.Valid p) :
    (swapOutcome o).Valid p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i => h1 _, fun i j hij => h2 _ _ (fun he => hij ((Equiv.swap 0 1).injective he)),
    fun i => h3 _, ?_⟩
  show ∑ i, o.money (Equiv.swap 0 1 i) ≤ _
  rw [Equiv.sum_comp (Equiv.swap 0 1) o.money]; exact h4

omit [Fintype G] in
/-- Realize a two-agent unified assignment (agent `0` gets `B0`, agent `1` gets `B1`, force-sale
set `F` split as `r0, r1`) as a concrete valid outcome with the stated utilities. -/
lemma realize2 (v : Fin 2 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (B0 B1 F : Finset G) (r0 r1 : ℝ)
    (hd01 : Disjoint B0 B1) (hdF0 : Disjoint F B0) (hdF1 : Disjoint F B1)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hsum : r0 + r1 ≤ ∑ g ∈ F, p g) :
    ∃ o : Outcome G 2, o.Valid p ∧
      util (v 0) o 0 = vbarSum (v 0) p B0 + r0 ∧
      util (v 1) o 1 = vbarSum (v 1) p B1 + r1 := by
  refine ⟨unifiedOutcome v p ![B0, B1] F ![r0, r1], ?_, ?_, ?_⟩
  · apply unifiedOutcome_valid v p hp
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hd01.symm]
    · intro i; fin_cases i <;> simpa using ‹_›
    · intro i; fin_cases i <;> simpa
    · rw [Fin.sum_univ_two]; simpa using hsum
  · rw [util_unifiedOutcome]; simp
  · rw [util_unifiedOutcome]; simp

/-- **Cut & Give** (the heart of the two-agent argument). If agent `0` (the *cutter*) has a
canonical MMS partition with a lower-priced split good than agent `1` (the *giver*), then there
is a valid outcome giving agent `0` at least `MMS0` and agent `1` at least `MMS1`. -/
lemma cutgive (v : Fin 2 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (Ac : Fin 2 → Finset G) (sc : Finset G) (qc : Fin 2 → ℝ)
    (hc : Config (v 0) p (MMS 2 (v 0) p) Ac sc qc)
    (sg : Finset G) (hsg : sg.card ≤ 1)
    (hbound : 2 * MMS 2 (v 1) p ≤ vbarSum (v 1) p (Finset.univ \ sg) + ∑ g ∈ sg, p g)
    (hcut : ∑ g ∈ sc, p g ≤ ∑ g ∈ sg, p g) :
    ∃ o : Outcome G 2, o.Valid p ∧
      MMS 2 (v 0) p ≤ util (v 0) o 0 ∧ MMS 2 (v 1) p ≤ util (v 1) o 1 := by
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hge⟩ := hc
  set M0 := MMS 2 (v 0) p
  set M1 := MMS 2 (v 1) p
  have hqsum : qc 0 + qc 1 = ∑ g ∈ sc, p g := by rw [← Fin.sum_univ_two qc]; exact hsat
  by_cases hCC : ∃ t : Fin 2, M1 ≤ vbarSum (v 1) p (Ac t) + qc t
  · obtain ⟨t, ht⟩ := hCC
    fin_cases t
    · obtain ⟨o, hov, h0, h1⟩ := realize2 v p hp (Ac 1) (Ac 0) sc (qc 1) (qc 0)
        (hdisjA 1 0 (by decide)) (hdisjs 1) (hdisjs 0) (hq0 1) (hq0 0)
        (by rw [add_comm]; exact le_of_eq hqsum)
      exact ⟨o, hov, by rw [h0]; exact hge 1, by rw [h1]; exact ht⟩
    · obtain ⟨o, hov, h0, h1⟩ := realize2 v p hp (Ac 0) (Ac 1) sc (qc 0) (qc 1)
        (hdisjA 0 1 (by decide)) (hdisjs 0) (hdisjs 1) (hq0 0) (hq0 1) (le_of_eq hqsum)
      exact ⟨o, hov, by rw [h0]; exact hge 0, by rw [h1]; exact ht⟩
  · push_neg at hCC
    have htex : ∃ t : Fin 2, Disjoint (Ac t) sg := by
      by_cases hd0 : Disjoint (Ac 0) sg
      · exact ⟨0, hd0⟩
      · refine ⟨1, ?_⟩
        rw [Finset.not_disjoint_iff] at hd0
        obtain ⟨x, hxA, hxs⟩ := hd0
        rw [Finset.disjoint_left]
        intro y hyA hys
        have hxy : x = y := Finset.card_le_one.mp hsg x hxs y hys
        subst hxy
        exact Finset.disjoint_left.mp (hdisjA 1 0 (by decide)) hyA hxA
    obtain ⟨t, htd⟩ := htex
    have hAtsub : Ac t ⊆ Finset.univ \ sg := Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, htd⟩
    have hqct_le : qc t ≤ ∑ g ∈ sg, p g := by
      have hle : qc t ≤ qc 0 + qc 1 := by
        rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> linarith [hq0 0, hq0 1]
      linarith [hqsum, hcut]
    obtain ⟨o, hov, h0, h1⟩ := realize2 v p hp (Ac t) ((Finset.univ \ Ac t) \ sg) sg
      (qc t) ((∑ g ∈ sg, p g) - qc t)
      (Finset.disjoint_left.mpr fun y hy hy2 =>
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy2).1).2 hy)
      htd.symm
      (Finset.disjoint_left.mpr fun y hy hy2 => (Finset.mem_sdiff.mp hy2).2 hy)
      (hq0 t) (by linarith [hqct_le]) (by linarith)
    refine ⟨o, hov, by rw [h0]; exact hge t, ?_⟩
    rw [h1]
    have hB1eq : (Finset.univ \ Ac t) \ sg = (Finset.univ \ sg) \ Ac t := sdiff_sdiff_comm
    have hvsdiff : vbarSum (v 1) p ((Finset.univ \ Ac t) \ sg)
        = vbarSum (v 1) p (Finset.univ \ sg) - vbarSum (v 1) p (Ac t) := by
      rw [hB1eq]; exact vbarSum_sdiff (v 1) p hAtsub
    rw [hvsdiff]
    linarith [hbound, hCC t]

/-- **MMS existence for two agents** (Theorem 1, MMS part). There is a valid outcome giving
each of the two agents at least its maximin share. -/
theorem exists_MMS_two (v : Fin 2 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 2, o.Valid p ∧ ∀ i, MMS 2 (v i) p ≤ util (v i) o i := by
  obtain ⟨Ac0, sc0, qc0, hcfg0, hcard0⟩ := exists_reduced (v 0) p (hv 0) hp
  obtain ⟨Ac1, sc1, qc1, hcfg1, hcard1⟩ := exists_reduced (v 1) p (hv 1) hp
  have hb0 := config_sum_bound (v 0) p (MMS 2 (v 0) p) Ac0 sc0 qc0 hcfg0
  have hb1 := config_sum_bound (v 1) p (MMS 2 (v 1) p) Ac1 sc1 qc1 hcfg1
  by_cases hcut : ∑ g ∈ sc0, p g ≤ ∑ g ∈ sc1, p g
  · obtain ⟨o, hov, h0, h1⟩ := cutgive v p hp Ac0 sc0 qc0 hcfg0 sc1 hcard1 hb1 hcut
    exact ⟨o, hov, fun i => by fin_cases i <;> assumption⟩
  · push_neg at hcut
    obtain ⟨o, hov, h0, h1⟩ := cutgive (fun i => v (Equiv.swap 0 1 i)) p hp Ac1 sc1 qc1
      (by simpa [Equiv.swap_apply_left] using hcfg1) sc0 hcard0
      (by simpa [Equiv.swap_apply_right] using hb0) (le_of_lt hcut)
    refine ⟨swapOutcome o, swapOutcome_valid p o hov, fun i => ?_⟩
    fin_cases i
    · rw [util_swapOutcome]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h1
    · rw [util_swapOutcome]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h0

end FairSelling
