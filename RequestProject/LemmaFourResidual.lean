import Mathlib
import RequestProject.ConfigSplit
import RequestProject.CanonicalStrict

/-!
# The residual (singleton) case of Lemma 4

`MatchingPhase` proves Lemma 4 of the manuscript except for the case in which the allocated bundle
is a *singleton* bundle: at most one kept good `K` together with money `m` produced by selling a
single good `f`.  This file proves that case, and hence Lemma 4 in full.

The argument follows the manuscript's `ℓ₃`/`ℓ₄` analysis, but is organised around the
configuration-splitting machinery of `ConfigSplit`:

* if the agent sells `f` itself in its own MMS configuration, then no value is destroyed by the
  forced sale and a pure counting argument gives two bundles (`MMS2_cash_of_total`);
* otherwise `f` sits inside one part of the agent's configuration; one *untouched* part is kept on
  its own, the other two parts are merged, and the surviving proceeds top both bundles up to
  `3/4 · MMS`.  The price condition `p f ≥ MMS/4` bounds the value destroyed by the sale.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Total value of all goods, split along a configuration. -/
lemma config_vbarSum_univ (w p : G → ℝ) {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ}
    {r : ℝ} (hcfg : ConfigN 3 w p r A s q) :
    vbarSum w p Finset.univ = (∑ i, vbarSum w p (A i)) + vbarSum w p s := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, -⟩ := hcfg
  have hbi : Finset.univ \ s = Finset.univ.biUnion A := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hg
      have hg' : g ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ g
      rcases Finset.mem_union.mp hg' with h | h
      · exact absurd h hg
      · simpa using h
    · rintro ⟨i, hi⟩ hgs
      exact Finset.disjoint_left.mp (hdisjs i) hgs hi
  have h1 : vbarSum w p (Finset.univ \ s) = ∑ i, vbarSum w p (A i) := by
    rw [hbi, vbarSum, Finset.sum_biUnion (fun i _ j _ hij => hdisjA i j hij)]
    rfl
  have h2 := vbarSum_sdiff w p (Finset.subset_univ s)
  rw [h1] at h2
  linarith

omit [Fintype G] in
/-- The value of the removed set `K ∪ {f}`. -/
lemma vbarSum_insert_disjoint (w p : G → ℝ) (K : Finset G) (f : G) (hfK : f ∉ K) :
    vbarSum w p (K ∪ {f}) = vbarSum w p K + vbar w p f := by
  rw [vbarSum_union w p (Finset.disjoint_singleton_right.mpr hfK)]
  simp [vbarSum]

/-- **The singleton case of Lemma 4.**  A bundle made of at most one kept good `K` plus money `m`
coming from the sale of the single good `f` is handed out, the unused proceeds `p f - m` being
banked.  An agent that values the bundle at most `3/4 · MMS` can still split what is left into two
bundles worth `3/4 · MMS` each. -/
theorem lemmaFour_singleton (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p)
    (K : Finset G) (f : G) (m : ℝ) (hfK : f ∉ K) (hm0 : 0 ≤ m) (hmf : m ≤ p f)
    (hKcard : K.card ≤ 1) (hprice : (1 / 4 : ℝ) * MMS 3 w p ≤ p f)
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ {f})) w)
      (cashPrice (Finset.univ \ (K ∪ {f})) p (p f - m)) := by
  classical
  set M : ℝ := MMS 3 w p with hM
  set τ : ℝ := (3 / 4 : ℝ) * M with hτ
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  set X : Finset G := K ∪ {f} with hX
  have hXcard : X.card ≤ 2 := by
    have h := Finset.card_union_le K ({f} : Finset G)
    simp only [Finset.card_singleton] at h
    rw [hX]
    omega
  have hvX : vbarSum w p X = vbarSum w p K + vbar w p f := vbarSum_insert_disjoint w p K f hfK
  have hvK0 : 0 ≤ vbarSum w p K := vbarSum_nonneg' w p hw K
  have hfbig : vbar w p f < τ := hnobig f
  have hpf_le : p f ≤ vbar w p f := le_max_left _ _
  obtain ⟨A, s, q, hcfg, hscard⟩ := exists_reduced_three w p hw hp
  have hq0 := hcfg.2.2.2.1
  have hqsum := hcfg.2.2.2.2.1
  have hge := hcfg.2.2.2.2.2
  by_cases hfs : f ∈ s
  · -- The agent sells `f` itself: the forced sale destroys no value, and counting suffices.
    have hslack : vbar w p f - p f ≤ vbarSum w p s - ∑ g ∈ s, p g := by
      have hterm : ∀ g ∈ s, (0 : ℝ) ≤ vbar w p g - p g := fun g _ => by
        simp only [vbar, sub_nonneg]; exact le_max_left _ _
      have hsum : ∑ g ∈ s, (vbar w p g - p g) = vbarSum w p s - ∑ g ∈ s, p g := by
        rw [Finset.sum_sub_distrib]; rfl
      have hone : vbar w p f - p f ≤ ∑ g ∈ s, (vbar w p g - p g) :=
        Finset.single_le_sum (f := fun g => vbar w p g - p g) hterm hfs
      linarith
    have hV : vbarSum w p Finset.univ = (∑ i, vbarSum w p (A i)) + vbarSum w p s :=
      config_vbarSum_univ w p hcfg
    have hparts : 3 * M - ∑ i, q i ≤ ∑ i, vbarSum w p (A i) := by
      have h := Finset.sum_le_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) => hge i)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at h
      push_cast at h
      linarith
    have hRem : vbarSum w p (Finset.univ \ X)
        = vbarSum w p Finset.univ - vbarSum w p X := vbarSum_sdiff w p (Finset.subset_univ X)
    refine MMS2_cash_of_total w p hw hp (Finset.univ \ X) (p f - m) τ (by linarith) (by linarith)
      (fun g _ => (hnobig g).le) ?_
    rw [hRem, hvX]
    linarith
  · -- `f` is kept in one part of the configuration.
    obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 3, f ∈ A i0 := by
      have hf' : f ∈ s ∪ Finset.univ.biUnion A := by
        rw [hcfg.2.2.1]; exact Finset.mem_univ f
      rcases Finset.mem_union.mp hf' with h | h
      · exact absurd h hfs
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
        exact ⟨i, hi⟩
    have hsX : s ∩ X ⊆ K := by
      intro x hx
      obtain ⟨hxs, hxX⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hxX with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.mp h ▸ hxs) hfs
    -- the untouched parts, and among them one with least proceeds share
    set U : Finset (Fin 3) := Finset.univ.filter (fun k => Disjoint (A k) X) with hU
    have hUne : U.Nonempty := by
      obtain ⟨j, hj⟩ := exists_part_disjoint A hcfg.1 X hXcard
      exact ⟨j, by simp [hU, hj]⟩
    obtain ⟨j, hjU, hjmin⟩ := Finset.exists_min_image (f := q) U hUne
    have hjdisj : Disjoint (A j) X := by simpa [hU] using hjU
    obtain ⟨j', j'', hj', hj'', hj'j''⟩ := fin3_others j
    have hj1 : j ≠ j' := Ne.symm hj'
    have hj2 : j ≠ j'' := Ne.symm hj''
    -- abbreviations for the pieces of the split
    set LC : ℝ := vbarSum w p (A j ∩ X) with hLC
    set LD : ℝ := vbarSum w p ((A j' ∪ A j'') ∩ X) with hLD
    set PS : ℝ := ∑ g ∈ s ∩ X, p g with hPS
    have hLC0 : LC = 0 := by
      have : A j ∩ X = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hjdisj
      simp [hLC, this, vbarSum]
    have hLD0 : 0 ≤ LD := vbarSum_nonneg' w p hw _
    have hPS0 : 0 ≤ PS := Finset.sum_nonneg (fun g _ => hp g)
    have hPSK : PS ≤ vbarSum w p K := by
      refine le_trans (Finset.sum_le_sum (fun g _ => le_max_left (p g) (w g))) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg hsX
        (fun g _ _ => le_trans (hw g) (le_max_right _ _))
    have hPSq : PS ≤ ∑ i, q i := by
      rw [hqsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun g _ _ => hp g)
    have hloss : LC + LD + PS ≤ vbarSum w p X := config_loss_le w p hcfg X hj1 hj2 hj'j''
    have hC := config_part_sdiff_ge w p hcfg X j
    have hD := config_two_parts_sdiff_ge w p hcfg X hj'j''
    have hT := config_sold_sdiff w p hcfg X
    -- either the lost proceeds are covered by the banked cash, or a second part is untouched
    have hcase : PS ≤ p f - m ∨ ∃ k, k ≠ j ∧ Disjoint (A k) X ∧ q j ≤ q k := by
      by_cases hle : PS ≤ p f - m
      · exact Or.inl hle
      · refine Or.inr ?_
        push_neg at hle
        have hne : (s ∩ X).Nonempty := by
          rcases Finset.eq_empty_or_nonempty (s ∩ X) with h | h
          · exfalso; rw [hPS, h] at hle; simp at hle; linarith
          · exact h
        obtain ⟨e, he⟩ := hne
        have heK : e ∈ K := hsX he
        have hKeq : K = {e} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨heK, fun x hx => Finset.card_le_one.mp hKcard x hx e heK⟩
        have hes : e ∈ s := (Finset.mem_inter.mp he).1
        -- only the part containing `f` is touched
        have huntouched : ∀ k, k ≠ i0 → Disjoint (A k) X := by
          intro k hk
          refine Finset.disjoint_left.mpr (fun x hx hxX => ?_)
          rcases Finset.mem_union.mp hxX with h | h
          · rw [hKeq, Finset.mem_singleton] at h
            exact (Finset.disjoint_left.mp (hcfg.2.1 k)) (h ▸ hes) hx
          · rw [Finset.mem_singleton] at h
            exact hk (by
              by_contra hne
              exact (Finset.disjoint_left.mp (hcfg.1 k i0 hne)) hx (h ▸ hi0))
        obtain ⟨k1, k2, hk1, hk2, hk12⟩ := fin3_others i0
        rcases eq_or_ne k1 j with rfl | hne1
        · exact ⟨k2, Ne.symm hk12, huntouched k2 hk2,
            hjmin k2 (by simp [hU, huntouched k2 hk2])⟩
        · exact ⟨k1, hne1, huntouched k1 hk1, hjmin k1 (by simp [hU, huntouched k1 hk1])⟩
    rw [hvX] at hloss
    have hqj := hq0 j
    have hqj' := hq0 j'
    have hqj'' := hq0 j''
    have hsum3 : ∑ i, q i = q j + q j' + q j'' := fin3_sum hj1 hj2 hj'j'' q
    -- the crucial estimate: if the isolated part needs money, the other two parts hold enough
    have hkey : M / 4 < q j → τ - M + m - p f + PS ≤ q j' + q j'' := by
      intro hqbig
      rcases hcase with hcov | ⟨k, hkj, -, hqk⟩
      · linarith
      · have hqpair : q j ≤ q j' + q j'' := by
          rcases fin3_cover hj1 hj2 hj'j'' k with h | h | h
          · exact absurd h hkj
          · rw [h] at hqk; linarith
          · rw [h] at hqk; linarith
        linarith
    refine MMS2_cash_of_config_split w p hw hp hcfg X (p f - m) τ (by linarith) hj1 hj2 ?_
    rw [hT, ← hPS]
    rcases le_or_gt τ (vbarSum w p (A j \ X)) with h1 | h1 <;>
      rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      have := hkey (by linarith)
      linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith

/-- **The residual case of Lemma 4 holds.** -/
theorem lemmaFourCashSold_holds : LemmaFourCashSold G := by
  intro w p hw hp hnobig K f m hfK hm0 hmf hKcard hprice hrej
  exact lemmaFour_singleton w p hw hp hnobig K f m hfK hm0 hmf hKcard hprice hrej

/-- **Lemma 4 of the manuscript, in cash-aware form, in full.** -/
theorem lemmaFourCash_holds : LemmaFourCash G := lemmaFourCash_of_sold lemmaFourCashSold_holds

/-- **The `n = 3`, `3/4`-MMS theorem after the preliminary phase**, with no assumptions beyond the
absence of big goods. -/
theorem exists_threequarter_MMS_three_nobig' (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i :=
  exists_threequarter_MMS_three_nobig lemmaFourCashSold_holds v p hv hp hnobig

end FairSelling
