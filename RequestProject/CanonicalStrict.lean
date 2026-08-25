import Mathlib
import RequestProject.CanonicalPartition
import RequestProject.MatchingPhase

/-!
# Lemma 3 in the manuscript's strict form

`RequestProject.CanonicalPartition` proves the manuscript's Lemma 3 in the form `IsCanonical`:
three bundles, each acceptable, at most one of them unrestricted, the others pure or singletons.

The matching phase needs the *strict* form `IsCanonicalStrict` of the manuscript (the numbered
conditions of the definition of a canonical partition in Section C):

* at most two goods are force-sold (Lemma 5 for `n = 3`);
* each non-leftovers bundle is pure (carries no money), or is a single good plus money coming from
  the sale of a **single** good `f` (`money k ≤ p f`);
* every such `f` is expensive: `p f ≥ τ / 3`, i.e. `p f ≥ (1 - ρ) · MMS` for `ρ = 3/4`.

This file proves Lemma 3 in that strict form, unconditionally
(`canonical_partition_three_strict`), following the manuscript's proof:

* if at most one part of the reduced MMS partition (Lemma 5) holds more than `MMS/4` of sale
  proceeds, that part is declared the leftovers bundle and the two others are stripped of their
  money and become pure (`canonical_strict_pure_parts`);
* otherwise the proceeds exceed `MMS/2` and are carried by at most two goods, so some force-sold
  good `F` has `p F ≥ MMS/4 = τ/3`.  If some remaining good `e` can be topped up with proceeds
  from `F` to exactly `τ`, that singleton bundle plus one bag-filled pure bundle plus the
  leftovers works (`canonical_strict_singleton`); otherwise every remaining good is worth less
  than `τ - p F ≤ (2/3)·τ`, and greedy bag-filling produces two pure bundles and a leftovers
  bundle containing `F` itself, with nothing sold at all (`canonical_strict_two_pure`).

As a consequence, the assumption of a strictly canonical partition can be discharged from the
matching-phase results: `exists_threequarter_MMS_three_nobig` gives the `3/4`-MMS allocation for
three agents with no big good, assuming only the residual case of Lemma 4.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- The degenerate case `τ ≤ 0`: the empty partition is strictly canonical. -/
lemma canonical_strict_trivial (w p : G → ℝ) {τ : ℝ} (hτ : τ ≤ 0) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover :=
  ⟨fun _ => ∅, ∅, fun _ => 0, 0,
    ⟨fun _ _ _ => by simp, fun _ => by simp, fun _ => le_rfl, by simp,
      fun _ => by simpa [vbarSum] using hτ, fun _ _ => Or.inl rfl⟩,
    by simp, fun _ _ => Or.inl rfl⟩

omit [Fintype G] [DecidableEq G] in
/-- **The manuscript's easy case.**  If at most one part of an MMS configuration carries more than
`r - τ` in sale proceeds, that part becomes the leftovers bundle and the two other parts become
pure. -/
lemma canonical_strict_pure_parts (w p : G → ℝ) {τ r : ℝ}
    (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
    (hdisjA : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hdisjs : ∀ i, Disjoint s (A i))
    (hq0 : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = ∑ g ∈ s, p g)
    (hge : ∀ i, r ≤ vbarSum w p (A i) + q i) (hscard : s.card ≤ 2)
    (lo : Fin 3) (hsmallq : ∀ i, i ≠ lo → q i ≤ r - τ) (hτr : τ ≤ r) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by
  classical
  refine ⟨A, s, fun i => if i = lo then q i else 0, lo,
    ⟨hdisjA, hdisjs, ?_, ?_, ?_, ?_⟩, hscard, ?_⟩
  · intro k; by_cases hk : k = lo <;> simp [hk, hq0]
  · have h1 : ∑ k, (if k = lo then q k else 0) = q lo := by simp
    rw [h1, ← hqsum]
    exact Finset.single_le_sum (f := q) (fun i _ => hq0 i) (Finset.mem_univ lo)
  · intro k
    by_cases hk : k = lo
    · subst hk; simpa using le_trans hτr (hge k)
    · simp only [hk, if_false, add_zero]
      have h1 := hge k
      have h2 := hsmallq k hk
      linarith
  · intro k hk; simp [hk]
  · intro k hk; simp [hk]

/-- **The singleton case.**  A good `e` that can be topped up with proceeds from the expensive
force-sold good `F` to exactly `τ` yields a strictly canonical partition: the singleton bundle
`{e}`, a bag-filled pure bundle, and the leftovers. -/
lemma canonical_strict_singleton (w p : G → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hsmall : ∀ g, vbar w p g < τ) (F e : G) (heF : e ≠ F)
    (hpF : τ / 3 ≤ p F)
    (htop : τ ≤ vbar w p e + p F)
    (htot : 4 * τ ≤ vbarSum w p (Finset.univ \ {F}) + p F) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by
  classical
  have hpFlt : p F < τ := lt_of_le_of_lt (le_max_left _ _) (hsmall F)
  have hue : vbar w p e < τ := hsmall e
  -- the goods available for the pure bundle
  set S : Finset G := (Finset.univ \ ({F} : Finset G)) \ {e} with hS
  have heU : ({e} : Finset G) ⊆ Finset.univ \ ({F} : Finset G) := by
    simp [Finset.subset_iff, heF]
  have hSsum : vbarSum w p S = vbarSum w p (Finset.univ \ {F}) - vbar w p e := by
    rw [hS, vbarSum_sdiff w p heU]
    simp [vbarSum]
  obtain ⟨B, hBS, hB1, hB2⟩ :=
    bagfill (vbar w p) τ (2 * τ) hτ.le (by linarith) S
      (fun g _ => by have := hsmall g; linarith)
      (by
        have hEq : ∑ g ∈ S, vbar w p g = vbarSum w p S := rfl
        rw [hEq, hSsum]; linarith)
  have hBsum : vbarSum w p B = ∑ g ∈ B, vbar w p g := rfl
  have hFS : F ∉ S := by simp [hS]
  have heS : e ∉ S := by simp [hS]
  have hFB : F ∉ B := fun h => hFS (hBS h)
  have heB : e ∉ B := fun h => heS (hBS h)
  set C : Finset G := insert F (insert e B) with hC
  have hCsum : vbarSum w p C = vbar w p F + vbar w p e + vbarSum w p B := by
    rw [hC, vbarSum, Finset.sum_insert (by simp [Ne.symm heF, hFB]), Finset.sum_insert heB]
    simp [vbarSum]
    ring
  have hkept2 : vbarSum w p (Finset.univ \ C)
      = vbarSum w p (Finset.univ \ {F}) - vbar w p e - vbarSum w p B := by
    rw [vbarSum_sdiff w p (Finset.subset_univ C), hCsum,
      vbarSum_sdiff w p (Finset.subset_univ ({F} : Finset G))]
    simp [vbarSum]
    ring
  -- the three bundles
  set X : Fin 3 → Finset G :=
    fun k => if k = 0 then {e} else if k = 1 then B else Finset.univ \ C with hX
  set m : Fin 3 → ℝ :=
    fun k => if k = 0 then τ - vbar w p e else if k = 1 then 0 else p F - (τ - vbar w p e)
    with hm
  have hX0 : X 0 = {e} := by simp [hX]
  have hX1 : X 1 = B := by simp [hX]
  have hX2 : X 2 = Finset.univ \ C := by simp [hX]
  have hm0' : m 0 = τ - vbar w p e := by simp [hm]
  have hm1' : m 1 = 0 := by simp [hm]
  have hm2' : m 2 = p F - (τ - vbar w p e) := by simp [hm]
  have hdeB : Disjoint ({e} : Finset G) B := by simpa using heB
  have hdeC : Disjoint ({e} : Finset G) (Finset.univ \ C) := by
    rw [Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [hC]
  have hdBC : Disjoint B (Finset.univ \ C) := by
    rw [Finset.disjoint_right]
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 (by simp [hC, hxB])
  -- the six conditions, checked bundle by bundle
  have d01 : Disjoint (X 0) (X 1) := by rw [hX0, hX1]; exact hdeB
  have d02 : Disjoint (X 0) (X 2) := by rw [hX0, hX2]; exact hdeC
  have d12 : Disjoint (X 1) (X 2) := by rw [hX1, hX2]; exact hdBC
  have hs0 : Disjoint ({F} : Finset G) (X 0) := by
    rw [hX0]; simpa [Finset.disjoint_singleton] using Ne.symm heF
  have hs1 : Disjoint ({F} : Finset G) (X 1) := by
    rw [hX1]; simpa [Finset.disjoint_singleton_left] using hFB
  have hs2 : Disjoint ({F} : Finset G) (X 2) := by
    rw [hX2, Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [hC]
  have hcard0 : (X 0).card = 1 := by rw [hX0]; simp
  have hmn0 : 0 ≤ m 0 := by rw [hm0']; linarith
  have hmn1 : 0 ≤ m 1 := by rw [hm1']
  have hmn2 : 0 ≤ m 2 := by rw [hm2']; linarith
  have hmle : m 0 ≤ p F := by rw [hm0']; linarith
  have hval0 : τ ≤ vbarSum w p (X 0) + m 0 := by
    rw [hX0, hm0', show vbarSum w p ({e} : Finset G) = vbar w p e from by simp [vbarSum]]
    linarith
  have hval1 : τ ≤ vbarSum w p (X 1) + m 1 := by
    rw [hX1, hm1', add_zero, hBsum]; exact hB1
  have hval2 : τ ≤ vbarSum w p (X 2) + m 2 := by
    rw [hX2, hm2', hkept2]
    linarith
  refine ⟨X, {F}, m, 2, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl hjk
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl hjk
  · intro k
    fin_cases k
    · exact hs0
    · exact hs1
    · exact hs2
  · intro k
    fin_cases k
    · exact hmn0
    · exact hmn1
    · exact hmn2
  · rw [Fin.sum_univ_three, hm0', hm1', hm2']
    simp
  · intro k
    fin_cases k
    · exact hval0
    · exact hval1
    · exact hval2
  · intro k hk
    fin_cases k
    · exact Or.inr hcard0
    · exact Or.inl hm1'
    · exact absurd rfl hk
  · simp
  · intro k hk
    fin_cases k
    · exact Or.inr ⟨hcard0, F, Finset.mem_singleton_self F, hmle, hpF⟩
    · exact Or.inl hm1'
    · exact absurd rfl hk

/-- **The two-pure-bundles case.**  If every good other than `F` is worth less than `(2/3)·τ`,
greedy bag-filling produces two pure bundles and a leftovers bundle containing `F`; nothing is
sold. -/
lemma canonical_strict_two_pure (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {τ : ℝ} (hτ : 0 < τ) (F : G)
    (hsmall : ∀ g ∈ (Finset.univ \ ({F} : Finset G)), vbar w p g < (2 / 3) * τ)
    (htot3 : 3 * τ ≤ vbarSum w p (Finset.univ \ {F}))
    (htotall : 4 * τ ≤ vbarSum w p Finset.univ) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by
  classical
  obtain ⟨B1, B2, -, -, hdisj, hge1, hge2, hle⟩ :=
    greedy_two_bags (vbar w p) (fun g => le_trans (hp g) (le_max_left _ _)) τ hτ
      (Finset.univ \ {F}) hsmall htot3
  have hkept2 : vbarSum w p (Finset.univ \ (B1 ∪ B2))
      = vbarSum w p Finset.univ - vbarSum w p B1 - vbarSum w p B2 := by
    rw [vbarSum_sdiff w p (Finset.subset_univ _), vbarSum_union w p hdisj]
    ring
  have hB1 : vbarSum w p B1 = ∑ g ∈ B1, vbar w p g := rfl
  have hB2 : vbarSum w p B2 = ∑ g ∈ B2, vbar w p g := rfl
  set X : Fin 3 → Finset G :=
    fun k => if k = 0 then B1 else if k = 1 then B2 else Finset.univ \ (B1 ∪ B2) with hX
  have hX0 : X 0 = B1 := by simp [hX]
  have hX1 : X 1 = B2 := by simp [hX]
  have hX2 : X 2 = Finset.univ \ (B1 ∪ B2) := by simp [hX]
  have hd1 : Disjoint B1 (Finset.univ \ (B1 ∪ B2)) := by
    rw [Finset.disjoint_right]
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ hxB)
  have hd2 : Disjoint B2 (Finset.univ \ (B1 ∪ B2)) := by
    rw [Finset.disjoint_right]
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ hxB)
  have d01 : Disjoint (X 0) (X 1) := by rw [hX0, hX1]; exact hdisj
  have d02 : Disjoint (X 0) (X 2) := by rw [hX0, hX2]; exact hd1
  have d12 : Disjoint (X 1) (X 2) := by rw [hX1, hX2]; exact hd2
  have hval0 : τ ≤ vbarSum w p (X 0) + (0 : ℝ) := by rw [hX0, add_zero, hB1]; exact hge1
  have hval1 : τ ≤ vbarSum w p (X 1) + (0 : ℝ) := by rw [hX1, add_zero, hB2]; exact hge2
  have hval2 : τ ≤ vbarSum w p (X 2) + (0 : ℝ) := by
    rw [hX2, add_zero, hkept2, hB1, hB2]; linarith
  refine ⟨X, ∅, fun _ => 0, 2, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl hjk
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl hjk
  · intro k; simp
  · intro k; exact le_rfl
  · simp
  · intro k
    fin_cases k
    · exact hval0
    · exact hval1
    · exact hval2
  · intro k _; exact Or.inl rfl
  · simp
  · intro k _; exact Or.inl rfl

/-- **Lemma 3, strict form.**  For a single agent with additive non-negative valuation `w` and
non-negative prices `p`, if every good is small (`v̄(g) < 3/4 · MMS`), then the goods admit a
*strictly* canonical partition into three bundles, each of value at least `3/4 · MMS`: at most two
goods are force-sold, each non-leftovers bundle is pure or a single good topped up with money from
the sale of a single good `f` with `p f ≥ MMS / 4`. -/
theorem canonical_partition_three_strict (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3 / 4) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p ((3 / 4) * MMS 3 w p) kept sold money leftover := by
  classical
  set M : ℝ := MMS 3 w p with hM
  set τ : ℝ := (3 / 4) * M with hτdef
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  rcases eq_or_lt_of_le hM0 with hMzero | hMpos
  · exact canonical_strict_trivial w p (by rw [hτdef, ← hMzero]; norm_num)
  have hτ : 0 < τ := by rw [hτdef]; linarith
  obtain ⟨A, s, q, hcfg, hscard⟩ := exists_reduced_three w p hw hp
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hqsum, hge⟩ := hcfg
  -- the total value available: goods outside `s` plus the sale proceeds
  have hVeq : vbarSum w p (Finset.univ \ s) = ∑ i : Fin 3, vbarSum w p (A i) := by
    rw [show Finset.univ \ s = Finset.biUnion Finset.univ A from ?_]
    · rw [vbarSum, Finset.sum_biUnion]
      · rfl
      · exact fun i _ j _ hij => hdisjA i j hij
    · ext g
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hg
        have hg' : g ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ g
        rcases Finset.mem_union.mp hg' with h | h
        · exact absurd h hg
        · simpa using h
      · rintro ⟨i, hi⟩ hgs
        exact Finset.disjoint_left.mp (hdisjs i) hgs hi
  have hVtot : 4 * τ ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g := by
    have hsum3 : (3 : ℝ) * M ≤ ∑ i, (vbarSum w p (A i) + q i) := by
      have h := Finset.sum_le_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) => hge i)
      simpa [Fin.sum_univ_three] using h
    rw [Finset.sum_add_distrib, hqsum, ← hVeq] at hsum3
    rw [hτdef]; linarith
  by_cases hbig : ∃ i j : Fin 3, i ≠ j ∧ M / 4 < q i ∧ M / 4 < q j
  · -- at least two parts carry more than `M/4`: some force-sold good is expensive
    obtain ⟨i, j, hij, hi, hj⟩ := hbig
    have hqtot : M / 2 < ∑ g ∈ s, p g := by
      rw [← hqsum]
      have hsum : q i + q j ≤ ∑ k, q k := by
        have hsub : ({i, j} : Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hq0 k)
        rw [Finset.sum_pair hij] at h2
        exact h2
      linarith
    have hsne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with rfl | h
      · simp at hqtot; linarith
      · exact h
    obtain ⟨F, hFs, hFmax⟩ := Finset.exists_max_image (f := p) s hsne
    have hpF0 : 0 ≤ p F := hp F
    have hpF : τ / 3 ≤ p F := by
      have hle : ∑ g ∈ s, p g ≤ (s.card : ℝ) * p F := by
        calc ∑ g ∈ s, p g ≤ ∑ _g ∈ s, p F := Finset.sum_le_sum (fun g hg => hFmax g hg)
        _ = (s.card : ℝ) * p F := by simp [mul_comm]
      have hcard : (s.card : ℝ) ≤ 2 := by exact_mod_cast hscard
      have h2 : M / 2 < 2 * p F := by nlinarith
      rw [hτdef]; linarith
    -- the total value with only `F` sold
    have hdisj_sF : Disjoint (Finset.univ \ s) (s \ ({F} : Finset G)) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx2).1
    have hunion : (Finset.univ \ s) ∪ (s \ ({F} : Finset G)) = Finset.univ \ {F} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro (hx | ⟨hx, hxF⟩)
        · rintro rfl; exact hx hFs
        · exact hxF
      · intro hxF
        by_cases hxs : x ∈ s
        · exact Or.inr ⟨hxs, hxF⟩
        · exact Or.inl hxs
    have hsplit : vbarSum w p (Finset.univ \ ({F} : Finset G))
        = vbarSum w p (Finset.univ \ s) + vbarSum w p (s \ {F}) := by
      rw [← hunion, vbarSum_union w p hdisj_sF]
    have hsF : ∑ g ∈ s, p g = p F + ∑ g ∈ s \ ({F} : Finset G), p g := by
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hFs)]
      simp [add_comm]
    have hsFle : ∑ g ∈ s \ ({F} : Finset G), p g ≤ vbarSum w p (s \ {F}) :=
      Finset.sum_le_sum (fun g _ => le_max_left _ _)
    have htotF : 4 * τ ≤ vbarSum w p (Finset.univ \ ({F} : Finset G)) + p F := by
      rw [hsF] at hVtot
      rw [hsplit]
      linarith
    by_cases hsing : ∃ e ∈ (Finset.univ \ ({F} : Finset G)), τ ≤ vbar w p e + p F
    · obtain ⟨e, heU, hee⟩ := hsing
      have heF : e ≠ F := by simpa using (Finset.mem_sdiff.mp heU).2
      exact canonical_strict_singleton w p hτ hsmall F e heF hpF hee htotF
    · push_neg at hsing
      have hsmallF : ∀ g ∈ (Finset.univ \ ({F} : Finset G)), vbar w p g < (2 / 3) * τ := by
        intro g hg
        have h := hsing g hg
        linarith
      have hpFlt : p F < τ := lt_of_le_of_lt (le_max_left _ _) (hsmall F)
      have htot3 : 3 * τ ≤ vbarSum w p (Finset.univ \ ({F} : Finset G)) := by linarith
      have hFuniv : vbarSum w p Finset.univ
          = vbarSum w p (Finset.univ \ ({F} : Finset G)) + vbar w p F := by
        rw [vbarSum_sdiff w p (Finset.subset_univ ({F} : Finset G))]
        simp [vbarSum]
      have hFge : p F ≤ vbar w p F := le_max_left _ _
      exact canonical_strict_two_pure w p hp hτ F hsmallF htot3 (by rw [hFuniv]; linarith)
  · -- at most one part carries more than `M/4`
    push_neg at hbig
    obtain ⟨lo, hlo⟩ : ∃ lo : Fin 3, ∀ i, i ≠ lo → q i ≤ M / 4 := by
      by_cases h0 : M / 4 < q 0
      · refine ⟨0, fun i hi => ?_⟩
        by_contra hcon
        exact absurd (hbig i 0 hi (lt_of_not_ge hcon)) (not_le.mpr h0)
      · by_cases h1 : M / 4 < q 1
        · refine ⟨1, fun i hi => ?_⟩
          by_contra hcon
          exact absurd (hbig i 1 hi (lt_of_not_ge hcon)) (not_le.mpr h1)
        · refine ⟨2, fun i hi => ?_⟩
          push_neg at h0 h1
          fin_cases i <;> simp_all
    refine canonical_strict_pure_parts w p A s q hdisjA hdisjs hq0 hqsum hge hscard lo ?_ ?_
    · intro i hi
      have h := hlo i hi
      rw [hτdef]; linarith
    · rw [hτdef]; linarith

/-- **The `n = 3`, `3/4`-MMS theorem after the preliminary phase.**  If no agent values any good at
`3/4 · MMS` or more, three agents admit a valid allocation giving everybody at least
`3/4 · MMS`, assuming only the residual case of Lemma 4 (which is discharged in
`RequestProject.LemmaFourResidual`, giving the unconditional
`exists_threequarter_MMS_three_nobig'`). -/
theorem exists_threequarter_MMS_three_nobig (hL4 : LemmaFourCashSold G)
    (v : Fin 3 → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨a, -, hmax⟩ :=
    Finset.exists_max_image (f := fun i => MMS 3 (v i) p) Finset.univ ⟨0, Finset.mem_univ 0⟩
  obtain ⟨kept, sold, money, lo, hcan⟩ :=
    canonical_partition_three_strict (v a) p (hv a) hp (hnobig a)
  exact exists_threequarter_MMS_three_of_canonical hL4 v p hv hp hnobig a
    (fun i => hmax i (Finset.mem_univ i)) kept sold money lo hcan

end FairSelling
