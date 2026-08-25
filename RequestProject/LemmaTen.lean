import Mathlib
import RequestProject.EpsEnvy

/-!
# Appendix C, Lemma 10: `EFX` existence versus `SEFX` existence

The manuscript distinguishes, in Appendix C, between goods that are *sellable* and goods that are
not, and between *full* allocations (every good is allocated or sold, and the whole sale proceeds
are distributed — condition (3) of the model) and *partial* allocations (conditions (1) and (2)
only, which is `Outcome.Valid`).  Both notions are recorded here (`Outcome.AllocatesAll`,
`Outcome.Full`), together with the no-selling notions `EFXalloc` and `EF1alloc`.

> **Lemma 10.**  If for some number of agents `n` and additive valuations, an `EFX` allocation
> always exists, then the same is true for `SEFX`, and vice versa.  The same holds for `EF1` and
> `SEF1`.

* The direction `SEFX ⟹ EFX` is proved in full: `EFXalloc_of_SEFX_full` and its packaged form
  `exists_EFX_of_exists_SEFX` (and `exists_EF1_of_exists_SEF1` for the `SEF1` version).  Applying
  the `SEFX` hypothesis to an instance in which no good is sellable (so that all prices vanish and
  no money exists) produces literally an `EFX` allocation.
* The direction `EFX ⟹ SEFX` is proved in full **for partial allocations**
  (`exists_SEFX_of_exists_EFX`, and `exists_SEF1_of_exists_EF1` for the `EF1` version): sell
  every sellable good and
  allocate the non-sellable goods according to an `EFX` allocation.  Every good is then allocated
  or sold and the outcome is `SEFXs`, hence `SEFX`; the sale proceeds are simply not distributed,
  which conditions (1)–(2) of the model permit.
* For **full** allocations the same construction must in addition hand out the whole sale
  proceeds without creating envy towards a money-holding agent.  This is exactly the extension
  result for mixed divisible and indivisible goods that the manuscript quotes from the literature
  (reference [8] of the manuscript); it is *not* reproved here, and is carried as an explicit
  hypothesis (`SEFX_full_of_EFX_of_money_extension`), never as an axiom.

Also recorded is the manuscript's observation preceding Lemma 10: if all goods are sellable then
an `EF` full allocation exists — sell everything and split the proceeds equally
(`exists_EF_full_of_all_sellable`).
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Full allocations and allocations of the goods -/

/-- Every good is either sold or allocated (the first half of condition (3)). -/
def Outcome.AllocatesAll (o : Outcome G n) : Prop :=
  o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ

/-- A **full allocation** (conditions (1), (2), (3) of the model) with respect to a set
`sellable` of sellable goods: a valid outcome that only sells sellable goods, allocates or sells
every good, and distributes exactly the sale proceeds. -/
def Outcome.Full (p : G → ℝ) (sellable : Finset G) (o : Outcome G n) : Prop :=
  o.Valid p ∧ o.sold ⊆ sellable ∧ o.AllocatesAll ∧ ∑ j, o.money j = ∑ g ∈ o.sold, p g

/-- `A` is a partition of the set `T` of goods into `n` (possibly empty) bundles. -/
def IsPartitionOf (A : Fin n → Finset G) (T : Finset G) : Prop :=
  (∀ j k, j ≠ k → Disjoint (A j) (A k)) ∧ Finset.univ.biUnion A = T

/-- `EFX` for an allocation of goods without selling. -/
def EFXalloc (v : Fin n → G → ℝ) (A : Fin n → Finset G) : Prop :=
  ∀ i j, ∀ g ∈ A j, ∑ g' ∈ A i, v i g' ≥ ∑ g' ∈ A j \ {g}, v i g'

/-- `EF1` for an allocation of goods without selling. -/
def EF1alloc (v : Fin n → G → ℝ) (A : Fin n → Finset G) : Prop :=
  ∀ i j, (A j).Nonempty → ∃ g ∈ A j, ∑ g' ∈ A i, v i g' ≥ ∑ g' ∈ A j \ {g}, v i g'

/- The auxiliary notion `SEF1'` that used to be recorded here — `SEF1` with an explicit exemption
for an agent holding neither goods nor money — is no longer needed: the definition `SEF1` of
`RequestProject.Selling` now allows the (relaxed) envy-free condition as an alternative to the
up-to-one-good condition, which covers an empty envied bundle. -/

/-! ### A computation rule for `v̄` -/

omit [Fintype G] [DecidableEq G] in
/-- On goods with zero price, `v̄ᵢ` agrees with `vᵢ` (for non-negative valuations). -/
theorem vbarSum_eq_sum_of_price_zero {vi p : G → ℝ} {A : Finset G} (hv : ∀ g, 0 ≤ vi g)
    (hp : ∀ g ∈ A, p g = 0) : vbarSum vi p A = ∑ g ∈ A, vi g := by
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [vbar, hp g hg]
  exact max_eq_right (hv g)

/-! ### All goods sellable: an `EF` full allocation exists -/

/-- The observation preceding Lemma 10: if all goods are sellable, selling everything and
splitting the proceeds equally is a full allocation which is `EF` (and, vacuously, `SEFX`). -/
theorem exists_EF_full_of_all_sellable (v : Fin n → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (hn : 0 < n) :
    ∃ o : Outcome G n, o.Full p Finset.univ ∧ EF v p o ∧ SEFX v p o := by
  classical
  refine ⟨⟨Finset.univ, fun _ => ∅, fun _ => (∑ g, p g) / n⟩, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j; simp
  · intro j k _; simp
  · intro j
    have : 0 ≤ ∑ g, p g := Finset.sum_nonneg fun g _ => hp g
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  · exact Finset.Subset.refl _
  · simp [Outcome.AllocatesAll]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  · intro i j; simp
  · intro i j
    exact ⟨fun _ => by simp, fun _ => Or.inr fun g hg => absurd hg (by simp)⟩

/-! ### `SEFX ⟹ EFX` -/

/-- If no good is sellable (so that all prices vanish), a full `SEFX` allocation *is* an `EFX`
allocation. -/
theorem EFXalloc_of_SEFX_full (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (p : G → ℝ)
    (hp : ∀ g, p g = 0) (o : Outcome G n) (hfull : o.Full p ∅) (hsefx : SEFX v p o) :
    IsPartitionOf o.kept Finset.univ ∧ EFXalloc v o.kept := by
  obtain ⟨hvalid, hsub, hall, hmsum⟩ := hfull
  have hsold : o.sold = ∅ := Finset.subset_empty.mp hsub
  have hmoney : ∀ j, o.money j = 0 := by
    intro j
    refine le_antisymm ?_ (hvalid.2.2.1 j)
    have h1 : ∑ k, o.money k = 0 := by rw [hmsum, hsold]; simp
    have h2 : o.money j ≤ ∑ k, o.money k :=
      Finset.single_le_sum (f := o.money) (fun k _ => hvalid.2.2.1 k) (Finset.mem_univ j)
    linarith
  refine ⟨⟨hvalid.2.1, ?_⟩, ?_⟩
  · have := hall
    rw [Outcome.AllocatesAll, hsold] at this
    simpa using this
  · intro i j g hg
    have hbi : vbarSum (v i) p (o.kept i) = ∑ g' ∈ o.kept i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    have hbj : vbarSum (v i) p (o.kept j) = ∑ g' ∈ o.kept j, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    have hbjg : vbarSum (v i) p (o.kept j \ {g}) = ∑ g' ∈ o.kept j \ {g}, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    rcases (hsefx i j).2 (hmoney j) with hEF | hall
    · -- the envy-free alternative: dropping a good only decreases the value
      rw [hbi, hbj, hmoney i] at hEF
      have hsub : ∑ g' ∈ o.kept j \ {g}, v i g' ≤ ∑ g' ∈ o.kept j, v i g' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun g' _ _ => hv i g')
      linarith
    · have hx := hall g hg
      rw [hbi, hbjg, hp g, hmoney i] at hx
      linarith

/-- **Lemma 10, direction `SEFX ⟹ EFX`.**  If every instance with sellable goods admits a full
`SEFX` allocation, then every instance without selling admits an `EFX` allocation. -/
theorem exists_EFX_of_exists_SEFX
    (hSEFX : ∀ w : Fin n → G → ℝ, (∀ i g, 0 ≤ w i g) →
      ∃ o : Outcome G n, o.Full (fun _ => 0) ∅ ∧ SEFX w (fun _ => 0) o)
    (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset G, IsPartitionOf A Finset.univ ∧ EFXalloc v A := by
  obtain ⟨o, hfull, hsefx⟩ := hSEFX v hv
  exact ⟨o.kept, EFXalloc_of_SEFX_full v hv _ (fun _ => rfl) o hfull hsefx⟩

/-- If no good is sellable, a full `SEF1` allocation *is* an `EF1` allocation. -/
theorem EF1alloc_of_SEF1_full (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (p : G → ℝ)
    (hp : ∀ g, p g = 0) (o : Outcome G n) (hfull : o.Full p ∅) (hsef1 : SEF1 v p o) :
    IsPartitionOf o.kept Finset.univ ∧ EF1alloc v o.kept := by
  obtain ⟨hvalid, hsub, hall, hmsum⟩ := hfull
  have hsold : o.sold = ∅ := Finset.subset_empty.mp hsub
  have hmoney : ∀ j, o.money j = 0 := by
    intro j
    refine le_antisymm ?_ (hvalid.2.2.1 j)
    have h1 : ∑ k, o.money k = 0 := by rw [hmsum, hsold]; simp
    have h2 : o.money j ≤ ∑ k, o.money k :=
      Finset.single_le_sum (f := o.money) (fun k _ => hvalid.2.2.1 k) (Finset.mem_univ j)
    linarith
  refine ⟨⟨hvalid.2.1, ?_⟩, ?_⟩
  · have := hall
    rw [Outcome.AllocatesAll, hsold] at this
    simpa using this
  · intro i j hne
    have hbi : vbarSum (v i) p (o.kept i) = ∑ g' ∈ o.kept i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    have hbj : vbarSum (v i) p (o.kept j) = ∑ g' ∈ o.kept j, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    rcases (hsef1 i j).2 (hmoney j) with hEF | ⟨g, hg, hx⟩
    · obtain ⟨g, hg⟩ := hne
      refine ⟨g, hg, ?_⟩
      rw [hbi, hbj, hmoney i] at hEF
      have hsub : ∑ g' ∈ o.kept j \ {g}, v i g' ≤ ∑ g' ∈ o.kept j, v i g' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun g' _ _ => hv i g')
      linarith
    · refine ⟨g, hg, ?_⟩
      rw [hbi, vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g), hp g,
        hmoney i] at hx
      linarith

/-- **Lemma 10, direction `SEF1 ⟹ EF1`.** -/
theorem exists_EF1_of_exists_SEF1
    (hSEF1 : ∀ w : Fin n → G → ℝ, (∀ i g, 0 ≤ w i g) →
      ∃ o : Outcome G n, o.Full (fun _ => 0) ∅ ∧ SEF1 w (fun _ => 0) o)
    (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset G, IsPartitionOf A Finset.univ ∧ EF1alloc v A := by
  obtain ⟨o, hfull, hsef1⟩ := hSEF1 v hv
  exact ⟨o.kept, EF1alloc_of_SEF1_full v hv _ (fun _ => rfl) o hfull hsef1⟩

/-! ### `EFX ⟹ SEFX` -/

section EFXtoSEFX

variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)

/-- The outcome built from an allocation `A` of the non-sellable goods: sell every sellable good
and hand out the bundles of `A`. -/
def sellAllOutcome (P : Fin n → ℝ) : Outcome G n := ⟨sellable, A, P⟩

variable {v p sellable A}

/-- Goods allocated by a partition of the non-sellable goods have zero price. -/
theorem price_zero_of_mem_bundle (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (j : Fin n) {g : G} (hg : g ∈ A j) :
    p g = 0 := by
  have : g ∈ Finset.univ \ sellable := by
    rw [← hA.2]
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hg⟩
  exact hp0 g (Finset.mem_sdiff.mp this).2

/-- **Lemma 10, direction `EFX ⟹ SEFX` (partial allocations).**  Selling every sellable good and
allocating the non-sellable goods according to an `EFX` allocation yields a valid outcome that
allocates or sells every good and is `SEFXs` (hence `SEFX`).  The proceeds are not distributed,
so this is a partial allocation. -/
theorem SEFXs_sellAll (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (hEFX : EFXalloc v A) :
    (sellAllOutcome sellable A (fun _ => 0)).Valid p ∧
      (sellAllOutcome sellable A (fun _ => 0)).AllocatesAll ∧
      SEFXs v p (sellAllOutcome sellable A (fun _ => 0)) := by
  classical
  have hpz : ∀ j, ∀ g ∈ A j, p g = 0 := fun j g hg => price_zero_of_mem_bundle hp0 hA j hg
  have hdisj : ∀ j, Disjoint sellable (A j) := by
    intro j
    refine Finset.disjoint_left.2 fun g hg hgA => ?_
    have : g ∈ Finset.univ \ sellable := by
      rw [← hA.2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hgA⟩
    exact (Finset.mem_sdiff.mp this).2 hg
  refine ⟨⟨hdisj, hA.1, fun _ => le_rfl, ?_⟩, ?_, ?_⟩
  · simp only [sellAllOutcome]
    simp only [Finset.sum_const_zero]
    exact Finset.sum_nonneg fun g _ => hp g
  · show sellable ∪ Finset.univ.biUnion A = Finset.univ
    rw [hA.2]
    simp
  · intro i j
    refine ⟨fun h => absurd h (by simp [sellAllOutcome]), fun g hg => ?_⟩
    have hgA : g ∈ A j := hg
    have h1 : vbarSum (v i) p (A i) = ∑ g' ∈ A i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g' hg' => hpz i g' hg')
    have h2 : vbarSum (v i) p (A j \ {g}) = ∑ g' ∈ A j \ {g}, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g)
        (fun g' hg' => hpz j g' (Finset.mem_sdiff.mp hg').1)
    have := hEFX i j g hgA
    simp only [sellAllOutcome, add_zero]
    rw [h1, h2, hpz j g hgA]
    simpa using this

/-- **Lemma 10, direction `EFX ⟹ SEFX` (partial allocations), packaged form.** -/
theorem exists_SEFX_of_exists_EFX (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hEFX : ∃ A : Fin n → Finset G, IsPartitionOf A (Finset.univ \ sellable) ∧ EFXalloc v A) :
    ∃ o : Outcome G n, o.Valid p ∧ o.AllocatesAll ∧ SEFX v p o := by
  obtain ⟨A, hA, hEFX⟩ := hEFX
  obtain ⟨h1, h2, h3⟩ := SEFXs_sellAll hv hp hp0 hA hEFX
  exact ⟨_, h1, h2, SEFX_of_SEFXs h1 h3⟩

/-- **Lemma 10, direction `EF1 ⟹ SEF1` (partial allocations).** -/
theorem exists_SEF1_of_exists_EF1 (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hEF1 : ∃ A : Fin n → Finset G, IsPartitionOf A (Finset.univ \ sellable) ∧ EF1alloc v A) :
    ∃ o : Outcome G n, o.Valid p ∧ o.AllocatesAll ∧ SEF1 v p o := by
  classical
  obtain ⟨A, hA, hEF1⟩ := hEF1
  have hpz : ∀ j, ∀ g ∈ A j, p g = 0 := fun j g hg => price_zero_of_mem_bundle hp0 hA j hg
  have hdisj : ∀ j, Disjoint sellable (A j) := by
    intro j
    refine Finset.disjoint_left.2 fun g hg hgA => ?_
    have : g ∈ Finset.univ \ sellable := by
      rw [← hA.2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hgA⟩
    exact (Finset.mem_sdiff.mp this).2 hg
  refine ⟨sellAllOutcome sellable A (fun _ => 0), ⟨hdisj, hA.1, fun _ => le_rfl, ?_⟩, ?_, ?_⟩
  · simp only [sellAllOutcome, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun g _ => hp g
  · show sellable ∪ Finset.univ.biUnion A = Finset.univ
    rw [hA.2]; simp
  · intro i j
    refine ⟨fun h => absurd h (by simp [sellAllOutcome]), fun _ => ?_⟩
    rcases Finset.eq_empty_or_nonempty (A j) with hemp | hne
    · -- an empty envied bundle: the envy-free alternative holds
      refine Or.inl ?_
      have h1 : (0 : ℝ) ≤ vbarSum (v i) p (A i) := vbarSum_nonneg (hv i) _
      simp only [sellAllOutcome, hemp, vbarSum, Finset.sum_empty, add_zero, ge_iff_le]
      simpa [vbarSum] using h1
    refine Or.inr ?_
    obtain ⟨g, hgA, hx⟩ := hEF1 i j hne
    refine ⟨g, hgA, ?_⟩
    have h1 : vbarSum (v i) p (A i) = ∑ g' ∈ A i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g' hg' => hpz i g' hg')
    have h2 : vbarSum (v i) p (A j \ {g}) = ∑ g' ∈ A j \ {g}, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g)
        (fun g' hg' => hpz j g' (Finset.mem_sdiff.mp hg').1)
    simp only [sellAllOutcome]
    rw [h1, h2, hpz j g hgA]
    simpa using hx

/-- **Lemma 10, direction `EFX ⟹ SEFX` (full allocations).**  With the whole sale proceeds
distributed, the construction needs in addition a distribution `P` of the proceeds under which no
agent envies a money-holding agent.  This is the extension result for mixed divisible and
indivisible goods quoted by the manuscript, which is *assumed* here (as an explicit hypothesis,
`hext`) rather than proved. -/
theorem SEFX_full_of_EFX_of_money_extension (hv : ∀ i g, 0 ≤ v i g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (hEFX : EFXalloc v A)
    (hext : ∃ P : Fin n → ℝ, (∀ j, 0 ≤ P j) ∧ (∑ j, P j = ∑ g ∈ sellable, p g) ∧
      ∀ i j, 0 < P j → (∑ g' ∈ A i, v i g') + P i ≥ (∑ g' ∈ A j, v i g') + P j) :
    ∃ o : Outcome G n, o.Full p sellable ∧ SEFX v p o := by
  classical
  obtain ⟨P, hP0, hPsum, hPEF⟩ := hext
  have hpz : ∀ j, ∀ g ∈ A j, p g = 0 := fun j g hg => price_zero_of_mem_bundle hp0 hA j hg
  have hbar : ∀ i j, vbarSum (v i) p (A j) = ∑ g' ∈ A j, v i g' := fun i j =>
    vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g' hg' => hpz j g' hg')
  have hdisj : ∀ j, Disjoint sellable (A j) := by
    intro j
    refine Finset.disjoint_left.2 fun g hg hgA => ?_
    have : g ∈ Finset.univ \ sellable := by
      rw [← hA.2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hgA⟩
    exact (Finset.mem_sdiff.mp this).2 hg
  refine ⟨sellAllOutcome sellable A P, ⟨⟨hdisj, hA.1, hP0, le_of_eq hPsum⟩, Finset.Subset.refl _,
    ?_, hPsum⟩, ?_⟩
  · show sellable ∪ Finset.univ.biUnion A = Finset.univ
    rw [hA.2]; simp
  · intro i j
    refine ⟨fun hj => ?_, fun hj => Or.inr fun g hg => ?_⟩
    · have := hPEF i j hj
      simp only [sellAllOutcome, hbar]
      exact this
    · have hgA : g ∈ A j := hg
      have hPi : (0 : ℝ) ≤ P i := hP0 i
      have h2 : vbarSum (v i) p (A j \ {g}) = ∑ g' ∈ A j \ {g}, v i g' :=
        vbarSum_eq_sum_of_price_zero (fun g => hv i g)
          (fun g' hg' => hpz j g' (Finset.mem_sdiff.mp hg').1)
      have := hEFX i j g hgA
      simp only [sellAllOutcome, hbar, h2, hpz j g hgA, add_zero]
      linarith

end EFXtoSEFX

end FairSelling
