import Mathlib

/-!
# Fair Allocation with Optional Selling

This file formalizes the model of *fair allocation of indivisible goods with optional
selling* described in the manuscript "Fair Allocation with Optional Selling", together
with the share-based fairness notions it introduces (Proportional Share, Maximin Share,
Truncated Proportional Share) and the envy-based notions (EF, SEF1, SEFX).

The main proved result is **Lemma 1** of the manuscript:
`MMS ≤ TPS ≤ PS`, together with the fact that the value `TPS` we define is indeed a
fixed point of the truncated-proportional map (matching the manuscript's definition of
`TPS` as the largest `t` with `(1/n) ∑ max{p(j), min{v(j), t}} = t`).

## Model

* Goods are the elements of a finite type `G`.
* Agents are indexed by `Fin n`.
* A subjective (additive, non-negative) valuation is a function `v : G → ℝ`.
* Market prices are a function `p : G → ℝ`.

An *outcome* `(S, A, P)` records:
* `sold`   : the set `S ⊆ G` of goods that are sold;
* `kept`   : for each agent `j`, the bundle `A j ⊆ G` of unsold goods it receives;
* `money`  : for each agent `j`, the share `P j` of the sale proceeds it receives.

Feasibility (`Outcome.Valid`) requires (cf. equations (1),(2) of the manuscript):
* no sold good is kept: `Disjoint S (A j)` for every `j`;
* kept bundles are pairwise disjoint;
* money shares are non-negative;
* distributed proceeds do not exceed the proceeds from sold goods:
  `∑ j, P j ≤ ∑ g ∈ S, p g`.

The utility of agent with valuation `v` for part `j` is `ui (A j, P j) = ∑ g ∈ A j, v g + P j`.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- An outcome of an allocation with selling: which goods are sold, which bundles of
unsold goods each agent keeps, and how the sale proceeds (money) are split. -/
structure Outcome (G : Type*) (n : ℕ) where
  /-- The set of goods that are sold. -/
  sold : Finset G
  /-- The bundle of (unsold) goods kept by each agent. -/
  kept : Fin n → Finset G
  /-- The amount of sale proceeds (money) received by each agent. -/
  money : Fin n → ℝ

variable {n : ℕ}

/-- Feasibility of an outcome with respect to a price function `p`. -/
def Outcome.Valid (p : G → ℝ) (o : Outcome G n) : Prop :=
  (∀ j, Disjoint o.sold (o.kept j)) ∧
  (∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k)) ∧
  (∀ j, 0 ≤ o.money j) ∧
  (∑ j, o.money j ≤ ∑ g ∈ o.sold, p g)

/-- The utility of the agent with valuation `v` for part `j` of the outcome `o`:
the subjective value of the kept bundle plus the money received. -/
def util (v : G → ℝ) (o : Outcome G n) (j : Fin n) : ℝ :=
  (∑ g ∈ o.kept j, v g) + o.money j

/-- The modified valuation `v̄ g = max (p g) (v g)` (Definition just before Definition 4). -/
def vbar (v p : G → ℝ) (g : G) : ℝ := max (p g) (v g)

/-- **Proportional Share** (Definition 1): `PS = (1/n) ∑_g max{p(g), v(g)}`. -/
noncomputable def PS (n : ℕ) (v p : G → ℝ) : ℝ := (∑ g, max (p g) (v g)) / n

/-- The truncated-proportional map `t ↦ (1/n) ∑_g max{p(g), min{v(g), t}}` from
Definition 3. -/
noncomputable def truncSum (n : ℕ) (v p : G → ℝ) (t : ℝ) : ℝ :=
  (∑ g, max (p g) (min (v g) t)) / n

/-- The set of values that some valid outcome guarantees to *every* agent. -/
def MMSset (n : ℕ) (v p : G → ℝ) : Set ℝ :=
  {r | ∃ o : Outcome G n, o.Valid p ∧ ∀ j, r ≤ util v o j}

/-- **Maximin Share with selling** (Definition 2), phrased as a supremum over the
values guaranteeable to every agent by a valid outcome. -/
noncomputable def MMS (n : ℕ) (v p : G → ℝ) : ℝ := sSup (MMSset n v p)

/-- The set of `t` with `t ≤ truncSum t`; `TPS` is its supremum (the largest fixed
point of `truncSum`). -/
def TPSset (n : ℕ) (v p : G → ℝ) : Set ℝ := {t | t ≤ truncSum n v p t}

/-- **Truncated Proportional Share with selling** (Definition 3): the largest `t` with
`(1/n) ∑_g max{p(g), min{v(g), t}} = t`. We define it as `sSup {t | t ≤ truncSum t}`
and prove below (`TPS_truncSum`) that it is indeed a fixed point of `truncSum`. -/
noncomputable def TPS (n : ℕ) (v p : G → ℝ) : ℝ := sSup (TPSset n v p)

/-! ### Envy-based fairness notions (Definition 4)

An allocation is given here by an `Outcome`; the modified valuation of agent `i`
(with valuation `vi` and price `p`) is `vbar vi p`. We record the definitions of
EF, SEF1 and SEFX. (These are recorded for faithfulness of the formalization; the
manuscript's envy theorems are not proved here.) -/

/-- `v̄i` value of a bundle. -/
def vbarSum (vi p : G → ℝ) (A : Finset G) : ℝ := ∑ g ∈ A, vbar vi p g

/-- Envy-freeness of an outcome from the point of view of a family of valuations
`v : Fin n → G → ℝ` (agent `i` uses valuation `v i`), with prices `p`
(Definition 4): every agent `i` weakly prefers its own part to every other part,
measured with `v̄i`. -/
def EF (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j, vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j

/-- **SEF1** (Definition 4.1).  For every ordered pair of agents `i, j`:
* if agent `j` holds money (`P_j > 0`), the plain envy-free condition
  `v̄i(A i) + P i ≥ v̄i(A j) + P j` must hold;
* if `P_j = 0`, it is enough that either the envy-free condition `v̄i(A i) + P i ≥ v̄i(A j)`
  holds, or that there is a good `g ∈ A j` with `v̄i(A i) + P i ≥ v̄i(A j \ g) + p g`.

Two points on the reading of the manuscript's definition, both discussed with the authors:
* the envying agent's own money `P_i` belongs on the left-hand side also in the relaxed
  condition — otherwise the notion would not be a relaxation of envy-freeness;
* the relaxed condition is a disjunction with the envy-free condition, because for an *empty*
  envied bundle no good `g ∈ A j` is available; without the disjunct no allocation in which
  some agent holds neither goods nor money could be SEF1.

The literal transcription of the manuscript's text is kept below as `SEF1lit`. -/
def SEF1 (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i ≥ vbarSum (v i) p (o.kept j)) ∨
      (∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))

/-- **SEFX** (Definition 4.2): as `SEF1`, but the up-to-any-good condition must hold for
*every* good `g ∈ A j`.  See `SEF1` for the two corrections applied to the manuscript's text;
the literal transcription is kept below as `SEFXlit`. -/
def SEFX (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i ≥ vbarSum (v i) p (o.kept j)) ∨
      (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))

/-- The *literal* transcription of Definition 4.1 of the manuscript, in which the envying
agent's own money `P_i` does not appear on the left-hand side of the relaxed condition and no
exemption is made for an empty envied bundle.  It is recorded only in order to state precisely
what fails for it (see `RequestProject.LemmaElevenCounterexample`); the notion used throughout
the development is the corrected `SEF1`. -/
def SEF1lit (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i)
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)

/-- The *literal* transcription of Definition 4.2 of the manuscript; cf. `SEF1lit`. -/
def SEFXlit (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i)
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)

section EnvyRelations

variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

omit [Fintype G] in
/-- Removing one good from a bundle, measured with `v̄i`. -/
theorem vbarSum_sdiff_singleton {vi p : G → ℝ} {A : Finset G} {g : G} (hg : g ∈ A) :
    vbarSum vi p A = vbarSum vi p (A \ {g}) + vbar vi p g := by
  classical
  have hA : A = insert g (A \ {g}) := by
    ext x
    by_cases hx : x = g <;> simp [hx, hg]
  rw [vbarSum, vbarSum, hA, Finset.sum_insert (by simp)]
  simp [add_comm]

/-- `SEFX` is a genuine relaxation of envy-freeness. -/
theorem SEFX_of_EF (h : EF v p o) : SEFX v p o := fun i j =>
  ⟨fun _ => h i j, fun hj => Or.inl (by have := h i j; rw [hj] at this; linarith)⟩

/-- `SEF1` is a genuine relaxation of envy-freeness. -/
theorem SEF1_of_EF (h : EF v p o) : SEF1 v p o := fun i j =>
  ⟨fun _ => h i j, fun hj => Or.inl (by have := h i j; rw [hj] at this; linarith)⟩

omit [Fintype G] in
/-- The `v̄i`-value of a bundle is non-negative when the valuation is. -/
theorem vbarSum_nonneg {vi p : G → ℝ} (hv : ∀ g, 0 ≤ vi g) (A : Finset G) :
    0 ≤ vbarSum vi p A :=
  Finset.sum_nonneg fun g _ => le_trans (hv g) (le_max_right _ _)

/-- `SEFX` implies `SEF1` (for a valid outcome and non-negative valuations: these are needed
only to handle an empty envied bundle). -/
theorem SEF1_of_SEFX (hv : ∀ i g, 0 ≤ v i g) (hvalid : o.Valid p) (h : SEFX v p o) :
    SEF1 v p o := by
  intro i j
  refine ⟨(h i j).1, fun hj => ?_⟩
  rcases (h i j).2 hj with hEF | hall
  · exact Or.inl hEF
  · rcases Finset.eq_empty_or_nonempty (o.kept j) with hemp | ⟨g, hg⟩
    · refine Or.inl ?_
      have h1 : 0 ≤ vbarSum (v i) p (o.kept i) := vbarSum_nonneg (hv i) _
      have h2 := hvalid.2.2.1 i
      rw [hemp]
      simp only [vbarSum, Finset.sum_empty] at *
      linarith
    · exact Or.inr ⟨g, hg, hall g hg⟩

omit [Fintype G] in
/-- The literal reading of Definition 4.2 implies the corrected `SEFX`, for a valid outcome. -/
theorem SEFX_of_SEFXlit (hvalid : o.Valid p) (h : SEFXlit v p o) : SEFX v p o := by
  intro i j
  refine ⟨(h i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (h i j).2 hj g hg
  have hmi := hvalid.2.2.1 i
  linarith

omit [Fintype G] in
/-- The literal reading of Definition 4.1 implies the corrected `SEF1`, for a valid outcome. -/
theorem SEF1_of_SEF1lit (hvalid : o.Valid p) (h : SEF1lit v p o) : SEF1 v p o := by
  intro i j
  refine ⟨(h i j).1, fun hj => Or.inr ?_⟩
  obtain ⟨g, hg, hx⟩ := (h i j).2 hj
  have hmi := hvalid.2.2.1 i
  exact ⟨g, hg, by linarith⟩

end EnvyRelations

/-! ### Basic positivity / nonemptiness facts -/

/-
The "sell nothing, keep nothing" outcome is valid; it witnesses `0 ∈ MMSset`.
-/
omit [Fintype G] [DecidableEq G] in
theorem mem_MMSset_zero (v p : G → ℝ) :
    (0 : ℝ) ∈ MMSset n v p := by
  -- The value for every agent is zero.
  use ⟨∅, fun _ => ∅, fun _ => 0⟩
  simp [Outcome.Valid, util]

omit [Fintype G] [DecidableEq G] in
theorem MMSset_nonempty (v p : G → ℝ) :
    (MMSset n v p).Nonempty := ⟨0, mem_MMSset_zero v p⟩

/-
`0 ∈ TPSset`, using `v, p ≥ 0`.
-/
omit [DecidableEq G] in
theorem mem_TPSset_zero (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    (0 : ℝ) ∈ TPSset n v p := by
  exact Set.mem_setOf_eq.mpr ( div_nonneg ( Finset.sum_nonneg fun _ _ => le_max_of_le_left ( hp _ ) ) ( Nat.cast_nonneg _ ) )

omit [DecidableEq G] in
theorem TPSset_nonempty (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    (TPSset n v p).Nonempty := ⟨0, mem_TPSset_zero v p hp⟩

/-
Every element of `TPSset` is `≤ PS`; in particular `TPSset` is bounded above.
-/
omit [DecidableEq G] in
theorem TPSset_le_PS (v p : G → ℝ) {t : ℝ} (ht : t ∈ TPSset n v p) :
    t ≤ PS n v p := by
  refine' le_trans ht ( div_le_div_of_nonneg_right ( Finset.sum_le_sum fun g _ => by cases max_cases ( p g ) ( v g ) <;> cases max_cases ( p g ) ( Min.min ( v g ) t ) <;> cases min_cases ( v g ) t <;> linarith ) ( Nat.cast_nonneg _ ) )

omit [DecidableEq G] in
theorem TPSset_bddAbove (v p : G → ℝ) :
    BddAbove (TPSset n v p) := ⟨PS n v p, fun _ ht => TPSset_le_PS v p ht⟩

/-! ### Lemma 1 : `MMS ≤ TPS ≤ PS` -/

/-
Key per-bundle inequality: if a bundle has utility at least `r` (with `r ≥ 0`),
then its truncated-at-`r` value plus its money is still at least `r`.
-/
omit [Fintype G] [DecidableEq G] in
theorem bundle_trunc_ge (v : G → ℝ) (hv : ∀ g, 0 ≤ v g) (o : Outcome G n)
    (j : Fin n) (r : ℝ) (hr : 0 ≤ r) (hmj : 0 ≤ o.money j) (hj : r ≤ util v o j) :
    r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j := by
  by_cases h_exists : ∃ g ∈ o.kept j, r ≤ v g;
  · obtain ⟨ g, hg₁, hg₂ ⟩ := h_exists;
    exact le_add_of_le_of_nonneg ( le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => le_min ( hv x ) hr ) hg₁ ) ) hmj;
  · unfold util at hj; simp_all +decide [ min_eq_left_of_lt ] ;

/-
If a valid outcome guarantees value `r ≥ 0` to every agent, then `r ∈ TPSset`,
i.e. `r ≤ truncSum r`.
-/
theorem mem_TPSset_of_valid (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    (o : Outcome G n) (hvalid : o.Valid p) (r : ℝ) (hr : 0 ≤ r)
    (hguar : ∀ j, r ≤ util v o j) :
    r ∈ TPSset n v p := by
  -- By `bundle_trunc_ge`, for each agent `j`, `r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j`.
  have hbundle_trunc_ge : ∀ j, r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j := by
    exact fun j => bundle_trunc_ge v hv o j r hr ( hvalid.2.2.1 j ) ( hguar j );
  -- Summing over the `n` agents (`Finset.univ : Finset (Fin n)`), and using `∑ j : Fin n, r = n * r` (`Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`):
  have hsum_trunc_ge : (n : ℝ) * r ≤ ∑ g ∈ Finset.biUnion Finset.univ o.kept, min (v g) r + ∑ j, o.money j := by
    rw [ Finset.sum_biUnion ];
    · simpa [ Finset.sum_add_distrib ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => hbundle_trunc_ge i;
    · exact fun i _ j _ hij => hvalid.2.1 i j hij;
  -- Now `min (v g) r ≤ max (p g) (min (v g) r)` and `p g ≤ max (p g) (min (v g) r)`, so
  have hsum_max_ge : ∑ g ∈ Finset.biUnion Finset.univ o.kept, min (v g) r + ∑ j, o.money j ≤ ∑ g ∈ Finset.biUnion Finset.univ o.kept, max (p g) (min (v g) r) + ∑ g ∈ o.sold, max (p g) (min (v g) r) := by
    refine' add_le_add ( Finset.sum_le_sum fun g hg => _ ) _;
    · exact le_max_right _ _;
    · exact le_trans hvalid.2.2.2 ( Finset.sum_le_sum fun _ _ => le_max_left _ _ );
  -- Also `U` and `o.sold` are disjoint (each `o.kept j` is disjoint from `o.sold` by `hks`, so their biUnion is; use `Finset.disjoint_biUnion_left` and `Disjoint.symm`).
  have hdisjoint : Disjoint (Finset.biUnion Finset.univ o.kept) o.sold := by
    exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by obtain ⟨ j, _, hj ⟩ := Finset.mem_biUnion.mp hx₁; exact Finset.disjoint_left.mp ( hvalid.1 j ) hx₂ hj;
  -- Hence `∑ g ∈ U, f g + ∑ g ∈ o.sold, f g = ∑ g ∈ U ∪ o.sold, f g` where `f g = max (p g) (min (v g) r)` (`Finset.sum_union` on disjoint sets).
  have hsum_union : ∑ g ∈ Finset.biUnion Finset.univ o.kept, max (p g) (min (v g) r) + ∑ g ∈ o.sold, max (p g) (min (v g) r) = ∑ g ∈ Finset.biUnion Finset.univ o.kept ∪ o.sold, max (p g) (min (v g) r) := by
    rw [ Finset.sum_union hdisjoint ];
  exact le_div_iff₀' ( by positivity ) |>.2 ( hsum_trunc_ge.trans <| hsum_max_ge.trans <| hsum_union.le.trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => le_max_of_le_left <| hp _ )

/-
**Lemma 1 (first inequality): `MMS ≤ TPS`.**
-/
theorem MMS_le_TPS (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ≤ TPS n v p := by
  by_contra h_contra;
  obtain ⟨r, hr⟩ : ∃ r, r ∈ MMSset n v p ∧ r > TPS n v p := by
    exact exists_lt_of_lt_csSup ( MMSset_nonempty v p ) ( not_le.mp h_contra );
  obtain ⟨o, hvalid, hguar⟩ := hr.left
  have hr_nonneg : 0 ≤ r := by
    exact le_trans ( by exact le_csSup ( TPSset_bddAbove v p ) ( mem_TPSset_zero v p hp ) ) hr.right.le
  have hr_in_TPSset : r ∈ TPSset n v p := by
    exact mem_TPSset_of_valid v p hn hv hp o hvalid r hr_nonneg hguar
  have hr_le_TPS : r ≤ TPS n v p := by
    exact le_csSup ( TPSset_bddAbove v p ) hr_in_TPSset
  linarith [hr.right]

/-
**Lemma 1 (second inequality): `TPS ≤ PS`.**
-/
omit [DecidableEq G] in
theorem TPS_le_PS (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n v p ≤ PS n v p := by
  refine' csSup_le ( _ ) _;
  · exact ⟨ 0, mem_TPSset_zero v p hp ⟩;
  · intro t ht
    apply TPSset_le_PS v p ht

/-! ### `TPS` is the largest fixed point of the truncated-proportional map

The manuscript defines `TPS` as the largest `t` with `truncSum t = t`. We defined it as
`sSup {t | t ≤ truncSum t}`; the following lemmas show these agree: our `TPS` is a fixed
point of `truncSum`, and it is the greatest fixed point. -/

/-
The truncated-proportional map is monotone (nondecreasing) in `t`.
-/
omit [DecidableEq G] in
theorem truncSum_mono (v p : G → ℝ) : Monotone (truncSum n v p) := by
  intro t t' h;
  exact div_le_div_of_nonneg_right ( Finset.sum_le_sum fun _ _ => max_le_max_left _ ( min_le_min_left _ h ) ) ( Nat.cast_nonneg _ )

/-
Our `TPS` is a fixed point of `truncSum`, matching the manuscript's Definition 3
(`(1/n) ∑_g max{p(g), min{v(g), TPS}} = TPS`).
-/
omit [DecidableEq G] in
theorem TPS_truncSum (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    truncSum n v p (TPS n v p) = TPS n v p := by
  unfold TPS;
  by_contra h;
  -- Since $TPSset n v p$ is nonempty and bounded above, it must have a supremum.
  obtain ⟨s, hs⟩ : ∃ s, sSup (TPSset n v p) = s ∧ s ∈ TPSset n v p := by
    refine' ⟨ _, rfl, _ ⟩;
    apply_rules [ IsClosed.csSup_mem ];
    · refine' isClosed_le continuous_id _;
      exact Continuous.div_const ( continuous_finset_sum _ fun _ _ => Continuous.max ( continuous_const ) ( Continuous.min ( continuous_const ) continuous_id' ) ) _;
    · exact ⟨ 0, mem_TPSset_zero v p hp ⟩;
    · exact TPSset_bddAbove v p;
  obtain ⟨t, ht⟩ : ∃ t, t ∈ TPSset n v p ∧ t > s := by
    simp_all +decide [ TPSset ];
    exact ⟨ truncSum n v p s, by linarith [ show truncSum n v p s ≤ truncSum n v p ( truncSum n v p s ) from by exact truncSum_mono v p hs.2 ], lt_of_le_of_ne hs.2 ( Ne.symm h ) ⟩;
  linarith [ le_csSup ( show BddAbove ( TPSset n v p ) from TPSset_bddAbove v p ) ht.1 ]

/-
`TPS` is the *largest* fixed point of `truncSum`: any fixed point is `≤ TPS`.
-/
omit [DecidableEq G] in
theorem TPS_greatest_fixed (v p : G → ℝ) {t : ℝ}
    (ht : truncSum n v p t = t) : t ≤ TPS n v p := by
  apply le_csSup;
  · convert TPSset_bddAbove v p using 1;
  · exact ht.ge

/-- **Lemma 1** of the manuscript: `MMS ≤ TPS ≤ PS`. -/
theorem MMS_le_TPS_le_PS (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ≤ TPS n v p ∧ TPS n v p ≤ PS n v p :=
  ⟨MMS_le_TPS v p hn hv hp, TPS_le_PS v p hp⟩

end FairSelling