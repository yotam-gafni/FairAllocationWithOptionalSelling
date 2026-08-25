import Mathlib
import RequestProject.ThreeAgents
import RequestProject.FeigeNorkin

/-!
# The `11/12` MMS gap for three agents (Proposition 1 of the manuscript)

Building on the Feige–Norkin instance formalized in `RequestProject.FeigeNorkin`, this file
constructs, for every `ρ > 11/12`, an instance of the model *with optional selling*
consisting of `n = 3` agents and `m = 8` goods in which **no** valid outcome gives every
agent at least `ρ` times her maximin share with selling.

The instance follows the manuscript: with `ṽR, ṽC, ṽU` the three Feige–Norkin valuations
(scaled by `3`, so that all targets are `36` rather than `12`),

* agent `0` has valuation `ṽR` and agent `1` has valuation `ṽC`;
* agent `2` has the zero valuation, and the price function is `p = δ · ṽU` for a small
  `δ > 0`.

Then the maximin share with selling is `36` for agents `0` and `1` (the prices are
dominated pointwise by their valuations, so the maximin share equals the classical one and
also equals the proportional share), and `36 δ` for agent `2` (all her value comes from
sale proceeds, so her maximin share is her proportional share, i.e. one third of the total
price).  Since the money in the system is worth at most `108 δ` to agents `0` and `1`,
choosing `δ` small forces a `ρ`-approximate outcome to hand agents `0` and `1` bundles of
goods worth more than `33` and to sell a set of goods worth more than `33` to agent `2` —
which is exactly what `FeigeNorkin.feigeNorkin_disjoint` forbids.

Main results:

* `MMS_agent_zero`, `MMS_agent_one`, `MMS_agent_two` — the maximin shares of the instance;
* `no_rho_MMS_three_eight` — the impossibility: for `ρ > 11/12` no valid outcome is
  `ρ`-MMS;
* `eleven_twelfths_gap` — the packaged statement of Proposition 1.
-/

open scoped BigOperators

namespace FairSelling

namespace ElevenTwelfths

open FeigeNorkin

/-- Casting a natural-number bundle value to `ℝ`. -/
lemma cast_sum_eq (s : Finset (Fin 8)) (w : Fin 8 → ℕ) (m : ℕ) (h : ∑ g ∈ s, w g = m) :
    ∑ g ∈ s, (w g : ℝ) = m := by
  rw [← Nat.cast_sum, h]

/-- The three valuations of the instance: the first two agents use the Feige–Norkin
valuations `ṽR` and `ṽC`, the third agent values no good (all her value comes from money). -/
noncomputable def instV : Fin 3 → Fin 8 → ℝ :=
  ![fun g => (fnR g : ℝ), fun g => (fnC g : ℝ), fun _ => 0]

/-- The price function of the instance: a small multiple `δ` of the third Feige–Norkin
valuation `ṽU`. -/
noncomputable def instP (δ : ℝ) : Fin 8 → ℝ := fun g => δ * (fnU g : ℝ)

lemma instV_nonneg : ∀ i g, 0 ≤ instV i g := by
  intro i g
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl <;> simp [instV]

lemma instP_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : ∀ g, 0 ≤ instP δ g := by
  intro g; exact mul_nonneg hδ (by positivity)

lemma instP_sum (δ : ℝ) : (∑ g, instP δ g) = 108 * δ := by
  have : (∑ g, instP δ g) = δ * ∑ g, (fnU g : ℝ) := by
    rw [Finset.mul_sum]; rfl
  rw [this, cast_sum_eq Finset.univ fnU 108 fnU_total]
  ring

/-- Every good is worth at least its price to agent `0`, provided `δ ≤ 1/12`. -/
lemma instP_le_R {δ : ℝ} (hδ : δ ≤ 1/12) (g : Fin 8) :
    instP δ g ≤ instV 0 g := by
  fin_cases g <;>
    simp only [instP, instV, fnR, fnU, Matrix.cons_val_zero] <;> norm_num <;> linarith

/-- Every good is worth at least its price to agent `1`, provided `δ ≤ 1/12`. -/
lemma instP_le_C {δ : ℝ} (hδ : δ ≤ 1/12) (g : Fin 8) :
    instP δ g ≤ instV 1 g := by
  fin_cases g <;>
    simp only [instP, instV, fnC, fnU, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      norm_num <;> linarith

/-! ### The maximin shares of the instance -/

/-- Agent `0`'s maximin share with selling is `36` (that is, `12` before scaling). -/
theorem MMS_agent_zero {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/12) :
    MMS 3 (instV 0) (instP δ) = 36 := by
  refine le_antisymm ?_ ?_
  · -- `MMS ≤ TPS ≤ PS = 36`
    have h := MMS_le_TPS_le_PS (instV 0) (instP δ) (n := 3) (by norm_num)
      (fun g => instV_nonneg 0 g) (instP_nonneg hδ0)
    have hPS : PS 3 (instV 0) (instP δ) = 36 := by
      unfold PS
      have : (∑ g, max (instP δ g) (instV 0 g)) = ∑ g, (fnR g : ℝ) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [max_eq_right (instP_le_R hδ g)]
        rfl
      rw [this, cast_sum_eq Finset.univ fnR 108 fnR_total]
      norm_num
    linarith [h.1, h.2]
  · -- the explicit partition into three bundles of value `36`
    refine le_MMS_of_outcome (by norm_num) (instV 0) (instP δ)
      (fun g => instV_nonneg 0 g) (instP_nonneg hδ0)
      ⟨∅, ![{2, 3, 4}, {0, 1}, {5, 6, 7}], fun _ => 0⟩ ?_ 36 ?_
    · refine ⟨fun _ => by simp, ?_, fun _ => le_refl 0, by simp⟩
      intro j k hjk
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
        first
          | (exact absurd rfl hjk)
          | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
              Matrix.cons_val_two, Matrix.tail_cons]; decide)
    · intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl <;>
        · simp only [util, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons, add_zero]
          show (36 : ℝ) ≤ ∑ g ∈ _, (fnR g : ℝ)
          rw [cast_sum_eq _ fnR 36 (by decide)]
          norm_num

/-- Agent `1`'s maximin share with selling is `36` (that is, `12` before scaling). -/
theorem MMS_agent_one {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/12) :
    MMS 3 (instV 1) (instP δ) = 36 := by
  refine le_antisymm ?_ ?_
  · have h := MMS_le_TPS_le_PS (instV 1) (instP δ) (n := 3) (by norm_num)
      (fun g => instV_nonneg 1 g) (instP_nonneg hδ0)
    have hPS : PS 3 (instV 1) (instP δ) = 36 := by
      unfold PS
      have : (∑ g, max (instP δ g) (instV 1 g)) = ∑ g, (fnC g : ℝ) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [max_eq_right (instP_le_C hδ g)]
        rfl
      rw [this, cast_sum_eq Finset.univ fnC 108 fnC_total]
      norm_num
    linarith [h.1, h.2]
  · refine le_MMS_of_outcome (by norm_num) (instV 1) (instP δ)
      (fun g => instV_nonneg 1 g) (instP_nonneg hδ0)
      ⟨∅, ![{2, 5}, {0, 3, 6}, {1, 4, 7}], fun _ => 0⟩ ?_ 36 ?_
    · refine ⟨fun _ => by simp, ?_, fun _ => le_refl 0, by simp⟩
      intro j k hjk
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
        first
          | (exact absurd rfl hjk)
          | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
              Matrix.cons_val_two, Matrix.tail_cons]; decide)
    · intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl <;>
        · simp only [util, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons, add_zero]
          show (36 : ℝ) ≤ ∑ g ∈ _, (fnC g : ℝ)
          rw [cast_sum_eq _ fnC 36 (by decide)]
          norm_num

/-- Agent `2` values no good, so her maximin share with selling is her proportional
share `36 δ`: sell everything and split the proceeds in three. -/
theorem MMS_agent_two {δ : ℝ} (hδ0 : 0 ≤ δ) :
    MMS 3 (instV 2) (instP δ) = 36 * δ := by
  refine le_antisymm ?_ ?_
  · have h := MMS_le_TPS_le_PS (instV 2) (instP δ) (n := 3) (by norm_num)
      (fun g => instV_nonneg 2 g) (instP_nonneg hδ0)
    have hPS : PS 3 (instV 2) (instP δ) = 36 * δ := by
      unfold PS
      have : (∑ g, max (instP δ g) (instV 2 g)) = ∑ g, instP δ g := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [max_eq_left]
        simpa [instV] using instP_nonneg hδ0 g
      rw [this, instP_sum]
      norm_num
      ring
    linarith [h.1, h.2]
  · refine le_MMS_of_outcome (by norm_num) (instV 2) (instP δ)
      (fun g => instV_nonneg 2 g) (instP_nonneg hδ0)
      ⟨Finset.univ, fun _ => ∅, fun _ => 36 * δ⟩ ?_ (36 * δ) ?_
    · refine ⟨fun _ => by simp, fun _ _ _ => by simp, fun _ => by positivity, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show (∑ g ∈ (Finset.univ : Finset (Fin 8)), instP δ g) = 108 * δ from instP_sum δ]
      norm_num
      linarith
    · intro j; simp [util]

/-! ### The impossibility -/

/-- **Proposition 1 (the `11/12` gap for `n = 3`, `m = 8`).**  For every `ρ > 11/12` there
is an instance with three agents and eight goods, non-negative additive valuations and
non-negative prices, in which every valid outcome leaves some agent with strictly less than
`ρ` times her maximin share with selling. -/
theorem no_rho_MMS_three_eight {ρ : ℝ} (hρ : 11/12 < ρ) :
    ∀ o : Outcome (Fin 8) 3, o.Valid (instP (min (ρ - 11/12) 1 / 12)) →
      ∃ i, util (instV i) o i
        < ρ * MMS 3 (instV i) (instP (min (ρ - 11/12) 1 / 12)) := by
  classical
  set ε : ℝ := ρ - 11/12 with hε_def
  have hε : 0 < ε := by simp [hε_def]; linarith
  set δ : ℝ := min ε 1 / 12 with hδ_def
  have hδ0 : 0 < δ := by
    have : 0 < min ε 1 := lt_min hε one_pos
    simpa [hδ_def] using by positivity
  have hδ12 : δ ≤ 1/12 := by
    have : min ε 1 ≤ 1 := min_le_right _ _
    simp only [hδ_def]
    linarith
  have hδε : 108 * δ ≤ 9 * ε := by
    have : min ε 1 ≤ ε := min_le_left _ _
    simp only [hδ_def]
    linarith
  intro o hvalid
  by_contra hcon
  push_neg at hcon
  -- the three agents' guarantees
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  rw [MMS_agent_zero hδ0.le hδ12] at h0
  rw [MMS_agent_one hδ0.le hδ12] at h1
  rw [MMS_agent_two hδ0.le] at h2
  -- total money available
  have hmoney_sum : ∑ j, o.money j ≤ ∑ g ∈ o.sold, instP δ g := hvalid.2.2.2
  have hmoney_nonneg : ∀ j, 0 ≤ o.money j := hvalid.2.2.1
  have hsoldU : (∑ g ∈ o.sold, instP δ g) = δ * ∑ g ∈ o.sold, (fnU g : ℝ) := by
    rw [Finset.mul_sum]; rfl
  have hsold_le : (∑ g ∈ o.sold, (fnU g : ℝ)) ≤ 108 := by
    have : (∑ g ∈ o.sold, (fnU g : ℝ)) ≤ ∑ g, (fnU g : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => by positivity)
    rw [cast_sum_eq Finset.univ fnU 108 fnU_total] at this
    simpa using this
  have hmoney_le : ∀ j, o.money j ≤ ∑ g ∈ o.sold, instP δ g := by
    intro j
    refine le_trans ?_ hmoney_sum
    exact Finset.single_le_sum (fun k _ => hmoney_nonneg k) (Finset.mem_univ j)
  have hmoney_small : ∀ j, o.money j ≤ 108 * δ := by
    intro j
    refine (hmoney_le j).trans ?_
    rw [hsoldU]
    calc δ * ∑ g ∈ o.sold, (fnU g : ℝ) ≤ δ * 108 := by
          exact mul_le_mul_of_nonneg_left hsold_le hδ0.le
      _ = 108 * δ := by ring
  -- agent 0 keeps goods worth more than 33
  have hR : (33 : ℝ) < ∑ g ∈ o.kept 0, (fnR g : ℝ) := by
    have hu : util (instV 0) o 0 = (∑ g ∈ o.kept 0, (fnR g : ℝ)) + o.money 0 := rfl
    have := hcon 0
    rw [MMS_agent_zero hδ0.le hδ12] at this
    rw [hu] at this
    have hm := hmoney_small 0
    nlinarith [hδε, hε]
  -- agent 1 keeps goods worth more than 33
  have hC : (33 : ℝ) < ∑ g ∈ o.kept 1, (fnC g : ℝ) := by
    have hu : util (instV 1) o 1 = (∑ g ∈ o.kept 1, (fnC g : ℝ)) + o.money 1 := rfl
    have := hcon 1
    rw [MMS_agent_one hδ0.le hδ12] at this
    rw [hu] at this
    have hm := hmoney_small 1
    nlinarith [hδε, hε]
  -- the sold goods are worth more than 33 to agent 2
  have hU : (33 : ℝ) < ∑ g ∈ o.sold, (fnU g : ℝ) := by
    have hu : util (instV 2) o 2 = o.money 2 := by
      simp [util, instV]
    have hmon := hmoney_le 2
    rw [hu] at h2
    rw [hsoldU] at hmon
    have hkey : 33 * δ + 36 * ε * δ ≤ δ * ∑ g ∈ o.sold, (fnU g : ℝ) := by
      nlinarith [h2, hmon]
    have hkey' : δ * (33 + 36 * ε) ≤ δ * ∑ g ∈ o.sold, (fnU g : ℝ) := by nlinarith [hkey]
    have := le_of_mul_le_mul_left hkey' hδ0
    nlinarith [hε]
  -- contradiction with the Feige–Norkin instance
  have hdisj : ∀ i k : Fin 3, i ≠ k →
      Disjoint (![o.kept 0, o.kept 1, o.sold] i) (![o.kept 0, o.kept 1, o.sold] k) := by
    intro i k hik
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hi3 with rfl | rfl | rfl <;> rcases hk3 with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact absurd rfl hik
        | exact hvalid.2.1 0 1 (by decide)
        | exact hvalid.2.1 1 0 (by decide)
        | exact (hvalid.1 0).symm
        | exact (hvalid.1 1).symm
        | exact hvalid.1 0
        | exact hvalid.1 1
  obtain ⟨i, hi⟩ := feigeNorkin_disjoint ![o.kept 0, o.kept 1, o.sold] hdisj
  · have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi3 with rfl | rfl | rfl
    · simp only [fnW, Matrix.cons_val_zero] at hi
      have : (∑ g ∈ o.kept 0, (fnR g : ℝ)) ≤ 33 := by
        rw [← Nat.cast_sum]
        exact_mod_cast hi
      linarith
    · simp only [fnW, Matrix.cons_val_one] at hi
      have : (∑ g ∈ o.kept 1, (fnC g : ℝ)) ≤ 33 := by
        rw [← Nat.cast_sum]
        exact_mod_cast hi
      linarith
    · simp only [fnW, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
      have : (∑ g ∈ o.sold, (fnU g : ℝ)) ≤ 33 := by
        rw [← Nat.cast_sum]
        exact_mod_cast hi
      linarith

/-- **Proposition 1**, packaged: for every `ρ > 11/12` there is an allocation instance with
`n = 3` agents and `m = 8` goods (non-negative additive valuations, non-negative prices) in
which no valid outcome gives every agent `ρ` times her maximin share with selling. -/
theorem eleven_twelfths_gap {ρ : ℝ} (hρ : 11/12 < ρ) :
    ∃ (v : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i g, 0 ≤ v i g) ∧ (∀ g, 0 ≤ p g) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, util (v i) o i < ρ * MMS 3 (v i) p := by
  refine ⟨instV, instP (min (ρ - 11/12) 1 / 12), instV_nonneg, instP_nonneg ?_,
    no_rho_MMS_three_eight hρ⟩
  have : 0 < min (ρ - 11/12) 1 := lt_min (by linarith) one_pos
  positivity

end ElevenTwelfths

end FairSelling
