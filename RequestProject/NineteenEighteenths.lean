import Mathlib
import RequestProject.ChoresExamples
import RequestProject.ChoresMMSPartition
import RequestProject.FeigeNorkinChores

/-!
# The `19/18` MMS gap for chores with outsourcing (Theorem 5, impossibility half)

Building on the Feige–Norkin chores instance of `RequestProject.FeigeNorkinChores`, this file
constructs, for every `ρ < 19/18`, an instance of the model *with optional outsourcing*
consisting of `n = 3` agents and `m = 8` chores in which **no** feasible outcome keeps every
agent's cost at or below `ρ` times her maximin share.

The instance mirrors the manuscript's `11/12` construction for goods with selling
(`RequestProject.ElevenTwelfths`), with the roles of "money" reversed.  With `cR, cC, cU` the
three Feige–Norkin chores cost vectors (scaled by `20`, so that all targets are `360` rather
than `18`) and a large factor `λ ≥ 2`:

* agent `0` has cost function `cR`, agent `1` has cost function `cC`;
* the outsourcing price is `p = λ · cU`, and agent `2`'s cost function is `p` itself.

Since `p` dominates `cR` and `cC` chore by chore, outsourcing never helps agents `0` and `1`
and their maximin shares are the classical ones, `360`.  Agent `2`, on the contrary, is
indifferent between doing a chore and outsourcing it, so all her cost is *divisible* and her
maximin share is her proportional share `360 λ`.  Taking `λ` large forces a `ρ`-approximate
outcome to give agents `0` and `1` bundles costing less than `380` and to leave a set of
chores (those outsourced or handled by agent `2`) of `cU`-cost less than `380` — which is
exactly what `FeigeNorkinChores.feigeNorkinChores_cover` forbids.

Main results:

* `MMS_agent_zero`, `MMS_agent_one`, `MMS_agent_two` — the maximin shares of the instance;
* `no_rho_MMS_chores_three_eight` — the impossibility;
* `nineteen_eighteenths_gap_chores` — the packaged statement.
-/

open scoped BigOperators

namespace FairChores

namespace NineteenEighteenths

open FeigeNorkinChores

/-- Casting a natural-number bundle cost to `ℝ`. -/
lemma cast_sum_eq (s : Finset (Fin 8)) (w : Fin 8 → ℕ) (m : ℕ) (h : ∑ t ∈ s, w t = m) :
    ∑ t ∈ s, (w t : ℝ) = m := by
  rw [← Nat.cast_sum, h]

/-- The outsourcing price of the instance: a large multiple `λ` of the third Feige–Norkin
cost vector `cU`. -/
noncomputable def instP (lam : ℝ) : Fin 8 → ℝ := fun t => lam * (fcU t : ℝ)

/-- The three cost functions of the instance: the first two agents use the Feige–Norkin cost
vectors `cR` and `cC`, the third agent's cost equals the outsourcing price (she is
indifferent between performing a chore and paying for it). -/
noncomputable def instC (lam : ℝ) : Fin 3 → Fin 8 → ℝ :=
  ![fun t => (fcR t : ℝ), fun t => (fcC t : ℝ), instP lam]

lemma instP_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : ∀ t, 0 ≤ instP lam t :=
  fun t => mul_nonneg hlam (by positivity)

lemma instC_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : ∀ i t, 0 ≤ instC lam i t := by
  intro i t
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl <;>
    simp only [instC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  · positivity
  · positivity
  · exact instP_nonneg hlam t

lemma instP_sum (lam : ℝ) : (∑ t, instP lam t) = 1080 * lam := by
  have h : (∑ t, instP lam t) = lam * ∑ t, (fcU t : ℝ) := by
    rw [Finset.mul_sum]; rfl
  rw [h, cast_sum_eq Finset.univ fcU 1080 fcU_total]
  ring

/-- For `λ ≥ 2`, the outsourcing price dominates agent `0`'s cost chore by chore. -/
lemma R_le_instP {lam : ℝ} (hlam : 2 ≤ lam) (t : Fin 8) : (fcR t : ℝ) ≤ instP lam t := by
  have h1 : (fcR t : ℝ) ≤ 2 * (fcU t : ℝ) := by
    have := (two_fcU_dominates t).1
    exact_mod_cast this
  have h2 : 2 * (fcU t : ℝ) ≤ lam * (fcU t : ℝ) :=
    mul_le_mul_of_nonneg_right hlam (by positivity)
  simpa [instP] using h1.trans h2

/-- For `λ ≥ 2`, the outsourcing price dominates agent `1`'s cost chore by chore. -/
lemma C_le_instP {lam : ℝ} (hlam : 2 ≤ lam) (t : Fin 8) : (fcC t : ℝ) ≤ instP lam t := by
  have h1 : (fcC t : ℝ) ≤ 2 * (fcU t : ℝ) := by
    have := (two_fcU_dominates t).2
    exact_mod_cast this
  have h2 : 2 * (fcU t : ℝ) ≤ lam * (fcU t : ℝ) :=
    mul_le_mul_of_nonneg_right hlam (by positivity)
  simpa [instP] using h1.trans h2

/-! ### The maximin shares of the instance -/

/-- Agent `0`'s maximin share is `360` (that is, `18` before scaling). -/
theorem MMS_agent_zero {lam : ℝ} (hlam : 2 ≤ lam) :
    MMS 3 (instC lam 0) (instP lam) = 360 := by
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  have hc : ∀ t, 0 ≤ instC lam 0 t := fun t => instC_nonneg hlam0 0 t
  have hcbar : ∀ t, cbar (instC lam 0) (instP lam) t = (fcR t : ℝ) := by
    intro t
    have := R_le_instP hlam t
    simp only [cbar, instC, Matrix.cons_val_zero]
    exact min_eq_left this
  refine le_antisymm ?_ ?_
  · -- the explicit partition into three bundles of cost `360`
    refine MMS_le_of_outcome (n := 3) hc (by norm_num)
      (o := ⟨∅, ![{2, 3, 4}, {0, 1}, {5, 6, 7}], fun _ => 0⟩) ?_ ?_
    · refine ⟨fun _ => by simp, ?_, ?_, fun _ => le_rfl, by simp⟩
      · intro j k hjk
        have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
        have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
        rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
          first
            | (exact absurd rfl hjk)
            | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Matrix.cons_val_two, Matrix.tail_cons]; decide)
      · simp only [Finset.empty_union]
        decide
    · intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl <;>
        · simp only [cost, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons, add_zero, instC]
          rw [cast_sum_eq _ fcR 360 (by decide)]
          norm_num
  · -- the total effective cost is `1080`
    have hbound := cbarSum_univ_le_nsmul_MMS (c := instC lam 0) (p := instP lam) (n := 3)
      hc (by norm_num)
    have hsum : cbarSum (instC lam 0) (instP lam) Finset.univ = 1080 := by
      simp only [cbarSum]
      rw [Finset.sum_congr rfl (fun t _ => hcbar t)]
      exact cast_sum_eq _ fcR 1080 fcR_total
    rw [hsum] at hbound
    norm_num at hbound
    linarith

/-- Agent `1`'s maximin share is `360`. -/
theorem MMS_agent_one {lam : ℝ} (hlam : 2 ≤ lam) :
    MMS 3 (instC lam 1) (instP lam) = 360 := by
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  have hc : ∀ t, 0 ≤ instC lam 1 t := fun t => instC_nonneg hlam0 1 t
  have hcbar : ∀ t, cbar (instC lam 1) (instP lam) t = (fcC t : ℝ) := by
    intro t
    have := C_le_instP hlam t
    simp only [cbar, instC, Matrix.cons_val_one]
    exact min_eq_left this
  refine le_antisymm ?_ ?_
  · refine MMS_le_of_outcome (n := 3) hc (by norm_num)
      (o := ⟨∅, ![{2, 5}, {0, 3, 6}, {1, 4, 7}], fun _ => 0⟩) ?_ ?_
    · refine ⟨fun _ => by simp, ?_, ?_, fun _ => le_rfl, by simp⟩
      · intro j k hjk
        have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
        have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
        rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
          first
            | (exact absurd rfl hjk)
            | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Matrix.cons_val_two, Matrix.tail_cons]; decide)
      · simp only [Finset.empty_union]
        decide
    · intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl <;>
        · simp only [cost, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons, add_zero, instC]
          rw [cast_sum_eq _ fcC 360 (by decide)]
          norm_num
  · have hbound := cbarSum_univ_le_nsmul_MMS (c := instC lam 1) (p := instP lam) (n := 3)
      hc (by norm_num)
    have hsum : cbarSum (instC lam 1) (instP lam) Finset.univ = 1080 := by
      simp only [cbarSum]
      rw [Finset.sum_congr rfl (fun t _ => hcbar t)]
      exact cast_sum_eq _ fcC 1080 fcC_total
    rw [hsum] at hbound
    norm_num at hbound
    linarith

/-- Agent `2` is indifferent between performing a chore and paying for it, so all her cost is
divisible and her maximin share is her proportional share `360 λ`. -/
theorem MMS_agent_two {lam : ℝ} (hlam0 : 0 ≤ lam) :
    MMS 3 (instC lam 2) (instP lam) = 360 * lam := by
  have hc : ∀ t, 0 ≤ instC lam 2 t := fun t => instC_nonneg hlam0 2 t
  have hcbar : ∀ t, cbar (instC lam 2) (instP lam) t = instP lam t := by
    intro t
    simp only [cbar, instC, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, min_self]
  refine le_antisymm ?_ ?_
  · -- outsource everything and split the bill in three
    refine MMS_le_of_outcome (n := 3) hc (by norm_num)
      (o := ⟨Finset.univ, fun _ => ∅, fun _ => 360 * lam⟩) ?_ ?_
    · refine ⟨fun _ => by simp, fun _ _ _ => by simp, by simp, fun _ => by positivity, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [instP_sum]
      push_cast
      linarith
    · intro j
      simp only [cost, Finset.sum_empty, zero_add]
      exact le_rfl
  · have hbound := cbarSum_univ_le_nsmul_MMS (c := instC lam 2) (p := instP lam) (n := 3)
      hc (by norm_num)
    have hsum : cbarSum (instC lam 2) (instP lam) Finset.univ = 1080 * lam := by
      simp only [cbarSum]
      rw [Finset.sum_congr rfl (fun t _ => hcbar t)]
      exact instP_sum lam
    rw [hsum] at hbound
    norm_num at hbound
    linarith

/-! ### The impossibility -/

/-- The scaling factor used for a given approximation ratio `ρ < 19/18`. -/
noncomputable def lamOf (rho : ℝ) : ℝ := 2 + 720 * |rho| / (380 - 360 * rho)

lemma lamOf_ge_two {rho : ℝ} (hrho : rho < 19/18) : 2 ≤ lamOf rho := by
  have hden : 0 < 380 - 360 * rho := by linarith
  have : 0 ≤ 720 * |rho| / (380 - 360 * rho) :=
    div_nonneg (by positivity) hden.le
  simp only [lamOf]; linarith

lemma lamOf_key {rho : ℝ} (hrho : rho < 19/18) : 720 * rho < lamOf rho * (380 - 360 * rho) := by
  have hden : 0 < 380 - 360 * rho := by linarith
  have hfrac : 720 * |rho| / (380 - 360 * rho) * (380 - 360 * rho) = 720 * |rho| := by
    field_simp
  have habs : rho ≤ |rho| := le_abs_self rho
  have hexp : lamOf rho * (380 - 360 * rho)
      = 2 * (380 - 360 * rho) + 720 * |rho| := by
    simp only [lamOf, add_mul, hfrac]
  rw [hexp]
  nlinarith [habs, hden]

/-- **Theorem 5 (impossibility half), the `19/18` gap for chores with outsourcing.**  For
every `ρ < 19/18` there is an instance with three agents and eight chores in which every
feasible outcome leaves some agent with a cost strictly larger than `ρ` times her maximin
share. -/
theorem no_rho_MMS_chores_three_eight {rho : ℝ} (hrho : rho < 19/18) :
    ∀ o : Outcome (Fin 8) 3, o.Valid (instP (lamOf rho)) →
      ∃ i, rho * MMS 3 (instC (lamOf rho) i) (instP (lamOf rho))
        < cost (instC (lamOf rho) i) o i := by
  classical
  set lam := lamOf rho with hlamdef
  have hlam2 : 2 ≤ lam := lamOf_ge_two hrho
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  have hkey : 720 * rho < lam * (380 - 360 * rho) := lamOf_key hrho
  have hrho380 : 360 * rho < 380 := by linarith
  intro o hvalid
  by_contra hcon
  push_neg at hcon
  obtain ⟨hdo, hdk, hcov, hpay0, hbudget⟩ := hvalid
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  rw [MMS_agent_zero hlam2] at h0
  rw [MMS_agent_one hlam2] at h1
  rw [MMS_agent_two hlam0] at h2
  -- the three costs, spelled out
  have hc0 : (∑ t ∈ o.kept 0, (fcR t : ℝ)) + o.pay 0 ≤ rho * 360 := by
    simpa [cost, instC] using h0
  have hc1 : (∑ t ∈ o.kept 1, (fcC t : ℝ)) + o.pay 1 ≤ rho * 360 := by
    simpa [cost, instC] using h1
  have hc2 : (∑ t ∈ o.kept 2, instP lam t) + o.pay 2 ≤ rho * (360 * lam) := by
    simpa [cost, instC] using h2
  -- agent `0` and agent `1` keep bundles costing less than `380`
  have hR : (∑ t ∈ o.kept 0, (fcR t : ℝ)) < 380 := by
    have := hpay0 0
    linarith
  have hC : (∑ t ∈ o.kept 1, (fcC t : ℝ)) < 380 := by
    have := hpay0 1
    linarith
  -- the chores that are outsourced or performed by agent `2` are cheap for agent `2`
  set B2 : Finset (Fin 8) := o.outsourced ∪ o.kept 2 with hB2
  have hdisj2 : Disjoint o.outsourced (o.kept 2) := hdo 2
  have hsplit : (∑ t ∈ B2, instP lam t)
      = (∑ t ∈ o.outsourced, instP lam t) + ∑ t ∈ o.kept 2, instP lam t := by
    rw [hB2, Finset.sum_union hdisj2]
  have hpay01 : o.pay 0 ≤ rho * 360 ∧ o.pay 1 ≤ rho * 360 := by
    constructor
    · have : (0:ℝ) ≤ ∑ t ∈ o.kept 0, (fcR t : ℝ) := Finset.sum_nonneg (fun t _ => by positivity)
      linarith
    · have : (0:ℝ) ≤ ∑ t ∈ o.kept 1, (fcC t : ℝ) := Finset.sum_nonneg (fun t _ => by positivity)
      linarith
  have hsum3 : ∑ j, o.pay j = o.pay 0 + o.pay 1 + o.pay 2 := by
    rw [Fin.sum_univ_three]
  have houts : (∑ t ∈ o.outsourced, instP lam t) ≤ o.pay 0 + o.pay 1 + o.pay 2 := by
    rw [← hsum3]; exact hbudget
  have hB2bound : (∑ t ∈ B2, instP lam t) ≤ 720 * rho + rho * (360 * lam) := by
    rw [hsplit]
    linarith [hpay01.1, hpay01.2, hc2]
  have hB2eq : (∑ t ∈ B2, instP lam t) = lam * ∑ t ∈ B2, (fcU t : ℝ) := by
    rw [Finset.mul_sum]; rfl
  have hU : (∑ t ∈ B2, (fcU t : ℝ)) < 380 := by
    have hlt : lam * ∑ t ∈ B2, (fcU t : ℝ) < lam * 380 := by
      rw [← hB2eq]
      nlinarith [hB2bound, hkey]
    have hlampos : (0:ℝ) < lam := by linarith
    exact lt_of_mul_lt_mul_left hlt hlampos.le
  -- every chore is kept by agent `0`, kept by agent `1`, or in `B2`
  have hcover : ∀ t : Fin 8,
      t ∈ (![o.kept 0, o.kept 1, B2] : Fin 3 → Finset (Fin 8)) 0 ∨
      t ∈ (![o.kept 0, o.kept 1, B2] : Fin 3 → Finset (Fin 8)) 1 ∨
      t ∈ (![o.kept 0, o.kept 1, B2] : Fin 3 → Finset (Fin 8)) 2 := by
    intro t
    have hmem : t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept := by
      rw [hcov]; exact Finset.mem_univ t
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rcases Finset.mem_union.mp hmem with h | h
    · exact Or.inr (Or.inr (Finset.mem_union_left _ h))
    · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp h
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hk3 with rfl | rfl | rfl
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr (Finset.mem_union_right _ hk))
  obtain ⟨i, hi⟩ := feigeNorkinChores_cover ![o.kept 0, o.kept 1, B2] hcover
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl
  · simp only [fcW, Matrix.cons_val_zero] at hi
    have : (380 : ℝ) ≤ ∑ t ∈ o.kept 0, (fcR t : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hi
    linarith
  · simp only [fcW, Matrix.cons_val_one] at hi
    have : (380 : ℝ) ≤ ∑ t ∈ o.kept 1, (fcC t : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hi
    linarith
  · simp only [fcW, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
    have : (380 : ℝ) ≤ ∑ t ∈ B2, (fcU t : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hi
    linarith

/-- **The `19/18` gap for chores with outsourcing**, packaged: for every `ρ < 19/18` there is
an instance with `n = 3` agents and `m = 8` chores (non-negative additive costs, non-negative
outsourcing prices) in which no feasible outcome keeps every agent's cost at or below `ρ`
times her maximin share. -/
theorem nineteen_eighteenths_gap_chores {rho : ℝ} (hrho : rho < 19/18) :
    ∃ (c : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i t, 0 ≤ c i t) ∧ (∀ t, 0 ≤ p t) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, rho * MMS 3 (c i) p < cost (c i) o i := by
  have hlam2 : 2 ≤ lamOf rho := lamOf_ge_two hrho
  have hlam0 : (0:ℝ) ≤ lamOf rho := by linarith
  exact ⟨instC (lamOf rho), instP (lamOf rho), instC_nonneg hlam0, instP_nonneg hlam0,
    no_rho_MMS_chores_three_eight hrho⟩

/-- **Theorem 5 (impossibility half), in the manuscript's `ε`-form.**  For every `ε > 0`
there is an allocation instance with chores and optional outsourcing that has no
`(19/18 − ε)`-MMS allocation. -/
theorem no_MMS_approx_below_nineteen_eighteenths {eps : ℝ} (heps : 0 < eps) :
    ∃ (c : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i t, 0 ≤ c i t) ∧ (∀ t, 0 ≤ p t) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, (19/18 - eps) * MMS 3 (c i) p < cost (c i) o i :=
  nineteen_eighteenths_gap_chores (by linarith)

end NineteenEighteenths

end FairChores
