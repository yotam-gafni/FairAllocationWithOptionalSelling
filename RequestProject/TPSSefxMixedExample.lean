import Mathlib
import RequestProject.TPSSefxPhaseImp

/-!
# Sharing is unavoidable in Algorithm 6

`RequestProject/TPSSefxPhaseImp.lean` runs the manuscript's Algorithm 6 in its three loops.  The
large-good loops allow **sharing**: an expensive good is sold and only a slice of its proceeds is
handed to the claimant, the rest staying free in the bank, so several agents may be served out of
one sold good (`PhaseTPS.pshare_step`).  The bag-filling loop, on the contrary, avoids sharing
entirely (`PhaseTPS.pbagfill_step`).

This file shows on an explicit instance that sharing really is needed — **already at the very
first step of the algorithm**: there is a stage at which no *pure* good can be sold, nothing is
in the bank, and no bag can be filled, so the only way forward is to sell a good that some agent
values above its price and hand out only part of the proceeds.

## The instance

Two agents, three goods:

| good           | `g₀`  | `g₁` | `g₂` |
|----------------|-------|------|------|
| `v₀`           | `0`   | `0`  | `0`  |
| `v₁`           | `100` | `6`  | `6`  |
| market price   | `4`   | `0`  | `0`  |

* `TPS₀ = 2` (`mixedTPS_zero`), so the threshold of agent `0` is `τ₀ = (2/3)·2 = 4/3` and
  `2·τ₀ = 8/3 < 4 = p(g₀)`: the good `g₀` is **expensive** for agent `0`, and giving it to
  anybody — or selling it and putting its whole price aside for one agent — would cost agent `0`
  more than the `2·τ₀` that the counting invariant allows.  So the pool cannot be bag-filled.

* `TPS₁ ≥ 12` (`mixedTPS_one_ge`), so agent `1` values every good strictly above its price after
  truncation: **no good is pure** (`mixed_not_pure`).  Selling any of them loses agent `1`
  something, so the pure moving knife of `PhaseTPS.pmoney_step` has nothing to cut, and the bank
  is empty at the start.

`mixed_case_reached` puts the three facts together.  `PhaseTPS.pshare_step` resolves exactly this
situation: `g₀` is sold, the claimant (agent `0`, whose threshold `4/3` is the smallest) receives
the slice `4/3`, the remaining `8/3` stays in the bank for agent `1`, and `g₀` is charged to
agent `0`, which holds nothing but that slice — its package costs agent `1` only
`4/3 + loss₁(g₀) = 4/3 + 8 ≤ 2·τ₁ = 16`.
-/
open scoped BigOperators

namespace FairSelling

namespace MixedGood

/-- The market prices: the first good costs `4`, the others are free. -/
noncomputable def mp : Fin 3 → ℝ := ![4, 0, 0]

/-- The valuations: agent `0` values nothing, agent `1` values the first good at `100` and each
of the other two at `6`. -/
noncomputable def mv : Fin 2 → Fin 3 → ℝ := ![![0, 0, 0], ![100, 6, 6]]

lemma mp_nonneg : ∀ g, 0 ≤ mp g := by
  intro g; fin_cases g <;> simp [mp]

lemma mv_nonneg : ∀ i g, 0 ≤ mv i g := by
  intro i g; fin_cases i <;> fin_cases g <;> simp [mv]

/-! ### The two truncated proportional shares -/

/-- Agent `0` values nothing, so its truncated proportional share is half the total price. -/
theorem mixedTPS_zero : TPS 2 (mv 0) mp = 2 := by
  have hPS : PS 2 (mv 0) mp = 2 := by
    unfold PS
    rw [Fin.sum_univ_three]
    simp [mv, mp]
    norm_num
  refine le_antisymm ?_ ?_
  · have := TPS_le_PS (n := 2) (mv 0) mp mp_nonneg
    rw [hPS] at this
    exact this
  · refine le_TPS_of_le_truncSum (mv 0) mp ?_
    unfold truncSum
    rw [Fin.sum_univ_three]
    simp [mv, mp]
    norm_num

/-- Agent `1` has a truncated proportional share of at least `12`: `t = 12` is a fixed point of
the truncated-proportional map, `(12 + 6 + 6)/2 = 12`. -/
theorem mixedTPS_one_ge : (12 : ℝ) ≤ TPS 2 (mv 1) mp := by
  refine le_TPS_of_le_truncSum (mv 1) mp ?_
  unfold truncSum
  rw [Fin.sum_univ_three]
  rw [show mp 0 = 4 from rfl, show mp 1 = 0 from rfl, show mp 2 = 0 from rfl,
    show mv 1 0 = 100 from rfl, show mv 1 1 = 6 from rfl, show mv 1 2 = 6 from rfl]
  norm_num

/-! ### The thresholds -/

theorem mixedThr_zero : GeneralTPS.thr mv mp 0 = 4 / 3 := by
  unfold GeneralTPS.thr
  rw [mixedTPS_zero]
  norm_num

theorem mixedThr_one_ge : (8 : ℝ) ≤ GeneralTPS.thr mv mp 1 := by
  unfold GeneralTPS.thr
  have := mixedTPS_one_ge
  norm_num
  linarith

/-- Both thresholds are positive. -/
theorem mixedThr_pos (j : Fin 2) : 0 < GeneralTPS.thr mv mp j := by
  fin_cases j
  · exact lt_of_lt_of_eq (by norm_num) mixedThr_zero.symm
  · exact lt_of_lt_of_le (by norm_num) mixedThr_one_ge

/-- **The first good is expensive for agent `0`.** -/
theorem mixed_expensive : 2 * GeneralTPS.thr mv mp 0 < mp 0 := by
  rw [mixedThr_zero]
  simp [mp]
  norm_num

/-! ### No good is pure -/

/-- **No good is pure**: agent `1` values every good, after truncation at its own truncated
proportional share, strictly above its market price, so selling it loses agent `1` something. -/
theorem mixed_not_pure (g : Fin 3) : ¬ PhaseTPS.PureGood mv mp (∅ : Finset (Fin 2)) g := by
  intro h
  have h1 := h 1 (by simp)
  have hT := mixedTPS_one_ge
  unfold ChargeTPS.saleLoss trunc at h1
  have hmvpos : 6 ≤ mv 1 g := by fin_cases g <;> norm_num [mv]
  have hmp4 : mp g ≤ 4 := by fin_cases g <;> norm_num [mp]
  have h2 : (6 : ℝ) ≤ min (mv 1 g) (TPS 2 (mv 1) mp) := le_min hmvpos (by linarith)
  have h3 : (6 : ℝ) ≤ max (mp g) (min (mv 1 g) (TPS 2 (mv 1) mp)) :=
    le_trans h2 (le_max_right _ _)
  linarith

/-! ### The initial stage of Algorithm 6 -/

lemma empty_pool : (PhaseTPS.emptyPStage (Fin 3) 2).pool = Finset.univ := by
  ext x
  simp [PhaseTPS.PStage.pool, PhaseTPS.PStage.sold, PhaseTPS.PStage.charge,
    PhaseTPS.emptyPStage]

lemma empty_served : (PhaseTPS.emptyPStage (Fin 3) 2).served = (∅ : Finset (Fin 2)) := rfl

lemma empty_bank : (PhaseTPS.emptyPStage (Fin 3) 2).bank = 0 := rfl

lemma empty_req (eps : ℝ) (j : Fin 2) :
    (PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps j = GeneralTPS.thr mv mp j := by
  simp [PhaseTPS.PStage.req, PhaseTPS.emptyPStage]

/-- The slice the moving knife would have to cut at the initial stage is positive: both agents
have a positive threshold. -/
theorem mixed_Qc_pos (eps : ℝ) :
    0 < CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0 (∅ : Finset (Fin 3)) := by
  have hgap : 0 < CfgTPS.gapMin mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
      (∅ : Finset (Fin 3)) := by
    unfold CfgTPS.gapMin
    rw [Finset.lt_inf'_iff]
    intro j _
    rw [empty_req]
    have hv : vbarSum (mv j) mp (∅ : Finset (Fin 3)) = 0 := by simp [vbarSum]
    rw [hv]
    have := mixedThr_pos j
    linarith
  have : CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
      (∅ : Finset (Fin 3)) = max 0 _ := rfl
  rw [this]
  exact lt_of_lt_of_le hgap (le_max_right _ _)

/-- **The sharing case of Algorithm 6 is reached at the first step.**  At the initial stage of
Algorithm 6 on this instance the good `g₀` is in the pool and expensive for the unserved agent
`0`, it is not pure, and the pure moving knife cannot be run because there is no money in the
bank and no pure good to sell.  The only way forward is `PhaseTPS.pshare_step`: sell `g₀` and
hand out only part of its proceeds. -/
theorem mixed_case_reached (eps : ℝ) :
    (PhaseTPS.emptyPStage (Fin 3) 2).Good mv mp eps ∧
    (0 : Fin 2) ∉ (PhaseTPS.emptyPStage (Fin 3) 2).served ∧
    (0 : Fin 3) ∈ (PhaseTPS.emptyPStage (Fin 3) 2).pool ∧
    2 * GeneralTPS.thr mv mp 0 < mp 0 ∧
    ¬ PhaseTPS.PureGood mv mp (PhaseTPS.emptyPStage (Fin 3) 2).served 0 ∧
    (∀ F : Finset (Fin 3), F ⊆ (PhaseTPS.emptyPStage (Fin 3) 2).pool →
      (∀ x ∈ F, PhaseTPS.PureGood mv mp (PhaseTPS.emptyPStage (Fin 3) 2).served x) →
      (PhaseTPS.emptyPStage (Fin 3) 2).bank + ∑ x ∈ F, mp x
        < CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
            (∅ : Finset (Fin 3))) := by
  refine ⟨PhaseTPS.good_emptyPStage mv mp eps, by simp [empty_served], ?_,
    mixed_expensive, ?_, ?_⟩
  · rw [empty_pool]; exact Finset.mem_univ _
  · rw [empty_served]; exact mixed_not_pure 0
  · intro F _ hFpure
    have hFempty : F = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
      have := hFpure x hx
      rw [empty_served] at this
      exact mixed_not_pure x this
    rw [hFempty, empty_bank]
    simpa using mixed_Qc_pos eps

end MixedGood

end FairSelling
