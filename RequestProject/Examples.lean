import Mathlib
import RequestProject.ThreeAgents
import RequestProject.TPSCompute
import RequestProject.TPSApprox

/-!
# Worked examples

Small, fully computed instances of the model.  They serve as sanity checks that the definitions
of `MMS`, `TPS` and `PS` are not degenerate, and they exercise the computation theorem
`TPS_eq_bracket_formula` on a concrete instance.

* `MMS_selling_example` — one worthless good with market price `2` and two agents: the maximin
  share *with selling* is `1`, whereas the classical maximin share (no selling) would be `0`.
* `TPS_example` — two goods worth `3` and `1`, no market value, two agents:
  `MMS = TPS = 1 < 2 = PS`.  The value of the `TPS` is obtained from the bracket formula.
-/

open scoped BigOperators

namespace FairSelling

namespace Examples

/-! ### Selling strictly increases the maximin share -/

/-- One good, worthless to both agents, with market price `2`. -/
def vsell : Fin 1 → ℝ := ![0]

/-- Its market price. -/
def psell : Fin 1 → ℝ := ![2]

/-- With selling, the two-agent maximin share of the single worthless-but-priced good is `1`
(sell it and split the proceeds); without selling it would be `0`. -/
theorem MMS_selling_example : MMS 2 vsell psell = 1 := by
  have hv : ∀ g, 0 ≤ vsell g := by
    intro g; fin_cases g; norm_num [vsell]
  have hp : ∀ g, 0 ≤ psell g := by
    intro g; fin_cases g; norm_num [psell]
  refine le_antisymm ?_ ?_
  · -- `MMS ≤ TPS ≤ PS = 1`
    have h := MMS_le_TPS_le_PS vsell psell (n := 2) (by norm_num) hv hp
    have hPS : PS 2 vsell psell = 1 := by
          simp [PS, vsell, psell]
    linarith [h.1, h.2, hPS.le, hPS.ge]
  · -- sell the good and give each agent half of the proceeds
    refine le_MMS_of_outcome (by norm_num) vsell psell hv hp
      ⟨Finset.univ, fun _ => ∅, fun _ => 1⟩ ?_ 1 ?_
    · refine ⟨fun _ => by simp, fun _ _ _ => by simp, fun _ => by norm_num, ?_⟩
      simp [psell]
    · intro j; simp [util]

/-! ### A worked `TPS` computation -/

/-- Two goods, worth `3` and `1`. -/
def vex : Fin 2 → ℝ := ![3, 1]

/-- Neither good has any market value. -/
def pex : Fin 2 → ℝ := ![0, 0]

private lemma truncSum_ex (t : ℝ) (ht0 : 0 ≤ t) :
    truncSum 2 vex pex t = (min 3 t + min 1 t) / 2 := by
  simp only [truncSum, Fin.sum_univ_two, vex, pex, Matrix.cons_val_zero, Matrix.cons_val_one,
    ]
  rw [max_eq_right (le_min (by norm_num) ht0), max_eq_right (le_min (by norm_num) ht0)]
  norm_num

/-- The proportional share of the instance is `2`. -/
theorem PS_example : PS 2 vex pex = 2 := by
  simp only [PS, Fin.sum_univ_two, vex, pex, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The truncated proportional share of the instance is `1`, computed through the bracket
formula of `TPS_eq_bracket_formula` on the interval `[1, 3]`. -/
theorem TPS_example : TPS 2 vex pex = 1 := by
  have hp : ∀ g, 0 ≤ pex g := by
    intro g; fin_cases g <;> norm_num [pex]
  have hf1 : truncSum 2 vex pex 1 = 1 := by
    rw [truncSum_ex 1 (by norm_num)]; norm_num
  have hf3 : truncSum 2 vex pex 3 = 2 := by
    rw [truncSum_ex 3 (by norm_num)]; norm_num
  have hvvals : ∀ g, vex g = 3 ∨ vex g = 1 := by
    intro g; fin_cases g
    · left; norm_num [vex]
    · right; norm_num [vex]
  have hnb : NoBreak vex pex 1 3 := by
    intro g
    refine ⟨?_, Or.inl (by rw [show pex g = 0 from by fin_cases g <;> norm_num [pex]]; norm_num)⟩
    rcases hvvals g with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h])
  obtain ⟨-, hval, -, -⟩ :=
    TPS_eq_bracket_formula (n := 2) vex pex (by norm_num) hp (by norm_num) hnb
      (by rw [hf1]) (by rw [hf3]; norm_num)
      (fun g hg => by
        rcases hvvals g with h | h
        · rw [h, hf3]; norm_num
        · rw [h] at hg; norm_num at hg)
      (fun g hg => by
        rw [show pex g = 0 from by fin_cases g <;> norm_num [pex]] at hg
        norm_num at hg)
  rw [hval]
  have hslope : (slopeGoods vex pex 1 3).card = 1 := by
    have : slopeGoods vex pex 1 3 = {0} := by
      ext g
      fin_cases g <;> simp [slopeGoods, vex, pex]
    rw [this]; rfl
  have hflat : flatConst vex pex 1 3 = 1 := by
    have hset : (Finset.univ.filter (fun g => ¬ ((3:ℝ) ≤ vex g ∧ pex g ≤ 1)))
        = ({1} : Finset (Fin 2)) := by
      ext g
      fin_cases g <;> simp [vex, pex]
    rw [flatConst, hset, Finset.sum_singleton]
    norm_num [vex, pex]
  rw [hslope, hflat]
  norm_num

/-- The maximin share with selling of the instance is `1`: it equals the `TPS` here, and both
are strictly below the proportional share `2`. -/
theorem MMS_example : MMS 2 vex pex = 1 := by
  have hv : ∀ g, 0 ≤ vex g := by
    intro g; fin_cases g <;> norm_num [vex]
  have hp : ∀ g, 0 ≤ pex g := by
    intro g; fin_cases g <;> norm_num [pex]
  refine le_antisymm ?_ ?_
  · have h := (MMS_le_TPS_le_PS vex pex (n := 2) (by norm_num) hv hp).1
    rw [TPS_example] at h
    exact h
  · -- give the first good to agent `0` and the second to agent `1`
    refine le_MMS_of_outcome (by norm_num) vex pex hv hp
      ⟨∅, fun j => {j}, fun _ => 0⟩ ?_ 1 ?_
    · refine ⟨fun _ => by simp, fun j k hjk => by simpa using hjk, fun _ => le_refl 0, by simp⟩
    · intro j
      fin_cases j <;> simp [util] <;> norm_num [vex]

end Examples

end FairSelling
