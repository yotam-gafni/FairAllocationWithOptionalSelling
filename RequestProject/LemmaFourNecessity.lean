import Mathlib
import RequestProject.MatchingPhase

/-!
# The price condition in Lemma 4 is necessary

The cash-aware form of the manuscript's Lemma 4 (`FairSelling.LemmaFourCash`) carries the
hypothesis that every force-sold good `f` satisfies `p f ≥ (1 - 3/4) · MMS = MMS / 4`.  This is
condition 1 in the manuscript's definition of a canonical partition.  Here we show that the
hypothesis cannot be dropped: `LemmaFourCashNoPrice` — literally `LemmaFourCash` with that
hypothesis deleted — is *false*, already for six goods.

The witness is the instance with prices identically `0` and values

`37, 13, 37, 13, 37, 13`

for the six goods.  Its three-agent maximin share is `50` (pair each `37` with a `13`), so the
acceptability threshold is `3/4 · 50 = 37.5` and no good is big.  Hand out the bundle consisting
of good `0` alone (worth `37 ≤ 37.5`, so the other agents reject it) while good `2` is sold for
`0`.  The remaining goods are worth `13, 13, 37, 13`, and no two disjoint bundles of them are
both worth more than `37`: every achievable bundle value is of the form `13a + 37b`, and two
such values above `37.5` would have to sum to more than `75`, while the total is only `76`.
-/

open scoped BigOperators

namespace FairSelling

/-- `LemmaFourCash` with the price condition on the force-sold goods deleted. -/
def LemmaFourCashNoPrice (G : Type*) [Fintype G] [DecidableEq G] : Prop :=
  ∀ (w p : G → ℝ), (∀ g, 0 ≤ w g) → (∀ g, 0 ≤ p g) →
    (∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) →
    ∀ (K S : Finset G) (m : ℝ), Disjoint K S → 0 ≤ m → m ≤ ∑ g ∈ S, p g →
      S.card ≤ 1 → (K.card ≤ 1 ∨ m = 0) →
      vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p →
      (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
        (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m))

namespace LemmaFourCounterexample

/-- The values of the six goods (natural numbers, to keep the arithmetic exact). -/
def wn : Fin 6 → ℕ
  | 0 => 37
  | 1 => 13
  | 2 => 37
  | 3 => 13
  | 4 => 37
  | 5 => 13

/-- The valuation of the counterexample. -/
noncomputable def w : Fin 6 → ℝ := fun g => (wn g : ℝ)

/-- All prices are zero: nothing can be gained by selling. -/
def p : Fin 6 → ℝ := fun _ => 0

/-- The three parts of an optimal three-way partition. -/
def parts : Fin 3 → Finset (Fin 6)
  | 0 => {0, 1}
  | 1 => {2, 3}
  | 2 => {4, 5}

lemma hw : ∀ g, 0 ≤ w g := fun _ => Nat.cast_nonneg _

lemma hp : ∀ g, 0 ≤ p g := fun _ => le_refl 0

@[simp] lemma vbar_eq (g : Fin 6) : vbar w p g = w g := by
  simp [vbar, p, w]

lemma wn_sum : ∑ g, wn g = 150 := by decide

lemma parts_sum : ∀ j, ∑ g ∈ parts j, wn g = 50 := by decide

lemma parts_disjoint : ∀ j k : Fin 3, j ≠ k → Disjoint (parts j) (parts k) := by decide

lemma vbarSum_univ : vbarSum w p Finset.univ = 150 := by
  have : vbarSum w p Finset.univ = ((∑ g, wn g : ℕ) : ℝ) := by
    simp only [vbarSum, vbar_eq, w]
    push_cast
    rfl
  rw [this, wn_sum]
  norm_num

/-- The three-agent maximin share of the instance is `50`. -/
lemma MMS_three : MMS 3 w p = 50 := by
  refine le_antisymm ?_ ?_
  · have h := three_MMS_le_vbarSum_univ w p hw hp
    rw [vbarSum_univ] at h
    linarith
  · refine le_MMS_of_outcome (by norm_num) w p hw hp ⟨∅, parts, fun _ => 0⟩ ?_ 50 ?_
    · exact ⟨fun j => by simp, parts_disjoint, fun _ => le_refl 0, by simp⟩
    · intro j
      have hj : ∑ g ∈ parts j, w g = ((∑ g ∈ parts j, wn g : ℕ) : ℝ) := by
        simp only [w]; push_cast; rfl
      simp only [util, hj, parts_sum j]
      norm_num

/-- The removed goods: good `0` is handed out, good `2` is sold (for nothing). -/
def K : Finset (Fin 6) := {0}

/-- The (single) sold good. -/
def S : Finset (Fin 6) := {2}

lemma K_disjoint_S : Disjoint K S := by decide

/-- The remainder of the goods. -/
def R : Finset (Fin 6) := Finset.univ \ (K ∪ S)

/-- The value of the remaining goods, as a natural number, in the cash-augmented world. -/
def cwn : Option (Fin 6) → ℕ
  | none => 0
  | some g => if g ∈ R then wn g else 0

lemma cashVal_eq (x : Option (Fin 6)) : cashVal R w x = (cwn x : ℝ) := by
  cases x with
  | none => simp [cwn]
  | some g => by_cases hg : g ∈ R <;> simp [cwn, restrictVal, hg, w]

lemma cashPrice_eq (x : Option (Fin 6)) : cashPrice R p 0 x = 0 := by
  cases x with
  | none => simp
  | some g => by_cases hg : g ∈ R <;> simp [restrictVal, hg, p]

/-- The combinatorial heart: no two disjoint bundles of the remaining goods are both worth
more than `37`. -/
lemma no_two_bundles : ∀ A B : Finset (Option (Fin 6)), Disjoint A B →
    (∑ x ∈ A, cwn x) ≤ 37 ∨ (∑ x ∈ B, cwn x) ≤ 37 := by
  decide +kernel

/-- The two-agent maximin share of the cash-augmented remainder is at most `37`, hence strictly
below the threshold `37.5`. -/
lemma MMS_two_le : MMS 2 (cashVal R w) (cashPrice R p 0) ≤ 37 := by
  refine csSup_le (MMSset_nonempty _ _) ?_
  rintro r ⟨o, ⟨-, hdisj, hmoney, hbudget⟩, hr⟩
  have hprice : ∑ g ∈ o.sold, cashPrice R p 0 g = 0 :=
    Finset.sum_eq_zero (fun g _ => cashPrice_eq g)
  have hsum0 : ∑ j, o.money j = 0 := by
    rw [hprice] at hbudget
    exact le_antisymm hbudget (Finset.sum_nonneg fun j _ => hmoney j)
  have hmz : ∀ j, o.money j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hmoney j)).mp hsum0 j (Finset.mem_univ j)
  have hutil : ∀ j, util (cashVal R w) o j = ((∑ x ∈ o.kept j, cwn x : ℕ) : ℝ) := by
    intro j
    rw [util, hmz j, add_zero]
    push_cast
    exact Finset.sum_congr rfl (fun x _ => cashVal_eq x)
  rcases no_two_bundles (o.kept 0) (o.kept 1) (hdisj 0 1 (by decide)) with h | h
  · have h1 := hr 0
    rw [hutil 0] at h1
    have h2 : ((∑ x ∈ o.kept 0, cwn x : ℕ) : ℝ) ≤ 37 := by exact_mod_cast h
    linarith
  · have h1 := hr 1
    rw [hutil 1] at h1
    have h2 : ((∑ x ∈ o.kept 1, cwn x : ℕ) : ℝ) ≤ 37 := by exact_mod_cast h
    linarith

end LemmaFourCounterexample

open LemmaFourCounterexample in
/-- **The price condition in Lemma 4 cannot be dropped.**  Without the requirement that a
force-sold good is expensive (`p f ≥ MMS / 4`, condition 1 of the manuscript's canonical
partitions), the cash-aware Lemma 4 is false. -/
theorem not_lemmaFourCashNoPrice : ¬ LemmaFourCashNoPrice (Fin 6) := by
  intro h
  have hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p := by
    intro g
    rw [MMS_three, vbar_eq]
    have : w g ≤ 37 := by
      simp only [w]
      have : wn g ≤ 37 := by fin_cases g <;> decide
      exact_mod_cast this
    linarith
  have hKval : vbarSum w p K + 0 ≤ (3 / 4 : ℝ) * MMS 3 w p := by
    rw [MMS_three]
    have : vbarSum w p K = 37 := by
      simp only [vbarSum, K, Finset.sum_singleton, vbar_eq, w]
      norm_num [wn]
    rw [this]
    norm_num
  have hS : (∑ g ∈ S, p g) = 0 := by simp [S, p]
  have hmain := h w p hw hp hnobig K S 0 K_disjoint_S (le_refl 0) (by rw [hS])
    (by decide) (Or.inr rfl) hKval
  rw [MMS_three, hS] at hmain
  have hR : (Finset.univ \ (K ∪ S) : Finset (Fin 6)) = R := rfl
  rw [hR, sub_zero] at hmain
  have hle := MMS_two_le
  norm_num at hmain
  linarith

end FairSelling
