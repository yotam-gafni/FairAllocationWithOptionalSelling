import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.ThreeAgents

/-!
# Equi-valued MMS partitions and the value readjustment (Definition 5 and Lemma 6)

Following Definition 5 of the manuscript, an MMS partition is *equi-valued* when all of its
parts are worth exactly the maximin share to the agent.  Such a partition need not exist for the
original valuations — with two agents and three goods worth `10, 6, 6` and no market, the maximin
share is `10` and no partition has both parts worth exactly `10` — and **Lemma 6** (*value
readjustment*) asserts that one may lower the valuations, without changing the maximin shares, so
that it does.

This file proves Lemma 6 (`exists_readjustment`).  The two ingredients are:

* `MMS_liquid_le` — in an MMS partition, the price of the goods of a part plus the money of that
  part never exceeds the maximin share.  (Otherwise the whole part could be sold and the excess
  money spread over the other parts, raising the worst part above the maximin share.)  This is the
  step that makes the readjustment possible at all: lowering `v` can lower `v̄ g = max (p g) (v g)`
  only down to `p g`.
* `exists_value_reduction` — given a target `T` between `∑_{g ∈ A} p g` and `∑_{g ∈ A} v̄ g`, the
  valuation can be lowered on `A` so that the `v̄`-value of `A` is exactly `T`.

The readjusted valuation also lowers the value of every good the agent intends to sell down to its
price (`EquiMMS.sell_price`).  This is needed by the analysis of the `2/3` algorithm — the second
stage of its preliminary phase classifies the hand-out of such a good as a loss of type `ℓ₂`,
which requires its `v̄`-value to be its price — and it comes for free here.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Equi-valued MMS partitions -/

/-- An **equi-valued MMS partition** of agent with valuation `w`: `k` pairwise disjoint parts of
goods, a set `sell` of goods that are sold with their proceeds split over the parts, and each part
worth exactly `μ`.  The parts need not use all the goods. -/
structure EquiMMS (w p : G → ℝ) (μ : ℝ) (k : ℕ) where
  /-- The goods of each part. -/
  part : Fin k → Finset G
  /-- The set `Sᵢ` of goods the agent intends to sell. -/
  sell : Finset G
  /-- The share of the proceeds that goes to each part. -/
  cash : Fin k → ℝ
  part_disj : ∀ j j', j ≠ j' → Disjoint (part j) (part j')
  sell_disj : ∀ j, Disjoint sell (part j)
  cash_nonneg : ∀ j, 0 ≤ cash j
  cash_sum : ∑ j, cash j = ∑ g ∈ sell, p g
  value : ∀ j, vbarSum w p (part j) + cash j = μ
  /-- A good the agent intends to sell is not worth more to it than its price: the readjustment
  of Lemma 6 lowers the value of such a good to its price, since the partition only uses the
  price. -/
  sell_price : ∀ e ∈ sell, w e ≤ p e

/-- The **budget** that an equi-valued MMS partition still sees in the state `(R, D)`: the
`v̄`-value of the goods of its parts that are still available, plus the price of the goods it
intends to sell that are still available, plus the banked money.  This is the manuscript's
informal "total value that we have at our disposal". -/
noncomputable def EquiMMS.budget {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k)
    (R : Finset G) (D : ℝ) : ℝ :=
  (∑ j, vbarSum w p (E.part j ∩ R)) + (∑ g ∈ E.sell ∩ R, p g) + D

/-- Before anything has been allocated, the budget is exactly `k · μ`. -/
lemma EquiMMS.budget_univ {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k) :
    E.budget Finset.univ 0 = k * μ := by
  simp only [EquiMMS.budget, Finset.inter_univ, add_zero]
  rw [← E.cash_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j _ => E.value j)]
  simp [mul_comm]

/-! ### Lowering a valuation to hit a prescribed `v̄`-value -/

omit [Fintype G] in
/-- **Lowering a valuation on a set to a prescribed total.**  If the target `T` lies between the
total price of `A` and its total `v̄`-value, then `v` can be lowered — only on `A`, and staying
non-negative — so that the `v̄`-value of `A` becomes exactly `T`. -/
theorem exists_value_reduction (p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (v : G → ℝ) (hv : ∀ g, 0 ≤ v g) :
    ∀ (A : Finset G) (T : ℝ), (∑ g ∈ A, p g) ≤ T → T ≤ ∑ g ∈ A, max (p g) (v g) →
    ∃ w : G → ℝ, (∀ g, 0 ≤ w g) ∧ (∀ g, w g ≤ v g) ∧ (∀ g ∉ A, w g = v g) ∧
      ∑ g ∈ A, max (p g) (w g) = T := by
  classical
  intro A
  induction A using Finset.induction with
  | empty =>
    intro T h1 h2
    simp only [Finset.sum_empty] at h1 h2
    exact ⟨v, hv, fun g => le_refl _, fun g _ => rfl, by simp; linarith⟩
  | @insert a s ha IH =>
    intro T h1 h2
    rw [Finset.sum_insert ha] at h1 h2
    by_cases hcase : (∑ g ∈ s, p g) + max (p a) (v a) ≤ T
    · obtain ⟨w, hw0, hwv, hwout, hwsum⟩ := IH (T - max (p a) (v a)) (by linarith) (by linarith)
      refine ⟨w, hw0, hwv, fun g hg => hwout g (fun h => hg (Finset.mem_insert_of_mem h)), ?_⟩
      rw [Finset.sum_insert ha, hwout a ha, hwsum]
      ring
    · push_neg at hcase
      obtain ⟨w, hw0, hwv, hwout, hwsum⟩ := IH (∑ g ∈ s, p g) (le_refl _)
        (Finset.sum_le_sum (fun g _ => le_max_left _ _))
      set c : ℝ := T - ∑ g ∈ s, p g with hc
      have hca : p a ≤ c := by simp only [hc]; linarith
      have hclt : c < max (p a) (v a) := by simp only [hc]; linarith
      have hcv : c ≤ v a := by
        rcases max_cases (p a) (v a) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hclt <;> linarith
      refine ⟨Function.update w a c, ?_, ?_, ?_, ?_⟩
      · intro g
        by_cases hg : g = a
        · subst hg; simpa using le_trans (hp g) hca
        · simpa [Function.update_of_ne hg] using hw0 g
      · intro g
        by_cases hg : g = a
        · subst hg; simpa using hcv
        · simpa [Function.update_of_ne hg] using hwv g
      · intro g hg
        have hga : g ≠ a := by rintro rfl; exact hg (Finset.mem_insert_self g s)
        rw [Function.update_of_ne hga]
        exact hwout g (fun h => hg (Finset.mem_insert_of_mem h))
      · rw [Finset.sum_insert ha]
        have hupd : ∑ g ∈ s, max (p g) (Function.update w a c g)
            = ∑ g ∈ s, max (p g) (w g) :=
          Finset.sum_congr rfl (fun g hg => by
            rw [Function.update_of_ne (by rintro rfl; exact ha hg)])
        rw [hupd, hwsum]
        simp only [Function.update_self]
        rw [max_eq_right hca, hc]
        ring

/-! ### The liquid value of a part of an MMS partition -/

/-- **The liquid value of a part is at most the maximin share.**  In an outcome all of whose parts
are worth at least the maximin share, the total *price* of the goods of a part, plus the money of
that part, never exceeds the maximin share.

Indeed, otherwise all the goods of that part could be sold, leaving that part with strictly more
than `MMS` in pure money, of which a small amount could be handed to each of the other parts;
every part would then be worth strictly more than `MMS`. -/
theorem MMS_liquid_le (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {o : Outcome G n} (hval : o.Valid p) (hge : ∀ j, MMS n v p ≤ util v o j) (j : Fin n) :
    (∑ g ∈ o.kept j, p g) + o.money j ≤ MMS n v p := by
  classical
  set μ : ℝ := MMS n v p with hμ
  set P : ℝ := (∑ g ∈ o.kept j, p g) + o.money j with hP
  by_contra hcon
  push_neg at hcon
  have hμ0 : 0 ≤ μ := MMS_nonneg hn v p hv hp
  set eps : ℝ := (P - μ) / (2 * n) with heps
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have heps0 : 0 < eps := by
    rw [heps]
    apply div_pos (by linarith) (by linarith)
  -- the modified outcome: everything of part `j` is sold
  set o' : Outcome G n :=
    { sold := o.sold ∪ o.kept j
      kept := fun l => if l = j then ∅ else o.kept l
      money := fun l => if l = j then P - (n - 1 : ℝ) * eps else o.money l + eps } with ho'
  have hdisj_sj : Disjoint o.sold (o.kept j) := hval.1 j
  have hmoneyj : 0 ≤ P - (n - 1 : ℝ) * eps := by
    have h1 : (n - 1 : ℝ) * eps ≤ (n : ℝ) * eps := by nlinarith
    have h2 : (n : ℝ) * eps = (P - μ) / 2 := by
      rw [heps]; field_simp
    linarith
  have hsumsold : ∑ g ∈ o'.sold, p g = (∑ g ∈ o.sold, p g) + ∑ g ∈ o.kept j, p g := by
    simp only [ho']
    exact Finset.sum_union hdisj_sj
  have hsummoney : ∑ l, o'.money l = P + ∑ l ∈ Finset.univ.erase j, o.money l := by
    have hj : o'.money j = P - ((n:ℝ) - 1) * eps := by simp [ho']
    have hne : ∀ l ∈ Finset.univ.erase j, o'.money l = o.money l + eps := by
      intro l hl
      simp [ho', (Finset.mem_erase.mp hl).1]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, Finset.sum_congr rfl hne,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.erase j).card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub hn, Nat.cast_one]
    rw [hcard]
    ring
  have hvalid' : o'.Valid p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l
      by_cases hl : l = j
      · simp [ho', hl]
      · simp only [ho', if_neg hl]
        rw [Finset.disjoint_union_left]
        exact ⟨hval.1 l, hval.2.1 j l (fun h => hl h.symm)⟩
    · intro l l' hll
      simp only [ho']
      by_cases hl : l = j
      · simp [hl]
      · by_cases hl' : l' = j
        · simp [hl']
        · simp only [if_neg hl, if_neg hl']
          exact hval.2.1 l l' hll
    · intro l
      by_cases hl : l = j
      · simp only [ho', if_pos hl]; exact hmoneyj
      · simp only [ho', if_neg hl]
        have := hval.2.2.1 l
        linarith
    · rw [hsummoney, hsumsold, hP]
      have hms : ∑ l, o.money l ≤ ∑ g ∈ o.sold, p g := hval.2.2.2
      have hsplit : ∑ l, o.money l = o.money j + ∑ l ∈ Finset.univ.erase j, o.money l :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      linarith
  -- every part of the modified outcome is worth more than `μ`
  have hbetter : ∀ l, μ + eps ≤ util v o' l := by
    intro l
    by_cases hl : l = j
    · subst hl
      have hgoal : util v o' l = P - ((n:ℝ) - 1) * eps := by simp [util, ho']
      rw [hgoal]
      have h1 : (n - 1 : ℝ) * eps ≤ (n : ℝ) * eps := by nlinarith
      have h2 : (n : ℝ) * eps = (P - μ) / 2 := by rw [heps]; field_simp
      have h3 : eps ≤ (P - μ) / 2 := by
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        nlinarith
      linarith
    · simp only [util, ho', if_neg hl]
      have := hge l
      simp only [util] at this
      linarith
  have hmem : μ + eps ∈ MMSset n v p := ⟨o', hvalid', hbetter⟩
  have hle : μ + eps ≤ MMS n v p := le_csSup (MMSset_bddAbove_of hn v p hv hp) hmem
  rw [← hμ] at hle
  linarith

/-! ### Lemma 6: the value readjustment -/

/-- **Lemma 6 for a single agent.**  Every valuation can be lowered pointwise, without changing
the maximin share, so that the agent has an equi-valued MMS partition. -/
theorem exists_equiMMS (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ w : G → ℝ, (∀ g, 0 ≤ w g) ∧ (∀ g, w g ≤ v g) ∧ MMS n w p = MMS n v p ∧
      Nonempty (EquiMMS w p (MMS n w p) n) := by
  classical
  set μ : ℝ := MMS n v p with hμ
  obtain ⟨o, hovalid, hcover, hoge⟩ := exists_MMS_partition hn v p hv hp
  -- distribute the unspent proceeds, so that the money of the parts is exactly the proceeds
  set slack : ℝ := (∑ g ∈ o.sold, p g) - ∑ l, o.money l with hslack
  have hslack0 : 0 ≤ slack := by rw [hslack]; linarith [hovalid.2.2.2]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set cash : Fin n → ℝ := fun l => o.money l + slack / n with hcash
  have hcash0 : ∀ l, 0 ≤ cash l :=
    fun l => add_nonneg (hovalid.2.2.1 l) (div_nonneg hslack0 (le_of_lt hn'))
  have hcashsum : ∑ l, cash l = ∑ g ∈ o.sold, p g := by
    rw [hcash]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hns : (n : ℝ) * (slack / n) = slack := by field_simp
    rw [hns, hslack]
    ring
  set o2 : Outcome G n := { sold := o.sold, kept := o.kept, money := cash } with ho2
  have ho2valid : o2.Valid p :=
    ⟨hovalid.1, hovalid.2.1, hcash0, le_of_eq hcashsum⟩
  have ho2ge : ∀ l, μ ≤ util v o2 l := by
    intro l
    have h1 := hoge l
    simp only [util, ho2, hcash]
    simp only [util] at h1
    have : 0 ≤ slack / n := div_nonneg hslack0 (le_of_lt hn')
    linarith
  -- the liquid value of every part is at most `μ`
  have hliq : ∀ l, (∑ g ∈ o.kept l, p g) + cash l ≤ μ := by
    intro l
    have := MMS_liquid_le hn v p hv hp ho2valid ho2ge l
    simpa [ho2] using this
  -- and the `v̄`-value of every part is at least `μ`
  have hupper : ∀ l, μ - cash l ≤ ∑ g ∈ o.kept l, max (p g) (v g) := by
    intro l
    have h1 := ho2ge l
    simp only [util, ho2] at h1
    have h2 : ∑ g ∈ o.kept l, v g ≤ ∑ g ∈ o.kept l, max (p g) (v g) :=
      Finset.sum_le_sum (fun g _ => le_max_right _ _)
    linarith
  -- lower the valuation on each part so that the part is worth exactly `μ`
  choose W hW0 hWv hWout hWsum using fun l =>
    exists_value_reduction p hp v hv (o.kept l) (μ - cash l) (by linarith [hliq l]) (hupper l)
  set w : G → ℝ := fun g => if h : ∃ l, g ∈ o.kept l then W h.choose g else min (v g) (p g)
    with hw
  have hkept : ∀ l, ∀ g ∈ o.kept l, w g = W l g := by
    intro l g hg
    have hex : ∃ l, g ∈ o.kept l := ⟨l, hg⟩
    have hcl : hex.choose = l := by
      by_contra hne
      exact Finset.disjoint_left.mp (hovalid.2.1 _ _ hne) hex.choose_spec hg
    simp only [hw, dif_pos hex, hcl]
  have hnotkept : ∀ g, (¬ ∃ l, g ∈ o.kept l) → w g = min (v g) (p g) := by
    intro g hg; simp only [hw, dif_neg hg]
  have hw0 : ∀ g, 0 ≤ w g := by
    intro g
    by_cases hg : ∃ l, g ∈ o.kept l
    · obtain ⟨l, hl⟩ := hg
      rw [hkept l g hl]; exact hW0 l g
    · rw [hnotkept g hg]; exact le_min (hv g) (hp g)
  have hwv : ∀ g, w g ≤ v g := by
    intro g
    by_cases hg : ∃ l, g ∈ o.kept l
    · obtain ⟨l, hl⟩ := hg
      rw [hkept l g hl]; exact hWv l g
    · rw [hnotkept g hg]; exact min_le_left _ _
  have hsoldw : ∀ e ∈ o.sold, w e ≤ p e := by
    intro e he
    have hnot : ¬ ∃ l, e ∈ o.kept l := by
      rintro ⟨l, hl⟩
      exact Finset.disjoint_left.mp (hovalid.1 l) he hl
    rw [hnotkept e hnot]
    exact min_le_right _ _
  have hvalue : ∀ l, vbarSum w p (o.kept l) + cash l = μ := by
    intro l
    have : vbarSum w p (o.kept l) = ∑ g ∈ o.kept l, max (p g) (W l g) := by
      simp only [vbarSum, vbar]
      exact Finset.sum_congr rfl (fun g hg => by rw [hkept l g hg])
    rw [this, hWsum l]
    ring
  -- the maximin share is unchanged
  have hMMSle : MMS n w p ≤ μ := by
    refine csSup_le ⟨0, ?_⟩ ?_
    · exact ⟨{ sold := ∅, kept := fun _ => ∅, money := fun _ => 0 },
        ⟨fun _ => by simp, fun _ _ _ => by simp, fun _ => le_refl 0, by simp⟩,
        fun _ => by simp [util]⟩
    · rintro r ⟨o', ho'valid, ho'ge⟩
      refine le_csSup (MMSset_bddAbove_of hn v p hv hp) ⟨o', ho'valid, fun l => ?_⟩
      refine (ho'ge l).trans ?_
      simp only [util]
      have : ∑ g ∈ o'.kept l, w g ≤ ∑ g ∈ o'.kept l, v g :=
        Finset.sum_le_sum (fun g _ => hwv g)
      linarith
  have hMMSge : μ ≤ MMS n w p := by
    refine le_csSup (MMSset_bddAbove_of hn w p hw0 hp) ?_
    refine ⟨unifiedOutcome (fun _ => w) p o.kept o.sold cash, ?_, fun l => ?_⟩
    · exact unifiedOutcome_valid (fun _ => w) p hp o.kept o.sold cash hovalid.2.1 hovalid.1
        hcash0 (le_of_eq hcashsum)
    · have hu : util w (unifiedOutcome (fun _ => w) p o.kept o.sold cash) l
          = vbarSum w p (o.kept l) + cash l :=
        util_unifiedOutcome (fun _ => w) p o.kept o.sold cash l
      rw [hu, hvalue l]
  have hMMSeq : MMS n w p = μ := le_antisymm hMMSle hMMSge
  refine ⟨w, hw0, hwv, hMMSeq, ⟨o.kept, o.sold, cash, hovalid.2.1, hovalid.1, hcash0,
    hcashsum, ?_, hsoldw⟩⟩
  intro l
  rw [hMMSeq]
  exact hvalue l

/-- **Lemma 6 (value readjustment).**  Every instance can be replaced by one with pointwise
smaller valuations, the same maximin shares, and in which every agent has an equi-valued MMS
partition.  Since the valuations only decrease, an allocation guaranteeing `ρ·MMS` in the
readjusted instance guarantees `ρ·MMS` in the original one. -/
theorem exists_readjustment (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ v' : Fin n → G → ℝ, (∀ i g, 0 ≤ v' i g) ∧ (∀ i g, v' i g ≤ v i g) ∧
      (∀ i, MMS n (v' i) p = MMS n (v i) p) ∧
      ∀ i, Nonempty (EquiMMS (v' i) p (MMS n (v' i) p) n) := by
  classical
  choose w hw0 hwv hwMMS hwE using fun i => exists_equiMMS hn (v i) p (hv i) hp
  exact ⟨w, hw0, hwv, hwMMS, hwE⟩

end FairSelling
