import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.ThreeAgents
import RequestProject.EquiMMS
import RequestProject.TwoThirdsLoss

/-!
# The value still at the disposal of an active agent

The proof of Lemma 9 in the manuscript rests on the assertion that, at the start of a round of the
main loop, "the total value that we have at our disposal is at least `n′ · MMSᵢ`", where `n′` is
the number of still-active agents.  The manuscript leaves the quantity informal; this file makes
it precise and proves the assertion.

The formal quantity is `EquiMMS.budget`: for an equi-valued MMS partition of the agent, the
`v̄`-value of the goods of its parts that are still available, plus the price of the goods it
intends to sell that are still available, plus the banked money.  Before anything is allocated
this is exactly `n · MMSᵢ` (`EquiMMS.budget_univ`), and the main result here,

* `losses_budget` — in any state satisfying the accounting invariant, every active agent `i` has
  an equi-valued MMS partition whose budget is at least `|T| · MMSᵢ`,

says that each of the `n − |T|` loss events consumed at most `MMSᵢ` of it.  The per-event bound is
`eventCost_le`, and it is exactly the manuscript's case analysis over the four loss types — the
place where the constant `ρ = 2/3` is used, through `3ρ − 1 = ρ · (3/2) − ... = 1`, i.e.
`3t − μ = μ`.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Splitting a sum along the state decomposition -/

/-- If the goods are covered by the available set `R` together with the pairwise disjoint sets
`Gb b` of goods consumed by the past events, then any sum over a set `A` splits accordingly. -/
lemma sum_split_cover {f : G → ℝ} (A R : Finset G) (Gb : Fin n → Finset G)
    (hcov : (Finset.univ : Finset G) = R ∪ Finset.univ.biUnion Gb)
    (hRG : ∀ b, Disjoint R (Gb b)) (hGG : ∀ b b', b ≠ b' → Disjoint (Gb b) (Gb b')) :
    ∑ g ∈ A, f g = (∑ g ∈ A ∩ R, f g) + ∑ b, ∑ g ∈ A ∩ Gb b, f g := by
  classical
  have h1 : A = (A ∩ R) ∪ (A ∩ Finset.univ.biUnion Gb) := by
    rw [← Finset.inter_union_distrib_left, ← hcov, Finset.inter_univ]
  have hdisj : Disjoint (A ∩ R) (A ∩ Finset.univ.biUnion Gb) := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx').2
    exact Finset.disjoint_left.mp (hRG b) (Finset.mem_inter.mp hx).2 hb
  have h2 : A ∩ Finset.univ.biUnion Gb = Finset.univ.biUnion (fun b => A ∩ Gb b) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxA, b, hb⟩; exact ⟨b, hxA, hb⟩
    · rintro ⟨b, hxA, hb⟩; exact ⟨hxA, b, hb⟩
  conv_lhs => rw [h1]
  rw [Finset.sum_union hdisj, h2, Finset.sum_biUnion]
  intro b _ b' _ hbb
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (hGG b b' hbb))

/-! ### The cost of one loss event -/

/-- The amount of budget that a single loss event `(Ea, Fa, c)` consumes: the value of the goods
of the parts it takes away, plus the price of the goods of the sell set it takes away, minus the
proceeds of the goods it sold, plus the money it handed out. -/
noncomputable def eventCost {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k)
    (Ea Fa : Finset G) (c : ℝ) : ℝ :=
  (∑ j, vbarSum w p (E.part j ∩ (Ea ∪ Fa))) + (∑ g ∈ E.sell ∩ (Ea ∪ Fa), p g)
    - (∑ g ∈ Fa, p g) + c

section Cost

variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}

omit [Fintype G] in
/-- The contribution of a single good to the cost of an event that takes it away without selling
it is at most its `v̄`-value, and it is `0` unless the good belongs to a part or to the sell
set. -/
private lemma good_cost_kept (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (g : G) :
    (∑ j, if g ∈ E.part j then vbar w p g else 0) + (if g ∈ E.sell then p g else 0)
      ≤ vbar w p g := by
  classical
  by_cases hs : g ∈ E.sell
  · have hnp : ∀ j, g ∉ E.part j := fun j hj => Finset.disjoint_left.mp (E.sell_disj j) hs hj
    simp only [if_neg (hnp _), Finset.sum_const_zero, zero_add, if_pos hs]
    exact le_max_left _ _
  · simp only [if_neg hs, add_zero]
    by_cases hj : ∃ j, g ∈ E.part j
    · obtain ⟨j₀, hj₀⟩ := hj
      have hzero : ∀ j ∈ Finset.univ, j ≠ j₀ → (if g ∈ E.part j then vbar w p g else 0) = 0 := by
        intro j _ hne
        rw [if_neg (fun h => Finset.disjoint_left.mp (E.part_disj j j₀ hne) h hj₀)]
      rw [Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h), if_pos hj₀]
    · push_neg at hj
      simp only [hj, if_false, Finset.sum_const_zero]
      exact le_trans (hp g) (le_max_left _ _)

omit [Fintype G] [DecidableEq G] in
/-- Every good of a part is worth at most `μ`. -/
lemma vbar_le_of_mem_part (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    {j : Fin k} {g : G} (hg : g ∈ E.part j) : vbar w p g ≤ μ := by
  classical
  have h1 : vbar w p g ≤ vbarSum w p (E.part j) := by
    refine Finset.single_le_sum (f := fun x => vbar w p x) (fun x _ => ?_) hg
    exact le_trans (hp x) (le_max_left _ _)
  have h2 := E.value j
  have h3 := E.cash_nonneg j
  simp only [vbarSum] at h1 h2
  linarith

omit [Fintype G] in
/-- The `v̄`-value that the parts and the sell set of an equi-valued partition see inside a set
`A` of goods is at most the total `v̄`-value of `A`. -/
lemma event_goods_le (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g) (A : Finset G) :
    (∑ j, vbarSum w p (E.part j ∩ A)) + (∑ g ∈ E.sell ∩ A, p g) ≤ ∑ g ∈ A, vbar w p g := by
  classical
  have h1 : (∑ j, vbarSum w p (E.part j ∩ A))
      = ∑ j, ∑ g ∈ A, (if g ∈ E.part j then vbar w p g else 0) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [vbarSum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x; simp [Finset.mem_inter, and_comm]
  have h2 : (∑ g ∈ E.sell ∩ A, p g) = ∑ g ∈ A, (if g ∈ E.sell then p g else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x; simp [Finset.mem_inter, and_comm]
  rw [h1, h2]
  calc (∑ j, ∑ g ∈ A, (if g ∈ E.part j then vbar w p g else 0))
        + ∑ g ∈ A, (if g ∈ E.sell then p g else 0)
      = ∑ g ∈ A, ((∑ j, if g ∈ E.part j then vbar w p g else 0)
          + (if g ∈ E.sell then p g else 0)) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    _ ≤ ∑ g ∈ A, vbar w p g :=
        Finset.sum_le_sum (fun g _ => good_cost_kept E hp g)

omit [Fintype G] in
/-- The cost of an event is bounded by the `v̄`-value of the goods it hands out, plus the money it
hands out, plus the amount by which the goods it sells are worth more to the agent than their
price. -/
lemma eventCost_le_aux (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (Ea Fa : Finset G) (hEF : Disjoint Ea Fa) (c : ℝ) :
    eventCost E Ea Fa c ≤ vbarSum w p Ea + (∑ g ∈ Fa, (vbar w p g - p g)) + c := by
  classical
  have hsplit := event_goods_le E hp
  -- split the event's goods into those handed out and those sold
  have hunion : ∀ (F : G → ℝ), ∑ g ∈ Ea ∪ Fa, F g = (∑ g ∈ Ea, F g) + ∑ g ∈ Fa, F g :=
    fun F => Finset.sum_union hEF
  have hE1 : ∀ j, vbarSum w p (E.part j ∩ (Ea ∪ Fa))
      = vbarSum w p (E.part j ∩ Ea) + vbarSum w p (E.part j ∩ Fa) := by
    intro j
    rw [Finset.inter_union_distrib_left, vbarSum, vbarSum, vbarSum]
    exact Finset.sum_union (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF))
  have hS1 : (∑ g ∈ E.sell ∩ (Ea ∪ Fa), p g)
      = (∑ g ∈ E.sell ∩ Ea, p g) + ∑ g ∈ E.sell ∩ Fa, p g := by
    rw [Finset.inter_union_distrib_left]
    exact Finset.sum_union (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF))
  have hEa := hsplit Ea
  have hFa := hsplit Fa
  simp only [eventCost, hS1, Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hE1 j)]
  have hFsum : ∑ g ∈ Fa, (vbar w p g - p g) = (∑ g ∈ Fa, vbar w p g) - ∑ g ∈ Fa, p g := by
    rw [Finset.sum_sub_distrib]
  rw [hFsum]
  simp only [vbarSum] at hEa hFa ⊢
  linarith

omit [Fintype G] in
/-- **The cost of a loss event is at most `μ`.**  This is the manuscript's case analysis over the
four loss types of Definition 7, and it is where the value `ρ = 2/3` is used: for a loss of type
`ℓ₃` or `ℓ₄` the bound comes out as `3t − μ`, which equals `μ` exactly when `t = (2/3)·μ`. -/
theorem eventCost_le (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (hμ : 0 ≤ μ) {t : ℝ} (ht : t = (2 / 3) * μ)
    {Ea Fa : Finset G} (hEF : Disjoint Ea Fa) {c : ℝ}
    (hloss : LossOK w p E.sell μ t Ea Fa c) :
    eventCost E Ea Fa c ≤ μ := by
  classical
  have haux := eventCost_le_aux E hp Ea Fa hEF c
  have hvbar0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  -- a good of the sell set contributes nothing to the sold-goods correction
  have hsell_zero : ∀ g ∈ E.sell, vbar w p g - p g = 0 := by
    intro g hg
    simp only [vbar, max_eq_left (E.sell_price g hg), sub_self]
  rcases hloss with h1 | h2 | h3 | h4
  · -- `ℓ₁`
    obtain ⟨e, heS, hcase⟩ := h1
    rcases hcase with ⟨hEa, hFa, hc⟩ | ⟨hEa, hFa, hc⟩
    · -- the good is handed over
      subst hEa; subst hFa; subst hc
      have : vbarSum w p {e} + (∑ g ∈ (∅ : Finset G), (vbar w p g - p g)) + 0 = vbar w p e := by
        simp [vbarSum]
      rw [this] at haux
      by_cases hmem : ∃ j, e ∈ E.part j
      · obtain ⟨j, hj⟩ := hmem
        exact haux.trans (vbar_le_of_mem_part E hp hj)
      · push_neg at hmem
        -- the good belongs to no part and is not sold: it costs nothing
        have hzero : eventCost E {e} ∅ 0 = 0 := by
          simp only [eventCost, Finset.union_empty, Finset.sum_empty, add_zero, sub_zero]
          have hp1 : ∀ j, E.part j ∩ ({e} : Finset G) = ∅ :=
            fun j => Finset.inter_singleton_of_notMem (hmem j)
          have hp2 : E.sell ∩ ({e} : Finset G) = ∅ :=
            Finset.inter_singleton_of_notMem heS
          simp [hp1, hp2, vbarSum]
        rw [hzero]
        exact hμ
    · -- the good is sold
      subst hEa; subst hFa
      have hrw : vbarSum w p (∅ : Finset G) + (∑ g ∈ ({e} : Finset G), (vbar w p g - p g)) + c
          = vbar w p e - p e + c := by simp [vbarSum]
      rw [hrw] at haux
      by_cases hmem : ∃ j, e ∈ E.part j
      · obtain ⟨j, hj⟩ := hmem
        have := vbar_le_of_mem_part E hp hj
        linarith
      · push_neg at hmem
        have hzero : eventCost E ∅ {e} c = c - p e := by
          simp only [eventCost, Finset.empty_union, Finset.sum_singleton]
          have hp1 : ∀ j, E.part j ∩ ({e} : Finset G) = ∅ :=
            fun j => Finset.inter_singleton_of_notMem (hmem j)
          have hp2 : E.sell ∩ ({e} : Finset G) = ∅ :=
            Finset.inter_singleton_of_notMem heS
          simp [hp1, hp2, vbarSum]
          ring
        rw [hzero]
        linarith
  · -- `ℓ₂`
    obtain ⟨hval, hF⟩ := h2
    have hFzero : ∑ g ∈ Fa, (vbar w p g - p g) ≤ 0 := by
      refine Finset.sum_nonpos (fun g hg => ?_)
      rcases hF g hg with h | h
      · exact le_of_eq (by simp only [vbar, max_eq_left h, sub_self])
      · exact le_of_eq (hsell_zero g h)
    have : t ≤ μ := by rw [ht]; linarith
    linarith
  · -- `ℓ₃`
    obtain ⟨⟨e, hEa, _, _⟩, ⟨f, hFa, _, hvf, _, hpf⟩, hc0, hbundle⟩ := h3
    subst hFa
    have hFsum : ∑ g ∈ ({f} : Finset G), (vbar w p g - p g) = vbar w p f - p f := by simp
    rw [hFsum] at haux
    have : vbar w p f - p f ≤ t - (μ - t) := by linarith
    linarith
  · -- `ℓ₄`
    obtain ⟨⟨e, hEa, _, _⟩, ⟨f, hFa, _, hvf, _, hpf⟩, hc0, hbundle⟩ := h4
    subst hFa
    have hFsum : ∑ g ∈ ({f} : Finset G), (vbar w p g - p g) = vbar w p f - p f := by simp
    rw [hFsum] at haux
    have : vbar w p f - p f ≤ t - (μ - t) := by linarith
    linarith

omit [Fintype G] in
/-- If the good that an event sells belongs to no part and is not one the agent intended to sell,
then that good only *lowers* the cost of the event, by its price. -/
lemma eventCost_sold_free (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g) (A : Finset G) (f : G)
    (hfp : ∀ j, f ∉ E.part j) (hfs : f ∉ E.sell) (c : ℝ) :
    eventCost E A {f} c ≤ vbarSum w p A - p f + c := by
  classical
  have h1 : ∀ j, E.part j ∩ (A ∪ {f}) = E.part j ∩ A := by
    intro j
    rw [Finset.inter_union_distrib_left, Finset.inter_singleton_of_notMem (hfp j),
      Finset.union_empty]
  have h2 : E.sell ∩ (A ∪ {f}) = E.sell ∩ A := by
    rw [Finset.inter_union_distrib_left, Finset.inter_singleton_of_notMem hfs,
      Finset.union_empty]
  have h3 := event_goods_le E hp A
  simp only [eventCost, h2, Finset.sum_singleton,
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => congrArg (vbarSum w p) (h1 j))]
  simp only [vbarSum] at h3 ⊢
  linarith

omit [Fintype G] in
/-- **Every loss event is either cheap or charged to a good of a part.**  This refines
`eventCost_le`: an event either costs at most the threshold `t = (2/3)·μ`, or it can be charged
to one of the goods it takes away that belongs to a part of the equi-valued partition, at a cost
of at most that good's `v̄`-value plus `μ/3`. -/
theorem eventCost_witness (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (hμ : 0 ≤ μ) {t : ℝ} (ht : t = (2 / 3) * μ)
    {Ea Fa : Finset G} (hEF : Disjoint Ea Fa) {c : ℝ}
    (hloss : LossOK w p E.sell μ t Ea Fa c) :
    eventCost E Ea Fa c ≤ t ∨
      ∃ x ∈ Ea ∪ Fa, (∃ j, x ∈ E.part j) ∧ eventCost E Ea Fa c ≤ vbar w p x + μ / 3 := by
  classical
  have haux := eventCost_le_aux E hp Ea Fa hEF c
  have hvbar0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hsell_zero : ∀ g ∈ E.sell, vbar w p g - p g = 0 := by
    intro g hg
    simp only [vbar, max_eq_left (E.sell_price g hg), sub_self]
  rcases hloss with h1 | h2 | h3 | h4
  · -- `ℓ₁`
    obtain ⟨e, heS, hcase⟩ := h1
    rcases hcase with ⟨hEa, hFa, hc⟩ | ⟨hEa, hFa, hc⟩
    · subst hEa; subst hFa; subst hc
      have hcost : eventCost E {e} ∅ 0 ≤ vbar w p e := by
        have hrw : vbarSum w p {e} + (∑ g ∈ (∅ : Finset G), (vbar w p g - p g)) + 0
            = vbar w p e := by simp [vbarSum]
        rw [hrw] at haux; exact haux
      by_cases hmem : ∃ j, e ∈ E.part j
      · exact Or.inr ⟨e, by simp, hmem, by linarith⟩
      · push_neg at hmem
        have hzero : eventCost E {e} ∅ 0 = 0 := by
          simp only [eventCost, Finset.union_empty, Finset.sum_empty, add_zero, sub_zero]
          have hp1 : ∀ j, E.part j ∩ ({e} : Finset G) = ∅ :=
            fun j => Finset.inter_singleton_of_notMem (hmem j)
          have hp2 : E.sell ∩ ({e} : Finset G) = ∅ :=
            Finset.inter_singleton_of_notMem heS
          simp [hp1, hp2, vbarSum]
        exact Or.inl (by rw [hzero]; exact ht0)
    · subst hEa; subst hFa
      have hcost : eventCost E ∅ {e} c ≤ vbar w p e := by
        have hrw : vbarSum w p (∅ : Finset G) + (∑ g ∈ ({e} : Finset G), (vbar w p g - p g)) + c
            = vbar w p e - p e + c := by simp [vbarSum]
        rw [hrw] at haux
        linarith
      by_cases hmem : ∃ j, e ∈ E.part j
      · exact Or.inr ⟨e, by simp, hmem, by linarith⟩
      · push_neg at hmem
        have hfree := eventCost_sold_free E hp ∅ e hmem heS c
        simp only [vbarSum, Finset.sum_empty] at hfree
        exact Or.inl (by linarith)
  · -- `ℓ₂`
    obtain ⟨hval, hF⟩ := h2
    have hFzero : ∑ g ∈ Fa, (vbar w p g - p g) ≤ 0 := by
      refine Finset.sum_nonpos (fun g hg => ?_)
      rcases hF g hg with h | h
      · exact le_of_eq (by simp only [vbar, max_eq_left h, sub_self])
      · exact le_of_eq (hsell_zero g h)
    exact Or.inl (by linarith)
  · -- `ℓ₃`
    obtain ⟨⟨e, hEa, _, _⟩, ⟨f, hFa, hfS, hvf, hcf, hpf⟩, hc0, hbundle⟩ := h3
    subst hFa
    have hFsum : ∑ g ∈ ({f} : Finset G), (vbar w p g - p g) = vbar w p f - p f := by simp
    rw [hFsum] at haux
    by_cases hmem : ∃ j, f ∈ E.part j
    · refine Or.inr ⟨f, by simp, hmem, ?_⟩
      simp only [vbarSum] at haux hbundle
      rw [ht] at hpf hbundle
      linarith
    · push_neg at hmem
      have hfree := eventCost_sold_free E hp Ea f hmem hfS c
      simp only [vbarSum] at hfree hbundle
      exact Or.inl (by linarith [hp f])
  · -- `ℓ₄`
    obtain ⟨⟨e, hEa, _, _⟩, ⟨f, hFa, hfS, hvf, hcf, hpf⟩, hc0, hbundle⟩ := h4
    subst hFa
    have hFsum : ∑ g ∈ ({f} : Finset G), (vbar w p g - p g) = vbar w p f - p f := by simp
    rw [hFsum] at haux
    by_cases hmem : ∃ j, f ∈ E.part j
    · refine Or.inr ⟨f, by simp, hmem, ?_⟩
      simp only [vbarSum] at haux hbundle
      rw [ht] at hpf hbundle
      linarith
    · push_neg at hmem
      have hfree := eventCost_sold_free E hp Ea f hmem hfS c
      simp only [vbarSum] at hfree hbundle
      exact Or.inl (by linarith [hp f])

end Cost

/-! ### The budget of an active agent -/

/-- **The budget in terms of the event costs.**  If the goods that are no longer available are
covered by the pairwise disjoint events, then the budget of an equi-valued partition in the state
`(R, D)` is at least its initial value `n·μ` minus the total cost of the events. -/
lemma budget_ge_of_cover {w p : G → ℝ} {μ : ℝ} (E : EquiMMS w p μ n) (R : Finset G) (D : ℝ)
    (alloc sold : Fin n → Finset G) (paid : Fin n → ℝ)
    (hdisj2 : ∀ b b', b ≠ b' → Disjoint (alloc b ∪ sold b) (alloc b' ∪ sold b'))
    (hdisjR : ∀ b, Disjoint R (alloc b ∪ sold b))
    (hcover : (Finset.univ : Finset G) = R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b))
    (hmoney : (∑ b, ∑ g ∈ sold b, p g) - ∑ b, paid b ≤ D) :
    (n : ℝ) * μ - ∑ b, eventCost E (alloc b) (sold b) (paid b) ≤ E.budget R D := by
  classical
  set Gb : Fin n → Finset G := fun b => alloc b ∪ sold b with hGb
  -- split the budget along the state decomposition
  have hpart : ∀ j, vbarSum w p (E.part j)
      = vbarSum w p (E.part j ∩ R) + ∑ b, vbarSum w p (E.part j ∩ Gb b) := by
    intro j
    simpa [vbarSum] using
      sum_split_cover (E.part j) R Gb hcover hdisjR hdisj2 (f := fun g => vbar w p g)
  have hsell : (∑ g ∈ E.sell, p g)
      = (∑ g ∈ E.sell ∩ R, p g) + ∑ b, ∑ g ∈ E.sell ∩ Gb b, p g :=
    sum_split_cover E.sell R Gb hcover hdisjR hdisj2 (f := p)
  -- the budget before anything was allocated
  have htotal : (∑ j, vbarSum w p (E.part j)) + (∑ g ∈ E.sell, p g)
      = (n : ℝ) * μ := by
    have := E.budget_univ
    simpa [EquiMMS.budget] using this
  -- the budget now, in terms of the event costs
  have hcost : ∑ b, eventCost E (alloc b) (sold b) (paid b)
      = (∑ b, ((∑ j, vbarSum w p (E.part j ∩ Gb b)) + ∑ g ∈ E.sell ∩ Gb b, p g))
        - (∑ b, ∑ g ∈ sold b, p g) + ∑ b, paid b := by
    simp only [eventCost, hGb]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hsum1 : ∑ j, vbarSum w p (E.part j)
      = (∑ j, vbarSum w p (E.part j ∩ R))
        + ∑ b, ∑ j, vbarSum w p (E.part j ∩ Gb b) := by
    rw [Finset.sum_congr rfl (fun j _ => hpart j), Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hcost, EquiMMS.budget]
  rw [hsum1, hsell] at htotal
  have hsplitsum : ∑ b, ((∑ j, vbarSum w p (E.part j ∩ Gb b)) + ∑ g ∈ E.sell ∩ Gb b, p g)
      = (∑ b, ∑ j, vbarSum w p (E.part j ∩ Gb b)) + ∑ b, ∑ g ∈ E.sell ∩ Gb b, p g :=
    Finset.sum_add_distrib
  rw [hsplitsum]
  linarith [hmoney]

/-- **The value still at the disposal of an active agent.**  In any state satisfying the
accounting invariant, every active agent `i` has an equi-valued MMS partition whose budget in that
state is at least `|T| · MMSᵢ`, where `T` is the set of still-active agents.

This is the manuscript's "the total value that we have at our disposal is at least `n′ · MMSᵢ`",
and it is the interface between the loss accounting (Proposition 5) and Lemma 9. -/
theorem losses_budget (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (hL : Losses v p T R D) {i : Fin n} (hi : i ∈ T) :
    ∃ E : EquiMMS (v i) p (MMS n (v i) p) n,
      ((T.card : ℝ)) * MMS n (v i) p ≤ E.budget R D := by
  classical
  obtain ⟨alloc, sold, paid, hempty, hdisj1, hdisj2, hdisjR, hcover, hpaid0, hmoney, htypes⟩ := hL
  obtain ⟨E, hE⟩ := htypes i hi
  refine ⟨E, ?_⟩
  have hμ0 : 0 ≤ MMS n (v i) p := MMS_nonneg hn (v i) p (hv i) hp
  have hbudget := budget_ge_of_cover E R D alloc sold paid hdisj2 hdisjR hcover hmoney
  -- every event costs at most `μ`, and the active agents carry no event
  have hcost_le : ∀ b, eventCost E (alloc b) (sold b) (paid b)
      ≤ if b ∈ T then 0 else MMS n (v i) p := by
    intro b
    by_cases hb : b ∈ T
    · obtain ⟨h1, h2, h3⟩ := hempty b hb
      rw [if_pos hb, h1, h2, h3]
      simp [eventCost, vbarSum]
    · rw [if_neg hb]
      exact eventCost_le E hp hμ0 (by rw [thr, rho]) (hdisj1 b) (hE b hb)
  have hsum_le : ∑ b, eventCost E (alloc b) (sold b) (paid b)
      ≤ ((n : ℝ) - T.card) * MMS n (v i) p := by
    refine le_trans (Finset.sum_le_sum (fun b _ => hcost_le b)) ?_
    have hkey : ∀ b : Fin n, (if b ∈ T then (0:ℝ) else MMS n (v i) p)
        = if b ∈ Finset.univ \ T then MMS n (v i) p else 0 := by
      intro b; by_cases hb : b ∈ T <;> simp [hb]
    have hcard : (((Finset.univ : Finset (Fin n)) \ T).card : ℝ) = (n : ℝ) - T.card := by
      have hle : T.card ≤ n := by simpa using Finset.card_le_univ T
      rw [Finset.card_univ_diff, Fintype.card_fin, Nat.cast_sub hle]
    calc ∑ b, (if b ∈ T then (0:ℝ) else MMS n (v i) p)
        = ∑ b, (if b ∈ Finset.univ \ T then MMS n (v i) p else 0) :=
          Finset.sum_congr rfl (fun b _ => hkey b)
      _ = ∑ _b ∈ (Finset.univ : Finset (Fin n)) \ T, MMS n (v i) p := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (((Finset.univ : Finset (Fin n)) \ T).card : ℝ) * MMS n (v i) p := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) - T.card) * MMS n (v i) p := le_of_eq (by rw [hcard])
  have hexp : ((n : ℝ) - T.card) * MMS n (v i) p
      = (n : ℝ) * MMS n (v i) p - (T.card : ℝ) * MMS n (v i) p := by ring
  rw [hexp] at hsum_le
  linarith

end FairSelling
