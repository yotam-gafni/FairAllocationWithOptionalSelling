import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.TPSApprox
import RequestProject.TwoThirdsMatching

/-!
# Canonical partitions and one round of the `2/3`-MMS algorithm

This file formalizes the objects manipulated by the main loop of the manuscript's Algorithm 1
(`APX-MMS-2/3`), and proves that **one round of the loop works**: from a canonical partition
proposed by the active agent of highest maximin share, the matching phase serves at least one
agent (the proposing agent, and possibly others), every served agent receives a bundle worth at
least its threshold, and every still-active agent finds every bundle handed out in this round
unacceptable.

## The state of the algorithm

The state is a triple `(T, R, D)`: the set `T` of still-active agents, the set `R` of goods that
are still available, and the amount `D` of banked money (the manuscript's `P′`, the proceeds of
goods sold in earlier rounds that were not handed out).  The goal at each state is
`Servable v p τ T R D` (from `RequestProject.TPSApprox`): the agents of `T` can be served out of
`R` and `D`, each reaching its threshold `τ`.

## Canonical partitions

`Canonical w p μ t k R D` is the manuscript's notion of a *canonical* `k`-partition of the
available resources for an agent with valuation `w`, maximin share `μ` and threshold `t = ρ·μ`:

* the parts are disjoint sets of available goods, together with money taken from the bank `D`
  and money taken from the sale of goods of `sell` (the set `Sᵢ` the agent intends to sell);
* the money of a part that is funded by a sale comes from the sale of a *single* good
  (`src`), and the same sold good may fund several parts;
* every good the agent intends to sell has price at least `(1−ρ)·μ` (condition 1);
* every part is acceptable, i.e. worth at least `t` (condition 2);
* apart from the *special* part (index `0`), every part is either *pure* (no money from a sale)
  or a *singleton* (one good plus money from the sale of one good) (condition 2);
* for a good `e` of a singleton part and a good `f` the agent intends to sell,
  `v̄(e) + p(f) > t` (condition 3).

## Results

* `servable_extend_set` — serving a whole set of agents at once, the many-agent version of
  `servable_extend`.
* `round_outcome` — the matching phase: the existence of the set of agents served in one round
  together with the parts they receive.
* `servable_of_round` — one round of the main loop, reducing `Servable` on the state before the
  round to `Servable` on the state after it.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Serving a set of agents at once -/

omit [Fintype G] in
/-- Serving all the agents of `Kset` with the bundles `bundle k` and the money `cash k`, the
money being raised from the bank `D` and from force-selling the goods `F`, and then serving the
remaining agents out of what is left. -/
lemma servable_extend_set (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (Kset : Finset (Fin n)) (hKT : Kset ⊆ T)
    (bundle : Fin n → Finset G) (F : Finset G) (cash : Fin n → ℝ)
    (hb : ∀ k ∈ Kset, bundle k ⊆ R) (hF : F ⊆ R)
    (hbdisj : ∀ k ∈ Kset, ∀ l ∈ Kset, k ≠ l → Disjoint (bundle k) (bundle l))
    (hbF : ∀ k ∈ Kset, Disjoint F (bundle k))
    (hcash0 : ∀ k ∈ Kset, 0 ≤ cash k)
    (hserve : ∀ k ∈ Kset, τ k ≤ vbarSum (v k) p (bundle k) + cash k)
    (hrec : Servable v p τ (T \ Kset) (R \ (Kset.biUnion bundle ∪ F))
              (D + (∑ g ∈ F, p g) - ∑ k ∈ Kset, cash k)) :
    Servable v p τ T R D := by
  classical
  obtain ⟨A', F', q', hA'R, hF'R, hA'disj, hF'disj, hq'0, hq'sum, hq'serve, hq'out⟩ := hrec
  refine ⟨fun k => if k ∈ Kset then bundle k else A' k, F' ∪ F,
    fun k => if k ∈ Kset then cash k else q' k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ Kset
    · simp only [if_pos hk]; exact hb k hk
    · simp only [if_neg hk]
      exact (hA'R k).trans Finset.sdiff_subset
  · exact Finset.union_subset (hF'R.trans Finset.sdiff_subset) hF
  · intro k l hkl
    by_cases hk : k ∈ Kset <;> by_cases hl : l ∈ Kset
    · simp only [if_pos hk, if_pos hl]; exact hbdisj k hk l hl hkl
    · simp only [if_pos hk, if_neg hl]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      have := hA'R l hx'
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at this
      exact this.2 (Or.inl ⟨k, hk, hx⟩)
    · simp only [if_neg hk, if_pos hl]
      refine Finset.disjoint_right.mpr (fun x hx hx' => ?_)
      have := hA'R k hx'
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at this
      exact this.2 (Or.inl ⟨l, hl, hx⟩)
    · simp only [if_neg hk, if_neg hl]; exact hA'disj k l hkl
  · intro k
    by_cases hk : k ∈ Kset
    · simp only [if_pos hk]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · have := hF'R hx
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at this
        exact this.2 (Or.inl ⟨k, hk, hx'⟩)
      · exact Finset.disjoint_left.mp (hbF k hk) hx hx'
    · simp only [if_neg hk]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (hF'disj k) hx hx'
      · have := hA'R k hx'
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inr hx)
  · intro k
    by_cases hk : k ∈ Kset
    · simp only [if_pos hk]; exact hcash0 k hk
    · simp only [if_neg hk]; exact hq'0 k
  · have hsplit : ∑ k, (if k ∈ Kset then cash k else q' k)
        = (∑ k ∈ Kset, cash k) + ∑ k ∈ Finset.univ \ Kset, q' k := by
      rw [← Finset.sum_sdiff (Finset.subset_univ Kset), add_comm]
      congr 1
      · exact Finset.sum_congr rfl (fun k hk => by simp [hk])
      · exact Finset.sum_congr rfl (fun k hk => by simp [(Finset.mem_sdiff.mp hk).2])
    have hq'zero : ∀ k ∈ Kset, q' k = 0 := by
      intro k hk
      exact (hq'out k (by simp [Finset.mem_sdiff, hk])).2
    have hq'univ : ∑ k ∈ Finset.univ \ Kset, q' k = ∑ k, q' k := by
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have : ∑ k ∈ Kset, q' k = 0 := Finset.sum_eq_zero hq'zero
      rw [this]; ring
    have hFunion : ∑ g ∈ F' ∪ F, p g = (∑ g ∈ F', p g) + ∑ g ∈ F, p g := by
      refine Finset.sum_union ?_
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      have := hF'R hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at this
      exact this.2 (Or.inr hx')
    rw [hsplit, hq'univ, hFunion]
    linarith [hq'sum]
  · intro k hk
    by_cases hkK : k ∈ Kset
    · simp only [if_pos hkK]; exact hserve k hkK
    · simp only [if_neg hkK]
      exact hq'serve k (Finset.mem_sdiff.mpr ⟨hk, hkK⟩)
  · intro k hk
    have hkK : k ∉ Kset := fun h => hk (hKT h)
    simp only [if_neg hkK]
    exact hq'out k (fun h => hk (Finset.mem_sdiff.mp h).1)

/-! ### Canonical partitions -/

/-- A **canonical partition** into `k` parts of the available goods `R` and banked money `D`,
for an agent with valuation `w`, maximin share `μ` and acceptance threshold `t = ρ·μ`
(Section B of the manuscript).  Part `0` is the *special* ("leftovers") part. -/
structure Canonical (w p : G → ℝ) (μ t : ℝ) (k : ℕ) [NeZero k] (R : Finset G) (D : ℝ) where
  /-- The goods of each part. -/
  goods : Fin k → Finset G
  /-- The set `Sᵢ` of still-available goods the agent intends to sell. -/
  sell : Finset G
  /-- The good of `sell` whose sale funds the part, if any. -/
  src : Fin k → Option G
  /-- The money of the part that comes from the bank `D`. -/
  dcash : Fin k → ℝ
  /-- The money of the part that comes from the sale of `src`. -/
  scash : Fin k → ℝ
  goods_subset : ∀ j, goods j ⊆ R
  goods_disj : ∀ j j', j ≠ j' → Disjoint (goods j) (goods j')
  sell_subset : sell ⊆ R
  sell_disj : ∀ j, Disjoint sell (goods j)
  src_mem : ∀ j f, src j = some f → f ∈ sell
  dcash_nonneg : ∀ j, 0 ≤ dcash j
  scash_nonneg : ∀ j, 0 ≤ scash j
  dcash_sum : ∑ j, dcash j ≤ D
  /-- The parts funded by the sale of `f` share out at most the price of `f`. -/
  scash_sum : ∀ f ∈ sell, ∑ j ∈ Finset.univ.filter (fun j => src j = some f), scash j ≤ p f
  scash_zero : ∀ j, src j = none → scash j = 0
  /-- Condition 1: a good that is put up for sale has price at least `(1−ρ)·μ`. -/
  price_large : ∀ f ∈ sell, μ - t ≤ p f
  /-- Condition 2: every part is acceptable. -/
  acceptable : ∀ j, t ≤ vbarSum w p (goods j) + dcash j + scash j
  /-- Condition 2: apart from the special part, every part is pure or a singleton. -/
  pure_or_singleton : ∀ j, j ≠ 0 → (src j = none ∨ ∃ e, goods j = {e})
  /-- Condition 2: all the money of a singleton part comes from the sale of its associated
  good, so none of it comes from the bank. -/
  singleton_dcash : ∀ j, j ≠ 0 → src j ≠ none → dcash j = 0
  /-- Condition 3, in its non-strict form.

  The manuscript states this condition with a strict inequality, `t < v̄(e) + p(f)`.  The
  construction of Proposition 6 only ever produces the non-strict version: the good `e` of a
  singleton part is a *large* good, `v̄(e) ≥ (1−ρ)·μ`, and condition 1 gives `p(f) ≥ (1−ρ)·μ`,
  so that `v̄(e) + p(f) ≥ 2(1−ρ)·μ = ρ·μ = t` for `ρ = 2/3` — with equality in the borderline
  case.  Nothing in the development uses the strict form (the role condition 3 plays in the
  manuscript is played here by the hypothesis `hloss` of `losses_of_round`), so the condition is
  stated non-strictly. -/
  singleton_cond : ∀ j, j ≠ 0 → src j ≠ none → ∀ e ∈ goods j, ∀ f ∈ sell,
    t ≤ vbar w p e + p f

namespace Canonical

variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}

/-- The total money of a part. -/
def cash (C : Canonical w p μ t k R D) (j : Fin k) : ℝ := C.dcash j + C.scash j

omit [Fintype G] in
lemma cash_nonneg (C : Canonical w p μ t k R D) (j : Fin k) : 0 ≤ C.cash j :=
  add_nonneg (C.dcash_nonneg j) (C.scash_nonneg j)

omit [Fintype G] in
lemma acceptable' (C : Canonical w p μ t k R D) (j : Fin k) :
    t ≤ vbarSum w p (C.goods j) + C.cash j := by
  have := C.acceptable j
  simp only [cash]; linarith

/-- The goods sold in order to fund the parts of `J`. -/
def sold (C : Canonical w p μ t k R D) (J : Finset (Fin k)) : Finset G :=
  J.biUnion (fun j => (C.src j).toFinset)

omit [Fintype G] in
lemma mem_sold {C : Canonical w p μ t k R D} {J : Finset (Fin k)} {f : G} :
    f ∈ C.sold J ↔ ∃ j ∈ J, C.src j = some f := by
  simp [sold, Option.mem_toFinset]

omit [Fintype G] in
lemma sold_subset_sell (C : Canonical w p μ t k R D) (J : Finset (Fin k)) :
    C.sold J ⊆ C.sell := by
  intro f hf
  obtain ⟨j, _, hj⟩ := mem_sold.mp hf
  exact C.src_mem j f hj

omit [Fintype G] in
lemma sold_subset (C : Canonical w p μ t k R D) (J : Finset (Fin k)) : C.sold J ⊆ R :=
  (C.sold_subset_sell J).trans C.sell_subset

omit [Fintype G] in
/-- The money handed out with the parts of `J` does not exceed the bank plus the proceeds of the
goods sold to fund them. -/
lemma cash_sum_le (C : Canonical w p μ t k R D) (J : Finset (Fin k)) :
    ∑ j ∈ J, C.cash j ≤ D + ∑ g ∈ C.sold J, p g := by
  classical
  have hd : ∑ j ∈ J, C.dcash j ≤ D := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun j _ _ => C.dcash_nonneg j)) C.dcash_sum
  have hs : ∑ j ∈ J, C.scash j ≤ ∑ g ∈ C.sold J, p g := by
    set t' : Finset (Option G) := insert none ((C.sold J).image some) with ht'
    have hmaps : ∀ j ∈ J, C.src j ∈ t' := by
      intro j hj
      cases hsrc : C.src j with
      | none => ?_
      | some f => ?_
      · simp [ht']
      · refine Finset.mem_insert_of_mem ?_
        exact Finset.mem_image_of_mem _ (mem_sold.mpr ⟨j, hj, hsrc⟩)
    have hfib := Finset.sum_fiberwise_of_maps_to hmaps C.scash
    have hnone : ∑ j ∈ J.filter (fun j => C.src j = none), C.scash j = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      exact C.scash_zero j (Finset.mem_filter.mp hj).2
    have hsome : ∀ f ∈ C.sold J,
        ∑ j ∈ J.filter (fun j => C.src j = some f), C.scash j ≤ p f := by
      intro f hf
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => C.scash_nonneg j))
        (C.scash_sum f (C.sold_subset_sell J hf))
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.2
    have hsplit : ∑ y ∈ t', ∑ j ∈ J.filter (fun j => C.src j = y), C.scash j
        = (∑ j ∈ J.filter (fun j => C.src j = none), C.scash j)
          + ∑ y ∈ (C.sold J).image some, ∑ j ∈ J.filter (fun j => C.src j = y), C.scash j := by
      rw [ht', Finset.sum_insert (by simp)]
    rw [hsplit, hnone, zero_add] at hfib
    rw [← hfib, Finset.sum_image (fun x _ y _ h => Option.some_injective _ h)]
    exact Finset.sum_le_sum hsome
  simp only [cash, Finset.sum_add_distrib]
  linarith

end Canonical

/-! ### One round of the main loop -/

omit [Fintype G] in
/-- **The matching phase of one round.**  Let `i` be an active agent holding a canonical
partition of the available resources into `|T|` parts (each acceptable to `i`).  Then there are a
set `Kset` of agents served in this round (containing `i`) and an injective assignment `part` of
parts to them such that every served agent finds its part acceptable, every still-active agent
finds *every* part handed out in the round unacceptable, and only `i` may receive the special
part. -/
theorem round_outcome (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ} {μ : ℝ} {i : Fin n} (hi : i ∈ T)
    {k : ℕ} [NeZero k] (hk : T.card = k)
    (C : Canonical (v i) p μ (τ i) k R D) :
    ∃ (Kset : Finset (Fin n)) (part : Fin n → Fin k),
      i ∈ Kset ∧ Kset ⊆ T ∧ Set.InjOn part Kset ∧
      (∀ a ∈ Kset, τ a ≤ vbarSum (v a) p (C.goods (part a)) + C.cash (part a)) ∧
      (∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
          vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < τ a) ∧
      (∀ a ∈ Kset, a ≠ i → part a ≠ 0) ∧ (Kset = T ∨ part i ≠ 0) := by
  classical
  have hcard : 0 < T.card := Finset.card_pos.mpr ⟨i, hi⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  -- the acceptance relation between the other active agents and the non-special parts
  set acc : Fin n → Fin k → Prop :=
    fun a j => τ a ≤ vbarSum (v a) p (C.goods j) + C.cash j with hacc
  haveI : DecidableRel acc := fun a j => Classical.dec _
  set A : Finset (Fin n) := T.erase i with hA
  set B : Finset (Fin k) := Finset.univ.erase 0 with hB
  have hAB : A.card ≤ B.card := by
    have h1 : A.card = T.card - 1 := by rw [hA, Finset.card_erase_of_mem hi]
    have h2 : B.card = k - 1 := by
      rw [hB, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨K, f, hKA, hinj, hfB, hfacc, hclosed, hlast⟩ :=
    exists_closed_matching acc A.card A B rfl hAB
  -- the part that agent `i` receives
  obtain ⟨j₀, hj₀acc, hj₀not, hj₀last⟩ :
      ∃ j₀ : Fin k, (∀ a ∈ A, a ∉ K → ¬ acc a j₀) ∧ (∀ b ∈ K, j₀ ≠ f b) ∧ (K = A ∨ j₀ ≠ 0) := by
    rcases hlast with hKeq | ⟨b, hbB, hbim, hbacc⟩
    · refine ⟨0, ?_, ?_, Or.inl hKeq⟩
      · intro a ha hna; exact absurd (hKeq ▸ ha) hna
      · intro b hb hcon
        have hmem : f b ∈ B := hfB b hb
        rw [hB] at hmem
        exact (Finset.mem_erase.mp hmem).1 hcon.symm
    · refine ⟨b, hbacc, ?_, Or.inr ?_⟩
      · intro b' hb' hcon
        exact hbim (Finset.mem_image.mpr ⟨b', hb', hcon.symm⟩)
      · rw [hB] at hbB; exact (Finset.mem_erase.mp hbB).1
  refine ⟨insert i K, fun a => if a = i then j₀ else f a, Finset.mem_insert_self _ _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hi
    · exact Finset.mem_of_mem_erase (hKA ha)
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exfalso
      have hbi : b ≠ a := fun h => (Finset.mem_erase.mp (hKA hb)).1 h
      simp only [if_neg hbi] at hab
      exact hj₀not b hb hab
    · exfalso
      have hai : a ≠ b := fun h => (Finset.mem_erase.mp (hKA ha)).1 h
      simp only [if_neg hai] at hab
      exact hj₀not a ha hab.symm
    · have hai : a ≠ i := fun h => (Finset.mem_erase.mp (hKA ha)).1 h
      have hbi : b ≠ i := fun h => (Finset.mem_erase.mp (hKA hb)).1 h
      simp only [if_neg hai, if_neg hbi] at hab
      exact hinj ha hb hab
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa using C.acceptable' j₀
    · have hai : a ≠ i := fun h => (Finset.mem_erase.mp (hKA ha)).1 h
      simp only [if_neg hai]
      exact hfacc a ha
  · intro a haT hna b hb
    have haA : a ∈ A := Finset.mem_erase.mpr ⟨fun h => hna (h ▸ Finset.mem_insert_self _ _), haT⟩
    have haK : a ∉ K := fun h => hna (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp hb with rfl | hb
    · have := hj₀acc a haA haK
      simpa [hacc, not_le] using this
    · have hbi : b ≠ i := fun h => (Finset.mem_erase.mp (hKA hb)).1 h
      simp only [if_neg hbi]
      have := hclosed a haA haK b hb
      simpa [hacc, not_le] using this
  · intro a ha hai
    simp only [if_neg hai]
    have haK : a ∈ K := by
      rcases Finset.mem_insert.mp ha with rfl | h
      · exact absurd rfl hai
      · exact h
    have hmem : f a ∈ B := hfB a haK
    rw [hB] at hmem
    exact (Finset.mem_erase.mp hmem).1
  · rcases hj₀last with hKeq | hne
    · refine Or.inl ?_
      rw [hKeq, hA, Finset.insert_erase hi]
    · exact Or.inr (by simpa using hne)

omit [Fintype G] in
/-- **One round of the main loop.**  If the active agent `i` holds a canonical partition of the
available resources into `|T|` parts, and if the state reached after the round is servable, then
the state before the round is servable.  The recursive hypothesis is given all the information
produced by the round (which agents were served, which part each of them received, and the fact
that the still-active agents find all of these parts unacceptable), since that is what is needed
to re-establish the invariant of the algorithm. -/
theorem servable_of_round (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ} {μ : ℝ} {i : Fin n} (hi : i ∈ T)
    {k : ℕ} [NeZero k] (hk : T.card = k)
    (C : Canonical (v i) p μ (τ i) k R D)
    (hrec : ∀ (Kset : Finset (Fin n)) (part : Fin n → Fin k), i ∈ Kset → Kset ⊆ T →
        Set.InjOn part Kset →
        (∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
          vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < τ a) →
        (∀ a ∈ Kset, a ≠ i → part a ≠ 0) → (Kset = T ∨ part i ≠ 0) →
        Servable v p τ (T \ Kset)
          (R \ ((Kset.image part).biUnion C.goods ∪ C.sold (Kset.image part)))
          (D + (∑ g ∈ C.sold (Kset.image part), p g)
              - ∑ j ∈ Kset.image part, C.cash j)) :
    Servable v p τ T R D := by
  classical
  obtain ⟨Kset, part, hiK, hKT, hinj, hserve, hloss, hspecial, hzero⟩ :=
    round_outcome v p τ hi hk C
  have himage : Kset.biUnion (fun a => C.goods (part a)) = (Kset.image part).biUnion C.goods := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hg⟩; exact ⟨part a, ⟨a, ha, rfl⟩, hg⟩
    · rintro ⟨j, ⟨a, ha, rfl⟩, hg⟩; exact ⟨a, ha, hg⟩
  have hsum : ∑ a ∈ Kset, C.cash (part a) = ∑ j ∈ Kset.image part, C.cash j :=
    (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
  refine servable_extend_set v p τ Kset hKT (fun a => C.goods (part a))
    (C.sold (Kset.image part)) (fun a => C.cash (part a))
    (fun a _ => C.goods_subset _) (C.sold_subset _) ?_ ?_
    (fun a _ => C.cash_nonneg _) hserve ?_
  · intro a ha b hb hab
    exact C.goods_disj _ _ (fun h => hab (hinj ha hb h))
  · intro a _
    exact Finset.disjoint_of_subset_left (C.sold_subset_sell _) (C.sell_disj _)
  · rw [himage, hsum]
    exact hrec Kset part hiK hKT hinj hloss hspecial hzero

end FairSelling
