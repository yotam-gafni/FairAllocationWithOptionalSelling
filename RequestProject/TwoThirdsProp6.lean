import Mathlib
import RequestProject.Selling
import RequestProject.TwoThirdsCanonical
import RequestProject.TwoThirdsBagFilling

/-!
# Proposition 6: constructing a canonical partition

This file formalizes **Proposition 6** of the manuscript (Algorithm 3,
`UNSTRUCTURED-FIND-CANONICAL`): if the large goods that are still available are at most as many
as the parts to be built, and the value still at our disposal is large enough, then a canonical
partition exists.

Throughout, `ε` plays the role of `(1−ρ)·MMSᵢ = MMSᵢ/3`, so that the acceptance threshold is
`t = 2ε = ρ·MMSᵢ` and the maximin share is `μ = 3ε`.  The resources are split into

* `A` — the *large* goods, `ε ≤ v̄(e) ≤ 2ε`, one per part;
* `C` — the *cheap* goods, `v̄(e) ≤ ε`;
* `S` — the goods the agent intends to sell, `p(e) ≥ ε` and `w(e) ≤ p(e)` (so `v̄(e) = p(e)`);
* `d` — the banked money `P′`.

The parts are built one at a time, from the last one down to part `0`, which is the *special*
("leftovers") part and simply absorbs whatever is left.  A part is built either

* by pouring banked money and then cheap goods on top of its large good until it reaches `2ε`
  (a *pure* part, of value at most `3ε`), or
* by pouring into it the proceeds of a single good of `S` (a *singleton* part): the manuscript's
  cascade, in which a sold good funds several consecutive parts.  The rule is: give the part all
  the remaining proceeds `r` if that keeps its value at most `3ε`, and otherwise give it exactly
  what it needs to reach `2ε`, which leaves more than `ε` of proceeds for the next part.  As a
  large good is worth at least `ε` and the leftover proceeds are always at least `ε`, a part is
  always made acceptable by the proceeds of *one* good, which is what canonicity condition 2(b)
  demands.

The state of the construction is carried by the hypotheses of `fill_exists`, and its output by
the structure `FillOut`.  `exists_canonical_of_small` packages the result as a `Canonical`
structure.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- The output of the filling procedure: `m` parts (indexed by the natural numbers below `m`,
part `0` being the special one) built out of the resources `Res`, the banked money `d` and the
proceeds `r` of the good `f₀` that is currently being sold. -/
structure FillOut (w p : G → ℝ) (ε : ℝ) (m : ℕ) (Res : Finset G) (d r : ℝ) (f₀ : Option G) where
  /-- The goods of each part. -/
  goods : ℕ → Finset G
  /-- The goods that are sold. -/
  sell : Finset G
  /-- The good whose sale funds each part, if any. -/
  src : ℕ → Option G
  /-- The banked money of each part. -/
  dcash : ℕ → ℝ
  /-- The sale proceeds of each part. -/
  scash : ℕ → ℝ
  goods_subset : ∀ j, goods j ⊆ Res
  goods_disj : ∀ j j', j ≠ j' → Disjoint (goods j) (goods j')
  goods_zero : ∀ j, m ≤ j → goods j = ∅
  sell_subset : sell ⊆ Res ∪ f₀.toFinset
  sell_disj : ∀ j, Disjoint sell (goods j)
  src_mem : ∀ j f, src j = some f → f ∈ sell
  src_zero : ∀ j, m ≤ j → src j = none
  dcash_nonneg : ∀ j, 0 ≤ dcash j
  scash_nonneg : ∀ j, 0 ≤ scash j
  dcash_zero : ∀ j, m ≤ j → dcash j = 0
  dcash_sum : ∑ j ∈ Finset.range m, dcash j ≤ d
  scash_sum : ∀ f, ∑ j ∈ (Finset.range m).filter (fun j => src j = some f), scash j
    ≤ (if f₀ = some f then r else p f)
  scash_zero : ∀ j, src j = none → scash j = 0
  price_large : ∀ f ∈ sell, ε ≤ p f
  acceptable : ∀ j < m, 2 * ε ≤ vbarSum w p (goods j) + dcash j + scash j
  pure_or_singleton : ∀ j, j ≠ 0 → j < m → (src j = none ∨ ∃ e, goods j = {e})
  singleton_dcash : ∀ j, j ≠ 0 → src j ≠ none → dcash j = 0
  singleton_large : ∀ j, j ≠ 0 → src j ≠ none → ∀ e ∈ goods j, ε ≤ vbar w p e

omit [Fintype G] in
/-- Adding one more part, of index `m`, on top of a filling of the smaller state. -/
lemma fillout_snoc (w p : G → ℝ) (ε : ℝ) {m : ℕ}
    {Res Res' : Finset G} {d r d' r' : ℝ} {f₀ f₀' : Option G}
    (F : FillOut w p ε m Res' d' r' f₀') (hRes' : Res' ⊆ Res)
    (hf₀' : ∀ f, f₀' = some f → f ∈ Res ∪ f₀.toFinset)
    (Enew : Finset G) (srcnew : Option G) (dnew snew : ℝ)
    (hEnew : Enew ⊆ Res)
    (hEdisj : Disjoint Enew (Res' ∪ f₀'.toFinset ∪ srcnew.toFinset))
    (hdnew : 0 ≤ dnew) (hsnew : 0 ≤ snew) (hd : d' + dnew ≤ d)
    (hacc : 2 * ε ≤ vbarSum w p Enew + dnew + snew)
    (hps : srcnew = none ∨ ∃ e, Enew = {e})
    (hsd : srcnew ≠ none → dnew = 0)
    (hsl : srcnew ≠ none → ∀ e ∈ Enew, ε ≤ vbar w p e)
    (hsz : srcnew = none → snew = 0)
    (hsnotin : ∀ f, srcnew = some f → f ∉ Res' ∧ ε ≤ p f ∧ f ∈ Res ∪ f₀.toFinset)
    (hmoney : ∀ f, (if srcnew = some f then snew else 0)
      + (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0)
      ≤ (if f₀ = some f then r else p f)) :
    Nonempty (FillOut w p ε (m + 1) Res d r f₀) := by
  classical
  -- the recursive parts never contain the new part's goods
  have hgoodsRes' : ∀ j, F.goods j ⊆ Res' := F.goods_subset
  have hEdisjRes' : Disjoint Enew Res' :=
    Finset.disjoint_of_subset_right (by intro x hx; simp [hx]) hEdisj
  refine ⟨{ goods := fun j => if j = m then Enew else F.goods j
            sell := F.sell ∪ srcnew.toFinset
            src := fun j => if j = m then srcnew else F.src j
            dcash := fun j => if j = m then dnew else F.dcash j
            scash := fun j => if j = m then snew else F.scash j
            goods_subset := ?_
            goods_disj := ?_
            goods_zero := ?_
            sell_subset := ?_
            sell_disj := ?_
            src_mem := ?_
            src_zero := ?_
            dcash_nonneg := ?_
            scash_nonneg := ?_
            dcash_zero := ?_
            dcash_sum := ?_
            scash_sum := ?_
            scash_zero := ?_
            price_large := ?_
            acceptable := ?_
            pure_or_singleton := ?_
            singleton_dcash := ?_
            singleton_large := ?_ }⟩
  · intro j
    by_cases h : j = m
    · simpa [h] using hEnew
    · simp only [if_neg h]; exact (F.goods_subset j).trans hRes'
  · intro j j' hjj
    by_cases h : j = m
    · have h' : j' ≠ m := fun hh => hjj (by rw [h, hh])
      simp only [if_pos h, if_neg h']
      exact Finset.disjoint_of_subset_right (F.goods_subset j') hEdisjRes'
    · by_cases h' : j' = m
      · simp only [if_neg h, if_pos h']
        exact (Finset.disjoint_of_subset_right (F.goods_subset j) hEdisjRes').symm
      · simp only [if_neg h, if_neg h']; exact F.goods_disj j j' hjj
  · intro j hj
    have h : j ≠ m := by omega
    simp only [if_neg h]
    exact F.goods_zero j (by omega)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp (F.sell_subset hx) with hx' | hx'
      · exact Finset.mem_union_left _ (hRes' hx')
      · exact hf₀' x (Option.mem_toFinset.mp hx')
    · exact hsnotin x (Option.mem_toFinset.mp hx) |>.2.2
  · intro j
    by_cases h : j = m
    · simp only [if_pos h]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp (F.sell_subset hx) with hy | hy
        · exact Finset.disjoint_left.mp hEdisj hx' (by simp [hy])
        · exact Finset.disjoint_left.mp hEdisj hx' (by simp [hy])
      · exact Finset.disjoint_left.mp hEdisj hx' (by simp [hx])
    · simp only [if_neg h]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (F.sell_disj j) hx hx'
      · exact (hsnotin x (Option.mem_toFinset.mp hx)).1 (F.goods_subset j hx')
  · intro j f hf
    by_cases h : j = m
    · rw [if_pos h] at hf
      exact Finset.mem_union_right _ (by simp [hf])
    · rw [if_neg h] at hf
      exact Finset.mem_union_left _ (F.src_mem j f hf)
  · intro j hj
    have h : j ≠ m := by omega
    simp only [if_neg h]
    exact F.src_zero j (by omega)
  · intro j; by_cases h : j = m
    · simpa [h] using hdnew
    · simp only [if_neg h]; exact F.dcash_nonneg j
  · intro j; by_cases h : j = m
    · simpa [h] using hsnew
    · simp only [if_neg h]; exact F.scash_nonneg j
  · intro j hj
    have h : j ≠ m := by omega
    simp only [if_neg h]
    exact F.dcash_zero j (by omega)
  · rw [Finset.sum_range_succ]
    have : ∑ j ∈ Finset.range m, (if j = m then dnew else F.dcash j)
        = ∑ j ∈ Finset.range m, F.dcash j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [if_neg (by simp at hj; omega)]
    rw [this, if_pos rfl]
    linarith [F.dcash_sum]
  · intro f
    have hsplit : ∑ j ∈ (Finset.range (m + 1)).filter
          (fun j => (if j = m then srcnew else F.src j) = some f),
          (if j = m then snew else F.scash j)
        = (if srcnew = some f then snew else 0)
          + ∑ j ∈ (Finset.range m).filter (fun j => F.src j = some f), F.scash j := by
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hnew : srcnew = some f
      · rw [if_pos (by simpa using hnew)]
        rw [Finset.sum_insert (by simp)]
        rw [if_pos rfl, if_pos hnew]
        congr 1
        rw [Finset.filter_congr (fun j hj => by
          simp only [Finset.mem_range] at hj
          rw [if_neg (by omega)])]
        exact Finset.sum_congr rfl (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          rw [if_neg (by omega)])
      · rw [if_neg (by simpa using hnew), if_neg hnew, zero_add]
        rw [Finset.filter_congr (fun j hj => by
          simp only [Finset.mem_range] at hj
          rw [if_neg (by omega)])]
        exact Finset.sum_congr rfl (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          rw [if_neg (by omega)])
    rw [hsplit]
    have hrec : ∑ j ∈ (Finset.range m).filter (fun j => F.src j = some f), F.scash j
        ≤ (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0) := by
      by_cases hf : f ∈ F.sell
      · rw [if_pos hf]; exact F.scash_sum f
      · rw [if_neg hf]
        have : (Finset.range m).filter (fun j => F.src j = some f) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr (fun j _ hj => hf (F.src_mem j f hj))
        rw [this, Finset.sum_empty]
    calc (if srcnew = some f then snew else 0)
          + ∑ j ∈ (Finset.range m).filter (fun j => F.src j = some f), F.scash j
        ≤ (if srcnew = some f then snew else 0)
          + (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0) := by linarith
      _ ≤ _ := hmoney f
  · intro j hj
    by_cases h : j = m
    · rw [if_pos h] at hj ⊢; exact hsz hj
    · rw [if_neg h] at hj ⊢; exact F.scash_zero j hj
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact F.price_large f hf
    · exact (hsnotin f (Option.mem_toFinset.mp hf)).2.1
  · intro j hj
    by_cases h : j = m
    · simp only [if_pos h]; exact hacc
    · simp only [if_neg h]; exact F.acceptable j (by omega)
  · intro j hj0 hj
    by_cases h : j = m
    · simp only [if_pos h]; exact hps
    · simp only [if_neg h]; exact F.pure_or_singleton j hj0 (by omega)
  · intro j hj0 hj
    by_cases h : j = m
    · rw [if_pos h] at hj ⊢; exact hsd hj
    · rw [if_neg h] at hj ⊢; exact F.singleton_dcash j hj0 hj
  · intro j hj0 hj e he
    by_cases h : j = m
    · rw [if_pos h] at hj he; exact hsl hj e he
    · rw [if_neg h] at hj he; exact F.singleton_large j hj0 hj e he

/-! ### The filling procedure -/

omit [Fintype G] [DecidableEq G] in
private lemma vbar_nonneg' {w p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ vbar w p g :=
  le_trans (hp g) (le_max_left _ _)

omit [Fintype G] in
private lemma vbarSum_union_three {w p : G → ℝ} {A C S : Finset G}
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S) :
    vbarSum w p (A ∪ C ∪ S)
      = (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + ∑ g ∈ S, vbar w p g := by
  classical
  have h1 : Disjoint (A ∪ C) S := Finset.disjoint_union_left.mpr ⟨hAS, hCS⟩
  simp only [vbarSum]
  rw [Finset.sum_union h1, Finset.sum_union hAC]

omit [Fintype G] in
/-- The last step of the filling procedure: a single part, the special one, which simply absorbs
all the remaining resources. -/
theorem fill_one (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε)
    (A C S : Finset G) (d r : ℝ) (f₀ : Option G)
    (hS2 : ∀ g ∈ S, vbar w p g = p g)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hd : 0 ≤ d) (hr : r = 0 ∨ ε ≤ r)
    (hf₀ : ∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f)
    (hf₀n : f₀ = none → r = 0)
    (hbud : 2 * ε ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r) :
    Nonempty (FillOut w p ε 1 (A ∪ C ∪ S) d r f₀) := by
  classical
  have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
  refine ⟨{ goods := fun j => if j = 0 then A ∪ C ∪ S else ∅
            sell := f₀.toFinset
            src := fun j => if j = 0 then f₀ else none
            dcash := fun j => if j = 0 then d else 0
            scash := fun j => if j = 0 then r else 0
            goods_subset := ?_
            goods_disj := ?_
            goods_zero := ?_
            sell_subset := ?_
            sell_disj := ?_
            src_mem := ?_
            src_zero := ?_
            dcash_nonneg := ?_
            scash_nonneg := ?_
            dcash_zero := ?_
            dcash_sum := ?_
            scash_sum := ?_
            scash_zero := ?_
            price_large := ?_
            acceptable := ?_
            pure_or_singleton := ?_
            singleton_dcash := ?_
            singleton_large := ?_ }⟩
  · intro j; by_cases h : j = 0 <;> simp [h]
  · intro j j' hjj
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : j' ≠ 0 := fun h => hjj (h.symm)
      simp [this]
    · have : j ≠ 0 := by omega
      simp [this]
  · intro j hj; rw [if_neg (by omega : j ≠ 0)]
  · exact Finset.subset_union_right
  · intro j
    by_cases h : j = 0
    · subst h
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      obtain ⟨hxA, hxC, hxS, _, _⟩ := hf₀ x (Option.mem_toFinset.mp hx)
      rcases Finset.mem_union.mp hx' with hx' | hx'
      · rcases Finset.mem_union.mp hx' with hx' | hx'
        · exact hxA hx'
        · exact hxC hx'
      · exact hxS hx'
    · simp [h]
  · intro j f hf
    by_cases h : j = 0
    · rw [if_pos h] at hf; simpa using hf
    · rw [if_neg h] at hf; exact absurd hf (by simp)
  · intro j hj; rw [if_neg (by omega : j ≠ 0)]
  · intro j; by_cases h : j = 0 <;> simp [h, hd]
  · intro j; by_cases h : j = 0 <;> simp [h, hr0]
  · intro j hj; rw [if_neg (by omega : j ≠ 0)]
  · simp
  · intro f
    have : (Finset.range 1).filter (fun j => (if j = 0 then f₀ else none) = some f)
        ⊆ {0} := by
      intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp; omega
    rcases Option.eq_none_or_eq_some f₀ with h' | ⟨f', h'⟩
    · simp only [h']
      simp
      exact hp f
    · by_cases hff : f' = f
      · subst hff
        rw [show (Finset.range 1).filter (fun j => (if j = 0 then f₀ else none) = some f')
            = {0} by ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
                     constructor
                     · rintro ⟨hj, -⟩; omega
                     · rintro rfl; exact ⟨by omega, by simp [h']⟩]
        simp [h']
      · rw [show (Finset.range 1).filter (fun j => (if j = 0 then f₀ else none) = some f)
            = ∅ by
              ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
                iff_false, not_and]
              intro hj
              interval_cases j
              simp [h']
              exact fun hc => hff (by simpa using hc)]
        simp only [Finset.sum_empty]
        split
        · exact hr0
        · exact hp f
  · intro j hj
    by_cases h : j = 0
    · rw [if_pos h] at hj ⊢; simp [hf₀n hj]
    · simp [h]
  · intro f hf; exact (hf₀ f (Option.mem_toFinset.mp hf)).2.2.2.2
  · intro j hj
    have h : j = 0 := by omega
    subst h
    have hSv : ∑ g ∈ S, vbar w p g = ∑ g ∈ S, p g := Finset.sum_congr rfl hS2
    have key : 2 * ε ≤ vbarSum w p (A ∪ C ∪ S) + d + r := by
      rw [vbarSum_union_three hAC hAS hCS, hSv]
      linarith
    simpa using key
  · intro j hj0 hj; omega
  · intro j hj0 hj
    rw [if_neg hj0] at hj; exact absurd rfl hj
  · intro j hj0 hj
    rw [if_neg hj0] at hj; exact absurd rfl hj

/-- **The filling procedure.**  `m + 1` parts, the special one being part `0`, are built out of
the large goods `A`, the cheap goods `C`, the goods `S` that the agent intends to sell, the
banked money `d` and the proceeds `r` of the good `f₀` currently being sold.

The two structural hypotheses are that there are no more large goods than parts (`A.card ≤ m+1`)
and that, unless there is nothing left to sell, every part gets a large good
(`A.card = m+1 ∨ (S = ∅ ∧ r = 0)`); the quantitative hypothesis is that the total value at our
disposal is at least `m·μ + t`, i.e. `μ` for each of the `m` non-special parts and `t` for the
special one, where `μ = 3ε` and `t = 2ε`. -/
theorem fill_exists (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (m : ℕ) (A C S : Finset G) (d r : ℝ) (f₀ : Option G),
      (∀ g ∈ A, ε ≤ vbar w p g) → (∀ g ∈ A, vbar w p g ≤ 2 * ε) →
      (∀ g ∈ C, vbar w p g ≤ ε) →
      (∀ g ∈ S, ε ≤ p g) → (∀ g ∈ S, vbar w p g = p g) →
      Disjoint A C → Disjoint A S → Disjoint C S →
      0 ≤ d → (r = 0 ∨ ε ≤ r) →
      (∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f) →
      (f₀ = none → r = 0) →
      A.card ≤ m + 1 → (A.card = m + 1 ∨ (S = ∅ ∧ r = 0)) →
      (m : ℝ) * (3 * ε) + 2 * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r →
      Nonempty (FillOut w p ε (m + 1) (A ∪ C ∪ S) d r f₀) := by
  classical
  intro m
  induction m with
  | zero =>
    intro A C S d r f₀ _ _ _ _ hS2 hAC hAS hCS hd hr hf₀ hf₀n _ _ hbud
    exact fill_one w p hp hε A C S d r f₀ hS2 hAC hAS hCS hd hr hf₀ hf₀n (by
      simp only [Nat.cast_zero, zero_mul, zero_add] at hbud
      linarith)
  | succ m ih =>
    intro A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n hcard hseed hbud
    have hvb0 : ∀ g, 0 ≤ vbar w p g := vbar_nonneg' hp
    have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
    by_cases hsale : S = ∅ ∧ r = 0
    · -- **The filling case**: nothing left to sell, the new part is pure.
      obtain ⟨hSe, hre⟩ := hsale
      obtain ⟨Aseed, A', hseedsub, hA'def, hσ1, hσ2, hAsplit, hA'card⟩ :
          ∃ (Aseed A' : Finset G), Aseed ⊆ A ∧ A' = A \ Aseed ∧
            (∀ e ∈ Aseed, ε ≤ vbar w p e) ∧ vbarSum w p Aseed ≤ 2 * ε ∧
            (∑ g ∈ A, vbar w p g) = vbarSum w p Aseed + ∑ g ∈ A', vbar w p g ∧
            A'.card ≤ m + 1 := by
        by_cases hAne : A.Nonempty
        · obtain ⟨a, ha⟩ := hAne
          refine ⟨{a}, A \ {a}, by simpa using ha, rfl, by simpa using hA1 a ha, ?_, ?_, ?_⟩
          · simpa [vbarSum] using hA2 a ha
          · rw [← Finset.sum_sdiff (by simpa using ha : ({a} : Finset G) ⊆ A)]
            simp [vbarSum, add_comm]
          · have : (A \ {a}).card = A.card - 1 := by
              rw [Finset.sdiff_singleton_eq_erase]; exact Finset.card_erase_of_mem ha
            have h1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
            omega
        · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
          exact ⟨∅, ∅, by simp, by simp [hAe], by simp, by simp [vbarSum]; linarith,
            by simp [hAe, vbarSum], by simp⟩
      set σ : ℝ := vbarSum w p Aseed with hσdef
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg (fun g _ => hvb0 g)
      set need : ℝ := 2 * ε - σ with hneeddef
      have hneed0 : 0 ≤ need := by simp only [hneeddef]; linarith
      set dnew : ℝ := min d need with hdnewdef
      have hdnew0 : 0 ≤ dnew := le_min hd hneed0
      set rest : ℝ := need - dnew with hrestdef
      have hrest0 : 0 ≤ rest := by
        simp only [hrestdef, hdnewdef, sub_nonneg]; exact min_le_right _ _
      -- the cheap goods suffice to cover what the bank could not
      have hrestC : rest ≤ ∑ g ∈ C, vbar w p g := by
        rcases le_total need d with hle | hlt
        · have : dnew = need := min_eq_right hle
          simp only [hrestdef, this, sub_self]
          exact Finset.sum_nonneg (fun g _ => hvb0 g)
        · have hdn : dnew = d := min_eq_left hlt
          have hA'sum : (∑ g ∈ A', vbar w p g) ≤ ((m : ℝ) + 1) * (2 * ε) := by
            calc (∑ g ∈ A', vbar w p g) ≤ ∑ _g ∈ A', 2 * ε :=
                  Finset.sum_le_sum (fun g hg => hA2 g (by
                    rw [hA'def] at hg; exact (Finset.mem_sdiff.mp hg).1))
              _ = (A'.card : ℝ) * (2 * ε) := by simp [mul_comm]
              _ ≤ ((m : ℝ) + 1) * (2 * ε) := by
                  have : (A'.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hA'card
                  nlinarith
          have hb : ((m : ℝ) + 1) * (3 * ε) + 2 * ε
              ≤ σ + (∑ g ∈ A', vbar w p g) + (∑ g ∈ C, vbar w p g) + d := by
            have := hbud
            rw [hAsplit, hSe, hre] at this
            push_cast at this ⊢
            simp only [Finset.sum_empty] at this
            linarith
          have hm0 : (0 : ℝ) ≤ ((m : ℝ) + 1) * ε := by positivity
          simp only [hrestdef, hdn, hneeddef]
          nlinarith
      obtain ⟨B, hBsub, hBge, hBmin⟩ :=
        exists_minimal_subset_sum (fun g => vbar w p g) rest C hrestC
      have hBle : (∑ g ∈ B, vbar w p g) ≤ rest + ε :=
        minimal_bag_le hrest0 hε (fun g hg => hC1 g (hBsub hg)) hBge hBmin
      have hB0 : 0 ≤ ∑ g ∈ B, vbar w p g := Finset.sum_nonneg (fun g _ => hvb0 g)
      -- the new part
      set Enew : Finset G := Aseed ∪ B with hEnewdef
      have hAseedB : Disjoint Aseed B :=
        Finset.disjoint_of_subset_left hseedsub (Finset.disjoint_of_subset_right hBsub hAC)
      have hEval : vbarSum w p Enew = σ + ∑ g ∈ B, vbar w p g := by
        simp only [hEnewdef, vbarSum, hσdef]
        exact Finset.sum_union hAseedB
      -- the recursive call
      have hC'sum : (∑ g ∈ C \ B, vbar w p g) = (∑ g ∈ C, vbar w p g) - ∑ g ∈ B, vbar w p g :=
        Finset.sum_sdiff_eq_sub hBsub
      have hf₀'rec : ∀ f, f₀ = some f →
          f ∉ A' ∧ f ∉ C \ B ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f := by
        intro f hf
        refine ⟨fun hc => (hf₀ f hf).1 ?_, fun hc => (hf₀ f hf).2.1 (Finset.mem_sdiff.mp hc).1,
          (hf₀ f hf).2.2.1, (hf₀ f hf).2.2.2.1, (hf₀ f hf).2.2.2.2⟩
        rw [hA'def] at hc
        exact (Finset.mem_sdiff.mp hc).1
      have hrec := ih A' (C \ B) S (d - dnew) r f₀
        (fun g hg => hA1 g (by rw [hA'def] at hg; exact (Finset.mem_sdiff.mp hg).1))
        (fun g hg => hA2 g (by rw [hA'def] at hg; exact (Finset.mem_sdiff.mp hg).1))
        (fun g hg => hC1 g (Finset.mem_sdiff.mp hg).1)
        hS1 hS2
        (Finset.disjoint_of_subset_left (by rw [hA'def]; exact Finset.sdiff_subset)
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hAC))
        (Finset.disjoint_of_subset_left (by rw [hA'def]; exact Finset.sdiff_subset) hAS)
        (Finset.disjoint_of_subset_left Finset.sdiff_subset hCS)
        (by simp only [hdnewdef]; rcases le_total d need with h | h
            · simp [min_eq_left h]
            · simp [min_eq_right h]; linarith)
        hr
        hf₀'rec
        hf₀n hA'card (Or.inr ⟨hSe, hre⟩) (by
          rw [hC'sum]
          have := hbud
          rw [hAsplit] at this
          push_cast at this ⊢
          have hcost : σ + (∑ g ∈ B, vbar w p g) + dnew ≤ 3 * ε := by
            simp only [hrestdef] at hBle; simp only [hneeddef] at hBle ⊢; linarith
          linarith)
      obtain ⟨F⟩ := hrec
      refine fillout_snoc w p ε F ?_ ?_ Enew none dnew 0 ?_ ?_ hdnew0 le_rfl (by linarith) ?_
        (Or.inl rfl) (fun h => absurd rfl h) (fun h => absurd rfl h) (fun _ => rfl)
        (fun f hf => absurd hf (by simp)) ?_
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (by rw [hA'def] at hx; exact (Finset.mem_sdiff.mp hx).1))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_sdiff.mp hx).1)
        · exact Finset.mem_union_right _ hx
      · intro f hf
        exact Finset.mem_union_right _ (by simp [hf])
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hseedsub hx))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hBsub hx))
      · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
        have hxAC : x ∈ Aseed ∨ x ∈ B := Finset.mem_union.mp hx
        simp only [Option.toFinset_none, Finset.union_empty] at hx'
        rcases Finset.mem_union.mp hx' with hx' | hx'
        · rcases Finset.mem_union.mp hx' with hx' | hx'
          · rcases Finset.mem_union.mp hx' with hx' | hx'
            · rw [hA'def] at hx'
              rcases hxAC with h | h
              · exact (Finset.mem_sdiff.mp hx').2 h
              · exact Finset.disjoint_left.mp hAC (Finset.mem_sdiff.mp hx').1 (hBsub h)
            · rcases hxAC with h | h
              · exact Finset.disjoint_left.mp hAC (hseedsub h) (Finset.mem_sdiff.mp hx').1
              · exact (Finset.mem_sdiff.mp hx').2 h
          · rcases hxAC with h | h
            · exact Finset.disjoint_left.mp hAS (hseedsub h) hx'
            · exact Finset.disjoint_left.mp hCS (hBsub h) hx'
        · obtain ⟨hxA, hxC, -⟩ := hf₀ x (Option.mem_toFinset.mp hx')
          rcases hxAC with h | h
          · exact hxA (hseedsub h)
          · exact hxC (hBsub h)
      · rw [hEval]
        simp only [hrestdef, hneeddef] at hBge
        simp only [hneeddef, hdnewdef] at *
        linarith
      · intro f
        simp only [reduceCtorEq, if_false, zero_add]
        by_cases hmem : f ∈ F.sell
        · rw [if_pos hmem]
        · rw [if_neg hmem]
          split
          · exact hr0
          · exact hp f
    · -- **The cascade case**: the new part is a singleton funded by the sale of one good.
      have hAcard : A.card = m + 1 + 1 := by
        rcases hseed with h | h
        · exact h
        · exact absurd h hsale
      obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
      -- the good that is being sold, and the proceeds available from it
      obtain ⟨f, r₁, S', hfA, hfC, hfS', hr₁ε, hr₁p, hpf, hS'sub, hbudeq, hr₁le, hfmem⟩ :
          ∃ (f : G) (r₁ : ℝ) (S' : Finset G),
            f ∉ A ∧ f ∉ C ∧ f ∉ S' ∧ ε ≤ r₁ ∧ r₁ ≤ p f ∧ ε ≤ p f ∧ S' ⊆ S ∧
            (∑ g ∈ S', p g) + r₁ = (∑ g ∈ S, p g) + r ∧
            r₁ ≤ (if f₀ = some f then r else p f) ∧ f ∈ (A ∪ C ∪ S) ∪ f₀.toFinset := by
        by_cases hr' : r = 0
        · have hSne : S.Nonempty := by
            rcases Finset.eq_empty_or_nonempty S with h | h
            · exact absurd ⟨h, hr'⟩ hsale
            · exact h
          obtain ⟨f, hf⟩ := hSne
          refine ⟨f, p f, S.erase f, fun hc => Finset.disjoint_left.mp hAS hc hf,
            fun hc => Finset.disjoint_left.mp hCS hc hf, Finset.notMem_erase _ _,
            hS1 f hf, le_rfl, hS1 f hf, Finset.erase_subset _ _, ?_, ?_, ?_⟩
          · rw [Finset.sum_erase_add _ _ hf, hr', add_zero]
          · rcases Option.eq_none_or_eq_some f₀ with h' | ⟨f', h'⟩
            · simp [h']
            · have : f' ≠ f := fun hc => (hf₀ f' h').2.2.1 (hc ▸ hf)
              rw [if_neg (by rw [h']; simpa using this)]
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hf)
        · obtain ⟨f, hf⟩ : ∃ f, f₀ = some f := by
            rcases Option.eq_none_or_eq_some f₀ with h' | h'
            · exact absurd (hf₀n h') hr'
            · exact h'
          obtain ⟨hfA, hfC, hfS, hrp, hpf⟩ := hf₀ f hf
          refine ⟨f, r, S, hfA, hfC, hfS, ?_, hrp, hpf, Finset.Subset.refl _, rfl, ?_, ?_⟩
          · rcases hr with h | h
            · exact absurd h hr'
            · exact h
          · rw [if_pos hf]
          · exact Finset.mem_union_right _ (by simp [hf])
      set σ : ℝ := vbar w p a with hσdef
      have hσ1 : ε ≤ σ := hA1 a ha
      have hσ2 : σ ≤ 2 * ε := hA2 a ha
      set snew : ℝ := if r₁ ≤ 3 * ε - σ then r₁ else 2 * ε - σ with hsnewdef
      set r' : ℝ := r₁ - snew with hr'def
      have hsnew0 : 0 ≤ snew := by
        simp only [hsnewdef]; split
        · linarith
        · linarith
      have hr'0 : 0 ≤ r' := by
        simp only [hr'def, hsnewdef]; split
        · simp
        · rename_i hc; push_neg at hc; linarith
      have hr'cases : r' = 0 ∨ ε ≤ r' := by
        simp only [hr'def, hsnewdef]; split
        · left; ring
        · rename_i hc; push_neg at hc; right; linarith
      have hacc : 2 * ε ≤ σ + snew := by
        simp only [hsnewdef]; split
        · linarith
        · linarith
      have hcost : σ + snew ≤ 3 * ε := by
        simp only [hsnewdef]; split
        · rename_i hc; linarith
        · linarith
      -- the recursive call
      have hA'card : (A.erase a).card = m + 1 := by
        rw [Finset.card_erase_of_mem ha, hAcard]
        omega
      have hrec := ih (A.erase a) C S' (d) r' (some f)
        (fun g hg => hA1 g (Finset.mem_of_mem_erase hg))
        (fun g hg => hA2 g (Finset.mem_of_mem_erase hg))
        hC1 (fun g hg => hS1 g (hS'sub hg)) (fun g hg => hS2 g (hS'sub hg))
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hAC)
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          (Finset.disjoint_of_subset_right hS'sub hAS))
        (Finset.disjoint_of_subset_right hS'sub hCS)
        hd hr'cases
        (fun f' hf' => by
          have : f' = f := by simpa using hf'.symm
          subst this
          exact ⟨fun hc => hfA (Finset.mem_of_mem_erase hc), hfC, hfS',
            le_trans (by simp only [hr'def]; linarith) hr₁p, hpf⟩)
        (by simp) (by omega) (Or.inl hA'card)
        (by
          have hAsum : (∑ g ∈ A, vbar w p g) = σ + ∑ g ∈ A.erase a, vbar w p g := by
            rw [hσdef, Finset.add_sum_erase _ _ ha]
          have := hbud
          rw [hAsum] at this
          push_cast at this ⊢
          simp only [hr'def]
          linarith [hbudeq]
          )
      obtain ⟨F⟩ := hrec
      refine fillout_snoc w p ε F ?_ ?_ {a} (some f) 0 snew ?_ ?_ le_rfl hsnew0 (by linarith)
        ?_ (Or.inr ⟨a, rfl⟩) (fun _ => rfl) ?_ (fun h => absurd h (by simp)) ?_ ?_
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_of_mem_erase hx))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        · exact Finset.mem_union_right _ (hS'sub hx)
      · intro f' hf'
        have : f' = f := by simpa using hf'.symm
        subst this; exact hfmem
      · simp only [Finset.singleton_subset_iff]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
      · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
        have hxa : x = a := by simpa using hx
        subst hxa
        rcases Finset.mem_union.mp hx' with hx' | hx'
        · rcases Finset.mem_union.mp hx' with hx' | hx'
          · rcases Finset.mem_union.mp hx' with hx' | hx'
            · rcases Finset.mem_union.mp hx' with hx' | hx'
              · exact (Finset.notMem_erase _ _) hx'
              · exact Finset.disjoint_left.mp hAC ha hx'
            · exact Finset.disjoint_left.mp hAS ha (hS'sub hx')
          · have haf : x = f := by simpa using hx'
            exact hfA (haf ▸ ha)
        · have haf : x = f := by simpa using hx'
          exact hfA (haf ▸ ha)
      · simp only [vbarSum, Finset.sum_singleton, ← hσdef]
        linarith
      · intro _ e he
        have : e = a := by simpa using he
        subst this; exact hσ1
      · intro f' hf'
        have : f' = f := by simpa using hf'.symm
        subst this
        refine ⟨fun hc => ?_, hpf, hfmem⟩
        rcases Finset.mem_union.mp hc with hc | hc
        · rcases Finset.mem_union.mp hc with hc | hc
          · exact hfA (Finset.mem_of_mem_erase hc)
          · exact hfC hc
        · exact hfS' hc
      · intro f'
        by_cases hff : f' = f
        · subst hff
          rw [if_pos rfl]
          have h1 : (if f' ∈ F.sell then (if some f' = some f' then r' else p f') else 0) ≤ r' := by
            split
            · rw [if_pos rfl]
            · exact hr'0
          have : snew + r' = r₁ := by simp only [hr'def]; ring
          linarith [hr₁le]
        · rw [if_neg (by simpa using fun hc => hff hc.symm)]
          rw [zero_add]
          by_cases hmem : f' ∈ F.sell
          · rw [if_pos hmem, if_neg (by simpa using fun hc => hff hc.symm)]
            have hnot : f₀ ≠ some f' := by
              intro hc
              obtain ⟨hA', hC', hS'', -⟩ := hf₀ f' hc
              rcases Finset.mem_union.mp (F.sell_subset hmem) with hx | hx
              · rcases Finset.mem_union.mp hx with hx | hx
                · rcases Finset.mem_union.mp hx with hx | hx
                  · exact hA' (Finset.mem_of_mem_erase hx)
                  · exact hC' hx
                · exact hS'' (hS'sub hx)
              · exact hff (by simpa using hx)
            rw [if_neg hnot]
          · rw [if_neg hmem]
            split
            · exact hr0
            · exact hp f'

/-! ### Pairing up the excess large goods -/

/-- **The filling procedure with pairing.**  If there are `t` large goods in excess of the number
of parts, `t` of the parts are made of *two* large goods each: such a part is pure and acceptable,
since a large good is worth at least `ε`.  Each such part may cost as much as `4ε` — more than the
`μ = 3ε` a part is allowed in the accounting of `fill_exists` — which is why the hypothesis asks
for `t·ε` of extra value.  This is the manuscript's step "if `|L₀| ≥ 2n₀` … create
`t = |L₀| − n₀ − 1` acceptable pure bundles, each containing two goods from `L₀`". -/
theorem fill_exists_pairs (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (t m : ℕ) (A C S : Finset G) (d r : ℝ) (f₀ : Option G),
      (∀ g ∈ A, ε ≤ vbar w p g) → (∀ g ∈ A, vbar w p g ≤ 2 * ε) →
      (∀ g ∈ C, vbar w p g ≤ ε) →
      (∀ g ∈ S, ε ≤ p g) → (∀ g ∈ S, vbar w p g = p g) →
      Disjoint A C → Disjoint A S → Disjoint C S →
      0 ≤ d → (r = 0 ∨ ε ≤ r) →
      (∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f) →
      (f₀ = none → r = 0) →
      A.card ≤ m + 1 + t → (A.card = m + 1 + t ∨ (S = ∅ ∧ r = 0)) →
      (m : ℝ) * (3 * ε) + 2 * ε + (t : ℝ) * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r →
      Nonempty (FillOut w p ε (m + 1) (A ∪ C ∪ S) d r f₀) := by
  classical
  intro t
  induction t with
  | zero =>
    intro m A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n hcard hseed hbud
    exact fill_exists w p hp hε m A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n
      (by omega) (by simpa using hseed) (by push_cast at hbud ⊢; linarith)
  | succ t ih =>
    intro m A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n hcard hseed hbud
    have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
    have hbud' : (m : ℝ) * (3 * ε) + 2 * ε + (t : ℝ) * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r := by
      push_cast at hbud
      nlinarith
    by_cases hm : m = 0
    · subst hm
      refine fill_one w p hp hε A C S d r f₀ hS2 hAC hAS hCS hd hr hf₀ hf₀n ?_
      push_cast at hbud
      nlinarith [Nat.cast_nonneg (α := ℝ) t]
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      by_cases hA2card : 2 ≤ A.card
      · -- pair up two large goods into one pure part
        obtain ⟨e₁, he₁⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨e₂, he₂⟩ : (A.erase e₁).Nonempty := by
          refine Finset.card_pos.mp ?_
          rw [Finset.card_erase_of_mem he₁]; omega
        have he₂A : e₂ ∈ A := Finset.mem_of_mem_erase he₂
        have hne : e₂ ≠ e₁ := Finset.ne_of_mem_erase he₂
        set A' : Finset G := (A.erase e₁).erase e₂ with hA'def
        have hA'card : A'.card = A.card - 2 := by
          rw [hA'def, Finset.card_erase_of_mem he₂, Finset.card_erase_of_mem he₁]
          omega
        have hAsum : (∑ g ∈ A, vbar w p g)
            = vbar w p e₁ + vbar w p e₂ + ∑ g ∈ A', vbar w p g := by
          rw [hA'def, show vbar w p e₁ + vbar w p e₂
                + ∑ g ∈ (A.erase e₁).erase e₂, vbar w p g
              = vbar w p e₁ + (vbar w p e₂ + ∑ g ∈ (A.erase e₁).erase e₂, vbar w p g) from by ring,
            Finset.add_sum_erase _ _ he₂, Finset.add_sum_erase _ _ he₁]
        have hrec := ih m A' C S d r f₀
          (fun g hg => hA1 g (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
          (fun g hg => hA2 g (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
          hC1 hS1 hS2
          (Finset.disjoint_of_subset_left
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hAC)
          (Finset.disjoint_of_subset_left
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hAS)
          hCS hd hr
          (fun f hf => ⟨fun hc => (hf₀ f hf).1
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)),
            (hf₀ f hf).2.1, (hf₀ f hf).2.2.1, (hf₀ f hf).2.2.2.1, (hf₀ f hf).2.2.2.2⟩)
          hf₀n (by omega)
          (by
            rcases hseed with h | h
            · left; omega
            · right; exact h)
          (by
            have h1 : vbar w p e₁ ≤ 2 * ε := hA2 e₁ he₁
            have h2 : vbar w p e₂ ≤ 2 * ε := hA2 e₂ he₂A
            rw [hAsum] at hbud
            push_cast at hbud ⊢
            linarith)
        obtain ⟨F⟩ := hrec
        refine fillout_snoc w p ε F ?_ (fun f hf => Finset.mem_union_right _ (by simp [hf]))
          {e₁, e₂} none 0 0 ?_ ?_ le_rfl le_rfl (by linarith) ?_ (Or.inl rfl)
          (fun h => absurd rfl h) (fun h => absurd rfl h) (fun _ => rfl)
          (fun f hf => absurd hf (by simp)) ?_
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
          · exact Finset.mem_union_right _ hx
        · intro x hx
          have hxe : x = e₁ ∨ x = e₂ := by simpa using hx
          rcases hxe with rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ he₁)
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ he₂A)
        · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          have hxe : x = e₁ ∨ x = e₂ := by simpa using hx
          have hxA : x ∈ A := by rcases hxe with rfl | rfl; exacts [he₁, he₂A]
          simp only [Option.toFinset_none, Finset.union_empty] at hx'
          rcases Finset.mem_union.mp hx' with hx' | hx'
          · rcases Finset.mem_union.mp hx' with hx' | hx'
            · rcases Finset.mem_union.mp hx' with hx' | hx'
              · rcases hxe with rfl | rfl
                · exact (Finset.notMem_erase _ _) (Finset.mem_of_mem_erase hx')
                · exact (Finset.notMem_erase _ _) hx'
              · exact Finset.disjoint_left.mp hAC hxA hx'
            · exact Finset.disjoint_left.mp hAS hxA hx'
          · exact (hf₀ x (Option.mem_toFinset.mp hx')).1 hxA
        · have h1 : ε ≤ vbar w p e₁ := hA1 e₁ he₁
          have h2 : ε ≤ vbar w p e₂ := hA1 e₂ he₂A
          have hpair : vbarSum w p {e₁, e₂} = vbar w p e₁ + vbar w p e₂ := by
            simp [vbarSum, Finset.sum_pair (Ne.symm hne)]
          rw [hpair]
          linarith
        · intro f
          simp only [reduceCtorEq, if_false, zero_add]
          by_cases hmem : f ∈ F.sell
          · rw [if_pos hmem]
          · rw [if_neg hmem]
            split
            · exact hr0
            · exact hp f
      · -- fewer than two large goods: no pairing is needed
        refine ih (m + 1) A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n
          (by omega) ?_ hbud'
        rcases hseed with h | h
        · omega
        · exact Or.inr h

/-! ### Proposition 6 -/

/-- **Proposition 6.**  If the available resources split into large goods `A` (worth between
`μ/3 = (1−ρ)μ` and `2μ/3 = ρμ`), cheap goods `C` (worth at most `μ/3`) and goods `S` that the
agent intends to sell (of price at least `μ/3`), if there are no more large goods than parts, and
if the value at our disposal is at least `(k−1)μ + ρμ`, then a canonical partition into `k` parts
exists.

The bound `(k−1)μ + ρμ` is the manuscript's "total value at our disposal is at least
`(n′+1−2ρ)MMSᵢ`" after the unification of the two cases `|L′| ≤ n′` and `|L′| = n′+1`: each of the
`k−1` ordinary parts costs at most `μ`, and the special part needs `ρμ`. -/
theorem exists_canonical_of_large_pairs (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {μ : ℝ} (hμ : 0 ≤ μ)
    {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ} (hD : 0 ≤ D) {A C S : Finset G}
    (hRdef : R = A ∪ C ∪ S)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hA1 : ∀ g ∈ A, μ / 3 ≤ vbar w p g) (hsmall : ∀ g ∈ R, vbar w p g ≤ 2 * μ / 3)
    (hC1 : ∀ g ∈ C, vbar w p g ≤ μ / 3)
    (hS1 : ∀ g ∈ S, μ / 3 ≤ p g) (hS2 : ∀ g ∈ S, w g ≤ p g)
    {t : ℕ} (hcard : A.card ≤ k + t)
    (hbud : ((k : ℝ) - 1) * μ + 2 * μ / 3 + (t : ℝ) * (μ / 3)
      ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + D + ∑ g ∈ S, p g) :
    Nonempty (Canonical w p μ (2 * μ / 3) k R D) := by
  classical
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  set ε : ℝ := μ / 3 with hεdef
  have hε : 0 ≤ ε := by simp only [hεdef]; linarith
  have hvbS : ∀ g ∈ S, vbar w p g = p g := by
    intro g hg; exact max_eq_left (hS2 g hg)
  -- move goods of `S` into the large goods until every part has one, or nothing is left to sell
  obtain ⟨S₁, hS₁sub, hS₁card⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := min (k + t - A.card) S.card)
      (le_trans (min_le_right _ _) le_rfl)
  set A' : Finset G := A ∪ S₁ with hA'def
  set S' : Finset G := S \ S₁ with hS'def
  have hA'S₁ : Disjoint A S₁ := Finset.disjoint_of_subset_right hS₁sub hAS
  have hA'card : A'.card = A.card + min (k + t - A.card) S.card := by
    rw [hA'def, Finset.card_union_of_disjoint hA'S₁, hS₁card]
  have hA'le : A'.card ≤ k + t := by
    rw [hA'card]; omega
  have hA'seed : A'.card = k + t ∨ S' = ∅ := by
    rcases le_total (k + t - A.card) S.card with h | h
    · left; rw [hA'card, min_eq_left h]; omega
    · right
      have : S₁ = S := Finset.eq_of_subset_of_card_le hS₁sub (by rw [hS₁card, min_eq_right h])
      simp [hS'def, this]
  have hRA' : A' ∪ C ∪ S' ⊆ R := by
    intro x hx
    rw [hRdef]
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
        · exact Finset.mem_union_right _ (hS₁sub hx)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hx).1
  have hSsplit : (∑ g ∈ S₁, p g) + (∑ g ∈ S', p g) = ∑ g ∈ S, p g := by
    rw [hS'def, Finset.sum_sdiff_eq_sub hS₁sub]; ring
  have hA'sum : (∑ g ∈ A', vbar w p g) = (∑ g ∈ A, vbar w p g) + ∑ g ∈ S₁, p g := by
    rw [hA'def, Finset.sum_union hA'S₁]
    congr 1
    exact Finset.sum_congr rfl (fun g hg => hvbS g (hS₁sub hg))
  -- run the filling procedure
  obtain ⟨F⟩ := fill_exists_pairs w p hp hε t (k - 1) A' C S' D 0 none
    (by
      intro g hg
      rcases Finset.mem_union.mp hg with hg | hg
      · exact hA1 g hg
      · rw [hvbS g (hS₁sub hg)]; exact hS1 g (hS₁sub hg))
    (by
      intro g hg
      have : g ∈ R := hRA' (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
      have := hsmall g this
      simp only [hεdef]; linarith)
    (by intro g hg; simpa [hεdef] using hC1 g hg)
    (fun g hg => hS1 g (Finset.mem_sdiff.mp hg).1)
    (fun g hg => hvbS g (Finset.mem_sdiff.mp hg).1)
    (Finset.disjoint_union_left.mpr ⟨hAC, Finset.disjoint_of_subset_left hS₁sub hCS.symm⟩)
    (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_of_subset_right Finset.sdiff_subset hAS,
      Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx)⟩)
    (Finset.disjoint_of_subset_right Finset.sdiff_subset hCS)
    hD (Or.inl rfl) (by simp) (fun _ => rfl)
    (by omega)
    (by
      rcases hA'seed with h | h
      · left; omega
      · right; exact ⟨h, rfl⟩)
    (by
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (1 : ℕ) ≤ k := hk
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast, hA'sum]
      simp only [hεdef] at hbud ⊢
      have h3 : (3 : ℝ) * (μ / 3) = μ := by ring
      rw [h3]
      linarith [hbud, hSsplit])
  -- package the result
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at F
  refine ⟨{ goods := fun j => F.goods (j : ℕ)
            sell := F.sell
            src := fun j => F.src (j : ℕ)
            dcash := fun j => F.dcash (j : ℕ)
            scash := fun j => F.scash (j : ℕ)
            goods_subset := fun j => (F.goods_subset j).trans hRA'
            goods_disj := ?_
            sell_subset := ?_
            sell_disj := fun j => F.sell_disj _
            src_mem := fun j f hf => F.src_mem _ f hf
            dcash_nonneg := fun j => F.dcash_nonneg _
            scash_nonneg := fun j => F.scash_nonneg _
            dcash_sum := ?_
            scash_sum := ?_
            scash_zero := fun j hj => F.scash_zero _ hj
            price_large := ?_
            acceptable := ?_
            pure_or_singleton := ?_
            singleton_dcash := ?_
            singleton_cond := ?_ }⟩
  · intro j j' hjj
    exact F.goods_disj _ _ (fun h => hjj (Fin.val_injective h))
  · intro x hx
    have hx' := F.sell_subset hx
    simp only [Option.toFinset_none, Finset.union_empty] at hx'
    exact hRA' hx'
  · rw [Fin.sum_univ_eq_sum_range (fun j => F.dcash j) k]
    exact F.dcash_sum
  · intro f _
    have h1 : ∑ j ∈ Finset.univ.filter (fun j : Fin k => F.src (j : ℕ) = some f),
          F.scash (j : ℕ)
        = ∑ j ∈ (Finset.range k).filter (fun j => F.src j = some f), F.scash j := by
      rw [Finset.sum_filter, Finset.sum_filter,
        Fin.sum_univ_eq_sum_range (fun j => if F.src j = some f then F.scash j else 0) k]
    rw [h1]
    simpa using F.scash_sum f
  · intro f hf
    have := F.price_large f hf
    simp only [hεdef] at this
    linarith
  · intro j
    have := F.acceptable (j : ℕ) j.isLt
    simp only [hεdef] at this
    linarith
  · intro j hj
    exact F.pure_or_singleton _ (by simpa using fun h => hj (Fin.val_injective (by simpa using h)))
      j.isLt
  · intro j hj
    exact F.singleton_dcash _ (by simpa using fun h => hj (Fin.val_injective (by simpa using h)))
  · intro j hj hsrc e he f hf
    have h1 := F.singleton_large (j : ℕ)
      (by simpa using fun h => hj (Fin.val_injective (by simpa using h))) hsrc e he
    have h2 := F.price_large f hf
    simp only [hεdef] at h1 h2
    linarith

/-- **Proposition 6**, the case with no excess large goods (`t = 0`): if there are no more large
goods than parts and the value at our disposal is at least `(k−1)μ + ρμ`, a canonical partition
into `k` parts exists. -/
theorem exists_canonical_of_few_large (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {μ : ℝ} (hμ : 0 ≤ μ)
    {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ} (hD : 0 ≤ D) {A C S : Finset G}
    (hRdef : R = A ∪ C ∪ S)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hA1 : ∀ g ∈ A, μ / 3 ≤ vbar w p g) (hsmall : ∀ g ∈ R, vbar w p g ≤ 2 * μ / 3)
    (hC1 : ∀ g ∈ C, vbar w p g ≤ μ / 3)
    (hS1 : ∀ g ∈ S, μ / 3 ≤ p g) (hS2 : ∀ g ∈ S, w g ≤ p g)
    (hcard : A.card ≤ k)
    (hbud : ((k : ℝ) - 1) * μ + 2 * μ / 3
      ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + D + ∑ g ∈ S, p g) :
    Nonempty (Canonical w p μ (2 * μ / 3) k R D) :=
  exists_canonical_of_large_pairs w p hp hμ hD hRdef hAC hAS hCS hA1 hsmall hC1 hS1 hS2
    (t := 0) (by omega) (by simpa using hbud)

end FairSelling
