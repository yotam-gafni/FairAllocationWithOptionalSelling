import Mathlib
import RequestProject.TPSSefxCharge

/-!
# Serving one more agent

This file contains the *constructive* half of the improvement step of `TPSSefxCharge.lean`: given
a good charged stage, an agent `k` that is still unserved, and a package for it — a set `S` of
pool goods to keep, a set `S₀` of pool goods to sell, `q` in cash and `r` put aside — which

* reaches `k`'s threshold,
* is safe for every other agent, and
* costs every still unserved agent at most `2τ`,

handing the package to `k` produces a good charged stage with one more served agent
(`step_serve`).  All the bookkeeping — disjointness, the money equation, the monotonicity of the
requirements — is discharged here, so that the remaining work in the improvement step is purely
the *existence* of such a package.

Two lemmas isolate the two reasons a package can be affordable:

* `cost_le_of_footprint` — a *self-financed* package, one whose cash and reserve together are the
  proceeds of the goods it sells, costs exactly the truncated value of its footprint `S ∪ S₀`.
  This is the bag-filling case: the sale proceeds are put aside inside the package, and never
  handed to anybody else, which is what makes `Unshrink` work.
* `cost_le_of_single_good` — a package consisting of cash drawn from one single sold good, and
  charged with that good, costs at most the truncation level `TPSⱼ ≤ 2τⱼ`, whatever the price of
  the good.  This is the large-good case.
-/

open scoped BigOperators

namespace FairSelling

namespace ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Two affordability criteria -/

omit [Fintype G] in
/-- **A self-financed package costs its footprint.**  If the cash `q` and the money `r` put aside
add up to the proceeds of the sold part `S₀`, then the package's cost to an agent is exactly the
truncated value of the whole footprint `S ∪ S₀`. -/
lemma cost_le_of_footprint (w p : G → ℝ) (t : ℝ) (S S₀ : Finset G) (hdisj : Disjoint S S₀)
    (q r : ℝ) (hqr : q + r = ∑ g ∈ S₀, p g) :
    truncBundle w p t S + q + r + ∑ g ∈ S₀, saleLoss w p t g = truncBundle w p t (S ∪ S₀) := by
  rw [sum_saleLoss, truncBundle, truncBundle, truncBundle, Finset.sum_union hdisj]
  linarith

omit [Fintype G] [DecidableEq G] in
/-- **A package of cash drawn from one single good.**  An agent holding `q` in proceeds of the
single good `g`, and charged with that good's sale loss, costs at most the truncation level. -/
lemma cost_le_of_single_good (w p : G → ℝ) (t : ℝ) (g : G) (q : ℝ) (hqp : q ≤ p g) (hqt : q ≤ t) :
    truncBundle w p t ∅ + q + 0 + ∑ x ∈ ({g} : Finset G), saleLoss w p t x ≤ t := by
  simp only [truncBundle, Finset.sum_empty, Finset.sum_singleton, zero_add, add_zero]
  exact cash_add_saleLoss_le w p t g q hqp hqt

/-! ### The pool -/

namespace CStage

lemma disjoint_pool_soldSet (s : CStage G n) : Disjoint s.pool s.soldSet := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [CStage.pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inl hx')

lemma disjoint_pool_bundle (s : CStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [CStage.pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))

lemma disjoint_pool_charge (s : CStage G n) (i : Fin n) : Disjoint s.pool (s.charge i) :=
  Finset.disjoint_left.mpr (fun _ hx hx' =>
    Finset.disjoint_left.mp (disjoint_pool_soldSet s) hx
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))

end CStage

/-! ### Serving an unserved agent -/

open CStage in
/-- **Handing a package to an unserved agent.**  All the hypotheses are the invariants that the
new package has to satisfy on its own; everything else is bookkeeping. -/
theorem step_serve (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    {s : CStage G n} (hs : s.Good v p eps)
    {k : Fin n} (hk : k ∉ s.served)
    {S S₀ : Finset G} (hSpool : S ⊆ s.pool) (hS₀pool : S₀ ⊆ s.pool) (hSS₀ : Disjoint S S₀)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hbank : 0 ≤ s.bank + (∑ g ∈ S₀, p g) - q - r)
    (hclaim : GeneralTPS.thr v p k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k →
      (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : ∀ j, j ∉ s.served → j ≠ k →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : CStage G n, s'.Good v p eps ∧ s.served.card < s'.served.card := by
  classical
  obtain ⟨hempty, hbdisj, hcdisj, hcb, hcash0, hresv0, hbank0, hmoney, hshare, hsafe, hcost⟩ := hs
  obtain ⟨hkb, hkc, hkcash, hkresv⟩ := hempty k hk
  refine ⟨⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
      Function.update s.cash k q, Function.update s.resv k r,
      s.bank + (∑ g ∈ S₀, p g) - q - r⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals
    dsimp only
  · -- unserved agents hold nothing
    intro i hi
    have hik : i ≠ k := fun h => hi (by rw [h]; exact Finset.mem_insert_self _ _)
    have his : i ∉ s.served := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨h1, h2, h3, h4⟩ := hempty i his
    rw [Function.update_of_ne hik, Function.update_of_ne hik, Function.update_of_ne hik,
      Function.update_of_ne hik]
    exact ⟨h1, h2, h3, h4⟩
  · -- bundles are pairwise disjoint
    intro i j hij
    by_cases hi : i = k
    · rw [hi, Function.update_self, Function.update_of_ne (fun h => hij (hi.trans h.symm))]
      exact Finset.disjoint_of_subset_left hSpool (disjoint_pool_bundle s j)
    · by_cases hj : j = k
      · rw [hj, Function.update_self, Function.update_of_ne hi]
        exact (Finset.disjoint_of_subset_left hSpool (disjoint_pool_bundle s i)).symm
      · rw [Function.update_of_ne hi, Function.update_of_ne hj]; exact hbdisj i j hij
  · -- charges are pairwise disjoint
    intro i j hij
    by_cases hi : i = k
    · rw [hi, Function.update_self, Function.update_of_ne (fun h => hij (hi.trans h.symm))]
      exact Finset.disjoint_of_subset_left hS₀pool (disjoint_pool_charge s j)
    · by_cases hj : j = k
      · rw [hj, Function.update_self, Function.update_of_ne hi]
        exact (Finset.disjoint_of_subset_left hS₀pool (disjoint_pool_charge s i)).symm
      · rw [Function.update_of_ne hi, Function.update_of_ne hj]; exact hcdisj i j hij
  · -- charges are disjoint from bundles
    intro i j
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      by_cases hj : j = k
      · rw [hj, Function.update_self]; exact hSS₀.symm
      · rw [Function.update_of_ne hj]
        exact Finset.disjoint_of_subset_left hS₀pool (disjoint_pool_bundle s j)
    · rw [Function.update_of_ne hi]
      by_cases hj : j = k
      · rw [hj, Function.update_self]
        exact (Finset.disjoint_of_subset_left hSpool (disjoint_pool_charge s i)).symm
      · rw [Function.update_of_ne hj]; exact hcb i j
  · intro i
    by_cases hi : i = k
    · rw [hi, Function.update_self]; exact hq
    · rw [Function.update_of_ne hi]; exact hcash0 i
  · intro i
    by_cases hi : i = k
    · rw [hi, Function.update_self]; exact hr
    · rw [Function.update_of_ne hi]; exact hresv0 i
  · exact hbank
  · -- the money equation
    have hsold' : CStage.soldSet
        ⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
          Function.update s.cash k q, Function.update s.resv k r,
          s.bank + (∑ g ∈ S₀, p g) - q - r⟩ = s.soldSet ∪ S₀ := by
      ext x
      simp only [CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i = k
        · rw [h, Function.update_self] at hi; exact Or.inr hi
        · rw [Function.update_of_ne h] at hi; exact Or.inl ⟨i, hi⟩
      · rintro (⟨i, hi⟩ | hi)
        · refine ⟨i, ?_⟩
          by_cases h : i = k
          · rw [h, hkc] at hi; exact absurd hi (Finset.notMem_empty x)
          · rw [Function.update_of_ne h]; exact hi
        · exact ⟨k, by rw [Function.update_self]; exact hi⟩
    have hdisjSS₀ : Disjoint s.soldSet S₀ :=
      Finset.disjoint_left.mpr (fun x hx hx' =>
        Finset.disjoint_left.mp (disjoint_pool_soldSet s) (hS₀pool hx') hx)
    have h1 : ∑ i, Function.update s.cash k q i = (∑ i, s.cash i) + q := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
      have : ∑ i ∈ Finset.univ \ {k}, s.cash i = (∑ i, s.cash i) - s.cash k := by
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]; simp
      rw [this, hkcash]; ring
    have h2 : ∑ i, Function.update s.resv k r i = (∑ i, s.resv i) + r := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
      have : ∑ i ∈ Finset.univ \ {k}, s.resv i = (∑ i, s.resv i) - s.resv k := by
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]; simp
      rw [this, hkresv]; ring
    rw [h1, h2, hsold', Finset.sum_union hdisjSS₀]
    linarith
  · -- share
    intro i hi
    by_cases hik : i = k
    · rw [hik, Function.update_self, Function.update_self]; exact hclaim
    · rw [Function.update_of_ne hik, Function.update_of_ne hik]
      exact hshare i ((Finset.mem_insert.mp hi).resolve_left hik)
  · -- safety
    intro i hi j
    have hreqmono : s.req v p eps j ≤ CStage.req v p eps
        ⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
          Function.update s.cash k q, Function.update s.resv k r,
          s.bank + (∑ g ∈ S₀, p g) - q - r⟩ j := by
      by_cases hj : j = k
      · rw [hj]
        simp only [CStage.req, if_neg hk, if_pos (Finset.mem_insert_self k s.served),
          Function.update_self]
        linarith [hclaim]
      · by_cases hjs : j ∈ s.served
        · have hmem : j ∈ insert k s.served := Finset.mem_insert_of_mem hjs
          simp only [CStage.req, if_pos hjs, if_pos hmem, Function.update_of_ne hj]
          exact le_rfl
        · have hmem : j ∉ insert k s.served := fun h =>
            hjs ((Finset.mem_insert.mp h).resolve_left hj)
          simp only [CStage.req, if_neg hjs, if_neg hmem]
          exact le_rfl
    simp only [CStage.CSafe]
    by_cases hik : i = k
    · rw [hik, Function.update_self, Function.update_self]
      by_cases hjk : j = k
      · left
        have hreq' : CStage.req v p eps
            ⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
              Function.update s.cash k q, Function.update s.resv k r,
              s.bank + (∑ g ∈ S₀, p g) - q - r⟩ j = vbarSum (v j) p S + q + eps := by
          rw [hjk]
          simp only [CStage.req, if_pos (Finset.mem_insert_self k s.served),
            Function.update_self]
        rw [hreq']
        linarith
      · rcases hsafenew j hjk with h | ⟨hq0, h⟩
        · exact Or.inl (le_trans h hreqmono)
        · exact Or.inr ⟨hq0, hkeep, fun g hg => le_trans (h g hg) hreqmono⟩
    · have his : i ∈ s.served := (Finset.mem_insert.mp hi).resolve_left hik
      rw [Function.update_of_ne hik, Function.update_of_ne hik]
      rcases hsafe i his j with h | ⟨h1, h2, h3⟩
      · exact Or.inl (le_trans h hreqmono)
      · exact Or.inr ⟨h1, h2, fun g hg => le_trans (h3 g hg) hreqmono⟩
  · -- cost
    intro i hi j hj
    have hjk : j ≠ k := fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _)
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    simp only [CStage.cost]
    by_cases hik : i = k
    · rw [hik, Function.update_self, Function.update_self, Function.update_self,
        Function.update_self]
      exact hcostnew j hjs hjk
    · have his : i ∈ s.served := (Finset.mem_insert.mp hi).resolve_left hik
      rw [Function.update_of_ne hik, Function.update_of_ne hik, Function.update_of_ne hik,
        Function.update_of_ne hik]
      exact hcost i his j hjs
  · -- one more agent is served
    rw [Finset.card_insert_of_notMem hk]
    omega

end ChargeTPS

end FairSelling
