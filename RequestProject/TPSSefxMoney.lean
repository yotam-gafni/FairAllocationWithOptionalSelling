import Mathlib
import RequestProject.Selling
import RequestProject.EpsEnvy
import RequestProject.LemmaEleven
import RequestProject.TPSApprox
import RequestProject.TPSCompute
import RequestProject.TPSSefx
import RequestProject.TPSSefxGeneral

/-!
# Theorem 2 (SEFX half) for instances of *goods and money*

This file proves, **without any unproved hypothesis**, the second half of the manuscript's
Theorem 2 for every instance in which each good is either

* **free**: it carries no price (`p g = 0`), or
* **liquid**: selling it loses nothing, in the sense that its truncated contribution
  `max{p(g), min{v_j(g), TPS_j}}` equals its price for *every* agent `j` — for instance because
  no agent values it above its market price.

That is `MoneyClass` below.  The class contains both special cases that were already known:
`p ≡ 0` (`RequestProject/TPSSefxZero.lean`) and "no agent values a good above its price"
(`exists_TPS_SEFX_of_money_goods`), and it is the exact class in which the two obstacles
documented in `ISSUES_TPS_SEFX.md` disappear:

* a liquid good may be sold and its proceeds banked without destroying anybody's budget, so the
  counting invariant of Algorithm 4 need not be *maintained* — it is **derived** from the safety
  of the bundles handed out so far (`counting`).  This is what makes the *stealing* step of
  Algorithm 6 harmless, which is the step at which the manuscript's accounting breaks down;
* the SEFX condition charges the price `p(g)` of the removed good, so the minimality argument
  that produces it has to be able to *sell* a good of the bundle it is shrinking; for a free good
  that charge is `0`, so plain minimality suffices.

## What is proved

`exists_TPS_SEFX_of_money_class`: for every instance of the class there is a valid outcome that
gives every agent at least `n/(2n−1)` of its truncated proportional share and is SEFX.

## The proof

All liquid goods are sold at the outset and their proceeds are banked; what remains is a pool of
free goods together with a pot of money.  A `Stage` (the structure of
`RequestProject/TPSSefxGeneral.lean`) is then improved step by step:

* `safe_cost` — a safe bundle costs an agent that is still unserved at most `2τ`, where
  `τ i = n/(2n−1)·TPS i`;
* `counting` — hence the goods still in the pool, plus the bank, are worth at least `(2m−1)τ` to
  every unserved agent, `m` being their number;
* `improvement` — so some sub-bundle of the pool together with a suitable amount of cash is
  *claimed*; a claimed configuration of minimal size, with the least amount of cash that still
  makes it claimed, is safe for everybody, and handing it to a claimant either serves a new agent
  or raises the total utility by `ε`;
* `descent`, `exists_full_stage` — the process stops, and a full stage is `ε`-SEFXu and gives
  every agent `τ i − ε`;
* `lemma11_TPS_u_add` then passes to the limit `ε → 0`.

The threshold used along the way is `τ i − ε` rather than `τ i`: the `ε` of the envy condition
propagates into the counting argument, and this is exactly the amount of slack needed to keep the
per-bundle cost at `2τ`.
-/

open scoped BigOperators

namespace FairSelling

namespace MoneyGoods

open GeneralTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The class of instances -/

open Classical in
/-- The goods that are sold at the outset: those carrying a positive price. -/
noncomputable def soldGoods (p : G → ℝ) : Finset G := Finset.univ.filter (fun g => p g ≠ 0)

omit [DecidableEq G] in
theorem mem_soldGoods {p : G → ℝ} {g : G} : g ∈ soldGoods p ↔ p g ≠ 0 := by
  classical
  simp [soldGoods]

omit [DecidableEq G] in
theorem price_eq_zero_of_notMem {p : G → ℝ} {g : G} (h : g ∉ soldGoods p) : p g = 0 := by
  by_contra hc
  exact h (mem_soldGoods.2 hc)

/-- **Instances of goods and money**: every good is either free or liquid (selling it loses
nothing, for every agent). -/
def MoneyClass (v : Fin n → G → ℝ) (p : G → ℝ) : Prop :=
  ∀ g, p g = 0 ∨ ∀ j, trunc (v j) p (TPS n (v j) p) g = p g

omit [DecidableEq G] in
/-- In an instance of the class, every good that is sold at the outset is liquid. -/
theorem trunc_eq_price_of_mem_soldGoods {v : Fin n → G → ℝ} {p : G → ℝ}
    (hclass : MoneyClass v p) {g : G} (hg : g ∈ soldGoods p) (j : Fin n) :
    trunc (v j) p (TPS n (v j) p) g = p g := by
  rcases hclass g with h | h
  · exact absurd h (mem_soldGoods.1 hg)
  · exact h j

/-! ### Stages -/

/-- The *guarantee* of agent `j`: its current utility if it is served, and the (slackened)
threshold `τ j − ε` if it is not. -/
noncomputable def guarM (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : Stage G n) (j : Fin n) :
    ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j else thr v p j - eps

/-- The bundle of agent `i` is `ε`-safe for agent `j`. -/
def SafeM (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : Stage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ guarM v p eps s j + eps) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ guarM v p eps s j + eps)

/-- A *good* stage: consistent bookkeeping, exactly the liquid goods sold, every served agent at
or above the slackened threshold, and every bundle safe for every agent.

Note that — unlike `GeneralTPS.Stage.Good` — no counting condition is imposed: in this class it is
a *consequence* of safety (`counting`). -/
def GoodM (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : Stage G n) : Prop :=
  (∀ i, i ∉ s.served → s.bundle i = ∅ ∧ s.cash i = 0) ∧
  (∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)) ∧
  (∀ i, Disjoint s.soldSet (s.bundle i)) ∧
  (∀ i, 0 ≤ s.cash i) ∧ 0 ≤ s.bank ∧
  ((∑ i, s.cash i) + s.bank = ∑ g ∈ s.soldSet, p g) ∧
  s.soldSet = soldGoods p ∧
  (∀ i ∈ s.served, thr v p i - eps ≤ vbarSum (v i) p (s.bundle i) + s.cash i) ∧
  (∀ i ∈ s.served, ∀ j, SafeM v p eps s i j)

/-! ### Elementary facts -/

omit [DecidableEq G] in
theorem thr_nonneg' (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    0 ≤ thr v p j := thr_nonneg v p hn hp j

omit [DecidableEq G] in
/-- The truncated proportional share is at most twice the threshold. -/
theorem TPS_le_two_thr (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g)
    (j : Fin n) : TPS n (v j) p ≤ 2 * thr v p j := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  have ht0 : 0 ≤ TPS n (v j) p := TPS_nonneg (v j) p hp
  have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) / (2 * n - 1)) := by
    rw [show (2 : ℝ) * ((n : ℝ) / (2 * n - 1)) = (2 * n) / (2 * n - 1) by ring,
      le_div_iff₀ hden]
    linarith
  show TPS n (v j) p ≤ 2 * (((n : ℝ) / (2 * n - 1)) * TPS n (v j) p)
  nlinarith

omit [DecidableEq G] in
theorem two_n_sub_one_thr (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (j : Fin n) :
    (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * TPS n (v j) p := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (2 * (n:ℝ) - 1) ≠ 0 := by intro h; linarith
  show (2 * (n : ℝ) - 1) * (((n : ℝ) / (2 * n - 1)) * TPS n (v j) p) = _
  field_simp

/-! ### A safe bundle is cheap for an unserved agent -/

/-- **A safe bundle costs an unserved agent at most `2τ`.**  This is the step at which the `ε` of
the envy condition is paid for by the slack in the threshold. -/
theorem safe_cost (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) {s : Stage G n} (hs : GoodM v p eps s)
    {i : Fin n} (hi : i ∈ s.served) {j : Fin n} (hj : j ∉ s.served) :
    truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i ≤ 2 * thr v p j := by
  classical
  have hthr0 : 0 ≤ thr v p j := thr_nonneg v p hn hp j
  have htle : TPS n (v j) p ≤ 2 * thr v p j := TPS_le_two_thr v p hn hp j
  have hguar : guarM v p eps s j = thr v p j - eps := by simp [guarM, hj]
  have hvbar0 : ∀ g : G, 0 ≤ vbar (v j) p g := fun g => le_trans (hp g) (le_max_left _ _)
  have hle : truncBundle (v j) p (TPS n (v j) p) (s.bundle i) ≤ vbarSum (v j) p (s.bundle i) :=
    truncBundle_le_vbarSum _ _ _ _
  rcases hs.2.2.2.2.2.2.2.2 i hi j with h | ⟨hc, _, h2⟩
  · rw [hguar] at h
    linarith
  · rw [hguar] at h2
    rw [hc, add_zero]
    set A := s.bundle i with hA
    rcases Finset.eq_empty_or_nonempty A with hempty | ⟨g, hg⟩
    · rw [hempty]
      simp only [truncBundle, Finset.sum_empty]
      linarith
    by_cases hsingle : A = {g}
    · have hg0 : p g ≤ thr v p j := by
        have := h2 g hg
        rw [hsingle] at this
        simp only [Finset.sdiff_self, vbarSum, Finset.sum_empty, zero_add] at this
        linarith
      rw [hsingle]
      simp only [truncBundle, Finset.sum_singleton, trunc]
      exact max_le (by linarith) (le_trans (min_le_right _ _) htle)
    · have hnsub : ¬ A ⊆ {g} := fun hsub =>
        hsingle (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hg))
      obtain ⟨h', hh', hhg⟩ := Finset.not_subset.mp hnsub
      have hhne : h' ≠ g := by simpa using hhg
      have hsplit : vbarSum (v j) p A = vbarSum (v j) p (A \ {g}) + vbar (v j) p g :=
        vbarSum_sdiff_singleton hg
      have hsafe_g : vbarSum (v j) p (A \ {g}) + p g ≤ thr v p j := by
        have := h2 g hg; linarith
      have hsafe_h : vbarSum (v j) p (A \ {h'}) + p h' ≤ thr v p j := by
        have := h2 h' hh'; linarith
      have hgh : g ∈ A \ {h'} := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hg, fun hc' => hhne (hc'.symm)⟩
      have hvg : vbar (v j) p g ≤ vbarSum (v j) p (A \ {h'}) :=
        Finset.single_le_sum (f := fun x => vbar (v j) p x) (fun x _ => hvbar0 x) hgh
      have hph : 0 ≤ p h' := hp h'
      have hpg : 0 ≤ p g := hp g
      linarith

/-! ### The counting argument, derived from safety -/

theorem counting (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hclass : MoneyClass v p)
    {s : Stage G n} (hs : GoodM v p eps s) {j : Fin n} (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank := by
  classical
  set t := TPS n (v j) p with ht
  set w : G → ℝ := trunc (v j) p t with hw
  set U : Finset G := s.soldSet ∪ Finset.univ.biUnion s.bundle with hU
  -- the total truncated value
  have htotal : ∑ g : G, w g = (n : ℝ) * t := by
    have := truncBundle_univ (v j) p hn hp
    simpa [truncBundle, hw, ht] using this
  have hsplit : (∑ g ∈ s.pool, w g) + ∑ g ∈ U, w g = ∑ g : G, w g := by
    have : U ⊆ (Finset.univ : Finset G) := Finset.subset_univ _
    simpa [Stage.pool, hU] using Finset.sum_sdiff (f := w) this
  -- the union splits into the sold goods and the bundles
  have hdisjSU : Disjoint s.soldSet (Finset.univ.biUnion s.bundle) := by
    refine Finset.disjoint_left.mpr (fun x hx hxb => ?_)
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hxb
    exact Finset.disjoint_left.mp (hs.2.2.1 i) hx hxi
  have hdisjb : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint s.bundle := by
    intro a _ b _ hab
    exact hs.2.1 a b hab
  have hUsum : ∑ g ∈ U, w g
      = (∑ g ∈ s.soldSet, w g) + ∑ i : Fin n, ∑ g ∈ s.bundle i, w g := by
    rw [hU, Finset.sum_union hdisjSU, Finset.sum_biUnion hdisjb]
  -- the sold goods are liquid
  have hsold : ∑ g ∈ s.soldSet, w g = ∑ g ∈ s.soldSet, p g := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    have hg' : g ∈ soldGoods p := by rwa [hs.2.2.2.2.2.2.1] at hg
    exact trunc_eq_price_of_mem_soldGoods hclass hg' j
  have hmoney : ∑ g ∈ s.soldSet, p g = (∑ i, s.cash i) + s.bank := hs.2.2.2.2.2.1.symm
  -- each bundle plus its cash costs at most `2τ`
  have hcost : ∀ i : Fin n, (∑ g ∈ s.bundle i, w g) + s.cash i
      ≤ if i ∈ s.served then 2 * thr v p j else 0 := by
    intro i
    by_cases hi : i ∈ s.served
    · simp only [hi, if_true]
      exact safe_cost v p eps hn hp hs hi hj
    · simp only [hi, if_false, (hs.1 i hi).1, (hs.1 i hi).2, Finset.sum_empty, add_zero, le_refl]
  have hcostsum : (∑ i : Fin n, ∑ g ∈ s.bundle i, w g) + ∑ i, s.cash i
      ≤ (s.served.card : ℝ) * (2 * thr v p j) := by
    have h1 : ∑ i : Fin n, ((∑ g ∈ s.bundle i, w g) + s.cash i)
        ≤ ∑ i : Fin n, if i ∈ s.served then 2 * thr v p j else 0 :=
      Finset.sum_le_sum (fun i _ => hcost i)
    have h2 : ∑ i : Fin n, (if i ∈ s.served then 2 * thr v p j else 0)
        = (s.served.card : ℝ) * (2 * thr v p j) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_add_distrib] at h1
    linarith [h1, h2.le, h2.ge]
  have hthr : (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * t :=
    two_n_sub_one_thr v p hn j
  have hpool : truncBundle (v j) p t s.pool = ∑ g ∈ s.pool, w g := rfl
  rw [hpool]
  have := hsplit
  rw [hUsum, hsold, hmoney, htotal] at this
  nlinarith [hcostsum, this, hthr]

end MoneyGoods

end FairSelling
