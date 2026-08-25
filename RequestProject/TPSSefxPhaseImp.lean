import Mathlib
import RequestProject.TPSSefxPhaseStep
import RequestProject.TPSSefxStep

/-!
# The improvement step of Algorithm 6, in the manuscript's phase structure

Algorithm 6 of the manuscript is a loop with three bodies, tried in this order:

1. the **large-good price loop**: while some available good `g` has a price above the threshold
   of some agent that is still unserved, `g` is sold and *part* of its proceeds — a slice cut by
   a moving knife — is handed out, the rest staying available for the other agents;
2. the **large-good value loop**: the same for a good that some unserved agent *values* above its
   threshold;
3. one step of **bag filling**: a bag is filled out of the pool until somebody claims it, and the
   bag is shrunk (`Shrink`) to a package nobody envies.

The two large-good loops allow *sharing*: the bundle they hand out is a single good, or a slice
of the proceeds of a single sold good, so that several agents may be served out of one sold good
and there are never more goods sold than agents allocated a bundle.  The bag-filling loop, on the
contrary, avoids sharing entirely: everything a bag sells is financed out of the bag itself.

This file carries out that case distinction for the phase-structured states of
`RequestProject/TPSSefxPhase.lean`.

* **`pshare_step`** — the large-good loops, with *sharing*.  A pool good `g` whose price is
  above twice the threshold of some unserved agent is sold, and the claimant receives the least
  slice `Qc(∅)` of the proceeds that makes somebody claim it; the rest stays in the bank, free
  for the other agents, so that several agents get served out of the one sold good.  The good is
  charged to the claimant, which from then on holds nothing but its slice `q ≤ p g`
  (`PStage.ShareOK`); by `ChargeTPS.cash_add_saleLoss_le` that package costs an unserved agent
  `j` at most `q + loss_j(g) ≤ TPS_j ≤ 2·τ_j`, however small the slice and however many agents
  share the good.  The step is **proved**.

* **`pmoney_step`** — the same moving knife for a set `F` of *pure* goods, which cost their
  seller nothing and are therefore charged to nobody.  `F = ∅` is allowed, and is the case in
  which the slice is paid for out of proceeds a *previous* sale left in the bank.  The step is
  **proved**, and `plarge_pure_step` specialises it to a good that is expensive for every
  unserved agent.

* **`pbagfill_step`** — the bag-filling loop.  `Shrink` (`CfgTPS.exists_min_adm` followed by
  `ChargeTPS.package_of_claimant`) produces a minimal admissible package out of the pool, and it
  is handed to its claimant, whose old package — if it had one — is released (`Unshrink`).
  Everything the new owner sells is financed out of its own package, so nothing is shared here.
  The step is **proved**; it needs the goods it bag-fills to be cheap (`p g ≤ 2·τⱼ` for every
  unserved `j`), which is exactly the negation of the entry condition of the large-good loops.

The one thing that is **not** proved is `PhaseTPS.pcarrier_reassign`
(`RequestProject/TPSSefxPhaseStep.lean`): the manuscript's `Unshrink` for an agent that is
re-allocated while it holds a slice of a shared good.  `ISSUES_THEOREM2.md` describes precisely
what is missing.
-/

open scoped BigOperators

namespace FairSelling

namespace PhaseTPS

open ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

section Step

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-! ### Preliminaries: requirements and feasibility of the pool -/

theorem preq_nonneg (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : PStage G n}
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j :=
  ChargeTPS.req_nonneg v p eps hn hp heps (PStage.good_toCStage v p eps hs) j

omit [DecidableEq G] in
theorem preq_eq_thr {s : PStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by
  simp [PStage.req, hj]

/-- **The pool is feasible**, for a phase-structured stage: this is the counting invariant of
Algorithm 4, which the charged bookkeeping derives from the local cost bound. -/
theorem pfeas_pool (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : PStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served) :
    CfgTPS.Feas v p (s.req v p eps) k0 s.bank s.pool ∅ := by
  have h := ChargeTPS.feas_pool v p eps hn hp (PStage.good_toCStage v p eps hs) (k0 := k0) hk0
  rwa [PStage.toCStage_pool] at h
/-! ### The large-good loops: the moving knife -/

/-- **The moving-knife step of Algorithm 6** — the two large-good loops.

A set `F` of *pure* pool goods is sold, and the claimant receives the least slice `Qc(∅)` of the
proceeds that makes somebody claim it, the rest staying in the bank, available to the other
agents.  This is the manuscript's moving knife, and it is the reason the loss to the agents that
are *not* served by the step is limited: selling a pure good costs nobody anything, and the
slice that is handed out is at most the threshold of every unserved agent.

The step is stated for an arbitrary set `F` of pure goods, and in particular covers

* `F = ∅` — the slice is paid for out of the free proceeds already in the bank, with nothing
  sold at all;
* `F` a single good — the manuscript's price loop for a good whose price already dominates the
  truncated contribution of every unserved agent (`plarge_pure_step` below).

Several agents may be served, one after another, out of the proceeds of a single sold good: this
is the *sharing* that the large-good loops allow, and it is harmless here because every bundle
handed out is a slice of the proceeds of a set of goods that cost their sellers nothing. -/
theorem pmoney_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) (k0 : Fin n)
    {F : Finset G} (hFpool : F ⊆ s.pool)
    (hFpure : ∀ g ∈ F, PureGood v p s.served g)
    (hafford : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.bank + ∑ g ∈ F, p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set q := CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) with hq
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 (∅ : Finset G)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have hqreq : ∀ m, q ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  have hq0 : 0 ≤ q := CfgTPS.Qc_nonneg v p (s.req v p eps) k0 _
  have hthr0 : ∀ j, 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp
  have hE : 0 ≤ s.cash k + s.resv k - ∑ x ∈ s.own k, p x := by
    have := hs.self_fin k; linarith
  have hpure' : ∀ x ∈ F, PureGood v p (insert k s.served) x :=
    fun x hx => PureGood.mono (Finset.subset_insert k s.served) (hFpure x hx)
  have hclaim' : s.req v p eps k ≤ vbarSum (v k) p ∅ + q := by simpa [vbarSum] using hclaim
  refine pstep_assign_any v p eps hcarrier hn hp heps hs (S := ∅) (S₀own := ∅) (S₀ext := F)
    (by simp) (by simp) hFpool
    (by simp) (by simp) (by simp) (q := q) (r := 0) hq0 le_rfl ?_ (by simpa using hq0)
    (Or.inl hpure') hclaim' (by simp) ?_ ?_
  · -- the slice is affordable
    simp only [Finset.sum_empty, add_zero]
    linarith
  · -- the slice is safe for everybody
    intro j _
    left
    simpa [vbarSum] using hqreq j
  · -- the slice costs every unserved agent at most its threshold
    intro j hj
    have hj' : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have h1 : q ≤ s.req v p eps j := hqreq j
    rw [preq_eq_thr v p eps hj'] at h1
    have := hthr0 j
    simp only [truncBundle, Finset.sum_empty, zero_add, add_zero]
    linarith

/-- **The price loop of Algorithm 6, for a good that is expensive for every unserved agent.**
Such a good is *pure*, so the moving-knife step applies to it: it is sold, the claimant receives
the least slice of the proceeds that makes somebody claim it, and the rest of the proceeds stays
in the bank, available to the other agents. -/
theorem plarge_pure_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k0 : Fin n} (hk0 : k0 ∉ s.served)
    {g : G} (hg : g ∈ s.pool)
    (hbig : ∀ j, j ∉ s.served → 2 * GeneralTPS.thr v p j < p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  have hpure : PureGood v p s.served g :=
    pureGood_of_TPS_le (fun j hj => by
      have h1 := ChargeTPS.TPS_le_two_thr v p hn hp j
      have h2 := hbig j hj
      linarith)
  refine pmoney_step v p eps hcarrier hn hp heps hs k0 (Finset.singleton_subset_iff.mpr hg)
    (fun x hx => by rwa [Finset.mem_singleton.mp hx]) ?_
  -- the slice is smaller than the price of the good
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have h1 : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.req v p eps k0 :=
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 k0
  rw [preq_eq_thr v p eps hk0] at h1
  have h2 := hbig k0 hk0
  have h3 := GeneralTPS.thr_nonneg v p hn hp k0
  have h4 := hs.bank_nonneg
  simp only [Finset.sum_singleton]
  linarith

/-! ### The bag-filling loop -/

/-- **The bag-filling step of Algorithm 6.**  When no pool good is expensive for an unserved
agent, the pool is filled into a bag, the bag is shrunk to a minimal admissible package, and the
package is handed to its claimant; if the claimant already holds a bundle, that bundle is
released first (`Unshrink`).  Everything the new owner sells is financed out of its own package —
the manuscript's *"sharing is avoided in the bag-filling loop"* — so the release is
unconditional. -/
theorem pbagfill_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    {P : Finset G} (hPpool : P ⊆ s.pool)
    (hfeas : CfgTPS.Feas v p (s.req v p eps) k0 s.bank P ∅)
    (hcheap : ∀ g ∈ P, ∀ j, j ∉ s.served → p g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  obtain ⟨S, S₀, hUP, hdisj, hadm, hmin⟩ :=
    CfgTPS.exists_min_adm v p (s.req v p eps) k0 s.bank P hp hfeas
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 S
  obtain ⟨S', S₀', q, hS'S, hS₀S₀', hfoot, hdisj', hq0, hqle, hclaim', hkeep, hsafe, hcosteq⟩ :=
    ChargeTPS.package_of_claimant v p (s.req v p eps) k0 s.bank hp hdisj hadm k hclaim
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have hbank : 0 ≤ s.bank := hs.bank_nonneg
  set A := ∑ x ∈ S₀', p x with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => hp x
  set r := max 0 (A - q) with hr
  have hr0 : 0 ≤ r := le_max_left _ _
  have hqr : q + r = max q A := by
    rcases le_or_gt A q with h | h
    · rw [hr, max_eq_left (by linarith : A - q ≤ 0), max_eq_left h, add_zero]
    · rw [hr, max_eq_right (by linarith : (0:ℝ) ≤ A - q), max_eq_right h.le]; ring
  have hS'P : S' ⊆ P :=
    Finset.Subset.trans (Finset.Subset.trans hS'S Finset.subset_union_left) hUP
  have hS₀'P : S₀' ⊆ P := fun x hx => hUP (hfoot ▸ Finset.mem_union_right S' hx)
  have hS'pool : S' ⊆ s.pool := Finset.Subset.trans hS'P hPpool
  have hS₀'pool : S₀' ⊆ s.pool := Finset.Subset.trans hS₀'P hPpool
  have hE : 0 ≤ s.cash k + s.resv k - ∑ x ∈ s.own k, p x := by
    have := hs.self_fin k; linarith
  refine pstep_assign_any v p eps hcarrier hn hp heps hs (S := S') (S₀own := S₀') (S₀ext := ∅)
    hS'pool hS₀'pool (by simp) hdisj' (by simp) (by simp) (q := q) (r := r) hq0 hr0 ?_ ?_
    (Or.inl (by simp)) hclaim' hkeep ?_ ?_
  · -- the package is affordable
    simp only [Finset.sum_empty, add_zero, ← hA]
    rw [hqr]
    rcases le_or_gt A q with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  · -- the sales are self-financed
    rw [hqr, ← hA]
    exact le_max_right _ _
  · -- the package is safe for everybody
    intro j _
    exact hsafe j
  · -- the cost bound
    intro j hj
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have hreqj : s.req v p eps j = GeneralTPS.thr v p j := preq_eq_thr v p eps hjs
    have hthrj : 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp j
    rcases le_or_gt A q with hAq | hAq
    · -- the claimant draws money from the bank: the package costs what `Shrink` guarantees
      have hr0' : r = 0 := by rw [hr, max_eq_left (by linarith : A - q ≤ 0)]
      have hcost := CfgTPS.cost_bound (w := v) (p := p) (req := s.req v p eps) (k0 := k0)
        (D := s.bank) (P := P) (S := S) (S₀ := S₀)
        (fun i => TPS n (v i) p) j hp hbank hreq0
        (by rw [hreqj]; exact ChargeTPS.thr_le_TPS v p hn hp j)
        (by rw [hreqj]; exact ChargeTPS.TPS_le_two_thr v p hn hp j)
        hUP hdisj hadm hmin
      rw [hreqj] at hcost
      have heq := hcosteq (TPS n (v j) p) (v j)
      rw [hr0']
      linarith
    · -- the claimant keeps the whole proceeds of what it sells: the package costs its whole
      -- truncated footprint
      have hr0' : r = A - q := by rw [hr, max_eq_right (by linarith : (0:ℝ) ≤ A - q)]
      have hloss : ∑ x ∈ S₀', saleLoss (v j) p (TPS n (v j) p) x
          = truncBundle (v j) p (TPS n (v j) p) S₀' - A := ChargeTPS.sum_saleLoss _ _ _ _
      have hsplit : truncBundle (v j) p (TPS n (v j) p) S'
          + truncBundle (v j) p (TPS n (v j) p) S₀'
          = truncBundle (v j) p (TPS n (v j) p) (S ∪ S₀) := by
        rw [← hfoot]
        exact (Finset.sum_union hdisj').symm
      have hgoal : truncBundle (v j) p (TPS n (v j) p) S' + q + r
          + ∑ x ∈ S₀', saleLoss (v j) p (TPS n (v j) p) x
          = truncBundle (v j) p (TPS n (v j) p) (S ∪ S₀) := by
        rw [hloss, hr0', ← hsplit]; ring
      rw [hgoal]
      rcases le_or_gt 2 (S ∪ S₀).card with hcard | hcard
      · have h2 := CfgTPS.truncBundle_add_le_two (w := v) (req := s.req v p eps) (k0 := k0)
          (fun i => TPS n (v i) p) j hp hbank hUP hmin hcard
        rw [hreqj] at h2
        linarith
      · -- the footprint is a single sold good, and pool goods are cheap
        have hS₀ne : S₀'.Nonempty := by
          rcases Finset.eq_empty_or_nonempty S₀' with he | he
          · exfalso; rw [he] at hA; simp only [Finset.sum_empty] at hA; rw [hA] at hAq; linarith
          · exact he
        obtain ⟨x, hx⟩ := hS₀ne
        have hxU : x ∈ S ∪ S₀ := hfoot ▸ Finset.mem_union_right S' hx
        have hcard1 : (S ∪ S₀).card = 1 := by
          have : 1 ≤ (S ∪ S₀).card := Finset.card_pos.mpr ⟨x, hxU⟩
          omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard1
        have hxy : x = y := by rw [hy] at hxU; simpa using hxU
        subst hxy
        have hxP : x ∈ P := hS₀'P hx
        have hpx : p x ≤ 2 * GeneralTPS.thr v p j := hcheap x hxP j hjs
        have htx : TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j :=
          ChargeTPS.TPS_le_two_thr v p hn hp j
        have h1 : trunc (v j) p (TPS n (v j) p) x ≤ max (p x) (TPS n (v j) p) :=
          trunc_le_max _ _ _ _
        rw [hy]
        simp only [truncBundle, Finset.sum_singleton]
        rcases max_cases (p x) (TPS n (v j) p) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;>
          linarith

/-! ### The price loop for a good that is not pure: sharing -/

/-- **The moving knife on a *shared* good** — the manuscript's price loop for a good whose price
exceeds the threshold of some unserved agent but which is *not* pure.

The good `g` is sold and the claimant receives the least slice `Qc(∅)` of the proceeds that
makes somebody claim it; the rest of the proceeds stays in the bank, free for the other agents,
so that several agents end up being served out of the one sold good.  This is the *sharing* the
manuscript allows in the large-good loops (and only there): every bundle handed out is a slice
of the proceeds of a **single** sold good, so there are never more goods sold than agents
allocated a bundle.

The good is charged to the claimant (`PStage.ShareOK`), which from then on holds nothing but its
slice `q ≤ p g`.  That is exactly what keeps the loss bounded for the agents that are *not*
served by the step: by `ChargeTPS.cash_add_saleLoss_le` the whole package costs an unserved
agent `j` at most `q + loss_j(g) ≤ TPS_j ≤ 2·τ_j`, however small the slice is and however many
agents share the good.

Sharing is only possible if the claimant is not *already* carrying a shared good; that case is
`pcarrier_reassign`, the one step of Algorithm 6 that is left unproved. -/
theorem pshare_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) (k0 : Fin n)
    {g : G} (hg : g ∈ s.pool)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set q := CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) with hq
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 (∅ : Finset G)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have hqreq : ∀ m, q ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  have hq0 : 0 ≤ q := CfgTPS.Qc_nonneg v p (s.req v p eps) k0 _
  have hE : 0 ≤ s.cash k + s.resv k - ∑ x ∈ s.own k, p x := by
    have := hs.self_fin k; linarith
  have hclaim' : s.req v p eps k ≤ vbarSum (v k) p ∅ + q := by simpa [vbarSum] using hclaim
  refine pstep_assign_any v p eps hcarrier hn hp heps hs (S := ∅) (S₀own := ∅) (S₀ext := {g})
    (by simp) (by simp) (Finset.singleton_subset_iff.mpr hg)
    (by simp) (by simp) (by simp) (q := q) (r := 0) hq0 le_rfl ?_ (by simpa using hq0)
    (Or.inr ⟨rfl, rfl, rfl, g, rfl, hqle⟩) hclaim' (by simp) ?_ ?_
  · -- the slice is affordable: it is cut out of the price of the good that is sold
    have hbank := hs.bank_nonneg
    simp only [Finset.sum_empty, Finset.sum_singleton, add_zero]
    linarith
  · -- the slice is safe for everybody
    intro j _
    left
    simpa [vbarSum] using hqreq j
  · -- the slice alone costs every unserved agent at most its threshold
    intro j hj
    have hj' : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have h1 : q ≤ s.req v p eps j := hqreq j
    rw [preq_eq_thr v p eps hj'] at h1
    have h2 := GeneralTPS.thr_nonneg v p hn hp j
    simp only [truncBundle, Finset.sum_empty, zero_add, add_zero]
    linarith

/-! ### Algorithm 6 -/

/-- **The improvement step of Algorithm 6**, split into the manuscript's cases, in the
manuscript's order.

1. *The large-good loops.*  If some good in the pool is expensive for an agent that is still
   unserved — its price is above twice that agent's threshold — the moving knife of
   `pshare_step` sells it and cuts the least slice of the proceeds that somebody claims, the
   rest staying in the bank for the other agents.  Every bundle handed out here is a slice of
   the proceeds of a *single* sold good, so several agents may be served out of one good and
   there are never more goods sold than agents allocated a bundle.  When the good happens to be
   *pure* this is `plarge_pure_step`, a special case of the moving knife `pmoney_step`, in which
   nothing is charged to anybody.

2. *The bag-filling loop.*  Otherwise no pool good is expensive for an unserved agent, and the
   whole pool can be bag-filled: it is feasible by the counting invariant (`pfeas_pool`), and
   `pbagfill_step` shrinks it to a package and hands it to its claimant, releasing the
   claimant's old package if it had one.  Nothing is shared here: everything the new owner sells
   is financed out of its own package. -/
theorem pimprovementStep (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) :
    PImprovementStep v p eps := by
  classical
  intro s hs hfull
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ s.served := by
    by_contra hcon
    push_neg at hcon
    exact hfull (Finset.eq_univ_of_forall hcon)
  by_cases hB : ∀ x ∈ s.pool, ∀ j, j ∉ s.served → p x ≤ 2 * GeneralTPS.thr v p j
  · -- the bag-filling loop
    exact pbagfill_step v p eps hcarrier hn hp heps hs (Finset.Subset.refl _)
      (pfeas_pool v p eps hn hp hs hk0) hB
  · -- the large-good loops
    push_neg at hB
    obtain ⟨g, hg, j0, hj0, hbig⟩ := hB
    -- the slice the claimant asks for is cut out of the price of the expensive good
    have hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ p g := by
      have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
      have h2 : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.req v p eps j0 :=
        CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 j0
      rw [preq_eq_thr v p eps hj0] at h2
      have h3 := GeneralTPS.thr_nonneg v p hn hp j0
      linarith
    exact pshare_step v p eps hcarrier hn hp heps hs k0 hg hqle

end Step

end PhaseTPS

end FairSelling
