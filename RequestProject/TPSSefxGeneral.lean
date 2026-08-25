import Mathlib
import RequestProject.Selling
import RequestProject.EpsEnvy
import RequestProject.LemmaEleven
import RequestProject.TPSApprox
import RequestProject.TPSCompute
import RequestProject.TPSSefx

/-!
# The general (priced) case of Theorem 2, SEFX half: the algorithmic skeleton

`RequestProject/TPSSefxZero.lean` proves the second half of Theorem 2 outright for instances in
which no good carries a price.  This file sets up the corresponding machinery for the *general*
case, in which goods may be sold and money changes hands, and reduces the theorem to a single
local statement — the *improvement step*, which is the content of the manuscript's Algorithm 6.

The reduction proved here is unconditional: `exists_eps_TPS_CSafeU_of_step` takes the improvement
step as an explicit hypothesis and derives the `ε`-approximate form of Theorem 2 from it, and
`exists_TPS_SEFX_of_step` then passes to the limit with Lemma 11.  Nothing in this file is left
as a `sorry`; the improvement step itself is proved, after a long detour through the per-good
ledger of `RequestProject/TPSSefxPot.lean` (see `ISSUES_TPS_SEFX.md` and `ISSUES_THEOREM2.md`
for a detailed account of the obstacles that detour had to overcome).

## The state of the algorithm

A `Stage` records which agents have already been served, the bundle of goods and the amount of
cash each of them holds, which goods have been sold, and how much of the sale proceeds is still
unallocated (`bank`).  A stage is `Good` when

* the bookkeeping is consistent (bundles are pairwise disjoint and disjoint from the sold goods,
  cash is non-negative, and cash plus bank equals the total sale proceeds);
* every served agent reaches its threshold `τ i = n/(2n−1)·TPS i` (`share`);
* every bundle is `ε`-*safe* for every agent, measured against the agent's *guarantee* — its own
  current utility if it is served, and its threshold if it is not (`safe`).  Safety is the
  conceptual form of the `ε`-SEFX condition: either exact envy-freeness, or the envied bundle
  carries no money, is kept in full by its owner, and is not envied up to any single good;
* the goods that are still unallocated, together with the bank, are worth at least
  `(2m−1)·τ j` to every unserved agent `j`, where `m` is the number of unserved agents
  (`counting`).  This is the invariant of the manuscript's Algorithm 4, and it is what allows
  the next agent to be served.

The last three conditions are exactly the invariants the manuscript maintains.  Because the
guarantee of a served agent is its own utility, and utilities never decrease, safety at any
moment survives all later steps; when every agent is served, the guarantees *are* the utilities
and safety *is* `ε`-SEFX (`csafeU_of_full`).

## The improvement step

Nothing in the model forces the set of sold goods to grow along the process: a successor stage
may perfectly well *un-sell* a good, which is the manuscript's `Unshrink` operation.  That
freedom is what makes the last invariant maintainable at all.

`ImprovementStep` says: from a good stage in which some agent is still unserved one can reach
another good stage in which either one more agent is served, or the total utility has gone up by
at least `ε`.  Total utility is bounded, so this cannot go on for ever; `descent` turns that into
a full allocation.  This is the exact point at which the manuscript's argument has to be made
precise, and where its proof is incomplete.
-/

open scoped BigOperators

namespace FairSelling

namespace GeneralTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The conceptual safety condition, utility form -/

/-- The conceptual form of the `ε`-`SEFXu` condition for the pair `(i, j)`: the same disjunction
as `CSafe`, but with the tolerance `ε` present also in the envy-free disjunct.  This is the form
that the algorithm can actually maintain; see `ISSUES_TPS_SEFX.md`. -/
def CSafeU (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (A : Fin n → Finset G) (q : Fin n → ℝ)
    (i j : Fin n) : Prop :=
  (vbarSum (v i) p (A i) + q i + eps ≥ vbarSum (v i) p (A j) + q j) ∨
  (q j = 0 ∧ (∀ g ∈ A j, p g ≤ v j g) ∧
    ∀ g ∈ A j, vbarSum (v i) p (A i) + q i + eps ≥ vbarSum (v i) p (A j \ {g}) + p g)

omit [Fintype G] in
/-- **Conceptual safety realizes `ε`-`SEFXu`.** -/
theorem epsSEFXu_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hsafe : ∀ i j, CSafeU v p eps A q i j) :
    epsSEFXu v p eps (unifiedOutcome v p A F q) := by
  classical
  intro i j
  set o := unifiedOutcome v p A F q with ho
  have hlhs : vbarSum (v i) p (o.kept i) + o.money i = vbarSum (v i) p (A i) + q i :=
    lhs_unifiedOutcome v p A F q i
  have hrhs : vbarSum (v i) p (o.kept j) + o.money j ≤ vbarSum (v i) p (A j) + q j :=
    rhs_unifiedOutcome_le v p A F q i j
  refine ⟨fun _ => ?_, fun g hg => ?_⟩
  · rcases hsafe i j with hEF | ⟨hqj, hkeep, _⟩
    · rw [hlhs]; linarith
    · -- an agent that keeps its whole bundle and banks nothing receives no money
      have hmz : o.money j = 0 := by
        simp only [ho, unifiedOutcome]
        have hempty : (A j).filter (fun g => v j g < p g) = ∅ :=
          Finset.filter_false_of_mem (fun g hg => not_lt.mpr (hkeep g hg))
        rw [hempty, hqj]; simp
      rw [hlhs, hmz]
      have : vbarSum (v i) p (o.kept j) ≤ vbarSum (v i) p (A j) + q j := by
        have := hrhs; rw [hmz] at this; linarith
      rw [hqj] at this
      linarith
  · -- the up-to-any-good clause
    have hsub : o.kept j ⊆ A j := by
      simp only [ho, unifiedOutcome]
      exact Finset.filter_subset _ _
    rcases hsafe i j with hEF | ⟨hqj, hkeep, hX⟩
    · have hsplit : vbarSum (v i) p (o.kept j)
          = vbarSum (v i) p (o.kept j \ {g}) + vbar (v i) p g :=
        vbarSum_sdiff_singleton hg
      have hpg : p g ≤ vbar (v i) p g := le_max_left _ _
      rw [hlhs]
      linarith
    · -- the owner keeps everything, so its kept bundle is its whole bundle
      have hkept : o.kept j = A j := by
        simp only [ho, unifiedOutcome]
        exact Finset.filter_true_of_mem (fun x hx => not_lt.mpr (hkeep x hx))
      have hmz : o.money j = 0 := by
        simp only [ho, unifiedOutcome]
        have hempty : (A j).filter (fun g => v j g < p g) = ∅ :=
          Finset.filter_false_of_mem (fun x hx => not_lt.mpr (hkeep x hx))
        rw [hempty, hqj]; simp
      rw [hlhs, hmz, hkept]
      rw [hkept] at hg
      have := hX g hg
      linarith

/-! ### Thresholds -/

/-- The threshold `τ i = n/(2n−1)·TPS i`. -/
noncomputable def thr (v : Fin n → G → ℝ) (p : G → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p

omit [DecidableEq G] in
theorem thr_nonneg (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (i : Fin n) :
    0 ≤ thr v p i := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (TPS_nonneg (v i) p hp)

/-! ### Stages -/

/-- A stage of the allocation process. -/
structure Stage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The bundle of goods held by each agent. -/
  bundle : Fin n → Finset G
  /-- The goods that have been sold. -/
  soldSet : Finset G
  /-- The sale proceeds held by each agent. -/
  cash : Fin n → ℝ
  /-- The sale proceeds that are not yet allocated. -/
  bank : ℝ

namespace Stage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- The goods that are neither sold nor allocated. -/
def pool (s : Stage G n) : Finset G :=
  Finset.univ \ (s.soldSet ∪ Finset.univ.biUnion s.bundle)

/-- The *guarantee* of agent `j`: its current utility if it is served, its threshold if not. -/
noncomputable def guar (s : Stage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j else thr v p j

/-- The bundle of agent `i` is `ε`-safe for agent `j`. -/
def Safe (s : Stage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.guar v p j + eps) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.guar v p j + eps)

/-- The total utility handed out so far. -/
noncomputable def total (s : Stage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)

/-- A *good* stage: consistent bookkeeping, every served agent above its threshold, every bundle
safe, and enough value left for the unserved agents. -/
def Good (s : Stage G n) : Prop :=
  (∀ i, i ∉ s.served → s.bundle i = ∅ ∧ s.cash i = 0) ∧
  (∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)) ∧
  (∀ i, Disjoint s.soldSet (s.bundle i)) ∧
  (∀ i, 0 ≤ s.cash i) ∧ 0 ≤ s.bank ∧
  ((∑ i, s.cash i) + s.bank = ∑ g ∈ s.soldSet, p g) ∧
  (∀ i ∈ s.served, thr v p i ≤ vbarSum (v i) p (s.bundle i) + s.cash i) ∧
  (∀ i ∈ s.served, ∀ j, s.Safe v p eps i j) ∧
  (∀ j, j ∉ s.served → (2 * ((n : ℝ) - s.served.card) - 1) * thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank)

end Stage

/-! ### The empty stage -/

/-- The stage in which nothing has happened yet. -/
def emptyStage (G : Type*) (n : ℕ) : Stage G n :=
  ⟨∅, fun _ => ∅, ∅, fun _ => 0, 0⟩

theorem pool_emptyStage : (emptyStage G n).pool = Finset.univ := by
  ext x
  simp [Stage.pool, emptyStage]

omit [DecidableEq G] in
theorem truncBundle_univ (w p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    truncBundle w p (TPS n w p) Finset.univ = (n : ℝ) * TPS n w p := by
  have hfix : truncSum n w p (TPS n w p) = TPS n w p := TPS_truncSum w p hp
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold truncSum at hfix
  unfold truncBundle trunc
  field_simp at hfix
  linarith

theorem Good_emptyStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) : (emptyStage G n).Good v p eps := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (2 * (n:ℝ) - 1) ≠ 0 := by intro h; linarith
  refine ⟨fun i _ => ⟨rfl, rfl⟩, fun i j _ => by simp [emptyStage],
    fun i => by simp [emptyStage], fun i => le_rfl, le_rfl, by simp [emptyStage], ?_, ?_, ?_⟩
  · intro i hi; exact absurd hi (by simp [emptyStage])
  · intro i hi; exact absurd hi (by simp [emptyStage])
  · intro j _
    rw [pool_emptyStage, truncBundle_univ (v j) p hn hp]
    show (2 * ((n : ℝ) - ((∅ : Finset (Fin n)).card : ℝ)) - 1) * thr v p j
      ≤ (n : ℝ) * TPS n (v j) p + (emptyStage G n).bank
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, emptyStage, add_zero]
    unfold thr
    rw [show (2 * (n : ℝ) - 1) * (((n : ℝ) / (2 * n - 1)) * TPS n (v j) p)
        = (n : ℝ) * TPS n (v j) p by field_simp]

/-! ### An upper bound on the total utility -/

/-- An upper bound for the total utility of any good stage. -/
noncomputable def totalBound (v : Fin n → G → ℝ) (p : G → ℝ) : ℝ :=
  (∑ i, vbarSum (v i) p Finset.univ) + ∑ g, p g

theorem total_le_bound (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hp : ∀ g, 0 ≤ p g)
    {s : Stage G n} (hs : s.Good v p eps) :
    s.total v p ≤ totalBound v p := by
  classical
  have h1 : ∀ i, vbarSum (v i) p (s.bundle i) ≤ vbarSum (v i) p Finset.univ := by
    intro i
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro g _ _
    exact le_trans (hp g) (le_max_left _ _)
  have h2 : (∑ i, s.cash i) ≤ ∑ g, p g := by
    have hb := hs.2.2.2.2.1
    have hsum := hs.2.2.2.2.2.1
    have : ∑ g ∈ s.soldSet, p g ≤ ∑ g, p g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun g _ _ => hp g)
    linarith
  unfold Stage.total totalBound
  rw [Finset.sum_add_distrib]
  exact add_le_add (Finset.sum_le_sum (fun i _ => h1 i)) h2

theorem total_nonneg (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hp : ∀ g, 0 ≤ p g)
    {s : Stage G n} (hs : s.Good v p eps) : 0 ≤ s.total v p := by
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hb : (0:ℝ) ≤ vbarSum (v i) p (s.bundle i) :=
    Finset.sum_nonneg (fun g _ => le_trans (hp g) (le_max_left _ _))
  linarith [hs.2.2.2.1 i]

/-! ### A full good stage is `ε`-safe -/

theorem csafeU_of_full (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) {s : Stage G n}
    (hs : s.Good v p eps) (hfull : s.served = Finset.univ) (i j : Fin n) :
    CSafeU v p eps s.bundle s.cash i j := by
  have hj : j ∈ s.served := by rw [hfull]; exact Finset.mem_univ j
  have hi : i ∈ s.served := by rw [hfull]; exact Finset.mem_univ i
  have hg : s.guar v p i = vbarSum (v i) p (s.bundle i) + s.cash i := by
    simp [Stage.guar, hi]
  have hsafe := hs.2.2.2.2.2.2.2.1 j hj i
  rw [Stage.Safe, hg] at hsafe
  rcases hsafe with h | ⟨h1, h2, h3⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨h1, h2, fun g hgm => by have := h3 g hgm; linarith⟩

/-! ### The improvement step -/

/-- **The improvement step**: from a good stage in which some agent is still unserved, one can
pass to a good stage in which either one more agent holds a bundle, or the total utility has
increased by at least `ε`.

This is the content of the manuscript's Algorithm 6 (bag filling together with the `Shrink`
stealing step).  It is *not* proved here; `ISSUES_TPS_SEFX.md` explains what goes wrong in the
manuscript's argument and what a proof would have to supply. -/
def ImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : Stage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : Stage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))

/-! ### The descent -/

section Descent

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- The inner descent: with the number of unserved agents fixed, the total utility increases by
at least `ε` at every step and is bounded, so the process cannot go on for ever. -/
theorem descent_inner (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : Stage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : Stage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
  intro b
  induction b with
  | zero =>
    intro s hs _ hb
    by_cases hfull : s.served = Finset.univ
    · exact ⟨s, hs, hfull⟩
    obtain ⟨s', hs', hprog⟩ := hstep s hs hfull
    rcases hprog with hcard | ⟨_, hval⟩
    · refine IH s' hs' ?_
      have h1 : s'.served.card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ s'.served)
      omega
    · exfalso
      have h1 := total_le_bound v p eps hp hs'
      simp only [Nat.cast_zero, zero_mul, sub_zero] at hb
      linarith
  | succ b ihb =>
    intro s hs hc hb
    by_cases hfull : s.served = Finset.univ
    · exact ⟨s, hs, hfull⟩
    obtain ⟨s', hs', hprog⟩ := hstep s hs hfull
    rcases hprog with hcard | ⟨hcard, hval⟩
    · refine IH s' hs' ?_
      have h1 : s'.served.card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ s'.served)
      omega
    · refine ihb s' hs' (by omega) ?_
      push_cast at hb ⊢
      linarith

/-- The descent: every good stage can be completed to a good stage in which every agent is
served. -/
theorem descent (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) :
    ∀ (c : ℕ) (s : Stage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
  intro c
  induction c with
  | zero =>
    intro s hs hc
    refine ⟨s, hs, ?_⟩
    have h1 : s.served.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ s.served)
    have : s.served.card = n := by omega
    exact Finset.eq_univ_of_card _ (by simpa using this)
  | succ c ihc =>
    intro s hs hc
    -- a number of steps that certainly exhausts the utility budget
    obtain ⟨b, hbb⟩ : ∃ b : ℕ, totalBound v p ≤ (b : ℝ) * eps := by
      obtain ⟨b, hb⟩ := exists_nat_gt (totalBound v p / eps)
      exact ⟨b, by rw [div_lt_iff₀ heps] at hb; linarith⟩
    refine descent_inner v p eps hp heps hstep c ihc b s hs hc ?_
    have := total_nonneg v p eps hp hs
    linarith

end Descent

/-! ### The reduction -/

/-- **Theorem 2 (SEFX half) reduces to the improvement step**, in its `ε`-approximate form.  If
the improvement step of the manuscript's Algorithm 6 can always be performed, then for every
`ε > 0` there is a conceptual assignment which gives every agent its threshold and in which no
agent `ε`-SEFX-envies another. -/
theorem exists_eps_TPS_CSafeU_of_step (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, CSafeU v p eps A q i j) := by
  obtain ⟨s, hs, hfull⟩ :=
    descent v p eps hp heps hstep n (emptyStage G n) (Good_emptyStage v p eps hn hp)
      (by simp [emptyStage])
  refine ⟨s.bundle, s.soldSet, s.cash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_, ?_⟩
  · have := hs.2.2.2.2.2.1
    have hb := hs.2.2.2.2.1
    linarith
  · intro i
    exact hs.2.2.2.2.2.2.1 i (by rw [hfull]; exact Finset.mem_univ i)
  · exact csafeU_of_full v p eps hs hfull

/-- **Theorem 2 (SEFX half) reduces to the improvement step.**  If for every `ε > 0` the
improvement step of Algorithm 6 can always be performed, then every allocation instance admits a
valid outcome that gives every agent at least `n/(2n−1)` of its truncated proportional share and
is SEFX. -/
theorem exists_TPS_SEFX_of_step (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g)
    (hstep : ∀ eps : ℝ, 0 < eps → ImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS_u v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :=
    exists_eps_TPS_CSafeU_of_step v p hn hp eps heps (hstep eps heps)
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, epsSEFXu_unifiedOutcome v p eps A F q hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  have hTPS : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
  nlinarith [hserve i]

/-! ### A fully proved special case: instances whose goods are pure money

At the opposite extreme from `RequestProject/TPSSefxZero.lean` (where no good has a price) lie
the instances in which no agent values any good above its market price.  There the whole
instance is money: selling everything and splitting the proceeds equally is envy free, and gives
every agent the full proportional share, which dominates `n/(2n−1)·TPS`. -/

/-- **Theorem 2 (SEFX half) for instances whose goods are pure money.**  If no agent values any
good above its price, then selling everything and splitting the proceeds equally is a valid
outcome that is envy free — hence SEFX — and gives every agent at least `n/(2n−1)` of its
truncated proportional share. -/
theorem exists_TPS_SEFX_of_money_goods (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hvp : ∀ i g, v i g ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  set M : ℝ := (∑ g, p g) / n with hM
  have hMnn : 0 ≤ M := div_nonneg (Finset.sum_nonneg fun g _ => hp g) (by linarith)
  refine ⟨⟨Finset.univ, fun _ => ∅, fun _ => M⟩, ⟨fun j => by simp, fun j k _ => by simp,
    fun j => hMnn, ?_⟩, ?_, ?_⟩
  · show (∑ _j : Fin n, M) ≤ ∑ g ∈ (Finset.univ : Finset G), p g
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hM,
      mul_div_cancel₀ _ hn0]
  · intro i
    -- the proportional share of a pure-money instance is `(∑ p)/n`
    have hPS : PS n (v i) p = M := by
      unfold PS
      rw [hM]
      congr 1
      exact Finset.sum_congr rfl fun g _ => max_eq_left (hvp i g)
    have hTPS : TPS n (v i) p ≤ M := hPS ▸ TPS_le_PS (n := n) (v i) p hp
    have hTPS0 : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
    have hratio : (n : ℝ) / (2 * n - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    show ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ (∑ _g ∈ (∅ : Finset G), v i _g) + M
    rw [Finset.sum_empty, zero_add]
    nlinarith
  · refine SEFX_of_EF ?_
    intro i j
    show vbarSum (v i) p ∅ + M ≥ vbarSum (v i) p ∅ + M
    exact le_rfl

end GeneralTPS

end FairSelling
