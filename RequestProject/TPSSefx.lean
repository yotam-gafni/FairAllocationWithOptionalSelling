import Mathlib
import RequestProject.Selling
import RequestProject.EpsEnvy
import RequestProject.LemmaEleven
import RequestProject.TPSApprox
import RequestProject.ThreeAgents

/-!
# Theorem 2, second half: an `n/(2n−1)`-TPS allocation that is also SEFX

The manuscript's Theorem 2 has two halves.  The first one — *every allocation instance has an
`n/(2n−1)`-TPS allocation* — is `FairSelling.exists_TPS_approx` in
`RequestProject/TPSApprox.lean`.  This file is about the second half:

> Every allocation instance has an allocation that is both `n/(2n−1)`-TPS and SEFX.

The manuscript proves it (Appendix D.2) by running the bag-filling algorithm of Algorithm 4 with
an added *stealing* (`Shrink`) step, producing for every `ε > 0` a partial allocation that is
`n/(2n−1)`-TPS and `ε`-SEFX, and then letting `ε → 0` by Lemma 11 (`FairSelling.lemma11_TPS`).

## What this file contains

* the *conceptual* description of an allocation used throughout the manuscript's algorithms —
  a bundle `A i` of goods for each agent plus `q i` in banked sale proceeds, the goods `F` being
  force-sold to finance the proceeds — realized as an `Outcome` by `unifiedOutcome`, in which
  every agent sells exactly the goods of its bundle that are worth less to it than their price;
* `CSafe`, the conceptual form of the `ε`-SEFX condition, and `epsSEFX_unifiedOutcome`, the
  statement that a conceptually safe assignment realizes an `ε`-SEFX outcome;
* a record of the first, superseded attempt at the algorithmic core (the manuscript's
  Algorithm 6) through `CSafe`, and of the deduction of Theorem 2 (second half) from it.  The
  SEFX half of Theorem 2 is proved unconditionally as `FairSelling.theorem_two_SEFX` in
  `RequestProject/TPSSefxTheorem2.lean`, through the *unified* condition `CSafeU` of
  `RequestProject/TPSSefxGeneral.lean` and the per-good ledger of
  `RequestProject/TPSSefxPot.lean`.

Two points about the conceptual condition `CSafe` deserve emphasis, because they are what makes
the second half of Theorem 2 substantially harder than the first one, and they are not addressed
by the manuscript's proof.  Both are discussed at length in `ISSUES_TPS_SEFX.md`.

1. *A bundle whose owner sells part of it must be envied by nobody at all.*  Definition 4 asks
   for the full envy-free condition towards every agent `j` with `P_j > 0`, and the relaxed,
   up-to-any-good condition is available only when `P_j = 0`.  An agent that is handed a bundle
   `B` and reaches its threshold only through `v̄_i(B)` (i.e. by selling the goods of `B` that it
   values below their price) receives the corresponding sale proceeds, so `P_j > 0` and *every*
   other agent must be exactly envy free towards it.  This is visible in `CSafe`: the
   up-to-any-good disjunct is available only for a bundle that carries no money and that its
   owner keeps in full.
2. *Agents that are served late are never checked.*  The manuscript's `Shrink` only prevents the
   agents that already hold a bundle from envying the bundle that is being handed out.  An agent
   that is still active holds nothing, is not consulted, and may well envy — in the SEFX sense —
   a bundle that was handed out earlier, so the invariant that is maintained does not imply that
   the final allocation is SEFX.  `ISSUES_TPS_SEFX.md` contains an instance in which this
   happens, and `RequestProject/TPSSefxExamples.lean` formalizes it.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The conceptual `ε`-SEFX condition -/

/-- The conceptual form of the `ε`-SEFX condition for the pair `(i, j)` of agents, for the
assignment that gives agent `k` the bundle `A k` of goods together with `q k` in banked sale
proceeds, agent `k` being free to sell the goods of `A k` that it values below their price (so
that its utility is `v̄_k(A k) + q k`).

Either agent `i` is exactly envy free towards `j`'s bundle, or `j`'s bundle carries no money,
`j` keeps all of it, and `i` is envy free towards it up to any single good, with tolerance
`ε`. -/
def CSafe (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (A : Fin n → Finset G) (q : Fin n → ℝ)
    (i j : Fin n) : Prop :=
  (vbarSum (v i) p (A i) + q i ≥ vbarSum (v i) p (A j) + q j) ∨
  (q j = 0 ∧ (∀ g ∈ A j, p g ≤ v j g) ∧
    ∀ g ∈ A j, vbarSum (v i) p (A i) + q i + eps ≥ vbarSum (v i) p (A j \ {g}) + p g)

omit [Fintype G] in
/-- In the realization `unifiedOutcome`, the `v̄`-value of the bundle that agent `i` keeps is the
plain `v`-value of that bundle: `i` keeps exactly the goods it values at least as much as their
price. -/
theorem vbarSum_kept_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept i)
      = ∑ g ∈ (unifiedOutcome v p A F q).kept i, v i g := by
  classical
  refine Finset.sum_congr rfl (fun g hg => ?_)
  simp only [unifiedOutcome, Finset.mem_filter, not_lt] at hg
  exact max_eq_right hg.2

omit [Fintype G] in
/-- The left-hand side of the (`ε`-)SEFX conditions for agent `i` in the realization is exactly
the conceptual value `v̄_i(A i) + q i` of its bundle. -/
theorem lhs_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept i) + (unifiedOutcome v p A F q).money i
      = vbarSum (v i) p (A i) + q i := by
  rw [vbarSum_kept_unifiedOutcome]
  have := util_unifiedOutcome v p A F q i
  simpa [util] using this

omit [Fintype G] in
/-- The bundle that agent `j` keeps, together with the money it receives, is worth to agent `i`
at most the conceptual value `v̄_i(A j) + q j` of `j`'s bundle. -/
theorem rhs_unifiedOutcome_le (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i j : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept j) + (unifiedOutcome v p A F q).money j
      ≤ vbarSum (v i) p (A j) + q j := by
  classical
  have hsplit : vbarSum (v i) p (A j)
      = vbarSum (v i) p ((A j).filter (fun g => ¬ v j g < p g))
        + vbarSum (v i) p ((A j).filter (fun g => v j g < p g)) := by
    unfold vbarSum
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (A j) (fun g => v j g < p g) _).symm
  have hle : ∑ g ∈ (A j).filter (fun g => v j g < p g), p g
      ≤ vbarSum (v i) p ((A j).filter (fun g => v j g < p g)) :=
    Finset.sum_le_sum (fun g _ => le_max_left _ _)
  simp only [unifiedOutcome]
  rw [hsplit]
  linarith

omit [Fintype G] in
/-- If the money handed to agent `j` in the realization is `0`, then `j` sells nothing and keeps
its whole bundle. -/
theorem kept_eq_of_money_zero (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (j : Fin n) (hmoney : (unifiedOutcome v p A F q).money j = 0) :
    (unifiedOutcome v p A F q).kept j = A j ∧ q j = 0 := by
  classical
  simp only [unifiedOutcome] at hmoney ⊢
  have hsum : ∑ g ∈ (A j).filter (fun g => v j g < p g), p g = 0 := by
    have h0 : 0 ≤ ∑ g ∈ (A j).filter (fun g => v j g < p g), p g :=
      Finset.sum_nonneg (fun g _ => hp g)
    linarith [hq j]
  have hqj : q j = 0 := by linarith [Finset.sum_nonneg (fun g (_ : g ∈ (A j).filter
    (fun g => v j g < p g)) => hp g)]
  refine ⟨?_, hqj⟩
  have hempty : (A j).filter (fun g => v j g < p g) = ∅ := by
    by_contra hne
    obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hgmem := hg
    simp only [Finset.mem_filter] at hgmem
    have hpos : 0 < p g := lt_of_le_of_lt (hv j g) hgmem.2
    have : p g ≤ ∑ x ∈ (A j).filter (fun g => v j g < p g), p x :=
      Finset.single_le_sum (fun x _ => hp x) hg
    linarith
  refine Finset.filter_true_of_mem (fun g hg => ?_)
  intro hlt
  have : g ∈ (A j).filter (fun g => v j g < p g) := Finset.mem_filter.mpr ⟨hg, hlt⟩
  rw [hempty] at this
  exact absurd this (Finset.notMem_empty g)

omit [Fintype G] in
/-- **Conceptual safety realizes `ε`-SEFX.**  If every ordered pair of agents satisfies `CSafe`,
then the outcome realizing the assignment is `ε`-SEFX. -/
theorem epsSEFX_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsafe : ∀ i j, CSafe v p eps A q i j) :
    epsSEFX v p eps (unifiedOutcome v p A F q) := by
  classical
  intro i j
  set o := unifiedOutcome v p A F q with ho
  have hlhs : vbarSum (v i) p (o.kept i) + o.money i = vbarSum (v i) p (A i) + q i :=
    lhs_unifiedOutcome v p A F q i
  constructor
  · -- the envied bundle carries money: the full envy-free condition is required
    intro hpos
    rcases hsafe i j with hEF | ⟨hqj, hkeep, _⟩
    · have := rhs_unifiedOutcome_le v p A F q i j
      rw [hlhs]
      linarith
    · -- if `j` keeps its whole bundle and holds no banked money it receives nothing
      exfalso
      have hmz : o.money j = 0 := by
        simp only [ho, unifiedOutcome]
        have hempty : (A j).filter (fun g => v j g < p g) = ∅ := by
          refine Finset.filter_false_of_mem (fun g hg => ?_)
          exact not_lt.mpr (hkeep g hg)
        rw [hempty, hqj]
        simp
      rw [hmz] at hpos
      exact lt_irrefl 0 hpos
  · -- the envied bundle carries no money
    intro hzero
    obtain ⟨hkept, hqj⟩ := kept_eq_of_money_zero v p hv hp A F q hq j hzero
    rcases hsafe i j with hEF | ⟨_, _, hX⟩
    · left
      rw [hlhs, hkept]
      rw [hqj] at hEF
      linarith
    · right
      intro g hg
      rw [hkept] at hg
      have := hX g hg
      rw [hlhs, hkept]
      linarith

/-! ### The algorithmic core (Algorithm 6) — superseded -/

/- **Superseded, and kept only for the record.**

The first attempt at the SEFX half of Theorem 2 went through the conceptual condition `CSafe`
above: it asked the algorithm to produce, for every `ε > 0`, an assignment in which *no* agent
`ε`-SEFX-envies another agent's bundle in the strong sense of `CSafe`, and then realized it with
`unifiedOutcome`.  That statement was left unproved, and it is not the statement the manuscript's
algorithm can deliver: `CSafe` grants the up-to-any-good disjunct only to a bundle that carries
no money and that its owner keeps in full (see the discussion at the head of this file and
`ISSUES_TPS_SEFX.md`).

The SEFX half of Theorem 2 is now proved unconditionally, and in the greater generality of
arbitrary (not necessarily nonnegative) valuations, as `FairSelling.theorem_two_SEFX` in
`RequestProject/TPSSefxTheorem2.lean`.  It uses the *unified* conceptual condition `CSafeU` of
`RequestProject/TPSSefxGeneral.lean` instead of `CSafe`, and the per-good ledger of
`RequestProject/TPSSefxPot.lean` for the algorithm itself.  Nothing depends on the two
declarations below, which used to read:

```
theorem exists_eps_TPS_CSafe (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1) - eps) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, CSafe v p eps A q i j) := by
  sorry

theorem exists_TPS_SEFX (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :=
    exists_eps_TPS_CSafe v p hn hv hp eps heps
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, epsSEFX_unifiedOutcome v p eps (le_of_lt heps) hv hp A F q hq0 hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  exact hserve i
```
-/

/-! ### A by-product: the maximin share dominates the same fraction of the TPS -/

/-- Applying the `n/(2n−1)`-TPS approximation to `n` copies of a single agent shows that the
maximin share with selling is at least `n/(2n−1)` of the truncated proportional share.  (By
Lemma 1 the two shares satisfy `MMS ≤ TPS`; this is a converse bound.) -/
theorem ratio_TPS_le_MMS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ((n : ℝ) / (2 * n - 1)) * TPS n v p ≤ MMS n v p := by
  classical
  obtain ⟨o, hvalid, hserve⟩ := exists_TPS_approx (fun _ : Fin n => v) p hn hp
  exact le_MMS_of_outcome hn v p hv hp o hvalid _ (fun j => hserve j)

end FairSelling
