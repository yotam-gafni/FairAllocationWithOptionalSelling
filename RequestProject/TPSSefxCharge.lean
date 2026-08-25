import Mathlib
import RequestProject.Selling
import RequestProject.EpsEnvy
import RequestProject.LemmaEleven
import RequestProject.TPSApprox
import RequestProject.TPSCompute
import RequestProject.TPSSefxGeneral

/-!
# Theorem 2, SEFX half: the *charged* bookkeeping of Algorithm 6

`RequestProject/TPSSefxGeneral.lean` reduces the SEFX half of Theorem 2 to a single local
statement, the `ImprovementStep`, and keeps the counting invariant of Algorithm 4 (*"with `m`
agents still unserved, every unserved agent values the pool plus the bank at least `(2m−1)·τ`"*)
as an explicit part of the state invariant.  That invariant is global, and it is exactly the
thing that a *steal* (an agent that already holds a bundle taking a new one) threatens to
destroy: the manuscript's answer is the `Unshrink` operation, together with the assertion that
*"there are no more goods sold at any step than agents that are currently allocated a bundle"*.

This file makes that idea precise.  The point is that the counting invariant need not be carried
around at all: it *follows* from a purely **local** invariant, one inequality per served agent.
Concretely, every sold good is *charged* to exactly one served agent, and the sale proceeds are
split into

* `cash i`, the money agent `i` actually holds and that counts towards its utility;
* `resv i`, money that has been *put aside* — raised by selling goods that were shrunk out of
  agent `i`'s own bag, and, as the user's description of Algorithm 6 puts it, *not given to any
  other agent* while `i` holds its bundle;
* `bank`, the free proceeds, which later agents may draw on.

The local invariant (`CStage.cost`) is then, for every served `i` and every unserved `j`,

```
   truncBundleⱼ(bundle i) + cash i + resv i + ∑_{g ∈ charge i} lossⱼ(g)  ≤  2·τⱼ,
```

where `lossⱼ(g) = truncⱼ(g) − p(g) ≥ 0` is the part of a sold good's truncated value that the
sale does not return as money.  Summing this over the served agents gives the counting invariant
of Algorithm 4 *exactly* (`counting_of_cost`): there is no slack lost anywhere.  This is the
formal content of "Unshrink works because the proceeds are put aside": the reserved money `resv i`
is charged to agent `i`'s own budget, so an agent whose sales are self-financed
(`cash i + resv i = ∑_{g ∈ charge i} p g`) can always give its whole package back — un-selling its
charged goods — without the bank ever going negative.

The three ways an agent can be served in Algorithm 6 all satisfy the local invariant, each for
its own reason (`cost_le_of_footprint`, `cost_le_of_single_good`, `cost_le_of_no_charge`).

Everything in this file is proved except the improvement step itself; see `ISSUES_THEOREM2.md`.
-/

open scoped BigOperators

namespace FairSelling

namespace ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The sale loss of a good -/

/-- The *sale loss* of the good `g`: the part of its truncated contribution that selling it does
not return as money.  It is non-negative, and it vanishes as soon as the price dominates. -/
def saleLoss (w p : G → ℝ) (t : ℝ) (g : G) : ℝ := trunc w p t g - p g

omit [Fintype G] [DecidableEq G] in
lemma saleLoss_nonneg (w p : G → ℝ) (t : ℝ) (g : G) : 0 ≤ saleLoss w p t g :=
  sub_nonneg.mpr (le_max_left _ _)

omit [Fintype G] [DecidableEq G] in
/-- **The single-good bound.**  Cash drawn from one single sold good, together with that good's
sale loss, never exceeds the truncation level.  This is what makes the *money* steps of
Algorithm 6 affordable: the agent that is charged with a sold good is one that draws its cash
from that very good. -/
lemma cash_add_saleLoss_le (w p : G → ℝ) (t : ℝ) (g : G) (c : ℝ) (hc : c ≤ p g) (hct : c ≤ t) :
    c + saleLoss w p t g ≤ t := by
  unfold saleLoss trunc
  rcases max_cases (p g) (min (w g) t) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · linarith
  · have : min (w g) t ≤ t := min_le_right _ _
    linarith

omit [Fintype G] [DecidableEq G] in
/-- The sale loss of a set of goods is its truncated value minus its price. -/
lemma sum_saleLoss (w p : G → ℝ) (t : ℝ) (X : Finset G) :
    ∑ g ∈ X, saleLoss w p t g = truncBundle w p t X - ∑ g ∈ X, p g := by
  unfold saleLoss truncBundle
  rw [Finset.sum_sub_distrib]

/-! ### Stages with charges -/

/-- A stage of Algorithm 6, with the sale bookkeeping made explicit. -/
structure CStage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The goods each agent keeps. -/
  bundle : Fin n → Finset G
  /-- The sold goods charged to each agent. -/
  charge : Fin n → Finset G
  /-- The sale proceeds each agent holds. -/
  cash : Fin n → ℝ
  /-- The sale proceeds *put aside* for each agent: raised by selling goods charged to it, and
  not available to anybody else while the agent holds its bundle. -/
  resv : Fin n → ℝ
  /-- The free sale proceeds. -/
  bank : ℝ

namespace CStage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- The goods that have been sold. -/
def soldSet (s : CStage G n) : Finset G := Finset.univ.biUnion s.charge

/-- The goods that are neither sold nor allocated. -/
def pool (s : CStage G n) : Finset G :=
  Finset.univ \ (s.soldSet ∪ Finset.univ.biUnion s.bundle)

/-- The *requirement* of agent `j`: its threshold if it is not served yet, and its current
utility raised by `ε` if it is.  A served agent has to gain at least `ε` to be worth serving
again; an unserved agent claims exactly its threshold, so that no share is lost to `ε`. -/
noncomputable def req (s : CStage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j + eps
  else GeneralTPS.thr v p j

/-- Agent `i`'s package is *safe* for agent `j`: either `j` values it at most at its
requirement, or the package carries no money, its owner keeps it whole, and `j` values it at
most at its requirement up to any single good. -/
def CSafe (s : CStage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.req v p eps j) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.req v p eps j)

/-- What agent `i`'s package costs the unserved agent `j`, measured in `j`'s truncated
contributions: the truncated value of the goods it keeps, the money it holds, the money put
aside for it, and the sale losses of the goods charged to it. -/
noncomputable def cost (s : CStage G n) (i j : Fin n) : ℝ :=
  truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i + s.resv i
    + ∑ g ∈ s.charge i, saleLoss (v j) p (TPS n (v j) p) g

/-- The total utility handed out so far. -/
noncomputable def total (s : CStage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)

/-- A *good* stage: consistent bookkeeping, every served agent above its threshold, every
package safe for everybody, and — the local replacement for the counting invariant of
Algorithm 4 — every package costing every unserved agent at most `2·τ`. -/
def Good (s : CStage G n) : Prop :=
  (∀ i, i ∉ s.served → s.bundle i = ∅ ∧ s.charge i = ∅ ∧ s.cash i = 0 ∧ s.resv i = 0) ∧
  (∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)) ∧
  (∀ i j, i ≠ j → Disjoint (s.charge i) (s.charge j)) ∧
  (∀ i j, Disjoint (s.charge i) (s.bundle j)) ∧
  (∀ i, 0 ≤ s.cash i) ∧ (∀ i, 0 ≤ s.resv i) ∧ 0 ≤ s.bank ∧
  ((∑ i, s.cash i) + (∑ i, s.resv i) + s.bank = ∑ g ∈ s.soldSet, p g) ∧
  (∀ i ∈ s.served, GeneralTPS.thr v p i ≤ vbarSum (v i) p (s.bundle i) + s.cash i) ∧
  (∀ i ∈ s.served, ∀ j, s.CSafe v p eps i j) ∧
  (∀ i ∈ s.served, ∀ j, j ∉ s.served → s.cost v p i j ≤ 2 * GeneralTPS.thr v p j)

end CStage

/-! ### The accounting: the local cost bound implies the counting invariant -/

open CStage in
/-- The cost of an unserved agent's package is zero. -/
lemma cost_eq_zero_of_notMem (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) {s : CStage G n}
    (hs : s.Good v p eps) {i : Fin n} (hi : i ∉ s.served) (j : Fin n) : s.cost v p i j = 0 := by
  obtain ⟨hb, hc, hcash, hresv⟩ := hs.1 i hi
  simp [CStage.cost, hb, hc, hcash, hresv, truncBundle]

open CStage in
/-- **The accounting theorem.**  The local, per-agent cost bound of a good stage implies the
counting invariant of Algorithm 4: with `m = n − |served|` agents still unserved, every unserved
agent values the pool through its truncated contributions, plus the free bank, at least
`(2m − 1)·τ`.

This is the formal content of the manuscript's remark that `Unshrink` keeps the number of sold
goods below the number of served agents.  Nothing is lost in the summation: the identity behind
the proof is that the pool plus the bank is exactly `(2n−1)·τ` minus the total cost of the
packages handed out. -/
theorem counting_of_cost (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps) (j : Fin n) (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank := by
  classical
  set w := v j with hw
  set t := TPS n (v j) p with ht
  set B : Finset G := Finset.univ.biUnion s.bundle with hB
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  -- the truncated value of everything
  have hUniv : truncBundle w p t Finset.univ = (2 * (n:ℝ) - 1) * GeneralTPS.thr v p j := by
    rw [GeneralTPS.truncBundle_univ w p hn hp]
    unfold GeneralTPS.thr
    have hne : ((n:ℝ) * 2 - 1) ≠ 0 := ne_of_gt (by linarith)
    rw [hw]
    field_simp
  -- the universe splits into pool, sold goods and bundles
  have hdisjSB : Disjoint s.soldSet B := by
    refine Finset.disjoint_left.mpr (fun x hx hxB => ?_)
    simp only [CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    simp only [hB, Finset.mem_biUnion, Finset.mem_univ, true_and] at hxB
    obtain ⟨i, hi⟩ := hx
    obtain ⟨k, hk⟩ := hxB
    exact Finset.disjoint_left.mp (hs.2.2.2.1 i k) hi hk
  have hsplit : truncBundle w p t Finset.univ
      = truncBundle w p t s.pool + truncBundle w p t (s.soldSet ∪ B) := by
    rw [truncBundle_sdiff w p t (Finset.subset_univ (s.soldSet ∪ B))]
    rfl
  have hSB : truncBundle w p t (s.soldSet ∪ B)
      = truncBundle w p t s.soldSet + truncBundle w p t B :=
    Finset.sum_union hdisjSB
  have hsold : truncBundle w p t s.soldSet = ∑ i, truncBundle w p t (s.charge i) := by
    unfold CStage.soldSet truncBundle
    refine Finset.sum_biUnion ?_
    intro a _ b _ hab
    exact hs.2.2.1 a b hab
  have hbund : truncBundle w p t B = ∑ i, truncBundle w p t (s.bundle i) := by
    unfold truncBundle
    rw [hB]
    refine Finset.sum_biUnion ?_
    intro a _ b _ hab
    exact hs.2.1 a b hab
  have hpsold : ∑ g ∈ s.soldSet, p g = ∑ i, ∑ g ∈ s.charge i, p g := by
    unfold CStage.soldSet
    refine Finset.sum_biUnion ?_
    intro a _ b _ hab
    exact hs.2.2.1 a b hab
  -- the total cost
  have hcost : ∑ i, s.cost v p i j
      = (∑ i, truncBundle w p t (s.bundle i)) + (∑ i, s.cash i) + (∑ i, s.resv i)
        + ((∑ i, truncBundle w p t (s.charge i)) - ∑ i, ∑ g ∈ s.charge i, p g) := by
    unfold CStage.cost
    rw [← hw, ← ht]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => sum_saleLoss w p t (s.charge i))
  have hmoney := hs.2.2.2.2.2.2.2.1
  have hkey : ∑ i, s.cost v p i j
      = (2 * (n:ℝ) - 1) * GeneralTPS.thr v p j - truncBundle w p t s.pool - s.bank := by
    rw [hcost]
    rw [hpsold] at hmoney
    have h1 : truncBundle w p t s.pool + (∑ i, truncBundle w p t (s.charge i))
        + (∑ i, truncBundle w p t (s.bundle i)) = (2 * (n:ℝ) - 1) * GeneralTPS.thr v p j := by
      rw [← hUniv, hsplit, hSB, hsold, hbund]; ring
    linarith
  -- the cost bound, summed
  have hbound : ∑ i, s.cost v p i j ≤ (s.served.card : ℝ) * (2 * GeneralTPS.thr v p j) := by
    have hsub : ∑ i, s.cost v p i j = ∑ i ∈ s.served, s.cost v p i j := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      exact cost_eq_zero_of_notMem v p eps hs hi j
    rw [hsub]
    calc ∑ i ∈ s.served, s.cost v p i j
        ≤ ∑ _i ∈ s.served, (2 * GeneralTPS.thr v p j) :=
          Finset.sum_le_sum (fun i hi => hs.2.2.2.2.2.2.2.2.2.2 i hi j hj)
      _ = (s.served.card : ℝ) * (2 * GeneralTPS.thr v p j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hkey, hbound]

/-! ### From a charged stage to a stage of `TPSSefxGeneral` -/

namespace CStage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- Forgetting the charges: the reserved money is simply added to the bank. -/
def toStage (s : CStage G n) : GeneralTPS.Stage G n :=
  ⟨s.served, s.bundle, s.soldSet, s.cash, s.bank + ∑ i, s.resv i⟩

omit [Fintype G] in
@[simp] lemma toStage_served (s : CStage G n) : (s.toStage).served = s.served := rfl
omit [Fintype G] in
@[simp] lemma toStage_bundle (s : CStage G n) : (s.toStage).bundle = s.bundle := rfl
omit [Fintype G] in
@[simp] lemma toStage_cash (s : CStage G n) : (s.toStage).cash = s.cash := rfl

lemma toStage_pool (s : CStage G n) : (s.toStage).pool = s.pool := rfl

omit [Fintype G] in
lemma toStage_total (s : CStage G n) : (s.toStage).total v p = s.total v p := rfl

end CStage

open CStage in
/-- A good charged stage is a good stage in the sense of `TPSSefxGeneral`: the counting
invariant of Algorithm 4 is *derived* from the local cost bound. -/
theorem good_toStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps) :
    (s.toStage).Good v p eps := by
  classical
  obtain ⟨hempty, hbdisj, hcdisj, hcb, hcash0, hresv0, hbank0, hmoney, hshare, hsafe, hcost⟩ := hs
  have hresvsum : 0 ≤ ∑ i, s.resv i := Finset.sum_nonneg (fun i _ => hresv0 i)
  refine ⟨fun i hi => ⟨(hempty i hi).1, (hempty i hi).2.2.1⟩, hbdisj, ?_, hcash0,
    show (0:ℝ) ≤ s.bank + ∑ i, s.resv i by linarith, ?_, hshare, ?_, ?_⟩
  · -- the sold goods are disjoint from every bundle
    intro i
    refine Finset.disjoint_left.mpr (fun x hx hxb => ?_)
    simp only [CStage.toStage, CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hx
    obtain ⟨k, hk⟩ := hx
    exact Finset.disjoint_left.mp (hcb k i) hk hxb
  · show (∑ i, s.cash i) + (s.bank + ∑ i, s.resv i) = ∑ g ∈ s.soldSet, p g
    linarith
  · -- safety
    intro i hi j
    have h := hsafe i hi j
    have hreq : s.req v p eps j ≤ (s.toStage).guar v p j + eps := by
      unfold CStage.req GeneralTPS.Stage.guar
      by_cases hj : j ∈ s.served <;> (simp [hj, CStage.toStage]; try linarith)
    rcases h with h | ⟨h1, h2, h3⟩
    · exact Or.inl (le_trans h hreq)
    · exact Or.inr ⟨h1, h2, fun g hg => le_trans (h3 g hg) hreq⟩
  · -- the counting invariant
    intro j hj
    have := counting_of_cost v p eps hn hp
      ⟨hempty, hbdisj, hcdisj, hcb, hcash0, hresv0, hbank0, hmoney, hshare, hsafe, hcost⟩ j hj
    show (2 * ((n : ℝ) - (s.served.card : ℝ)) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + (s.bank + ∑ i, s.resv i)
    linarith

/-! ### The empty stage -/

/-- The charged stage in which nothing has happened yet. -/
def emptyCStage (G : Type*) (n : ℕ) : CStage G n :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0⟩

theorem good_emptyCStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyCStage G n).Good v p eps := by
  refine ⟨fun i _ => ⟨rfl, rfl, rfl, rfl⟩, fun i j _ => by simp [emptyCStage],
    fun i j _ => by simp [emptyCStage], fun i j => by simp [emptyCStage],
    fun i => le_rfl, fun i => le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
  · have h : (Finset.univ.biUnion fun _ : Fin n => (∅ : Finset G)) = ∅ := by ext x; simp
    simp [emptyCStage, CStage.soldSet, h]
  · intro i hi; exact absurd hi (by simp [emptyCStage])
  · intro i hi; exact absurd hi (by simp [emptyCStage])
  · intro i hi; exact absurd hi (by simp [emptyCStage])

/-! ### The improvement step and the descent -/

/-- **The improvement step for charged stages**: from a good charged stage in which some agent is
still unserved one can pass to a good charged stage in which either one more agent holds a
bundle, or the total utility has increased by at least `ε`. -/
def CImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : CStage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : CStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))

section Descent

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem ctotal_le_bound (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p :=
  GeneralTPS.total_le_bound v p eps hp (good_toStage v p eps hn heps hp hs)

theorem ctotal_nonneg (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p :=
  GeneralTPS.total_nonneg v p eps hp (good_toStage v p eps hn heps hp hs)

/-- The inner descent: with the number of unserved agents fixed, the total utility increases by
at least `ε` at every step and is bounded, so the process cannot go on for ever. -/
theorem cdescent_inner (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : CImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : CStage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : CStage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : CStage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      GeneralTPS.totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : CStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
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
      have h1 := ctotal_le_bound v p eps hn heps.le hp hs'
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

/-- The descent: every good charged stage can be completed to one in which every agent is
served. -/
theorem cdescent (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : CImprovementStep v p eps) :
    ∀ (c : ℕ) (s : CStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : CStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
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
    obtain ⟨b, hbb⟩ : ∃ b : ℕ, GeneralTPS.totalBound v p ≤ (b : ℝ) * eps := by
      obtain ⟨b, hb⟩ := exists_nat_gt (GeneralTPS.totalBound v p / eps)
      exact ⟨b, by rw [div_lt_iff₀ heps] at hb; linarith⟩
    refine cdescent_inner v p eps hn hp heps hstep c ihc b s hs hc ?_
    have := ctotal_nonneg v p eps hn heps.le hp hs
    linarith

end Descent

/-! ### The reduction to Theorem 2 -/

/-- The `ε`-approximate form of Theorem 2 (SEFX half), from the charged improvement step. -/
theorem exists_eps_TPS_CSafeU_of_Cstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps) (hstep : CImprovementStep v p eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, GeneralTPS.CSafeU v p eps A q i j) := by
  classical
  obtain ⟨s0, hs0, hfull⟩ := cdescent v p eps hn hp heps hstep n
    (emptyCStage G n) (good_emptyCStage v p eps) (by simp [emptyCStage])
  set s := s0.toStage with hsdef
  have hs : s.Good v p eps := good_toStage v p eps hn heps.le hp hs0
  have hfulls : s.served = Finset.univ := hfull
  refine ⟨s.bundle, s.soldSet, s.cash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_, ?_⟩
  · have := hs.2.2.2.2.2.1
    have hb := hs.2.2.2.2.1
    linarith
  · intro i
    exact hs.2.2.2.2.2.2.1 i (by rw [hfulls]; exact Finset.mem_univ i)
  · exact GeneralTPS.csafeU_of_full v p eps hs hfulls

/-- **Theorem 2 (SEFX half) reduces to the charged improvement step.** -/
theorem exists_TPS_SEFX_of_Cstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → CImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS_u v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :=
    exists_eps_TPS_CSafeU_of_Cstep v p hn hp eps heps (hstep eps heps)
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, GeneralTPS.epsSEFXu_unifiedOutcome v p eps A F q hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  have hTPS : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
  nlinarith [hserve i]

end ChargeTPS

end FairSelling
