import Mathlib
import RequestProject.TPSSefxConfig

/-!
# Algorithm 6 with the manuscript's phase structure: the state

`RequestProject/TPSSefxCharge.lean` introduced *charged stages*, in which every sold good is
charged to one served agent, and showed that the counting invariant of Algorithm 4 follows from
a purely local, per-agent cost bound (`ChargeTPS.counting_of_cost`).  What that bookkeeping could
not express is the manuscript's `Unshrink`: an agent that already holds a bundle and *steals* a
new one has to give its old package back, and for that it has to be able to buy back the goods
it had sold.

This file refines the state so that `Unshrink` is always possible.  The refinement is exactly the
manuscript's distinction between the two ways a good gets sold:

* in the **bag-filling** loop the sale is *self-financed*: the proceeds of the goods a bag sells
  are either handed to the bag's owner or *put aside* for it, so the owner alone holds the whole
  price and can always undo the sale.  These goods are the field `own`.

* in the **large-good** loops a good is sold and only *part* of its proceeds is handed out — the
  manuscript's moving knife — the rest staying available for the other agents, so that several
  agents may be served out of one sold good.  Such a good is never bought back; the agent it is
  charged to keeps the responsibility for it for ever.  These goods are the field `ext`, and
  each of them is either

  * **pure** — its price already dominates its truncated contribution for every unserved agent,
    so carrying it costs nobody anything and the free proceeds in the bank may be drawn by
    anybody with no further charge — or
  * **shared** (`PStage.ShareOK`) — the agent it is charged to holds nothing but a slice of its
    proceeds, of size at most its price, so that the sale costs an unserved agent `j` at most
    `TPSⱼ ≤ 2·τⱼ` (`ChargeTPS.cash_add_saleLoss_le`).

With that split, releasing an agent is unconditional as long as it carries no *shared* good
(`own` is paid for by the agent's own cash and reserve, a pure `ext` good is simply kept), which
is what makes the stealing case of Algorithm 6 work.  Releasing an agent that carries a shared
good is the one step that is left unproved (`PhaseTPS.pcarrier_reassign`).

The file sets up the state (`PStage`), its invariant (`PStage.Good`), the translation into a
charged stage (`PStage.toCStage`, `good_toCStage`) — which imports the whole accounting of
`ChargeTPS` — the descent, and the reduction of Theorem 2 (SEFX half) to a single improvement
step for these states.
-/

open scoped BigOperators

namespace FairSelling

namespace PhaseTPS

open ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Pure goods -/

/-- A good is *pure* for the set `served` of already served agents if selling it loses nothing:
its price dominates its truncated contribution for every agent that is not served yet.  Selling
a pure good therefore costs an unserved agent exactly the money it yields. -/
def PureGood (v : Fin n → G → ℝ) (p : G → ℝ) (served : Finset (Fin n)) (g : G) : Prop :=
  ∀ j, j ∉ served → saleLoss (v j) p (TPS n (v j) p) g = 0

omit [DecidableEq G] in
lemma PureGood.mono {v : Fin n → G → ℝ} {p : G → ℝ} {A B : Finset (Fin n)} (hAB : A ⊆ B)
    {g : G} (h : PureGood v p A g) : PureGood v p B g :=
  fun j hj => h j (fun hjA => hj (hAB hjA))

omit [DecidableEq G] in
/-- A good whose price is at least the truncation level of every unserved agent is pure. -/
lemma pureGood_of_TPS_le {v : Fin n → G → ℝ} {p : G → ℝ} {A : Finset (Fin n)} {g : G}
    (h : ∀ j, j ∉ A → TPS n (v j) p ≤ p g) : PureGood v p A g := by
  intro j hj
  unfold saleLoss trunc
  have h1 : min (v j g) (TPS n (v j) p) ≤ p g := le_trans (min_le_right _ _) (h j hj)
  rw [max_eq_left h1]
  ring

/-! ### The state -/

/-- A stage of Algorithm 6 in its phase-structured form. -/
structure PStage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The goods each agent keeps. -/
  bundle : Fin n → Finset G
  /-- The goods sold *inside* an agent's own package: the agent holds their whole price, as cash
  or put aside, and can undo the sale at any moment. -/
  own : Fin n → Finset G
  /-- The pure goods an agent has sold in a large-good step: only part of the proceeds was
  handed out, the rest is free, and the agent keeps the charge for ever. -/
  ext : Fin n → Finset G
  /-- The sale proceeds each agent holds. -/
  cash : Fin n → ℝ
  /-- The sale proceeds put aside for each agent. -/
  resv : Fin n → ℝ
  /-- The free sale proceeds. -/
  bank : ℝ

namespace PStage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- All the goods charged to an agent. -/
def charge (s : PStage G n) (i : Fin n) : Finset G := s.own i ∪ s.ext i

/-- The goods that have been sold. -/
def sold (s : PStage G n) : Finset G := Finset.univ.biUnion s.charge

/-- The goods that are neither sold nor allocated. -/
def pool (s : PStage G n) : Finset G :=
  Finset.univ \ (s.sold ∪ Finset.univ.biUnion s.bundle)

/-- The requirement of an agent: its threshold if unserved, its current utility raised by `ε`
if it is already served. -/
noncomputable def req (s : PStage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j + eps
  else GeneralTPS.thr v p j

/-- Agent `i`'s package is safe for agent `j`. -/
def PSafe (s : PStage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.req v p eps j) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.req v p eps j)

/-- Agent `i` *carries* the shared good `g`: `g` was sold in a large-good step and only part of
its proceeds — at most `p g`, and in fact the slice `i` was handed — stays with `i`, the rest
being free in the bank.  For that to cost `i`'s unserved neighbours no more than they can
afford, `i` must hold nothing but that money, and `g` must be the only good `i` is charged with
that is not pure. -/
def ShareOK (s : PStage G n) (i : Fin n) (g : G) : Prop :=
  s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.resv i = 0 ∧ s.cash i ≤ p g ∧
    ∀ g' ∈ s.ext i, g' ≠ g → PureGood v p s.served g'

/-- What agent `i`'s package costs the unserved agent `j`.  The pure goods of `ext i` cost
nothing, so they contribute `0`; a *shared* good of `ext i` contributes its sale loss. -/
noncomputable def cost (s : PStage G n) (i j : Fin n) : ℝ :=
  truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i + s.resv i
    + ∑ g ∈ s.own i, saleLoss (v j) p (TPS n (v j) p) g
    + ∑ g ∈ s.ext i, saleLoss (v j) p (TPS n (v j) p) g

/-- The total utility handed out so far. -/
noncomputable def total (s : PStage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)

/-- The invariant of Algorithm 6. -/
structure Good (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : PStage G n) : Prop where
  /-- An unserved agent holds nothing. -/
  unserved : ∀ i, i ∉ s.served →
    s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.ext i = ∅ ∧ s.cash i = 0 ∧ s.resv i = 0
  /-- Bundles are pairwise disjoint. -/
  bundle_disj : ∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)
  /-- Sold goods are in nobody's bundle. -/
  charge_bundle : ∀ i j, Disjoint (s.charge i) (s.bundle j)
  /-- Self-financed sales belong to one agent only. -/
  own_disj : ∀ i j, i ≠ j → Disjoint (s.own i) (s.own j)
  /-- A self-financed sale is never also a large-good sale. -/
  own_ext : ∀ i j, Disjoint (s.own i) (s.ext j)
  /-- A large-good sale is either *pure* — its price already dominates its truncated
  contribution for every unserved agent, so carrying it costs nobody anything — or *shared*:
  the agent charged with it holds nothing but a slice of its proceeds. -/
  ext_ok : ∀ i, ∀ g ∈ s.ext i, PureGood v p s.served g ∨ s.ShareOK v p i g
  /-- Only a pure large-good sale may be charged to more than one agent. -/
  ext_uniq : ∀ i i', i ≠ i' → ∀ g ∈ s.ext i, g ∈ s.ext i' → PureGood v p s.served g
  cash_nonneg : ∀ i, 0 ≤ s.cash i
  resv_nonneg : ∀ i, 0 ≤ s.resv i
  bank_nonneg : 0 ≤ s.bank
  /-- Self-financing: an agent holds the whole price of the goods it sold on its own. -/
  self_fin : ∀ i, ∑ g ∈ s.own i, p g ≤ s.cash i + s.resv i
  /-- The money equation. -/
  money : (∑ i, s.cash i) + (∑ i, s.resv i) + s.bank = ∑ g ∈ s.sold, p g
  /-- Every served agent is above its threshold. -/
  share : ∀ i ∈ s.served, GeneralTPS.thr v p i ≤ vbarSum (v i) p (s.bundle i) + s.cash i
  /-- Every package is safe for everybody. -/
  safe : ∀ i ∈ s.served, ∀ j, s.PSafe v p eps i j
  /-- Every package costs every unserved agent at most `2τ`. -/
  cost_le : ∀ i ∈ s.served, ∀ j, j ∉ s.served → s.cost v p i j ≤ 2 * GeneralTPS.thr v p j

end PStage

/-! ### Translation into a charged stage -/

namespace PStage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

open Classical in
/-- The charged stage underlying a phase-structured stage: the pure goods of `ext` are attributed
to the *first* agent charged with them, which turns the cover of the sold goods into a
partition.  This changes no cost, because pure goods cost nothing. -/
noncomputable def toCStage (s : PStage G n) : ChargeTPS.CStage G n :=
  ⟨s.served, s.bundle,
    fun i => s.own i ∪ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k),
    s.cash, s.resv, s.bank⟩

omit [Fintype G] in
open Classical in
lemma toCStage_charge (s : PStage G n) (i : Fin n) :
    (s.toCStage).charge i = s.own i ∪ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k) :=
  rfl

omit [Fintype G] in
@[simp] lemma toCStage_served (s : PStage G n) : (s.toCStage).served = s.served := rfl
omit [Fintype G] in
@[simp] lemma toCStage_bundle (s : PStage G n) : (s.toCStage).bundle = s.bundle := rfl
omit [Fintype G] in
@[simp] lemma toCStage_cash (s : PStage G n) : (s.toCStage).cash = s.cash := rfl
omit [Fintype G] in
@[simp] lemma toCStage_resv (s : PStage G n) : (s.toCStage).resv = s.resv := rfl
omit [Fintype G] in
@[simp] lemma toCStage_bank (s : PStage G n) : (s.toCStage).bank = s.bank := rfl

omit [Fintype G] in
lemma charge_subset (s : PStage G n) (i : Fin n) : (s.toCStage).charge i ⊆ s.charge i := by
  classical
  intro x hx
  rw [toCStage_charge] at hx
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_of_mem_filter _ h)

omit [Fintype G] in
lemma toCStage_soldSet (s : PStage G n) : (s.toCStage).soldSet = s.sold := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [ChargeTPS.CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, charge_subset s i hi⟩
  · intro x hx
    simp only [PStage.sold, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    -- take the least agent charged with `x`
    set T : Finset (Fin n) := Finset.univ.filter (fun k => x ∈ s.charge k) with hT
    have hTne : T.Nonempty := ⟨i, by simp [hT, hi]⟩
    set i0 := T.min' hTne with hi0
    have hi0mem : x ∈ s.charge i0 := by
      have := T.min'_mem hTne
      simp only [hT, Finset.mem_filter] at this
      exact this.2
    have hmin : ∀ k, x ∈ s.charge k → i0 ≤ k := by
      intro k hk
      exact T.min'_le k (by simp [hT, hk])
    refine Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ i0, ?_⟩
    rw [toCStage_charge]
    rcases Finset.mem_union.mp hi0mem with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, hmin⟩)

lemma toCStage_pool (s : PStage G n) : (s.toCStage).pool = s.pool := by
  unfold ChargeTPS.CStage.pool PStage.pool
  rw [toCStage_soldSet]
  rfl

lemma toCStage_req (s : PStage G n) (j : Fin n) :
    (s.toCStage).req v p eps j = s.req v p eps j := rfl

omit [Fintype G] in
lemma toCStage_total (s : PStage G n) : (s.toCStage).total v p = s.total v p := rfl

lemma toCStage_cost {s : PStage G n} (hs : s.Good v p eps) (i j : Fin n) (hj : j ∉ s.served) :
    (s.toCStage).cost v p i j = s.cost v p i j := by
  classical
  have hdisj : Disjoint (s.own i) ((s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k)) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hs.own_ext i i)
  have hsum : ∑ g ∈ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k),
      saleLoss (v j) p (TPS n (v j) p) g
      = ∑ g ∈ s.ext i, saleLoss (v j) p (TPS n (v j) p) g := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hx hxF
    obtain ⟨k, hk, hik⟩ : ∃ k, x ∈ s.charge k ∧ ¬ (i ≤ k) := by
      by_contra hc
      push_neg at hc
      exact hxF (Finset.mem_filter.mpr ⟨hx, hc⟩)
    have hki : k ≠ i := by rintro rfl; exact hik le_rfl
    have hxk : x ∈ s.ext k := by
      rcases Finset.mem_union.mp hk with h | h
      · exact absurd hx (Finset.disjoint_left.mp (hs.own_ext k i) h)
      · exact h
    exact hs.ext_uniq i k (Ne.symm hki) x hx hxk j hj
  unfold ChargeTPS.CStage.cost PStage.cost
  rw [toCStage_charge, Finset.sum_union hdisj, hsum]
  simp only [toCStage_bundle, toCStage_cash, toCStage_resv]
  ring

/-- **The invariant transfers to the charged bookkeeping**, hence the whole accounting of
`ChargeTPS` — in particular the counting invariant of Algorithm 4 — applies. -/
theorem good_toCStage {s : PStage G n} (hs : s.Good v p eps) :
    (s.toCStage).Good v p eps := by
  classical
  refine ⟨?_, hs.bundle_disj, ?_, ?_, hs.cash_nonneg, hs.resv_nonneg, hs.bank_nonneg, ?_, ?_,
    ?_, ?_⟩
  · -- unserved agents hold nothing
    intro i hi
    obtain ⟨hb, ho, he, hc, hr⟩ := hs.unserved i hi
    refine ⟨hb, ?_, hc, hr⟩
    rw [toCStage_charge, ho, he]
    simp
  · -- charges are pairwise disjoint
    intro i j hij
    rw [toCStage_charge, toCStage_charge]
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · refine Finset.disjoint_union_right.mpr ⟨hs.own_disj i j hij, ?_⟩
      exact Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hs.own_ext i j)
    · refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
      · exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
          (hs.own_ext j i).symm
      · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
        have h1 := (Finset.mem_filter.mp hx).2
        have h2 := (Finset.mem_filter.mp hx').2
        have hxi : x ∈ s.charge i :=
          Finset.mem_union_right _ (Finset.mem_of_mem_filter _ hx)
        have hxj : x ∈ s.charge j :=
          Finset.mem_union_right _ (Finset.mem_of_mem_filter _ hx')
        exact hij (le_antisymm (h1 j hxj) (h2 i hxi))
  · -- sold goods are in nobody's bundle
    intro i j
    exact Finset.disjoint_of_subset_left (charge_subset s i) (hs.charge_bundle i j)
  · -- the money equation
    show (∑ i, s.cash i) + (∑ i, s.resv i) + s.bank = ∑ g ∈ (s.toCStage).soldSet, p g
    rw [toCStage_soldSet]
    exact hs.money
  · exact hs.share
  · -- safety
    intro i hi j
    rcases hs.safe i hi j with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  · -- the cost bound
    intro i hi j hj
    rw [toCStage_cost v p eps hs i j hj]
    exact hs.cost_le i hi j hj

/-! ### Consequences of the invariant -/

lemma disjoint_pool_sold (s : PStage G n) : Disjoint s.pool s.sold := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [PStage.pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inl hx')

lemma disjoint_pool_bundle (s : PStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [PStage.pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))

lemma disjoint_pool_charge (s : PStage G n) (i : Fin n) : Disjoint s.pool (s.charge i) :=
  Finset.disjoint_left.mpr (fun _ hx hx' =>
    Finset.disjoint_left.mp (disjoint_pool_sold s) hx
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))

omit [Fintype G] in
lemma charge_subset_sold (s : PStage G n) (i : Fin n) : s.charge i ⊆ s.sold :=
  fun _ hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

end PStage

/-! ### The empty stage -/

/-- The stage in which nothing has happened yet. -/
def emptyPStage (G : Type*) (n : ℕ) : PStage G n :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0⟩

theorem good_emptyPStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyPStage G n).Good v p eps := by
  classical
  have hsold : (emptyPStage G n).sold = (∅ : Finset G) := by
    ext x; simp [PStage.sold, PStage.charge, emptyPStage]
  refine ⟨fun i _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun i j _ => by simp [emptyPStage],
    fun i j => by simp [PStage.charge, emptyPStage], fun i j _ => by simp [emptyPStage],
    fun i j => by simp [emptyPStage], fun i g hg => absurd hg (by simp [emptyPStage]),
    fun i i' _ g hg _ => absurd hg (by simp [emptyPStage]),
    fun i => le_rfl, fun i => le_rfl, le_rfl, fun i => by simp [emptyPStage], ?_, ?_, ?_, ?_⟩
  · rw [hsold]; simp [emptyPStage]
  · intro i hi; exact absurd hi (by simp [emptyPStage])
  · intro i hi; exact absurd hi (by simp [emptyPStage])
  · intro i hi; exact absurd hi (by simp [emptyPStage])

/-! ### The improvement step and the descent -/

/-- **The improvement step**: from a good stage in which some agent is still unserved one can
pass to a good stage in which either one more agent holds a bundle, or the total utility has
increased by at least `ε`. -/
def PImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : PStage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))

section Descent

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem ptotal_le_bound (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : PStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p :=
  ChargeTPS.ctotal_le_bound v p eps hn heps hp (PStage.good_toCStage v p eps hs)

theorem ptotal_nonneg (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : PStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p :=
  ChargeTPS.ctotal_nonneg v p eps hn heps hp (PStage.good_toCStage v p eps hs)

/-- The inner descent: with the number of unserved agents fixed, the total utility increases by
at least `ε` at every step and is bounded. -/
theorem pdescent_inner (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : PImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : PStage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : PStage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : PStage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      GeneralTPS.totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : PStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
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
      have h1 := ptotal_le_bound v p eps hn heps.le hp hs'
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

/-- Every good stage can be completed to one in which every agent is served. -/
theorem pdescent (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : PImprovementStep v p eps) :
    ∀ (c : ℕ) (s : PStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : PStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
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
    refine pdescent_inner v p eps hn hp heps hstep c ihc b s hs hc ?_
    have := ptotal_nonneg v p eps hn heps.le hp hs
    linarith

end Descent

/-! ### The reduction to Theorem 2 -/

/-- **Theorem 2 (SEFX half) reduces to the phase-structured improvement step.** -/
theorem exists_TPS_SEFX_of_Pstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → PImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine ChargeTPS.exists_TPS_SEFX_of_Cstep v p hn hp ?_
  intro eps heps s hs hfull
  -- the charged improvement step is only ever applied to stages coming from `PStage`s, so we
  -- run the descent at the level of `PStage` and re-package the outcome
  obtain ⟨s0, hs0, hs0full⟩ := pdescent v p eps hn hp heps (hstep eps heps) n
    (emptyPStage G n) (good_emptyPStage v p eps) (by simp [emptyPStage])
  refine ⟨s0.toCStage, PStage.good_toCStage v p eps hs0, ?_⟩
  left
  have h1 : s.served.card < n := by
    have h2 : s.served ⊂ Finset.univ := ⟨Finset.subset_univ _, fun h => hfull
      (Finset.Subset.antisymm (Finset.subset_univ _) h)⟩
    have := Finset.card_lt_card h2
    simpa using this
  have h3 : (s0.toCStage).served.card = n := by
    show s0.served.card = n
    rw [hs0full]; simp
  omega

end PhaseTPS

end FairSelling
