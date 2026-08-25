import Mathlib
import RequestProject.TPSSefxConfig
import RequestProject.TPSSefxStep

/-!
# Algorithm 6 with a per-good ledger for the shared sale proceeds: the state

`RequestProject/TPSSefxPhase.lean` refined the charged bookkeeping of
`RequestProject/TPSSefxCharge.lean` so that an agent could always give its package back — with
one exception, an agent holding a *slice* of a good that was sold in a large-good step and whose
remaining proceeds went into the anonymous bank.  `ISSUES_THEOREM2.md` explains why that case
could not be closed: once the free leftover of a sold good has been spent by somebody else, the
good can neither be bought back nor charged to another agent.

This file replaces the anonymous bank for those leftovers by a **per-good ledger**.  When a good
`g` is sold in a large-good step, the agents that hold a slice of its proceeds are recorded
(`QStage.src`), and

```
   pot g  =  p g − ∑ (slices of g currently held)
```

is the part of the proceeds nobody holds.  Two rules make everything work:

* the **pot of a sold good may only be used to cut further slices of that same good** — the free
  money the rest of the algorithm may draw on is `freeBank = bank − ∑ pot`;
* **every holder of `g` is charged with `g`**, not just one of them.  Charging a sale loss to
  several agents only over-counts, which is harmless for the accounting, and it removes the need
  to move a charge when a holder is re-allocated.

With those two rules, releasing an agent is *unconditional*: its slice goes back into the pot of
its good, and if it was the last holder the pot has grown back to the full price `p g`, so the
sale can simply be undone.  This is the manuscript's `Unshrink`.

The price is paid in the counting invariant, which now reads

```
   (2·(n − |served|) − 1)·τⱼ ≤ truncBundleⱼ(pool) + bank − ∑_{g sold in a cut} min(pot g, τⱼ)
```

(`QStage.qcounting`).  The deduction is capped at `τⱼ`, and that cap is what makes a single
holder of an *expensive* good affordable: a holder of `g` costs `j` at most
`slice + lossⱼ(g) + min(pot g, τⱼ) ≤ 2τⱼ` whatever the price of `g` (`slice_cost_le`).  The
algorithm keeps the deduction honest by cutting a further slice out of any pot that is large
enough to serve somebody, so that when it comes to bag filling every pot is below every
requirement and `min(pot g, τⱼ) = pot g` really is the money the bag filling may not touch.
-/

open scoped BigOperators

namespace FairSelling

namespace PotTPS

open ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The cost of holding a slice of a sold good -/

omit [Fintype G] [DecidableEq G] in
/-- **A slice of a sold good is affordable.**  An agent whose whole package is a slice `a` of the
proceeds of the sold good `g`, and which is charged both with the sale loss of `g` and with the
capped deduction `min(c, τ)` for the part `c` of the proceeds nobody holds, costs an unserved
agent at most `2τ` — whatever the price of `g`. -/
lemma slice_cost_le (w p : G → ℝ) (t τ : ℝ) (g : G) (a c : ℝ)
    (hac : a + c ≤ p g) (hat : a ≤ τ) (ht : t ≤ 2 * τ) :
    a + (saleLoss w p t g + min c τ) ≤ 2 * τ := by
  have hmin1 : min c τ ≤ c := min_le_left _ _
  have hmin2 : min c τ ≤ τ := min_le_right _ _
  unfold saleLoss trunc
  rcases max_cases (p g) (min (w g) t) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · linarith
  · have h1 : min (w g) t ≤ t := min_le_right _ _
    linarith

/-! ### The state -/

/-- A stage of Algorithm 6 with a per-good ledger for the proceeds of the goods that were sold in
a large-good step. -/
structure QStage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The goods each agent keeps. -/
  bundle : Fin n → Finset G
  /-- The goods sold *inside* an agent's own package: the agent holds their whole price, as cash
  or put aside, and can undo the sale at any moment. -/
  own : Fin n → Finset G
  /-- The good — there is at most one — a *cut* of whose proceeds the agent holds.  The agent is
  then charged with that good. -/
  src : Fin n → Finset G
  /-- The sale proceeds each agent holds. -/
  cash : Fin n → ℝ
  /-- The sale proceeds put aside for each agent. -/
  resv : Fin n → ℝ
  /-- The sale proceeds nobody holds. -/
  bank : ℝ

namespace QStage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- The goods that were sold in a large-good step, and cut into slices. -/
def cutSet (s : QStage G n) : Finset G := Finset.univ.biUnion s.src

/-- The goods that have been sold. -/
def sold (s : QStage G n) : Finset G := (Finset.univ.biUnion s.own) ∪ s.cutSet

/-- The goods that are neither sold nor allocated. -/
def pool (s : QStage G n) : Finset G :=
  Finset.univ \ (s.sold ∪ Finset.univ.biUnion s.bundle)

/-- The agents holding a slice of the proceeds of `g`. -/
def holders (s : QStage G n) (g : G) : Finset (Fin n) :=
  Finset.univ.filter (fun i => g ∈ s.src i)

/-- The part of the proceeds of a cut good that nobody holds. -/
noncomputable def pot (s : QStage G n) (p : G → ℝ) (g : G) : ℝ :=
  p g - ∑ i ∈ s.holders g, s.cash i

/-- The money the algorithm may freely draw on: the bank minus the pots of the cut goods, which
are reserved for cutting further slices of their own good. -/
noncomputable def freeBank (s : QStage G n) (p : G → ℝ) : ℝ :=
  s.bank - ∑ g ∈ s.cutSet, s.pot p g

/-- The requirement of an agent: its threshold if unserved, its current utility raised by `ε`
if it is already served. -/
noncomputable def req (s : QStage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j + eps
  else GeneralTPS.thr v p j

/-- Agent `i`'s package is safe for agent `j`. -/
def PSafe (s : QStage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.req v p eps j) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.req v p eps j)

/-- What agent `i`'s package costs the unserved agent `j`: the truncated value of the goods it
keeps, the money it holds and the money put aside for it, the sale losses of the goods it sold
inside its own package, and — if it holds a slice of a cut good — the sale loss of that good
together with the capped deduction for the part of its proceeds nobody holds. -/
noncomputable def cost (s : QStage G n) (i j : Fin n) : ℝ :=
  truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i + s.resv i
    + ∑ g ∈ s.own i, saleLoss (v j) p (TPS n (v j) p) g
    + ∑ g ∈ s.src i,
        (saleLoss (v j) p (TPS n (v j) p) g + min (s.pot p g) (GeneralTPS.thr v p j))

/-- The total utility handed out so far. -/
noncomputable def total (s : QStage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)

/-- The invariant of Algorithm 6 with a per-good ledger. -/
structure Good (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : QStage G n) : Prop where
  /-- An unserved agent holds nothing. -/
  unserved : ∀ i, i ∉ s.served →
    s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.src i = ∅ ∧ s.cash i = 0 ∧ s.resv i = 0
  /-- Bundles are pairwise disjoint. -/
  bundle_disj : ∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)
  /-- Sold goods are in nobody's bundle. -/
  sold_bundle : ∀ i, Disjoint s.sold (s.bundle i)
  /-- Self-financed sales belong to one agent only. -/
  own_disj : ∀ i j, i ≠ j → Disjoint (s.own i) (s.own j)
  /-- A self-financed sale is never a cut. -/
  own_cut : ∀ i j, Disjoint (s.own i) (s.src j)
  /-- An agent holds a slice of at most one cut good. -/
  src_card : ∀ i, (s.src i).card ≤ 1
  /-- An agent holding a slice holds nothing else. -/
  cutter : ∀ i, s.src i ≠ ∅ → s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.resv i = 0
  cash_nonneg : ∀ i, 0 ≤ s.cash i
  resv_nonneg : ∀ i, 0 ≤ s.resv i
  /-- The slices of a cut good never exceed its price. -/
  pot_nonneg : ∀ g ∈ s.cutSet, 0 ≤ s.pot p g
  /-- The pots are part of the bank. -/
  bank_pot : ∑ g ∈ s.cutSet, s.pot p g ≤ s.bank
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
  /-- A slice is never bigger than the threshold of an agent that is still unserved. -/
  slice_le : ∀ i, s.src i ≠ ∅ → ∀ j, j ∉ s.served → s.cash i ≤ GeneralTPS.thr v p j

end QStage

/-! ### Elementary consequences -/

namespace QStage

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

omit [Fintype G] in
lemma mem_cutSet {s : QStage G n} {g : G} {i : Fin n} (h : g ∈ s.src i) : g ∈ s.cutSet :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩

omit [Fintype G] in
lemma src_subset_cutSet (s : QStage G n) (i : Fin n) : s.src i ⊆ s.cutSet :=
  fun _ hg => mem_cutSet hg

omit [Fintype G] in
lemma own_subset_sold (s : QStage G n) (i : Fin n) : s.own i ⊆ s.sold :=
  fun _ hg => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hg⟩)

omit [Fintype G] in
lemma cutSet_subset_sold (s : QStage G n) : s.cutSet ⊆ s.sold := fun _ hg =>
  Finset.mem_union_right _ hg

omit [Fintype G] in
lemma src_subset_sold (s : QStage G n) (i : Fin n) : s.src i ⊆ s.sold :=
  fun _ hg => cutSet_subset_sold s (mem_cutSet hg)

lemma disjoint_pool_sold (s : QStage G n) : Disjoint s.pool s.sold := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inl hx')

lemma disjoint_pool_bundle (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))

lemma disjoint_pool_own (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.own i) :=
  Finset.disjoint_of_subset_right (own_subset_sold s i) (disjoint_pool_sold s)

lemma disjoint_pool_src (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.src i) :=
  Finset.disjoint_of_subset_right (src_subset_sold s i) (disjoint_pool_sold s)

lemma disjoint_pool_cutSet (s : QStage G n) : Disjoint s.pool s.cutSet :=
  Finset.disjoint_of_subset_right (cutSet_subset_sold s) (disjoint_pool_sold s)

variable {v p eps}

lemma bank_nonneg {s : QStage G n} (hs : s.Good v p eps) : 0 ≤ s.bank := by
  have h1 : 0 ≤ ∑ g ∈ s.cutSet, s.pot p g :=
    Finset.sum_nonneg (fun g hg => hs.pot_nonneg g hg)
  linarith [hs.bank_pot]

lemma freeBank_nonneg_of {s : QStage G n} (hs : s.Good v p eps) : 0 ≤ s.freeBank p := by
  have := hs.bank_pot
  unfold freeBank
  linarith

lemma req_nonneg (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j := by
  unfold req
  by_cases hj : j ∈ s.served
  · rw [if_pos hj]
    have h1 : 0 ≤ vbarSum (v j) p (s.bundle j) :=
      Finset.sum_nonneg (fun g _ => le_trans (hp g) (le_max_left _ _))
    have h2 := hs.cash_nonneg j
    linarith
  · rw [if_neg hj]
    exact GeneralTPS.thr_nonneg v p hn hp j

omit [DecidableEq G] in
lemma req_eq_thr {s : QStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by
  simp [req, hj]

omit [Fintype G] in
/-- The slice an agent holds, together with the pot of its good, does not exceed the price. -/
lemma cash_add_pot_le' {s : QStage G n} (hcn : ∀ i, 0 ≤ s.cash i) {i : Fin n} {g : G}
    (hg : g ∈ s.src i) : s.cash i + s.pot p g ≤ p g := by
  have hmem : i ∈ s.holders g := by simp [holders, hg]
  have h : s.cash i ≤ ∑ m ∈ s.holders g, s.cash m :=
    Finset.single_le_sum (f := s.cash) (fun m _ => hcn m) hmem
  unfold pot
  linarith

lemma cash_add_pot_le {s : QStage G n} (hs : s.Good v p eps) {i : Fin n} {g : G}
    (hg : g ∈ s.src i) : s.cash i + s.pot p g ≤ p g :=
  cash_add_pot_le' hs.cash_nonneg hg

/-- **The cost of a slice holder**, from the local data only. -/
lemma cost_le_of_src' (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} {i : Fin n} {g : G}
    (hb : s.bundle i = ∅) (ho : s.own i = ∅) (hrz : s.resv i = 0) (hsrc : s.src i = {g})
    (hle : s.cash i + s.pot p g ≤ p g) {j : Fin n}
    (hcash : s.cash i ≤ GeneralTPS.thr v p j) :
    s.cost v p i j ≤ 2 * GeneralTPS.thr v p j := by
  have ht := ChargeTPS.TPS_le_two_thr v p hn hp j
  have := slice_cost_le (v j) p (TPS n (v j) p) (GeneralTPS.thr v p j) g (s.cash i)
    (s.pot p g) hle hcash ht
  simp only [cost, hb, ho, hrz, hsrc, truncBundle, Finset.sum_empty, Finset.sum_singleton,
    zero_add, add_zero]
  linarith

/-- The pot of a good that is still in the pool is its whole price. -/
lemma pot_of_pool {s : QStage G n} {g : G} (hg : g ∈ s.pool) : s.pot p g = p g := by
  have hh : s.holders g = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun i hi => ?_)
    simp only [holders, Finset.mem_filter] at hi
    exact Finset.disjoint_left.mp (disjoint_pool_src s i) hg hi.2
  simp [pot, hh]

/-- The threshold never exceeds the requirement. -/
lemma thr_le_req (heps : 0 ≤ eps) {s : QStage G n} (hs : s.Good v p eps) (j : Fin n) :
    GeneralTPS.thr v p j ≤ s.req v p eps j := by
  unfold req
  by_cases hj : j ∈ s.served
  · rw [if_pos hj]; have := hs.share j hj; linarith
  · rw [if_neg hj]

/-- **The cost of a slice holder.**  An agent whose package is a slice of the proceeds of a cut
good costs every unserved agent at most `2τ`. -/
lemma cost_le_of_src (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    {i : Fin n} (hi : s.src i ≠ ∅) {j : Fin n}
    (hcash : s.cash i ≤ GeneralTPS.thr v p j) :
    s.cost v p i j ≤ 2 * GeneralTPS.thr v p j := by
  obtain ⟨hb, ho, hr⟩ := hs.cutter i hi
  obtain ⟨g, hg⟩ : ∃ g, s.src i = {g} := by
    have h1 := hs.src_card i
    have h2 : (s.src i).card ≠ 0 := fun h => hi (Finset.card_eq_zero.mp h)
    exact Finset.card_eq_one.mp (by omega)
  have hgs : g ∈ s.src i := by rw [hg]; simp
  have hle := cash_add_pot_le hs hgs
  have ht := ChargeTPS.TPS_le_two_thr v p hn hp j
  have := slice_cost_le (v j) p (TPS n (v j) p) (GeneralTPS.thr v p j) g (s.cash i)
    (s.pot p g) hle hcash ht
  simp only [cost, hb, ho, hr, hg, truncBundle, Finset.sum_empty, Finset.sum_singleton,
    zero_add, add_zero]
  linarith

/-! ### The pot of a good that has not been cut -/

lemma pot_nonneg' (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps) (g : G) :
    0 ≤ s.pot p g := by
  classical
  by_cases hg : g ∈ s.cutSet
  · exact hs.pot_nonneg g hg
  · have hh : s.holders g = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun i hi => ?_)
      simp only [holders, Finset.mem_filter] at hi
      exact hg (mem_cutSet hi.2)
    simp [pot, hh, hp g]

/-! ### The accounting -/

omit [Fintype G] in
/-- A sum over a union is at most the sum of the sums, for a non-negative summand. -/
lemma sum_biUnion_le {ι : Type*} (T : Finset ι) (u : ι → Finset G) (f : G → ℝ)
    (hf : ∀ g, 0 ≤ f g) : ∑ g ∈ T.biUnion u, f g ≤ ∑ i ∈ T, ∑ g ∈ u i, f g := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 := Finset.sum_union_inter (s₁ := u a) (s₂ := T.biUnion u) (f := f)
      have h2 : 0 ≤ ∑ g ∈ (u a) ∩ (T.biUnion u), f g := Finset.sum_nonneg (fun g _ => hf g)
      linarith

lemma cost_eq_zero_of_notMem {s : QStage G n} (hs : s.Good v p eps) {i : Fin n}
    (hi : i ∉ s.served) (j : Fin n) : s.cost v p i j = 0 := by
  obtain ⟨hb, ho, hc, hcash, hresv⟩ := hs.unserved i hi
  simp [cost, hb, ho, hc, hcash, hresv, truncBundle]

/-- **The accounting theorem.**  The per-agent cost bound implies the counting invariant of
Algorithm 4, with the pots of the cut goods deducted from the bank — each of them capped at the
threshold of the agent the invariant is stated for. -/
theorem qcounting (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    (j : Fin n) (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool
        + (s.bank - ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p j)) := by
  classical
  set w := v j with hw
  set t := TPS n (v j) p with ht
  set τ := GeneralTPS.thr v p j with hτ
  have hτ0 : 0 ≤ τ := GeneralTPS.thr_nonneg v p hn hp j
  set B : Finset G := Finset.univ.biUnion s.bundle with hB
  set OW : Finset G := Finset.univ.biUnion s.own with hOW
  -- the truncated value of everything
  have hUniv : truncBundle w p t Finset.univ = (2 * (n:ℝ) - 1) * τ := by
    rw [GeneralTPS.truncBundle_univ w p hn hp, hτ, hw]
    unfold GeneralTPS.thr
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hne : ((n:ℝ) * 2 - 1) ≠ 0 := ne_of_gt (by linarith)
    field_simp
  -- the universe splits
  have hdisjSB : Disjoint s.sold B := by
    refine Finset.disjoint_left.mpr (fun x hx hxB => ?_)
    simp only [hB, Finset.mem_biUnion, Finset.mem_univ, true_and] at hxB
    obtain ⟨k, hk⟩ := hxB
    exact Finset.disjoint_left.mp (hs.sold_bundle k) hx hk
  have hsplit : truncBundle w p t Finset.univ
      = truncBundle w p t s.pool + truncBundle w p t (s.sold ∪ B) := by
    rw [truncBundle_sdiff w p t (Finset.subset_univ (s.sold ∪ B))]
    rfl
  have hSB : truncBundle w p t (s.sold ∪ B)
      = truncBundle w p t s.sold + truncBundle w p t B :=
    Finset.sum_union hdisjSB
  have hbund : truncBundle w p t B = ∑ i, truncBundle w p t (s.bundle i) := by
    unfold truncBundle
    rw [hB]
    exact Finset.sum_biUnion (fun a _ b _ hab => hs.bundle_disj a b hab)
  -- the sold goods split into the self-financed sales and the cut goods
  have hdisjOWcut : Disjoint OW s.cutSet := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    simp only [hOW, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    simp only [cutSet, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx'
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hx'
    exact Finset.disjoint_left.mp (hs.own_cut a b) ha hb
  have hlosssold : ∑ g ∈ s.sold, saleLoss w p t g
      = (∑ i, ∑ g ∈ s.own i, saleLoss w p t g) + ∑ g ∈ s.cutSet, saleLoss w p t g := by
    show ∑ g ∈ OW ∪ s.cutSet, saleLoss w p t g = _
    rw [Finset.sum_union hdisjOWcut]
    congr 1
    rw [hOW]
    exact Finset.sum_biUnion (fun a _ b _ hab => hs.own_disj a b hab)
  have hsoldtrunc : truncBundle w p t s.sold
      = (∑ g ∈ s.sold, p g) + ∑ g ∈ s.sold, saleLoss w p t g := by
    rw [sum_saleLoss w p t s.sold]; ring
  -- the total cost
  have hcost : ∑ i, s.cost v p i j
      = (∑ i, truncBundle w p t (s.bundle i)) + (∑ i, s.cash i) + (∑ i, s.resv i)
        + (∑ i, ∑ g ∈ s.own i, saleLoss w p t g)
        + ∑ i, ∑ g ∈ s.src i, (saleLoss w p t g + min (s.pot p g) τ) := by
    unfold cost
    rw [← hw, ← ht, ← hτ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  -- the cut goods are charged at least once each
  have hcut : ∑ g ∈ s.cutSet, (saleLoss w p t g + min (s.pot p g) τ)
      ≤ ∑ i, ∑ g ∈ s.src i, (saleLoss w p t g + min (s.pot p g) τ) := by
    refine sum_biUnion_le Finset.univ s.src _ (fun g => ?_)
    have h1 : 0 ≤ saleLoss w p t g := saleLoss_nonneg w p t g
    have h2 : 0 ≤ min (s.pot p g) τ := le_min (pot_nonneg' hp hs g) hτ0
    linarith
  have hcutsplit : ∑ g ∈ s.cutSet, (saleLoss w p t g + min (s.pot p g) τ)
      = (∑ g ∈ s.cutSet, saleLoss w p t g) + ∑ g ∈ s.cutSet, min (s.pot p g) τ :=
    Finset.sum_add_distrib
  have hmoney := hs.money
  have hkey : ∑ i, s.cost v p i j
      ≥ (2 * (n:ℝ) - 1) * τ - truncBundle w p t s.pool
        - (s.bank - ∑ g ∈ s.cutSet, min (s.pot p g) τ) := by
    rw [hcost]
    have h1 : truncBundle w p t s.pool + truncBundle w p t s.sold
        + (∑ i, truncBundle w p t (s.bundle i)) = (2 * (n:ℝ) - 1) * τ := by
      rw [← hUniv, hsplit, hSB, hbund]; ring
    rw [hsoldtrunc, hlosssold] at h1
    linarith [hcut, hcutsplit]
  -- the cost bound, summed
  have hbound : ∑ i, s.cost v p i j ≤ (s.served.card : ℝ) * (2 * τ) := by
    have hsub : ∑ i, s.cost v p i j = ∑ i ∈ s.served, s.cost v p i j := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      exact cost_eq_zero_of_notMem hs hi j
    rw [hsub]
    calc ∑ i ∈ s.served, s.cost v p i j
        ≤ ∑ _i ∈ s.served, (2 * τ) :=
          Finset.sum_le_sum (fun i hi => hs.cost_le i hi j hj)
      _ = (s.served.card : ℝ) * (2 * τ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hexp : (2 * ((n : ℝ) - s.served.card) - 1) * τ
      = (2 * (n:ℝ) - 1) * τ - (s.served.card : ℝ) * (2 * τ) := by ring
  rw [hexp]
  linarith

/-! ### Forgetting the ledger -/

/-- The plain stage underlying a ledger stage: the reserved money is added to the bank. -/
noncomputable def toStage (s : QStage G n) : GeneralTPS.Stage G n :=
  ⟨s.served, s.bundle, s.sold, s.cash, s.bank + ∑ i, s.resv i⟩

omit [Fintype G] in
@[simp] lemma toStage_served (s : QStage G n) : (s.toStage).served = s.served := rfl
omit [Fintype G] in
@[simp] lemma toStage_bundle (s : QStage G n) : (s.toStage).bundle = s.bundle := rfl
omit [Fintype G] in
@[simp] lemma toStage_cash (s : QStage G n) : (s.toStage).cash = s.cash := rfl
omit [Fintype G] in
@[simp] lemma toStage_soldSet (s : QStage G n) : (s.toStage).soldSet = s.sold := rfl

lemma toStage_pool (s : QStage G n) : (s.toStage).pool = s.pool := rfl

omit [Fintype G] in
lemma toStage_total (s : QStage G n) : (s.toStage).total v p = s.total v p := rfl

/-- **The invariant transfers to the plain bookkeeping.** -/
theorem good_toStage (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : (s.toStage).Good v p eps := by
  classical
  have hresvsum : 0 ≤ ∑ i, s.resv i := Finset.sum_nonneg (fun i _ => hs.resv_nonneg i)
  have hbank := bank_nonneg hs
  refine ⟨fun i hi => ⟨(hs.unserved i hi).1, (hs.unserved i hi).2.2.2.1⟩, hs.bundle_disj,
    hs.sold_bundle, hs.cash_nonneg, by show (0:ℝ) ≤ s.bank + ∑ i, s.resv i; linarith, ?_,
    hs.share, ?_, ?_⟩
  · show (∑ i, s.cash i) + (s.bank + ∑ i, s.resv i) = ∑ g ∈ s.sold, p g
    have := hs.money; linarith
  · -- safety
    intro i hi j
    have hreq : s.req v p eps j ≤ (s.toStage).guar v p j + eps := by
      unfold req GeneralTPS.Stage.guar
      by_cases hj : j ∈ s.served
      · simp [hj, toStage]
      · simp [hj, toStage]; linarith
    rcases hs.safe i hi j with h | ⟨h1, h2, h3⟩
    · exact Or.inl (le_trans h hreq)
    · exact Or.inr ⟨h1, h2, fun g hg => le_trans (h3 g hg) hreq⟩
  · -- the counting invariant
    intro j hj
    have h := qcounting hn hp hs j hj
    have h2 : 0 ≤ ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p j) :=
      Finset.sum_nonneg (fun g _ =>
        le_min (pot_nonneg' hp hs g) (GeneralTPS.thr_nonneg v p hn hp j))
    show (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + (s.bank + ∑ i, s.resv i)
    linarith

end QStage

/-! ### The empty stage -/

/-- The stage in which nothing has happened yet. -/
def emptyQStage (G : Type*) (n : ℕ) : QStage G n :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0⟩

theorem good_emptyQStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyQStage G n).Good v p eps := by
  classical
  have hcut : (emptyQStage G n).cutSet = (∅ : Finset G) := by
    ext x; simp [QStage.cutSet, emptyQStage]
  have hsold : (emptyQStage G n).sold = (∅ : Finset G) := by
    ext x; simp [QStage.sold, QStage.cutSet, emptyQStage]
  refine ⟨fun i _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun i j _ => by simp [emptyQStage],
    fun i => by simp [hsold], fun i j _ => by simp [emptyQStage],
    fun i j => by simp [emptyQStage], fun i => by simp [emptyQStage],
    fun i hi => absurd (rfl : (emptyQStage G n).src i = ∅) hi,
    fun i => le_rfl, fun i => le_rfl, ?_, ?_, fun i => by simp [emptyQStage], ?_, ?_, ?_, ?_,
    fun i hi => absurd (rfl : (emptyQStage G n).src i = ∅) hi⟩
  · intro g hg; rw [hcut] at hg; exact absurd hg (by simp)
  · rw [hcut]; simp [emptyQStage]
  · rw [hsold]; simp [emptyQStage]
  · intro i hi; exact absurd hi (by simp [emptyQStage])
  · intro i hi; exact absurd hi (by simp [emptyQStage])
  · intro i hi; exact absurd hi (by simp [emptyQStage])

/-! ### The improvement step and the descent -/

/-- **The improvement step**: from a good stage in which some agent is still unserved one can
pass to a good stage in which either one more agent holds a bundle, or the total utility has
increased by at least `ε`. -/
def QImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : QStage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))

section Descent

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem qtotal_le_bound (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p :=
  GeneralTPS.total_le_bound v p eps hp (QStage.good_toStage hn hp heps hs)

theorem qtotal_nonneg (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p :=
  GeneralTPS.total_nonneg v p eps hp (QStage.good_toStage hn hp heps hs)

/-- The inner descent: with the number of unserved agents fixed, the total utility increases by
at least `ε` at every step and is bounded. -/
theorem qdescent_inner (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : QImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : QStage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : QStage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      GeneralTPS.totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
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
      have h1 := qtotal_le_bound v p eps hn hp heps.le hs'
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
theorem qdescent (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : QImprovementStep v p eps) :
    ∀ (c : ℕ) (s : QStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
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
    refine qdescent_inner v p eps hn hp heps hstep c ihc b s hs hc ?_
    have := qtotal_nonneg v p eps hn hp heps.le hs
    linarith

end Descent

/-! ### The reduction to Theorem 2 -/

/-- **Theorem 2 (SEFX half) reduces to the ledger improvement step.** -/
theorem exists_TPS_SEFX_of_Qstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → QImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS_u v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨s0, hs0, hs0full⟩ := qdescent v p eps hn hp heps (hstep eps heps) n
    (emptyQStage G n) (good_emptyQStage v p eps) (by simp [emptyQStage])
  set s := s0.toStage with hsdef
  have hs : s.Good v p eps := QStage.good_toStage hn hp heps.le hs0
  have hfulls : s.served = Finset.univ := hs0full
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :
      ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
        (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
        (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
        (∀ i j, GeneralTPS.CSafeU v p eps A q i j) := by
    refine ⟨s.bundle, s.soldSet, s.cash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_, ?_⟩
    · have := hs.2.2.2.2.2.1
      have hb := hs.2.2.2.2.1
      linarith
    · intro i
      exact hs.2.2.2.2.2.2.1 i (by rw [hfulls]; exact Finset.mem_univ i)
    · exact GeneralTPS.csafeU_of_full v p eps hs hfulls
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, GeneralTPS.epsSEFXu_unifiedOutcome v p eps A F q hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  have hTPS : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
  nlinarith [hserve i]

end PotTPS

end FairSelling
