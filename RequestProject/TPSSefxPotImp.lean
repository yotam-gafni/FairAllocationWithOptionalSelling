import Mathlib
import RequestProject.TPSSefxPotStep
import RequestProject.TPSSefxStep

/-!
# The improvement step of Algorithm 6, with the per-good ledger

Algorithm 6 of the manuscript is a loop with three bodies.  With the per-good ledger of
`RequestProject/TPSSefxPot.lean` they become:

1. **`qsell_step`** — the *large-good loops*: a pool good `g` that is expensive for some agent
   that is still unserved is sold, and the claimant receives the least slice `Qc(∅)` of the
   proceeds that makes somebody claim it.  The rest of the proceeds stays in the **pot of `g`**,
   available only to cut further slices of `g`.
2. **`qcut_step`** — cutting a further slice out of a pot that is already large enough to serve
   somebody.  This is what keeps the pots small, and it is what makes the deduction in the
   counting invariant harmless when it comes to bag filling.
3. **`qbagfill_step`** — the bag-filling loop, run on the pool with the *free* bank
   `freeBank = bank − ∑ pot`.  It is feasible (`qfeas_pool`) exactly because every pot is by
   then below the requirement of every unserved agent, so that the capped deduction
   `min (pot g) τⱼ` of the counting invariant is the whole pot.

Unlike the anonymous-bank version of `RequestProject/TPSSefxPhaseImp.lean`, no step needs the
claimant to be free of a shared good: `qstep_assign` releases a slice unconditionally.
-/

open scoped BigOperators

namespace FairSelling

namespace PotTPS

open ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

section Step

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-! ### Feasibility of the pool -/

/-- **The pool is feasible for the free bank**, provided every pot is below the threshold of the
unserved agent `k0`.  This is the counting invariant `qcounting`: the deduction it makes for the
cut goods is capped at `τ`, and when every pot is below `τ` that deduction is exactly the money
the pots hold back, so what is left is the free bank. -/
theorem qfeas_pool (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served)
    (hsmall : ∀ g ∈ s.cutSet, s.pot p g ≤ GeneralTPS.thr v p k0) :
    CfgTPS.Feas v p (s.req v p eps) k0 (s.freeBank p) s.pool ∅ := by
  classical
  have hcount := QStage.qcounting hn hp hs k0 hk0
  have hthr : 0 ≤ GeneralTPS.thr v p k0 := GeneralTPS.thr_nonneg v p hn hp k0
  have hmin : ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p k0)
      = ∑ g ∈ s.cutSet, s.pot p g :=
    Finset.sum_congr rfl (fun g hg => min_eq_left (hsmall g hg))
  have hcard : (s.served.card : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : s.served.card < n := by
      have h2 : s.served ⊂ Finset.univ :=
        ⟨Finset.subset_univ _, fun h => hk0 (h (Finset.mem_univ k0))⟩
      simpa using Finset.card_lt_card h2
    have : (s.served.card : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hmul : GeneralTPS.thr v p k0
      ≤ (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p k0 := by nlinarith
  have hle : truncBundle (v k0) p (TPS n (v k0) p) s.pool ≤ vbarSum (v k0) p s.pool :=
    truncBundle_le_vbarSum _ _ _ _
  have hreq : s.req v p eps k0 = GeneralTPS.thr v p k0 := QStage.req_eq_thr hk0
  have hfreeeq : s.freeBank p = s.bank - ∑ g ∈ s.cutSet, s.pot p g := rfl
  unfold CfgTPS.Feas
  simp only [Finset.sum_empty, add_zero]
  refine CfgTPS.Qc_le_of_gap v p (s.req v p eps) k0 (QStage.freeBank_nonneg_of hs) k0 ?_
  rw [hreq, hfreeeq]
  rw [hmin] at hcount
  linarith

/-! ### The large-good loops: the moving knife -/

/-- **Cutting a further slice out of an existing pot.**  If the pot of a cut good `g0` is large
enough to serve the claimant, the claimant receives a slice of it.  Nothing is sold, and the
claimant's old package — if it had one — is released. -/
theorem qcut_step (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) (k0 : Fin n) {g0 : G} (hg0 : g0 ∈ s.cutSet)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.pot p g0) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set q := CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) with hqdef
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 (∅ : Finset G)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hqreq : ∀ m, q ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  have hq0 : 0 ≤ q := CfgTPS.Qc_nonneg v p (s.req v p eps) k0 _
  have hclaim' : s.req v p eps k ≤ vbarSum (v k) p ∅ + q := by simpa [vbarSum] using hclaim
  refine qstep_assign v p eps hn hp heps hs (S := ∅) (S₀ := ∅) (Src := {g0}) (Snew := ∅)
    (by simp) (by simp) (by simp) hq0 le_rfl (by simp) (fun _ => ⟨rfl, rfl, rfl⟩)
    (Or.inl rfl) (fun _ => Finset.singleton_subset_iff.mpr hg0) ?_ ?_ (by simp) (by simpa using hq0)
    hclaim' (by simp) ?_ (by simp)
  · intro g hg
    rw [Finset.mem_singleton.mp hg]
    exact hqle
  · intro _ j hj
    have h1 := hqreq j
    rwa [QStage.req_eq_thr hj] at h1
  · intro j _
    left
    simpa [vbarSum] using hqreq j

/-- **Selling an expensive pool good and cutting a slice of its proceeds.**  The good `g0` is
sold, the claimant receives the least slice `Qc(∅)` of its proceeds that makes somebody claim
it, and the rest of the proceeds goes into the **pot of `g0`**, from which further slices of
`g0` — and nothing else — may later be cut. -/
theorem qsell_step (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) (k0 : Fin n) {g0 : G} (hg0 : g0 ∈ s.pool)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ p g0) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set q := CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) with hqdef
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 (∅ : Finset G)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hqreq : ∀ m, q ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  have hq0 : 0 ≤ q := CfgTPS.Qc_nonneg v p (s.req v p eps) k0 _
  have hclaim' : s.req v p eps k ≤ vbarSum (v k) p ∅ + q := by simpa [vbarSum] using hclaim
  refine qstep_assign v p eps hn hp heps hs (S := ∅) (S₀ := ∅) (Src := {g0}) (Snew := {g0})
    (by simp) (by simp) (by simp) hq0 le_rfl (by simp) (fun _ => ⟨rfl, rfl, rfl⟩)
    (Or.inr ⟨rfl, Finset.singleton_subset_iff.mpr hg0⟩) (by simp) ?_ ?_ (by simp)
    (by simpa using hq0) hclaim' (by simp) ?_ (by simp)
  · intro g hg
    rw [Finset.mem_singleton.mp hg, QStage.pot_of_pool hg0]
    exact hqle
  · intro _ j hj
    have h1 := hqreq j
    rwa [QStage.req_eq_thr hj] at h1
  · intro j _
    left
    simpa [vbarSum] using hqreq j

/-! ### The bag-filling loop -/

/-- **The bag-filling step of Algorithm 6.**  When no pool good is expensive for an unserved
agent, the pool is filled into a bag out of the *free* bank, the bag is shrunk to a minimal
admissible package, and the package is handed to its claimant; if the claimant already holds a
package it is released first (`Unshrink`).  Everything the new owner sells is financed out of
its own package. -/
theorem qbagfill_step (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    (hfeas : CfgTPS.Feas v p (s.req v p eps) k0 (s.freeBank p) s.pool ∅)
    (hcheap : ∀ g ∈ s.pool, ∀ j, j ∉ s.served → p g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set D : ℝ := s.freeBank p with hDdef
  obtain ⟨S, S₀, hUP, hdisj, hadm, hmin⟩ :=
    CfgTPS.exists_min_adm v p (s.req v p eps) k0 D s.pool hp hfeas
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 S
  obtain ⟨S', S₀', q, hS'S, hS₀S₀', hfoot, hdisj', hq0, hqle, hclaim', hkeep, hsafe, hcosteq⟩ :=
    ChargeTPS.package_of_claimant v p (s.req v p eps) k0 D hp hdisj hadm k hclaim
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hD0 : 0 ≤ D := QStage.freeBank_nonneg_of hs
  set A : ℝ := ∑ x ∈ S₀', p x with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => hp x
  set r : ℝ := max 0 (A - q) with hrdef
  have hr0 : 0 ≤ r := le_max_left _ _
  have hqr : q + r = max q A := by
    rcases le_or_gt A q with h | h
    · rw [hrdef, max_eq_left (by linarith : A - q ≤ 0), max_eq_left h, add_zero]
    · rw [hrdef, max_eq_right (by linarith : (0:ℝ) ≤ A - q), max_eq_right h.le]; ring
  have hS'P : S' ⊆ s.pool :=
    Finset.Subset.trans (Finset.Subset.trans hS'S Finset.subset_union_left) hUP
  have hS₀'P : S₀' ⊆ s.pool := fun x hx => hUP (hfoot ▸ Finset.mem_union_right S' hx)
  refine qstep_assign v p eps hn hp heps hs (S := S') (S₀ := S₀') (Src := ∅) (Snew := ∅)
    hS'P hS₀'P hdisj' hq0 hr0 (by simp) (by simp) (Or.inl rfl) (by simp) (by simp) (by simp)
    ?_ ?_ hclaim' hkeep (fun j _ => hsafe j) ?_
  · -- the package is affordable out of the free bank
    intro _
    rw [hqr, ← hAdef]
    rcases le_or_gt A q with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  · -- the sales are self-financed
    rw [hqr, ← hAdef]
    exact le_max_right _ _
  · -- the cost bound
    intro _ j hj
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have hreqj : s.req v p eps j = GeneralTPS.thr v p j := QStage.req_eq_thr hjs
    have hthrj : 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp j
    rcases le_or_gt A q with hAq | hAq
    · have hr0' : r = 0 := by rw [hrdef, max_eq_left (by linarith : A - q ≤ 0)]
      have hcost := CfgTPS.cost_bound (w := v) (p := p) (req := s.req v p eps) (k0 := k0)
        (D := D) (P := s.pool) (S := S) (S₀ := S₀)
        (fun i => TPS n (v i) p) j hp hD0 hreq0
        (by rw [hreqj]; exact ChargeTPS.thr_le_TPS v p hn hp j)
        (by rw [hreqj]; exact ChargeTPS.TPS_le_two_thr v p hn hp j)
        hUP hdisj hadm hmin
      rw [hreqj] at hcost
      have heq := hcosteq (TPS n (v j) p) (v j)
      rw [hr0']
      linarith
    · have hr0' : r = A - q := by rw [hrdef, max_eq_right (by linarith : (0:ℝ) ≤ A - q)]
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
          (fun i => TPS n (v i) p) j hp hD0 hUP hmin hcard
        rw [hreqj] at h2
        linarith
      · have hS₀ne : S₀'.Nonempty := by
          rcases Finset.eq_empty_or_nonempty S₀' with he | he
          · exfalso
            rw [he] at hAdef
            simp only [Finset.sum_empty] at hAdef
            rw [hAdef] at hAq; linarith
          · exact he
        obtain ⟨x, hx⟩ := hS₀ne
        have hxU : x ∈ S ∪ S₀ := hfoot ▸ Finset.mem_union_right S' hx
        have hcard1 : (S ∪ S₀).card = 1 := by
          have : 1 ≤ (S ∪ S₀).card := Finset.card_pos.mpr ⟨x, hxU⟩
          omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard1
        have hxy : x = y := by rw [hy] at hxU; simpa using hxU
        subst hxy
        have hxP : x ∈ s.pool := hS₀'P hx
        have hpx : p x ≤ 2 * GeneralTPS.thr v p j := hcheap x hxP j hjs
        have htx : TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j :=
          ChargeTPS.TPS_le_two_thr v p hn hp j
        have h1 : trunc (v j) p (TPS n (v j) p) x ≤ max (p x) (TPS n (v j) p) :=
          trunc_le_max _ _ _ _
        rw [hy]
        simp only [truncBundle, Finset.sum_singleton]
        rcases max_cases (p x) (TPS n (v j) p) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;>
          linarith

/-! ### Algorithm 6 -/

/-- **The improvement step of Algorithm 6**, in the manuscript's order.

1. If some pool good is expensive for an agent that is still unserved, it is sold and a slice of
   its proceeds is cut for the claimant (`qsell_step`).
2. Otherwise, if some pot is already big enough to serve the claimant, a further slice is cut
   out of it (`qcut_step`).
3. Otherwise every pot is below the requirement of every unserved agent, the whole pool is
   feasible for the free bank (`qfeas_pool`), and one bag-filling step is performed
   (`qbagfill_step`). -/
theorem qimprovementStep (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) :
    QImprovementStep v p eps := by
  classical
  intro s hs hfull
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ s.served := by
    by_contra hcon
    push_neg at hcon
    exact hfull (Finset.eq_univ_of_forall hcon)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hqreq : ∀ m, CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  by_cases hbig : ∃ g ∈ s.pool, ∃ j, j ∉ s.served ∧ 2 * GeneralTPS.thr v p j < p g
  · obtain ⟨g, hg, j0, hj0, hbg⟩ := hbig
    have h1 : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ GeneralTPS.thr v p j0 := by
      have := hqreq j0
      rwa [QStage.req_eq_thr hj0] at this
    have h2 : 0 ≤ GeneralTPS.thr v p j0 := GeneralTPS.thr_nonneg v p hn hp j0
    exact qsell_step v p eps hn hp heps hs k0 hg (by linarith)
  · push_neg at hbig
    by_cases hA : ∃ g0 ∈ s.cutSet, CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.pot p g0
    · obtain ⟨g0, hg0, hle⟩ := hA
      exact qcut_step v p eps hn hp heps hs k0 hg0 hle
    · push_neg at hA
      have hsmall : ∀ g ∈ s.cutSet, s.pot p g ≤ GeneralTPS.thr v p k0 := by
        intro g hg
        have h1 := hA g hg
        have h2 := hqreq k0
        rw [QStage.req_eq_thr hk0] at h2
        linarith
      exact qbagfill_step v p eps hn hp heps hs (qfeas_pool v p eps hn hp hs hk0 hsmall) hbig

end Step

end PotTPS

end FairSelling
