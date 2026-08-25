import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.ThreeAgents
import RequestProject.TPSApprox
import RequestProject.TwoThirdsCanonical
import RequestProject.EquiMMS

/-!
# The invariant of the `2/3`-MMS algorithm: loss events

This file sets up the bookkeeping that the analysis of the manuscript's Algorithm 1 maintains
along the run: Definition 7 (the four *loss types*), the state invariant, and the two statements
that drive the induction, namely

* **Proposition 5** — the invariant is preserved by one round of the main loop
  (`losses_of_round`), and by the two stages of the preliminary phase (`losses_of_stage1`,
  `losses_of_stage2`);
* **Lemma 9** — at every step of the main loop, the active agent of highest maximin share has a
  canonical partition of the available resources (`canonical_of_inv`).

Proposition 5 is proved here.  Lemma 9 is the combinatorial heart of the proof of Theorem 3; it
is proved in `RequestProject.TwoThirdsLemma9`.

The analysis assumes that every agent has an MMS partition all of whose parts are worth *exactly*
its maximin share (`EquiMMS`, Definition 5, in the normalized form of Lemma 5: the money of the
sold goods is split over the parts).  Such a partition need not exist for the original valuations
— with two agents and three goods worth `10, 6, 6` and no market, the maximin share is `10` and
no partition has both parts worth exactly `10` — which is why the valuations are first readjusted
downwards; this is Lemma 6, proved in `RequestProject.EquiMMS` as `exists_readjustment`.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The threshold -/

/-- The approximation ratio of the general-`n` part of Theorem 3. -/
noncomputable def rho : ℝ := 2 / 3

/-- The acceptance threshold of agent `i`: `ρ · MMSᵢ`.  A bundle is *acceptable* to `i` when it is
worth at least `thr i` to it. -/
noncomputable def thr (v : Fin n → G → ℝ) (p : G → ℝ) (i : Fin n) : ℝ := rho * MMS n (v i) p

lemma thr_nonneg (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) (i : Fin n) : 0 ≤ thr v p i :=
  mul_nonneg (by norm_num [rho]) (MMS_nonneg hn (v i) p (hv i) hp)

omit [Fintype G] [DecidableEq G] in
lemma thr_le_thr (v : Fin n → G → ℝ) (p : G → ℝ) {i j : Fin n}
    (h : MMS n (v i) p ≤ MMS n (v j) p) : thr v p i ≤ thr v p j := by
  unfold thr rho
  have : (0:ℝ) ≤ 2 / 3 := by norm_num
  nlinarith

/-! ### Definition 7: the four loss types

A round of the algorithm removes from the pool a set `E` of goods (those handed out with the
bundle that was allocated), a set `F` of goods that were force-sold in order to fund that bundle,
and an amount `c` of money (the money handed out with the bundle).  Each of the four definitions
below describes such a triple from the point of view of a still-active agent with valuation `w`,
set `S` of goods it intends to sell, and threshold `t = ρ·MMS`. -/

/-- Loss of type `ℓ₁`: a single good `e`, which the agent did not intend to sell, leaves the
pool; either it is handed over as the whole bundle (and then no money is handed out with it), or
it is sold and at most its price is handed out.

The manuscript states `ℓ₁` for the first case only ("the bundle `B` contains only one good `e`
and no money, and `e ∉ Sᵢ`"), but uses it in the second one as well: the first stage of the
preliminary phase sells the good `e` and hands out money, and the proof of Lemma 9 describes an
`ℓ₁` loss as "a single good `e ∉ Sᵢ` is sold".  Both readings are covered here. -/
def LossL1 (p : G → ℝ) (S : Finset G) (E F : Finset G) (c : ℝ) : Prop :=
  ∃ e, e ∉ S ∧ ((E = {e} ∧ F = ∅ ∧ c = 0) ∨ (E = ∅ ∧ F = {e} ∧ c ≤ p e))

/-- Loss of type `ℓ₂`: the bundle is worth at most `t` to the agent, and it contains no money
received from selling a good that the agent values above its price, unless the agent intended to
sell that good anyway. -/
def LossL2 (w p : G → ℝ) (S : Finset G) (t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  vbarSum w p E + c ≤ t ∧ (∀ f ∈ F, w f ≤ p f ∨ f ∈ S)

/-- Loss of type `ℓ₃`: the bundle consists of one good `e` and of part of the money received from
selling a good `f`; both have `v̄` value at most `t` and neither is a good the agent intended to
sell.

The condition `μ - t ≤ p f` is not part of the manuscript's list, but the manuscript's own bound
on the loss of an `ℓ₃` event uses it: the loss is estimated as
`v̄(B) + v(f) - p(f) ≤ ρ·μ + v(f) - (1-ρ)·μ`, which is exactly the substitution
`p f ≥ (1-ρ)·μ = μ - t`.  It holds because `f` was sold by the algorithm only because it belonged
to the sell set of the *proposing* agent, whose maximin share is the largest among the active
agents, and canonicity condition 1 bounds the price of such a good from below.

The last conjunct, `v̄(E) + c ≤ t`, is the manuscript's "the value of the singleton part `Bⱼ`
containing `eⱼ` that was allocated … is at most `ρ·MMSₖ` (because `Bⱼ` was not acceptable for
agent `k`)"; it is used in the same estimate. -/
def LossL3 (w p : G → ℝ) (S : Finset G) (μ t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  (∃ e, E = {e} ∧ e ∉ S ∧ vbar w p e ≤ t) ∧
  (∃ f, F = {f} ∧ f ∉ S ∧ vbar w p f ≤ t ∧ c ≤ p f ∧ μ - t ≤ p f) ∧ 0 ≤ c ∧
  vbarSum w p E + c ≤ t

/-- Loss of type `ℓ₄`: as `ℓ₃`, except that the good `e` of the bundle is one the agent intended
to sell (and it was not sold). -/
def LossL4 (w p : G → ℝ) (S : Finset G) (μ t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  (∃ e, E = {e} ∧ e ∈ S ∧ vbar w p e ≤ t) ∧
  (∃ f, F = {f} ∧ f ∉ S ∧ vbar w p f ≤ t ∧ c ≤ p f ∧ μ - t ≤ p f) ∧ 0 ≤ c ∧
  vbarSum w p E + c ≤ t

/-- Definition 7: a loss event is of one of the four types. -/
def LossOK (w p : G → ℝ) (S : Finset G) (μ t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  LossL1 p S E F c ∨ LossL2 w p S t E F c ∨ LossL3 w p S μ t E F c ∨ LossL4 w p S μ t E F c

/-! ### The state invariant -/

/-- **Proposition 5.**  The state `(T, R, D)` — active agents `T`, available goods `R`, banked
money `D` — is *accounted for*: to every agent `b` that has already been served corresponds one
loss event, consisting of the goods `alloc b` that were handed to it, the goods `sold b` that
were sold in that round and the money `paid b` that was handed out; these events cover exactly
the goods that are no longer available, the money handed out is accounted for by the proceeds of
the goods that were sold, and every event is, for every still-active agent, a loss of one of the
four types of Definition 7 relative to an equi-valued MMS partition of that agent.  (Agents that
are still active carry the empty event.) -/
def Losses (v : Fin n → G → ℝ) (p : G → ℝ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ) : Prop :=
  ∃ (alloc sold : Fin n → Finset G) (paid : Fin n → ℝ),
    (∀ b ∈ T, alloc b = ∅ ∧ sold b = ∅ ∧ paid b = 0) ∧
    (∀ b, Disjoint (alloc b) (sold b)) ∧
    (∀ b b', b ≠ b' → Disjoint (alloc b ∪ sold b) (alloc b' ∪ sold b')) ∧
    (∀ b, Disjoint R (alloc b ∪ sold b)) ∧
    (Finset.univ = R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b)) ∧
    (∀ b, 0 ≤ paid b) ∧
    ((∑ b, ∑ g ∈ sold b, p g) - ∑ b, paid b ≤ D) ∧
    (∀ i ∈ T, ∃ E : EquiMMS (v i) p (MMS n (v i) p) n,
      ∀ b ∉ T, LossOK (v i) p E.sell (MMS n (v i) p) (thr v p i) (alloc b) (sold b) (paid b))

/-- The invariant of the main loop: the state is accounted for, the bank is non-negative and — the
outcome of the preliminary phase, Proposition 4 — no available good is worth as much as the
threshold to an active agent. -/
def Inv (v : Fin n → G → ℝ) (p : G → ℝ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ) : Prop :=
  0 ≤ D ∧ Losses v p T R D ∧ ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < thr v p i

/-- At the start of the algorithm nothing has been allocated, and the state is accounted for by
the empty history. -/
theorem losses_initial (v : Fin n → G → ℝ) (p : G → ℝ)
    (hE : ∀ i, Nonempty (EquiMMS (v i) p (MMS n (v i) p) n)) :
    Losses v p Finset.univ Finset.univ (0 : ℝ) := by
  classical
  refine ⟨fun _ => ∅, fun _ => ∅, fun _ => 0, fun b _ => ⟨rfl, rfl, rfl⟩, fun b => by simp,
    fun b b' _ => by simp, fun b => by simp, by simp, fun b => le_refl 0, by simp, ?_⟩
  intro i _
  obtain ⟨E⟩ := hE i
  exact ⟨E, fun b hb => absurd (Finset.mem_univ b) hb⟩

omit [Fintype G] [DecidableEq G] in
private lemma sum_ite_mem_split {M : Type*} [AddCommMonoid M] (K : Finset (Fin n))
    (x y : Fin n → M) :
    ∑ b, (if b ∈ K then x b else y b) = (∑ b ∈ K, x b) + ∑ b ∈ Finset.univ \ K, y b := by
  classical
  rw [← Finset.sum_sdiff (Finset.subset_univ K), add_comm]
  congr 1
  · exact Finset.sum_congr rfl (fun b hb => by simp [hb])
  · exact Finset.sum_congr rfl (fun b hb => by simp [(Finset.mem_sdiff.mp hb).2])

/-- **Extending the accounting by one round.**  The agents of `Kset` are served: agent `b` gets
the goods `Ea b` and `ca b` units of money, and the goods `Fa b` are sold in the process.  If
every still-active agent sees each of these events as a loss of one of the four types, the new
state is accounted for. -/
theorem losses_extend_set (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D) {Kset : Finset (Fin n)} (hKT : Kset ⊆ T)
    (Ea Fa : Fin n → Finset G) (ca : Fin n → ℝ)
    (hEsub : ∀ b ∈ Kset, Ea b ⊆ R) (hFsub : ∀ b ∈ Kset, Fa b ⊆ R)
    (hEF : ∀ b ∈ Kset, Disjoint (Ea b) (Fa b))
    (hpair : ∀ b ∈ Kset, ∀ b' ∈ Kset, b ≠ b' → Disjoint (Ea b ∪ Fa b) (Ea b' ∪ Fa b'))
    (hc0 : ∀ b ∈ Kset, 0 ≤ ca b)
    (htype : ∀ i ∈ T \ Kset, ∀ Ei : EquiMMS (v i) p (MMS n (v i) p) n, ∀ b ∈ Kset,
      LossOK (v i) p Ei.sell (MMS n (v i) p) (thr v p i) (Ea b) (Fa b) (ca b)) :
    Losses v p (T \ Kset) (R \ Kset.biUnion (fun b => Ea b ∪ Fa b))
      (D + (∑ b ∈ Kset, ∑ g ∈ Fa b, p g) - ∑ b ∈ Kset, ca b) := by
  classical
  obtain ⟨alloc, sold, paid, hempty, hdisj1, hdisj2, hdisjR, hcover, hpaid0, hmoney, htypes⟩ := hL
  set U : Finset G := Kset.biUnion (fun b => Ea b ∪ Fa b) with hU
  have hUR : U ⊆ R := by
    intro g hg
    obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.mp hg
    rcases Finset.mem_union.mp hgb with h | h
    · exact hEsub b hb h
    · exact hFsub b hb h
  have hsubU : ∀ b ∈ Kset, Ea b ∪ Fa b ⊆ U := fun b hb g hg => Finset.mem_biUnion.mpr ⟨b, hb, hg⟩
  refine ⟨fun b => if b ∈ Kset then Ea b else alloc b, fun b => if b ∈ Kset then Fa b else sold b,
    fun b => if b ∈ Kset then ca b else paid b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hbK : b ∉ Kset := (Finset.mem_sdiff.mp hb).2
    simp only [if_neg hbK]
    exact hempty b (Finset.mem_sdiff.mp hb).1
  · intro b
    by_cases hb : b ∈ Kset
    · simp only [if_pos hb]; exact hEF b hb
    · simp only [if_neg hb]; exact hdisj1 b
  · intro b b' hbb
    by_cases hb : b ∈ Kset <;> by_cases hb' : b' ∈ Kset
    · simp only [if_pos hb, if_pos hb']; exact hpair b hb b' hb' hbb
    · simp only [if_pos hb, if_neg hb']
      exact Finset.disjoint_of_subset_left ((hsubU b hb).trans hUR) (hdisjR b')
    · simp only [if_neg hb, if_pos hb']
      exact (Finset.disjoint_of_subset_left ((hsubU b' hb').trans hUR) (hdisjR b)).symm
    · simp only [if_neg hb, if_neg hb']; exact hdisj2 b b' hbb
  · intro b
    by_cases hb : b ∈ Kset
    · simp only [if_pos hb]
      exact Finset.disjoint_of_subset_right (hsubU b hb) Finset.sdiff_disjoint
    · simp only [if_neg hb]
      exact Finset.disjoint_of_subset_left Finset.sdiff_subset (hdisjR b)
  · ext g
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_iff, Finset.mem_sdiff]
    have hg : g ∈ R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b) := by
      rw [← hcover]; exact Finset.mem_univ g
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hg
    by_cases hgU : g ∈ U
    · obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.mp hgU
      refine Or.inr ⟨b, ?_⟩
      simp only [if_pos hb]
      exact ⟨trivial, Finset.mem_union.mp hgb⟩
    · rcases hg with hgR | ⟨b, hb⟩
      · exact Or.inl ⟨hgR, hgU⟩
      · by_cases hbK : b ∈ Kset
        · exfalso
          have := hempty b (hKT hbK)
          rw [this.1, this.2.1] at hb
          simp at hb
        · exact Or.inr ⟨b, by simp only [if_neg hbK]; exact ⟨trivial, hb⟩⟩
  · intro b
    by_cases hb : b ∈ Kset
    · simp only [if_pos hb]; exact hc0 b hb
    · simp only [if_neg hb]; exact hpaid0 b
  · have hsold : ∑ b, ∑ g ∈ (if b ∈ Kset then Fa b else sold b), p g
        = (∑ b ∈ Kset, ∑ g ∈ Fa b, p g) + ∑ b, ∑ g ∈ sold b, p g := by
      have h1 : ∑ b, ∑ g ∈ (if b ∈ Kset then Fa b else sold b), p g
          = ∑ b, (if b ∈ Kset then ∑ g ∈ Fa b, p g else ∑ g ∈ sold b, p g) :=
        Finset.sum_congr rfl (fun b _ => by by_cases hb : b ∈ Kset <;> simp [hb])
      rw [h1, sum_ite_mem_split]
      congr 1
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have : ∑ b ∈ Kset, ∑ g ∈ sold b, p g = 0 :=
        Finset.sum_eq_zero (fun b hb => by rw [(hempty b (hKT hb)).2.1]; simp)
      rw [this]; ring
    have hpd : ∑ b, (if b ∈ Kset then ca b else paid b) = (∑ b ∈ Kset, ca b) + ∑ b, paid b := by
      rw [sum_ite_mem_split]
      congr 1
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have : ∑ b ∈ Kset, paid b = 0 :=
        Finset.sum_eq_zero (fun b hb => (hempty b (hKT hb)).2.2)
      rw [this]; ring
    rw [hsold, hpd]
    linarith
  · intro i hi
    obtain ⟨Ei, hEi⟩ := htypes i (Finset.mem_sdiff.mp hi).1
    refine ⟨Ei, ?_⟩
    intro b hb
    by_cases hbK : b ∈ Kset
    · simp only [if_pos hbK]
      exact htype i hi Ei b hbK
    · simp only [if_neg hbK]
      refine hEi b (fun hbT => hb (Finset.mem_sdiff.mpr ⟨hbT, hbK⟩))

/-- Extending the accounting by a single event. -/
theorem losses_extend (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D) {a : Fin n} (ha : a ∈ T)
    (E F : Finset G) (c : ℝ) (hE : E ⊆ R) (hF : F ⊆ R) (hEF : Disjoint E F) (hc : 0 ≤ c)
    (htype : ∀ i ∈ T.erase a, ∀ Ei : EquiMMS (v i) p (MMS n (v i) p) n,
      LossOK (v i) p Ei.sell (MMS n (v i) p) (thr v p i) E F c) :
    Losses v p (T.erase a) (R \ (E ∪ F)) (D + (∑ g ∈ F, p g) - c) := by
  classical
  have key := losses_extend_set v p hL (Kset := {a}) (by simpa using ha)
    (fun _ => E) (fun _ => F) (fun _ => c) (fun b _ => hE) (fun b _ => hF) (fun b _ => hEF)
    (fun b hb b' hb' hbb => absurd (by rw [Finset.mem_singleton.mp hb,
      Finset.mem_singleton.mp hb']) hbb)
    (fun b _ => hc) ?_
  · have h1 : T \ ({a} : Finset (Fin n)) = T.erase a := by
      rw [Finset.erase_eq]
    have h2 : ({a} : Finset (Fin n)).biUnion (fun _ => E ∪ F) = E ∪ F := by simp
    rw [h1, h2] at key
    simpa using key
  · intro i hi Ei b _
    exact htype i (by rwa [Finset.erase_eq]) Ei

/-! ### Lemma 9

**Lemma 9** — for `ρ = 2/3` a canonical partition exists at every step of the main part of the
algorithm — used to be stated here as an unproved statement.  It is now *proved*, in
`RequestProject.TwoThirdsLemma9` (`canonical_of_inv`), out of the accounting of
`RequestProject.TwoThirdsBudget` and the combinatorial descent of
`RequestProject.TwoThirdsDescent`. -/

/-! ### Proposition 5 -/

/-- **Proposition 5, one round of the main loop.**  If the state before the round is accounted
for and no available good is worth as much as its threshold to an active agent, and if the round
serves the agents of `Kset` with the parts `part` of a canonical partition `C` of agent `i`, then
the state after the round is accounted for.

Each served agent `b` accounts for the goods `C.goods (part b)` of its part and for the money
`C.cash (part b)` handed out with it; the good sold to fund the part (if any) is charged to the
first — in the order of `Fin n` — of the served agents whose part it funds, so that the events
are pairwise disjoint.

The classification of Definition 7 is then: an event with no sold good is of type `ℓ₂`, because
a still-active agent finds the part unacceptable (`hloss`); an event whose sold good `f` the
still-active agent intended to sell anyway is again of type `ℓ₂`; and otherwise the part is not
the special part, hence — by condition 2 of canonicity — is a singleton `{e}` funded entirely by
the sale of `f`, which is a loss of type `ℓ₃` (if `e` is not a good the agent intended to sell)
or `ℓ₄` (if it is). -/
theorem losses_of_round (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hInv : Inv v p T R D) {i : Fin n}
    (hmax : ∀ a ∈ T, MMS n (v a) p ≤ MMS n (v i) p)
    {k : ℕ} [NeZero k] (C : Canonical (v i) p (MMS n (v i) p) (thr v p i) k R D)
    (Kset : Finset (Fin n)) (part : Fin n → Fin k) (hKT : Kset ⊆ T)
    (hinj : Set.InjOn part Kset)
    (hloss : ∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
      vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < thr v p a)
    (hspecial : ∀ a ∈ Kset, a ≠ i → part a ≠ 0) (hzero : Kset = T ∨ part i ≠ 0) :
    Losses v p (T \ Kset)
      (R \ ((Kset.image part).biUnion C.goods ∪ C.sold (Kset.image part)))
      (D + (∑ g ∈ C.sold (Kset.image part), p g) - ∑ j ∈ Kset.image part, C.cash j) := by
  classical
  obtain ⟨hD, hL, hsmall⟩ := hInv
  set J : Finset (Fin k) := Kset.image part with hJ
  -- The good sold to fund a part is charged to the first served agent that uses it.
  set Fa : Fin n → Finset G := fun b =>
    (C.src (part b)).toFinset \
      (Kset.filter (fun b' => b' < b)).biUnion (fun b' => (C.src (part b')).toFinset) with hFadef
  have hFasub : ∀ b, Fa b ⊆ (C.src (part b)).toFinset := fun b => Finset.sdiff_subset
  have hsrc_of_mem : ∀ b, ∀ g ∈ Fa b, C.src (part b) = some g := by
    intro b g hg
    have := hFasub b hg
    rwa [Option.mem_toFinset, Option.mem_def] at this
  have hFasell : ∀ b, Fa b ⊆ C.sell := fun b g hg => C.src_mem _ _ (hsrc_of_mem b g hg)
  -- disjointness of the events
  have hpair : ∀ b ∈ Kset, ∀ b' ∈ Kset, b ≠ b' →
      Disjoint (C.goods (part b) ∪ Fa b) (C.goods (part b') ∪ Fa b') := by
    intro b hb b' hb' hbb
    rw [Finset.disjoint_left]
    intro g hg hg'
    have hpp : part b ≠ part b' := fun h => hbb (hinj hb hb' h)
    rcases Finset.mem_union.mp hg with hg1 | hg1 <;> rcases Finset.mem_union.mp hg' with hg2 | hg2
    · exact Finset.disjoint_left.mp (C.goods_disj _ _ hpp) hg1 hg2
    · exact Finset.disjoint_left.mp (C.sell_disj (part b)) (hFasell b' hg2) hg1
    · exact Finset.disjoint_left.mp (C.sell_disj (part b')) (hFasell b hg1) hg2
    · rcases lt_or_gt_of_ne hbb with hlt | hlt
      · have : g ∈ (Kset.filter (fun x => x < b')).biUnion
            (fun b'' => (C.src (part b'')).toFinset) :=
          Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hlt⟩, hFasub b hg1⟩
        exact (Finset.mem_sdiff.mp hg2).2 this
      · have : g ∈ (Kset.filter (fun x => x < b)).biUnion
            (fun b'' => (C.src (part b'')).toFinset) :=
          Finset.mem_biUnion.mpr ⟨b', Finset.mem_filter.mpr ⟨hb', hlt⟩, hFasub b' hg2⟩
        exact (Finset.mem_sdiff.mp hg1).2 this
  -- the union of the charged goods is exactly the set of goods sold in this round
  have hunionF : Kset.biUnion Fa = C.sold J := by
    ext g
    simp only [Finset.mem_biUnion, Canonical.sold, hJ, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, hgb⟩
      exact ⟨part b, ⟨b, hb, rfl⟩, hFasub b hgb⟩
    · rintro ⟨j, ⟨b, hb, rfl⟩, hgj⟩
      set W : Finset (Fin n) := Kset.filter (fun x => g ∈ (C.src (part x)).toFinset) with hW
      have hWne : W.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hgj⟩⟩
      refine ⟨W.min' hWne, (Finset.mem_filter.mp (W.min'_mem hWne)).1, ?_⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (W.min'_mem hWne)).2, ?_⟩
      intro hcon
      obtain ⟨b', hb', hgb'⟩ := Finset.mem_biUnion.mp hcon
      obtain ⟨hb'K, hb'lt⟩ := Finset.mem_filter.mp hb'
      exact absurd (W.min'_le b' (Finset.mem_filter.mpr ⟨hb'K, hgb'⟩)) (not_le.mpr hb'lt)
  have hgoodsU : Kset.biUnion (fun b => C.goods (part b)) = J.biUnion C.goods := by
    ext g
    simp only [Finset.mem_biUnion, hJ, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, hg⟩; exact ⟨part b, ⟨b, hb, rfl⟩, hg⟩
    · rintro ⟨j, ⟨b, hb, rfl⟩, hg⟩; exact ⟨b, hb, hg⟩
  have hunion : Kset.biUnion (fun b => C.goods (part b) ∪ Fa b) = J.biUnion C.goods ∪ C.sold J := by
    rw [← hgoodsU, ← hunionF]
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨a, ha, h | h⟩
      · exact Or.inl ⟨a, ha, h⟩
      · exact Or.inr ⟨a, ha, h⟩
    · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
      · exact ⟨a, ha, Or.inl h⟩
      · exact ⟨a, ha, Or.inr h⟩
  have hcashsum : ∑ b ∈ Kset, C.cash (part b) = ∑ j ∈ J, C.cash j :=
    (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
  have hFsum : ∑ b ∈ Kset, ∑ g ∈ Fa b, p g = ∑ g ∈ C.sold J, p g := by
    rw [← hunionF, Finset.sum_biUnion]
    intro b hb b' hb' hbb
    exact Finset.disjoint_of_subset_left Finset.subset_union_right
      (Finset.disjoint_of_subset_right Finset.subset_union_right (hpair b hb b' hb' hbb))
  have key := losses_extend_set v p hL hKT (fun b => C.goods (part b)) Fa
    (fun b => C.cash (part b)) (fun b _ => C.goods_subset _)
    (fun b _ => (hFasell b).trans C.sell_subset)
    (fun b _ => (Finset.disjoint_of_subset_left (hFasell b) (C.sell_disj (part b))).symm)
    hpair (fun b _ => C.cash_nonneg _) ?_
  · rw [hunion, hFsum, hcashsum] at key
    exact key
  · intro a ha Ei b hb
    obtain ⟨haT, haK⟩ := Finset.mem_sdiff.mp ha
    have hlt := hloss a haT haK b hb
    rcases Finset.eq_empty_or_nonempty (Fa b) with hFe | ⟨f, hf⟩
    · exact Or.inr (Or.inl ⟨le_of_lt hlt, by rw [hFe]; simp⟩)
    · have hsrc : C.src (part b) = some f := hsrc_of_mem b f hf
      have hFb : Fa b = {f} := by
        have hsub : Fa b ⊆ {f} := by
          intro g hg
          have : C.src (part b) = some g := hsrc_of_mem b g hg
          rw [hsrc] at this
          simp [Option.some_inj.mp this]
        rcases Finset.subset_singleton_iff.mp hsub with h | h
        · exact absurd (h ▸ hf) (by simp)
        · exact h
      have hfsell : f ∈ C.sell := C.src_mem _ _ hsrc
      by_cases hfS : f ∈ Ei.sell
      · refine Or.inr (Or.inl ⟨le_of_lt hlt, ?_⟩)
        intro g hg
        rw [hFb, Finset.mem_singleton] at hg
        exact Or.inr (hg ▸ hfS)
      · -- the part is a singleton funded by the sale of `f`
        have hbne0 : part b ≠ 0 := by
          by_cases hbi : b = i
          · subst hbi
            rcases hzero with hKT' | h
            · exact absurd (hKT' ▸ haT) haK
            · exact h
          · exact hspecial b hb hbi
        have hsrcne : C.src (part b) ≠ none := by rw [hsrc]; simp
        obtain ⟨e, he⟩ := (C.pure_or_singleton (part b) hbne0).resolve_left hsrcne
        have hdc : C.dcash (part b) = 0 := C.singleton_dcash (part b) hbne0 hsrcne
        have hcf : C.cash (part b) ≤ p f := by
          have h1 : C.scash (part b) ≤ p f := by
            refine le_trans (Finset.single_le_sum
              (f := C.scash) (fun j _ => C.scash_nonneg j) ?_) (C.scash_sum f hfsell)
            simp [hsrc]
          simp only [Canonical.cash, hdc, zero_add]
          exact h1
        have hc0 : 0 ≤ C.cash (part b) := C.cash_nonneg _
        have heR : e ∈ R := C.goods_subset (part b) (by rw [he]; simp)
        have hfR : f ∈ R := C.sell_subset hfsell
        have hve : vbar (v a) p e ≤ thr v p a := le_of_lt (hsmall a haT e heR)
        have hvf : vbar (v a) p f ≤ thr v p a := le_of_lt (hsmall a haT f hfR)
        -- the price of a good the *proposing* agent sells is at least `(1-ρ)` of its maximin
        -- share, which — the proposing agent having the largest maximin share — is at least
        -- `(1-ρ)` of the maximin share of the still-active agent `a`
        have hprice : MMS n (v a) p - thr v p a ≤ p f := by
          refine le_trans ?_ (C.price_large f hfsell)
          have hle : MMS n (v a) p ≤ MMS n (v i) p := hmax a haT
          simp only [thr, rho]
          linarith
        by_cases heS : e ∈ Ei.sell
        · exact Or.inr (Or.inr (Or.inr
            ⟨⟨e, he, heS, hve⟩, ⟨f, hFb, hfS, hvf, hcf, hprice⟩, hc0, le_of_lt hlt⟩))
        · exact Or.inr (Or.inr (Or.inl
            ⟨⟨e, he, heS, hve⟩, ⟨f, hFb, hfS, hvf, hcf, hprice⟩, hc0, le_of_lt hlt⟩))

/-- **Proposition 5, first stage of the preliminary phase.**  Selling an expensive good `g` and
paying its threshold to the active agent `j` of *lowest* maximin share preserves the accounting:
for a remaining active agent this is a loss of type `ℓ₁` (if it did not intend to sell `g`) or of
type `ℓ₂` (if it did). -/
theorem losses_of_stage1 (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D)
    {j : Fin n} (hj : j ∈ T) (hmin : ∀ a ∈ T, MMS n (v j) p ≤ MMS n (v a) p)
    {g : G} (hg : g ∈ R) (hprice : thr v p j ≤ p g) (hthr0 : 0 ≤ thr v p j) :
    Losses v p (T.erase j) (R.erase g) (D + p g - thr v p j) := by
  classical
  have key := losses_extend v p hL hj ∅ {g} (thr v p j) (Finset.empty_subset _)
    (by simpa using hg) (by simp) hthr0 ?_
  · have hR : R \ ((∅ : Finset G) ∪ {g}) = R.erase g := by
      simp [Finset.sdiff_singleton_eq_erase]
    have hD : D + (∑ x ∈ ({g} : Finset G), p x) - thr v p j = D + p g - thr v p j := by
      simp
    rw [hR, hD] at key
    exact key
  · intro i hi Ei
    by_cases hgS : g ∈ Ei.sell
    · -- the agent intended to sell `g` anyway: a loss of type `ℓ₂`
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have : thr v p j ≤ thr v p i :=
          thr_le_thr v p (hmin i (Finset.mem_of_mem_erase hi))
        simpa [vbarSum] using this
      · intro f hf
        rw [Finset.mem_singleton] at hf
        exact Or.inr (hf ▸ hgS)
    · exact Or.inl ⟨g, hgS, Or.inr ⟨rfl, rfl, hprice⟩⟩

/-- **Proposition 5, second stage of the preliminary phase.**  Handing a good `g` that agent `i`
values above its threshold to `i` preserves the accounting: for a remaining active agent this is a
loss of type `ℓ₁` (if it did not intend to sell `g`) or of type `ℓ₂` (if it did — and then its
`v̄` value of `g` is its price, which the first stage has left below the threshold). -/
theorem losses_of_stage2 (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D)
    (hstage1 : ∀ a ∈ T, ∀ e ∈ R, p e < thr v p a)
    {i : Fin n} (hi : i ∈ T) {g : G} (hg : g ∈ R) :
    Losses v p (T.erase i) (R.erase g) D := by
  classical
  have key := losses_extend v p hL hi {g} ∅ 0 (by simpa using hg) (Finset.empty_subset _)
    (by simp) le_rfl ?_
  · have hR : R \ (({g} : Finset G) ∪ ∅) = R.erase g := by
      simp [Finset.sdiff_singleton_eq_erase]
    rw [hR] at key
    simpa using key
  · intro b hb Eb
    by_cases hgS : g ∈ Eb.sell
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have h1 : v b g ≤ p g := Eb.sell_price g hgS
        have h2 : p g < thr v p b := hstage1 b (Finset.mem_of_mem_erase hb) g hg
        have : vbarSum (v b) p {g} = p g := by
          simp [vbarSum, vbar, max_eq_left h1]
        rw [this]
        linarith
      · intro f hf; simp at hf
    · exact Or.inl ⟨g, hgS, Or.inl ⟨rfl, rfl, rfl⟩⟩

end FairSelling
