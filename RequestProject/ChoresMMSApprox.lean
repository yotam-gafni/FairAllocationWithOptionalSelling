import Mathlib
import RequestProject.ChoresBagFilling

/-!
# Theorem 5 / Lemma 18: a `2`-approximation of the MMS for chores with outsourcing

This file assembles the bag-filling analysis of `RequestProject.ChoresBagFilling` into the
manuscript's result:

> **Theorem 5 (first half) / Lemma 18.**  Every allocation instance with chores (and optional
> outsourcing) has a `2`-MMS allocation.

`exists_two_MMS_chores` states exactly this: for arbitrary non-negative cost functions
`c₁,…,cₙ` and outsourcing prices `p` there is a feasible outcome in which the cost of agent
`i` is at most `2 · MMSᵢ`, where `MMSᵢ` is the maximin share of agent `i` in the chores model
with outsourcing.

The two further statements of the manuscript's chores appendix, which it makes without proof,
are formalized elsewhere in the development: the `19/18` impossibility bound accompanying
Theorem 5 in `RequestProject.NineteenEighteenths`
(`nineteen_eighteenths_gap_chores`), and the remark that for `n = 2` the *exact* maximin share
can be guaranteed in `RequestProject.ChoresTwoAgents` (`exists_MMS_two_chores`).
-/

open scoped BigOperators

namespace FairChores

variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

/-- An agent whose maximin share is `0` can perform (or pay for) every chore at no cost. -/
lemma cbar_eq_zero_of_MMS_eq_zero {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t)
    (hn : 0 < n) (h0 : MMS n c p = 0) (t : T) : cbar c p t = 0 := by
  classical
  have hbound := wtSum_univ_le_nsmul_MMS (c := c) (p := p) (n := n) hc hn
  rw [h0] at hbound
  simp only [mul_zero] at hbound
  have hnonneg : ∀ s ∈ (Finset.univ : Finset T), 0 ≤ wt c p 0 s := fun s _ => wt_nonneg hc hp s
  have hzero : wt c p 0 t = 0 := by
    have hsum : ∑ s, wt c p 0 s = 0 :=
      le_antisymm hbound (Finset.sum_nonneg hnonneg)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum t (Finset.mem_univ t)
  by_cases hpos : 0 < cbar c p t
  · exfalso
    rw [wt, if_pos hpos] at hzero
    have := cbar_le_price (c := c) (p := p) t
    rw [hzero] at this
    linarith
  · have := cbar_nonneg hc hp t
    linarith [not_lt.mp hpos]

/-- **Theorem 5 (existence half) / Lemma 18 of the manuscript.**  Every instance of chores
with optional outsourcing admits a feasible outcome in which every agent's cost is at most
twice its maximin share. -/
theorem exists_two_MMS_chores (hn : 0 < n) (c : Fin n → T → ℝ) (p : T → ℝ)
    (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ i, cost (c i) o i ≤ 2 * MMS n (c i) p := by
  classical
  set mu : Fin n → ℝ := fun i => MMS n (c i) p with hmudef
  have hmunn : ∀ i, 0 ≤ mu i := fun i => MMS_nonneg (hc i) hn
  -- it suffices to produce a self-service allocation of all chores with costs `≤ 2 · muᵢ`
  suffices hsuff : ∃ P : PreAlloc T n,
      (∀ i j, i ≠ j → Disjoint (P.bundle i) (P.bundle j)) ∧
      (∀ i, Disjoint P.outs (P.bundle i)) ∧
      (P.outs ∪ Finset.univ.biUnion P.bundle = Finset.univ) ∧
      (∀ i, 0 ≤ P.share i) ∧
      (∑ i, P.share i = ∑ t ∈ P.outs, p t) ∧
      (∀ i, cbarSum (c i) p (P.bundle i) + P.share i ≤ 2 * mu i) by
    obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := hsuff
    obtain ⟨o, hvalid, hcost⟩ := exists_outcome_of_preAlloc P p c hp h1 h2 h3 h4 h5
    exact ⟨o, hvalid, fun i => by rw [hcost i]; exact h6 i⟩
  by_cases hzero : ∃ i0, mu i0 = 0
  · -- some agent can do everything for free; give it all the chores
    obtain ⟨i0, hi0⟩ := hzero
    have hcb : ∀ t, cbar (c i0) p t = 0 := fun t =>
      cbar_eq_zero_of_MMS_eq_zero (hc i0) hp hn hi0 t
    refine ⟨⟨fun j => if j = i0 then Finset.univ else ∅, ∅, fun _ => 0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      dsimp only
      by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [hi, hj]
      exact absurd (hi.trans hj.symm) hij
    · intro i; simp
    · dsimp only
      simp only [Finset.empty_union]
      refine Finset.eq_univ_iff_forall.mpr fun s => ?_
      exact Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, by simp⟩
    · intro i; exact le_rfl
    · simp
    · intro i
      dsimp only
      by_cases hi : i = i0
      · subst hi
        have hz : cbarSum (c i) p Finset.univ = 0 := by
          simp [cbarSum, hcb]
        simp only [if_true, add_zero, hz, hi0]
        norm_num
      · simp only [if_neg hi, cbarSum_empty, add_zero]
        linarith [hmunn i]
  · -- all thresholds are positive: run the bag-filling algorithm
    push_neg at hzero
    have hmupos : ∀ i, 0 < mu i := fun i => lt_of_le_of_ne (hmunn i) (Ne.symm (hzero i))
    have hAne : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]
      exact hn
    have hinv : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Inv c p mu i (Finset.univ : Finset (Fin n)).card Finset.univ := by
      intro i _
      left
      rw [Finset.card_univ, Fintype.card_fin]
      exact wtSum_univ_le_nsmul_MMS (hc i) hn
    obtain ⟨P, hP, hcost⟩ :=
      bagfill_exists hc hp hmupos (Finset.univ : Finset (Fin n)).card Finset.univ Finset.univ
        rfl hAne hinv
    exact ⟨P, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.1, hP.2.2.2.2.2.2,
      fun i => hcost i (Finset.mem_univ i)⟩

end FairChores
