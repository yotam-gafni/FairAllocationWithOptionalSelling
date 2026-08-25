import Mathlib
import RequestProject.ChoresModel

/-!
# The bag-filling step for chores with outsourcing

This file formalizes one round of the manuscript's algorithm
`APX-MMS-Chores-With-Outsourcing-2` (Algorithm 13): the `while` loop that fills a bag `X`
with chores from the available pool, setting aside (into `Ψ`) the chores that would push the
bag above `2 · MMSᵢ` for *every* active agent.

The outcome of a round is captured by `BagGoal`: either

* every remaining chore is *very expensive* (`c̄ᵢ(t) > 2 · MMSᵢ`) for every active agent — this
  is the situation in which the algorithm outsources all remaining chores and shares the bill
  (line 17); or
* there is a nonempty bag `B` and an active agent `i` that can take it at cost at most
  `2 · MMSᵢ`, such that every other active agent `j` either finds `B` costly enough
  (`c̄_j(B) ≥ MMS_j`, the normal bag-filling situation) or finds *every* remaining chore
  expensive (`c̄_j(t) > MMS_j` for all `t ∉ B`) — the "violation" case of line 14, which the
  manuscript's analysis shows can happen at most once per agent.

The proof is a formalization of the `while` loop: the invariant maintained is that every
active agent either is already satisfied by the current bag `X`, or finds every chore set
aside so far expensive.
-/

open scoped BigOperators

namespace FairChores

variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)

/-- The two possible outcomes of a round of bag-filling; see the module docstring. -/
def BagGoal (A : Finset (Fin n)) (R : Finset T) : Prop :=
  (∀ i ∈ A, ∀ t ∈ R, 2 * mu i < cbar (c i) p t) ∨
  ∃ B ⊆ R, B.Nonempty ∧ ∃ i ∈ A, cbarSum (c i) p B ≤ 2 * mu i ∧
    ∀ j ∈ A, j ≠ i → (mu j ≤ cbarSum (c j) p B ∨ ∀ t ∈ R \ B, mu j < cbar (c j) p t)

omit [Fintype T] in
lemma cbarSum_insert {ci p : T → ℝ} {X : Finset T} {t : T} (ht : t ∉ X) :
    cbarSum ci p (insert t X) = cbar ci p t + cbarSum ci p X := by
  simp [cbarSum, Finset.sum_insert ht]

variable {c p mu}

omit [Fintype T] in
/-- The exit case of the `while` loop: no chore is available any more. -/
lemma bag_exit (hmu : ∀ i, 0 < mu i) {A : Finset (Fin n)} {R X Psi : Finset T}
    (hX : X ⊆ R) (hPsi : Psi ⊆ R) (hdisj : Disjoint X Psi)
    (hempty : R \ (X ∪ Psi) = ∅)
    (hP : ∀ j ∈ A, mu j ≤ cbarSum (c j) p X ∨ ∀ t ∈ Psi, mu j < cbar (c j) p t)
    (hQ : X = ∅ → ∀ t ∈ Psi, ∀ j ∈ A, 2 * mu j < cbar (c j) p t)
    (hU : ∃ j ∈ A, cbarSum (c j) p X < mu j) :
    BagGoal c p mu A R := by
  classical
  have hPsiX : Psi = R \ X := by
    ext s
    constructor
    · intro hs
      exact Finset.mem_sdiff.mpr ⟨hPsi hs, fun hsX => Finset.disjoint_left.mp hdisj hsX hs⟩
    · intro hs
      obtain ⟨hsR, hsX⟩ := Finset.mem_sdiff.mp hs
      by_contra hsPsi
      have : s ∈ R \ (X ∪ Psi) :=
        Finset.mem_sdiff.mpr ⟨hsR, fun h => (Finset.mem_union.mp h).elim hsX hsPsi⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty s)
  rcases Finset.eq_empty_or_nonempty X with hXe | hXne
  · left
    intro i hi t ht
    refine hQ hXe t ?_ i hi
    rw [hPsiX, hXe]
    simpa using ht
  · right
    obtain ⟨j0, hj0A, hj0⟩ := hU
    refine ⟨X, hX, hXne, j0, hj0A, ?_, ?_⟩
    · have := hmu j0
      linarith
    · intro j hjA hne
      rcases hP j hjA with h | h
      · exact Or.inl h
      · exact Or.inr fun t ht => h t (by rw [hPsiX]; exact ht)

omit [Fintype T] in
/-- The `while` loop of Algorithm 13, by induction on the number of available chores. -/
lemma bag_aux (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i)
    (A : Finset (Fin n)) (R : Finset T) :
    ∀ (m : ℕ) (X Psi : Finset T), X ⊆ R → Psi ⊆ R → Disjoint X Psi →
      (R \ (X ∪ Psi)).card ≤ m →
      (∀ j ∈ A, mu j ≤ cbarSum (c j) p X ∨ ∀ t ∈ Psi, mu j < cbar (c j) p t) →
      (X = ∅ → ∀ t ∈ Psi, ∀ j ∈ A, 2 * mu j < cbar (c j) p t) →
      (∃ j ∈ A, cbarSum (c j) p X < mu j) →
      BagGoal c p mu A R := by
  classical
  intro m
  induction m with
  | zero =>
    intro X Psi hX hPsi hdisj hcard hP hQ hU
    exact bag_exit hmu hX hPsi hdisj (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)) hP hQ hU
  | succ m ih =>
    intro X Psi hX hPsi hdisj hcard hP hQ hU
    rcases Finset.eq_empty_or_nonempty (R \ (X ∪ Psi)) with hAv | ⟨t, htAv⟩
    · exact bag_exit hmu hX hPsi hdisj hAv hP hQ hU
    obtain ⟨htR, htXPsi⟩ := Finset.mem_sdiff.mp htAv
    have htX : t ∉ X := fun h => htXPsi (Finset.mem_union_left _ h)
    have htPsi : t ∉ Psi := fun h => htXPsi (Finset.mem_union_right _ h)
    have hcardX : (R \ (insert t X ∪ Psi)).card ≤ m := by
      have hEq : R \ (insert t X ∪ Psi) = (R \ (X ∪ Psi)).erase t := by
        ext s
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hEq, Finset.card_erase_of_mem htAv]
      omega
    have hcardPsi : (R \ (X ∪ insert t Psi)).card ≤ m := by
      have hEq : R \ (X ∪ insert t Psi) = (R \ (X ∪ Psi)).erase t := by
        ext s
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hEq, Finset.card_erase_of_mem htAv]
      omega
    by_cases hall : ∀ j ∈ A, mu j ≤ cbarSum (c j) p (insert t X)
    · by_cases hsome : ∃ i ∈ A, cbarSum (c i) p (insert t X) ≤ 2 * mu i
      · -- the bag can be given away: the normal bag-filling case
        obtain ⟨i, hiA, hi⟩ := hsome
        exact Or.inr ⟨insert t X, Finset.insert_subset htR hX, ⟨t, Finset.mem_insert_self _ _⟩,
          i, hiA, hi, fun j hjA _ => Or.inl (hall j hjA)⟩
      · -- the chore `t` is put aside
        push_neg at hsome
        refine ih X (insert t Psi) hX (Finset.insert_subset htR hPsi) ?_ hcardPsi ?_ ?_ hU
        · exact Finset.disjoint_insert_right.mpr ⟨htX, hdisj⟩
        · intro j hjA
          by_cases hsat : mu j ≤ cbarSum (c j) p X
          · exact Or.inl hsat
          · push_neg at hsat
            have hPsi' : ∀ s ∈ Psi, mu j < cbar (c j) p s := by
              rcases hP j hjA with h | h
              · exact absurd h (not_le.mpr hsat)
              · exact h
            refine Or.inr fun s hs => ?_
            rcases Finset.mem_insert.mp hs with rfl | hsPsi
            · have h2 := hsome j hjA
              rw [cbarSum_insert htX] at h2
              linarith
            · exact hPsi' s hsPsi
        · intro hXe s hs j hjA
          rcases Finset.mem_insert.mp hs with rfl | hsPsi
          · have h2 := hsome j hjA
            rw [cbarSum_insert htX, hXe] at h2
            simpa [cbarSum] using h2
          · exact hQ hXe s hsPsi j hjA
    · -- some agent is still unsatisfied: keep filling the bag
      push_neg at hall
      obtain ⟨j1, hj1A, hj1⟩ := hall
      refine ih (insert t X) Psi (Finset.insert_subset htR hX) hPsi ?_ hcardX ?_ ?_
        ⟨j1, hj1A, hj1⟩
      · exact Finset.disjoint_insert_left.mpr ⟨htPsi, hdisj⟩
      · intro j hjA
        rcases hP j hjA with h | h
        · refine Or.inl (le_trans h ?_)
          rw [cbarSum_insert htX]
          have := cbar_nonneg (hc j) hp t
          linarith
        · exact Or.inr h
      · intro hXe
        exact absurd hXe (by simp)

omit [Fintype T] in
/-- **The bag-filling lemma.**  For any nonempty set `A` of active agents and any set `R` of
available chores, either all remaining chores are very expensive for all active agents, or a
nonempty bag can be handed to an active agent at cost at most twice its threshold, in such a
way that every other active agent either finds the bag costly enough or finds every remaining
chore expensive. -/
theorem bag_lemma (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i)
    {A : Finset (Fin n)} (hA : A.Nonempty) (R : Finset T) :
    BagGoal c p mu A R := by
  classical
  obtain ⟨j0, hj0⟩ := hA
  refine bag_aux hc hp hmu A R (R \ (∅ ∪ ∅)).card ∅ ∅ (by simp) (by simp) (by simp) le_rfl
    (fun j _ => Or.inr (by simp)) (fun _ t ht => absurd ht (by simp))
    ⟨j0, hj0, by simpa [cbarSum] using hmu j0⟩

end FairChores
