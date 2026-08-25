import Mathlib
import RequestProject.Selling

/-!
# Small-`n` existence results for fair allocation with selling

This file builds on `RequestProject.Selling` and develops results towards the small-`n`
existence theorems of the manuscript "Fair Allocation with Optional Selling".

## Main result of this file

* **Attainment of the maximin share** (`MMS_mem`): the supremum defining `MMS` is actually
  achieved by a valid outcome. Equivalently (`exists_outcome_ge_MMS`) there is a valid
  outcome giving every part at least `MMS n v p`. This is the technical backbone of the
  existence theorems, since their proofs speak of "an agent's MMS partition".

## Proof strategy

Every valid outcome is reduced to a canonical *assignment form* `outcomeOf assign m`, where
the discrete datum `assign : G → Option (Fin n)` (each good sold, `none`, or kept by `some j`)
ranges over a finite type, and, for each fixed `assign`, the money split `m` ranges over a
compact set. Maximising the worst-bundle utility `minUtil` is therefore a maximum over a
finite family of compact optimisations, hence attained (`exists_max_outcome`).
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

/-- Minimum utility over the `n` parts: the value of the agent's worst bundle. -/
noncomputable def minUtil (v : G → ℝ) (o : Outcome G n) : ℝ := ⨅ j, util v o j

omit [Fintype G] [DecidableEq G] in
lemma le_minUtil_iff (hn : 0 < n) (v : G → ℝ) (o : Outcome G n) (r : ℝ) :
    r ≤ minUtil v o ↔ ∀ j, r ≤ util v o j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [minUtil, le_ciInf_iff (Finite.bddBelow_range _)]

omit [Fintype G] [DecidableEq G] in
lemma mem_MMSset_iff (hn : 0 < n) (v p : G → ℝ) (r : ℝ) :
    r ∈ MMSset n v p ↔ ∃ o : Outcome G n, o.Valid p ∧ r ≤ minUtil v o := by
  constructor
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (le_minUtil_iff hn v o r).mpr h⟩
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (le_minUtil_iff hn v o r).mp h⟩

/-- The outcome determined by an assignment (each good is sold, `none`, or kept by `some j`)
together with a money split `m`. -/
def outcomeOf (assign : G → Option (Fin n)) (m : Fin n → ℝ) : Outcome G n where
  sold := Finset.univ.filter (fun g => assign g = none)
  kept := fun j => Finset.univ.filter (fun g => assign g = some j)
  money := m

/-- The sale proceeds available under an assignment. -/
noncomputable def procOf (p : G → ℝ) (assign : G → Option (Fin n)) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => assign g = none), p g

/-- The subjective value of the goods assigned (kept) to part `j`. -/
noncomputable def keptVal (v : G → ℝ) (assign : G → Option (Fin n)) (j : Fin n) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => assign g = some j), v g

/-- The worst-bundle utility of the outcome `outcomeOf assign m`, written directly in terms
of the assignment data. -/
noncomputable def minUtilData (v : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ) : ℝ :=
  ⨅ j, keptVal v assign j + m j

omit [DecidableEq G] in
lemma minUtil_outcomeOf (v : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ) :
    minUtil v (outcomeOf assign m) = minUtilData v assign m := rfl

private lemma continuous_iInf_add (c : Fin n → ℝ) :
    Continuous (fun m : Fin n → ℝ => ⨅ j, c j + m j) := by
  cases n with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin 0 → ℝ => (0 : ℝ)))
  | succ k =>
    haveI : Nonempty (Fin (k + 1)) := ⟨0⟩
    have heq : (fun m : Fin (k + 1) → ℝ => ⨅ j, c j + m j)
        = Finset.univ.inf' Finset.univ_nonempty
            (fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => c j + m j) := by
      funext m
      rw [Finset.inf'_apply (f := fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => c j + m j)]
      rw [Finset.inf'_univ_eq_ciInf]
    rw [heq]
    exact Continuous.finset_inf' Finset.univ_nonempty
      (fun j _ => continuous_const.add (continuous_apply j))

omit [DecidableEq G] in
/-- The outcome `outcomeOf assign m` is feasible provided the money split is nonnegative and
does not exceed the available proceeds. -/
theorem outcomeOf_valid (p : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hms : ∑ j, m j ≤ procOf p assign) :
    (outcomeOf assign m).Valid p := by
  refine ⟨?_, ?_, hm0, ?_⟩
  · intro j
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [outcomeOf, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2; exact absurd hx2.2 (by simp)
  · intro j k hjk
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [outcomeOf, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2
    exact hjk (Option.some.inj hx2.2)
  · exact hms

omit [DecidableEq G] in
/-- For a fixed assignment, the money split maximising the worst-bundle utility exists
(compactness of the money simplex). -/
theorem exists_opt_money (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (assign : G → Option (Fin n)) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (∑ j, m j ≤ procOf p assign) ∧
      ∀ m', (∀ j, 0 ≤ m' j) → (∑ j, m' j ≤ procOf p assign) →
        minUtilData v assign m' ≤ minUtilData v assign m := by
  set P := procOf p assign with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun g _ => hp g)
  set K : Set (Fin n → ℝ) := {m | (∀ j, 0 ≤ m j) ∧ ∑ j, m j ≤ P} with hK
  have hKcomp : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => P))
    · have h1 : IsClosed {m : Fin n → ℝ | ∀ j, 0 ≤ m j} := by
        have he : {m : Fin n → ℝ | ∀ j, 0 ≤ m j} = ⋂ j, {m : Fin n → ℝ | 0 ≤ m j} := by
          ext m; simp
        rw [he]; exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
      have h2 : IsClosed {m : Fin n → ℝ | ∑ j, m j ≤ P} :=
        isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
      exact h1.inter h2
    · intro m hm
      obtain ⟨hnn, hsum⟩ := hm
      simp only [Set.mem_Icc]
      refine ⟨fun j => hnn j, fun j => ?_⟩
      calc m j ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
        _ ≤ P := hsum
  have hKne : K.Nonempty := ⟨0, ⟨fun j => le_refl 0, by simpa using hP0⟩⟩
  have hcont : Continuous (fun m : Fin n → ℝ => minUtilData v assign m) :=
    continuous_iInf_add (keptVal v assign)
  obtain ⟨m, hmK, hmax⟩ := hKcomp.exists_isMaxOn hKne hcont.continuousOn
  exact ⟨m, hmK.1, hmK.2, fun m' h0 hs => hmax (show m' ∈ K from ⟨h0, hs⟩)⟩

/-- Any valid outcome can be re-expressed in assignment form (dumping unallocated goods into
part `0`) without decreasing its worst-bundle utility. -/
theorem exists_assignform_ge (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g)
    (o : Outcome G n) (ho : o.Valid p) :
    ∃ (assign : G → Option (Fin n)) (m : Fin n → ℝ),
      (∀ j, 0 ≤ m j) ∧ (∑ j, m j ≤ procOf p assign) ∧
      minUtil v o ≤ minUtilData v assign m := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hsold, hdisj, hmoney, hbudget⟩ := ho
  set assign : G → Option (Fin n) :=
    fun g => if g ∈ o.sold then none
      else (if h : ∃ j, g ∈ o.kept j then some h.choose else some ⟨0, hn⟩) with hassign
  have hnone : ∀ g, assign g = none ↔ g ∈ o.sold := by
    intro g
    constructor
    · intro h
      by_contra hgs
      simp only [hassign, if_neg hgs] at h
      split at h <;> simp_all
    · intro h; simp only [hassign, if_pos h]
  have hkept : ∀ j g, g ∈ o.kept j → assign g = some j := by
    intro j g hg
    have hgs : g ∉ o.sold := Finset.disjoint_right.mp (hsold j) hg
    have hex : ∃ k, g ∈ o.kept k := ⟨j, hg⟩
    simp only [hassign, if_neg hgs, dif_pos hex]
    have hc : g ∈ o.kept hex.choose := hex.choose_spec
    by_cases hkj : hex.choose = j
    · rw [hkj]
    · exact absurd (Finset.disjoint_left.mp (hdisj _ _ hkj) hc hg) (by simp)
  refine ⟨assign, o.money, hmoney, ?_, ?_⟩
  · have hset : Finset.univ.filter (fun g => assign g = none) = o.sold := by
      ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnone g]
    rw [procOf, hset]; exact hbudget
  · apply ciInf_mono (Finite.bddBelow_range _)
    intro j
    have hsub : o.kept j ⊆ Finset.univ.filter (fun g => assign g = some j) := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hkept j g hg
    have hle : (∑ g ∈ o.kept j, v g) ≤ keptVal v assign j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hv i)
    show util v o j ≤ keptVal v assign j + o.money j
    simp only [util]; linarith [hle]

/-- Every good is either sold or kept by some part in an outcome of assignment form. -/
theorem outcomeOf_cover (assign : G → Option (Fin n)) (m : Fin n → ℝ) :
    (outcomeOf assign m).sold ∪ Finset.univ.biUnion (outcomeOf assign m).kept = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro g
  simp only [outcomeOf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  rcases h : assign g with _ | i
  · exact Or.inl rfl
  · exact Or.inr ⟨i, rfl⟩

/-- There is a valid outcome maximising the worst-bundle utility over all valid outcomes; it can
be taken to allocate every good (sold or kept). -/
theorem exists_max_outcome (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) (hn : 0 < n) :
    ∃ o : Outcome G n, o.Valid p ∧
      (o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧
      ∀ o' : Outcome G n, o'.Valid p → minUtil v o' ≤ minUtil v o := by
  choose m hm using fun assign => exists_opt_money v p hp assign
  obtain ⟨a0, ha0⟩ := Finite.exists_max
    (fun assign : G → Option (Fin n) => minUtilData v assign (m assign))
  refine ⟨outcomeOf a0 (m a0), outcomeOf_valid p a0 (m a0) (hm a0).1 (hm a0).2.1,
    outcomeOf_cover a0 (m a0), ?_⟩
  intro o' ho'
  obtain ⟨assign', m', hm0', hms', hle'⟩ := exists_assignform_ge hn v p hv o' ho'
  calc minUtil v o' ≤ minUtilData v assign' m' := hle'
    _ ≤ minUtilData v assign' (m assign') := (hm assign').2.2 m' hm0' hms'
    _ ≤ minUtilData v a0 (m a0) := ha0 assign'
    _ = minUtil v (outcomeOf a0 (m a0)) := (minUtil_outcomeOf v a0 (m a0)).symm

/-- **Attainment of the maximin share.** The supremum defining `MMS` is attained: there is a
valid outcome giving every agent (part) at least the value `MMS n v p`. -/
theorem MMS_mem (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ∈ MMSset n v p := by
  obtain ⟨o, hovalid, _hcover, homax⟩ := exists_max_outcome v p hv hp hn
  have hub : ∀ r ∈ MMSset n v p, r ≤ minUtil v o := by
    intro r hr
    obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn v p r).mp hr
    exact hr'.trans (homax o' hv')
  have hmem : minUtil v o ∈ MMSset n v p := (mem_MMSset_iff hn v p _).mpr ⟨o, hovalid, le_refl _⟩
  have hbdd : BddAbove (MMSset n v p) := ⟨minUtil v o, fun r hr => hub r hr⟩
  have hEq : MMS n v p = minUtil v o := le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup hbdd hmem)
  show MMS n v p ∈ MMSset n v p
  rw [hEq]; exact hmem

/-- There is a valid outcome giving every agent (part) at least its maximin share. -/
theorem exists_outcome_ge_MMS (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ j, MMS n v p ≤ util v o j :=
  MMS_mem hn v p hv hp

/-- **An MMS partition that allocates every good.** There is a valid outcome allocating every
good (sold or kept), for which every part is worth at least `MMS n v p`. -/
theorem exists_MMS_partition (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧ ∀ j, MMS n v p ≤ util v o j := by
  obtain ⟨o, hovalid, hcover, homax⟩ := exists_max_outcome v p hv hp hn
  have hub : ∀ r ∈ MMSset n v p, r ≤ minUtil v o := by
    intro r hr
    obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn v p r).mp hr
    exact hr'.trans (homax o' hv')
  have hmem : minUtil v o ∈ MMSset n v p := (mem_MMSset_iff hn v p _).mpr ⟨o, hovalid, le_refl _⟩
  have hbdd : BddAbove (MMSset n v p) := ⟨minUtil v o, fun r hr => hub r hr⟩
  have hEq : MMS n v p = minUtil v o := le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup hbdd hmem)
  refine ⟨o, hovalid, hcover, fun j => ?_⟩
  rw [hEq]
  exact (le_minUtil_iff hn v o (minUtil v o)).mp (le_refl _) j

/-! ### Realizing "unified" assignments as concrete outcomes

In the manuscript's arguments it is convenient to think of goods as being handed out *in full*
to agents, each of whom may then privately decide to keep or to sell every good they receive,
realizing value `v̄ g = max (p g) (v g)` from it (`vbar`).  In addition, a set `F` of goods may
be *force-sold*, with the proceeds split among the agents by a money vector `q`.

`unifiedOutcome` turns such a description into a concrete `Outcome`, and the two lemmas below
record its utility profile and its feasibility. -/

open Classical in
/-- The concrete outcome realizing the unified assignment where agent `i` receives the goods
`A i` (to keep or sell privately), the goods in `F` are force-sold, and `q i` is the share of
the force-sale proceeds given to agent `i`. -/
noncomputable def unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) : Outcome G n where
  sold := F ∪ Finset.univ.biUnion (fun i => (A i).filter (fun g => v i g < p g))
  kept := fun i => (A i).filter (fun g => ¬ v i g < p g)
  money := fun i => q i + ∑ g ∈ (A i).filter (fun g => v i g < p g), p g

omit [Fintype G] in
/-- Under `unifiedOutcome`, agent `i` obtains exactly `v̄i (A i) + q i`. -/
theorem util_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    util (v i) (unifiedOutcome v p A F q) i = vbarSum (v i) p (A i) + q i := by
  classical
  simp only [util, unifiedOutcome, vbarSum, vbar]
  rw [← Finset.sum_filter_add_sum_filter_not (A i) (fun g => v i g < p g)
        (fun g => max (p g) (v i g))]
  have h1 : ∑ g ∈ (A i).filter (fun g => v i g < p g), max (p g) (v i g)
      = ∑ g ∈ (A i).filter (fun g => v i g < p g), p g := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [Finset.mem_filter] at hg
    exact max_eq_left (le_of_lt hg.2)
  have h2 : ∑ g ∈ (A i).filter (fun g => ¬ v i g < p g), max (p g) (v i g)
      = ∑ g ∈ (A i).filter (fun g => ¬ v i g < p g), v i g := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [Finset.mem_filter, not_lt] at hg
    exact max_eq_right hg.2
  rw [h1, h2]; ring

omit [Fintype G] in
/-- Feasibility of `unifiedOutcome`, given that the groups `A i` are pairwise disjoint and
disjoint from `F`, the shares are nonnegative, and they do not exceed the force-sale proceeds. -/
theorem unifiedOutcome_valid (v : Fin n → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hF : ∀ i, Disjoint F (A i))
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i ≤ ∑ g ∈ F, p g) :
    (unifiedOutcome v p A F q).Valid p := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp only [unifiedOutcome]
    rw [Finset.disjoint_union_left]
    refine ⟨Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hF i), ?_⟩
    rw [Finset.disjoint_biUnion_left]
    intro k _
    by_cases hik : k = i
    · subst hik
      exact Finset.disjoint_left.mpr (fun g hg1 hg2 => by
        simp only [Finset.mem_filter] at hg1 hg2; exact hg2.2 hg1.2)
    · exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hA k i hik))
  · intro i j hij
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hA i j hij))
  · intro i
    exact add_nonneg (hq0 i) (Finset.sum_nonneg (fun g _ => hp g))
  · simp only [unifiedOutcome]
    have hdisj : Disjoint F (Finset.univ.biUnion (fun i => (A i).filter (fun g => v i g < p g))) := by
      rw [Finset.disjoint_biUnion_right]
      exact fun i _ => Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hF i)
    rw [Finset.sum_union hdisj]
    have hbu : ∑ g ∈ Finset.univ.biUnion (fun i => (A i).filter (fun g => v i g < p g)), p g
        = ∑ i, ∑ g ∈ (A i).filter (fun g => v i g < p g), p g := by
      rw [Finset.sum_biUnion]
      intro i _ j _ hij
      exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hA i j hij))
    rw [hbu, Finset.sum_add_distrib]
    exact add_le_add hq (le_refl _)

end FairSelling
