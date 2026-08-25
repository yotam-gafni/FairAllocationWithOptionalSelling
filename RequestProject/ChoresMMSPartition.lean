import Mathlib
import RequestProject.ChoresModel

/-!
# Attainment of the maximin share for chores with outsourcing

The maximin share of the chores model (`FairChores.MMS`) is defined as the *infimum* of the
set of values `r` for which some feasible outcome costs every part at most `r`.  The
arguments of the manuscript speak of "the MMS partition of an agent", so we need to know
that this infimum is attained.

This is the mirror image of `RequestProject.SmallN` (`FairSelling.MMS_mem`): every feasible
outcome is put into *assignment form* `assignOutcome assign m`, where the discrete datum
`assign : T → Option (Fin n)` (each chore is outsourced, `none`, or performed by `some j`)
ranges over a finite type and, for a fixed `assign`, the payment vector `m` may be taken in
the compact simplex `{m ≥ 0 | ∑ m = bill}`.  Minimising the worst-part cost is therefore a
minimum over a finite family of compact optimisations, hence attained
(`exists_min_outcome`).

Main results:

* `MMS_mem_chores` — `MMS n c p ∈ MMSset n c p`;
* `exists_MMS_partition_chores` — a feasible outcome all of whose parts cost at most
  `MMS n c p`;
* `MMS_le_of_outcome` — the converse direction, used to compute maximin shares.
-/

open scoped BigOperators

namespace FairChores

variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

/-- Maximum cost over the `n` parts: the cost of the agent's worst part. -/
noncomputable def maxCost (c : T → ℝ) (o : Outcome T n) : ℝ := ⨆ j, cost c o j

omit [Fintype T] [DecidableEq T] in
lemma maxCost_le_iff (hn : 0 < n) (c : T → ℝ) (o : Outcome T n) (r : ℝ) :
    maxCost c o ≤ r ↔ ∀ j, cost c o j ≤ r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [maxCost, ciSup_le_iff (Finite.bddAbove_range _)]

lemma mem_MMSset_iff (hn : 0 < n) (c p : T → ℝ) (r : ℝ) :
    r ∈ MMSset n c p ↔ ∃ o : Outcome T n, o.Valid p ∧ maxCost c o ≤ r := by
  constructor
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (maxCost_le_iff hn c o r).mpr h⟩
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (maxCost_le_iff hn c o r).mp h⟩

/-- If some feasible outcome costs every part at most `r`, then `MMS ≤ r`. -/
lemma MMS_le_of_outcome {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) {o : Outcome T n}
    (hvalid : o.Valid p) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) : MMS n c p ≤ r :=
  csInf_le (MMSset_bddBelow hc hn) ⟨o, hvalid, hle⟩

/-- The outcome determined by an assignment (each chore is outsourced, `none`, or performed
by `some j`) together with a payment vector `m`. -/
def assignOutcome (assign : T → Option (Fin n)) (m : Fin n → ℝ) : Outcome T n where
  outsourced := Finset.univ.filter (fun t => assign t = none)
  kept := fun j => Finset.univ.filter (fun t => assign t = some j)
  pay := m

/-- The outsourcing bill incurred by an assignment. -/
noncomputable def billOf (p : T → ℝ) (assign : T → Option (Fin n)) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => assign t = none), p t

/-- The in-house cost of the chores assigned to part `j`. -/
noncomputable def keptCost (c : T → ℝ) (assign : T → Option (Fin n)) (j : Fin n) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => assign t = some j), c t

/-- The worst-part cost of `assignOutcome assign m`, written in terms of the data. -/
noncomputable def maxCostData (c : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ) : ℝ :=
  ⨆ j, keptCost c assign j + m j

omit [DecidableEq T] in
lemma maxCost_assignOutcome (c : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ) :
    maxCost c (assignOutcome assign m) = maxCostData c assign m := rfl

private lemma continuous_iSup_add (K : Fin n → ℝ) :
    Continuous (fun m : Fin n → ℝ => ⨆ j, K j + m j) := by
  cases n with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin 0 → ℝ => (0 : ℝ)))
  | succ k =>
    haveI : Nonempty (Fin (k + 1)) := ⟨0⟩
    have heq : (fun m : Fin (k + 1) → ℝ => ⨆ j, K j + m j)
        = Finset.univ.sup' Finset.univ_nonempty
            (fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => K j + m j) := by
      funext m
      rw [Finset.sup'_apply (f := fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => K j + m j)]
      rw [Finset.sup'_univ_eq_ciSup]
    rw [heq]
    exact Continuous.finset_sup' Finset.univ_nonempty
      (fun j _ => continuous_const.add (continuous_apply j))

omit [DecidableEq T] in
/-- `maxCostData` is monotone in the payment vector. -/
lemma maxCostData_mono (c : T → ℝ) (assign : T → Option (Fin n)) {m m' : Fin n → ℝ}
    (h : ∀ j, m j ≤ m' j) : maxCostData c assign m ≤ maxCostData c assign m' :=
  ciSup_mono (Finite.bddAbove_range _) (fun j => by linarith [h j])

omit [Fintype T] [DecidableEq T] in
/-- A feasible payment vector may be shrunk to one paying the bill exactly. -/
lemma exists_shrink {bill : ℝ} (hb : 0 ≤ bill) (m' : Fin n → ℝ) (h0 : ∀ j, 0 ≤ m' j)
    (hs : bill ≤ ∑ j, m' j) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (∀ j, m j ≤ m' j) ∧ ∑ j, m j = bill := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun j _ => h0 j) : (0:ℝ) ≤ ∑ j, m' j) with heq | hpos
  · refine ⟨m', h0, fun j => le_rfl, ?_⟩
    have : bill = 0 := le_antisymm (by rw [← heq] at hs; exact hs) hb
    rw [this, ← heq]
  · set t : ℝ := bill / ∑ j, m' j with ht
    have ht0 : 0 ≤ t := div_nonneg hb hpos.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hpos]; exact hs
    refine ⟨fun j => t * m' j, fun j => mul_nonneg ht0 (h0 j), fun j => ?_, ?_⟩
    · nlinarith [h0 j]
    · rw [← Finset.mul_sum, ht, div_mul_cancel₀]
      exact ne_of_gt hpos

/-- Feasibility of `assignOutcome`. -/
theorem assignOutcome_valid (p : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hms : billOf p assign ≤ ∑ j, m j) :
    (assignOutcome assign m).Valid p := by
  classical
  refine ⟨?_, ?_, ?_, hm0, hms⟩
  · intro j
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [assignOutcome, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2; exact absurd hx2.2 (by simp)
  · intro j k hjk
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [assignOutcome, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2
    exact hjk (Option.some.inj hx2.2)
  · apply Finset.eq_univ_of_forall
    intro t
    simp only [assignOutcome, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    rcases h : assign t with _ | i
    · exact Or.inl rfl
    · exact Or.inr ⟨i, rfl⟩

omit [DecidableEq T] in
/-- For a fixed assignment there is an optimal payment vector. -/
theorem exists_opt_money (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hn : 0 < n)
    (assign : T → Option (Fin n)) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (billOf p assign ≤ ∑ j, m j) ∧
      ∀ m', (∀ j, 0 ≤ m' j) → (billOf p assign ≤ ∑ j, m' j) →
        maxCostData c assign m ≤ maxCostData c assign m' := by
  classical
  set B := billOf p assign with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun t _ => hp t)
  set K : Set (Fin n → ℝ) := {m | (∀ j, 0 ≤ m j) ∧ ∑ j, m j = B} with hK
  have hKcomp : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => B))
    · have h1 : IsClosed {m : Fin n → ℝ | ∀ j, 0 ≤ m j} := by
        have he : {m : Fin n → ℝ | ∀ j, 0 ≤ m j} = ⋂ j, {m : Fin n → ℝ | 0 ≤ m j} := by
          ext m; simp
        rw [he]; exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
      have h2 : IsClosed {m : Fin n → ℝ | ∑ j, m j = B} :=
        isClosed_eq (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
      exact h1.inter h2
    · intro m hm
      obtain ⟨hnn, hsum⟩ := hm
      simp only [Set.mem_Icc]
      refine ⟨fun j => hnn j, fun j => ?_⟩
      calc m j ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
        _ = B := hsum
  have hKne : K.Nonempty := by
    refine ⟨fun j => if j = ⟨0, hn⟩ then B else 0, fun j => ?_, ?_⟩
    · by_cases hj : j = ⟨0, hn⟩ <;> simp [hj, hB0]
    · simp
  have hcont : Continuous (fun m : Fin n → ℝ => maxCostData c assign m) :=
    continuous_iSup_add (keptCost c assign)
  obtain ⟨m, hmK, hmin⟩ := hKcomp.exists_isMinOn hKne hcont.continuousOn
  refine ⟨m, hmK.1, le_of_eq hmK.2.symm, ?_⟩
  intro m' h0 hs
  obtain ⟨m'', h0'', hle'', hsum''⟩ := exists_shrink hB0 m' h0 hs
  calc maxCostData c assign m ≤ maxCostData c assign m'' :=
        hmin (show m'' ∈ K from ⟨h0'', hsum''⟩)
    _ ≤ maxCostData c assign m' := maxCostData_mono c assign hle''

/-- Every feasible outcome can be re-expressed in assignment form without increasing its
worst-part cost. -/
theorem exists_assignform_le (hn : 0 < n) (c p : T → ℝ) (o : Outcome T n) (ho : o.Valid p) :
    ∃ (assign : T → Option (Fin n)) (m : Fin n → ℝ),
      (∀ j, 0 ≤ m j) ∧ (billOf p assign ≤ ∑ j, m j) ∧
      maxCostData c assign m ≤ maxCost c o := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hdo, hdk, hcov, hm0, hbudget⟩ := ho
  set assign : T → Option (Fin n) :=
    fun t => if t ∈ o.outsourced then none
      else (if h : ∃ j, t ∈ o.kept j then some h.choose else some ⟨0, hn⟩) with hassign
  have hnone : ∀ t, assign t = none ↔ t ∈ o.outsourced := by
    intro t
    constructor
    · intro h
      by_contra hts
      simp only [hassign, if_neg hts] at h
      split at h <;> simp_all
    · intro h; simp only [hassign, if_pos h]
  have hkept : ∀ j t, t ∈ o.kept j → assign t = some j := by
    intro j t ht
    have hts : t ∉ o.outsourced := Finset.disjoint_right.mp (hdo j) ht
    have hex : ∃ k, t ∈ o.kept k := ⟨j, ht⟩
    simp only [hassign, if_neg hts, dif_pos hex]
    have hc : t ∈ o.kept hex.choose := hex.choose_spec
    by_cases hkj : hex.choose = j
    · rw [hkj]
    · exact absurd (Finset.disjoint_left.mp (hdk _ _ hkj) hc ht) (by simp)
  have hsub : ∀ j, Finset.univ.filter (fun t => assign t = some j) ⊆ o.kept j := by
    intro j t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hts : t ∉ o.outsourced := by
      intro hcon
      rw [(hnone t).mpr hcon] at ht; exact absurd ht (by simp)
    have hmem : t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept := by
      rw [hcov]; exact Finset.mem_univ t
    rcases Finset.mem_union.mp hmem with h | h
    · exact absurd h hts
    · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp h
      have := hkept k t hk
      rw [this] at ht
      have : k = j := Option.some.inj ht
      rwa [this] at hk
  refine ⟨assign, o.pay, hm0, ?_, ?_⟩
  · have hset : Finset.univ.filter (fun t => assign t = none) = o.outsourced := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnone t]
    rw [billOf, hset]; exact hbudget
  · refine ciSup_mono (Finite.bddAbove_range _) (fun j => ?_)
    show keptCost c assign j + o.pay j ≤ cost c o j
    simp only [cost, keptCost]
    have heq : Finset.univ.filter (fun t => assign t = some j) = o.kept j := by
      apply Finset.Subset.antisymm (hsub j)
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hkept j t ht
    rw [heq]

/-- There is a feasible outcome minimising the worst-part cost. -/
theorem exists_min_outcome (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hn : 0 < n) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ o' : Outcome T n, o'.Valid p → maxCost c o ≤ maxCost c o' := by
  classical
  choose m hm using fun assign => exists_opt_money c p hp hn assign
  obtain ⟨a0, ha0⟩ := Finite.exists_min
    (fun assign : T → Option (Fin n) => maxCostData c assign (m assign))
  refine ⟨assignOutcome a0 (m a0),
    assignOutcome_valid p a0 (m a0) (hm a0).1 (hm a0).2.1, ?_⟩
  intro o' ho'
  obtain ⟨assign', m', hm0', hms', hle'⟩ := exists_assignform_le hn c p o' ho'
  calc maxCost c (assignOutcome a0 (m a0)) = maxCostData c a0 (m a0) :=
        maxCost_assignOutcome c a0 (m a0)
    _ ≤ maxCostData c assign' (m assign') := ha0 assign'
    _ ≤ maxCostData c assign' m' := (hm assign').2.2 m' hm0' hms'
    _ ≤ maxCost c o' := hle'

/-- **Attainment of the maximin share for chores.** -/
theorem MMS_mem_chores (hn : 0 < n) (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) :
    MMS n c p ∈ MMSset n c p := by
  obtain ⟨o, hovalid, homin⟩ := exists_min_outcome c p hp hn
  have hlb : ∀ r ∈ MMSset n c p, maxCost c o ≤ r := by
    intro r hr
    obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn c p r).mp hr
    exact (homin o' hv').trans hr'
  have hmem : maxCost c o ∈ MMSset n c p := (mem_MMSset_iff hn c p _).mpr ⟨o, hovalid, le_rfl⟩
  have hEq : MMS n c p = maxCost c o :=
    le_antisymm (csInf_le (MMSset_bddBelow hc hn) hmem) (le_csInf ⟨_, hmem⟩ hlb)
  rw [hEq]; exact hmem

/-- **An MMS partition for chores**: a feasible outcome all of whose parts cost at most the
maximin share. -/
theorem exists_MMS_partition_chores (hn : 0 < n) (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ j, cost c o j ≤ MMS n c p :=
  MMS_mem_chores hn c p hc hp

end FairChores
