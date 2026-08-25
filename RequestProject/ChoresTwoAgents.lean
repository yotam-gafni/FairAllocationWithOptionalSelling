import Mathlib
import RequestProject.ChoresMMSPartition
import RequestProject.ChoresPreAlloc

/-!
# Exact MMS for two agents, for chores with outsourcing

This file proves the chores analogue of the manuscript's Theorem 1 (the MMS half): for two
agents with additive non-negative cost functions and outsourcing prices there is a feasible
outcome in which **every** agent's cost is at most her maximin share
(`exists_MMS_two_chores`).

The proof is the mirror image of the *Cut & Give* protocol of `RequestProject.TwoAgents`:

* every agent has an MMS partition in which at most one chore is *split*, i.e. forcibly
  outsourced with its price shared between the two parts (`exists_reducedC`, the chores form
  of Lemma 5 for `n = 2`); all other chores are handed out in full, an agent receiving a
  chore paying the effective cost `c̄ = min c p` for it;
* the agent whose split chore is cheaper is the **Cutter**, the other one is the **Giver**;
* if one of the Cutter's two parts is acceptable to the Giver, the Giver takes it and the
  Cutter takes the other part (Cut & Choose);
* otherwise the Giver hands one part to the Cutter and keeps *not* the other part, but the
  complement in which the Giver's own split chore `g_G` is outsourced and the Cutter's split
  chore `g_C` is not (Cut & Give).  Since the two parts of the Giver's own MMS partition
  together contain exactly the same chores and the same total payment, and the Giver keeps
  the cheaper of the two sides, her cost is at most her maximin share.
-/

open scoped BigOperators

namespace FairChores

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- A "unified" two-part configuration for a single cost function `c`: two disjoint groups
`A 0`, `A 1` of chores handed out in full (costing `c̄`), a set `s` of *split* (forcibly
outsourced) chores whose price is shared by the payment vector `q`, covering all chores, and
where every part costs at most `r`. -/
def ConfigC (c p : T → ℝ) (r : ℝ) (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint s (A i)) ∧
  (s ∪ Finset.univ.biUnion A = Finset.univ) ∧ (∀ i, 0 ≤ q i) ∧
  (∑ i, q i = ∑ t ∈ s, p t) ∧ (∀ i, cbarSum c p (A i) + q i ≤ r)

omit [Fintype T] in
lemma cbarSum_union (c p : T → ℝ) {A B : Finset T} (h : Disjoint A B) :
    cbarSum c p (A ∪ B) = cbarSum c p A + cbarSum c p B := by
  simp only [cbarSum]; rw [Finset.sum_union h]

omit [Fintype T] [DecidableEq T] in
lemma cbarSum_singleton (c p : T → ℝ) (t : T) : cbarSum c p ({t} : Finset T) = cbar c p t := by
  simp [cbarSum]

/-- One reduction step: if the split set has at least two chores, one of them can be moved
into a group, strictly decreasing the number of split chores while preserving `ConfigC`. -/
theorem reduce_stepC (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (r : ℝ)
    (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ)
    (hcfg : ConfigC c p r A s q) (hcard : 2 ≤ s.card) :
    ∃ (A' : Fin 2 → Finset T) (s' : Finset T) (q' : Fin 2 → ℝ),
      ConfigC c p r A' s' q' ∧ s'.card < s.card := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hle⟩ := hcfg
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g, hgs, hgmin⟩ := s.exists_min_image p hne
  have hpg : 0 ≤ p g := hp g
  have hgA : ∀ k, g ∉ A k := fun k => Finset.disjoint_left.mp (hdisjs k) hgs
  have hsumbound : 2 * p g ≤ ∑ h ∈ s, p h := by
    calc 2 * p g ≤ (s.card : ℝ) * p g := by
          apply mul_le_mul_of_nonneg_right _ hpg; exact_mod_cast hcard
      _ = ∑ _h ∈ s, p g := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ h ∈ s, p h := Finset.sum_le_sum (fun h hh => hgmin h hh)
  have hq01 : q 0 + q 1 = ∑ h ∈ s, p h := by rw [← Fin.sum_univ_two q]; exact hsat
  have key : ∀ i j : Fin 2, i ≠ j → p g ≤ q i →
      ∃ (A' : Fin 2 → Finset T) (s' : Finset T) (q' : Fin 2 → ℝ),
        ConfigC c p r A' s' q' ∧ s'.card < s.card := by
    intro i j hij hqi
    have hk : ∀ k : Fin 2, k = i ∨ k = j := fun k => by omega
    refine ⟨Function.update A i (A i ∪ {g}), s.erase g, Function.update q i (q i - p g),
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Finset.card_erase_lt_of_mem hgs⟩
    · intro a b hab
      rcases hk a with ha | ha <;> rcases hk b with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · subst a; subst b
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Finset.disjoint_union_left]
        exact ⟨hdisjA i j hij, Finset.disjoint_singleton_left.mpr (hgA j)⟩
      · subst a; subst b
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Finset.disjoint_union_right]
        exact ⟨hdisjA j i (Ne.symm hij), Finset.disjoint_singleton_right.mpr (hgA j)⟩
      · exact absurd (ha.trans hb.symm) hab
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self, Finset.disjoint_union_right]
        refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) (hdisjs i), ?_⟩
        exact Finset.disjoint_singleton_right.mpr (fun h => (Finset.mem_erase.mp h).1 rfl)
      · rw [Function.update_of_ne hki]
        exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) (hdisjs k)
    · apply Finset.eq_univ_of_forall
      intro x
      have hx : x ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx ⊢
      rcases hx with hxs | ⟨k, hxk⟩
      · by_cases hxg : x = g
        · refine Or.inr ⟨i, ?_⟩
          rw [Function.update_self]
          exact Finset.mem_union_right _ (by rw [hxg]; exact Finset.mem_singleton_self g)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hxg, hxs⟩)
      · refine Or.inr ⟨k, ?_⟩
        by_cases hki : k = i
        · subst k; rw [Function.update_self]; exact Finset.mem_union_left _ hxk
        · rw [Function.update_of_ne hki]; exact hxk
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self]; linarith [hqi]
      · rw [Function.update_of_ne hki]; exact hq0 k
    · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_erase_eq_sub hgs]
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ ({i} : Finset (Fin 2))), Finset.sum_singleton]
      rw [hsat]; ring
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self, Function.update_self]
        rw [cbarSum_union c p (Finset.disjoint_singleton_right.mpr (hgA i)),
          cbarSum_singleton c p g]
        have hmin : cbar c p g ≤ p g := cbar_le_price g
        have := hle i
        linarith
      · rw [Function.update_of_ne hki, Function.update_of_ne hki]
        exact hle k
  rcases (show p g ≤ q 0 ∨ p g ≤ q 1 by
      by_contra h; push_neg at h; obtain ⟨h0, h1⟩ := h; linarith [hsumbound, hq01]) with h0 | h1
  · exact key 0 1 (by decide) h0
  · exact key 1 0 (by decide) h1

/-- Iterating `reduce_stepC` we reach a configuration with at most one split chore. -/
theorem reduce_to_oneC (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ),
      ConfigC c p r A s q → s.card ≤ k →
      ∃ (A' : Fin 2 → Finset T) (s' : Finset T) (q' : Fin 2 → ℝ),
        ConfigC c p r A' s' q' ∧ s'.card ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro A s q hcfg hk
    exact ⟨A, s, q, hcfg, hk.trans (by norm_num)⟩
  | succ k ih =>
    intro A s q hcfg hk
    by_cases hc : s.card ≤ 1
    · exact ⟨A, s, q, hcfg, hc⟩
    · have h2 : 2 ≤ s.card := by omega
      obtain ⟨A', s', q', hcfg', hlt⟩ := reduce_stepC c p hp r A s q hcfg h2
      exact ih A' s' q' hcfg' (by omega)

/-- **Lemma 5 for chores, `n = 2`.** Every cost function has an MMS partition into two parts
that forcibly outsources at most one chore. -/
theorem exists_reducedC (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) :
    ∃ (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ),
      ConfigC c p (MMS 2 c p) A s q ∧ s.card ≤ 1 := by
  classical
  obtain ⟨o, hovalid, hle⟩ := exists_MMS_partition_chores (n := 2) (by norm_num) c p hc hp
  obtain ⟨hdo, hdk, hcov, hpay0, hbudget⟩ := hovalid
  obtain ⟨q, hq0, hqle, hqsum⟩ :=
    exists_shrink (n := 2) (bill := ∑ t ∈ o.outsourced, p t)
      (Finset.sum_nonneg fun t _ => hp t) o.pay hpay0 hbudget
  have hcfg : ConfigC c p (MMS 2 c p) o.kept o.outsourced q := by
    refine ⟨fun i j hij => hdk i j hij, fun i => hdo i, hcov, hq0, hqsum, fun i => ?_⟩
    have h1 : cbarSum c p (o.kept i) ≤ ∑ t ∈ o.kept i, c t := cbarSum_le_sum c p _
    have h2 := hle i
    simp only [cost] at h2
    linarith [hqle i]
  exact reduce_to_oneC c p hp (MMS 2 c p) o.outsourced.card o.kept o.outsourced q hcfg le_rfl

omit [Fintype T] in
lemma biU_twoC (A : Fin 2 → Finset T) : Finset.univ.biUnion A = A 0 ∪ A 1 := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Fin.exists_fin_two]

/-- From a two-part configuration in which both parts cost at most `M`, the total effective
cost of the unsplit chores plus the price of the split chores is at most `2 M`. -/
lemma configC_sum_bound (c p : T → ℝ) (M : ℝ) (A : Fin 2 → Finset T) (s : Finset T)
    (q : Fin 2 → ℝ) (h : ConfigC c p M A s q) :
    cbarSum c p (Finset.univ \ s) + ∑ t ∈ s, p t ≤ 2 * M := by
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hle⟩ := h
  rw [biU_twoC A] at hcover
  have hAunion : A 0 ∪ A 1 = Finset.univ \ s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (hx | hx)
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 0) hxs hx
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 1) hxs hx
    · intro hxs
      have hmem : x ∈ s ∪ (A 0 ∪ A 1) := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hmem with h' | h'
      · exact absurd h' hxs
      · exact Finset.mem_union.mp h'
  have hcb : cbarSum c p (A 0 ∪ A 1) = cbarSum c p (A 0) + cbarSum c p (A 1) :=
    cbarSum_union c p (hdisjA 0 1 (by decide))
  have hqsum : q 0 + q 1 = ∑ t ∈ s, p t := by rw [← Fin.sum_univ_two q]; exact hsat
  rw [← hAunion, hcb]
  linarith [hle 0, hle 1, hqsum]

/-- Realize a two-agent unified assignment (agent `0` handles `B0`, agent `1` handles `B1`,
the chores of `F` are forcibly outsourced with the bill split as `r0, r1`) as a feasible
outcome with the stated costs. -/
lemma realize2C (c : Fin 2 → T → ℝ) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (B0 B1 F : Finset T) (r0 r1 : ℝ)
    (hd01 : Disjoint B0 B1) (hdF0 : Disjoint F B0) (hdF1 : Disjoint F B1)
    (hcover : F ∪ (B0 ∪ B1) = Finset.univ)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hsum : r0 + r1 = ∑ t ∈ F, p t) :
    ∃ o : Outcome T 2, o.Valid p ∧
      cost (c 0) o 0 = cbarSum (c 0) p B0 + r0 ∧
      cost (c 1) o 1 = cbarSum (c 1) p B1 + r1 := by
  classical
  obtain ⟨o, hvalid, hcost⟩ :=
    exists_outcome_of_preAlloc ⟨![B0, B1], F, ![r0, r1]⟩ p c hp
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [hd01.symm])
      (by intro i; fin_cases i <;> simpa)
      (by
        show F ∪ Finset.univ.biUnion ![B0, B1] = Finset.univ
        rw [biU_twoC]
        simpa using hcover)
      (by intro i; fin_cases i <;> simpa)
      (by rw [Fin.sum_univ_two]; simpa using hsum)
  exact ⟨o, hvalid, by simpa using hcost 0, by simpa using hcost 1⟩

/-- Swap the two parts of an outcome. -/
def swapOutcomeC (o : Outcome T 2) : Outcome T 2 where
  outsourced := o.outsourced
  kept := fun i => o.kept (Equiv.swap 0 1 i)
  pay := fun i => o.pay (Equiv.swap 0 1 i)

omit [Fintype T] [DecidableEq T] in
lemma cost_swapOutcomeC (c : T → ℝ) (o : Outcome T 2) (j : Fin 2) :
    cost c (swapOutcomeC o) j = cost c o (Equiv.swap 0 1 j) := rfl

lemma swapOutcomeC_valid (p : T → ℝ) (o : Outcome T 2) (h : o.Valid p) :
    (swapOutcomeC o).Valid p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun i => h1 _, fun i j hij => h2 _ _ (fun he => hij ((Equiv.swap 0 1).injective he)),
    ?_, fun i => h4 _, ?_⟩
  · show o.outsourced ∪ Finset.univ.biUnion (fun i => o.kept (Equiv.swap 0 1 i)) = Finset.univ
    rw [← h3]
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨Equiv.swap 0 1 i, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨Equiv.swap 0 1 i, by simpa using hi⟩
  · show _ ≤ ∑ i, o.pay (Equiv.swap 0 1 i)
    rw [Equiv.sum_comp (Equiv.swap 0 1) o.pay]; exact h5

/-- **Cut & Give for chores** (the heart of the two-agent argument). If agent `0` (the
*Cutter*) has a canonical MMS partition whose split chore is no more expensive than the
Giver's, then there is a feasible outcome in which agent `0` pays at most `MMS0` and agent
`1` pays at most `MMS1`. -/
lemma cutgiveC (c : Fin 2 → T → ℝ) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (Ac : Fin 2 → Finset T) (sc : Finset T) (qc : Fin 2 → ℝ)
    (hc : ConfigC (c 0) p (MMS 2 (c 0) p) Ac sc qc)
    (sg : Finset T) (hsg : sg.card ≤ 1)
    (hbound : cbarSum (c 1) p (Finset.univ \ sg) + ∑ t ∈ sg, p t ≤ 2 * MMS 2 (c 1) p)
    (hcut : ∑ t ∈ sc, p t ≤ ∑ t ∈ sg, p t) :
    ∃ o : Outcome T 2, o.Valid p ∧
      cost (c 0) o 0 ≤ MMS 2 (c 0) p ∧ cost (c 1) o 1 ≤ MMS 2 (c 1) p := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hle⟩ := hc
  set M0 := MMS 2 (c 0) p
  set M1 := MMS 2 (c 1) p
  have hqsum : qc 0 + qc 1 = ∑ t ∈ sc, p t := by rw [← Fin.sum_univ_two qc]; exact hsat
  have hcoverC : sc ∪ (Ac 0 ∪ Ac 1) = Finset.univ := by rw [← biU_twoC Ac]; exact hcover
  by_cases hCC : ∃ t : Fin 2, cbarSum (c 1) p (Ac t) + qc t ≤ M1
  · -- Cut & Choose: the Giver takes an acceptable part, the Cutter the other one
    obtain ⟨t, ht⟩ := hCC
    fin_cases t
    · obtain ⟨o, hov, h0, h1⟩ := realize2C c p hp (Ac 1) (Ac 0) sc (qc 1) (qc 0)
        (hdisjA 1 0 (by decide)) (hdisjs 1) (hdisjs 0)
        (by rw [Finset.union_comm (Ac 1) (Ac 0)]; exact hcoverC)
        (hq0 1) (hq0 0) (by rw [add_comm]; exact hqsum)
      exact ⟨o, hov, by rw [h0]; exact hle 1, by rw [h1]; exact ht⟩
    · obtain ⟨o, hov, h0, h1⟩ := realize2C c p hp (Ac 0) (Ac 1) sc (qc 0) (qc 1)
        (hdisjA 0 1 (by decide)) (hdisjs 0) (hdisjs 1) hcoverC (hq0 0) (hq0 1) hqsum
      exact ⟨o, hov, by rw [h0]; exact hle 0, by rw [h1]; exact ht⟩
  · -- Cut & Give: no part is acceptable to the Giver
    push_neg at hCC
    have htex : ∃ t : Fin 2, Disjoint (Ac t) sg := by
      by_cases hd0 : Disjoint (Ac 0) sg
      · exact ⟨0, hd0⟩
      · refine ⟨1, ?_⟩
        rw [Finset.not_disjoint_iff] at hd0
        obtain ⟨x, hxA, hxs⟩ := hd0
        rw [Finset.disjoint_left]
        intro y hyA hys
        have hxy : x = y := Finset.card_le_one.mp hsg x hxs y hys
        subst hxy
        exact Finset.disjoint_left.mp (hdisjA 1 0 (by decide)) hyA hxA
    obtain ⟨t, htd⟩ := htex
    have hAtsub : Ac t ⊆ Finset.univ \ sg := Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, htd⟩
    have hqct_le : qc t ≤ ∑ t ∈ sg, p t := by
      have hle' : qc t ≤ qc 0 + qc 1 := by
        rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> linarith [hq0 0, hq0 1]
      linarith [hqsum, hcut]
    obtain ⟨o, hov, h0, h1⟩ := realize2C c p hp (Ac t) ((Finset.univ \ Ac t) \ sg) sg
      (qc t) ((∑ t ∈ sg, p t) - qc t)
      (Finset.disjoint_left.mpr fun y hy hy2 =>
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy2).1).2 hy)
      htd.symm
      (Finset.disjoint_left.mpr fun y hy hy2 => (Finset.mem_sdiff.mp hy2).2 hy)
      (by
        apply Finset.eq_univ_of_forall
        intro x
        by_cases hxg : x ∈ sg
        · exact Finset.mem_union_left _ hxg
        · by_cases hxA : x ∈ Ac t
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxA)
          · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxA⟩, hxg⟩)
      (hq0 t) (by linarith [hqct_le]) (by ring)
    refine ⟨o, hov, by rw [h0]; exact hle t, ?_⟩
    rw [h1]
    have hB1eq : (Finset.univ \ Ac t) \ sg = (Finset.univ \ sg) \ Ac t := sdiff_sdiff_comm
    have hcbsd : cbarSum (c 1) p ((Finset.univ \ Ac t) \ sg)
        = cbarSum (c 1) p (Finset.univ \ sg) - cbarSum (c 1) p (Ac t) := by
      rw [hB1eq]
      have := cbarSum_sdiff (c 1) p hAtsub
      linarith
    rw [hcbsd]
    linarith [hbound, hCC t]

/-- **Exact MMS for two agents, chores with outsourcing.** There is a feasible outcome in
which each of the two agents pays at most her maximin share. -/
theorem exists_MMS_two_chores (c : Fin 2 → T → ℝ) (p : T → ℝ)
    (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T 2, o.Valid p ∧ ∀ i, cost (c i) o i ≤ MMS 2 (c i) p := by
  obtain ⟨Ac0, sc0, qc0, hcfg0, hcard0⟩ := exists_reducedC (c 0) p (hc 0) hp
  obtain ⟨Ac1, sc1, qc1, hcfg1, hcard1⟩ := exists_reducedC (c 1) p (hc 1) hp
  have hb0 := configC_sum_bound (c 0) p (MMS 2 (c 0) p) Ac0 sc0 qc0 hcfg0
  have hb1 := configC_sum_bound (c 1) p (MMS 2 (c 1) p) Ac1 sc1 qc1 hcfg1
  by_cases hcut : ∑ t ∈ sc0, p t ≤ ∑ t ∈ sc1, p t
  · obtain ⟨o, hov, h0, h1⟩ := cutgiveC c p hp Ac0 sc0 qc0 hcfg0 sc1 hcard1 hb1 hcut
    exact ⟨o, hov, fun i => by fin_cases i <;> assumption⟩
  · push_neg at hcut
    obtain ⟨o, hov, h0, h1⟩ := cutgiveC (fun i => c (Equiv.swap 0 1 i)) p hp Ac1 sc1 qc1
      (by simpa [Equiv.swap_apply_left] using hcfg1) sc0 hcard0
      (by simpa [Equiv.swap_apply_right] using hb0) (le_of_lt hcut)
    refine ⟨swapOutcomeC o, swapOutcomeC_valid p o hov, fun i => ?_⟩
    fin_cases i
    · rw [cost_swapOutcomeC]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h1
    · rw [cost_swapOutcomeC]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h0

end FairChores
