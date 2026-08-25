import Mathlib

/-!
# Chores with Outsourcing — the model

This file formalizes the *chores with outsourcing* model of the manuscript's appendix
"Extension: Chores with Outsourcing".

The model is the mirror image of the goods-with-selling model of `RequestProject.Selling`:

* chores are the elements of a finite type `T`;
* agent `i` has an additive, non-negative **cost** function `c i : T → ℝ`;
* every chore `t` can be **outsourced** at the publicly known market price `p t ≥ 0`, the
  payment being divisibly shared between the agents;
* following the manuscript we write `c̄ᵢ(t) = min {cᵢ(t), p(t)}` (`cbar`) for the effective
  cost of a chore to agent `i`: either the agent performs it, or the agent pays for it to be
  outsourced.

An outcome `(S, A, P)` records the set `S` of outsourced chores, the bundle `A j` of chores
performed by agent `j`, and the amount `P j` of the outsourcing bill paid by agent `j`.
Feasibility (`Outcome.Valid`) requires that **every** chore is either outsourced or performed
by exactly one agent (chores, unlike goods, must all be allocated), that payments are
non-negative and that the outsourcing bill is covered: `∑ t ∈ S, p t ≤ ∑ j, P j`.

The disutility of agent `i` in part `j` is `costᵢ(A j, P j) = ∑ t ∈ A j, cᵢ(t) + P j`, and the
**maximin share** `MMSᵢ` is the least value `r` such that some feasible outcome has all parts
of cost at most `r` (an infimum instead of the supremum used for goods).
-/

open scoped BigOperators

namespace FairChores

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- An outcome of a chores allocation with outsourcing: which chores are outsourced, which
bundle of chores each agent performs, and how the outsourcing bill is split. -/
structure Outcome (T : Type*) (n : ℕ) where
  /-- The set of chores that are outsourced. -/
  outsourced : Finset T
  /-- The bundle of chores performed by each agent. -/
  kept : Fin n → Finset T
  /-- The part of the outsourcing bill paid by each agent. -/
  pay : Fin n → ℝ

variable {n : ℕ}

/-- Feasibility of a chores outcome with respect to the outsourcing prices `p`. -/
def Outcome.Valid (p : T → ℝ) (o : Outcome T n) : Prop :=
  (∀ j, Disjoint o.outsourced (o.kept j)) ∧
  (∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k)) ∧
  (o.outsourced ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧
  (∀ j, 0 ≤ o.pay j) ∧
  (∑ t ∈ o.outsourced, p t ≤ ∑ j, o.pay j)

/-- The disutility (cost) of the agent with cost function `c` for part `j` of the outcome `o`:
the cost of the chores it performs plus the share of the outsourcing bill it pays. -/
def cost (c : T → ℝ) (o : Outcome T n) (j : Fin n) : ℝ := (∑ t ∈ o.kept j, c t) + o.pay j

/-- The effective cost `c̄ᵢ(t) = min {cᵢ(t), p(t)}` of a chore. -/
def cbar (c p : T → ℝ) (t : T) : ℝ := min (c t) (p t)

/-- The effective cost of a set of chores. -/
def cbarSum (c p : T → ℝ) (A : Finset T) : ℝ := ∑ t ∈ A, cbar c p t

/-- The set of values `r` such that some feasible outcome costs every agent at most `r`. -/
def MMSset (n : ℕ) (c p : T → ℝ) : Set ℝ :=
  {r | ∃ o : Outcome T n, o.Valid p ∧ ∀ j, cost c o j ≤ r}

/-- **Maximin share for chores with outsourcing**: the least cost an agent can guarantee
itself by partitioning the chores (and choosing what to outsource and how to split the bill)
into `n` parts, if it then receives the worst part. -/
noncomputable def MMS (n : ℕ) (c p : T → ℝ) : ℝ := sInf (MMSset n c p)

section Basic

variable {c p : T → ℝ}

omit [Fintype T] [DecidableEq T] in
@[simp] lemma cbarSum_empty (c p : T → ℝ) : cbarSum c p (∅ : Finset T) = 0 := by
  simp [cbarSum]

omit [Fintype T] [DecidableEq T] in
lemma cbar_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (t : T) : 0 ≤ cbar c p t :=
  le_min (hc t) (hp t)

omit [Fintype T] [DecidableEq T] in
lemma cbar_le_cost (t : T) : cbar c p t ≤ c t := min_le_left _ _

omit [Fintype T] [DecidableEq T] in
lemma cbar_le_price (t : T) : cbar c p t ≤ p t := min_le_right _ _

omit [Fintype T] [DecidableEq T] in
lemma cbarSum_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (A : Finset T) :
    0 ≤ cbarSum c p A :=
  Finset.sum_nonneg fun t _ => cbar_nonneg hc hp t

omit [Fintype T] [DecidableEq T] in
lemma cbarSum_mono (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p A ≤ cbarSum c p B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun t _ _ => cbar_nonneg hc hp t

omit [Fintype T] in
lemma cbarSum_sdiff (c p : T → ℝ) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p B = cbarSum c p (B \ A) + cbarSum c p A := by
  simp only [cbarSum]
  rw [← Finset.sum_sdiff h]

omit [Fintype T] [DecidableEq T] in
lemma cbarSum_le_sum (c p : T → ℝ) (A : Finset T) : cbarSum c p A ≤ ∑ t ∈ A, c t :=
  Finset.sum_le_sum fun t _ => cbar_le_cost t

omit [Fintype T] [DecidableEq T] in
lemma single_le_cbarSum (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A : Finset T} {t : T}
    (ht : t ∈ A) : cbar c p t ≤ cbarSum c p A :=
  Finset.single_le_sum (fun s _ => cbar_nonneg hc hp s) ht

/-- In a feasible outcome, every chore is either outsourced or performed by exactly one
agent, so any additive quantity splits accordingly. -/
lemma Outcome.sum_split {o : Outcome T n} (hvalid : o.Valid p) (f : T → ℝ) :
    ∑ t, f t = (∑ t ∈ o.outsourced, f t) + ∑ j, ∑ t ∈ o.kept j, f t := by
  classical
  obtain ⟨hdo, hdk, hcov, -, -⟩ := hvalid
  have hdisj : Disjoint o.outsourced (Finset.univ.biUnion o.kept) := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hx'
    exact Finset.disjoint_left.mp (hdo j) hx hj
  have h1 : ∑ t, f t = ∑ t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept, f t := by
    rw [hcov]
  rw [h1, Finset.sum_union hdisj, Finset.sum_biUnion (fun i _ j _ hij => hdk i j hij)]

/-- The total cost of a feasible outcome is at least the total effective cost of all chores.
(This is the manuscript's `n · MMSᵢ ≥ c̄ᵢ(M)`, before taking the infimum.) -/
lemma cbarSum_univ_le_sum_cost {o : Outcome T n} (hvalid : o.Valid p) :
    cbarSum c p Finset.univ ≤ ∑ j, cost c o j := by
  classical
  have hsplit := Outcome.sum_split hvalid (cbar c p)
  have h1 : ∑ j, cost c o j
      = (∑ j, ∑ t ∈ o.kept j, c t) + ∑ j, o.pay j := by
    simp [cost, Finset.sum_add_distrib]
  have h2 : ∑ t ∈ o.outsourced, cbar c p t ≤ ∑ t ∈ o.outsourced, p t :=
    Finset.sum_le_sum fun t _ => cbar_le_price t
  have h3 : ∀ j, ∑ t ∈ o.kept j, cbar c p t ≤ ∑ t ∈ o.kept j, c t :=
    fun j => Finset.sum_le_sum fun t _ => cbar_le_cost t
  have h4 : ∑ j, ∑ t ∈ o.kept j, cbar c p t ≤ ∑ j, ∑ t ∈ o.kept j, c t :=
    Finset.sum_le_sum fun j _ => h3 j
  have h5 := hvalid.2.2.2.2
  simp only [cbarSum]
  rw [hsplit, h1]
  linarith

end Basic

section MMSBasic

variable {c p : T → ℝ}

/-- Every part of a feasible outcome has non-negative cost. -/
lemma cost_nonneg (hc : ∀ t, 0 ≤ c t) {o : Outcome T n} (hvalid : o.Valid p) (j : Fin n) :
    0 ≤ cost c o j :=
  add_nonneg (Finset.sum_nonneg fun t _ => hc t) (hvalid.2.2.2.1 j)

/-- `MMSset` is bounded below by `0` (as soon as there is at least one agent). -/
lemma MMSset_bddBelow (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : BddBelow (MMSset n c p) := by
  refine ⟨0, ?_⟩
  rintro r ⟨o, hvalid, hle⟩
  exact le_trans (cost_nonneg hc hvalid ⟨0, hn⟩) (hle ⟨0, hn⟩)

/-- Outsourcing nothing and giving every chore to agent `0` is feasible, so `MMSset` is
nonempty. -/
lemma MMSset_nonempty (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : (MMSset n c p).Nonempty := by
  classical
  refine ⟨∑ t, c t, ⟨∅, fun j => if j = ⟨0, hn⟩ then Finset.univ else ∅, fun _ => 0⟩, ?_, ?_⟩
  · refine ⟨by simp, ?_, ?_, by simp, by simp⟩
    · intro j k hjk
      by_cases hj : j = ⟨0, hn⟩ <;> by_cases hk : k = ⟨0, hn⟩ <;> simp [hj, hk]
      exact absurd (hj.trans hk.symm) hjk
    · refine Finset.eq_univ_iff_forall.mpr fun t => ?_
      simp only [Finset.empty_union, Finset.mem_biUnion]
      exact ⟨⟨0, hn⟩, Finset.mem_univ _, by simp⟩
  · intro j
    by_cases hj : j = ⟨0, hn⟩
    · simp [cost, hj]
    · simp [cost, hj]
      exact Finset.sum_nonneg fun t _ => hc t

/-- The maximin share is non-negative. -/
lemma MMS_nonneg (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : 0 ≤ MMS n c p :=
  le_csInf (MMSset_nonempty hc hn) (by
    rintro r ⟨o, hvalid, hle⟩
    exact le_trans (cost_nonneg hc hvalid ⟨0, hn⟩) (hle ⟨0, hn⟩))

/-- If every part of a feasible outcome costs at most `r`, then every chore whose in-house
cost exceeds `r` is outsourced.  For `r = MMSᵢ` this is the manuscript's observation that
a chore that is too expensive for agent `i` must be outsourced in its MMS partition. -/
lemma mem_outsourced_of_lt_cost {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    {r : ℝ} (hle : ∀ j, cost c o j ≤ r) {t : T} (ht : r < c t) : t ∈ o.outsourced := by
  classical
  by_contra hnot
  have hmem : t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept := by
    rw [hvalid.2.2.1]; exact Finset.mem_univ t
  rcases Finset.mem_union.mp hmem with h | h
  · exact hnot h
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp h
    have h1 : c t ≤ ∑ s ∈ o.kept j, c s :=
      Finset.single_le_sum (fun s _ => hc s) hj
    have h2 := hvalid.2.2.2.1 j
    have h3 := hle j
    simp only [cost] at h3
    linarith

/-- Without outsourcing, no chore costs more than the value guaranteed by the partition: the
property that underlies the classical bag-filling `2`-approximation for indivisible chores
(Algorithm 12 of the manuscript). -/
lemma cost_le_of_outsourced_empty {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    (hempty : o.outsourced = ∅) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) (t : T) : c t ≤ r := by
  by_contra hgt
  have hmem := mem_outsourced_of_lt_cost hvalid hc hle (not_le.mp hgt)
  rw [hempty] at hmem
  exact absurd hmem (Finset.notMem_empty t)

end MMSBasic

/-! ### The weight function `wt`

For the analysis of the bag-filling algorithm we need a bound on `n · MMSᵢ` sharper than
`c̄ᵢ(M) ≤ n · MMSᵢ`: a chore `t` that is *expensive* for agent `i` (i.e. `c̄ᵢ(t) > MMSᵢ`) has to
be outsourced in any of agent `i`'s optimal partitions, hence contributes its full market
price `p(t)` — and not merely `c̄ᵢ(t)` — to the total cost of that partition. -/

/-- The weight of a chore relative to a threshold `mu`: the market price for chores that are
expensive for the agent (`mu < c̄ᵢ(t)`), and the effective cost otherwise. -/
noncomputable def wt (c p : T → ℝ) (mu : ℝ) (t : T) : ℝ :=
  if mu < cbar c p t then p t else cbar c p t

/-- The total weight of a set of chores. -/
noncomputable def wtSum (c p : T → ℝ) (mu : ℝ) (A : Finset T) : ℝ := ∑ t ∈ A, wt c p mu t

section Weight

variable {c p : T → ℝ} {mu : ℝ}

omit [Fintype T] [DecidableEq T] in
lemma cbar_le_wt (t : T) : cbar c p t ≤ wt c p mu t := by
  unfold wt
  split
  · exact cbar_le_price t
  · exact le_rfl

omit [Fintype T] [DecidableEq T] in
lemma wt_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (t : T) : 0 ≤ wt c p mu t :=
  le_trans (cbar_nonneg hc hp t) (cbar_le_wt t)

omit [Fintype T] [DecidableEq T] in
lemma cbarSum_le_wtSum (A : Finset T) : cbarSum c p A ≤ wtSum c p mu A :=
  Finset.sum_le_sum fun t _ => cbar_le_wt t

omit [Fintype T] [DecidableEq T] in
lemma wtSum_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (A : Finset T) :
    0 ≤ wtSum c p mu A :=
  Finset.sum_nonneg fun t _ => wt_nonneg hc hp t

omit [Fintype T] in
lemma wtSum_sdiff {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu B = wtSum c p mu (B \ A) + wtSum c p mu A := by
  simp only [wtSum]
  rw [← Finset.sum_sdiff h]

omit [Fintype T] [DecidableEq T] in
lemma wtSum_mono (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu A ≤ wtSum c p mu B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun t _ _ => wt_nonneg hc hp t

/-- If no chore has effective cost in the interval `(mu, r]` and some feasible outcome costs
every agent at most `r`, then the total weight of all chores is at most `n · r`. -/
lemma wtSum_univ_le_of_mem_MMSset (hc : ∀ t, 0 ≤ c t) {r : ℝ}
    (hgap : ∀ t, mu < cbar c p t → r < cbar c p t) (hr : r ∈ MMSset n c p) :
    wtSum c p mu Finset.univ ≤ n * r := by
  classical
  obtain ⟨o, hvalid, hle⟩ := hr
  have hsplit := Outcome.sum_split hvalid (wt c p mu)
  have h1 : ∑ t ∈ o.outsourced, wt c p mu t ≤ ∑ t ∈ o.outsourced, p t :=
    Finset.sum_le_sum fun t _ => by
      unfold wt; split
      · exact le_rfl
      · exact cbar_le_price t
  have h2 : ∀ j, ∑ t ∈ o.kept j, wt c p mu t ≤ ∑ t ∈ o.kept j, c t := by
    intro j
    refine Finset.sum_le_sum fun t ht => ?_
    unfold wt
    split
    · rename_i hexp
      exfalso
      have hgt := hgap t hexp
      have hct : r < c t := lt_of_lt_of_le hgt (cbar_le_cost t)
      have hmem := mem_outsourced_of_lt_cost hvalid hc hle hct
      exact Finset.disjoint_left.mp (hvalid.1 j) hmem ht
    · exact cbar_le_cost t
  have h3 : ∑ j, ∑ t ∈ o.kept j, wt c p mu t ≤ ∑ j, ∑ t ∈ o.kept j, c t :=
    Finset.sum_le_sum fun j _ => h2 j
  have h4 : ∑ j, cost c o j ≤ n * r := by
    calc ∑ j : Fin n, cost c o j ≤ ∑ _j : Fin n, r := Finset.sum_le_sum fun j _ => hle j
      _ = n * r := by simp [mul_comm]
  have h5 : ∑ j, cost c o j = (∑ j, ∑ t ∈ o.kept j, c t) + ∑ j, o.pay j := by
    simp [cost, Finset.sum_add_distrib]
  have h6 := hvalid.2.2.2.2
  simp only [wtSum]
  rw [hsplit]
  linarith

/-- **The key bound**: the total weight of all chores, relative to the threshold `MMSᵢ`, is at
most `n · MMSᵢ`.  Since `c̄ᵢ ≤ wtᵢ` this refines the manuscript's `c̄ᵢ(M) ≤ n · MMSᵢ`. -/
theorem wtSum_univ_le_nsmul_MMS (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) :
    wtSum c p (MMS n c p) Finset.univ ≤ n * MMS n c p := by
  classical
  set mu := MMS n c p with hmudef
  obtain ⟨d, hd, hgapd⟩ :
      ∃ d : ℝ, 0 < d ∧ ∀ t, mu < cbar c p t → mu + d ≤ cbar c p t := by
    set S := (Finset.univ.image fun t => cbar c p t).filter (fun x => mu < x) with hS
    rcases S.eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, fun t ht => ?_⟩
      exfalso
      have hmem : cbar c p t ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_image]
        exact ⟨⟨t, Finset.mem_univ t, rfl⟩, ht⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · refine ⟨S.min' hne - mu, ?_, fun t ht => ?_⟩
      · have hmin := S.min'_mem hne
        simp only [hS, Finset.mem_filter] at hmin
        linarith [hmin.2]
      · have hmem : cbar c p t ∈ S := by
          simp only [hS, Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨t, Finset.mem_univ t, rfl⟩, ht⟩
        have := S.min'_le _ hmem
        linarith
  have hkey : ∀ ε : ℝ, 0 < ε → ε < d → wtSum c p mu Finset.univ ≤ n * mu + n * ε := by
    intro ε hε hεd
    obtain ⟨r, hrmem, hrlt⟩ : ∃ r ∈ MMSset n c p, r < mu + ε :=
      exists_lt_of_csInf_lt (MMSset_nonempty hc hn) (by
        show MMS n c p < mu + ε
        rw [← hmudef]; linarith)
    have hgap : ∀ t, mu < cbar c p t → r < cbar c p t := by
      intro t ht
      have := hgapd t ht
      linarith
    have hbd := wtSum_univ_le_of_mem_MMSset hc hgap hrmem
    have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  refine le_of_forall_pos_le_add ?_
  intro ε' hε'
  set ε := min (d / 2) (ε' / n) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεd : ε < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 := hkey ε hε hεd
  have h2 : (n:ℝ) * ε ≤ ε' := by
    have h3 : ε ≤ ε' / n := min_le_right _ _
    calc (n:ℝ) * ε ≤ n * (ε' / n) := by nlinarith
      _ = ε' := by field_simp
  linarith

end Weight

end FairChores
