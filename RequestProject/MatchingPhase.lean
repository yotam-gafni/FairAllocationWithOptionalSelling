import Mathlib
import RequestProject.CanonicalPartition
import RequestProject.Matching
import RequestProject.ThreeAgentCashComposition

/-!
# The matching phase of the `n = 3`, `3/4`-MMS algorithm

After the preliminary phase (no good is worth `3/4 · MMS` to anybody) one agent — the
*partitioning agent* — proposes a canonical partition of the goods into three bundles, each worth
at least `3/4 · MMS` to itself (manuscript Lemma 3, proved in `CanonicalPartition`).  One of the
bundles is the unrestricted *leftovers* bundle; the two others are *pure* (they carry no sale
money) or *singleton* (one good plus the proceeds of a single sold good).

The manuscript then matches the two non-partitioning agents against the two non-leftovers bundles.
This file analyses that matching phase completely, including the case the manuscript leaves
implicit (an agent that finds *every* bundle unacceptable).  The outcome of the analysis is:

* `matching_phase_two` — the combinatorial trichotomy of the `2 × 2` matching: either a perfect
  matching, or a bundle rejected by both agents, or one agent accepts both bundles while the
  other accepts neither.
* `special_case_pure_allocation` — in the special (third) case, if one of the two non-leftovers
  bundles is pure, a complete `3/4`-MMS allocation of *all three* agents exists outright.
* `canonical_partitioner_survives` — after any single canonical bundle has been handed out, the
  partitioning agent can still split what remains (goods plus banked proceeds) into two parts
  worth `3/4 · MMS` each.  In particular a loss of *exactly* `3/4 · MMS` is as harmless as a
  strictly smaller one.
* `canonical_shave` — the manuscript's "w.l.o.g. the singleton bundles are worth *exactly*
  `3/4 · MMS` to the partitioning agent" step: excess sale money can always be moved to the
  leftovers bundle.  (`canonical_partitioner_survives` shows the step is in fact not needed:
  a loss of exactly `3/4 · MMS` is as harmless as a strict one.)
* `matching_phase_three` — the resulting dichotomy: either the whole instance is already solved,
  or we are in a **single loss event**: one agent is served with a pure-or-singleton bundle
  funded by at most one sold good, and each remaining agent either already has its guarantee or
  values the allocated bundle at most `3/4 · MMS`.

`SingleLossConfig` is exactly the input of the manuscript's Lemma 4, whose cash-aware form is
recorded here as the interface `LemmaFourCash`.  The pure case of Lemma 4 is proved here
(`lemmaFour_of_no_undervaluation`), and `lemmaFourCash_of_sold` reduces Lemma 4 to its residual
singleton case, which is proved in `RequestProject.LemmaFourResidual`.  The price condition on
force-sold goods that these interfaces carry is genuinely needed — see `not_lemmaFourCashNoPrice`
in `RequestProject.LemmaFourNecessity`.  Finally
`exists_threequarter_MMS_three_of_canonical` assembles everything.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-! ## The combinatorial matching phase -/

/-- **The matching phase, combinatorially.**  Two agents (`Fin 2`) are matched against the two
non-leftovers bundles (`Fin 2`), agent `j` accepting bundle `k` iff `acc j k = true`.  Then
exactly one of the following happens:

* a **perfect matching** exists;
* some bundle is **rejected by both** agents;
* one agent accepts **both** bundles and the other agent accepts **neither** — the special case.

Proved by exhaustive case analysis. -/
theorem matching_phase_two (acc : Fin 2 → Fin 2 → Bool) :
    (∃ σ : Equiv.Perm (Fin 2), ∀ j, acc j (σ j) = true)
    ∨ (∃ k, ∀ j, acc j k = false)
    ∨ (∃ j j' : Fin 2, j ≠ j' ∧ (∀ k, acc j k = true) ∧ (∀ k, acc j' k = false)) := by
  revert acc
  decide

/-! ## Two-agent remainders with banked cash and a sellable reserve -/

omit [Fintype G] in
/-- Bundles of ordinary goods inside the remainder keep their `v̄`-value in the cash-augmented
instance. -/
lemma vbarSum_map_some (R : Finset G) (w p : G → ℝ) (c : ℝ) {C : Finset G} (hC : C ⊆ R) :
    vbarSum (cashVal R w) (cashPrice R p c) (C.map Function.Embedding.some)
      = vbarSum w p C := by
  classical
  simp only [vbarSum, Finset.sum_map, Function.Embedding.some_apply, vbar, cashVal_some,
    cashPrice_some]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [restrictVal_mem R w (hC hg), restrictVal_mem R p (hC hg)]

/-- **Two bundles with banked cash and a sellable reserve.**  If the remainder `R` contains two
disjoint bundles `C, D` and a further disjoint set `T` whose goods may be sold, and the banked
cash `c` together with the proceeds of `T` can top both bundles up to `τ`, then the two-agent
maximin share of the cash-augmented remainder is at least `τ`.

This strengthens `MMS2_cash_of_two_bundles` (the case `T = ∅`): the proceeds of `T` are divisible,
so they may be split between the two bundles. -/
lemma MMS2_cash_of_two_bundles_sell (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C D T : Finset G) (c c0 c1 τ : ℝ)
    (hCD : Disjoint C D) (hCT : Disjoint C T) (hDT : Disjoint D T)
    (hCR : C ⊆ R) (hDR : D ⊆ R) (hTR : T ⊆ R)
    (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hbudget : c0 + c1 ≤ c + ∑ g ∈ T, p g)
    (hC : τ ≤ vbarSum w p C + c0) (hD : τ ≤ vbarSum w p D + c1) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p c) := by
  classical
  set A : Fin 2 → Finset (Option G) :=
    ![C.map Function.Embedding.some, D.map Function.Embedding.some] with hA
  set F : Finset (Option G) := insert none (T.map Function.Embedding.some) with hF
  set q : Fin 2 → ℝ := ![c0, c1] with hq
  have hsumF : ∑ x ∈ F, cashPrice R p c x = c + ∑ g ∈ T, p g := by
    have hnone : none ∉ T.map Function.Embedding.some := by simp
    rw [hF, Finset.sum_insert hnone, cashPrice_none, Finset.sum_map]
    congr 1
    exact Finset.sum_congr rfl (fun g hg => by
      simpa using restrictVal_mem R p (hTR hg))
  refine le_MMS_of_outcome (by norm_num) _ _ (cashVal_nonneg R w hw)
    (cashPrice_nonneg R p hp c hc)
    (unifiedOutcome (fun _ => cashVal R w) (cashPrice R p c) A F q) ?_ τ ?_
  · refine unifiedOutcome_valid _ _ (cashPrice_nonneg R p hp c hc) A F q ?_ ?_ ?_ ?_
    · intro i j hij
      have hmapCD : Disjoint (C.map Function.Embedding.some) (D.map Function.Embedding.some) :=
        (Finset.disjoint_map _).mpr hCD
      fin_cases i <;> fin_cases j <;> simp only [hA] at hij ⊢
      · exact absurd rfl hij
      · exact hmapCD
      · exact hmapCD.symm
      · exact absurd rfl hij
    · intro i
      have hnoneC : none ∉ C.map Function.Embedding.some := by simp
      have hnoneD : none ∉ D.map Function.Embedding.some := by simp
      have hmapTC : Disjoint (T.map Function.Embedding.some) (C.map Function.Embedding.some) :=
        (Finset.disjoint_map _).mpr hCT.symm
      have hmapTD : Disjoint (T.map Function.Embedding.some) (D.map Function.Embedding.some) :=
        (Finset.disjoint_map _).mpr hDT.symm
      fin_cases i <;>
        simp only [hA, hF, Finset.disjoint_insert_left]
      · exact ⟨hnoneC, hmapTC⟩
      · exact ⟨hnoneD, hmapTD⟩
    · intro i; fin_cases i
      · simpa [hq] using hc0
      · simpa [hq] using hc1
    · rw [hsumF, Fin.sum_univ_two]
      simpa [hq] using hbudget
  · intro j
    have hu := util_unifiedOutcome (fun _ : Fin 2 => cashVal R w) (cashPrice R p c) A F q j
    refine le_trans ?_ hu.ge
    fin_cases j
    · simpa [hA, hq, vbarSum_map_some R w p c hCR] using hC
    · simpa [hA, hq, vbarSum_map_some R w p c hDR] using hD

/-! ## Canonical partitions in the manuscript's strict form -/

/-- **Strictly canonical partition.**  In addition to `IsCanonical`, this records the two extra
structural facts the manuscript's construction provides:

* at most two goods are force-sold (Lemma 5 for `n = 3`);
* each non-leftovers bundle is *pure* (no money), or consists of a single good together with
  money coming from the sale of a **single** good `f`;
* that good is expensive: `p f ≥ τ / 3`, i.e. `p f ≥ (1 - 3/4) · MMS` when `τ = 3/4 · MMS`.
  This is condition 1 of the manuscript's definition of a canonical partition, and it is what
  bounds the value destroyed by force-selling `f`.
-/
def IsCanonicalStrict (w p : G → ℝ) (τ : ℝ) (kept : Fin 3 → Finset G) (sold : Finset G)
    (money : Fin 3 → ℝ) (leftover : Fin 3) : Prop :=
  IsCanonical w p τ kept sold money leftover ∧ sold.card ≤ 2 ∧
    ∀ k, k ≠ leftover →
      money k = 0 ∨ ((kept k).card = 1 ∧ ∃ f ∈ sold, money k ≤ p f ∧ τ / 3 ≤ p f)

omit [Fintype G] [DecidableEq G] in
/-- **Shaving a canonical partition.**  It is without loss of generality to assume that every
non-leftovers bundle of a canonical partition is worth *exactly* `τ` to the partitioning agent
(or carries no money at all): any excess sale money can be moved to the leftovers bundle.  The
resulting partition is still strictly canonical, and the leftovers bundle only got richer. -/
lemma canonical_shave (w p : G → ℝ) {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G}
    {money : Fin 3 → ℝ} {lo : Fin 3} (hcan : IsCanonicalStrict w p τ kept sold money lo) :
    ∃ money' : Fin 3 → ℝ, IsCanonicalStrict w p τ kept sold money' lo ∧
      (∀ k, k ≠ lo → money' k = 0 ∨ vbarSum w p (kept k) + money' k = τ) ∧
      (∀ k, k ≠ lo → money' k ≤ money k) ∧ money lo ≤ money' lo := by
  classical
  obtain ⟨⟨hdisj, hsold, hm0, hmsum, hacc, hpure⟩, hcard, hstrict⟩ := hcan
  set s : Fin 3 → ℝ := fun k => min (money k) (max 0 (τ - vbarSum w p (kept k))) with hs
  have hsdef : ∀ k, s k = min (money k) (max 0 (τ - vbarSum w p (kept k))) := fun k => rfl
  have hs0 : ∀ k, 0 ≤ s k := fun k => le_min (hm0 k) (le_max_left _ _)
  have hsle : ∀ k, s k ≤ money k := fun k => min_le_left _ _
  have hsexact : ∀ k, s k = 0 ∨ vbarSum w p (kept k) + s k = τ := by
    intro k
    rcases le_or_gt τ (vbarSum w p (kept k)) with h | h
    · left
      rw [hsdef k, max_eq_left (by linarith)]
      exact min_eq_right (hm0 k)
    · right
      have hmk : τ - vbarSum w p (kept k) ≤ money k := by linarith [hacc k]
      rw [hsdef k, max_eq_right (by linarith), min_eq_right hmk]
      ring
  have hsacc : ∀ k, τ ≤ vbarSum w p (kept k) + s k := by
    intro k
    rcases hsexact k with h | h
    · rcases le_or_gt τ (vbarSum w p (kept k)) with h' | h'
      · linarith [hs0 k]
      · exfalso
        have hmk : τ - vbarSum w p (kept k) ≤ money k := by linarith [hacc k]
        rw [hsdef k, max_eq_right (by linarith), min_eq_right hmk] at h
        linarith
    · linarith
  set E : ℝ := ∑ j ∈ Finset.univ.erase lo, (money j - s j) with hE
  have hEnn : 0 ≤ E := Finset.sum_nonneg (fun j _ => by linarith [hsle j])
  set money' : Fin 3 → ℝ := fun k => if k = lo then money lo + E else s k with hmoney'
  have hlo : money' lo = money lo + E := by simp [hmoney']
  have hne : ∀ k, k ≠ lo → money' k = s k := by intro k hk; simp [hmoney', hk]
  refine ⟨money', ⟨⟨hdisj, hsold, ?_, ?_, ?_, ?_⟩, hcard, ?_⟩, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = lo
    · rw [hk, hlo]; linarith [hm0 lo]
    · rw [hne k hk]; exact hs0 k
  · have hsplit : ∑ k, money' k = ∑ k, money k := by
      rw [← Finset.add_sum_erase _ money' (Finset.mem_univ lo),
        ← Finset.add_sum_erase _ money (Finset.mem_univ lo)]
      have h1 : ∑ j ∈ Finset.univ.erase lo, money' j = ∑ j ∈ Finset.univ.erase lo, s j :=
        Finset.sum_congr rfl (fun j hj => hne j (Finset.ne_of_mem_erase hj))
      rw [h1, hlo, hE, add_assoc, ← Finset.sum_add_distrib]
      have h2 : ∑ j ∈ Finset.univ.erase lo, (money j - s j + s j)
          = ∑ j ∈ Finset.univ.erase lo, money j :=
        Finset.sum_congr rfl (fun j _ => by ring)
      rw [h2]
    rw [hsplit]; exact hmsum
  · intro k
    by_cases hk : k = lo
    · rw [hk, hlo]; linarith [hacc lo]
    · rw [hne k hk]; exact hsacc k
  · intro k hk
    rcases hpure k hk with h | h
    · exact Or.inl (by rw [hne k hk]; exact le_antisymm (by rw [← h]; exact hsle k) (hs0 k))
    · exact Or.inr h
  · intro k hk
    rcases hstrict k hk with h | ⟨hc, f, hf, hfp, hfprice⟩
    · exact Or.inl (by rw [hne k hk]; exact le_antisymm (by rw [← h]; exact hsle k) (hs0 k))
    · exact Or.inr ⟨hc, f, hf, by rw [hne k hk]; exact (hsle k).trans hfp, hfprice⟩
  · intro k hk; rw [hne k hk]; exact hsexact k
  · intro k hk; rw [hne k hk]; exact hsle k
  · rw [hlo]; linarith

/-! ## Realizing allocations -/

omit [Fintype G] in
/-- Turning three pairwise disjoint bundles (with money financed by a force-sold set) into a valid
three-agent outcome. -/
lemma outcome_of_bundles (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (X : Fin 3 → Finset G) (F : Finset G) (q : Fin 3 → ℝ)
    (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hF : ∀ i, Disjoint F (X i))
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i ≤ ∑ g ∈ F, p g)
    (hval : ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ vbarSum (v i) p (X i) + q i) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  refine ⟨unifiedOutcome v p X F q, unifiedOutcome_valid v p hp X F q hX hF hq0 hq, fun i => ?_⟩
  rw [util_unifiedOutcome]
  exact hval i

omit [Fintype G] in
/-- **The perfect-matching case.**  If every agent is matched to a bundle of a canonical partition
that it accepts, the allocation is a valid `3/4`-MMS outcome. -/
lemma outcome_of_matching (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    {w : G → ℝ} {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ}
    {lo : Fin 3} (hcan : IsCanonical w p τ kept sold money lo)
    (σ : Equiv.Perm (Fin 3))
    (hacc : ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ vbarSum (v i) p (kept (σ i)) + money (σ i)) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨hdisj, hsold, hm0, hmsum, -, -⟩ := hcan
  refine outcome_of_bundles v p hp (fun i => kept (σ i)) sold (fun i => money (σ i))
    (fun i j hij => hdisj _ _ (fun h => hij (σ.injective h))) (fun i => hsold _)
    (fun i => hm0 _) ?_ hacc
  calc ∑ i, money (σ i) = ∑ k, money k := Equiv.sum_comp σ money
    _ ≤ ∑ g ∈ sold, p g := hmsum

omit [Fintype G] in
/-- **Allocating three bundles of a canonical partition to the three agents.**  If each agent `i`
accepts the bundle `ka i` assigned to it, and the assignment is a bijection, the resulting
allocation (executing the proposed sale) is a valid `3/4`-MMS outcome. -/
lemma outcome_of_assignment (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    {w : G → ℝ} {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ}
    {lo : Fin 3} (hcan : IsCanonical w p τ kept sold money lo)
    (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (kx ky kz : Fin 3) (hkxy : kx ≠ ky) (hkxz : kx ≠ kz) (hkyz : ky ≠ kz)
    (hx : (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p (kept kx) + money kx)
    (hy : (3 / 4 : ℝ) * MMS 3 (v y) p ≤ vbarSum (v y) p (kept ky) + money ky)
    (hz : (3 / 4 : ℝ) * MMS 3 (v z) p ≤ vbarSum (v z) p (kept kz) + money kz) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨hdisj, hsold, hm0, hmsum, -, -⟩ := hcan
  set ka : Fin 3 → Fin 3 := fun i => if i = x then kx else if i = y then ky else kz with hka
  have hkax : ka x = kx := by simp [hka]
  have hkay : ka y = ky := by simp [hka, (Ne.symm hxy)]
  have hkaz : ka z = kz := by simp [hka, (Ne.symm hxz), (Ne.symm hyz)]
  have hinj : ∀ i j, i ≠ j → ka i ≠ ka j := by
    intro i j hij
    rcases fin3_cover hxy hxz hyz i with hi | hi | hi <;>
      rcases fin3_cover hxy hxz hyz j with hj | hj | hj <;> subst hi <;> subst hj <;>
      simp_all [Ne.symm hkxy, Ne.symm hkxz, Ne.symm hkyz]
  refine outcome_of_bundles v p hp (fun i => kept (ka i)) sold (fun i => money (ka i))
    (fun i j hij => hdisj _ _ (hinj i j hij)) (fun i => hsold _) (fun i => hm0 _) ?_ ?_
  · have h1 : ∑ i, money (ka i) = money (ka x) + money (ka y) + money (ka z) :=
      fin3_sum hxy hxz hyz (fun i => money (ka i))
    have h2 : ∑ k, money k = money kx + money ky + money kz :=
      fin3_sum hkxy hkxz hkyz money
    rw [h1, hkax, hkay, hkaz, ← h2]
    exact hmsum
  · intro i
    rcases fin3_cover hxy hxz hyz i with hi | hi | hi <;> rw [hi]
    · simpa [hkax] using hx
    · simpa [hkay] using hy
    · simpa [hkaz] using hz

/-! ## The partitioning agent survives any single bundle loss -/

omit [Fintype G] in
/-- The three indices of `Fin 3` other than a given one. -/
lemma fin3_others (k : Fin 3) : ∃ j j' : Fin 3, j ≠ k ∧ j' ≠ k ∧ j ≠ j' := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

/-- **The partitioning agent survives a bundle loss.**  Suppose the partitioning agent's canonical
partition has bundle `k` handed out, funded by selling a subset `Sa ⊆ sold` whose proceeds cover
the bundle's money share, with the unused proceeds banked as cash.  Then the partitioning agent
can still split the remaining goods and cash into two parts worth `τ` each: its two other bundles
survive, the goods of `sold \ Sa` being sellable inside the remainder.

Note that this holds whether the bundle is worth exactly `τ` or more to the partitioning agent. -/
lemma canonical_partitioner_survives (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ} {lo : Fin 3}
    (hcan : IsCanonical w p τ kept sold money lo)
    (k : Fin 3) (Sa : Finset G) (hSa : Sa ⊆ sold) (hfund : money k ≤ ∑ g ∈ Sa, p g) :
    τ ≤ MMS 2 (cashVal (Finset.univ \ (kept k ∪ Sa)) w)
      (cashPrice (Finset.univ \ (kept k ∪ Sa)) p ((∑ g ∈ Sa, p g) - money k)) := by
  classical
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := hcan
  obtain ⟨j, j', hjk, hj'k, hjj'⟩ := fin3_others k
  set R : Finset G := Finset.univ \ (kept k ∪ Sa) with hR
  have hsub : ∀ B : Finset G, Disjoint B (kept k) → Disjoint B Sa → B ⊆ R := by
    intro B h1 h2 x hx
    rw [hR, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_union]
    rintro (h | h)
    · exact (Finset.disjoint_left.mp h1 hx) h
    · exact (Finset.disjoint_left.mp h2 hx) h
  have hjR : kept j ⊆ R :=
    hsub _ (hdisj _ _ hjk) (Finset.disjoint_of_subset_right hSa (hsold j).symm)
  have hj'R : kept j' ⊆ R :=
    hsub _ (hdisj _ _ hj'k) (Finset.disjoint_of_subset_right hSa (hsold j').symm)
  have hTR : sold \ Sa ⊆ R :=
    hsub _ (Finset.disjoint_of_subset_left Finset.sdiff_subset (hsold k))
      (Finset.sdiff_disjoint)
  have hsplit : (∑ g ∈ Sa, p g) + ∑ g ∈ sold \ Sa, p g = ∑ g ∈ sold, p g := by
    rw [add_comm]; exact Finset.sum_sdiff hSa
  have hsum3 : ∑ i, money i = money k + money j + money j' := by
    rcases fin3_others k with -
    have : ∀ f : Fin 3 → ℝ, ∑ i, f i = f k + f j + f j' :=
      fun f => fin3_sum (Ne.symm hjk) (Ne.symm hj'k) hjj' f
    exact this money
  refine MMS2_cash_of_two_bundles_sell w p hw hp R (kept j) (kept j') (sold \ Sa)
    ((∑ g ∈ Sa, p g) - money k) (money j) (money j') τ
    (hdisj _ _ hjj')
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (hsold j).symm)
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (hsold j').symm)
    hjR hj'R hTR (by linarith) (hm0 j) (hm0 j') ?_ (hacc j) (hacc j')
  have := hm0 k
  linarith [hmsum, hsum3, hsplit]

/-- A set contained in `U` is disjoint from the complement of `U`. -/
lemma disjoint_compl_of_subset {Y U : Finset G} (hYU : Y ⊆ U) :
    Disjoint Y (Finset.univ \ U) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  exact (Finset.mem_sdiff.mp hx').2 (hYU hx)

/-! ## Value counting for an agent that rejects bundles -/

/-- `4 · (3/4 · MMS) = 3 · MMS ≤ v̄(all goods)`. -/
lemma four_thr_le_vbarSum_univ (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    4 * ((3 / 4 : ℝ) * MMS 3 w p) ≤ vbarSum w p Finset.univ := by
  have := three_MMS_le_vbarSum_univ w p hw hp
  linarith

/-- **Counting after rejecting every bundle.**  If an agent values each of the three bundles of a
partition (goods plus money share) at most `3/4 · MMS`, then everything outside those bundles is
worth more than `3/4 · MMS` plus the total distributed money to it. -/
lemma reject_all_counting (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (kept : Fin 3 → Finset G) (money : Fin 3 → ℝ)
    (hdisj : ∀ j k, j ≠ k → Disjoint (kept j) (kept k))
    (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h12 : k1 ≠ k2)
    (hrej : ∀ k, vbarSum w p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p + ∑ k, money k ≤
      vbarSum w p (Finset.univ \ (kept k0 ∪ kept k1 ∪ kept k2)) := by
  classical
  have hd01 : Disjoint (kept k0) (kept k1) := hdisj _ _ h01
  have hd02 : Disjoint (kept k0) (kept k2) := hdisj _ _ h02
  have hd12 : Disjoint (kept k1) (kept k2) := hdisj _ _ h12
  have hu : vbarSum w p (kept k0 ∪ kept k1 ∪ kept k2)
      = vbarSum w p (kept k0) + vbarSum w p (kept k1) + vbarSum w p (kept k2) := by
    rw [vbarSum_union w p (Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩), vbarSum_union w p hd01]
  have hsub : kept k0 ∪ kept k1 ∪ kept k2 ⊆ Finset.univ := Finset.subset_univ _
  have hsdiff := vbarSum_sdiff w p hsub
  have htot := four_thr_le_vbarSum_univ w p hw hp
  have hsum : ∑ k, money k = money k0 + money k1 + money k2 := fin3_sum h01 h02 h12 money
  rw [hsdiff, hu]
  have hh0 := hrej k0
  have hh1 := hrej k1
  have hh2 := hrej k2
  rw [hsum]
  linarith

/-- **Counting after rejecting one bundle.**  If an agent values a bundle `K` plus money `m` at
most `3/4 · MMS`, and values the force-sold set at most `2 · (3/4 · MMS)`, then what is left after
removing the bundle and the sold goods is worth at least `3/4 · MMS + m` to it. -/
lemma reject_one_counting (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (K S : Finset G) (m : ℝ)
    (hS : vbarSum w p S ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p))
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p + m ≤ vbarSum w p (Finset.univ \ (K ∪ S)) := by
  classical
  have hsub : K ∪ S ⊆ Finset.univ := Finset.subset_univ _
  have hsdiff := vbarSum_sdiff w p hsub
  have htot := four_thr_le_vbarSum_univ w p hw hp
  have hKS : vbarSum w p (K ∪ S) ≤ vbarSum w p K + vbarSum w p S := by
    have hunion : K ∪ S = K ∪ (S \ K) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    have hdisj : Disjoint K (S \ K) := Finset.disjoint_sdiff
    have hle : vbarSum w p (S \ K) ≤ vbarSum w p S := by
      simp only [vbarSum]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun g _ _ => le_max_of_le_left (hp g))
    rw [hunion, vbarSum_union w p hdisj]
    linarith
  rw [hsdiff]
  linarith

/-! ## The special case: one agent accepts everything, the other nothing -/

/-- Small goods make the force-sold set cheap. -/
lemma vbarSum_sold_le (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (S : Finset G) (hcard : S.card ≤ 2)
    (hsmall : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) :
    vbarSum w p S ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p) := by
  classical
  calc vbarSum w p S ≤ ∑ _g ∈ S, ((3 / 4 : ℝ) * MMS 3 w p) :=
        Finset.sum_le_sum (fun g _ => (hsmall g).le)
    _ = (S.card : ℝ) * ((3 / 4 : ℝ) * MMS 3 w p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p) := by
        have h1 : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        have h2 : (0 : ℝ) ≤ (3 / 4 : ℝ) * MMS 3 w p := by
          have := MMS_nonneg (n := 3) (by norm_num) w p hw hp
          linarith
        exact mul_le_mul_of_nonneg_right h1 h2

/-- **The special case with a pure bundle.**  Suppose the partitioning agent `a` proposed a
canonical partition, agent `b` accepts the pure non-leftovers bundle `kA`, and agent `d` rejects
all three bundles.  Then a complete `3/4`-MMS allocation exists: `b` takes the pure bundle, and
the remaining value is split between `a` and `d` — either `a` takes the two other bundles and `d`
everything else (which then contains the force-sold goods, worth a lot to `d`), or the sale
proceeds alone already satisfy `a`, and `d` takes everything except the pure bundle and the
force-sold goods. -/
lemma special_case_pure_allocation (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonical (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo)
    (hcard : sold.card ≤ 2)
    (kA kB : Fin 3) (hkA : kA ≠ lo) (hkB : kB ≠ lo) (hkAB : kA ≠ kB)
    (hpure : money kA = 0)
    (hbacc : (3 / 4 : ℝ) * MMS 3 (v b) p ≤ vbarSum (v b) p (kept kA) + money kA)
    (hdrej : ∀ k, vbarSum (v d) p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 (v d) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := hcan
  have hdA : Disjoint (kept kA) (kept kB) := hdisj _ _ hkAB
  have hdAlo : Disjoint (kept kA) (kept lo) := hdisj _ _ hkA
  have hdBlo : Disjoint (kept kB) (kept lo) := hdisj _ _ hkB
  have hbval : (3 / 4 : ℝ) * MMS 3 (v b) p ≤ vbarSum (v b) p (kept kA) := by
    rw [hpure] at hbacc; linarith
  by_cases hcase : (3 / 4 : ℝ) * MMS 3 (v a) p ≤
      vbarSum (v a) p (kept kB) + vbarSum (v a) p (kept lo)
  · -- `a` takes the two other bundles, `b` the pure bundle, `d` everything else (which
    -- contains the force-sold goods).
    set X : Fin 3 → Finset G := fun i =>
      if i = a then kept kB ∪ kept lo else if i = b then kept kA
      else Finset.univ \ (kept kA ∪ kept kB ∪ kept lo) with hX
    have hXa : X a = kept kB ∪ kept lo := by simp [hX]
    have hXb : X b = kept kA := by simp [hX, (Ne.symm hab)]
    have hXd : X d = Finset.univ \ (kept kA ∪ kept kB ∪ kept lo) := by
      simp [hX, (Ne.symm had), (Ne.symm hbd)]
    have hsubunion : ∀ i, i ≠ d → X i ⊆ kept kA ∪ kept kB ∪ kept lo := by
      intro i hi
      rcases fin3_cover hab had hbd i with h | h | h
      · subst h; rw [hXa]; intro x hx
        rcases Finset.mem_union.mp hx with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ h'
      · subst h; rw [hXb]; intro x hx
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
      · exact absurd h hi
    refine outcome_of_bundles v p hp X ∅ 0 ?_ (fun i => by simp) (fun i => le_refl 0)
      (by simp) ?_
    · intro i j hij
      have hda : Disjoint (X a) (X b) := by
        rw [hXa, hXb]
        exact Finset.disjoint_union_left.mpr ⟨hdA.symm, hdAlo.symm⟩
      have hdad : Disjoint (X a) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion a had)
      have hdbd : Disjoint (X b) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion b hbd)
      rcases fin3_cover hab had hbd i with hi | hi | hi <;>
        rcases fin3_cover hab had hbd j with hj | hj | hj <;> rw [hi, hj] <;>
        first
          | exact absurd (hi.trans hj.symm) hij
          | exact hda
          | exact hda.symm
          | exact hdad
          | exact hdad.symm
          | exact hdbd
          | exact hdbd.symm
    · intro i
      rcases fin3_cover hab had hbd i with hi | hi | hi <;> rw [hi]
      · rw [hXa, Pi.zero_apply, add_zero, vbarSum_union (v a) p hdBlo]; exact hcase
      · rw [hXb, Pi.zero_apply, add_zero]; exact hbval
      · rw [hXd, Pi.zero_apply, add_zero]
        have := reject_all_counting (v d) p (hv d) hp kept money hdisj kA kB lo hkAB hkA hkB hdrej
        have hmsum0 : (0 : ℝ) ≤ ∑ k, money k := Finset.sum_nonneg (fun k _ => hm0 k)
        linarith
  · -- The sale proceeds alone already satisfy `a`; `d` takes everything except the pure bundle
    -- and the sold goods.
    push_neg at hcase
    have hkBacc := hacc kB
    have hloacc := hacc lo
    have hmoney : (3 / 4 : ℝ) * MMS 3 (v a) p < money kB + money lo := by linarith
    have hmsum3 : money kA + money kB + money lo = ∑ k, money k :=
      (fin3_sum hkAB hkA hkB money).symm
    have hpsold : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ ∑ g ∈ sold, p g := by
      rw [hpure] at hmsum3; linarith [hmsum]
    have hvsold : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p sold := by
      refine le_trans hpsold ?_
      exact Finset.sum_le_sum (fun g _ => le_max_left _ _)
    set X : Fin 3 → Finset G := fun i =>
      if i = a then sold else if i = b then kept kA
      else Finset.univ \ (kept kA ∪ sold) with hX
    have hXa : X a = sold := by simp [hX]
    have hXb : X b = kept kA := by simp [hX, (Ne.symm hab)]
    have hXd : X d = Finset.univ \ (kept kA ∪ sold) := by
      simp [hX, (Ne.symm had), (Ne.symm hbd)]
    have hsubunion : ∀ i, i ≠ d → X i ⊆ kept kA ∪ sold := by
      intro i hi
      rcases fin3_cover hab had hbd i with h | h | h
      · subst h; rw [hXa]; exact Finset.subset_union_right
      · subst h; rw [hXb]; exact Finset.subset_union_left
      · exact absurd h hi
    refine outcome_of_bundles v p hp X ∅ 0 ?_ (fun i => by simp) (fun i => le_refl 0)
      (by simp) ?_
    · intro i j hij
      have hda : Disjoint (X a) (X b) := by rw [hXa, hXb]; exact hsold kA
      have hdad : Disjoint (X a) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion a had)
      have hdbd : Disjoint (X b) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion b hbd)
      rcases fin3_cover hab had hbd i with hi | hi | hi <;>
        rcases fin3_cover hab had hbd j with hj | hj | hj <;> rw [hi, hj] <;>
        first
          | exact absurd (hi.trans hj.symm) hij
          | exact hda
          | exact hda.symm
          | exact hdad
          | exact hdad.symm
          | exact hdbd
          | exact hdbd.symm
    · intro i
      rcases fin3_cover hab had hbd i with hi | hi | hi <;> rw [hi]
      · rw [hXa, Pi.zero_apply, add_zero]; exact hvsold
      · rw [hXb, Pi.zero_apply, add_zero]; exact hbval
      · rw [hXd, Pi.zero_apply, add_zero]
        have hsoldsmall := vbarSum_sold_le (v d) p (hv d) hp sold hcard (hnobig d)
        have := reject_one_counting (v d) p (hv d) hp (kept kA) sold (money kA)
          hsoldsmall (hdrej kA)
        linarith [hm0 kA]

/-! ## Single loss events and Lemma 4 -/

/-- **A single loss event.**  One agent `x` has been served with a bundle consisting of the goods
`K` and the money `m`, financed by selling at most one good (`S`), the unused proceeds being
banked.  Every other agent either already has its `3/4`-MMS guarantee on the cash-augmented
remainder, or values the allocated bundle at most `3/4 · MMS` (so the loss it suffers is a loss
event of the manuscript's types `ℓ₁`–`ℓ₄`). -/
def SingleLossConfig (v : Fin 3 → G → ℝ) (p : G → ℝ) : Prop :=
  ∃ (x : Fin 3) (K S : Finset G) (m : ℝ),
    Disjoint K S ∧ 0 ≤ m ∧ m ≤ ∑ g ∈ S, p g ∧ S.card ≤ 1 ∧ (K.card ≤ 1 ∨ S = ∅) ∧
    (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p K + m ∧
    ∀ i, i ≠ x →
      ((3 / 4 : ℝ) * MMS 3 (v i) p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) (v i))
          (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)))
      ∨ (vbarSum (v i) p K + m ≤ (3 / 4 : ℝ) * MMS 3 (v i) p ∧
          ∀ f ∈ S, (1 / 4 : ℝ) * MMS 3 (v i) p ≤ p f)

/-- **Lemma 4 of the manuscript, in cash-aware form, as an interface.**  If a pure or singleton
bundle funded by at most one sold good is handed out and an agent values it at most `3/4 · MMS`,
then that agent can still split the remaining goods and the banked proceeds into two parts worth
`3/4 · MMS` each. -/
def LemmaFourCash (G : Type*) [Fintype G] [DecidableEq G] : Prop :=
  ∀ (w p : G → ℝ), (∀ g, 0 ≤ w g) → (∀ g, 0 ≤ p g) →
    (∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) →
    ∀ (K S : Finset G) (m : ℝ), Disjoint K S → 0 ≤ m → m ≤ ∑ g ∈ S, p g →
      S.card ≤ 1 → (K.card ≤ 1 ∨ S = ∅) → (∀ f ∈ S, (1 / 4 : ℝ) * MMS 3 w p ≤ p f) →
      vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p →
      (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
        (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m))

/-- **The easy branch of Lemma 4.**  If the agent does not value the force-sold goods above
their market price, then no value at all is destroyed by the sale, and the cash-augmented
remainder still has total value at least `3 · (3/4 · MMS)`; bag filling then splits it into two
acceptable parts.  This covers in particular the case of a *pure* bundle (nothing is sold). -/
lemma lemmaFour_of_no_undervaluation (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p)
    (K S : Finset G) (m : ℝ) (hKS : Disjoint K S) (hmS : m ≤ ∑ g ∈ S, p g)
    (hS : vbarSum w p S ≤ ∑ g ∈ S, p g)
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
      (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)) := by
  classical
  have hτ : 0 ≤ (3 / 4 : ℝ) * MMS 3 w p := by
    have := MMS_nonneg (n := 3) (by norm_num) w p hw hp
    linarith
  refine MMS2_cash_of_total w p hw hp (Finset.univ \ (K ∪ S)) ((∑ g ∈ S, p g) - m)
    ((3 / 4 : ℝ) * MMS 3 w p) (by linarith) hτ (fun g _ => (hnobig g).le) ?_
  have hsdiff := vbarSum_sdiff w p (Finset.subset_univ (K ∪ S))
  have hunion := vbarSum_union w p hKS
  have htot := four_thr_le_vbarSum_univ w p hw hp
  rw [hsdiff, hunion]
  linarith

/-- **The residual case of Lemma 4**, stated as an interface: a *singleton* bundle, consisting of
at most one kept good plus money produced by selling one good `f`.  (This is the case that the
value-counting argument `lemmaFour_of_no_undervaluation` does not reach; it is proved in
`RequestProject.LemmaFourResidual`.) -/
def LemmaFourCashSold (G : Type*) [Fintype G] [DecidableEq G] : Prop :=
  ∀ (w p : G → ℝ), (∀ g, 0 ≤ w g) → (∀ g, 0 ≤ p g) →
    (∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) →
    ∀ (K : Finset G) (f : G) (m : ℝ), f ∉ K → 0 ≤ m → m ≤ p f → K.card ≤ 1 →
      (1 / 4 : ℝ) * MMS 3 w p ≤ p f →
      vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p →
      (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ {f})) w)
        (cashPrice (Finset.univ \ (K ∪ {f})) p (p f - m))

/-- **Lemma 4 reduces to its residual (singleton) case.**  A pure bundle is handled by the
value-counting argument. -/
theorem lemmaFourCash_of_sold (h : LemmaFourCashSold G) : LemmaFourCash G := by
  classical
  intro w p hw hp hnobig K S m hKS hm0 hmS hScard hKcard hprice hrej
  rcases S.eq_empty_or_nonempty with rfl | ⟨f, hfS⟩
  · exact lemmaFour_of_no_undervaluation w p hw hp hnobig K ∅ m hKS hmS (by simp [vbarSum]) hrej
  · have hSeq : S = {f} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hfS, fun x hx => Finset.card_le_one.mp hScard x hx f hfS⟩
    subst hSeq
    have hKone : K.card ≤ 1 := by
      rcases hKcard with hc | hc
      · exact hc
      · exact absurd hc (Finset.singleton_ne_empty f)
    have hfK : f ∉ K :=
      fun hmem => (Finset.disjoint_left.mp hKS hmem) (Finset.mem_singleton_self f)
    have hmf : m ≤ p f := by simpa using hmS
    simpa using h w p hw hp hnobig K f m hfK hm0 hmf hKone
      (hprice f (Finset.mem_singleton_self f)) hrej

/-- A single loss event, together with Lemma 4, yields a complete `3/4`-MMS allocation. -/
theorem outcome_of_singleLossConfig (hL4 : LemmaFourCash G) (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (h : SingleLossConfig v p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨x, K, S, m, hKS, hm0, hmS, hScard, hKcard, hserved, hrest⟩ := h
  obtain ⟨y, z, hyx, hzx, hyz⟩ := fin3_others x
  have key : ∀ i, i ≠ x → (3 / 4 : ℝ) * MMS 3 (v i) p ≤
      MMS 2 (cashVal (Finset.univ \ (K ∪ S)) (v i))
        (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)) := by
    intro i hi
    rcases hrest i hi with h1 | ⟨h2, h3⟩
    · exact h1
    · exact hL4 (v i) p (hv i) hp (hnobig i) K S m hKS hm0 hmS hScard hKcard h3 h2
  exact finish_from_cash_reduction v p hv hp x y z (Ne.symm hyx) (Ne.symm hzx) hyz
    K S m ((∑ g ∈ S, p g) - m) hKS hm0 (by linarith) (by linarith) hserved
    (key y hyx) (key z hzx)

/-- **Handing out one non-leftovers bundle produces a single loss event.**  Agent `x` accepts the
non-leftovers bundle `k` of the partitioning agent's canonical partition; the bundle is funded by
selling at most one good.  Every other agent is either the partitioning agent (which survives the
loss by `canonical_partitioner_survives`) or values the bundle at most `3/4 · MMS`. -/
lemma singleLoss_of_canonical_bundle (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a : Fin 3) (hva : ∀ g, 0 ≤ v a g) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ} {lo : Fin 3}
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo)
    (k : Fin 3) (hk : k ≠ lo) (x : Fin 3)
    (hxacc : (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p (kept k) + money k)
    (hrest : ∀ i, i ≠ x → i = a ∨
      vbarSum (v i) p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 (v i) p) :
    SingleLossConfig v p := by
  classical
  have hcanon := hcan.1
  have hstrict := hcan.2.2
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := id hcanon
  rcases hstrict k hk with hzero | ⟨hcard1, f, hf, hfp⟩
  · -- a pure bundle: nothing has to be sold
    refine ⟨x, kept k, ∅, 0, Finset.disjoint_empty_right _, le_refl 0, by simp, by simp,
      Or.inr rfl, by rw [hzero] at hxacc; simpa using hxacc, fun i hi => ?_⟩
    rcases hrest i hi with rfl | hrej
    · refine Or.inl ?_
      have := canonical_partitioner_survives (v i) p hva hp hcanon k ∅
        (Finset.empty_subset _) (by simp [hzero])
      simpa [hzero] using this
    · exact Or.inr ⟨by rw [hzero] at hrej; exact hrej, by simp⟩
  · -- a singleton bundle funded by the single sold good `f`
    obtain ⟨hfp, hfprice⟩ := hfp
    have hfnot : f ∉ kept k := fun hmem => (Finset.disjoint_left.mp (hsold k) hf) hmem
    have hsum : ∑ g ∈ ({f} : Finset G), p g = p f := Finset.sum_singleton _ _
    refine ⟨x, kept k, {f}, money k, Finset.disjoint_singleton_right.mpr hfnot, hm0 k,
      by rw [hsum]; exact hfp, by simp, Or.inl (le_of_eq hcard1), hxacc, fun i hi => ?_⟩
    rcases hrest i hi with rfl | hrej
    · exact Or.inl (canonical_partitioner_survives (v i) p hva hp hcanon k {f}
        (Finset.singleton_subset_iff.mpr hf) (by rw [hsum]; exact hfp))
    · refine Or.inr ⟨hrej, fun g hg => ?_⟩
      rw [Finset.mem_singleton.mp hg]
      have := hmax i
      linarith

/-! ## The matching phase -/

/-- **The matching phase for three agents.**  Given the canonical partition proposed by the
partitioning agent `a` (in the manuscript's strict form) and no big goods, either the instance is
already completely solved, or we are in a single loss event. -/
theorem matching_phase_three (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo) :
    (∃ o : Outcome G 3, o.Valid p ∧
        ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i)
      ∨ SingleLossConfig v p := by
  classical
  have hcanon := hcan.1
  have hcard := hcan.2.1
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := id hcanon
  obtain ⟨k1, k2, hk1, hk2, hk12⟩ := fin3_others lo
  obtain ⟨b, d, hba, hda, hbd⟩ := fin3_others a
  -- the two non-leftovers bundles and the two non-partitioning agents, indexed by `Fin 2`
  set bd : Fin 2 → Fin 3 := ![b, d] with hbdf
  set kk : Fin 2 → Fin 3 := ![k1, k2] with hkkf
  have hbd0 : bd 0 = b := rfl
  have hbd1 : bd 1 = d := rfl
  have hkk0 : kk 0 = k1 := rfl
  have hkk1 : kk 1 = k2 := rfl
  have hbdinj : ∀ i j : Fin 2, i ≠ j → bd i ≠ bd j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hbd]
  have hkkinj : ∀ i j : Fin 2, i ≠ j → kk i ≠ kk j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hk12]
  have hkklo : ∀ i : Fin 2, kk i ≠ lo := by
    intro i; fin_cases i <;> simpa [hkkf] using ‹_›
  have hbda : ∀ i : Fin 2, bd i ≠ a := by
    intro i; fin_cases i <;> simpa [hbdf] using ‹_›
  set acc : Fin 2 → Fin 2 → Bool := fun j k =>
    decide ((3 / 4 : ℝ) * MMS 3 (v (bd j)) p ≤
      vbarSum (v (bd j)) p (kept (kk k)) + money (kk k)) with haccdef
  have hacc_true : ∀ j k, acc j k = true → (3 / 4 : ℝ) * MMS 3 (v (bd j)) p ≤
      vbarSum (v (bd j)) p (kept (kk k)) + money (kk k) := by
    intro j k h; simpa [haccdef] using of_decide_eq_true h
  have hacc_false : ∀ j k, acc j k = false →
      vbarSum (v (bd j)) p (kept (kk k)) + money (kk k) ≤
        (3 / 4 : ℝ) * MMS 3 (v (bd j)) p := by
    intro j k h
    simp only [haccdef, decide_eq_false_iff_not, not_le] at h
    exact h.le
  rcases matching_phase_two acc with ⟨σ, hσ⟩ | ⟨k, hk⟩ | ⟨j, j', hjj', hall, hnone⟩
  · -- Perfect matching: the partitioning agent takes the leftovers bundle.
    refine Or.inl ?_
    have hne : σ 0 ≠ σ 1 := fun h => by simpa using σ.injective h
    refine outcome_of_assignment v p hp hcanon a b d hba.symm hda.symm hbd
      lo (kk (σ 0)) (kk (σ 1)) (Ne.symm (hkklo _)) (Ne.symm (hkklo _)) (hkkinj _ _ hne)
      (hacc lo) ?_ ?_
    · simpa [hbd0] using hacc_true 0 (σ 0) (hσ 0)
    · simpa [hbd1] using hacc_true 1 (σ 1) (hσ 1)
  · -- A non-leftovers bundle rejected by both non-partitioning agents: hand it to the
    -- partitioning agent.
    refine Or.inr (singleLoss_of_canonical_bundle v p hp a (hv a) hmax hcan (kk k) (hkklo k) a
      (hacc (kk k)) (fun i hi => Or.inr ?_))
    rcases fin3_cover hba.symm hda.symm hbd i with h | h | h
    · exact absurd h hi
    · rw [h]; simpa [hbd0] using hacc_false 0 k (hk 0)
    · rw [h]; simpa [hbd1] using hacc_false 1 k (hk 1)
  · -- The special case: agent `bd j` accepts both bundles, agent `bd j'` accepts neither.
    set B : Fin 3 := bd j with hB
    set D : Fin 3 := bd j' with hD
    have hBD : B ≠ D := hbdinj j j' hjj'
    have hBa : B ≠ a := hbda j
    have hDa : D ≠ a := hbda j'
    have hBacc : ∀ i : Fin 2, (3 / 4 : ℝ) * MMS 3 (v B) p ≤
        vbarSum (v B) p (kept (kk i)) + money (kk i) := fun i => hacc_true j i (hall i)
    have hDrej : ∀ i : Fin 2, vbarSum (v D) p (kept (kk i)) + money (kk i) ≤
        (3 / 4 : ℝ) * MMS 3 (v D) p := fun i => hacc_false j' i (hnone i)
    by_cases hDlo : (3 / 4 : ℝ) * MMS 3 (v D) p ≤ vbarSum (v D) p (kept lo) + money lo
    · -- `D` accepts the leftovers bundle: everybody is matched after all.
      refine Or.inl (outcome_of_assignment v p hp hcanon a B D (Ne.symm hBa) (Ne.symm hDa) hBD
        (kk 0) (kk 1) lo (hkkinj 0 1 (by decide)) (hkklo 0) (hkklo 1)
        (hacc (kk 0)) (hBacc 1) hDlo)
    · -- `D` rejects every bundle.
      push_neg at hDlo
      have hDall : ∀ k : Fin 3, vbarSum (v D) p (kept k) + money k ≤
          (3 / 4 : ℝ) * MMS 3 (v D) p := by
        intro k
        rcases fin3_cover hk12 hk1 hk2 k with h | h | h
        · rw [h]; simpa [hkk0] using hDrej 0
        · rw [h]; simpa [hkk1] using hDrej 1
        · rw [h]; exact hDlo.le
      by_cases hpure : money k1 = 0 ∨ money k2 = 0
      · -- One of the two bundles is pure: a complete allocation exists outright.
        refine Or.inl ?_
        rcases hpure with h0 | h0
        · exact special_case_pure_allocation v p hv hp a B D (Ne.symm hBa) (Ne.symm hDa) hBD
            hnobig kept sold money lo hcanon hcard k1 k2 hk1 hk2 hk12 h0
            (by simpa [hkk0] using hBacc 0) hDall
        · exact special_case_pure_allocation v p hv hp a B D (Ne.symm hBa) (Ne.symm hDa) hBD
            hnobig kept sold money lo hcanon hcard k2 k1 hk2 hk1 (Ne.symm hk12) h0
            (by simpa [hkk1] using hBacc 1) hDall
      · -- Both bundles are singleton bundles: hand one of them to `B`, a single loss event.
        refine Or.inr (singleLoss_of_canonical_bundle v p hp a (hv a) hmax hcan k1 hk1 B
          (by simpa [hkk0] using hBacc 0) (fun i hi => ?_))
        rcases fin3_cover hBa hBD (Ne.symm hDa) i with h | h | h
        · exact absurd h hi
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact hDall k1)

/-- **The `n = 3`, `3/4`-MMS theorem, from a strictly canonical partition and Lemma 4.**  Only
the residual case of Lemma 4 (`LemmaFourCashSold`, the sale of a single good the agent values
above its market price) is assumed; every other case is proved. -/
theorem exists_threequarter_MMS_three_of_canonical (hL4 : LemmaFourCashSold G)
    (v : Fin 3 → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  rcases matching_phase_three v p hv hp hnobig a hmax kept sold money lo hcan with h | h
  · exact h
  · exact outcome_of_singleLossConfig (lemmaFourCash_of_sold hL4) v p hv hp hnobig h

end FairSelling
