import Mathlib
import RequestProject.EpsEnvy

/-!
# Appendix C, Lemma 11: passing to the limit `ε → 0`

The manuscript's Lemma 11 reads:

> For a given allocation instance with sellable goods and a given value of `ρ` and individual
> share values `sᵢ`, suppose that for every `ε > 0` there is an allocation (partial allocation,
> respectively) that is `(ρ − ε)·sᵢ` and `ε-SEFX`.  Then there also is an allocation (partial
> allocation, respectively) that is `ρ·sᵢ` and `SEFX`.

Its proof is a compactness argument: there are finitely many *classes* of (partial) allocations,
one for each decision (which agent gets it / sold / unallocated) for each good, and within a class
the possible money vectors form a compact set.

The compactness argument is carried out below, in the form of `exists_limit_of_valid_seq`: from a
sequence of valid outcomes one can extract a subsequence with constant class whose money vectors
converge.

With the notions `SEFX` and `ε-SEFX` as corrected in `RequestProject.Selling` and
`RequestProject.EpsEnvy` — the envying agent's own money `Pᵢ` counted on the left-hand side of the
up-to-any-good condition, and that condition offered as an alternative to the envy-free condition
— the limiting argument goes through and Lemma 11 holds verbatim: this is `lemma11`.

The correction is what makes the argument work.  Under the *literal* reading of Definition 4/8
(`SEFXlit`, `epsSEFXlit`) the statement is **false**; see
`RequestProject.LemmaElevenCounterexample`.  The reason is that the literal `SEFX` condition is
*not a closed condition* on the money vector: an agent `j` holding an arbitrarily small positive
amount of money `P_j` only has to satisfy the (plain) envy-freeness condition, whereas at
`P_j = 0` it must satisfy the strictly stronger up-to-any-good condition
`v̄ᵢ(Aᵢ) ≥ v̄ᵢ(A_j \ g) + p(g)` in which the envying agent's own money `Pᵢ` is *not* counted.
Once `Pᵢ` is counted on the left, the condition *is* closed, and the supremum is attained.

Three statements are proved here, all by the same limiting argument:

* `lemma11` — Lemma 11 exactly as stated, for the corrected notions of Definition 4.2/8.2.
* `lemma11_utility` — the same with the conclusion phrased as `SEFXu`, the *utility form* of
  `SEFX` (the standard notion `EFXM` for mixed divisible/indivisible goods).  For valid outcomes
  `SEFXu` and the corrected `SEFX` are equivalent (`SEFX_iff_SEFXu`), so this is the same result.
* `lemma11_strict` — the conclusion is the stronger `SEFXs` (in which the envied agent's money is
  charged even when positive), at the price of strengthening the hypothesis to `ε-SEFXs`.
-/

open scoped BigOperators
open Filter Topology

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The compactness step -/

omit [Fintype G] [DecidableEq G] in
/-- In a valid outcome, each agent's money is at most the total sale proceeds. -/
theorem money_le_proceeds {p : G → ℝ} {o : Outcome G n} (h : o.Valid p) (j : Fin n) :
    o.money j ≤ ∑ g ∈ o.sold, p g := by
  have h1 : o.money j ≤ ∑ k, o.money k :=
    Finset.single_le_sum (f := o.money) (fun k _ => h.2.2.1 k) (Finset.mem_univ j)
  linarith [h.2.2.2]

omit [DecidableEq G] in
/-- Any sequence of outcomes has a subsequence along which the *class* (the set of sold goods and
the assignment of the kept goods) is constant. -/
theorem exists_class_subseq (o : ℕ → Outcome G n) :
    ∃ (S : Finset G) (A : Fin n → Finset G) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ k, (o (φ k)).sold = S) ∧ (∀ k, (o (φ k)).kept = A) := by
  classical
  have hfreq : ∃ c : Finset G × (Fin n → Finset G),
      ∃ᶠ k in atTop, ((o k).sold, (o k).kept) = c := by
    by_contra h
    push_neg at h
    have h' : ∀ c : Finset G × (Fin n → Finset G),
        ∀ᶠ k in atTop, ((o k).sold, (o k).kept) ≠ c := by
      intro c
      simpa [Filter.not_frequently] using h c
    have h'' : ∀ᶠ k in atTop, ∀ c : Finset G × (Fin n → Finset G),
        ((o k).sold, (o k).kept) ≠ c := Filter.eventually_all.2 h'
    obtain ⟨k, hk⟩ := h''.exists
    exact hk _ rfl
  obtain ⟨c, hc⟩ := hfreq
  obtain ⟨φ, hφ, hφc⟩ := Filter.extraction_of_frequently_atTop hc
  refine ⟨c.1, c.2, φ, hφ, fun k => ?_, fun k => ?_⟩
  · exact congrArg Prod.fst (hφc k)
  · exact congrArg Prod.snd (hφc k)

omit [DecidableEq G] in
/-- **The compactness step of Lemma 11.**  From any sequence of valid outcomes one can extract a
subsequence whose class is constant and whose money vectors converge. -/
theorem exists_limit_of_valid_seq {p : G → ℝ} (o : ℕ → Outcome G n)
    (hval : ∀ k, (o k).Valid p) :
    ∃ (S : Finset G) (A : Fin n → Finset G) (P : Fin n → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ k, (o (φ k)).sold = S) ∧ (∀ k, (o (φ k)).kept = A) ∧
      Tendsto (fun k => (o (φ k)).money) atTop (𝓝 P) := by
  classical
  obtain ⟨S, A, φ₁, hφ₁, hS, hA⟩ := exists_class_subseq o
  set C : ℝ := max (∑ g ∈ S, p g) 0 with hC
  have hCnonneg : 0 ≤ C := le_max_right _ _
  have hmem : ∀ k, (o (φ₁ k)).money ∈ Metric.closedBall (0 : Fin n → ℝ) C := by
    intro k
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hCnonneg).2 fun j => ?_
    have h0 : 0 ≤ (o (φ₁ k)).money j := (hval (φ₁ k)).2.2.1 j
    have h1 : (o (φ₁ k)).money j ≤ ∑ g ∈ S, p g := by
      have := money_le_proceeds (hval (φ₁ k)) j
      rwa [hS k] at this
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact le_trans h1 (le_max_left _ _)
  obtain ⟨P, -, φ₂, hφ₂, htend⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  refine ⟨S, A, P, φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun k => hS _, fun k => hA _, htend⟩

/-! ### Lemma 11, utility form -/

/-- **Lemma 11 (corrected: utility form).**  If for every `ε > 0` there is a valid outcome that
guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFX` in the sense of Definition 8,
then there is a valid outcome that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFXu`
(the utility form of `SEFX`, i.e. `EFXM`; for valid outcomes this is equivalent to the corrected
`SEFX`, see `SEFX_iff_SEFXu`).

For the literal reading of Definition 4.2/8.2 the statement is false; see
`RequestProject.LemmaElevenCounterexample`. -/
theorem lemma11_utility (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXu v p o := by
  classical
  -- the `ε = 1/(k+1)` witnesses
  choose ω hval hshare henvy using fun k : ℕ => H (1 / (k + 1)) (by positivity)
  have hepspos : ∀ k : ℕ, (0:ℝ) ≤ 1 / (k + 1) := fun k => by positivity
  -- pass to the utility form of the envy condition
  have henvyu : ∀ k : ℕ, epsSEFXu v p (1 / (k + 1)) (ω k) := fun k =>
    epsSEFXu_of_epsSEFX (hepspos k) (hval k) (henvy k)
  obtain ⟨S, A, P, φ, hφ, hS, hA, htend⟩ := exists_limit_of_valid_seq (p := p) ω hval
  set q : ℕ → Fin n → ℝ := fun k => (ω (φ k)).money with hq
  have hqj : ∀ j, Tendsto (fun k => q k j) atTop (𝓝 (P j)) := fun j =>
    (tendsto_pi_nhds.1 htend) j
  set e : ℕ → ℝ := fun k => 1 / ((φ k : ℝ) + 1) with he
  have hetend : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  refine ⟨⟨S, A, P⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- sold goods are not kept
    intro j
    have := (hval (φ 0)).1 j
    rwa [hS 0, hA 0] at this
  · -- kept bundles are pairwise disjoint
    intro j k hjk
    have := (hval (φ 0)).2.1 j k hjk
    rwa [hA 0] at this
  · -- money is non-negative
    intro j
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hqj j)
      (fun k => (hval (φ k)).2.2.1 j)
  · -- the distributed money does not exceed the proceeds
    have hsum : Tendsto (fun k => ∑ j, q k j) atTop (𝓝 (∑ j, P j)) :=
      tendsto_finset_sum _ fun j _ => hqj j
    refine le_of_tendsto_of_tendsto' hsum tendsto_const_nhds fun k => ?_
    have := (hval (φ k)).2.2.2
    rwa [hS k] at this
  · -- the share guarantee, in the limit
    intro i
    have hlhs : Tendsto (fun k => (rho - e k) * s i) atTop (𝓝 (rho * s i)) := by
      have : Tendsto (fun k => rho - e k) atTop (𝓝 rho) := by
        simpa using tendsto_const_nhds.sub hetend
      simpa using this.mul_const (s i)
    have hrhs : Tendsto (fun k => (∑ g ∈ A i, v i g) + q k i) atTop
        (𝓝 ((∑ g ∈ A i, v i g) + P i)) := tendsto_const_nhds.add (hqj i)
    refine le_of_tendsto_of_tendsto' hlhs hrhs fun k => ?_
    have := hshare (φ k) i
    rw [util, hA k] at this
    exact this
  · -- the envy condition, in the limit
    intro i j
    constructor
    · -- the envied agent holds money: plain envy-freeness
      intro hPj
      have hev : ∀ᶠ k in atTop, 0 < q k j := (hqj j).eventually_const_lt hPj
      have key : ∀ᶠ k in atTop,
          vbarSum (v i) p (A j) + q k j ≤ vbarSum (v i) p (A i) + q k i + e k := by
        filter_upwards [hev] with k hk
        have := (henvyu (φ k) i j).1 (by simpa [hq, hA k] using hk)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j) + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j) + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto hL hR key
      simpa using this
    · -- the up-to-any-good condition, in the limit
      intro g hg
      have key : ∀ k,
          vbarSum (v i) p (A j \ {g}) + p g + q k j
            ≤ vbarSum (v i) p (A i) + q k i + e k := by
        intro k
        have := (henvyu (φ k) i j).2 g (by simpa [hA k] using hg)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j \ {g}) + p g + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j \ {g}) + p g + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto' hL hR key
      simpa using this

/-! ### Lemma 11 with the utility form of the envy condition as input

The algorithm of Appendix D.2 naturally maintains the *utility* form `ε-SEFXu` of the envy
condition, in which the tolerance `ε` is present also in the clause for a bundle that carries
money (see `ISSUES_TPS_SEFX.md`).  The limiting argument above works verbatim for that input. -/

/-- **Lemma 11 (utility form), with `ε-SEFXu` as input.**  If for every `ε > 0` there is a valid
outcome that guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFXu`, then there is a
valid outcome that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFXu`. -/
theorem lemma11_utility_u (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFXu v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXu v p o := by
  classical
  -- the `ε = 1/(k+1)` witnesses
  choose ω hval hshare henvyu using fun k : ℕ => H (1 / (k + 1)) (by positivity)
  obtain ⟨S, A, P, φ, hφ, hS, hA, htend⟩ := exists_limit_of_valid_seq (p := p) ω hval
  set q : ℕ → Fin n → ℝ := fun k => (ω (φ k)).money with hq
  have hqj : ∀ j, Tendsto (fun k => q k j) atTop (𝓝 (P j)) := fun j =>
    (tendsto_pi_nhds.1 htend) j
  set e : ℕ → ℝ := fun k => 1 / ((φ k : ℝ) + 1) with he
  have hetend : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  refine ⟨⟨S, A, P⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- sold goods are not kept
    intro j
    have := (hval (φ 0)).1 j
    rwa [hS 0, hA 0] at this
  · -- kept bundles are pairwise disjoint
    intro j k hjk
    have := (hval (φ 0)).2.1 j k hjk
    rwa [hA 0] at this
  · -- money is non-negative
    intro j
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hqj j)
      (fun k => (hval (φ k)).2.2.1 j)
  · -- the distributed money does not exceed the proceeds
    have hsum : Tendsto (fun k => ∑ j, q k j) atTop (𝓝 (∑ j, P j)) :=
      tendsto_finset_sum _ fun j _ => hqj j
    refine le_of_tendsto_of_tendsto' hsum tendsto_const_nhds fun k => ?_
    have := (hval (φ k)).2.2.2
    rwa [hS k] at this
  · -- the share guarantee, in the limit
    intro i
    have hlhs : Tendsto (fun k => (rho - e k) * s i) atTop (𝓝 (rho * s i)) := by
      have : Tendsto (fun k => rho - e k) atTop (𝓝 rho) := by
        simpa using tendsto_const_nhds.sub hetend
      simpa using this.mul_const (s i)
    have hrhs : Tendsto (fun k => (∑ g ∈ A i, v i g) + q k i) atTop
        (𝓝 ((∑ g ∈ A i, v i g) + P i)) := tendsto_const_nhds.add (hqj i)
    refine le_of_tendsto_of_tendsto' hlhs hrhs fun k => ?_
    have := hshare (φ k) i
    rw [util, hA k] at this
    exact this
  · -- the envy condition, in the limit
    intro i j
    constructor
    · -- the envied agent holds money: plain envy-freeness
      intro hPj
      have hev : ∀ᶠ k in atTop, 0 < q k j := (hqj j).eventually_const_lt hPj
      have key : ∀ᶠ k in atTop,
          vbarSum (v i) p (A j) + q k j ≤ vbarSum (v i) p (A i) + q k i + e k := by
        filter_upwards [hev] with k hk
        have := (henvyu (φ k) i j).1 (by simpa [hq, hA k] using hk)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j) + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j) + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto hL hR key
      simpa using this
    · -- the up-to-any-good condition, in the limit
      intro g hg
      have key : ∀ k,
          vbarSum (v i) p (A j \ {g}) + p g + q k j
            ≤ vbarSum (v i) p (A i) + q k i + e k := by
        intro k
        have := (henvyu (φ k) i j).2 g (by simpa [hA k] using hg)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j \ {g}) + p g + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j \ {g}) + p g + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto' hL hR key
      simpa using this


/-- **Lemma 11, with `ε-SEFXu` as input.**  If for every `ε > 0` there is a valid outcome that
guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFXu`, then there is a valid outcome
that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFX`. -/
theorem lemma11_u (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFXu v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFX v p o := by
  obtain ⟨o, hvalid, hshare, hsefx⟩ := lemma11_utility_u v p rho s H
  exact ⟨o, hvalid, hshare, SEFX_of_SEFXu hsefx⟩

/-- **Lemma 11.**  For a given instance, a given `ρ` and given share values `sᵢ`: if for every
`ε > 0` there is a valid outcome that guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is
`ε-SEFX` (Definition 8.2), then there is a valid outcome that guarantees every agent `i` at least
`ρ·sᵢ` and is `SEFX` (Definition 4.2).

Here `SEFX` and `ε-SEFX` are the corrected notions: the envying agent's own money is counted on
the left-hand side of the up-to-any-good condition, and the (relaxed) envy-free condition is
accepted as an alternative to it. -/
theorem lemma11 (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFX v p o := by
  obtain ⟨o, hvalid, hshare, hsefx⟩ := lemma11_utility v p rho s H
  exact ⟨o, hvalid, hshare, SEFX_of_SEFXu hsefx⟩

/-! ### Lemma 11, strict form -/

/-- **Lemma 11 (corrected: strict form).**  If for every `ε > 0` there is a valid outcome that
guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFXs`, then there is a valid outcome
that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFXs`, hence in particular `SEFX` in the
sense of Definition 4.2 of the manuscript. -/
theorem lemma11_strict (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFXs v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXs v p o := by
  classical
  choose ω hval hshare henvy using fun k : ℕ => H (1 / (k + 1)) (by positivity)
  obtain ⟨S, A, P, φ, hφ, hS, hA, htend⟩ := exists_limit_of_valid_seq (p := p) ω hval
  set q : ℕ → Fin n → ℝ := fun k => (ω (φ k)).money with hq
  have hqj : ∀ j, Tendsto (fun k => q k j) atTop (𝓝 (P j)) := fun j =>
    (tendsto_pi_nhds.1 htend) j
  set e : ℕ → ℝ := fun k => 1 / ((φ k : ℝ) + 1) with he
  have hetend : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  refine ⟨⟨S, A, P⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    have := (hval (φ 0)).1 j
    rwa [hS 0, hA 0] at this
  · intro j k hjk
    have := (hval (φ 0)).2.1 j k hjk
    rwa [hA 0] at this
  · intro j
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hqj j)
      (fun k => (hval (φ k)).2.2.1 j)
  · have hsum : Tendsto (fun k => ∑ j, q k j) atTop (𝓝 (∑ j, P j)) :=
      tendsto_finset_sum _ fun j _ => hqj j
    refine le_of_tendsto_of_tendsto' hsum tendsto_const_nhds fun k => ?_
    have := (hval (φ k)).2.2.2
    rwa [hS k] at this
  · intro i
    have hlhs : Tendsto (fun k => (rho - e k) * s i) atTop (𝓝 (rho * s i)) := by
      have : Tendsto (fun k => rho - e k) atTop (𝓝 rho) := by
        simpa using tendsto_const_nhds.sub hetend
      simpa using this.mul_const (s i)
    have hrhs : Tendsto (fun k => (∑ g ∈ A i, v i g) + q k i) atTop
        (𝓝 ((∑ g ∈ A i, v i g) + P i)) := tendsto_const_nhds.add (hqj i)
    refine le_of_tendsto_of_tendsto' hlhs hrhs fun k => ?_
    have := hshare (φ k) i
    rw [util, hA k] at this
    exact this
  · intro i j
    constructor
    · intro hPj
      have hev : ∀ᶠ k in atTop, 0 < q k j := (hqj j).eventually_const_lt hPj
      have key : ∀ᶠ k in atTop,
          vbarSum (v i) p (A j) + q k j ≤ vbarSum (v i) p (A i) + q k i + e k := by
        filter_upwards [hev] with k hk
        have := (henvy (φ k) i j).1 (by simpa [hq, hA k] using hk)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j) + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j) + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + q k i + e k) atTop
          (𝓝 (vbarSum (v i) p (A i) + P i)) := by
        simpa using (tendsto_const_nhds.add (hqj i)).add hetend
      have := le_of_tendsto_of_tendsto hL hR key
      simpa using this
    · intro g hg
      have key : ∀ k,
          vbarSum (v i) p (A j \ {g}) + p g + q k j ≤ vbarSum (v i) p (A i) + e k := by
        intro k
        have := (henvy (φ k) i j).2 g (by simpa [hA k] using hg)
        rw [hA k] at this
        simpa [he] using this
      have hL : Tendsto (fun k => vbarSum (v i) p (A j \ {g}) + p g + q k j) atTop
          (𝓝 (vbarSum (v i) p (A j \ {g}) + p g + P j)) := tendsto_const_nhds.add (hqj j)
      have hR : Tendsto (fun k => vbarSum (v i) p (A i) + e k) atTop
          (𝓝 (vbarSum (v i) p (A i))) := by
        simpa using tendsto_const_nhds.add hetend
      have := le_of_tendsto_of_tendsto' hL hR key
      simpa using this

/-! ### The form in which Lemma 11 is used for the `TPS` approximation -/

/-- **Lemma 11 for the truncated proportional share** (utility form).  If for every `ε > 0` some
valid outcome is `(ρ − ε)`-`TPS` and `ε-SEFX`, then some valid outcome is `ρ`-`TPS` and `SEFXu`. -/
theorem lemma11_TPS_utility (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFXu v p o :=
  lemma11_utility v p rho (fun i => TPS n (v i) p) H

/-- **Lemma 11 for the truncated proportional share.**  If for every `ε > 0` some valid outcome
is `(ρ − ε)`-`TPS` and `ε-SEFX`, then some valid outcome is `ρ`-`TPS` and `SEFX`. -/
theorem lemma11_TPS (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o :=
  lemma11 v p rho (fun i => TPS n (v i) p) H

/-- **Lemma 11 for the truncated proportional share** (strict form).  If for every `ε > 0` some
valid outcome is `(ρ − ε)`-`TPS` and `ε-SEFXs`, then some valid outcome is `ρ`-`TPS` and
`SEFX`. -/
theorem lemma11_TPS_strict (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFXs v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  obtain ⟨o, hvalid, hshare, hsefx⟩ := lemma11_strict v p rho (fun i => TPS n (v i) p) H
  exact ⟨o, hvalid, hshare, SEFX_of_SEFXs hvalid hsefx⟩

/-- **Lemma 11 for the truncated proportional share**, with `ε-SEFXu` as input. -/
theorem lemma11_TPS_u (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFXu v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o :=
  lemma11_u v p rho (fun i => TPS n (v i) p) H

end FairSelling
