import Mathlib
import RequestProject.ChoresModel

/-!
# Envy notions for chores with outsourcing (Definition 9)

This file formalizes Section "Envy Notion Definitions For Chores" of the manuscript's chores
appendix: envy-freeness `EF` and its relaxations `SEF1` (strong envy free up to one chore) and
`SEFX` (strong/sellable envy free up to any chore) for chores with outsourcing, together with
the "local pairwise maximin" derivation that motivates them.

## Definition 9 of the manuscript

> A chores allocation `(A₁,P₁),…,(Aₙ,Pₙ)` is envy free (EF) if for every agent `i` and other
> agent `j`, `c̄ᵢ(Aᵢ) + Pᵢ ≤ c̄ᵢ(A_j) + P_j`.  An allocation satisfies the following relaxations
> of EF if the above envy free condition holds whenever `Pᵢ > 0`, and the following relaxed
> conditions hold if `Pᵢ = 0`:
> 1. SEF1: `p(t) − cᵢ(t) ≥ c̄ᵢ(Aᵢ) − c̄ᵢ(A_j) − P_j` for some chore `t ∈ Aᵢ`;
> 2. SEFX: `p(t) − cᵢ(t) ≥ c̄ᵢ(Aᵢ) − c̄ᵢ(A_j) − P_j` for every chore `t ∈ Aᵢ`.

Exactly as in the goods setting (`RequestProject.Selling`), the literal reading of the relaxed
conditions is *not* a relaxation of envy-freeness, for two reasons, both of which we record
with explicit counterexamples below:

* an agent with an **empty** bundle has no chore `t ∈ Aᵢ` to exhibit, although it is not
  envious at all (`SEF1lit_not_relaxation_of_EF`); the relaxed condition must therefore be
  read as a *disjunction* with the envy-free condition itself;
* the in-house cost `cᵢ(t)` in the "delta" `p(t) − cᵢ(t)` must be read as the *effective* cost
  `c̄ᵢ(t) = min{cᵢ(t), p(t)}`, which is how it is obtained in the manuscript's own derivation
  of the condition (the displayed inequality `p(t) − c̄ᵢ(t) ≥ c̄ᵢ(Bᵢ) − c̄ᵢ(B_j)` there);
  with `cᵢ(t)` the delta may be negative and even a fully envy-free allocation violates it
  (`SEFXlit_not_relaxation_of_EF`).

The corrected notions `SEF1`, `SEFX` are genuine relaxations of `EF` (`SEF1_of_EF`,
`SEFX_of_EF`) and are implied by the literal ones (`SEFX_of_SEFXlit`, `SEF1_of_SEF1lit`).
-/

open scoped BigOperators

namespace FairChores

variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

/-- **Envy-freeness** for chores with outsourcing (Definition 9): every agent `i` weakly
prefers its own part to every other part, where a part is evaluated with the effective costs
`c̄ᵢ` plus the share of the outsourcing bill. -/
def EF (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j, cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j

/-- **SEF1** for chores (Definition 9.1), in the corrected reading: for every ordered pair of
agents `i, j`, if `Pᵢ > 0` the envy-free condition must hold, and if `Pᵢ = 0` it is enough that
either the envy-free condition holds, or that *some* chore `t ∈ Aᵢ` has an outsourcing delta
`p(t) − c̄ᵢ(t)` at least as large as `i`'s envy towards `j`. -/
def SEF1 (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 →
      (cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∨
      (∃ t ∈ o.kept i,
        (cbarSum (c i) p (o.kept i) + o.pay i) - (cbarSum (c i) p (o.kept j) + o.pay j)
          ≤ p t - cbar (c i) p t))

/-- **SEFX** for chores (Definition 9.2), in the corrected reading: as `SEF1`, but the
outsourcing delta condition must hold for *every* chore `t ∈ Aᵢ`. -/
def SEFX (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 →
      (cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∨
      (∀ t ∈ o.kept i,
        (cbarSum (c i) p (o.kept i) + o.pay i) - (cbarSum (c i) p (o.kept j) + o.pay j)
          ≤ p t - cbar (c i) p t))

/-- The *literal* transcription of Definition 9.1: the delta uses the in-house cost `cᵢ(t)`
and no exemption is made for an empty bundle. -/
def SEF1lit (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 → ∃ t ∈ o.kept i,
        cbarSum (c i) p (o.kept i) - cbarSum (c i) p (o.kept j) - o.pay j ≤ p t - c i t)

/-- The *literal* transcription of Definition 9.2; cf. `SEF1lit`. -/
def SEFXlit (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 → ∀ t ∈ o.kept i,
        cbarSum (c i) p (o.kept i) - cbarSum (c i) p (o.kept j) - o.pay j ≤ p t - c i t)

section Relations

variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}

omit [Fintype T] [DecidableEq T] in
/-- `SEFX` is a genuine relaxation of envy-freeness. -/
theorem SEFX_of_EF (h : EF c p o) : SEFX c p o := fun i j =>
  ⟨fun _ => h i j, fun _ => Or.inl (h i j)⟩

omit [Fintype T] [DecidableEq T] in
/-- `SEF1` is a genuine relaxation of envy-freeness. -/
theorem SEF1_of_EF (h : EF c p o) : SEF1 c p o := fun i j =>
  ⟨fun _ => h i j, fun _ => Or.inl (h i j)⟩

/-- `SEFX` implies `SEF1`. -/
theorem SEF1_of_SEFX (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t)
    (hvalid : o.Valid p) (h : SEFX c p o) : SEF1 c p o := by
  intro i j
  refine ⟨(h i j).1, fun hi => ?_⟩
  rcases (h i j).2 hi with hEF | hall
  · exact Or.inl hEF
  · rcases Finset.eq_empty_or_nonempty (o.kept i) with hemp | ⟨t, ht⟩
    · refine Or.inl ?_
      have h1 : 0 ≤ cbarSum (c i) p (o.kept j) := cbarSum_nonneg (hc i) hp _
      have h2 := hvalid.2.2.2.1 j
      rw [hemp, hi, cbarSum_empty]
      linarith
    · exact Or.inr ⟨t, ht, hall t ht⟩

omit [Fintype T] [DecidableEq T] in
/-- The literal reading of Definition 9.2 implies the corrected `SEFX`. -/
theorem SEFX_of_SEFXlit (h : SEFXlit c p o) : SEFX c p o := by
  intro i j
  refine ⟨(h i j).1, fun hi => Or.inr fun t ht => ?_⟩
  have hlit := (h i j).2 hi t ht
  have hct : cbar (c i) p t ≤ c i t := cbar_le_cost t
  rw [hi]
  linarith

omit [Fintype T] [DecidableEq T] in
/-- The literal reading of Definition 9.1 implies the corrected `SEF1`. -/
theorem SEF1_of_SEF1lit (h : SEF1lit c p o) : SEF1 c p o := by
  intro i j
  refine ⟨(h i j).1, fun hi => Or.inr ?_⟩
  obtain ⟨t, ht, hlit⟩ := (h i j).2 hi
  have hct : cbar (c i) p t ≤ c i t := cbar_le_cost t
  exact ⟨t, ht, by rw [hi]; linarith⟩

end Relations

/-! ### The local pairwise maximin derivation

The manuscript motivates the "delta" form of Definition 9 as follows: `SEFX` should forbid
outsourcing a chore `t` from `Bᵢ`, water-filling the resulting costs on `B_j` and `Bᵢ \ {t}`,
and ending up below `c̄ᵢ(Bᵢ)`, i.e. it should forbid
`(c̄ᵢ(Bᵢ \ {t}) + c̄ᵢ(B_j) + p(t))/2 < c̄ᵢ(Bᵢ)`.  The two lemmas below are the two steps of the
manuscript's computation: this water-filling inequality is exactly the delta condition, and
the delta condition degenerates to the plain envy-free condition when `c̄ᵢ(t) = p(t)`,
while for `c̄ᵢ(t) ≠ p(t)` the effective cost `c̄ᵢ(t)` is the in-house cost `cᵢ(t)`. -/

section Derivation

variable {ci p : T → ℝ}

omit [Fintype T] in
/-- Removing one chore from a bundle, measured with `c̄ᵢ`. -/
theorem cbarSum_sdiff_singleton {A : Finset T} {t : T} (ht : t ∈ A) :
    cbarSum ci p A = cbarSum ci p (A \ {t}) + cbar ci p t := by
  classical
  have hA : A = insert t (A \ {t}) := by
    ext x
    by_cases hx : x = t <;> simp [hx, ht]
  rw [cbarSum, cbarSum, hA, Finset.sum_insert (by simp)]
  simp [add_comm]

omit [Fintype T] in
/-- **The water-filling derivation**: for a chore `t` of agent `i`'s bundle `Bᵢ`, outsourcing
`t` and splitting the resulting total cost equally between `Bᵢ \ {t}` and `B_j` is no
improvement over `Bᵢ` exactly when the outsourcing delta `p(t) − c̄ᵢ(t)` covers agent `i`'s
envy towards `B_j`. -/
theorem waterfilling_iff_delta {Bi Bj : Finset T} {t : T} (ht : t ∈ Bi) :
    (cbarSum ci p (Bi \ {t}) + cbarSum ci p Bj + p t) / 2 ≥ cbarSum ci p Bi ↔
      p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj := by
  rw [cbarSum_sdiff_singleton (ci := ci) (p := p) ht]
  constructor <;> intro h <;> linarith

omit [Fintype T] [DecidableEq T] in
/-- If the effective cost of `t` is its market price, the delta condition is precisely the
envy-free condition. -/
theorem delta_iff_EF_of_cbar_eq_price {Bi Bj : Finset T} {t : T} (h : cbar ci p t = p t) :
    (p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj) ↔
      cbarSum ci p Bi ≤ cbarSum ci p Bj := by
  rw [h]
  constructor <;> intro h' <;> linarith

omit [Fintype T] [DecidableEq T] in
/-- If the effective cost of `t` is not its market price, it is the in-house cost, so the
delta condition takes the manuscript's form `p(t) − cᵢ(t) ≥ c̄ᵢ(Bᵢ) − c̄ᵢ(B_j)`. -/
theorem cbar_eq_cost_of_ne_price {t : T} (h : cbar ci p t ≠ p t) : cbar ci p t = ci t := by
  rcases min_cases (ci t) (p t) with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 h

end Derivation

/-! ### The literal notions are not relaxations of envy-freeness

Two chores, both with market price `1`, both costing `5` to each of two agents; each agent
performs one chore and no money changes hands.  Since `c̄ᵢ = min{5, 1} = 1` for both chores,
the allocation is fully envy free, and it satisfies the corrected `SEFX` (and hence `SEF1`);
but the literal delta `p(t) − cᵢ(t) = 1 − 5 = −4` is negative, so the literal `SEFX` and
`SEF1` both fail. -/

namespace LitCounterexample

/-- The cost function of both agents: every chore costs `5` in-house. -/
def cc : Fin 2 → Fin 2 → ℝ := fun _ _ => 5

/-- The market price of both chores is `1`. -/
def pp : Fin 2 → ℝ := fun _ => 1

/-- Each agent performs one chore; nothing is outsourced and no money changes hands. -/
def oo : Outcome (Fin 2) 2 :=
  { outsourced := ∅
    kept := fun j => {j}
    pay := fun _ => 0 }

lemma oo_valid : oo.Valid pp := by
  refine ⟨by simp [oo], ?_, ?_, by simp [oo], by simp [oo]⟩
  · intro j k hjk
    simp [oo, hjk]
  · refine Finset.eq_univ_iff_forall.mpr fun t => ?_
    simp only [oo, Finset.empty_union, Finset.mem_biUnion]
    exact ⟨t, Finset.mem_univ _, by simp⟩

lemma cbar_cc : ∀ t, cbar (cc 0) pp t = 1 := by
  intro t; simp [cbar, cc, pp]

lemma cbarSum_single (i j : Fin 2) : cbarSum (cc i) pp {j} = 1 := by
  simp [cbarSum, cbar, cc, pp]

lemma cbarSum_kept (i j : Fin 2) : cbarSum (cc i) pp (oo.kept j) = 1 :=
  cbarSum_single i j

/-- The allocation is envy free. -/
theorem oo_EF : EF cc pp oo := by
  intro i j
  simp [oo, cbarSum_single]

/-- ... and satisfies the corrected `SEFX`. -/
theorem oo_SEFX : SEFX cc pp oo := SEFX_of_EF oo_EF

/-- ... but it does **not** satisfy the literal `SEFX`: the literal notion is therefore not a
relaxation of envy-freeness. -/
theorem oo_not_SEFXlit : ¬ SEFXlit cc pp oo := by
  intro h
  have h2 := (h 0 1).2 (by simp [oo]) 0 (by simp [oo])
  rw [cbarSum_kept, cbarSum_kept] at h2
  norm_num [oo, cc, pp] at h2

/-- ... and it does not satisfy the literal `SEF1` either. -/
theorem oo_not_SEF1lit : ¬ SEF1lit cc pp oo := by
  intro h
  obtain ⟨t, ht, h2⟩ := (h 0 1).2 (by simp [oo])
  rw [cbarSum_kept, cbarSum_kept] at h2
  norm_num [oo, cc, pp] at h2

/-- Summary: there is a valid, fully envy-free chores allocation that satisfies neither the
literal `SEF1` nor the literal `SEFX` of Definition 9. -/
theorem lit_not_relaxation_of_EF :
    ∃ (c : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
      o.Valid p ∧ EF c p o ∧ ¬ SEF1lit c p o ∧ ¬ SEFXlit c p o :=
  ⟨cc, pp, oo, oo_valid, oo_EF, oo_not_SEF1lit, oo_not_SEFXlit⟩

end LitCounterexample

end FairChores
