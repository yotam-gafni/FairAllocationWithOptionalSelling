import Mathlib
import RequestProject.TPSSefxCharge
import RequestProject.TPSSefxServe

/-!
# Shrinking a bag to a safe, minimal, affordable package

This file is the combinatorial core of the improvement step of Algorithm 6: the `Shrink`
operation, in the corrected form described in `ISSUES_TPS_SEFX.md`.

Fix valuations `w`, prices `p`, and for every agent a *requirement* `req m` (its threshold if it
is unserved, its current utility raised by `ε` if it is served).  A *package* is a pair of
disjoint sets of pool goods `(S, S₀)` — `S` is kept, `S₀` is sold — together with an amount `q`
of cash; the cash is financed from the free bank `D` and from the proceeds of `S₀`.

The amount of cash attached to a package is always the *least* one that makes somebody claim it,

```
   Qc S  =  max {0, minₘ (req m − v̄ₘ(S))},
```

which has two crucial consequences: some agent claims the package (`Qc_claimed`), and as soon as
the package carries money *every* agent is exactly envy free towards it (`Qc_safe`) — which is
what Definition 4 of the manuscript demands of a bundle that carries sale proceeds.

A package is *feasible* if its cash can be paid (`Feas`) and *admissible* if in addition no agent
envies it up to any set of goods (`Adm`).  Two constructions are carried out:

* `exists_adm` — every feasible package can be shrunk to an admissible one *with the same
  footprint* `S ∪ S₀`, by repeatedly selling a set of goods that some agent envies;
* `exists_min_adm` — among all admissible packages with footprint inside the pool one may choose
  one whose footprint is of least cardinality, and, among those, one that sells as little as
  possible.  Minimality of the footprint is what bounds the cost of the package.
-/

open scoped BigOperators

namespace FairSelling

namespace CfgTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

section Defs

variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)

/-- The least requirement gap left by the set `S`. -/
noncomputable def gapMin (S : Finset G) : ℝ :=
  Finset.univ.inf' ⟨k0, Finset.mem_univ k0⟩ (fun m => req m - vbarSum (w m) p S)

/-- The least amount of cash that makes the set `S` claimed by somebody. -/
noncomputable def Qc (S : Finset G) : ℝ := max 0 (gapMin w p req k0 S)

/-- The package `(S, S₀)` is *feasible* with a free bank of `D`: its cash can be paid out of the
bank together with the proceeds of the goods it sells. -/
def Feas (D : ℝ) (S S₀ : Finset G) : Prop := Qc w p req k0 S ≤ D + ∑ g ∈ S₀, p g

/-- The package `(S, S₀)` is *admissible*: it is feasible, and no agent values what is left of
`S` after removing a set of goods, plus the price of the removed goods and the cash, above its
requirement.  Taking `X` a singleton is the up-to-any-good condition of Definition 4. -/
def Adm (D : ℝ) (S S₀ : Finset G) : Prop :=
  Feas w p req k0 D S S₀ ∧
  ∀ X ⊆ S, X.Nonempty → ∀ m,
    vbarSum (w m) p (S \ X) + (∑ g ∈ X, p g) + Qc w p req k0 S ≤ req m

end Defs

section Basic

variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)

omit [Fintype G] [DecidableEq G] in
lemma gapMin_le (S : Finset G) (m : Fin n) :
    gapMin w p req k0 S ≤ req m - vbarSum (w m) p S :=
  Finset.inf'_le _ (Finset.mem_univ m)

omit [Fintype G] [DecidableEq G] in
lemma Qc_nonneg (S : Finset G) : 0 ≤ Qc w p req k0 S := le_max_left _ _

omit [Fintype G] [DecidableEq G] in
/-- Somebody claims the package: the agent realizing the least gap. -/
lemma Qc_claimed (S : Finset G) : ∃ k, req k ≤ vbarSum (w k) p S + Qc w p req k0 S := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' (⟨k0, Finset.mem_univ k0⟩ :
    (Finset.univ : Finset (Fin n)).Nonempty) (fun m => req m - vbarSum (w m) p S)
  refine ⟨k, ?_⟩
  have : gapMin w p req k0 S = req k - vbarSum (w k) p S := hk
  have h2 : gapMin w p req k0 S ≤ Qc w p req k0 S := le_max_right _ _
  rw [this] at h2
  linarith

omit [Fintype G] [DecidableEq G] in
/-- A package that carries money is envied by nobody. -/
lemma Qc_safe {S : Finset G} (h : 0 < Qc w p req k0 S) (m : Fin n) :
    vbarSum (w m) p S + Qc w p req k0 S ≤ req m := by
  have hq : Qc w p req k0 S = gapMin w p req k0 S := by
    unfold Qc at h ⊢
    rcases max_cases (0:ℝ) (gapMin w p req k0 S) with ⟨he, hle⟩ | ⟨he, hle⟩
    · rw [he] at h; exact absurd h (lt_irrefl 0)
    · exact he
  have := gapMin_le w p req k0 S m
  rw [← hq] at this
  linarith

omit [Fintype G] [DecidableEq G] in
/-- An upper bound for the cash of a package. -/
lemma Qc_le_of_gap {S : Finset G} {c : ℝ} (hc : 0 ≤ c) (m : Fin n)
    (h : req m - vbarSum (w m) p S ≤ c) : Qc w p req k0 S ≤ c :=
  max_le hc (le_trans (gapMin_le w p req k0 S m) h)

end Basic

/-! ### Shrinking a feasible package to an admissible one -/

section Shrink

variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)

omit [Fintype G] in
/-- **Shrinking.**  Every feasible package can be turned into an admissible package with the same
footprint, by repeatedly selling a set of goods that some agent envies. -/
theorem exists_adm (hp : ∀ g, 0 ≤ p g) :
    ∀ (c : ℕ) (S S₀ : Finset G), S.card ≤ c → Disjoint S S₀ → Feas w p req k0 D S S₀ →
      ∃ T T₀ : Finset G, T ⊆ S ∧ S₀ ⊆ T₀ ∧ T ∪ T₀ = S ∪ S₀ ∧ Disjoint T T₀ ∧
        Adm w p req k0 D T T₀ := by
  intro c
  induction c with
  | zero =>
    intro S S₀ hcard hdisj hfeas
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hS
    refine ⟨∅, S₀, Finset.Subset.refl _, Finset.Subset.refl _, rfl, hdisj, hfeas, ?_⟩
    intro X hX hXne m
    exact absurd (Finset.subset_empty.mp hX ▸ hXne) (by simp)
  | succ c ih =>
    intro S S₀ hcard hdisj hfeas
    by_cases hadm : ∀ X ⊆ S, X.Nonempty → ∀ m,
        vbarSum (w m) p (S \ X) + (∑ g ∈ X, p g) + Qc w p req k0 S ≤ req m
    · exact ⟨S, S₀, Finset.Subset.refl _, Finset.Subset.refl _, rfl, hdisj, hfeas, hadm⟩
    · push_neg at hadm
      obtain ⟨X, hXS, hXne, m, hm⟩ := hadm
      have hXS₀ : Disjoint X S₀ := Finset.disjoint_of_subset_left hXS hdisj
      have hpX : 0 ≤ ∑ g ∈ X, p g := Finset.sum_nonneg (fun g _ => hp g)
      have hfeas' : Feas w p req k0 D (S \ X) (S₀ ∪ X) := by
        have h1 : Qc w p req k0 (S \ X) ≤ (∑ g ∈ X, p g) + Qc w p req k0 S := by
          refine Qc_le_of_gap w p req k0 (by linarith [Qc_nonneg w p req k0 S]) m ?_
          linarith
        have h2 : ∑ g ∈ S₀ ∪ X, p g = (∑ g ∈ S₀, p g) + ∑ g ∈ X, p g :=
          Finset.sum_union hXS₀.symm
        unfold Feas at hfeas ⊢
        rw [h2]
        linarith
      have hcard' : (S \ X).card ≤ c := by
        have : (S \ X).card < S.card := by
          refine Finset.card_lt_card ?_
          refine ⟨Finset.sdiff_subset, ?_⟩
          obtain ⟨x, hx⟩ := hXne
          intro hcon
          have := hcon (hXS hx)
          simp only [Finset.mem_sdiff] at this
          exact this.2 hx
        omega
      have hdisj' : Disjoint (S \ X) (S₀ ∪ X) := by
        refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
        · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
        · exact Finset.sdiff_disjoint
      obtain ⟨T, T₀, hT, hT₀, hTU, hTdisj, hTadm⟩ := ih (S \ X) (S₀ ∪ X) hcard' hdisj' hfeas'
      refine ⟨T, T₀, Finset.Subset.trans hT Finset.sdiff_subset,
        Finset.Subset.trans Finset.subset_union_left hT₀,
        ?_, hTdisj, hTadm⟩
      rw [hTU]
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      by_cases hx : x ∈ X
      · have := hXS hx
        tauto
      · tauto

end Shrink


/-! ### Choosing a package with a minimal footprint -/

section Minimal

variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)

omit [Fintype G] in
open Classical in
/-- **The choice of package.**  Among the admissible packages whose footprint lies in the pool,
choose one minimizing the pair (size of the footprint, number of goods sold), lexicographically.
The pool itself is feasible by hypothesis, so there is something to choose from. -/
theorem exists_min_adm (P : Finset G) (hp : ∀ g, 0 ≤ p g) (hfeasP : Feas w p req k0 D P ∅) :
    ∃ S S₀ : Finset G, S ∪ S₀ ⊆ P ∧ Disjoint S S₀ ∧ Adm w p req k0 D S S₀ ∧
      ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card
          ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card := by
  classical
  set C : Finset (Finset G × Finset G) :=
    (P.powerset ×ˢ P.powerset).filter (fun x => Disjoint x.1 x.2 ∧ Adm w p req k0 D x.1 x.2)
    with hC
  have hCne : C.Nonempty := by
    obtain ⟨T, T₀, hT, hT₀, hTU, hTdisj, hTadm⟩ :=
      exists_adm w p req k0 D hp P.card P ∅ le_rfl (by simp) hfeasP
    refine ⟨(T, T₀), ?_⟩
    have hT₀P : T₀ ⊆ P := by
      intro x hx
      have : x ∈ T ∪ T₀ := Finset.mem_union_right _ hx
      rw [hTU] at this
      simpa using this
    simp only [hC, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    exact ⟨⟨hT, hT₀P⟩, hTdisj, hTadm⟩
  obtain ⟨x, hxC, hxmin⟩ := Finset.exists_min_image C
    (fun x => (x.1 ∪ x.2).card * (P.card + 1) + x.2.card) hCne
  simp only [hC, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hxC
  refine ⟨x.1, x.2, Finset.union_subset hxC.1.1 hxC.1.2, hxC.2.1, hxC.2.2, ?_⟩
  intro T T₀ hTP hTdisj hTadm
  refine hxmin (T, T₀) ?_
  simp only [hC, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  exact ⟨⟨Finset.Subset.trans Finset.subset_union_left hTP,
    Finset.Subset.trans Finset.subset_union_right hTP⟩, hTdisj, hTadm⟩

variable {w p req k0 D}

omit [Fintype G] in
/-- **Footprint minimality.**  Removing any single good from the footprint of the chosen package
leaves something that the free bank can no longer pay for. -/
theorem lt_Qc_erase {P S S₀ : Finset G} (hp : ∀ g, 0 ≤ p g) (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    {g : G} (hg : g ∈ S ∪ S₀) : D < Qc w p req k0 ((S ∪ S₀) \ {g}) := by
  classical
  by_contra hcon
  push_neg at hcon
  set U := S ∪ S₀ with hU
  have hfeas : Feas w p req k0 D (U \ {g}) ∅ := by
    unfold Feas
    simpa using hcon
  obtain ⟨T, T₀, hT, _, hTU, hTdisj, hTadm⟩ :=
    exists_adm w p req k0 D hp (U \ {g}).card (U \ {g}) ∅ le_rfl (by simp) hfeas
  have hTUeq : T ∪ T₀ = U \ {g} := by rw [hTU]; simp
  have hTP : T ∪ T₀ ⊆ P := by rw [hTUeq]; exact Finset.Subset.trans Finset.sdiff_subset hUP
  have hkey := hmin T T₀ hTP hTdisj hTadm
  rw [hTUeq] at hkey
  have hcardU : (U \ {g}).card = U.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hg]
  have hUpos : 1 ≤ U.card := Finset.card_pos.mpr ⟨g, hg⟩
  have hT₀P : T₀ ⊆ P := Finset.Subset.trans (Finset.Subset.trans Finset.subset_union_right
    (le_of_eq hTUeq)) (Finset.Subset.trans Finset.sdiff_subset hUP)
  have hT₀card : T₀.card ≤ P.card := Finset.card_le_card hT₀P
  rw [hcardU] at hkey
  have hUcardP : U.card ≤ P.card := Finset.card_le_card hUP
  nlinarith [hkey, hT₀card, hUpos, Nat.sub_add_cancel hUpos]

omit [Fintype G] in
/-- **The tie-break.**  If the chosen package sells anything, then keeping the whole footprint is
not admissible. -/
theorem not_adm_keep_all {P S S₀ : Finset G} (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    (hS₀ : S₀.Nonempty) : ¬ Adm w p req k0 D (S ∪ S₀) ∅ := by
  intro hadm
  have := hmin (S ∪ S₀) ∅ (by simpa using hUP) (by simp) hadm
  simp only [Finset.union_empty, Finset.card_empty, add_zero] at this
  have : S₀.card = 0 := by omega
  exact absurd (Finset.card_eq_zero.mp this) (Finset.nonempty_iff_ne_empty.mp hS₀)

end Minimal


/-! ### The cost of the chosen package -/

section Cost

variable {w : Fin n → G → ℝ} {p : G → ℝ} {req : Fin n → ℝ} {k0 : Fin n} {D : ℝ}

omit [Fintype G] [DecidableEq G] in
lemma saleLoss_le_vbar (t : ℝ) (u : G → ℝ) (g : G) :
    ChargeTPS.saleLoss u p t g ≤ vbar u p g - p g := by
  have := trunc_le_vbar u p t g
  unfold ChargeTPS.saleLoss
  linarith

omit [Fintype G] [DecidableEq G] in
lemma Qc_empty_le (hreq0 : ∀ m, 0 ≤ req m) (m : Fin n) : Qc w p req k0 ∅ ≤ req m := by
  refine max_le (hreq0 m) ?_
  have := gapMin_le w p req k0 ∅ m
  simp only [vbarSum, Finset.sum_empty, sub_zero] at this
  exact this

omit [Fintype G] in
/-- **The cost of a footprint of at least two goods.**  Footprint minimality forces every good of
the footprint, and the footprint minus any good, to be worth less than `req j − D` to the agent
`j`, so the whole footprint is worth less than `2·(req j − D)`. -/
theorem truncBundle_add_le_two {P S S₀ : Finset G} (t : Fin n → ℝ) (j : Fin n)
    (hp : ∀ g, 0 ≤ p g) (hD : 0 ≤ D) (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    (hcard : 2 ≤ (S ∪ S₀).card) :
    truncBundle (w j) p (t j) (S ∪ S₀) + D ≤ 2 * req j := by
  classical
  set U := S ∪ S₀ with hU
  obtain ⟨g, hg, h, hh, hgh⟩ := Finset.one_lt_card.mp hcard
  have key : ∀ x ∈ U, vbarSum (w j) p (U \ {x}) < req j - D := by
    intro x hx
    have h1 : D < Qc w p req k0 (U \ {x}) := lt_Qc_erase hp hUP hmin hx
    have h2 : D < gapMin w p req k0 (U \ {x}) := by
      unfold Qc at h1
      rcases max_cases (0:ℝ) (gapMin w p req k0 (U \ {x})) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at h1; linarith
      · rw [he] at h1; exact h1
    have h3 := gapMin_le w p req k0 (U \ {x}) j
    linarith
  have hsplit : truncBundle (w j) p (t j) U
      = truncBundle (w j) p (t j) (U \ {g}) + truncBundle (w j) p (t j) ({g} : Finset G) :=
    truncBundle_sdiff (w j) p (t j) (Finset.singleton_subset_iff.mpr hg)
  have h1 : truncBundle (w j) p (t j) (U \ {g}) ≤ vbarSum (w j) p (U \ {g}) :=
    truncBundle_le_vbarSum _ _ _ _
  have hgU : g ∈ U \ {h} := Finset.mem_sdiff.mpr ⟨hg, by simpa using hgh⟩
  have h2 : truncBundle (w j) p (t j) ({g} : Finset G) ≤ vbarSum (w j) p (U \ {h}) := by
    simp only [truncBundle, Finset.sum_singleton]
    refine le_trans (trunc_le_vbar (w j) p (t j) g) ?_
    refine Finset.single_le_sum (fun x _ => ?_) hgU
    exact le_trans (hp x) (le_max_left _ _)
  have k1 := key g hg
  have k2 := key h hh
  linarith

omit [Fintype G] in
/-- **The cost of the chosen package.**  Whatever its shape, the package chosen by
`exists_min_adm` costs any agent `j` whose requirement is a threshold at most twice that
threshold — the bound the counting argument needs. -/
theorem cost_bound {P S S₀ : Finset G} (t : Fin n → ℝ) (j : Fin n)
    (hp : ∀ g, 0 ≤ p g) (hD : 0 ≤ D)
    (hreq0 : ∀ m, 0 ≤ req m) (hreqt : req j ≤ t j) (htreq : t j ≤ 2 * req j)
    (hUP : S ∪ S₀ ⊆ P) (hdisj : Disjoint S S₀) (hadm : Adm w p req k0 D S S₀)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card) :
    truncBundle (w j) p (t j) S + Qc w p req k0 S
      + ∑ g ∈ S₀, ChargeTPS.saleLoss (w j) p (t j) g ≤ 2 * req j := by
  classical
  have hcosteq : truncBundle (w j) p (t j) S + Qc w p req k0 S
      + ∑ g ∈ S₀, ChargeTPS.saleLoss (w j) p (t j) g
      = truncBundle (w j) p (t j) (S ∪ S₀) + Qc w p req k0 S - ∑ g ∈ S₀, p g := by
    rw [ChargeTPS.sum_saleLoss, truncBundle, truncBundle, truncBundle,
      Finset.sum_union hdisj]
    ring
  have hreqj : 0 ≤ req j := hreq0 j
  rcases lt_or_ge (S ∪ S₀).card 2 with hlt | hge
  · -- the footprint has at most one good
    have hc2 : (S ∪ S₀).card = 0 ∨ (S ∪ S₀).card = 1 := by omega
    rcases hc2 with hc | hc
    · -- empty footprint
      have hSe : S = ∅ := by
        have : S ⊆ S ∪ S₀ := Finset.subset_union_left
        rw [Finset.card_eq_zero.mp hc] at this
        exact Finset.subset_empty.mp this
      have hS₀e : S₀ = ∅ := by
        have : S₀ ⊆ S ∪ S₀ := Finset.subset_union_right
        rw [Finset.card_eq_zero.mp hc] at this
        exact Finset.subset_empty.mp this
      rw [hSe, hS₀e]
      simp only [truncBundle, Finset.sum_empty, zero_add, add_zero]
      linarith [Qc_empty_le (w := w) (p := p) (k0 := k0) hreq0 j]
    · -- one good in the footprint
      obtain ⟨g, hgU⟩ := Finset.card_eq_one.mp hc
      have hScases : S = ∅ ∨ S = {g} :=
        Finset.subset_singleton_iff.mp (hgU ▸ (Finset.subset_union_left : S ⊆ S ∪ S₀))
      have hS₀cases : S₀ = ∅ ∨ S₀ = {g} :=
        Finset.subset_singleton_iff.mp (hgU ▸ (Finset.subset_union_right : S₀ ⊆ S ∪ S₀))
      have hQ1nn : 0 ≤ Qc w p req k0 ({g} : Finset G) := Qc_nonneg w p req k0 _
      rcases hScases with hSe | hSe
      · -- the good is sold
        rcases hS₀cases with hS₀e | hS₀e
        · exfalso; rw [hSe, hS₀e] at hgU; simp at hgU
        · -- `S = ∅`, `S₀ = {g}`
          rw [hSe, hS₀e]
          simp only [truncBundle, Finset.sum_empty, zero_add, Finset.sum_singleton]
          have hRle : ∀ m, Qc w p req k0 (∅ : Finset G) ≤ req m := fun m => Qc_empty_le hreq0 m
          have hloss := saleLoss_le_vbar (p := p) (t j) (w j) g
          have hloss0 := ChargeTPS.saleLoss_nonneg (w j) p (t j) g
          have hnotadm : ¬ Adm w p req k0 D (S ∪ S₀) ∅ :=
            not_adm_keep_all hUP hmin (by rw [hS₀e]; exact ⟨g, by simp⟩)
          rw [hgU] at hnotadm
          by_cases hfeasg : Feas w p req k0 D ({g} : Finset G) ∅
          · -- keeping the good is feasible, so it must be inadmissible
            have hviol : ∃ X ⊆ ({g} : Finset G), X.Nonempty ∧ ∃ m,
                req m < vbarSum (w m) p (({g} : Finset G) \ X) + (∑ x ∈ X, p x)
                  + Qc w p req k0 ({g} : Finset G) := by
              by_contra hcon
              push_neg at hcon
              exact hnotadm ⟨hfeasg, fun X hX hXne m => hcon X hX hXne m⟩
            obtain ⟨X, hX, hXne, m, hm⟩ := hviol
            have hXg : X = {g} := (Finset.subset_singleton_iff.mp hX).resolve_left
              (Finset.nonempty_iff_ne_empty.mp hXne)
            rw [hXg] at hm
            simp only [Finset.sdiff_self, vbarSum, Finset.sum_empty, zero_add,
              Finset.sum_singleton] at hm
            rcases eq_or_lt_of_le hQ1nn with hQ1 | hQ1
            · -- the good alone needs no cash: its price exceeds every requirement
              have hRp : Qc w p req k0 (∅ : Finset G) ≤ p g := by
                linarith [hRle m]
              have hRt : Qc w p req k0 (∅ : Finset G) ≤ t j := le_trans (hRle j) hreqt
              have := ChargeTPS.cash_add_saleLoss_le (w j) p (t j) g
                (Qc w p req k0 (∅ : Finset G)) hRp hRt
              linarith
            · -- the good alone needs cash, and then nobody envies it
              have hsafe := Qc_safe w p req k0 hQ1 j
              simp only [vbarSum, Finset.sum_singleton] at hsafe
              linarith [hRle m]
          · -- keeping the good is infeasible
            have hQ1D : D < Qc w p req k0 ({g} : Finset G) := by
              unfold Feas at hfeasg
              push_neg at hfeasg
              simpa using hfeasg
            have hQ1pos : 0 < Qc w p req k0 ({g} : Finset G) := lt_of_le_of_lt hD hQ1D
            have hsafe := Qc_safe w p req k0 hQ1pos j
            simp only [vbarSum, Finset.sum_singleton] at hsafe
            linarith [hRle j, hp g]
      · -- the good is kept
        rcases hS₀cases with hS₀e | hS₀e
        · rw [hSe, hS₀e]
          simp only [truncBundle, Finset.sum_singleton, Finset.sum_empty, add_zero]
          rcases eq_or_lt_of_le hQ1nn with hQ1 | hQ1
          · -- no cash: the good's price is bounded by the requirement
            have hpg : p g ≤ req j := by
              have := hadm.2 {g} (by rw [hSe]) ⟨g, by simp⟩ j
              rw [hSe] at this
              simp only [Finset.sdiff_self, vbarSum, Finset.sum_empty, zero_add,
                Finset.sum_singleton] at this
              linarith
            have h1 : trunc (w j) p (t j) g ≤ max (p g) (t j) := trunc_le_max _ _ _ _
            rcases max_cases (p g) (t j) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;>
              linarith
          · have hsafe := Qc_safe w p req k0 hQ1 j
            simp only [vbarSum, Finset.sum_singleton] at hsafe
            have := trunc_le_vbar (w j) p (t j) g
            linarith
        · exfalso; rw [hSe, hS₀e] at hdisj; simp at hdisj
  · -- the footprint has at least two goods
    have h1 := truncBundle_add_le_two (w := w) (req := req) (k0 := k0) t j hp hD hUP hmin hge
    have h2 := hadm.1
    unfold Feas at h2
    rw [hcosteq]
    linarith

end Cost

end CfgTPS

end FairSelling
