import Mathlib
import RequestProject.Selling

/-!
# Computing the Truncated Proportional Share

This file formalizes Appendix E of the manuscript: the claim that `f(t) ≥ t` implies
`TPS ≥ t` (called "Claim E" in the manuscript), and the correctness of the simple
algorithm that computes the `TPS` exactly:

> Consider the (at most `2m+1`) breakpoints `{0} ∪ {v(g)} ∪ {p(g)}`, sorted in decreasing
> order `s₁, s₂, …`.  Find the first index `k` with `f(sₖ) ≥ sₖ`.  If `k = 1` then
> `TPS = PS`.  If `k > 1` then `sₖ ≤ TPS < sₖ₋₁`, and, since `f` is affine on the
> interval `[sₖ, sₖ₋₁]`, the `TPS` is obtained by solving a linear equation there.

The results below are stated in a form that is independent of the sorting step:

* `le_TPS_of_le_truncSum` — Claim E.
* `truncSum_bracket` — on an interval `[a, c]` containing no breakpoint in its interior,
  `f(t) = (C + k·t)/n` where `k` is the number of goods `g` with `v(g) ≥ c` and
  `p(g) ≤ a`, and `C` is the (constant) contribution of the remaining goods.
* `TPS_lt_of_no_fixed_above` — if `f(b) < b` and `f(s) < s` at every breakpoint `s ≥ b`,
  then `TPS < b`  (this is the statement that justifies scanning the breakpoints from
  the top and stopping at the first one with `f(s) ≥ s`).
* `TPS_eq_PS_of_top` — the case `k = 1`: `TPS = PS`.
* `TPS_eq_bracket_formula` — the case `k > 1`: the `TPS` is the solution `C/(n−k)` of the
  linear equation on the bracketing interval, and it lies in `[a, c)`.
* `TPS_eq_PS_of_max_breakpoint`, `TPS_of_consecutive_breakpoints` — the same two cases packaged
  directly in terms of the breakpoint set `{0} ∪ {v(g)} ∪ {p(g)}`.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Claim E -/

omit [DecidableEq G] in
/-- **Claim E** of the manuscript: if `f(t) ≥ t` for some `t`, then `TPS ≥ t`. -/
theorem le_TPS_of_le_truncSum (v p : G → ℝ) {t : ℝ} (ht : t ≤ truncSum n v p t) :
    t ≤ TPS n v p :=
  le_csSup (TPSset_bddAbove v p) ht

omit [DecidableEq G] in
/-- `TPS` is nonnegative (prices being nonnegative). -/
theorem TPS_nonneg (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ TPS n v p :=
  le_csSup (TPSset_bddAbove v p) (mem_TPSset_zero v p hp)

/-! ### The truncated-proportional map is affine between breakpoints -/

/-- `NoBreak v p a c` says that no breakpoint of the truncated-proportional map lies
strictly between `a` and `c`: every value `v g` and every price `p g` is either `≤ a`
or `≥ c`. -/
def NoBreak (v p : G → ℝ) (a c : ℝ) : Prop :=
  ∀ g, (v g ≤ a ∨ c ≤ v g) ∧ (p g ≤ a ∨ c ≤ p g)

open Classical in
/-- The goods whose contribution to `f` equals `t` throughout the interval `[a, c]`. -/
noncomputable def slopeGoods (v p : G → ℝ) (a c : ℝ) : Finset G :=
  Finset.univ.filter (fun g => c ≤ v g ∧ p g ≤ a)

/-- The (constant) contribution to `n · f` of the goods that are not `slopeGoods`. -/
noncomputable def flatConst (v p : G → ℝ) (a c : ℝ) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => ¬ (c ≤ v g ∧ p g ≤ a)), max (p g) (min (v g) a)

omit [Fintype G] [DecidableEq G] in
private lemma trunc_pointwise (v p : G → ℝ) {a c t : ℝ} (hnb : NoBreak v p a c)
    (hat : a ≤ t) (htc : t ≤ c) (g : G) :
    max (p g) (min (v g) t)
      = (if c ≤ v g ∧ p g ≤ a then t else max (p g) (min (v g) a)) := by
  rcases hnb g with ⟨hv, hp⟩
  by_cases hcase : c ≤ v g ∧ p g ≤ a
  · rw [if_pos hcase]
    rw [min_eq_right (le_trans htc hcase.1), max_eq_right (le_trans hcase.2 hat)]
  · rw [if_neg hcase]
    rcases hv with hv | hv
    · rw [min_eq_left (le_trans hv hat), min_eq_left hv]
    · -- `c ≤ v g`, so by the case assumption `p g > a`, hence `c ≤ p g`
      have hpa : ¬ p g ≤ a := fun h => hcase ⟨hv, h⟩
      have hpc : c ≤ p g := hp.resolve_left hpa
      rw [min_eq_right (le_trans htc hv), max_eq_left (le_trans htc hpc)]
      rcases le_total (v g) a with h | h
      · rw [min_eq_left h, max_eq_left (le_trans (le_trans h hat) (le_trans htc hpc))]
      · rw [min_eq_right h, max_eq_left (le_trans (le_trans hat htc) hpc)]

omit [DecidableEq G] in
/-- **Affinity between breakpoints.**  If no breakpoint lies strictly inside `[a, c]`,
then for `t ∈ [a, c]` we have `f(t) = (C + k·t)/n`, where `k` is the number of goods
whose value is at least `c` and whose price is at most `a`, and `C` is the constant
contribution of the other goods. -/
theorem truncSum_bracket (v p : G → ℝ) {a c t : ℝ} (hnb : NoBreak v p a c)
    (hat : a ≤ t) (htc : t ≤ c) :
    truncSum n v p t
      = (flatConst v p a c + ((slopeGoods v p a c).card : ℝ) * t) / n := by
  classical
  unfold truncSum flatConst slopeGoods
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g => c ≤ v g ∧ p g ≤ a)
        (fun g => max (p g) (min (v g) t))]
  have h1 : ∑ g ∈ Finset.univ.filter (fun g => c ≤ v g ∧ p g ≤ a), max (p g) (min (v g) t)
      = ((Finset.univ.filter (fun g => c ≤ v g ∧ p g ≤ a)).card : ℝ) * t := by
    rw [Finset.sum_congr rfl (fun g hg => ?_), Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mem_filter] at hg
    rw [trunc_pointwise v p hnb hat htc g, if_pos hg.2]
  have h2 : ∑ g ∈ Finset.univ.filter (fun g => ¬ (c ≤ v g ∧ p g ≤ a)), max (p g) (min (v g) t)
      = ∑ g ∈ Finset.univ.filter (fun g => ¬ (c ≤ v g ∧ p g ≤ a)), max (p g) (min (v g) a) := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [Finset.mem_filter] at hg
    rw [trunc_pointwise v p hnb hat htc g, if_neg hg.2]
  rw [h1, h2]; ring

/-! ### Localizing the TPS -/

omit [DecidableEq G] in
/-- If `t` is at least every value `v g`, then `f(t) = PS`. -/
theorem truncSum_of_ge (v p : G → ℝ) {t : ℝ} (ht : ∀ g, v g ≤ t) :
    truncSum n v p t = PS n v p := by
  unfold truncSum PS
  congr 1
  exact Finset.sum_congr rfl (fun g _ => by rw [min_eq_left (ht g)])

omit [DecidableEq G] in
/-- **The case `k = 1` of the algorithm.**  If `s` dominates every value `v g` and
`f(s) ≥ s`, then `TPS = PS`. -/
theorem TPS_eq_PS_of_top (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {s : ℝ}
    (hs : ∀ g, v g ≤ s) (hfs : s ≤ truncSum n v p s) :
    TPS n v p = PS n v p := by
  have hsPS : s ≤ PS n v p := by rw [← truncSum_of_ge v p hs]; exact hfs
  have hfix : PS n v p ≤ truncSum n v p (PS n v p) :=
    le_of_eq (truncSum_of_ge v p (fun g => le_trans (hs g) hsPS)).symm
  exact le_antisymm (TPS_le_PS v p hp) (le_TPS_of_le_truncSum v p hfix)

omit [DecidableEq G] in
/-- **Scanning the breakpoints from the top.**  If `f(b) < b` and `f(s) < s` at every
breakpoint `s ≥ b` (breakpoints being the values `v g` and the prices `p g`), then
`TPS < b`. -/
theorem TPS_lt_of_no_fixed_above (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {b : ℝ}
    (hb : truncSum n v p b < b)
    (hbv : ∀ g, b ≤ v g → truncSum n v p (v g) < v g)
    (hbp : ∀ g, b ≤ p g → truncSum n v p (p g) < p g) :
    TPS n v p < b := by
  classical
  by_contra hcon
  push_neg at hcon   -- `b ≤ TPS`
  set t₀ := TPS n v p with ht₀def
  have hfix : truncSum n v p t₀ = t₀ := TPS_truncSum v p hp
  -- `t₀` is not a breakpoint
  have hnotv : ∀ g, v g ≠ t₀ := by
    intro g hg
    have := hbv g (by rw [hg]; exact hcon)
    rw [hg, hfix] at this; exact lt_irrefl _ this
  have hnotp : ∀ g, p g ≠ t₀ := by
    intro g hg
    have := hbp g (by rw [hg]; exact hcon)
    rw [hg, hfix] at this; exact lt_irrefl _ this
  have hbt : b < t₀ := lt_of_le_of_ne hcon (by rintro rfl; exact absurd hfix (ne_of_lt hb))
  -- the left endpoint `a`
  set L : Finset ℝ :=
    (insert b (((Finset.univ.image v) ∪ (Finset.univ.image p)).filter
      (fun s => b ≤ s))).filter (fun s => s < t₀) with hLdef
  have hbL : b ∈ L := by
    simp only [hLdef, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, hbt⟩
  obtain ⟨a, haL, hamax⟩ := Finset.exists_max_image L (fun x => x) ⟨b, hbL⟩
  have hat₀ : a < t₀ := by
    simp only [hLdef, Finset.mem_filter] at haL; exact haL.2
  have hba : b ≤ a := hamax b hbL
  have hga : truncSum n v p a < a := by
    simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at haL
    rcases haL.1 with h | h
    · rw [h]; exact hb
    · rcases h.1 with ⟨g, _, hg⟩ | ⟨g, _, hg⟩
      · rw [← hg]; exact hbv g (by rw [hg]; exact h.2)
      · rw [← hg]; exact hbp g (by rw [hg]; exact h.2)
  -- the right endpoint `c`
  set U : Finset ℝ :=
    (((Finset.univ.image v) ∪ (Finset.univ.image p)).filter (fun s => t₀ < s)) with hUdef
  -- in either case we produce `c > t₀` with `NoBreak v p a c`
  have main : ∀ c : ℝ, t₀ < c → NoBreak v p a c → c < truncSum n v p c := by
    intro c hc hnb
    have h1 := truncSum_bracket (n := n) v p hnb (le_of_lt hat₀) (le_of_lt hc)
    have h2 := truncSum_bracket (n := n) v p hnb (le_refl a) (le_of_lt (lt_trans hat₀ hc))
    have h3 := truncSum_bracket (n := n) v p hnb (le_of_lt (lt_trans hat₀ hc)) (le_refl c)
    set C := flatConst v p a c
    set k := ((slopeGoods v p a c).card : ℝ)
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    -- from `f(t₀) = t₀`
    have e1 : C + k * t₀ = n * t₀ := by
      rw [hfix] at h1
      rw [eq_comm, div_eq_iff (ne_of_gt hn')] at h1
      linarith [h1]
    -- from `f(a) < a`
    have e2 : C + k * a < n * a := by
      rw [h2, div_lt_iff₀ hn'] at hga
      linarith [hga]
    have hkn : (n : ℝ) - k < 0 := by
      nlinarith [hat₀, e1, e2]
    rw [h3, lt_div_iff₀ hn']
    nlinarith [hc, hkn, e1]
  by_cases hU : U.Nonempty
  · obtain ⟨c, hcU, hcmin⟩ := U.exists_min_image id hU
    have hct : t₀ < c := by
      simp only [hUdef, Finset.mem_filter] at hcU; exact hcU.2
    have hnb : NoBreak v p a c := by
      intro g
      constructor
      · rcases lt_trichotomy (v g) t₀ with h | h | h
        · left
          by_contra hcontra
          push_neg at hcontra
          have : v g ∈ L := by
            simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
              Finset.mem_image]
            exact ⟨Or.inr ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩, h⟩
          exact absurd (hamax _ this) (not_le.mpr hcontra)
        · exact absurd h (hnotv g)
        · right
          refine hcmin (v g) ?_
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, h⟩
      · rcases lt_trichotomy (p g) t₀ with h | h | h
        · left
          by_contra hcontra
          push_neg at hcontra
          have : p g ∈ L := by
            simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
              Finset.mem_image]
            exact ⟨Or.inr ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩, h⟩
          exact absurd (hamax _ this) (not_le.mpr hcontra)
        · exact absurd h (hnotp g)
        · right
          refine hcmin (p g) ?_
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, h⟩
    have hcgt := main c hct hnb
    -- but `c` is a breakpoint `≥ b`, so `f(c) < c`
    have : truncSum n v p c < c := by
      simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hcU
      rcases hcU.1 with ⟨g, _, hg⟩ | ⟨g, _, hg⟩
      · rw [← hg]; exact hbv g (by rw [hg]; exact le_trans hcon (le_of_lt hct))
      · rw [← hg]; exact hbp g (by rw [hg]; exact le_trans hcon (le_of_lt hct))
    linarith
  · -- no breakpoint above `t₀`
    rw [Finset.not_nonempty_iff_eq_empty] at hU
    have hle : ∀ g, v g ≤ t₀ ∧ p g ≤ t₀ := by
      intro g
      constructor
      · by_contra hcontra
        push_neg at hcontra
        have : v g ∈ U := by
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, hcontra⟩
        rw [hU] at this; exact absurd this (Finset.notMem_empty _)
      · by_contra hcontra
        push_neg at hcontra
        have : p g ∈ U := by
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, hcontra⟩
        rw [hU] at this; exact absurd this (Finset.notMem_empty _)
    set c := t₀ + 1 with hcdef
    have hct : t₀ < c := by simp [hcdef]
    have hnb : NoBreak v p a c := by
      intro g
      refine ⟨Or.inl ?_, Or.inl ?_⟩
      · by_contra hcontra
        push_neg at hcontra
        have : v g ∈ L := by
          simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          exact ⟨Or.inr ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩,
            lt_of_le_of_ne (hle g).1 (hnotv g)⟩
        exact absurd (hamax _ this) (not_le.mpr hcontra)
      · by_contra hcontra
        push_neg at hcontra
        have : p g ∈ L := by
          simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          exact ⟨Or.inr ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩,
            lt_of_le_of_ne (hle g).2 (hnotp g)⟩
        exact absurd (hamax _ this) (not_le.mpr hcontra)
    have hcgt := main c hct hnb
    -- but `f(c) = f(t₀) = t₀ < c`
    have hfc : truncSum n v p c = t₀ := by
      rw [truncSum_of_ge v p (fun g => le_trans (hle g).1 (le_of_lt hct)),
        ← truncSum_of_ge (n := n) v p (fun g => (hle g).1), hfix]
    rw [hfc] at hcgt
    linarith

/-! ### The case `k > 1`: solving the linear equation on the bracketing interval -/

omit [DecidableEq G] in
/-- **Correctness of the computation of the `TPS`.**  Suppose `[a, c]` contains no
breakpoint in its interior, `f(a) ≥ a`, `f(c) < c`, and `f(s) < s` at every breakpoint
`s ≥ c`.  Then, writing `k` for the number of goods with `v(g) ≥ c` and `p(g) ≤ a` and
`C` for the constant contribution of the remaining goods, we have `k < n` and
`TPS = C/(n − k)`; moreover `a ≤ TPS < c`. -/
theorem TPS_eq_bracket_formula (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {a c : ℝ}
    (hac : a ≤ c) (hnb : NoBreak v p a c)
    (hfa : a ≤ truncSum n v p a) (hfc : truncSum n v p c < c)
    (hbv : ∀ g, c ≤ v g → truncSum n v p (v g) < v g)
    (hbp : ∀ g, c ≤ p g → truncSum n v p (p g) < p g) :
    ((slopeGoods v p a c).card : ℝ) < n ∧
      TPS n v p = flatConst v p a c / (n - ((slopeGoods v p a c).card : ℝ)) ∧
      a ≤ TPS n v p ∧ TPS n v p < c := by
  classical
  have hTPSlt : TPS n v p < c := TPS_lt_of_no_fixed_above v p hn hp hfc hbv hbp
  have hTPSge : a ≤ TPS n v p := le_TPS_of_le_truncSum v p hfa
  have hfix : truncSum n v p (TPS n v p) = TPS n v p := TPS_truncSum v p hp
  set t₀ := TPS n v p with ht₀
  set C := flatConst v p a c with hC
  set k := ((slopeGoods v p a c).card : ℝ) with hk
  have h1 := truncSum_bracket (n := n) v p hnb hTPSge (le_of_lt hTPSlt)
  have h2 := truncSum_bracket (n := n) v p hnb (le_refl a) hac
  have h3 := truncSum_bracket (n := n) v p hnb hac (le_refl c)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [hfix] at h1
  have e1 : C + k * t₀ = n * t₀ := by
    rw [eq_comm, div_eq_iff (ne_of_gt hn')] at h1
    linarith [h1]
  have e3 : C + k * c < n * c := by rw [h3, div_lt_iff₀ hn'] at hfc; linarith
  have hkn : k < n := by nlinarith [hTPSlt, e1, e3]
  refine ⟨hkn, ?_, hTPSge, hTPSlt⟩
  rw [eq_div_iff (by linarith : (n:ℝ) - k ≠ 0)]
  linarith

/-! ### The algorithm, packaged in terms of the breakpoints

The manuscript's algorithm scans the breakpoints `{0} ∪ {v(g)} ∪ {p(g)}` from the top and stops
at the first one, `sₖ`, with `f(sₖ) ≥ sₖ`.  The two corollaries below say exactly what that
stopping point tells us. -/

open Classical in
/-- The breakpoints of the truncated-proportional map: `{0} ∪ {v(g) : g} ∪ {p(g) : g}`. -/
noncomputable def breakpoints (v p : G → ℝ) : Finset ℝ :=
  insert 0 ((Finset.univ.image v) ∪ (Finset.univ.image p))

omit [DecidableEq G] in
lemma vval_mem_breakpoints (v p : G → ℝ) (g : G) : v g ∈ breakpoints v p := by
  classical
  simp only [breakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inl ⟨g, Finset.mem_univ g, rfl⟩)

omit [DecidableEq G] in
lemma price_mem_breakpoints (v p : G → ℝ) (g : G) : p g ∈ breakpoints v p := by
  classical
  simp only [breakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr ⟨g, Finset.mem_univ g, rfl⟩)

omit [DecidableEq G] in
/-- **The algorithm stops at the largest breakpoint** (`k = 1`): then `TPS = PS`. -/
theorem TPS_eq_PS_of_max_breakpoint (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {a : ℝ}
    (hmax : ∀ s ∈ breakpoints v p, s ≤ a) (hfa : a ≤ truncSum n v p a) :
    TPS n v p = PS n v p :=
  TPS_eq_PS_of_top v p hp (fun g => hmax _ (vval_mem_breakpoints v p g)) hfa

omit [DecidableEq G] in
/-- **The algorithm stops below the largest breakpoint** (`k > 1`): the `TPS` lies in the
interval `[a, c)` between the stopping breakpoint `a` and the previous one `c`, and it is the
solution `C/(n − k)` of the linear equation satisfied by `f` there. -/
theorem TPS_of_consecutive_breakpoints (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g)
    {a c : ℝ} (hac : a < c) (hc : c ∈ breakpoints v p)
    (hgap : ∀ s ∈ breakpoints v p, s ≤ a ∨ c ≤ s)
    (hfa : a ≤ truncSum n v p a)
    (habove : ∀ s ∈ breakpoints v p, c ≤ s → truncSum n v p s < s) :
    ((slopeGoods v p a c).card : ℝ) < n ∧
      TPS n v p = flatConst v p a c / (n - ((slopeGoods v p a c).card : ℝ)) ∧
      a ≤ TPS n v p ∧ TPS n v p < c := by
  refine TPS_eq_bracket_formula v p hn hp (le_of_lt hac)
    (fun g => ⟨hgap _ (vval_mem_breakpoints v p g), hgap _ (price_mem_breakpoints v p g)⟩)
    hfa (habove c hc (le_refl c))
    (fun g hg => habove _ (vval_mem_breakpoints v p g) hg)
    (fun g hg => habove _ (price_mem_breakpoints v p g) hg)

end FairSelling
