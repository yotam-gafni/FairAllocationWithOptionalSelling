import Mathlib
import RequestProject.EqualProceeds
import RequestProject.TPSCompute

/-!
# Appendix H, Theorem 7: `1/n`-TPS with equal proceeds

This file formalizes the bag-filling algorithm of Appendix H and its guarantee: for every
instance there is a feasible outcome with **equal proceeds** in which every agent `i` gets
utility at least `(1/n) · TPS_i`, where `TPS_i` is the truncated proportional share of
Definition 3 (defined with *unconstrained* proceeds).

## The quantities of the algorithm

For an agent with valuation `vᵢ`, prices `p` and target `t = TPSᵢ`:

* `effVal vᵢ p t g = max (p g) (min (vᵢ g) t)` is the manuscript's `v'ᵢ(g)`;
* `keepPart` / `sellPart` split a bundle into the goods the agent prefers to keep
  (`p g ≤ min (vᵢ g) t`) and those she prefers to sell;
* `netVal n vᵢ p t g` is the manuscript's `ṽᵢ(g)`: the value the agent actually derives from
  `g` under equal proceeds, namely `min (vᵢ g) t` if she keeps `g` and `p g / n` if she sells
  it (only `1/n` of the proceeds comes back to her).

The defining property of `TPS` used here is `∑_g v'ᵢ(g) = n · TPSᵢ` (`TPS_truncSum`).

## The proof

Instead of running the algorithm as a stateful loop, the argument is packaged as an induction
on the set `T` of agents that are still active (`bagFilling_induction`), carrying the potential

`Φₖ = v'ₖ(R) + n · s   ≥   |T| · TPSₖ`,

where `R` is the set of goods still available and `s` the money each agent holds so far.
The single round (`round_exists`) is the case analysis of the manuscript: sell an expensive
good, hand over a single valuable good, or bag-fill and give the bag to the agent that
generates the most sale proceeds from it.  Each round costs an active agent at most `TPSₖ`
of the potential, which is exactly what the induction needs.
-/

open scoped BigOperators

namespace FairSelling

namespace EqualProceedsBagFilling

variable {G : Type*} {n : ℕ}

/-- The effective value `v'ᵢ(g) = max{min{tᵢ, vᵢ(g)}, p(g)}`. -/
noncomputable def effVal (vi p : G → ℝ) (tk : ℝ) (g : G) : ℝ := max (p g) (min (vi g) tk)

/-- `ṽᵢ(g)`: the value the agent derives from `g` under equal proceeds — she keeps `g` when
`p g ≤ min (vᵢ g) tᵢ`, and otherwise sells it and receives `1/n` of its price. -/
noncomputable def netVal (n : ℕ) (vi p : G → ℝ) (tk : ℝ) (g : G) : ℝ :=
  if p g ≤ min (vi g) tk then min (vi g) tk else p g / n

/-- `∑_{g ∈ B} v'ᵢ(g)`. -/
noncomputable def effSum (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : ℝ :=
  ∑ g ∈ B, effVal vi p tk g

/-- `∑_{g ∈ B} ṽᵢ(g)`. -/
noncomputable def netSum (n : ℕ) (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : ℝ :=
  ∑ g ∈ B, netVal n vi p tk g

/-- `∑_{g ∈ B} p(g)`. -/
def priceSum (p : G → ℝ) (B : Finset G) : ℝ := ∑ g ∈ B, p g

/-- The goods of `B` that the agent prefers to keep. -/
noncomputable def keepPart (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : Finset G :=
  B.filter (fun g => p g ≤ min (vi g) tk)

/-- The goods of `B` that the agent prefers to sell. -/
noncomputable def sellPart (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : Finset G :=
  B.filter (fun g => ¬ p g ≤ min (vi g) tk)

variable {vi p : G → ℝ} {tk : ℝ}

theorem keepPart_subset (B : Finset G) : keepPart vi p tk B ⊆ B := Finset.filter_subset _ _

theorem sellPart_subset (B : Finset G) : sellPart vi p tk B ⊆ B := Finset.filter_subset _ _

theorem keepPart_disjoint_sellPart (B : Finset G) :
    Disjoint (keepPart vi p tk B) (sellPart vi p tk B) := by
  unfold keepPart sellPart
  exact Finset.disjoint_filter_filter_not _ _ _

theorem effVal_nonneg (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ effVal vi p tk g :=
  le_trans (hp g) (le_max_left _ _)

theorem effSum_nonneg (hp : ∀ g, 0 ≤ p g) (B : Finset G) : 0 ≤ effSum vi p tk B :=
  Finset.sum_nonneg fun g _ => effVal_nonneg hp g

theorem priceSum_nonneg (hp : ∀ g, 0 ≤ p g) (B : Finset G) : 0 ≤ priceSum p B :=
  Finset.sum_nonneg fun g _ => hp g

theorem netVal_nonneg (hv : ∀ g, 0 ≤ vi g) (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (g : G) :
    0 ≤ netVal n vi p tk g := by
  unfold netVal
  split
  · exact le_min (hv g) ht
  · exact div_nonneg (hp g) (Nat.cast_nonneg _)

theorem netSum_nonneg (hv : ∀ g, 0 ≤ vi g) (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (B : Finset G) :
    0 ≤ netSum n vi p tk B :=
  Finset.sum_nonneg fun g _ => netVal_nonneg hv hp ht g

/-- `v'ᵢ(g) ≤ p(g) + tᵢ`. -/
theorem effVal_le_add (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (g : G) :
    effVal vi p tk g ≤ p g + tk := by
  unfold effVal
  refine max_le (by linarith) (le_trans (min_le_right _ _) (by linarith [hp g]))

/-- If a good is not more expensive than the target, its effective value is at most the
target. -/
theorem effVal_le_of_price_le (h : p g ≤ tk) : effVal vi p tk g ≤ tk :=
  max_le h (min_le_right _ _)

/-- `v'ᵢ(g) ≤ n · ṽᵢ(g)`. -/
theorem effVal_le_nsmul_netVal (hv : ∀ g, 0 ≤ vi g) (ht : 0 ≤ tk)
    (hn : 0 < n) (g : G) : effVal vi p tk g ≤ (n : ℝ) * netVal n vi p tk g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold effVal netVal
  split
  · rename_i h
    rw [max_eq_right h]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [le_min (hv g) ht]
  · rename_i h
    push_neg at h
    rw [max_eq_left h.le, mul_div_cancel₀ _ (ne_of_gt hn')]

theorem effSum_le_nsmul_netSum (hv : ∀ g, 0 ≤ vi g) (ht : 0 ≤ tk)
    (hn : 0 < n) (B : Finset G) :
    effSum vi p tk B ≤ (n : ℝ) * netSum n vi p tk B := by
  unfold effSum netSum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun g _ => effVal_le_nsmul_netVal hv ht hn g

/-- The effective value of a bundle splits into the effective value of the kept part plus the
price of the sold part. -/
theorem effSum_split (B : Finset G) :
    effSum vi p tk B = effSum vi p tk (keepPart vi p tk B) + priceSum p (sellPart vi p tk B) := by
  unfold effSum priceSum keepPart sellPart
  rw [← Finset.sum_filter_add_sum_filter_not B (fun g => p g ≤ min (vi g) tk)
    (fun g => effVal vi p tk g)]
  congr 1
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := (Finset.mem_filter.mp hg).2
  unfold effVal
  exact max_eq_left (by push_neg at hg'; exact hg'.le)

/-- The net value of a bundle splits into the effective value of the kept part plus `1/n` of the
price of the sold part. -/
theorem netSum_split (B : Finset G) :
    netSum n vi p tk B
      = effSum vi p tk (keepPart vi p tk B) + priceSum p (sellPart vi p tk B) / n := by
  unfold netSum effSum priceSum keepPart sellPart
  rw [← Finset.sum_filter_add_sum_filter_not B (fun g => p g ≤ min (vi g) tk)
    (fun g => netVal n vi p tk g)]
  congr 1
  · refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := (Finset.mem_filter.mp hg).2
    unfold netVal effVal
    rw [if_pos hg', max_eq_right hg']
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := (Finset.mem_filter.mp hg).2
    unfold netVal
    rw [if_neg hg']

/-- On the kept part, the effective value is bounded by the true value. -/
theorem effSum_keepPart_le (B : Finset G) :
    effSum vi p tk (keepPart vi p tk B) ≤ ∑ g ∈ keepPart vi p tk B, vi g := by
  refine Finset.sum_le_sum fun g hg => ?_
  have hg' := (Finset.mem_filter.mp hg).2
  unfold effVal
  exact max_le (le_trans hg' (min_le_left _ _)) (min_le_left _ _)

/-! ## One round of the algorithm -/

section Round

variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)

/-- Filling a bag: from any bundle that already satisfies some active agent one can pass to a
sub-bundle that satisfies some active agent but becomes insufficient for *every* active agent
as soon as one of its goods is removed. -/
theorem exists_minimal_bag (T : Finset (Fin n)) (s : ℝ) : ∀ B : Finset G,
    (∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) B) →
    ∃ B' ⊆ B, (∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) B') ∧
      (∀ e ∈ B', ∀ k ∈ T, netSum n (v k) p (t k) (B' \ {e}) < t k / n - s) := by
  intro B
  induction B using Finset.strongInduction with
  | _ B ih =>
    intro hB
    by_cases hex : ∃ e ∈ B, ∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) (B \ {e})
    · obtain ⟨e, he, hk⟩ := hex
      obtain ⟨B', hB'sub, h1, h2⟩ :=
        ih (B \ {e}) (Finset.sdiff_ssubset (by simpa using he) ⟨e, by simp⟩) hk
      exact ⟨B', hB'sub.trans Finset.sdiff_subset, h1, h2⟩
    · push_neg at hex
      exact ⟨B, Finset.Subset.refl _, hB, fun e he k hk => hex e he k hk⟩

/-- **One round of the bag-filling algorithm.**  If every still-active agent `k ∈ T` has
potential `v'ₖ(R) + n·s ≥ tₖ`, then some active agent `i` can be given a bundle `C` of kept
goods together with a set `D` of goods sold on her behalf so that

* `i` reaches her target: `tᵢ/n ≤ vᵢ(C) + s + p(D)/n`;
* every other active agent loses at most `tₖ` of potential:
  `v'ₖ(C ∪ D) − p(D) ≤ tₖ`. -/
theorem round_exists
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (ht : ∀ i, 0 ≤ t i) (hn : 0 < n)
    (R : Finset G) (s : ℝ) (hs : 0 ≤ s) (T : Finset (Fin n)) (hT : T.Nonempty)
    (hinv : ∀ k ∈ T, t k ≤ effSum (v k) p (t k) R + n * s) :
    ∃ i ∈ T, ∃ C D : Finset G, C ⊆ R ∧ D ⊆ R ∧ Disjoint C D ∧
      t i / n ≤ (∑ g ∈ C, v i g) + s + priceSum p D / n ∧
      (∀ k ∈ T, k ≠ i → effSum (v k) p (t k) (C ∪ D) - priceSum p D ≤ t k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Step 0: an agent that is already satisfied by the money she holds
  by_cases hsat : ∃ i ∈ T, t i / n ≤ s
  · obtain ⟨i, hi, hle⟩ := hsat
    refine ⟨i, hi, ∅, ∅, by simp, by simp, by simp, by simpa [priceSum] using hle, ?_⟩
    intro k hk hne
    simpa [effSum, priceSum] using ht k
  push_neg at hsat
  -- Step 1: a good that is more expensive than some active agent's target
  by_cases hexp : ∃ e ∈ R, ∃ i ∈ T, t i ≤ p e
  · obtain ⟨e, he, i, hi, hle⟩ := hexp
    refine ⟨i, hi, ∅, {e}, by simp, by simpa using he, by simp, ?_, ?_⟩
    · have hdiv : t i / n ≤ p e / n := by gcongr
      simpa [priceSum] using by linarith
    · intro k hk hne
      have hb := effVal_le_add (vi := v k) hp (ht k) e
      simp only [effSum, priceSum, Finset.empty_union, Finset.sum_singleton]
      linarith
  push_neg at hexp
  -- Step 2: a good that is valuable enough for some active agent
  by_cases hval : ∃ e ∈ R, ∃ i ∈ T, t i / n - s ≤ v i e
  · obtain ⟨e, he, i, hi, hle⟩ := hval
    refine ⟨i, hi, {e}, ∅, by simpa using he, by simp, by simp, ?_, ?_⟩
    · simp only [priceSum, Finset.sum_empty, Finset.sum_singleton, zero_div]
      linarith
    · intro k hk hne
      simp only [effSum, priceSum, Finset.union_empty, Finset.sum_singleton, Finset.sum_empty,
        sub_zero]
      exact effVal_le_of_price_le (hexp e he k hk).le
  push_neg at hval
  -- Step 3: bag filling
  have hRsat : ∀ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) R := by
    intro k hk
    have h1 := hinv k hk
    have h2 := effSum_le_nsmul_netSum (vi := v k) (p := p) (hv k) (ht k) hn R
    rw [sub_le_iff_le_add, div_le_iff₀ hn']
    nlinarith
  obtain ⟨k1, hk1⟩ := hT
  obtain ⟨B, hBR, hBsat, hBmin⟩ :=
    exists_minimal_bag v p t T s R ⟨k1, hk1, hRsat k1 hk1⟩
  obtain ⟨k0, hk0T, hk0⟩ := hBsat
  -- the bag is nonempty
  have hBne : B.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B with hemp | hne
    · exfalso
      have h0 : netSum n (v k0) p (t k0) B = 0 := by simp [hemp, netSum]
      have := hsat k0 hk0T
      rw [h0] at hk0
      linarith
    · exact hne
  obtain ⟨e, heB⟩ := hBne
  have heR : e ∈ R := hBR heB
  -- the agents that the bag satisfies, and the winner among them
  classical
  obtain ⟨i, hiW, hmax⟩ :=
    Finset.exists_max_image (T.filter (fun k => t k / n - s ≤ netSum n (v k) p (t k) B))
      (fun k => priceSum p (sellPart (v k) p (t k) B))
      ⟨k0, Finset.mem_filter.mpr ⟨hk0T, hk0⟩⟩
  have hiT : i ∈ T := (Finset.mem_filter.mp hiW).1
  have hiB : t i / n - s ≤ netSum n (v i) p (t i) B := (Finset.mem_filter.mp hiW).2
  refine ⟨i, hiT, keepPart (v i) p (t i) B, sellPart (v i) p (t i) B,
    (keepPart_subset B).trans hBR, (sellPart_subset B).trans hBR,
    keepPart_disjoint_sellPart B, ?_, ?_⟩
  · -- the winner reaches her target
    have hsplit := netSum_split (n := n) (vi := v i) (p := p) (tk := t i) B
    have hkeep := effSum_keepPart_le (vi := v i) (p := p) (tk := t i) B
    rw [hsplit] at hiB
    linarith
  · -- every other active agent loses at most `t k` of potential
    intro k hk hne
    have hunion : keepPart (v i) p (t i) B ∪ sellPart (v i) p (t i) B = B :=
      Finset.filter_union_filter_not_eq _ _
    rw [hunion]
    set a : ℝ := effSum (v k) p (t k) (keepPart (v k) p (t k) B) with ha
    set b : ℝ := priceSum p (sellPart (v k) p (t k) B) with hb
    set d : ℝ := priceSum p (sellPart (v i) p (t i) B) with hd
    have hsplitE : effSum (v k) p (t k) B = a + b := effSum_split B
    have hsplitN : netSum n (v k) p (t k) B = a + b / n := netSum_split B
    have ha0 : 0 ≤ a := effSum_nonneg hp _
    have hb0 : 0 ≤ b := priceSum_nonneg hp _
    have hd0 : 0 ≤ d := priceSum_nonneg hp _
    rw [hsplitE]
    rcases le_or_gt b d with hbd | hbd
    · -- the winner generates at least as much money from the bag as `k` would
      -- so `k` is compensated; the bag is worth less than `2 tₖ/n` to her
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
        have hik : (i : ℕ) ≠ (k : ℕ) := fun h => hne (Fin.ext h).symm
        have h1 := i.isLt
        have h2 := k.isLt
        have : 2 ≤ n := by omega
        exact_mod_cast this
      have hremove : netSum n (v k) p (t k) B
          = netSum n (v k) p (t k) (B \ {e}) + netVal n (v k) p (t k) e := by
        unfold netSum
        rw [Finset.sum_sdiff_eq_sub (by simpa using heB)]
        simp
      have hlast : netVal n (v k) p (t k) e ≤ t k / n := by
        unfold netVal
        split
        · rename_i hkeep'
          have h1 := hval e heR k hk
          have h2 : min (v k e) (t k) ≤ v k e := min_le_left _ _
          have h3 : (0:ℝ) ≤ s := hs
          linarith
        · have := hexp e heR k hk
          gcongr
      have hprev := hBmin e heB k hk
      have hlt : netSum n (v k) p (t k) B < (t k / n - s) + t k / n := by
        rw [hremove]; linarith
      have hhalf : (t k / n) + (t k / n) ≤ t k := by
        rw [← add_div, div_le_iff₀ hn']
        nlinarith [ht k]
      have hbn : 0 ≤ b / n := by positivity
      linarith
    · -- the winner generates less money, so `k` did not qualify for the bag
      have hkW : k ∉ T.filter (fun k => t k / n - s ≤ netSum n (v k) p (t k) B) := by
        intro hkW
        have := hmax k hkW
        simp only [hb, hd] at hbd
        linarith
      have hknot : netSum n (v k) p (t k) B < t k / n - s := by
        by_contra hcon
        push_neg at hcon
        exact hkW (Finset.mem_filter.mpr ⟨hk, hcon⟩)
      rw [hsplitN] at hknot
      have hmul : (n : ℝ) * a + b < t k - (n : ℝ) * s := by
        have h := mul_lt_mul_of_pos_left hknot hn'
        have e1 : (n : ℝ) * (a + b / n) = (n : ℝ) * a + b := by field_simp
        have e2 : (n : ℝ) * (t k / n - s) = t k - (n : ℝ) * s := by field_simp
        rw [e1, e2] at h
        exact h
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (n : ℝ) - 1) ha0]

end Round

/-! ## The induction over active agents, and Theorem 7 -/

section Main

variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)

/-- **The bag-filling algorithm.**  If every agent `k` of the active set `T` has potential
`v'ₖ(R) + n·s ≥ |T| · tₖ`, then the remaining goods `R` can be distributed (some kept by the
agents, some sold with the proceeds shared equally) so that every active agent ends with
`tₖ/n`. -/
theorem bagFilling_induction
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (ht : ∀ i, 0 ≤ t i) (hn : 0 < n) :
    ∀ (T : Finset (Fin n)) (R : Finset G) (s : ℝ), 0 ≤ s →
      (∀ k ∈ T, (T.card : ℝ) * t k ≤ effSum (v k) p (t k) R + n * s) →
      ∃ (C : Fin n → Finset G) (D : Finset G),
        (∀ k, C k ⊆ R) ∧ D ⊆ R ∧
        (∀ j k, j ≠ k → Disjoint (C j) (C k)) ∧ (∀ k, Disjoint (C k) D) ∧
        ∀ k ∈ T, t k / n ≤ (∑ g ∈ C k, v k g) + s + priceSum p D / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro R s hs hinv
    rcases Finset.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _ => ∅, ∅, by simp, by simp, by simp, by simp, by simp⟩
    · have hcard1 : (1 : ℝ) ≤ (T.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hT
      have hinv' : ∀ k ∈ T, t k ≤ effSum (v k) p (t k) R + (n : ℝ) * s := by
        intro k hk
        have h := hinv k hk
        nlinarith [ht k]
      obtain ⟨i, hiT, C0, D0, hC0R, hD0R, hdisj0, hisat, hloss⟩ :=
        round_exists v p t hv hp ht hn R s hs T hT hinv'
      have hsubR : C0 ∪ D0 ⊆ R := Finset.union_subset hC0R hD0R
      have hdisjR : Disjoint (R \ (C0 ∪ D0)) (C0 ∪ D0) := Finset.sdiff_disjoint
      have hpD0 : 0 ≤ priceSum p D0 := priceSum_nonneg hp _
      have hs' : (0 : ℝ) ≤ s + priceSum p D0 / n := by positivity
      have hinv2 : ∀ k ∈ T.erase i,
          (((T.erase i).card : ℝ)) * t k
            ≤ effSum (v k) p (t k) (R \ (C0 ∪ D0)) + (n : ℝ) * (s + priceSum p D0 / n) := by
        intro k hk
        have hkT : k ∈ T := Finset.mem_of_mem_erase hk
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        have hsplit : effSum (v k) p (t k) (R \ (C0 ∪ D0))
            = effSum (v k) p (t k) R - effSum (v k) p (t k) (C0 ∪ D0) := by
          unfold effSum
          exact Finset.sum_sdiff_eq_sub hsubR
        have hcard : ((T.erase i).card : ℝ) = (T.card : ℝ) - 1 := by
          rw [Finset.card_erase_of_mem hiT]
          have : 1 ≤ T.card := Finset.card_pos.mpr hT
          push_cast [Nat.cast_sub this]
          ring
        have hmoney : (n : ℝ) * (s + priceSum p D0 / n)
            = (n : ℝ) * s + priceSum p D0 := by
          field_simp
        have hl := hloss k hkT hki
        have h := hinv k hkT
        rw [hsplit, hcard, hmoney]
        nlinarith
      obtain ⟨C1, D1, hC1R, hD1R, hC1disj, hC1D1, hsat1⟩ :=
        ih (T.erase i) (Finset.erase_ssubset hiT) (R \ (C0 ∪ D0)) (s + priceSum p D0 / n) hs'
          hinv2
      have hR'sub : R \ (C0 ∪ D0) ⊆ R := Finset.sdiff_subset
      have hC1disjC0 : ∀ k, Disjoint (C1 k) C0 := fun k =>
        (hdisjR.mono (hC1R k) Finset.subset_union_left)
      have hC1disjD0 : ∀ k, Disjoint (C1 k) D0 := fun k =>
        (hdisjR.mono (hC1R k) Finset.subset_union_right)
      have hD1disjC0 : Disjoint D1 C0 := hdisjR.mono hD1R Finset.subset_union_left
      have hD1disjD0 : Disjoint D1 D0 := hdisjR.mono hD1R Finset.subset_union_right
      have hpD : priceSum p (D0 ∪ D1) = priceSum p D0 + priceSum p D1 := by
        unfold priceSum
        exact Finset.sum_union hD1disjD0.symm
      have hpD1 : 0 ≤ priceSum p D1 := priceSum_nonneg hp _
      refine ⟨Function.update C1 i C0, D0 ∪ D1, ?_, ?_, ?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = i
        · subst hk
          simp only [Function.update_self]
          exact hC0R
        · simp only [Function.update_of_ne hk]
          exact (hC1R k).trans hR'sub
      · exact Finset.union_subset hD0R (hD1R.trans hR'sub)
      · intro j k hjk
        by_cases hj : j = i
        · subst hj
          have hk : k ≠ j := fun h => hjk h.symm
          simp only [Function.update_of_ne hk, Function.update_self]
          exact (hC1disjC0 k).symm
        · by_cases hk : k = i
          · subst hk
            simp only [Function.update_of_ne hj, Function.update_self]
            exact hC1disjC0 j
          · simp only [Function.update_of_ne hj, Function.update_of_ne hk]
            exact hC1disj j k hjk
      · intro k
        by_cases hk : k = i
        · subst hk
          simp only [Function.update_self]
          exact Finset.disjoint_union_right.mpr ⟨hdisj0, hD1disjC0.symm⟩
        · simp only [Function.update_of_ne hk]
          exact Finset.disjoint_union_right.mpr ⟨hC1disjD0 k, hC1D1 k⟩
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp only [Function.update_self, hpD]
          have : priceSum p D1 / n ≥ 0 := by positivity
          rw [add_div]
          linarith
        · have hke : k ∈ T.erase i := Finset.mem_erase.mpr ⟨hki, hk⟩
          have := hsat1 k hke
          simp only [Function.update_of_ne hki, hpD]
          rw [add_div]
          linarith

end Main

section Theorem7

variable [Fintype G] [DecidableEq G]

/-- **Theorem 7 of Appendix H.**  Every instance admits a feasible outcome with *equal
proceeds* in which every agent `i` receives at least `(1/n) · TPSᵢ`, where `TPSᵢ` is the
truncated proportional share of Definition 3 (with unconstrained proceeds). -/
theorem exists_equalProceeds_TPS_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, TPS n (v i) p / n ≤ util (v i) o i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set t : Fin n → ℝ := fun i => TPS n (v i) p with htdef
  have ht : ∀ i, 0 ≤ t i := fun i => TPS_nonneg (v i) p hp
  have hfix : ∀ i, effSum (v i) p (t i) Finset.univ = (n : ℝ) * t i := by
    intro i
    have h := TPS_truncSum (n := n) (v i) p hp
    unfold truncSum at h
    unfold effSum effVal
    rw [div_eq_iff (ne_of_gt hn')] at h
    rw [h]
    ring
  obtain ⟨C, D, hCR, hDR, hCdisj, hCD, hsat⟩ :=
    bagFilling_induction v p t hv hp ht hn Finset.univ Finset.univ 0 le_rfl (by
      intro k _
      rw [hfix k, Finset.card_univ, Fintype.card_fin]
      simp)
  refine ⟨⟨D, C, fun _ => priceSum p D / n⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun j => (hCD j).symm
  · exact hCdisj
  · intro j
    have := priceSum_nonneg hp D
    positivity
  · have : ∑ _j : Fin n, priceSum p D / n = priceSum p D := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ (ne_of_gt hn')]
    simpa [priceSum] using this.le
  · intro i
    simp [priceSum]
  · intro i
    have h := hsat i (Finset.mem_univ i)
    have ht' : t i = TPS n (v i) p := rfl
    rw [ht'] at h
    simp only [util]
    linarith

/-- Since `MMSᵢ ≤ TPSᵢ` (Lemma 1), the same outcome guarantees `(1/n)·MMSᵢ` — where `MMSᵢ` is
the *unconstrained* maximin share — to every agent. -/
theorem exists_equalProceeds_MMS_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, MMS n (v i) p / n ≤ util (v i) o i := by
  obtain ⟨o, hvalid, hep, hsat⟩ := exists_equalProceeds_TPS_approx v p hn hv hp
  refine ⟨o, hvalid, hep, fun i => le_trans ?_ (hsat i)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  gcongr
  exact MMS_le_TPS (v i) p hn (hv i) hp

/-- A fortiori, every agent gets at least `(1/n)` of her *equal-proceeds* maximin share; by
Example 4 this factor `1/n` cannot be improved. -/
theorem exists_equalProceeds_MMSEP_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, MMSEP n (v i) p / n ≤ util (v i) o i := by
  obtain ⟨o, hvalid, hep, hsat⟩ := exists_equalProceeds_MMS_approx v p hn hv hp
  refine ⟨o, hvalid, hep, fun i => le_trans ?_ (hsat i)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  gcongr
  exact MMSEP_le_MMS (v i) p hn (hv i) hp

/-- The same conclusion with a **full** allocation: every good is either sold or allocated, and
the distributed proceeds equal the proceeds of the sold goods (equation (3) of the model).
Leftover goods are simply handed to the first agent, which only increases her utility. -/
theorem exists_equalProceeds_TPS_approx_full (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ ∧
      (∑ j, o.money j) = ∑ g ∈ o.sold, p g ∧
      ∀ i, TPS n (v i) p / n ≤ util (v i) o i := by
  classical
  obtain ⟨o, hvalid, hep, hsat⟩ := exists_equalProceeds_TPS_approx v p hn hv hp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set L : Finset G := Finset.univ \ (o.sold ∪ Finset.univ.biUnion o.kept) with hL
  set kept' : Fin n → Finset G := Function.update o.kept i0 (o.kept i0 ∪ L) with hkept'
  have hLsold : Disjoint L o.sold :=
    Finset.disjoint_left.mpr fun g hg hg' =>
      (Finset.mem_sdiff.mp hg).2 (Finset.mem_union_left _ hg')
  have hLkept : ∀ k, Disjoint L (o.kept k) := fun k =>
    Finset.disjoint_left.mpr fun g hg hg' =>
      (Finset.mem_sdiff.mp hg).2
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hg'⟩))
  have hkeptsub : ∀ k, o.kept k ⊆ kept' k := by
    intro k
    by_cases hk : k = i0
    · subst hk
      simp only [hkept', Function.update_self]
      exact Finset.subset_union_left
    · simp only [hkept', Function.update_of_ne hk]
      exact Finset.Subset.refl _
  have hmem : ∀ k g, g ∈ kept' k → g ∈ o.kept k ∨ g ∈ L := by
    intro k g hg
    by_cases hk : k = i0
    · subst hk
      simp only [hkept', Function.update_self] at hg
      exact Finset.mem_union.mp hg
    · simp only [hkept', Function.update_of_ne hk] at hg
      exact Or.inl hg
  refine ⟨⟨o.sold, kept', o.money⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Finset.disjoint_left.mpr fun g hg hg' => ?_
    rcases hmem j g hg' with h | h
    · exact Finset.disjoint_left.mp (hvalid.1 j) hg h
    · exact Finset.disjoint_left.mp hLsold h hg
  · intro j k hjk
    refine Finset.disjoint_left.mpr fun g hg hg' => ?_
    rcases hmem j g hg with h | h <;> rcases hmem k g hg' with h' | h'
    · exact Finset.disjoint_left.mp (hvalid.2.1 j k hjk) h h'
    · exact Finset.disjoint_left.mp (hLkept j) h' h
    · exact Finset.disjoint_left.mp (hLkept k) h h'
    · -- `g` cannot lie in `L` twice in disjoint bundles; here both bundles contain `L`
      -- which forces `j = k`, contradicting `hjk`
      exfalso
      by_cases hj : j = i0
      · by_cases hk : k = i0
        · exact hjk (hj.trans hk.symm)
        · simp only [hkept', Function.update_of_ne hk] at hg'
          exact Finset.disjoint_left.mp (hLkept k) h' hg'
      · simp only [hkept', Function.update_of_ne hj] at hg
        exact Finset.disjoint_left.mp (hLkept j) h hg
  · exact hvalid.2.2.1
  · exact hvalid.2.2.2
  · exact hep
  · -- every good is sold or allocated
    refine Finset.eq_univ_iff_forall.mpr fun g => ?_
    by_cases hg : g ∈ o.sold ∪ Finset.univ.biUnion o.kept
    · rcases Finset.mem_union.mp hg with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
          hkeptsub k hk⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, ?_⟩)
      simp only [hkept', Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hg⟩)
  · -- the distributed proceeds are exactly the proceeds of the sold goods
    have h : ∀ j, o.money j = (∑ g ∈ o.sold, p g) / n := hep
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hn')]
  · intro i
    refine le_trans (hsat i) ?_
    unfold util
    have : ∑ g ∈ o.kept i, v i g ≤ ∑ g ∈ kept' i, v i g :=
      Finset.sum_le_sum_of_subset_of_nonneg (hkeptsub i) fun g _ _ => hv i g
    simpa using this

end Theorem7


/-! ## A remark on the manuscript's proof of Theorem 7

The write-up of the proof states, for the bag `B` handed to agent `i` in a bag-filling round
and any other active agent `k`, that "`v'ₖ(B) ≤ (2/n)·TPSₖ`, as otherwise `k` would have taken
`B` one step earlier".  What the stopping rule of the round actually gives is the same bound
for the *net* value `ṽₖ(B)` (that is what the agents declare), and the two differ by the factor
`n` on the goods `k` would sell.  The bound as literally stated is false; the instance below
exhibits a bag consisting of a single good for which none of the three rules fires for `k` —
so `k` would indeed not have taken it earlier — yet `v'ₖ(B) > (2/n)·TPSₖ`.

This is why the induction here carries the potential `v'ₖ(R) + n·s` and charges each round the
loss `v'ₖ(B) − p(D)`, where `p(D)` is the money the winner's sales return to `k`: with that
bookkeeping each round costs an active agent at most `TPSₖ`, which is what the argument needs.
-/

section Remark

/-- For a valuation that is identically zero, the truncated proportional share is just the
average price. -/
theorem TPS_of_zero_val [Fintype G] (p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n (fun _ => (0 : ℝ)) p = (∑ g, p g) / n := by
  have hval : ∀ x : ℝ, truncSum n (fun _ => (0 : ℝ)) p x = (∑ g, p g) / n := by
    intro x
    unfold truncSum
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rcases le_or_gt 0 x with hx | hx
    · rw [min_eq_left hx, max_eq_left (hp g)]
    · rw [min_eq_right hx.le, max_eq_left (le_trans hx.le (hp g))]
  have hset : TPSset n (fun _ => (0 : ℝ)) p = Set.Iic ((∑ g, p g) / n) := by
    ext x
    simp [TPSset, hval x]
  rw [TPS, hset, csSup_Iic]

/-- The instance: ten agents, ten goods that are worthless to the agent, nine of price `1` and
one of price `9/10`. -/
noncomputable def remarkPrice : Fin 10 → ℝ := fun g => if g = 0 then 9 / 10 else 1

theorem remarkPrice_nonneg : ∀ g, 0 ≤ remarkPrice g := by
  intro g; unfold remarkPrice; split <;> norm_num

theorem remarkTPS : TPS 10 (fun _ => (0 : ℝ)) remarkPrice = 99 / 100 := by
  rw [TPS_of_zero_val remarkPrice remarkPrice_nonneg]
  norm_num [remarkPrice, Fin.sum_univ_succ]

/-- **The manuscript's intermediate bound `v'ₖ(B) ≤ (2/n)·TPSₖ` is false as stated.**  In the
instance above, the single-good bag `B = {g₀}` is one that a round can produce: the good is
cheaper than the agent's `TPS` (rule 1 does not fire), it is worth less to her than
`TPSₖ/n` (rule 2 does not fire), and its net value `ṽₖ(B)` is below `TPSₖ/n`, so she does not
claim the bag.  Nevertheless `v'ₖ(B) = 9/10` exceeds `(2/10)·TPSₖ = 99/500`.  The bound is
correct for the net value `ṽₖ(B)`, which is what the stopping rule controls. -/
theorem effSum_gt_two_div_n_of_netSum_lt :
    ∃ (val pr : Fin 10 → ℝ) (e : Fin 10) (t : ℝ),
      (∀ g, 0 ≤ val g) ∧ (∀ g, 0 ≤ pr g) ∧ t = TPS 10 val pr ∧
      pr e < t ∧ val e < t / 10 ∧
      netSum 10 val pr t {e} < t / 10 ∧
      (2 / 10) * t < effSum val pr t {e} := by
  refine ⟨fun _ => 0, remarkPrice, 0, 99 / 100, fun _ => le_rfl, remarkPrice_nonneg,
    remarkTPS.symm, ?_, ?_, ?_, ?_⟩
  · norm_num [remarkPrice]
  · norm_num
  · rw [netSum, Finset.sum_singleton, netVal]
    norm_num [remarkPrice]
  · rw [effSum, Finset.sum_singleton, effVal]
    norm_num [remarkPrice]

end Remark

end EqualProceedsBagFilling

end FairSelling
