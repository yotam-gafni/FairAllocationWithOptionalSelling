import Mathlib
import RequestProject.EqualProceeds

/-!
# Appendix H: Examples 3 and 4

Two instances showing how bad the equal-proceeds restriction is.

* **Example 3** (`EqualProceedsExampleThree`): `m = n` goods, `n - 1` of them worth `1` to the
  agent and unsellable, and one worthless good with market price `1`.  The unconstrained
  maximin share is `1` while the equal-proceeds maximin share is only `1/n`
  (`MMSEP_eq`, `MMS_eq`, `MMSEP_eq_MMS_div`).

* **Example 4** (`EqualProceedsExampleFour`): `m = n` goods, all with market price `1`;
  agent `1` values each good at `1/L` and all other agents value each good at `L`.  The
  equal-proceeds maximin shares are `1` for agent `1` and `L` for the others, and no valid
  equal-proceeds outcome gives every agent more than roughly `1/n` of her equal-proceeds
  maximin share (`no_better_than_one_over_n`).

Both statements are for `n ≥ 1` (resp. `n ≥ 2`) agents, encoded as `Fin (N+1)` (resp.
`Fin (N+2)`); goods are indexed by the same type as the agents.
-/

open scoped BigOperators

namespace FairSelling

/-! ## A pigeonhole lemma used by both examples -/

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

omit [Fintype G] in
/-- Pigeonhole: if the kept bundles of an outcome are pairwise disjoint and, outside of `E`,
are contained in a set `R` of fewer goods than there are agents in `T`, then some agent of `T`
keeps nothing outside `E`. -/
theorem exists_kept_subset (o : Outcome G n) (E R : Finset G) (T : Finset (Fin n))
    (hdisj : ∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k))
    (hsub : ∀ j, o.kept j \ E ⊆ R)
    (hcard : R.card < T.card) :
    ∃ j ∈ T, o.kept j ⊆ E := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ j ∈ T, (o.kept j \ E).Nonempty := by
    intro j hj
    obtain ⟨g, hg, hgE⟩ := Finset.not_subset.mp (hcon j hj)
    exact ⟨g, Finset.mem_sdiff.mpr ⟨hg, hgE⟩⟩
  have hbi : (T.biUnion fun j => o.kept j \ E).card = ∑ j ∈ T, (o.kept j \ E).card := by
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    exact (hdisj x y hxy).mono Finset.sdiff_subset Finset.sdiff_subset
  have hsub' : (T.biUnion fun j => o.kept j \ E) ⊆ R := by
    intro g hg
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hg
    exact hsub j hj
  have h1 : T.card ≤ ∑ j ∈ T, (o.kept j \ E).card := by
    calc T.card = ∑ _j ∈ T, 1 := by simp
    _ ≤ ∑ j ∈ T, (o.kept j \ E).card :=
        Finset.sum_le_sum fun j hj => Finset.card_pos.mpr (hne j hj)
  have h2 := Finset.card_le_card hsub'
  omega

/-! ## Example 3 -/

namespace EqualProceedsExampleThree

variable (N : ℕ)

/-- The agent's valuation: the good `0` is worthless, all others are worth `1`. -/
def val : Fin (N + 1) → ℝ := fun g => if g = 0 then 0 else 1

/-- The market prices: only the worthless good `0` can be sold, for `1`. -/
def price : Fin (N + 1) → ℝ := fun g => if g = 0 then 1 else 0

/-- The bundles: agent `j ≠ 0` keeps the good `j`, agent `0` keeps nothing. -/
def keptFun : Fin (N + 1) → Finset (Fin (N + 1)) := fun j => if j = 0 then ∅ else {j}

theorem val_nonneg : ∀ g, 0 ≤ val N g := by
  intro g; unfold val; split <;> norm_num

theorem price_nonneg : ∀ g, 0 ≤ price N g := by
  intro g; unfold price; split <;> norm_num

theorem max_price_val (g : Fin (N + 1)) : max (price N g) (val N g) = 1 := by
  unfold price val; split <;> norm_num

theorem price_sold : ∑ g ∈ ({0} : Finset (Fin (N + 1))), price N g = 1 := by
  simp [price]

theorem keptFun_disj (j k : Fin (N + 1)) (hjk : j ≠ k) :
    Disjoint (keptFun N j) (keptFun N k) := by
  unfold keptFun
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk, hjk]

theorem sold_keptFun_disj (j : Fin (N + 1)) :
    Disjoint ({0} : Finset (Fin (N + 1))) (keptFun N j) := by
  unfold keptFun
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj, Ne.symm hj]

theorem PS_eq : PS (N + 1) (val N) (price N) = 1 := by
  unfold PS
  rw [Finset.sum_congr rfl fun g _ => max_price_val N g, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (by positivity)

/-- The outcome realizing the unconstrained maximin share `1`: sell good `0`, give its proceeds
to agent `0`, and give good `j` to agent `j` for `j ≠ 0`. -/
def out1 : Outcome (Fin (N + 1)) (N + 1) where
  sold := {0}
  kept := keptFun N
  money := fun j => if j = 0 then 1 else 0

/-- The outcome realizing the equal-proceeds maximin share `1/(N+1)`: as `out1`, but the
proceeds of good `0` are split equally. -/
noncomputable def out2 : Outcome (Fin (N + 1)) (N + 1) where
  sold := {0}
  kept := keptFun N
  money := fun _ => 1 / ((N : ℝ) + 1)

theorem out1_valid : (out1 N).Valid (price N) := by
  refine ⟨sold_keptFun_disj N, keptFun_disj N, ?_, ?_⟩
  · intro j; simp only [out1]; split <;> norm_num
  · simp only [out1, price_sold]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1)) (fun _ => (1 : ℝ))]
    simp

theorem out2_valid : (out2 N).Valid (price N) := by
  refine ⟨sold_keptFun_disj N, keptFun_disj N, ?_, ?_⟩
  · intro j; simp only [out2]; positivity
  · simp only [out2, price_sold]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_one_div, div_self (by positivity)]

theorem out2_equalProceeds : (out2 N).EqualProceeds (price N) := by
  intro i
  simp only [out2, price_sold]
  push_cast
  ring

theorem util_out1 (j : Fin (N + 1)) : util (val N) (out1 N) j = 1 := by
  unfold util out1 keptFun
  by_cases hj : j = 0 <;> simp [hj, val]

theorem util_out2 (j : Fin (N + 1)) : (1 : ℝ) / ((N : ℝ) + 1) ≤ util (val N) (out2 N) j := by
  unfold util out2 keptFun
  by_cases hj : j = 0
  · simp [hj]
  · have hv : val N j = 1 := by simp [val, hj]
    simp only [hj, if_false, Finset.sum_singleton, hv]
    linarith

/-- **The unconstrained maximin share of Example 3 is `1`.** -/
theorem MMS_eq : MMS (N + 1) (val N) (price N) = 1 := by
  apply le_antisymm
  · refine csSup_le (MMSset_nonempty _ _) fun r hr => ?_
    have := MMSset_le_PS (val N) (price N) (Nat.succ_pos N) (val_nonneg N) (price_nonneg N) hr
    rwa [PS_eq] at this
  · refine le_csSup (MMSset_bddAbove _ _ (Nat.succ_pos N) (val_nonneg N) (price_nonneg N)) ?_
    exact ⟨out1 N, out1_valid N, fun j => (util_out1 N j).ge⟩

/-- **The equal-proceeds maximin share of Example 3 is `1/n`.** -/
theorem MMSEP_eq : MMSEP (N + 1) (val N) (price N) = 1 / ((N : ℝ) + 1) := by
  apply le_antisymm
  · refine MMSEP_le _ _ fun r hr => ?_
    obtain ⟨o, hvalid, hep, hguar⟩ := hr
    have hcard : ((Finset.univ : Finset (Fin (N + 1))) \ {(0 : Fin (N + 1))}).card
        < (Finset.univ : Finset (Fin (N + 1))).card := by
      have h : ((Finset.univ : Finset (Fin (N + 1))) \ {(0 : Fin (N + 1))}).card = N := by
        rw [Finset.card_sdiff]
        simp
      simp only [Finset.card_univ, Fintype.card_fin, h]
      omega
    obtain ⟨j, -, hj⟩ := exists_kept_subset o {(0 : Fin (N + 1))}
      ((Finset.univ : Finset (Fin (N + 1))) \ {(0 : Fin (N + 1))}) Finset.univ hvalid.2.1
      (fun j => Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)) hcard
    have hvj : ∑ g ∈ o.kept j, val N g = 0 := by
      refine Finset.sum_eq_zero fun g hg => ?_
      have hg0 : g = 0 := Finset.mem_singleton.mp (hj hg)
      simp [val, hg0]
    have hle : ∑ g ∈ o.sold, price N g ≤ 1 := by
      calc ∑ g ∈ o.sold, price N g
          ≤ ∑ g : Fin (N + 1), price N g :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun g _ _ => price_nonneg N g)
        _ = 1 := by simp [price]
    have hmoney : o.money j ≤ 1 / ((N : ℝ) + 1) := by
      rw [hep j]
      have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      gcongr
    have hg := hguar j
    unfold util at hg
    rw [hvj] at hg
    linarith
  · refine le_MMSEP _ _ (Nat.succ_pos N) (val_nonneg N) (price_nonneg N) ?_
    exact ⟨out2 N, out2_valid N, out2_equalProceeds N, fun j => util_out2 N j⟩

/-- **Example 3**: the equal-proceeds maximin share is `1/n` times the unconstrained maximin
share. -/
theorem MMSEP_eq_MMS_div :
    MMSEP (N + 1) (val N) (price N) = MMS (N + 1) (val N) (price N) / ((N : ℝ) + 1) := by
  rw [MMSEP_eq, MMS_eq]

end EqualProceedsExampleThree

/-! ## Example 4 -/

namespace EqualProceedsExampleFour

variable (N : ℕ)

/-- Every good has market price `1`. -/
def price : Fin (N + 2) → ℝ := fun _ => 1

/-- Agent `0` values every good at `1/L`, every other agent values every good at `L`. -/
noncomputable def val (L : ℝ) (i : Fin (N + 2)) : Fin (N + 2) → ℝ :=
  fun _ => if i = 0 then 1 / L else L

theorem price_nonneg : ∀ g, 0 ≤ price N g := fun _ => zero_le_one

theorem price_sum_univ : ∑ g : Fin (N + 2), price N g = ((N : ℝ) + 2) := by
  simp [price]

theorem price_sum (S : Finset (Fin (N + 2))) : ∑ g ∈ S, price N g = (S.card : ℝ) := by
  simp [price]

/-- Selling all the goods: with equal proceeds each agent receives `1`. -/
def outSellAll : Outcome (Fin (N + 2)) (N + 2) where
  sold := Finset.univ
  kept := fun _ => ∅
  money := fun _ => 1

/-- Keeping all the goods, one per agent. -/
def outKeepAll : Outcome (Fin (N + 2)) (N + 2) where
  sold := ∅
  kept := fun j => {j}
  money := fun _ => 0

theorem outSellAll_valid : (outSellAll N).Valid (price N) := by
  refine ⟨fun j => by simp [outSellAll], fun j k _ => by simp [outSellAll], fun j => by
    simp [outSellAll], ?_⟩
  simp only [outSellAll]
  rw [price_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

theorem outSellAll_equalProceeds : (outSellAll N).EqualProceeds (price N) := by
  intro i
  simp only [outSellAll]
  rw [price_sum, Finset.card_univ, Fintype.card_fin, div_self (by positivity)]

theorem outKeepAll_valid : (outKeepAll N).Valid (price N) := by
  refine ⟨fun j => by simp [outKeepAll], fun j k hjk => by simp [outKeepAll, hjk],
    fun j => by simp [outKeepAll], by simp [outKeepAll]⟩

theorem outKeepAll_equalProceeds : (outKeepAll N).EqualProceeds (price N) := by
  intro i
  simp [outKeepAll]

/-- For a constant valuation `c` and unit prices, the equal-proceeds maximin share is
`max 1 c`: the agent either keeps one good per bundle, or sells everything and splits the
proceeds. -/
theorem MMSEP_const (c : ℝ) (hc : 0 ≤ c) :
    MMSEP (N + 2) (fun _ => c) (price N) = max 1 c := by
  have hn : 0 < N + 2 := by omega
  have hv : ∀ g : Fin (N + 2), (0 : ℝ) ≤ c := fun _ => hc
  apply le_antisymm
  · have hPS : PS (N + 2) (fun _ => c) (price N) = max 1 c := by
      have hsum : ∑ g : Fin (N + 2), max (price N g) c = ((N : ℝ) + 2) * max 1 c := by
        simp [price]
      unfold PS
      rw [hsum]
      push_cast
      rw [mul_comm, mul_div_assoc, div_self (by positivity), mul_one]
    calc MMSEP (N + 2) (fun _ => c) (price N)
        ≤ PS (N + 2) (fun _ => c) (price N) :=
          MMSEP_le_PS _ _ hn hv (price_nonneg N)
      _ = max 1 c := hPS
  · refine max_le ?_ ?_
    · refine le_MMSEP _ _ hn hv (price_nonneg N)
        ⟨outSellAll N, outSellAll_valid N, outSellAll_equalProceeds N, fun j => ?_⟩
      simp [util, outSellAll]
    · refine le_MMSEP _ _ hn hv (price_nonneg N)
        ⟨outKeepAll N, outKeepAll_valid N, outKeepAll_equalProceeds N, fun j => ?_⟩
      simp [util, outKeepAll]

theorem val_zero (L : ℝ) : val N L 0 = fun _ => 1 / L := by
  funext g; simp [val]

theorem val_ne_zero (L : ℝ) {i : Fin (N + 2)} (hi : i ≠ 0) : val N L i = fun _ => L := by
  funext g; simp [val, hi]

theorem MMSEP_agent_zero (L : ℝ) (hL : 1 ≤ L) :
    MMSEP (N + 2) (val N L 0) (price N) = 1 := by
  rw [val_zero, MMSEP_const N (1 / L) (by positivity), max_eq_left]
  rw [div_le_one (by linarith)]
  exact hL

theorem MMSEP_agent_other (L : ℝ) (hL : 1 ≤ L) {i : Fin (N + 2)} (hi : i ≠ 0) :
    MMSEP (N + 2) (val N L i) (price N) = L := by
  rw [val_ne_zero N L hi, MMSEP_const N L (by linarith), max_eq_right hL]

/-- **Example 4**: for every `ε > 0` there is an instance (all prices `1`, agent `1` valuing
every good at `1/L` and the others at `L`, for a large `L`) in which every valid equal-proceeds
outcome leaves some agent below `(1/n + ε)` times her equal-proceeds maximin share.  Hence no
approximation better than `1/n` of the equal-proceeds MMS can be guaranteed. -/
theorem no_better_than_one_over_n (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ o : Outcome (Fin (N + 2)) (N + 2),
      o.Valid (price N) → o.EqualProceeds (price N) →
      ∃ i, util (val N L i) o i
            < (1 / ((N : ℝ) + 2) + ε) * MMSEP (N + 2) (val N L i) (price N) := by
  refine ⟨((N : ℝ) + 2) / ε + 1, by nlinarith [div_pos (show (0:ℝ) < (N:ℝ) + 2 by positivity) hε],
    ?_⟩
  set L : ℝ := ((N : ℝ) + 2) / ε + 1 with hLdef
  have hNpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hL1 : 1 ≤ L := by
    have : 0 < ((N : ℝ) + 2) / ε := div_pos hNpos hε
    simp only [hLdef]; linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hεL : ε * L = ((N : ℝ) + 2) + ε := by
    simp only [hLdef]
    field_simp
  have hdiv : ((N : ℝ) + 2) / L < ε := by
    rw [div_lt_iff₀ hLpos]
    nlinarith
  have hone : (1 : ℝ) < ε * L := by
    rw [hεL]; linarith
  intro o hvalid hep
  have hcast : (((N + 2 : ℕ)) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
  have hmoney : ∀ j, o.money j = (o.sold.card : ℝ) / ((N : ℝ) + 2) := by
    intro j
    rw [hep j, price_sum, hcast]
  by_cases hk : o.sold.card ≤ 1
  · -- few goods sold: agent `0` gets almost nothing
    refine ⟨0, ?_⟩
    rw [MMSEP_agent_zero N L hL1, mul_one, val_zero]
    have hcard : ((o.kept 0).card : ℝ) ≤ (N : ℝ) + 2 := by
      have := Finset.card_le_univ (o.kept 0)
      simp only [Fintype.card_fin] at this
      exact_mod_cast le_trans (by exact_mod_cast this) (le_of_eq (by push_cast; ring))
    have hsum : ∑ _g ∈ o.kept 0, (1 : ℝ) / L = ((o.kept 0).card : ℝ) * (1 / L) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hmon : o.money 0 ≤ 1 / ((N : ℝ) + 2) := by
      have hk' : (o.sold.card : ℝ) ≤ 1 := by exact_mod_cast hk
      rw [hmoney 0]
      gcongr
    unfold util
    rw [hsum]
    have h1 : ((o.kept 0).card : ℝ) * (1 / L) ≤ ((N : ℝ) + 2) / L := by
      rw [mul_one_div, div_le_div_iff_of_pos_right hLpos]
      exact hcard
    linarith
  · -- at least two goods sold: some agent other than `0` keeps nothing
    push_neg at hk
    have hRcard : ((Finset.univ : Finset (Fin (N + 2))) \ o.sold).card
        < ((Finset.univ : Finset (Fin (N + 2))) \ {(0 : Fin (N + 2))}).card := by
      have h1 : ((Finset.univ : Finset (Fin (N + 2))) \ o.sold).card = (N + 2) - o.sold.card := by
        simp [Finset.card_sdiff]
      have h2 : ((Finset.univ : Finset (Fin (N + 2))) \ {(0 : Fin (N + 2))}).card = N + 1 := by
        simp [Finset.card_sdiff]
      have h3 : o.sold.card ≤ N + 2 := by
        have := Finset.card_le_univ o.sold
        simpa using this
      omega
    obtain ⟨i, hiT, hi⟩ := exists_kept_subset o ∅ ((Finset.univ : Finset (Fin (N + 2))) \ o.sold)
      ((Finset.univ : Finset (Fin (N + 2))) \ {(0 : Fin (N + 2))}) hvalid.2.1
      (fun j => by
        intro g hg
        have hg' : g ∈ o.kept j := (Finset.mem_sdiff.mp hg).1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        exact fun hgs => (Finset.disjoint_left.mp (hvalid.1 j) hgs) hg')
      hRcard
    have hi0 : i ≠ 0 := by
      have := (Finset.mem_sdiff.mp hiT).2
      simpa using this
    refine ⟨i, ?_⟩
    rw [MMSEP_agent_other N L hL1 hi0, val_ne_zero N L hi0]
    have hkept : o.kept i = ∅ := Finset.subset_empty.mp hi
    have hsold : (o.sold.card : ℝ) ≤ (N : ℝ) + 2 := by
      have := Finset.card_le_univ o.sold
      simp only [Fintype.card_fin] at this
      calc (o.sold.card : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast this
        _ = (N : ℝ) + 2 := hcast
    have hutil : util (fun _ => L) o i = (o.sold.card : ℝ) / ((N : ℝ) + 2) := by
      unfold util
      rw [hkept, hmoney i]
      simp
    rw [hutil]
    have h1 : (o.sold.card : ℝ) / ((N : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hNpos]
      exact hsold
    have h2 : (1 : ℝ) < (1 / ((N : ℝ) + 2) + ε) * L := by
      have hle : ε ≤ 1 / ((N : ℝ) + 2) + ε := by
        have : (0 : ℝ) < 1 / ((N : ℝ) + 2) := by positivity
        linarith
      nlinarith
    linarith

end EqualProceedsExampleFour

end FairSelling
