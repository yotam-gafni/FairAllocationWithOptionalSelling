import Mathlib
import RequestProject.SmallN
import RequestProject.TwoAgents

/-!
# MMS partitions with few force-sold goods (manuscript Lemma 5, general `n`)

The manuscript's **Lemma 5** states that every agent has an MMS partition (into `n` parts) that
force-sells at most `n − 1` goods.  This file generalizes the two-agent `Config`/`reduce_to_one`
machinery of `RequestProject.TwoAgents` to an arbitrary number of parts.

A `ConfigN`-configuration for a single valuation `w` (with prices `p`, threshold `r`) records `n`
disjoint kept-good bundles `A i`, a set `s` of force-sold goods with proceeds split by a money
vector `q`, covering all goods, in which every part is worth at least `r`.  `reduce_stepN` shows
that whenever `n ≤ s.card` a force-sold good can be absorbed into a part (strictly reducing the
number of force-sold goods), and iterating gives a configuration with `s.card ≤ n − 1`
(`exists_reducedN`).  Specialized to `n = 3` this is the input to the canonical-partition
construction of Lemma 3.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- An `n`-part "unified" configuration for a single valuation `w`: `n` pairwise-disjoint kept
bundles `A i` (valued `v̄`), a set `s` of force-sold goods with proceeds split by `q`, covering all
goods, with every part worth at least `r`. -/
def ConfigN (n : ℕ) (w p : G → ℝ) (r : ℝ) (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint s (A i)) ∧
  (s ∪ Finset.univ.biUnion A = Finset.univ) ∧ (∀ i, 0 ≤ q i) ∧
  (∑ i, q i = ∑ g ∈ s, p g) ∧ (∀ i, r ≤ vbarSum w p (A i) + q i)

/-
One reduction step for `n` parts: if the force-sold set has at least `n` goods, one of them
can be moved (kept in full) into a part, strictly decreasing the number of force-sold goods while
preserving all `ConfigN` properties.
-/
theorem reduce_stepN (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ)
    (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ)
    (hcfg : ConfigN n w p r A s q) (hcard : n ≤ s.card) :
    ∃ (A' : Fin n → Finset G) (s' : Finset G) (q' : Fin n → ℝ),
      ConfigN n w p r A' s' q' ∧ s'.card < s.card := by
  obtain ⟨g, hg⟩ : ∃ g ∈ s, ∀ h ∈ s, p g ≤ p h := by
    exact Finset.exists_min_image _ _ ( Finset.card_pos.mp ( lt_of_lt_of_le hn hcard ) );
  obtain ⟨i, hi⟩ : ∃ i : Fin n, p g ≤ q i := by
    have h_bound : (n : ℝ) * p g ≤ ∑ i, q i := by
      rw [ hcfg.2.2.2.2.1 ];
      exact le_trans ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hcard ) ( hp g ) ) ( Finset.sum_le_sum hg.2 );
    contrapose! h_bound;
    simpa using Finset.sum_lt_sum_of_nonempty ⟨ ⟨ 0, hn ⟩, Finset.mem_univ _ ⟩ fun i _ => h_bound i;
  refine' ⟨ Function.update A i ( A i ∪ { g } ), s.erase g, Function.update q i ( q i - p g ), _, _ ⟩ <;> simp_all +decide [ ConfigN ];
  · refine' ⟨ _, _, _, _, _ ⟩;
    · intro j k hjk; by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all +decide [ Finset.disjoint_left ] ;
      · grind;
      · grind +qlia;
      · exact hcfg.1 _ _ hjk;
    · intro j; by_cases hj : j = i <;> simp_all +decide [ Finset.disjoint_left ] ;
      intro a ha₁ ha₂; specialize hcfg; have := hcfg.2.1 i ha₂; aesop;
    · grind +qlia;
    · intro j; by_cases hj : j = i <;> simp +decide [ *, Function.update_apply ] ;
    · refine' ⟨ _, _ ⟩;
      · simp +decide [ ← hcfg.2.2.2.2.1, Finset.sum_update_of_mem ];
      · intro j; by_cases hj : j = i <;> simp_all +decide [ Function.update_apply ] ;
        by_cases h : g ∈ A i <;> simp_all +decide [ vbarSum ];
        · exact absurd ( Finset.disjoint_left.mp ( hcfg.2.1 i ) hg.1 h ) ( by simp +decide );
        · linarith [ hcfg.2.2.2.2.2 i, show vbar w p g ≥ p g from le_max_left _ _ ];
  · exact ⟨ g, hg.1 ⟩

/-
Iterating `reduce_stepN` reaches a configuration with at most `n − 1` force-sold goods.
-/
theorem reduce_to_nsub1 (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ),
      ConfigN n w p r A s q → s.card ≤ k →
      ∃ (A' : Fin n → Finset G) (s' : Finset G) (q' : Fin n → ℝ),
        ConfigN n w p r A' s' q' ∧ s'.card ≤ n - 1 := by
  intro k;
  induction' k with k ih;
  · exact fun A s q h1 h2 => ⟨ A, s, q, h1, by omega ⟩;
  · intro A s q hcfg hcard;
    by_cases hcase : s.card ≤ n - 1;
    · exact ⟨ A, s, q, hcfg, hcase ⟩;
    · obtain ⟨ A', s', q', hcfg', hcard' ⟩ := reduce_stepN n hn w p hp r A s q hcfg ( by omega );
      exact ih A' s' q' hcfg' ( by omega )

/-
**Lemma 5 (general `n`).**  Every valuation admits an MMS configuration with at most `n − 1`
force-sold goods.
-/
theorem exists_reducedN (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ),
      ConfigN n w p (MMS n w p) A s q ∧ s.card ≤ n - 1 := by
  obtain ⟨ o, ho₁, ho₂, ho₃ ⟩ := exists_MMS_partition hn w p hw hp;
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = ∑ g ∈ o.sold, p g) ∧ (∀ i, MMS n w p ≤ vbarSum w p (o.kept i) + q i) := by
    refine' ⟨ fun i => o.money i + ( ∑ g ∈ o.sold, p g - ∑ j, o.money j ) / n, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, mul_div_cancel₀ _ ( by positivity : ( n : ℝ ) ≠ 0 ) ];
    · exact fun i => add_nonneg ( ho₁.2.2.1 i ) ( div_nonneg ( sub_nonneg.2 ( ho₁.2.2.2 ) ) ( Nat.cast_nonneg _ ) );
    · intro j; specialize ho₃ j; simp_all +decide [ util ] ;
      refine' le_trans ho₃ _;
      exact add_le_add ( sum_le_vbarSum _ _ _ ) ( le_add_of_nonneg_right <| div_nonneg ( sub_nonneg.2 <| ho₁.2.2.2 ) <| Nat.cast_nonneg _ );
  convert reduce_to_nsub1 n hn w p hp ( MMS n w p ) ( Finset.card o.sold ) ( fun i => o.kept i ) o.sold q _ _;
  · exact ⟨ ho₁.2.1, fun i => ho₁.1 i, ho₂, hq.1, hq.2.1, hq.2.2 ⟩;
  · rfl

/-- **Lemma 5, `n = 3`.**  Every valuation has an MMS configuration into three parts that
force-sells at most two goods: three pairwise-disjoint kept bundles `A i` and a force-sold set `s`
with `s.card ≤ 2`, whose proceeds are split by `q`, covering all goods, with every part worth at
least `MMS`. -/
theorem exists_reduced_three (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ),
      ConfigN 3 w p (MMS 3 w p) A s q ∧ s.card ≤ 2 := by
  obtain ⟨A, s, q, hcfg, hcard⟩ := exists_reducedN 3 (by norm_num) w p hw hp
  exact ⟨A, s, q, hcfg, by simpa using hcard⟩

end FairSelling