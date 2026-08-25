import Mathlib
import RequestProject.ThreeAgents
import RequestProject.Matching
import RequestProject.MMSPartition

/-!
# Canonical partitions for three agents (manuscript Lemma 3)

This file formalizes the manuscript's **Lemma 3** (Section C.1): for a single agent, if every
good is "small" (`v̄(g) < 3/4 · MMS`), then the goods admit a *canonical* partition into three
unified bundles, each acceptable (value `≥ 3/4 · MMS`).

A *canonical partition* (Definition around eq. (7) in the manuscript, specialized to `n = 3`)
consists of three unified bundles — each a set of goods handed in full plus a share of the sale
proceeds — such that at most one bundle (the *leftovers* bundle) is unrestricted, and every other
bundle is either

* **pure**: it carries no sale money (`money k = 0`), or
* **singleton**: it consists of a single good (`(kept k).card = 1`), plus some sale money.

The core combinatorial ingredient of the hard case is a *greedy bag-filling* fact
(`greedy_two_bags`): a set of small items of large enough total value can be split into two
bundles each above a threshold `τ`, whose combined value stays below `3τ` (so that a third
bundle formed from the rest is also above `τ`).

## Status

Lemma 3 (`canonical_partition_three`) is **fully proved** (no `sorry`), using only the standard
axioms.  Supporting results, all proved here:

* `greedy_two_bags` — the greedy bag-filling crux (the value analysis behind cases 3A/3B).
* `canonical_partition_three_small` — the all-pure case (every good `< 1/2·MMS`).
* `canonical_items_money` — the manuscript's case 3 (force-selling / singleton bundles).
* `canonical_partition_three` — Lemma 3 itself, assembled from an MMS partition with at most two
  force-sold goods (`exists_reduced_three`, the `n = 3` case of Lemma 5).
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- **Canonical partition predicate** (`n = 3`), for a single valuation `w` with prices `p` and
acceptability threshold `τ`.  The data is: three kept-good bundles `kept k`, a set `sold` of
force-sold goods whose proceeds are split by `money`, and the index `leftover` of the unrestricted
bundle.  The conditions are: the kept bundles are pairwise disjoint and disjoint from `sold`; the
money shares are non-negative and financed by the sale proceeds; every bundle is acceptable
(`v̄`-value plus money `≥ τ`); and every non-leftovers bundle is pure (no money) or a singleton
(one good). -/
def IsCanonical (w p : G → ℝ) (τ : ℝ) (kept : Fin 3 → Finset G) (sold : Finset G)
    (money : Fin 3 → ℝ) (leftover : Fin 3) : Prop :=
  (∀ j k, j ≠ k → Disjoint (kept j) (kept k)) ∧
  (∀ k, Disjoint sold (kept k)) ∧
  (∀ k, 0 ≤ money k) ∧
  (∑ k, money k ≤ ∑ g ∈ sold, p g) ∧
  (∀ k, τ ≤ vbarSum w p (kept k) + money k) ∧
  (∀ k, k ≠ leftover → money k = 0 ∨ (kept k).card = 1)

/-
**Greedy bag-filling (crux of Lemma 3).**  Let `u ≥ 0` be a weight function, `τ > 0`, and let
`S` be a set of "small" items, each of weight `< (2/3)·τ`, whose total weight is at least `3τ`.
Then `S` can be split into two disjoint sub-bundles `B1, B2`, each of weight at least `τ`, whose
combined weight stays below `3τ`.

The combined-weight bound `< 3τ` is what allows the remaining goods to form an acceptable third
(leftovers) bundle in the manuscript's construction, and is where greedy (largest-first) filling
is essential: filling `B1` with the largest items forces every item available to `B2` to be small
enough that `B2` overshoots the threshold only slightly.
-/
omit [Fintype G] in
lemma greedy_two_bags (u : G → ℝ) (hu : ∀ g, 0 ≤ u g)
    (τ : ℝ) (hτ : 0 < τ) (S : Finset G)
    (hsmall : ∀ g ∈ S, u g < (2/3) * τ)
    (htot : 3 * τ ≤ ∑ g ∈ S, u g) :
    ∃ B1 B2 : Finset G, B1 ⊆ S ∧ B2 ⊆ S ∧ Disjoint B1 B2 ∧
      τ ≤ ∑ g ∈ B1, u g ∧ τ ≤ ∑ g ∈ B2, u g ∧
      (∑ g ∈ B1, u g) + (∑ g ∈ B2, u g) ≤ 3 * τ := by
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ ∈ S, ∀ x ∈ S, u x ≤ u x₁ := by
    exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty ( by rintro rfl; norm_num at htot; linarith ) );
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ ∈ S \ {x₁}, ∀ x ∈ S \ {x₁}, u x ≤ u x₂ := by
    by_cases hS_singleton : S = {x₁};
    · grind;
    · exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty ( by aesop ) );
  by_cases h_case : τ ≤ u x₁ + u x₂;
  · refine' ⟨ { x₁, x₂ }, _ ⟩;
    have := bagfill u τ ( ( 5 / 3 ) * τ ) ( by linarith ) ( by linarith ) ( S \ { x₁, x₂ } ) ?_ ?_ <;> simp_all +decide [ Finset.subset_iff ]; all_goals grind;
  · -- Apply `bagfill` to `S \ {x₁}` with `lo = τ - u x₁` and `hi = τ - u x₁ + τ/2`.
    obtain ⟨B1', hB1'⟩ : ∃ B1' ⊆ S \ {x₁}, τ - u x₁ ≤ ∑ g ∈ B1', u g ∧ ∑ g ∈ B1', u g ≤ τ - u x₁ + τ / 2 := by
      apply bagfill;
      · linarith [ hu x₁, hu x₂, hsmall x₁ hx₁.1, hsmall x₂ ( Finset.mem_sdiff.mp hx₂.1 |>.1 ) ];
      · linarith;
      · grind +qlia;
      · rw [ Finset.sum_eq_add_sum_diff_singleton hx₁.1 ] at htot ; linarith [ hu x₁ ];
    -- Apply `bagfill` to `S \ B1` with `lo = τ` and `hi = (3/2)τ`.
    obtain ⟨B2, hB2⟩ : ∃ B2 ⊆ S \ (insert x₁ B1'), τ ≤ ∑ g ∈ B2, u g ∧ ∑ g ∈ B2, u g ≤ (3 / 2) * τ := by
      apply bagfill;
      · linarith;
      · linarith;
      · grind;
      · rw [ ← Finset.sum_sdiff ( show insert x₁ B1' ⊆ S from ?_ ) ] at *;
        · grind;
        · exact Finset.insert_subset hx₁.1 ( Finset.Subset.trans hB1'.1 ( Finset.sdiff_subset ) );
    refine' ⟨ insert x₁ B1', B2, _, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact ⟨ fun hx => hB2.1 hx |>.2.1 rfl, Finset.disjoint_left.mpr fun x hx₁ hx₂ => hB2.1 hx₂ |>.2.2 hx₁ ⟩;
    · grind;
    · grind

/-
**Lemma 3, the all-pure case.**  If every good is *very* small (`v̄(g) < (1/2)·MMS`), then the
goods split into three pure bundles, each of value `≥ 3/4·MMS`.  This is the clean case of Lemma 3
(no selling needed): apply `greedy_two_bags` to all the goods to obtain two bundles `B1, B2`
of combined value `≤ 3·(3/4·MMS)`, and let the third bundle be everything else, whose value is
then at least `3·MMS − 3·(3/4·MMS) = 3/4·MMS`.
-/
theorem canonical_partition_three_small (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (1/2) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by
  by_cases hMMS : MMS 3 w p = 0;
  · refine' ⟨ fun _ => ∅, ∅, fun _ => 0, 0, _, _, _, _, _ ⟩ <;> simp +decide [ hMMS ];
    exact Finset.sum_nonneg fun _ _ => le_max_of_le_left ( hp _ );
  · obtain ⟨B1, B2, hB1, hB2, hdisj, hsum1, hsum2, hsum3⟩ : ∃ B1 B2 : Finset G, B1 ⊆ Finset.univ ∧ B2 ⊆ Finset.univ ∧ Disjoint B1 B2 ∧ 3 / 4 * MMS 3 w p ≤ ∑ g ∈ B1, vbar w p g ∧ 3 / 4 * MMS 3 w p ≤ ∑ g ∈ B2, vbar w p g ∧ (∑ g ∈ B1, vbar w p g) + (∑ g ∈ B2, vbar w p g) ≤ 3 * (3 / 4 * MMS 3 w p) := by
      apply greedy_two_bags (fun g => vbar w p g) (fun g => by
        exact le_max_of_le_left ( hp g )) (3 / 4 * MMS 3 w p) (by
      exact mul_pos ( by norm_num ) ( lt_of_le_of_ne ( MMS_nonneg ( by norm_num ) w p hw hp ) ( Ne.symm hMMS ) )) Finset.univ (by
      exact fun g _ => by linarith [ hsmall g ] ;) (by
      have := three_MMS_le_vbarSum_univ w p hw hp;
      linarith! [ show 0 ≤ MMS 3 w p from MMS_nonneg ( by decide ) w p hw hp ]);
    refine' ⟨ fun k => if k = 0 then B1 else if k = 1 then B2 else Finset.univ \ ( B1 ∪ B2 ), ∅, fun _ => 0, 2, _, _, _, _, _ ⟩ <;> simp +decide;
    · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
      simp_all +decide [ Finset.disjoint_left ];
      exact fun g hg1 hg2 => hdisj hg2 hg1;
    · intro k
      fin_cases k <;> simp +decide [ * ];
      · exact hsum1;
      · exact hsum2;
      · have hsum_univ : vbarSum w p Finset.univ = ∑ g ∈ B1, vbar w p g + ∑ g ∈ B2, vbar w p g + vbarSum w p (Finset.univ \ (B1 ∪ B2)) := by
          unfold vbarSum; simp +decide [ * ] ;
          rw [ Finset.sum_union hdisj ] ; ring;
        linarith [ three_MMS_le_vbarSum_univ w p hw hp ]

/-
**The item-and-money construction (hard case of Lemma 3).**  Suppose a set `s` of goods is
force-sold, with total proceeds `P = ∑_{g∈s} p g` exceeding `2/3·τ` (where `τ := 3/4·MMS`), that
every good is small (`v̄ < τ`), that `s` has at most two goods, and that the "available value"
`V = v̄(univ \ s) + P` is at least `4τ = 3·MMS`.  Then there is a canonical partition of value
`≥ τ`.

This packages the manuscript's case 3 of Lemma 3.  The construction distributes the *items*
`univ \ s` (each `< τ`) together with the divisible money `P`.
-/
set_option maxHeartbeats 1600000 in
lemma canonical_items_money (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3/4) * MMS 3 w p) (s : Finset G) (hscard : s.card ≤ 2)
    (hP : (2/3) * ((3/4) * MMS 3 w p) < ∑ g ∈ s, p g)
    (hV : 4 * ((3/4) * MMS 3 w p) ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by
  by_cases hτ : 0 < (3 / 4) * MMS 3 w p;
  · have hP_lt_2τ : ∑ g ∈ s, p g < 2 * (3 / 4 * MMS 3 w p) := by
      have hP_lt_2τ : ∑ g ∈ s, p g < ∑ g ∈ s, (3 / 4 * MMS 3 w p) := by
        exact Finset.sum_lt_sum_of_nonempty ( Finset.nonempty_of_ne_empty ( by rintro rfl; norm_num at hP; linarith ) ) fun g hg => lt_of_le_of_lt ( le_max_left _ _ ) ( hsmall g );
      exact hP_lt_2τ.trans_le ( by norm_num; nlinarith [ show ( s.card : ℝ ) ≤ 2 by norm_cast ] );
    by_cases hA : ∀ g ∈ Finset.univ \ s, vbar w p g < (2 / 3) * (3 / 4 * MMS 3 w p);
    · by_cases hA1 : 3 * (3 / 4 * MMS 3 w p) ≤ vbarSum w p (Finset.univ \ s);
      · obtain ⟨B1, B2, hB1, hB2, hdisj, hB1_ge, hB2_ge, hB1B2_le⟩ : ∃ B1 B2 : Finset G, B1 ⊆ Finset.univ \ s ∧ B2 ⊆ Finset.univ \ s ∧ Disjoint B1 B2 ∧ (3 / 4 * MMS 3 w p) ≤ vbarSum w p B1 ∧ (3 / 4 * MMS 3 w p) ≤ vbarSum w p B2 ∧ vbarSum w p B1 + vbarSum w p B2 ≤ 3 * (3 / 4 * MMS 3 w p) := by
          have := greedy_two_bags (vbar w p) (fun g => by
            exact le_max_of_le_left ( hp g )) (3 / 4 * MMS 3 w p) hτ (Finset.univ \ s) hA hA1;
          exact this;
        refine' ⟨ fun i => if i = 0 then B1 else if i = 1 then B2 else ( Finset.univ \ s ) \ ( B1 ∪ B2 ), s, fun i => if i = 0 then 0 else if i = 1 then 0 else ∑ g ∈ s, p g, 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
        · simp_all +decide [ Finset.disjoint_left, Finset.subset_iff ];
          exact fun x hx hx' => hdisj hx' hx;
        · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
          exact ⟨ fun x hx hx' => hB1 hx' hx, fun x hx hx' => hB2 hx' hx ⟩;
        · exact Finset.sum_nonneg fun _ _ => hp _;
        · simp +decide [ Fin.sum_univ_three ];
        · grind +suggestions;
      · obtain ⟨B1, hB1⟩ : ∃ B1 ⊆ Finset.univ \ s, (3 / 4 * MMS 3 w p) ≤ ∑ g ∈ B1, vbar w p g ∧ ∑ g ∈ B1, vbar w p g ≤ (5 / 3) * (3 / 4 * MMS 3 w p) := by
          apply bagfill (fun g => vbar w p g) (3 / 4 * MMS 3 w p) ((5 / 3) * (3 / 4 * MMS 3 w p)) (by linarith) (by linarith) (Finset.univ \ s) (by
          grind) (by
          linarith!);
        obtain ⟨c, hc⟩ : ∃ c ∈ Finset.univ \ s, c ∉ B1 := by
          by_cases hB1_eq : B1 = Finset.univ \ s;
          · simp_all +decide [ vbarSum ];
            grind +splitImp;
          · exact Finset.exists_of_ssubset ( lt_of_le_of_ne hB1.1 hB1_eq );
        refine' ⟨ fun k => if k = 0 then B1 else if k = 1 then { c } else Finset.univ \ ( s ∪ B1 ∪ { c } ), s, fun k => if k = 0 then 0 else if k = 1 then 3 / 4 * MMS 3 w p - vbar w p c else ∑ g ∈ s, p g - ( 3 / 4 * MMS 3 w p - vbar w p c ), 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.sum_univ_three ];
        · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
          grind;
        · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
          grind;
        · intro k; split_ifs <;> norm_num;
          · linarith [ hsmall c ];
          · linarith [ hsmall c, show 0 ≤ vbar w p c from le_max_of_le_left ( hp c ) ];
        · simp_all +decide [ Fin.forall_fin_succ ];
          simp_all +decide [ vbarSum ];
          rw [ Finset.sum_union ];
          · linarith;
          · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( hB1.1 hx' ) |>.2 hx;
    · obtain ⟨a, ha⟩ : ∃ a ∈ Finset.univ \ s, ∀ b ∈ Finset.univ \ s, vbar w p b ≤ vbar w p a := by
        exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty ( by aesop_cat ) );
      by_cases hB : vbar w p a ≥ (2 / 3) * (3 / 4 * MMS 3 w p) ∧ ∃ b ∈ Finset.univ \ (s ∪ {a}), vbar w p b ≥ (2 / 3) * (3 / 4 * MMS 3 w p);
      · obtain ⟨ b, hb₁, hb₂ ⟩ := hB.2;
        refine' ⟨ fun i => if i = 0 then { a } else if i = 1 then { b } else Finset.univ \ ( s ∪ { a, b } ), s, fun i => if i = 0 then 3 / 4 * MMS 3 w p - vbar w p a else if i = 1 then 3 / 4 * MMS 3 w p - vbar w p b else ∑ g ∈ s, p g - ( 3 / 4 * MMS 3 w p - vbar w p a ) - ( 3 / 4 * MMS 3 w p - vbar w p b ), 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.sum_univ_three ];
        · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
          grind;
        · simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
        · grind;
        · refine' ⟨ _, _ ⟩;
          · intro k; fin_cases k <;> simp +decide [ * ] ;
            · simp +decide [ vbarSum ];
            · simp +decide [ vbarSum ];
            · have h_split : vbarSum w p (Finset.univ \ s) = vbarSum w p {a} + vbarSum w p {b} + vbarSum w p (Finset.univ \ (s ∪ {a, b})) := by
                rw [ ← vbarSum_union, ← vbarSum_union ] <;> norm_num;
                · congr with x ; by_cases hx : x = a <;> by_cases hx' : x = b <;> simp_all +decide [ Finset.mem_sdiff ];
                · grind;
              simp_all +decide [ Finset.sum_singleton, vbarSum ];
              linarith;
          · intro k hk; fin_cases k <;> simp +decide at hk ⊢;
      · obtain ⟨B2, hB2⟩ : ∃ B2 ⊆ Finset.univ \ (s ∪ {a}), (3 / 4 * MMS 3 w p) ≤ vbarSum w p B2 ∧ vbarSum w p B2 ≤ (5 / 3) * (3 / 4 * MMS 3 w p) := by
          apply bagfill (vbar w p) (3 / 4 * MMS 3 w p) (5 / 3 * (3 / 4 * MMS 3 w p)) (by linarith) (by linarith) (Finset.univ \ (s ∪ {a})) (by
          grind) (by
          have h_sum : vbarSum w p (Finset.univ \ s) = vbar w p a + vbarSum w p (Finset.univ \ (s ∪ {a})) := by
            rw [ show Finset.univ \ s = { a } ∪ ( Finset.univ \ ( s ∪ { a } ) ) from ?_, vbarSum_union ] <;> norm_num;
            · unfold vbarSum; aesop;
            · grind;
          linarith! [ hsmall a ]);
        refine' ⟨ fun i => if i = 0 then { a } else if i = 1 then B2 else Finset.univ \ ( s ∪ { a } ∪ B2 ), s, fun i => if i = 0 then 3 / 4 * MMS 3 w p - vbar w p a else if i = 1 then 0 else ∑ g ∈ s, p g - ( 3 / 4 * MMS 3 w p - vbar w p a ), 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
        · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
          exact fun h => hB2.1 h |>.1 rfl;
        · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
          exact fun x hx hx' => hB2.1 hx' |>.2 hx;
        · grind +extAll;
        · simp +decide [ Fin.sum_univ_three ];
        · refine' ⟨ _, hB2.2.1, _ ⟩;
          · simp +decide [ vbarSum ];
          · have hV2 : vbarSum w p (Finset.univ \ (s ∪ {a} ∪ B2)) = vbarSum w p (Finset.univ \ s) - vbarSum w p {a} - vbarSum w p B2 := by
              rw [ ← vbarSum_sdiff, ← vbarSum_sdiff ];
              · congr 1 ; ext ; simp +decide [ Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton ] ; tauto;
              · grind;
              · exact Finset.singleton_subset_iff.mpr ha.1;
            unfold vbarSum at * ; norm_num at * ; linarith [ hsmall a ];
  · contrapose! hsmall;
    by_cases h : ∃ g, p g > 0;
    · exact h.imp fun g hg => by linarith [ hw g, hp g, show 0 ≤ vbar w p g from le_max_of_le_left ( hp g ) ] ;
    · simp_all +decide [ show p = fun _ => 0 from funext fun _ => le_antisymm ( le_of_not_gt fun hi => h ⟨ _, hi ⟩ ) ( hp _ ) ];
      exact absurd hP ( not_lt_of_ge ( mul_nonneg ( by norm_num ) ( mul_nonneg ( by norm_num ) ( MMS_nonneg ( by norm_num ) _ _ hw ( fun _ => by norm_num ) ) ) ) )

/-
**Lemma 3 (canonical partition for `n = 3`).**  For a single agent with additive
non-negative valuation `w` and non-negative prices `p`, if every good `g` is small
(`v̄(g) < 3/4 · MMS`), then there is a canonical partition of the goods into three bundles, each
of value at least `3/4 · MMS`.
-/
theorem canonical_partition_three (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3/4) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by
  obtain ⟨A, s, q, hcfg, hscard⟩ := exists_reduced_three w p hw hp;
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hqsum, hge⟩ := hcfg;
  -- Let's establish the value identity `hVeq : vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g = ∑ i : Fin 3, (vbarSum w p (A i) + q i)`.
  have hVeq : vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g = ∑ i, (vbarSum w p (A i) + q i) := by
    have hVeq : vbarSum w p (Finset.univ \ s) = ∑ i : Fin 3, vbarSum w p (A i) := by
      rw [ show Finset.univ \ s = Finset.biUnion Finset.univ A from ?_ ];
      · rw [ vbarSum, Finset.sum_biUnion ];
        · rfl;
        · exact fun i _ j _ hij => hdisjA i j hij;
      · simp_all +decide [ Finset.ext_iff ];
        exact fun g => ⟨ fun hg => by simpa [ hg ] using hcover g, fun ⟨ i, hi ⟩ => fun hg => Finset.disjoint_left.mp ( hdisjs i ) hg hi ⟩;
    simp +decide [ *, Finset.sum_add_distrib ];
  by_cases hbig : ∃ i j : Fin 3, i ≠ j ∧ (1 / 4) * MMS 3 w p < q i ∧ (1 / 4) * MMS 3 w p < q j;
  · obtain ⟨ i, j, hij, hi, hj ⟩ := hbig;
    apply canonical_items_money w p hw hp hsmall s hscard;
    · rw [ ← hqsum, Fin.sum_univ_three ];
      fin_cases i <;> fin_cases j <;> simp +decide at hij hi hj ⊢ <;> linarith! [ hq0 0, hq0 1, hq0 2 ];
    · linarith [ hge i, hge j, show ∑ i, ( vbarSum w p ( A i ) + q i ) ≥ 3 * MMS 3 w p by exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i _ => hge i ) ];
  · -- Define `leftover` as the index with the largest money.
    obtain ⟨leftover, hleftover⟩ : ∃ leftover : Fin 3, ∀ i, i ≠ leftover → q i ≤ (1 / 4) * MMS 3 w p := by
      contrapose! hbig;
      obtain ⟨ i, hi, hi' ⟩ := hbig 0; obtain ⟨ j, hj, hj' ⟩ := hbig i; use i, j; aesop;
    refine' ⟨ A, s, fun i => if i = leftover then q i else 0, leftover, _, _, _, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three ];
    · exact fun k => by split_ifs <;> linarith [ hq0 leftover ] ;
    · fin_cases leftover <;> linarith! [ hq0 0, hq0 1, hq0 2 ];
    · grind

end FairSelling