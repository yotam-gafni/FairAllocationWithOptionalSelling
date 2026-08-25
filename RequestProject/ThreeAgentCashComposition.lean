import Mathlib
import RequestProject.ThreeAgentCash

/-!
# Composing a served bundle with a cash-augmented two-agent remainder

This is the corrected version of the final reduction step.  Sale proceeds not paid to the first
agent are represented by the cash token in the two-agent subproblem and are then mapped back to
the original outcome.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Forget the cash token and retain the ordinary goods in a finite set. -/
def optionGoods (s : Finset (Option G)) : Finset G :=
  s.biUnion (fun x => match x with | none => ∅ | some g => {g})

@[simp] lemma mem_optionGoods {s : Finset (Option G)} {g : G} :
    g ∈ optionGoods s ↔ some g ∈ s := by
  unfold optionGoods;
  grind +qlia

lemma optionGoods_disjoint {s t : Finset (Option G)} (h : Disjoint s t) :
    Disjoint (optionGoods s) (optionGoods t) := by
  simp_all +decide [ Finset.disjoint_left, mem_optionGoods ]

lemma sum_cashPrice_optionGoods (R : Finset G) (p : G → ℝ) (cash : ℝ)
    (s : Finset (Option G)) :
    (∑ g ∈ optionGoods s, restrictVal R p g) + (if none ∈ s then cash else 0) =
      ∑ x ∈ s, cashPrice R p cash x := by
  induction' s using Finset.induction with x s hx ih <;> simp +decide [ * ];
  · exact Finset.sum_empty;
  · cases x <;> simp +decide [ *, Finset.sum_insert hx ];
    · rw [ add_comm, ← ih ] ; simp +decide [ hx, optionGoods ] ;
    · rw [ ← ih, show optionGoods ( insert ( some _ ) s ) = { ‹_› } ∪ optionGoods s from ?_ ];
      · grind +suggestions;
      · ext; simp [optionGoods]

lemma sum_cashVal_optionGoods (R : Finset G) (w : G → ℝ) (s : Finset (Option G)) :
    ∑ g ∈ optionGoods s, restrictVal R w g = ∑ x ∈ s, cashVal R w x := by
  induction' s using Finset.induction with x s hx ih;
  · rfl;
  · cases x <;> simp_all +decide [ Finset.sum_insert hx ];
    · rw [ ← ih, show optionGoods ( insert none s ) = optionGoods s from by ext; simp +decide [ hx ] ];
    · rw [ ← ih, show optionGoods ( insert ( some _ ) s ) = { ‹_› } ∪ optionGoods s from ?_ ];
      · rw [ Finset.sum_union ] <;> simp +decide [ hx ];
      · ext; simp [optionGoods]

/-- Drop the cash token from an outcome, retaining ordinary goods and money shares. -/
def dropCashOutcome (o : Outcome (Option G) 2) : Outcome G 2 where
  sold := optionGoods o.sold
  kept i := optionGoods (o.kept i)
  money := o.money

lemma dropCashOutcome_sold_disjoint (o : Outcome (Option G) 2)
    (h : ∀ i, Disjoint o.sold (o.kept i)) :
    ∀ i, Disjoint (dropCashOutcome o).sold ((dropCashOutcome o).kept i) := by
  exact fun i => optionGoods_disjoint ( h i )

lemma dropCashOutcome_kept_disjoint (o : Outcome (Option G) 2)
    (h : ∀ i j, i ≠ j → Disjoint (o.kept i) (o.kept j)) :
    ∀ i j, i ≠ j → Disjoint ((dropCashOutcome o).kept i) ((dropCashOutcome o).kept j) := by
  exact fun i j hij => optionGoods_disjoint ( h i j hij )

/-
Dropping the token turns its price into an external cash reserve in the budget inequality.
-/
lemma dropCashOutcome_budget (R : Finset G) (p : G → ℝ) (cash : ℝ)
    (o : Outcome (Option G) 2) (hcash : 0 ≤ cash)
    (hbudget : ∑ i, o.money i ≤ ∑ x ∈ o.sold, cashPrice R p cash x) :
    ∑ i, (dropCashOutcome o).money i ≤
      (∑ g ∈ (dropCashOutcome o).sold, restrictVal R p g) + cash := by
  convert hbudget.trans _ using 1;
  rw [ ← sum_cashPrice_optionGoods ];
  split_ifs <;> simp_all +decide [ dropCashOutcome ]

/-
The token and all ordinary goods outside `R` have zero consumption value, so dropping them
preserves utility.
-/
lemma util_dropCashOutcome (R : Finset G) (w : G → ℝ)
    (o : Outcome (Option G) 2) (i : Fin 2) :
    util (restrictVal R w) (dropCashOutcome o) i = util (cashVal R w) o i := by
  unfold util;
  rw [ ← sum_cashVal_optionGoods ];
  rfl

/-
Composition when the two-agent remainder has an external cash reserve.  This is the same
construction as `compose_three`, with the reserve canceled against unused proceeds from `Sa`.
-/
lemma compose_three_with_reserve (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome G 2)
    (ho2sold : ∀ i, Disjoint o2.sold (o2.kept i))
    (ho2disj : ∀ i j, i ≠ j → Disjoint (o2.kept i) (o2.kept j))
    (ho2money : ∀ i, 0 ≤ o2.money i)
    (ho2budget : ∑ i, o2.money i ≤
      ∑ g ∈ o2.sold, restrictVal (Finset.univ \ (Ka ∪ Sa)) p g + cash)
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v d)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  -- Define the sets and cash values for the composition.
  set R : Finset G := Finset.univ \ (Ka ∪ Sa)
  set Bb : Finset G := o2.kept 0 ∩ R
  set Bd : Finset G := o2.kept 1 ∩ R
  set cb := o2.money 0
  set cd := o2.money 1;
  refine' ⟨ unifiedOutcome v p ( fun i ↦ if i = a then Ka else if i = b then Bb else Bd ) ( Sa ∪ ( o2.sold ∩ R ) ) ( fun i ↦ if i = a then ma else if i = b then cb else cd ), _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three ];
  · convert unifiedOutcome_valid v p hp ( fun i => if i = a then Ka else if i = b then Bb else Bd ) ( Sa ∪ o2.sold ∩ R ) ( fun i => if i = a then ma else if i = b then cb else cd ) _ _ _ _ using 1;
    · simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
      grind;
    · simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
      grind;
    · grind;
    · rw [ Fin.sum_univ_three ];
      rw [ Finset.sum_union ];
      · rw [ show ∑ x ∈ o2.sold ∩ R, p x = ∑ x ∈ o2.sold, restrictVal R p x from ?_ ];
        · grind;
        · rw [ ← Finset.sum_subset ( Finset.inter_subset_left ) ];
          any_goals exact Finset.univ;
          · simp +decide [ Finset.sum_ite, restrictVal ];
          · simp +contextual [ Finset.ext_iff ];
      · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( Finset.mem_inter.mp hx' |>.2 ) |>.2 ( Finset.mem_union_right _ hx );
  · intro i
    by_cases hi : i = a ∨ i = b ∨ i = d;
    · rcases hi with ( rfl | rfl | rfl ) <;> simp_all +decide [ util_unifiedOutcome ];
      · split_ifs <;> simp_all +decide [ util ];
        refine' le_trans hb _;
        rw [ ← Finset.sum_subset ( show Bb ⊆ o2.kept 0 from Finset.inter_subset_left ) ];
        · refine' add_le_add _ le_rfl;
          refine' Finset.sum_le_sum fun x hx => _;
          unfold restrictVal vbar; aesop;
        · simp +contextual [ Bb, restrictVal ];
      · split_ifs <;> simp_all +decide [ util ];
        refine' le_trans hd _;
        rw [ ← Finset.sum_subset ( show Bd ⊆ o2.kept 1 from Finset.inter_subset_left ) ];
        · refine' add_le_add _ le_rfl;
          refine' Finset.sum_le_sum fun x hx => _;
          unfold restrictVal vbar; aesop;
        · simp +contextual [ Bd, restrictVal ];
    · fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases d <;> trivial

/-
A valid two-agent outcome on remaining goods plus banked cash can be combined with the
already-served first agent.
-/
lemma compose_three_cash (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hcash0 : 0 ≤ cash)
    (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome (Option G) 2)
    (ho2 : o2.Valid (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash))
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v d)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  apply compose_three_with_reserve v p hp a b d hab had hbd Ka Sa ma cash hKSa hma0 hbudget haU (dropCashOutcome o2);
  any_goals rw [ util_dropCashOutcome ] ; assumption;
  · exact dropCashOutcome_sold_disjoint o2 ho2.1;
  · exact dropCashOutcome_kept_disjoint o2 ho2.2.1;
  · exact fun i => ho2.2.2.1 i;
  · convert dropCashOutcome_budget ( Finset.univ \ ( Ka ∪ Sa ) ) p cash o2 hcash0 ho2.2.2.2 using 1

/-
It suffices that each remaining agent's cash-augmented two-agent MMS reaches its original
`3/4` threshold.
-/
lemma finish_from_cash_reduction (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hcash0 : 0 ≤ cash)
    (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (hRb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v b))
        (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash))
    (hRd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v d))
        (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash)) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨o2, ho2⟩ : ∃ o2 : Outcome (Option G) 2, o2.Valid (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash) ∧ ∀ i, MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v (if i = 0 then b else d))) (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash) ≤ util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v (if i = 0 then b else d))) o2 i := by
    convert exists_MMS_two ( fun i => cashVal ( Finset.univ \ ( Ka ∪ Sa ) ) ( v ( if i = 0 then b else d ) ) ) ( cashPrice ( Finset.univ \ ( Ka ∪ Sa ) ) p cash ) _ _ using 1;
    · exact fun i g => cashVal_nonneg _ _ ( hv _ ) _;
    · exact fun g => cashPrice_nonneg _ _ hp _ hcash0 g;
  refine' compose_three_cash v p hp a b d hab had hbd Ka Sa ma cash hKSa hma0 hcash0 hbudget haU o2 ho2.1 _ _;
  · exact le_trans hRb ( ho2.2 0 );
  · exact le_trans hRd ( ho2.2 1 )

end FairSelling