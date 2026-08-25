import Mathlib
import RequestProject.ThreeAgents

/-!
# A two-agent remainder with banked sale proceeds

When a bundle is funded by selling a good, the unused proceeds remain available to the two
agents who have not yet been served.  This module represents those banked proceeds by one
additional, purely sellable good.  It is the bookkeeping interface needed by the three-agent
proof; unlike simply deleting every sold good, it does not discard unused money.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- The valuation in a remainder `R`, augmented by a cash token.  Ordinary goods outside `R`
have value zero, and the cash token has no consumption value. -/
def cashVal (R : Finset G) (w : G → ℝ) : Option G → ℝ
  | none => 0
  | some g => restrictVal R w g

/-- Prices in a remainder augmented by already-banked sale proceeds `c`. -/
def cashPrice (R : Finset G) (p : G → ℝ) (c : ℝ) : Option G → ℝ
  | none => c
  | some g => restrictVal R p g

@[simp] lemma cashVal_none (R : Finset G) (w : G → ℝ) : cashVal R w none = 0 := rfl
@[simp] lemma cashVal_some (R : Finset G) (w : G → ℝ) (g : G) :
    cashVal R w (some g) = restrictVal R w g := rfl
@[simp] lemma cashPrice_none (R : Finset G) (p : G → ℝ) (c : ℝ) :
    cashPrice R p c none = c := rfl
@[simp] lemma cashPrice_some (R : Finset G) (p : G → ℝ) (c : ℝ) (g : G) :
    cashPrice R p c (some g) = restrictVal R p g := rfl

lemma cashVal_nonneg (R : Finset G) (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) :
    ∀ x, 0 ≤ cashVal R w x := by
  intro x
  cases x with
  | none => simp
  | some g => simpa using restrictVal_nonneg R hw g

lemma cashPrice_nonneg (R : Finset G) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (c : ℝ) (hc : 0 ≤ c) : ∀ x, 0 ≤ cashPrice R p c x := by
  intro x
  cases x with
  | none => simpa using hc
  | some g => simpa using restrictVal_nonneg R hp g

/-
If an agent can exhibit two disjoint bundles of remaining goods and split the banked cash
between them so that both reach `τ`, then its two-agent MMS in the cash-augmented remainder is
at least `τ`.
-/
lemma MMS2_cash_of_two_bundles (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C D : Finset G) (c c0 c1 τ : ℝ)
    (hCD : Disjoint C D) (hCR : C ⊆ R) (hDR : D ⊆ R)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hcash : c0 + c1 ≤ c)
    (hC : τ ≤ vbarSum w p C + c0) (hD : τ ≤ vbarSum w p D + c1) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p c) := by
  -- Apply the lemma `le_MMS_of_outcome` to the outcome constructed from `C` and `D`.
  have h_outcome : ∃ o : Outcome (Option G) 2, o.Valid (cashPrice R p c) ∧ ∀ j, τ ≤ util (cashVal R w) o j := by
    refine' ⟨ unifiedOutcome ( fun _ => cashVal R w ) ( cashPrice R p c ) ( fun i => if i = 0 then C.map Function.Embedding.some else D.map Function.Embedding.some ) { none } ( fun i => if i = 0 then c0 else c1 ), _, _ ⟩ <;> simp_all +decide [ Outcome.Valid, util ];
    · unfold unifiedOutcome; simp +decide [ Finset.disjoint_left, Finset.disjoint_right ] ;
      refine' ⟨ _, _, _, _ ⟩;
      · grind;
      · exact ⟨ fun a ha ha' b hb hab => False.elim ( Finset.disjoint_left.mp hCD ha ( hab ▸ hb ) ), fun a ha ha' b hb hab => False.elim ( Finset.disjoint_left.mp hCD ( hab ▸ hb ) ha ) ⟩;
      · refine' ⟨ add_nonneg hc0 _, add_nonneg hc1 _ ⟩; all_goals exact Finset.sum_nonneg fun x hx => cashPrice_nonneg R p hp c ( by linarith ) _;
      · simp +decide [ Fin.univ_succ, Finset.sum_biUnion, hCD ];
        rw [ Finset.sum_union ];
        · linarith;
        · simp_all +decide [ Finset.disjoint_left ];
    · convert And.intro hC hD using 2 <;> simp +decide [ vbarSum ];
      · simp +decide [ unifiedOutcome, cashVal, cashPrice ];
        rw [ Finset.sum_filter, Finset.sum_filter ];
        rw [ Finset.sum_map, Finset.sum_map ] ; simp +decide [ vbar ] ; ring;
        simp +decide [ add_comm, add_left_comm, add_assoc, Finset.sum_add_distrib, max_def' ];
        rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; split_ifs <;> linarith [ hw x, hp x, show restrictVal R w x = w x from if_pos ( hCR hx ), show restrictVal R p x = p x from if_pos ( hCR hx ) ] ;
      · unfold unifiedOutcome; simp +decide [ Finset.sum_map, vbar ] ;
        simp +decide [ Finset.sum_filter, Finset.sum_map, cashPrice, cashVal, restrictVal ];
        rw [ add_comm, Finset.sum_congr rfl fun x hx => show ( if ( if x ∈ R then p x else 0 ) ≤ if x ∈ R then w x else 0 then if x ∈ R then w x else 0 else 0 ) = max ( p x ) ( w x ) - ( if ( if x ∈ R then w x else 0 ) < if x ∈ R then p x else 0 then if x ∈ R then p x else 0 else 0 ) from ?_ ] ; simp +decide [ Finset.sum_add_distrib, Finset.sum_sub_distrib ] ; ring;
        grind;
  convert le_MMS_of_outcome ( hn := by decide ) ( cashVal R w ) ( cashPrice R p c ) ( cashVal_nonneg R w hw ) ( cashPrice_nonneg R p hp c ( by linarith ) ) h_outcome.choose h_outcome.choose_spec.1 τ h_outcome.choose_spec.2 using 1

/-
Selling one good and banking all of its proceeds preserves two complete parts of a
three-part MMS configuration.
-/
lemma remove_one_cash_MMS2 (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (g : G) :
    MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ {g}) w)
      (cashPrice (Finset.univ \ {g}) p (p g)) := by
  obtain ⟨A, s, q, hcfg, hs⟩ := exists_reduced_three w p hw hp;
  obtain ⟨lost, j, k, hlj, hlk, hjk, hg⟩ : ∃ lost j k : Fin 3, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ s ∨ ∃ lost j k : Fin 3, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost := by
    by_cases hg : g ∈ s <;> simp_all +decide [ ConfigN ];
    · exact ⟨ 0, 1, 2, Or.inl ⟨ by decide, by decide, by decide ⟩ ⟩;
    · simp_all +decide [ Finset.ext_iff ];
      obtain ⟨ i, hi ⟩ := hcfg.2.2.1 g |>.resolve_left hg; use i; fin_cases i <;> simp_all +decide ;
  · have h_outcome : ∃ o : Outcome (Option G) 2, o.Valid (cashPrice (Finset.univ \ {g}) p (p g)) ∧ util (cashVal (Finset.univ \ {g}) w) o 0 ≥ vbarSum w p (A j) + q j ∧ util (cashVal (Finset.univ \ {g}) w) o 1 ≥ vbarSum w p (A k) + q k := by
      refine' ⟨ unifiedOutcome ( fun i => cashVal ( Finset.univ \ { g } ) w ) ( cashPrice ( Finset.univ \ { g } ) p ( p g ) ) ( fun i => if i = 0 then Finset.map ( Function.Embedding.some ) ( A j ) else Finset.map ( Function.Embedding.some ) ( A k ) ) ( Finset.map ( Function.Embedding.some ) ( s \ { g } ) ∪ { none } ) ( fun i => if i = 0 then q j else q k ), _, _, _ ⟩ <;> simp +decide [ unifiedOutcome_valid, util_unifiedOutcome ];
      · refine' unifiedOutcome_valid _ _ _ _ _ _ _ _ _ _;
        · exact fun x => cashPrice_nonneg _ _ hp _ ( hp g ) x;
        · simp +decide [ Fin.forall_fin_two, Finset.disjoint_left ];
          exact ⟨ fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 j k hjk ) ha hb, fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 k j ( Ne.symm hjk ) ) ha hb ⟩;
        · have := hcfg.2.1; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        · exact fun i => by split_ifs <;> [ exact hcfg.2.2.2.1 j; exact hcfg.2.2.2.1 k ] ;
        · have := hcfg.2.2.2.2.1; simp_all +decide [ Fin.sum_univ_three ] ;
          unfold restrictVal; simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ] ;
          fin_cases j <;> fin_cases k <;> fin_cases lost <;> simp +decide at hlj hlk hjk ⊢ <;> linarith! [ hcfg.2.2.2.1 0, hcfg.2.2.2.1 1, hcfg.2.2.2.1 2 ];
      · convert util_unifiedOutcome _ _ _ _ _ _ |> Eq.ge using 1;
        simp +decide [ vbarSum, cashVal, cashPrice ];
        refine' Finset.sum_congr rfl fun x hx => _;
        by_cases hxg : x = g <;> simp +decide [ hxg, vbar, cashVal, cashPrice ];
        have := hcfg.2.1 j; simp_all +decide [ Finset.disjoint_left ] ;
      · convert le_rfl using 1;
        convert util_unifiedOutcome _ _ _ _ _ _ using 1;
        simp +decide [ vbarSum, cashVal, cashPrice ];
        refine' Finset.sum_congr rfl fun x hx => _;
        simp +decide [ vbar, cashVal, cashPrice ];
        by_cases hxg : x = g <;> simp +decide [ hxg, restrictVal ];
        have := hcfg.2.1 k; simp_all +decide [ Finset.disjoint_left ] ;
    obtain ⟨ o, ho₁, ho₂, ho₃ ⟩ := h_outcome;
    have h_outcome : ∀ i, util (cashVal (Finset.univ \ {g}) w) o i ≥ MMS 3 w p := by
      intro i
      fin_cases i <;> simp_all +decide [ ConfigN ];
      · linarith [ hcfg.2.2.2.2.2 j ];
      · linarith [ hcfg.2.2.2.2.2 k ];
    apply le_MMS_of_outcome;
    any_goals assumption;
    · decide +revert;
    · exact cashVal_nonneg _ _ hw;
    · exact fun x => by cases x <;> [ exact hp g; exact restrictVal_nonneg _ ( fun _ => hp _ ) _ ] ;
  · obtain ⟨lost, j, k, hlj, hlk, hjk, hg⟩ : ∃ lost j k : Fin 3, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost ∧ s ∩ {g} = ∅ := by
      have := hcfg.2.1;
      obtain ⟨ lost, j, k, hlj, hlk, hjk, hg ⟩ := ‹∃ lost j k, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost›; use lost, j, k; simp_all +decide [ Finset.disjoint_left ] ;
      exact Finset.disjoint_iff_inter_eq_empty.mp ( Finset.disjoint_singleton_right.mpr fun h => this lost h hg );
    obtain ⟨o, ho_valid, ho_util⟩ : ∃ o : Outcome (Option G) 2, o.Valid (cashPrice (Finset.univ \ {g}) p (p g)) ∧ ∀ i, MMS 3 w p ≤ util (cashVal (Finset.univ \ {g}) w) o i := by
      refine' ⟨ _, _, _ ⟩;
      refine' unifiedOutcome ( fun i => cashVal ( Finset.univ \ { g } ) w ) ( cashPrice ( Finset.univ \ { g } ) p ( p g ) ) ( fun i => Finset.map ( Function.Embedding.some ) ( A ( if i = 0 then j else k ) ) ) ( Finset.map ( Function.Embedding.some ) s ) ( fun i => q ( if i = 0 then j else k ) );
      · refine' unifiedOutcome_valid _ _ _ _ _ _ _ _ _ _;
        · exact fun x => cashPrice_nonneg _ _ hp _ ( hp g ) x;
        · simp +decide [ Fin.forall_fin_two, Finset.disjoint_left ];
          exact ⟨ fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 j k hjk ) ha hb, fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 k j ( Ne.symm hjk ) ) ha hb ⟩;
        · have := hcfg.2.1; simp_all +decide [ Finset.disjoint_left ] ;
        · exact fun i => hcfg.2.2.2.1 _;
        · have := hcfg.2.2.2.2.1; simp_all +decide [ Fin.sum_univ_three ] ;
          have h_sum_restrict : ∑ x ∈ s, restrictVal (Finset.univ \ {g}) p x = ∑ x ∈ s, p x := by
            exact Finset.sum_congr rfl fun x hx => if_pos <| by rw [ Finset.ext_iff ] at hg; specialize hg; have := hg.2 x; aesop;
          fin_cases j <;> fin_cases k <;> fin_cases lost <;> simp +decide at hlj hlk hjk ⊢ <;> linarith! [ hcfg.2.2.2.1 0, hcfg.2.2.2.1 1, hcfg.2.2.2.1 2 ];
      · intro i
        have h_util : util (cashVal (Finset.univ \ {g}) w) (unifiedOutcome (fun i => cashVal (Finset.univ \ {g}) w) (cashPrice (Finset.univ \ {g}) p (p g)) (fun i => Finset.map Function.Embedding.some (A (if i = 0 then j else k))) (Finset.map Function.Embedding.some s) fun i => q (if i = 0 then j else k)) i = vbarSum w p (A (if i = 0 then j else k)) + q (if i = 0 then j else k) := by
          convert util_unifiedOutcome _ _ _ _ _ _ using 1;
          simp +decide [ vbarSum, cashVal, cashPrice ];
          refine' Finset.sum_congr rfl fun x hx => _;
          simp +decide [ vbar, cashVal, cashPrice ];
          simp +decide [ restrictVal, Finset.mem_sdiff, Finset.mem_singleton ];
          have := hcfg.1 ( if i = 0 then j else k ) lost; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        have := hcfg.2.2.2.2.2 ( if i = 0 then j else k ) ; aesop;
    apply le_MMS_of_outcome;
    all_goals norm_cast;
    · exact cashVal_nonneg _ _ hw;
    · exact fun x => cashPrice_nonneg _ _ hp _ ( hp g ) x

/-
A total-value criterion for a cash-augmented two-agent remainder.  If ordinary goods
plus banked cash have value at least `3τ` and every ordinary good is worth at most `τ`, then two
bundles worth `τ` can be formed.
-/
lemma MMS2_cash_of_total (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R : Finset G) (cash τ : ℝ) (hcash : 0 ≤ cash) (hτ : 0 ≤ τ)
    (hsmall : ∀ g ∈ R, vbar w p g ≤ τ)
    (htotal : 3 * τ ≤ vbarSum w p R + cash) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p cash) := by
  by_cases hcase : τ ≤ ∑ g ∈ R, vbar w p g;
  · -- Use `bagfill` to select $C$ with $\tau \leq \text{value}(C) \leq 2\tau$.
    obtain ⟨C, hC⟩ : ∃ C ⊆ R, τ ≤ vbarSum w p C ∧ vbarSum w p C ≤ 2 * τ := by
      have := bagfill ( fun g => vbar w p g ) τ ( 2 * τ ) hτ ( by linarith ) R ?_ hcase;
      · exact this;
      · exact fun g hg => by linarith [ hsmall g hg ] ;
    convert MMS2_cash_of_two_bundles w p hw hp R C ( R \ C ) cash 0 cash _ _ _ _ _ _ using 1;
    any_goals tauto;
    · simp +decide [ vbarSum_sdiff, hC.1 ];
      grind;
    · exact Finset.disjoint_sdiff;
    · grind +splitImp;
  · apply MMS2_cash_of_two_bundles;
    any_goals tauto;
    · linarith!;
    · simp +decide [ vbarSum ];
    · exact le_add_of_nonneg_left ( Finset.sum_nonneg fun _ _ => le_max_of_le_left ( hp _ ) )

end FairSelling