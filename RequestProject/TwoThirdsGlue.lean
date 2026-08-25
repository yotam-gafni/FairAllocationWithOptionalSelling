import Mathlib
import RequestProject.Selling
import RequestProject.TwoThirdsCanonical
import RequestProject.TwoThirdsProp6

/-!
# Assembling canonical partitions out of pure parts

The proof of Lemma 9 in the manuscript builds the canonical partition in two stages: a sequence of
transformations creates a number of *pure* acceptable parts (each made of two large goods), and
Proposition 6 then produces the remaining parts out of what is left.  This file provides the
plumbing for that assembly:

* `CanonExists w p μ t k R D` — "a canonical `k`-partition of `(R, D)` exists"; for `k = 0` the
  statement is vacuously true, which lets the recursion of Lemma 9 stop gracefully;
* `CanonExists.mono` — a canonical partition of a smaller pool is one of a larger pool;
* `canonical_cons` — one more pure acceptable part, made of goods that the canonical partition of
  the smaller pool does not touch, extends it to a canonical `(k+1)`-partition.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- There is a canonical `k`-partition of the available resources `(R, D)`.  For `k = 0` this is
vacuously true. -/
def CanonExists (w p : G → ℝ) (μ t : ℝ) (k : ℕ) (R : Finset G) (D : ℝ) : Prop :=
  ∀ h : 0 < k, Nonempty (@Canonical G _ w p μ t k ⟨Nat.pos_iff_ne_zero.mp h⟩ R D)

omit [Fintype G] in
/-- With a `NeZero` instance at hand, `CanonExists` is the existence of a canonical partition. -/
lemma CanonExists.nonempty {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
    (h : CanonExists w p μ t k R D) : Nonempty (Canonical w p μ t k R D) :=
  h (Nat.pos_of_ne_zero (NeZero.ne k))

omit [Fintype G] in
lemma canonExists_of_nonempty {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
    (h : Nonempty (Canonical w p μ t k R D)) : CanonExists w p μ t k R D :=
  fun _ => h

omit [Fintype G] in
lemma canonExists_zero (w p : G → ℝ) (μ t : ℝ) (R : Finset G) (D : ℝ) :
    CanonExists w p μ t 0 R D := fun h => absurd h (by omega)

omit [Fintype G] in
/-- A canonical partition of a smaller pool of goods is a canonical partition of a larger one. -/
lemma CanonExists.mono {w p : G → ℝ} {μ t : ℝ} {k : ℕ} {R R' : Finset G} {D D' : ℝ}
    (hR : R ⊆ R') (hD : D ≤ D') (h : CanonExists w p μ t k R D) :
    CanonExists w p μ t k R' D' := by
  intro hk
  haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
  obtain ⟨C⟩ := h hk
  exact ⟨{ C with
    goods_subset := fun j => (C.goods_subset j).trans hR
    sell_subset := C.sell_subset.trans hR
    dcash_sum := le_trans C.dcash_sum hD }⟩

omit [Fintype G] in
/-- **Adding one pure part.**  If a canonical `k`-partition of `(R', D)` exists and `new` is a set
of available goods, disjoint from `R'`, that is acceptable on its own, then a canonical
`(k+1)`-partition of `(R, D)` exists: the new part is added at the last index (or, when `k = 0`,
becomes the special part). -/
lemma canonical_cons {w p : G → ℝ} {μ t : ℝ} {k : ℕ} {R R' new : Finset G} {D : ℝ}
    (hD : 0 ≤ D) (hR' : R' ⊆ R) (hnew : new ⊆ R) (hdisj : Disjoint new R')
    (hacc : t ≤ vbarSum w p new)
    (h : CanonExists w p μ t k R' D) :
    CanonExists w p μ t (k + 1) R D := by
  classical
  intro _
  haveI : NeZero (k + 1) := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- no other part: the new part is the special part
    subst hk
    exact ⟨{ goods := fun _ => new
             sell := ∅
             src := fun _ => none
             dcash := fun _ => 0
             scash := fun _ => 0
             goods_subset := fun _ => hnew
             goods_disj := fun j j' hjj =>
               absurd (Fin.ext (by have := j.isLt; have := j'.isLt; omega)) hjj
             sell_subset := by simp
             sell_disj := fun _ => by simp
             src_mem := fun j f hf => by simp at hf
             dcash_nonneg := fun _ => le_rfl
             scash_nonneg := fun _ => le_rfl
             dcash_sum := by simpa using hD
             scash_sum := fun f hf => by simp at hf
             scash_zero := fun _ _ => rfl
             price_large := fun f hf => by simp at hf
             acceptable := fun _ => by simpa using hacc
             pure_or_singleton := fun _ _ => Or.inl rfl
             singleton_dcash := fun _ _ h => absurd rfl h
             singleton_cond := fun _ _ h => absurd rfl h }⟩
  · haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
    obtain ⟨C⟩ := h hk
    have hlast : ¬ ((Fin.last k : Fin (k + 1)) : ℕ) < k := by simp
    have hgoods_disj_new : ∀ j : Fin k, Disjoint new (C.goods j) :=
      fun j => Finset.disjoint_of_subset_right (C.goods_subset j) hdisj
    refine ⟨{ goods := fun j => if h : (j : ℕ) < k then C.goods ⟨j, h⟩ else new
              sell := C.sell
              src := fun j => if h : (j : ℕ) < k then C.src ⟨j, h⟩ else none
              dcash := fun j => if h : (j : ℕ) < k then C.dcash ⟨j, h⟩ else 0
              scash := fun j => if h : (j : ℕ) < k then C.scash ⟨j, h⟩ else 0
              goods_subset := ?_
              goods_disj := ?_
              sell_subset := C.sell_subset.trans hR'
              sell_disj := ?_
              src_mem := ?_
              dcash_nonneg := ?_
              scash_nonneg := ?_
              dcash_sum := ?_
              scash_sum := ?_
              scash_zero := ?_
              price_large := C.price_large
              acceptable := ?_
              pure_or_singleton := ?_
              singleton_dcash := ?_
              singleton_cond := ?_ }⟩
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact (C.goods_subset _).trans hR'
      · simp only [dif_neg hj]; exact hnew
    · intro j j' hjj
      by_cases hj : (j : ℕ) < k <;> by_cases hj' : (j' : ℕ) < k
      · simp only [dif_pos hj, dif_pos hj']
        exact C.goods_disj _ _ (fun h => hjj (Fin.ext (by simpa using congrArg Fin.val h)))
      · simp only [dif_pos hj, dif_neg hj']
        exact (hgoods_disj_new _).symm
      · simp only [dif_neg hj, dif_pos hj']
        exact hgoods_disj_new _
      · exact absurd (Fin.ext (by omega : (j : ℕ) = (j' : ℕ))) hjj
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.sell_disj _
      · simp only [dif_neg hj]
        exact Finset.disjoint_of_subset_left C.sell_subset hdisj.symm
    · intro j f hf
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj] at hf; exact C.src_mem _ f hf
      · rw [dif_neg hj] at hf; exact absurd hf (by simp)
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.dcash_nonneg _
      · simp only [dif_neg hj]; exact le_rfl
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.scash_nonneg _
      · simp only [dif_neg hj]; exact le_rfl
    · have hcast : ∀ j : Fin k,
          (if h : ((j.castSucc : Fin (k + 1)) : ℕ) < k then C.dcash ⟨(j.castSucc : ℕ), h⟩ else 0)
            = C.dcash j := by
        intro j
        rw [dif_pos (show ((j.castSucc : Fin (k + 1)) : ℕ) < k by simp)]
        exact congrArg C.dcash (Fin.ext (by simp))
      rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hcast j),
        dif_neg hlast, add_zero]
      exact C.dcash_sum
    · intro f hf
      have hstep : ∑ j ∈ Finset.univ.filter
            (fun j : Fin (k + 1) => (if h : (j : ℕ) < k then C.src ⟨j, h⟩ else none) = some f),
              (if h : (j : ℕ) < k then C.scash ⟨j, h⟩ else 0)
          = ∑ j ∈ Finset.univ.filter (fun j : Fin k => C.src j = some f), C.scash j := by
        have hcast : ∀ j : Fin k,
            (if (if h : ((j.castSucc : Fin (k + 1)) : ℕ) < k then C.src ⟨(j.castSucc : ℕ), h⟩
                  else none) = some f then
              (if h : ((j.castSucc : Fin (k + 1)) : ℕ) < k then C.scash ⟨(j.castSucc : ℕ), h⟩
                else 0) else 0)
              = (if C.src j = some f then C.scash j else 0) := by
          intro j
          rw [dif_pos (show ((j.castSucc : Fin (k + 1)) : ℕ) < k by simp),
            dif_pos (show ((j.castSucc : Fin (k + 1)) : ℕ) < k by simp)]
          have hj : (⟨(j.castSucc : ℕ), (by simp : ((j.castSucc : Fin (k+1)) : ℕ) < k)⟩ : Fin k) = j :=
            Fin.ext (by simp)
          rw [hj]
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc,
          Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hcast j), dif_neg hlast]
        simp
      rw [hstep]
      exact C.scash_sum f hf
    · intro j hj
      by_cases hjk : (j : ℕ) < k
      · rw [dif_pos hjk] at hj ⊢; exact C.scash_zero _ hj
      · rw [dif_neg hjk]
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.acceptable _
      · simp only [dif_neg hj, add_zero]; exact hacc
    · intro j _
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]
        by_cases hz : (⟨j, hj⟩ : Fin k) = 0
        · -- the special part of `C` sits at index `0`, which is excluded
          exfalso
          have hj0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val hz
          exact absurd (Fin.ext (show (j : ℕ) = ((0 : Fin (k + 1)) : ℕ) by simp [hj0]))
            (by assumption)
        · exact C.pure_or_singleton _ hz
      · rw [dif_neg hj]; exact Or.inl rfl
    · intro j hjne hsrc
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj] at hsrc ⊢
        refine C.singleton_dcash _ (fun hz => ?_) hsrc
        have hj0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val hz
        exact hjne (Fin.ext (show (j : ℕ) = ((0 : Fin (k + 1)) : ℕ) by simp [hj0]))
      · rw [dif_neg hj] at hsrc; exact absurd rfl hsrc
    · intro j hjne hsrc e he f hf
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj] at hsrc he
        refine C.singleton_cond _ (fun hz => ?_) hsrc e he f hf
        have hj0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val hz
        exact hjne (Fin.ext (show (j : ℕ) = ((0 : Fin (k + 1)) : ℕ) by simp [hj0]))
      · rw [dif_neg hj] at hsrc; exact absurd rfl hsrc

end FairSelling
