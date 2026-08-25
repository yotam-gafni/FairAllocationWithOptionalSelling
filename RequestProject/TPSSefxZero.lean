import Mathlib
import RequestProject.Selling
import RequestProject.EpsEnvy
import RequestProject.TPSApprox
import RequestProject.TPSCompute

/-!
# Theorem 2 (SEFX half) for instances without sellable goods

This file proves, **without any unproved hypothesis**, the second half of the manuscript's
Theorem 2 in the special case in which every good has price `0`:

> If `p ≡ 0`, every allocation instance admits a (partial) allocation that gives every agent at
> least `n/(2n−1)` of its truncated proportional share and is `SEFX`.

With `p ≡ 0` the notion `SEFX` of Definition 4 is the usual `EFX`, and no money changes hands,
so the whole difficulty of the general case — bundles that carry sale proceeds, and the
bookkeeping of the value that is lost when a good is turned into money — disappears.  What
remains is the combinatorial heart of the manuscript's Algorithm 6, and it is proved here in a
form that repairs the two gaps of the manuscript's argument (see `ISSUES_TPS_SEFX.md`):

* every bundle that is handed out is **minimal**: no good can be dropped from it without making
  it worthless to *every* agent (not only to the agents that already hold a bundle);
* consequently no agent — including the agents that are served later — envies it up to any good.

## The proof

Instead of running the algorithm, we argue *variationally*, which removes the need for the
manuscript's `ε`-progress and termination argument altogether.  A **state** consists of a set
`T` of served agents together with pairwise disjoint bundles `A i` (empty outside `T`) such that

* every served agent reaches its threshold `τ i = n/(2n−1)·TPS i` (`GoodSt.share`), and
* every bundle is *safe*: for every good `g` of a served bundle `A i` and every agent `j`, agent
  `j` values `A i \ {g}` at most at its *guarantee* `θ j` — the value of its own bundle if it is
  served, and `τ j` if it is not yet (`GoodSt.safe`).

States are finitely many, so we may pick one maximizing `|T|` and, among those, the total value
`∑ i, v i (A i)`.  If some agent were unserved, the counting argument of Algorithm 4 (each safe
bundle is worth at most `2τ j` to an unserved agent `j`, so the unallocated goods are worth at
least `(2m−1)τ j ≥ τ j` to it) would produce a claimed set of unallocated goods, and shrinking it
to a minimal claimed set would produce a strictly better state — a contradiction.  Hence every
agent is served, and safety is exactly `SEFX`.
-/

open scoped BigOperators

namespace FairSelling

namespace ZeroPrice

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Minimal claimed sets -/

/-- **Shrinking to a minimal claimed set.**  Any set with a property `P` contains a subset with
`P` from which no single element can be removed while keeping `P`. -/
theorem exists_minimal_sub {α : Type*} [DecidableEq α] (P : Finset α → Prop) :
    ∀ (B : Finset α), P B → ∃ C ⊆ B, P C ∧ ∀ g ∈ C, ¬ P (C.erase g) := by
  intro B
  induction B using Finset.strongInduction with
  | _ B ih =>
    intro hB
    by_cases h : ∃ g ∈ B, P (B.erase g)
    · obtain ⟨g, hg, hPg⟩ := h
      obtain ⟨C, hCsub, hC, hCmin⟩ := ih (B.erase g) (Finset.erase_ssubset hg) hPg
      exact ⟨C, hCsub.trans (Finset.erase_subset _ _), hC, hCmin⟩
    · push_neg at h
      exact ⟨B, Finset.Subset.refl _, hB, h⟩

/-! ### States -/

/-- The value of a bundle for an agent with valuation `w`. -/
def bval (w : G → ℝ) (S : Finset G) : ℝ := ∑ g ∈ S, w g

/-- The threshold `τ i = n/(2n−1)·TPS i` of agent `i`. -/
noncomputable def thr (v : Fin n → G → ℝ) (p : G → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p

/-- A state of the allocation process: the set of served agents and their bundles. -/
abbrev St (G : Type*) (n : ℕ) := Finset (Fin n) × (Fin n → Finset G)

/-- The *guarantee* of agent `j` in the state `s`: the value of its own bundle if it is served,
and its threshold if it is not (it will end up with at least its threshold). -/
noncomputable def theta (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) (j : Fin n) : ℝ :=
  if j ∈ s.1 then bval (v j) (s.2 j) else thr v p j

/-- The state is *legitimate*: bundles are empty outside `T` and pairwise disjoint, every served
agent reaches its threshold, and every bundle is safe (removing any good from it leaves it below
the guarantee of every agent). -/
def GoodSt (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) : Prop :=
  (∀ i, i ∉ s.1 → s.2 i = ∅) ∧
  (∀ i j, i ≠ j → Disjoint (s.2 i) (s.2 j)) ∧
  (∀ i ∈ s.1, thr v p i ≤ bval (v i) (s.2 i)) ∧
  (∀ i ∈ s.1, ∀ j : Fin n, ∀ g ∈ s.2 i, bval (v j) ((s.2 i).erase g) ≤ theta v p s j)

/-- The empty state is legitimate. -/
theorem GoodSt_empty (v : Fin n → G → ℝ) (p : G → ℝ) :
    GoodSt v p ((∅ : Finset (Fin n)), fun _ => (∅ : Finset G)) := by
  refine ⟨fun i _ => rfl, fun i j _ => by simp, fun i hi => absurd hi (by simp), ?_⟩
  intro i hi
  exact absurd hi (by simp)

omit [Fintype G] [DecidableEq G] in
/-- With zero prices the modified valuation `v̄` is the valuation itself. -/
theorem vbarSum_eq_bval (w p : G → ℝ) (hp0 : ∀ g, p g = 0) (hw : ∀ g, 0 ≤ w g) (S : Finset G) :
    vbarSum w p S = bval w S := by
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp [vbar, hp0 g, max_eq_right (hw g)]

/-! ### The counting argument -/

/-- The unallocated goods of a state. -/
def pool (s : St G n) : Finset G := Finset.univ \ (Finset.univ.biUnion s.2)

/-- **Each safe bundle is worth at most `2τ j` to an unserved agent `j`** (measured through the
truncated contributions).  This is the property that keeps the counting argument of Algorithm 4
alive. -/
theorem truncBundle_le_two_thr (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    {i : Fin n} (hi : i ∈ s.1) {j : Fin n} (hj : j ∉ s.1) :
    truncBundle (v j) p (TPS n (v j) p) (s.2 i) ≤ 2 * thr v p j := by
  classical
  have hp : ∀ g, 0 ≤ p g := fun g => le_of_eq (hp0 g).symm
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  set t := TPS n (v j) p with ht
  have ht0 : 0 ≤ t := TPS_nonneg (v j) p hp
  have hthr : thr v p j = ((n : ℝ) / (2 * n - 1)) * t := rfl
  have hthr0 : 0 ≤ thr v p j := by
    rw [hthr]; exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) ht0
  have htle : t ≤ 2 * thr v p j := by
    rw [hthr]
    have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) / (2 * n - 1)) := by
      rw [show (2 : ℝ) * ((n : ℝ) / (2 * n - 1)) = (2 * n) / (2 * n - 1) by ring,
        le_div_iff₀ hden]
      linarith
    nlinarith
  have htrunc_le_v : ∀ g, trunc (v j) p t g ≤ v j g := by
    intro g
    simp only [trunc, hp0 g]
    exact max_le (hv j g) (min_le_left _ _)
  have htrunc_le_t : ∀ g, trunc (v j) p t g ≤ t := by
    intro g
    simp only [trunc, hp0 g]
    exact max_le ht0 (min_le_right _ _)
  have hsum_le : truncBundle (v j) p t (s.2 i) ≤ bval (v j) (s.2 i) :=
    Finset.sum_le_sum (fun g _ => htrunc_le_v g)
  have htheta : theta v p s j = thr v p j := by simp [theta, hj]
  set A := s.2 i with hA
  rcases Finset.eq_empty_or_nonempty A with hempty | ⟨g, hg⟩
  · rw [hempty]
    simp only [truncBundle, Finset.sum_empty]
    linarith
  · by_cases hsingle : A = {g}
    · rw [hsingle]
      simp only [truncBundle, Finset.sum_singleton]
      exact le_trans (htrunc_le_t g) htle
    · have hnsub : ¬ A ⊆ {g} := fun hsub =>
        hsingle (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hg))
      obtain ⟨h, hh, hhg⟩ := Finset.not_subset.mp hnsub
      have hhne : h ≠ g := by simpa using hhg
      have hsplit : bval (v j) (A.erase g) + v j g = bval (v j) A :=
        Finset.sum_erase_add A _ hg
      have hsafe_g : bval (v j) (A.erase g) ≤ thr v p j := by
        have := hs.2.2.2 i hi j g hg
        rwa [htheta] at this
      have hsafe_h : bval (v j) (A.erase h) ≤ thr v p j := by
        have := hs.2.2.2 i hi j h hh
        rwa [htheta] at this
      have hgh : g ∈ A.erase h := Finset.mem_erase.mpr ⟨Ne.symm hhne, hg⟩
      have hvg : v j g ≤ bval (v j) (A.erase h) :=
        Finset.single_le_sum (f := v j) (fun x _ => hv j x) hgh
      have : bval (v j) A ≤ 2 * thr v p j := by linarith
      linarith

/-- **The counting argument.**  If some agent is unserved, the unallocated goods are worth at
least its threshold to it. -/
theorem thr_le_pool (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    {j : Fin n} (hj : j ∉ s.1) :
    thr v p j ≤ bval (v j) (pool s) := by
  classical
  have hp : ∀ g, 0 ≤ p g := fun g => le_of_eq (hp0 g).symm
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  set t := TPS n (v j) p with ht
  have ht0 : 0 ≤ t := TPS_nonneg (v j) p hp
  have hthr : thr v p j = ((n : ℝ) / (2 * n - 1)) * t := rfl
  have hthr0 : 0 ≤ thr v p j := by
    rw [hthr]; exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) ht0
  have hthr_eq : (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * t := by
    rw [hthr]; field_simp
  -- the total truncated value is `n · TPS`
  have htotal : ∑ g : G, trunc (v j) p t g = (n : ℝ) * t := by
    have hfix : truncSum n (v j) p t = t := TPS_truncSum (v j) p hp
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    unfold truncSum at hfix
    field_simp at hfix
    simpa [trunc] using hfix
  -- split the goods into the pool and the assigned bundles
  set U : Finset G := Finset.univ.biUnion s.2 with hU
  have hUsub : U ⊆ Finset.univ := Finset.subset_univ _
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint s.2 := by
    intro a _ b _ hab
    exact hs.2.1 a b hab
  have hsplit : ∑ g ∈ pool s, trunc (v j) p t g + ∑ g ∈ U, trunc (v j) p t g
      = ∑ g : G, trunc (v j) p t g := Finset.sum_sdiff hUsub
  have hbi : ∑ g ∈ U, trunc (v j) p t g
      = ∑ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g := Finset.sum_biUnion hdisj
  -- each assigned bundle costs at most `2τ`
  have hcost : ∀ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g
      ≤ if i ∈ s.1 then 2 * thr v p j else 0 := by
    intro i
    by_cases hi : i ∈ s.1
    · simp only [hi, if_true]
      exact truncBundle_le_two_thr v p hp0 hv hn s hs hi hj
    · simp only [hi, if_false, hs.1 i hi, Finset.sum_empty, le_refl]
  have hcostsum : ∑ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g
      ≤ (s.1.card : ℝ) * (2 * thr v p j) := by
    calc ∑ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g
        ≤ ∑ i : Fin n, if i ∈ s.1 then 2 * thr v p j else 0 :=
          Finset.sum_le_sum (fun i _ => hcost i)
      _ = (s.1.card : ℝ) * (2 * thr v p j) := by
          rw [Finset.sum_ite_mem]
          simp [Finset.sum_const]
  -- the number of served agents is at most `n - 1`
  have hcard : (s.1.card : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : s.1.card < n := by
      have : s.1 ⊂ Finset.univ := by
        refine Finset.ssubset_univ_iff.mpr (fun hcon => ?_)
        exact hj (hcon ▸ Finset.mem_univ j)
      simpa using Finset.card_lt_card this
    have : (s.1.card : ℝ) < (n : ℝ) := by exact_mod_cast h1
    have h2 : s.1.card + 1 ≤ n := h1
    have : ((s.1.card : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  -- the pool retains at least `τ`
  have hpoolt : thr v p j ≤ ∑ g ∈ pool s, trunc (v j) p t g := by
    have := hsplit
    rw [hbi, htotal] at this
    nlinarith [hcostsum, hcard, hthr0, hthr_eq]
  refine le_trans hpoolt (Finset.sum_le_sum (fun g _ => ?_))
  simp only [trunc, hp0 g]
  exact max_le (hv j g) (min_le_left _ _)

/-! ### The improvement step -/

/-- An agent *claims* a set of goods if it is unserved and the set meets its threshold, or it is
served and the set is strictly better than its current bundle. -/
def Claims (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) (B : Finset G) (k : Fin n) : Prop :=
  if k ∈ s.1 then bval (v k) (s.2 k) < bval (v k) B else thr v p k ≤ bval (v k) B

/-- A set is claimed if some agent claims it. -/
def Claimed (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) (B : Finset G) : Prop :=
  ∃ k, Claims v p s B k

/-- **The improvement step.**  From a legitimate state in which some agent is unserved one can
build a legitimate state that serves one more agent, or serves the same agents with a strictly
larger total value. -/
theorem exists_better (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    (hT : s.1 ≠ Finset.univ) :
    ∃ s' : St G n, GoodSt v p s' ∧
      (s.1.card < s'.1.card ∨
        (s'.1.card = s.1.card ∧ ∑ i, bval (v i) (s.2 i) < ∑ i, bval (v i) (s'.2 i))) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ s.1 := by
    by_contra hcon
    push_neg at hcon
    exact hT (Finset.eq_univ_iff_forall.mpr hcon)
  -- the pool is claimed by the unserved agent `j`
  have hclaimpool : Claimed v p s (pool s) := by
    refine ⟨j, ?_⟩
    simp only [Claims, hj, if_false]
    exact thr_le_pool v p hp0 hv hn s hs hj
  obtain ⟨C, hCsub, hCclaim, hCmin⟩ := exists_minimal_sub (Claimed v p s) (pool s) hclaimpool
  obtain ⟨k, hk⟩ := hCclaim
  -- `C` is disjoint from every assigned bundle
  have hCdisj : ∀ i, Disjoint C (s.2 i) := by
    intro i
    refine Finset.disjoint_left.mpr (fun g hgC hgi => ?_)
    have hmem := hCsub hgC
    simp only [pool, Finset.mem_sdiff, Finset.mem_biUnion] at hmem
    exact hmem.2 ⟨i, Finset.mem_univ i, hgi⟩
  -- minimality, in the form needed for safety
  have hmin : ∀ g ∈ C, ∀ m : Fin n, bval (v m) (C.erase g) ≤ theta v p s m := by
    intro g hg m
    have hnc : ¬ Claims v p s (C.erase g) m := fun hc => hCmin g hg ⟨m, hc⟩
    by_cases hms : m ∈ s.1
    · simp only [Claims, hms, if_true, not_lt] at hnc
      simpa [theta, hms] using hnc
    · simp only [Claims, hms, if_false, not_le] at hnc
      simp only [theta, hms, if_false]
      exact le_of_lt hnc
  set A' : Fin n → Finset G := Function.update s.2 k C with hA'def
  have hA'k : A' k = C := by simp [hA'def]
  have hA'ne : ∀ i, i ≠ k → A' i = s.2 i := by
    intro i hi
    simp [hA'def, Function.update_of_ne hi]
  have hdisj' : ∀ i j : Fin n, i ≠ j → Disjoint (A' i) (A' j) := by
    intro a b hab
    by_cases hak : a = k
    · subst hak
      rw [hA'k, hA'ne b (Ne.symm hab)]
      exact hCdisj b
    · by_cases hbk : b = k
      · subst hbk
        rw [hA'k, hA'ne a hak]
        exact (hCdisj a).symm
      · rw [hA'ne a hak, hA'ne b hbk]
        exact hs.2.1 a b hab
  by_cases hks : k ∈ s.1
  · -- the claimant already holds a bundle: it exchanges it for `C`
    have hgain : bval (v k) (s.2 k) < bval (v k) C := by
      simpa [Claims, hks] using hk
    have hthrk : thr v p k ≤ bval (v k) C := le_trans (hs.2.2.1 k hks) (le_of_lt hgain)
    have hthetamono : ∀ m, theta v p s m ≤ theta v p (s.1, A') m := by
      intro m
      by_cases hmk : m = k
      · subst hmk
        simp only [theta, hks, if_true, hA'k]
        exact le_of_lt hgain
      · by_cases hms : m ∈ s.1 <;> simp [theta, hms, hA'ne m hmk]
    refine ⟨(s.1, A'), ⟨?_, hdisj', ?_, ?_⟩, Or.inr ⟨rfl, ?_⟩⟩
    · intro i hi
      dsimp only at hi ⊢
      have hik : i ≠ k := fun h => hi (h ▸ hks)
      rw [hA'ne i hik]
      exact hs.1 i hi
    · intro i hi
      dsimp only at hi ⊢
      by_cases hik : i = k
      · subst hik; rw [hA'k]; exact hthrk
      · rw [hA'ne i hik]; exact hs.2.2.1 i hi
    · intro i hi m g hg
      dsimp only at hi hg ⊢
      by_cases hik : i = k
      · subst hik
        rw [hA'k] at hg ⊢
        exact le_trans (hmin g hg m) (hthetamono m)
      · rw [hA'ne i hik] at hg ⊢
        exact le_trans (hs.2.2.2 i hi m g hg) (hthetamono m)
    · have h1 : ∑ i, bval (v i) (A' i)
          = bval (v k) C + ∑ i ∈ Finset.univ.erase k, bval (v i) (s.2 i) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hA'k]
        refine congrArg _ (Finset.sum_congr rfl (fun i hi => ?_))
        rw [hA'ne i (Finset.mem_erase.mp hi).1]
      have h2 : ∑ i, bval (v i) (s.2 i)
          = bval (v k) (s.2 k) + ∑ i ∈ Finset.univ.erase k, bval (v i) (s.2 i) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
      simp only [h1, h2]
      linarith
  · -- the claimant is unserved: it is served now
    have hthrk : thr v p k ≤ bval (v k) C := by
      simpa [Claims, hks] using hk
    have hthetamono : ∀ m, theta v p s m ≤ theta v p (insert k s.1, A') m := by
      intro m
      by_cases hmk : m = k
      · subst hmk
        simp only [theta, Finset.mem_insert, true_or, if_true, hks, if_false, hA'k]
        exact hthrk
      · by_cases hms : m ∈ s.1 <;>
          simp [theta, hms, hA'ne m hmk, Finset.mem_insert, hmk]
    refine ⟨(insert k s.1, A'), ⟨?_, hdisj', ?_, ?_⟩, Or.inl ?_⟩
    · intro i hi
      dsimp only at hi ⊢
      have hik : i ≠ k := fun h => hi (by simp [h])
      rw [hA'ne i hik]
      exact hs.1 i (fun hcon => hi (Finset.mem_insert_of_mem hcon))
    · intro i hi
      dsimp only at hi ⊢
      by_cases hik : i = k
      · subst hik; rw [hA'k]; exact hthrk
      · rw [hA'ne i hik]
        exact hs.2.2.1 i ((Finset.mem_insert.mp hi).resolve_left hik)
    · intro i hi m g hg
      dsimp only at hi hg ⊢
      by_cases hik : i = k
      · subst hik
        rw [hA'k] at hg ⊢
        exact le_trans (hmin g hg m) (hthetamono m)
      · rw [hA'ne i hik] at hg ⊢
        exact le_trans
          (hs.2.2.2 i ((Finset.mem_insert.mp hi).resolve_left hik) m g hg) (hthetamono m)
    · simpa using Finset.card_lt_card (Finset.ssubset_insert hks)

/-! ### The theorem -/

/-- **Theorem 2 (SEFX half) for instances in which no good has a price.**  Every allocation
instance with `p ≡ 0` admits a valid outcome that gives every agent at least `n/(2n−1)` of its
truncated proportional share and is `SEFX`. -/
theorem exists_TPS_SEFX_of_prices_zero (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp0 : ∀ g, p g = 0) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  -- the legitimate states form a nonempty finite set
  set S : Finset (St G n) := Finset.univ.filter (fun s => GoodSt v p s) with hSdef
  have hSne : S.Nonempty :=
    ⟨((∅ : Finset (Fin n)), fun _ => (∅ : Finset G)), by
      simp [hSdef, GoodSt_empty v p]⟩
  -- first maximize the number of served agents
  obtain ⟨s₁, hs₁S, hmax₁⟩ := S.exists_max_image (fun s => s.1.card) hSne
  set S₂ : Finset (St G n) := S.filter (fun s => s.1.card = s₁.1.card) with hS₂def
  have hS₂ne : S₂.Nonempty := ⟨s₁, by simp [hS₂def, hs₁S]⟩
  -- then the total value
  obtain ⟨s, hsS₂, hmax₂⟩ :=
    S₂.exists_max_image (fun s => ∑ i, bval (v i) (s.2 i)) hS₂ne
  have hsS : s ∈ S := (Finset.mem_filter.mp hsS₂).1
  have hscard : s.1.card = s₁.1.card := (Finset.mem_filter.mp hsS₂).2
  have hsgood : GoodSt v p s := (Finset.mem_filter.mp hsS).2
  -- every agent is served
  have hfull : s.1 = Finset.univ := by
    by_contra hne
    obtain ⟨s', hgood', hbetter⟩ := exists_better v p hp0 hv hn s hsgood hne
    have hs'S : s' ∈ S := by simp [hSdef, hgood']
    rcases hbetter with hcard | ⟨hcard, hval⟩
    · have := hmax₁ s' hs'S
      omega
    · have hs'S₂ : s' ∈ S₂ := by
        simp only [hS₂def, Finset.mem_filter]
        exact ⟨hs'S, by omega⟩
      exact absurd (hmax₂ s' hs'S₂) (not_le.mpr hval)
  -- the outcome
  refine ⟨⟨∅, s.2, fun _ => 0⟩, ⟨fun j => by simp, fun j k hjk => hsgood.2.1 j k hjk,
    fun j => le_rfl, by simp⟩, ?_, ?_⟩
  · intro i
    have hi : i ∈ s.1 := by rw [hfull]; exact Finset.mem_univ i
    have := hsgood.2.2.1 i hi
    simpa [util, thr, bval] using this
  · intro i j
    refine ⟨fun h => absurd h (by simp), fun _ => Or.inr (fun g hg => ?_)⟩
    have hj : j ∈ s.1 := by rw [hfull]; exact Finset.mem_univ j
    have hsafe := hsgood.2.2.2 j hj i g hg
    have hi : i ∈ s.1 := by rw [hfull]; exact Finset.mem_univ i
    have htheta : theta v p s i = bval (v i) (s.2 i) := by simp [theta, hi]
    rw [htheta] at hsafe
    have h1 : vbarSum (v i) p (s.2 i) = bval (v i) (s.2 i) :=
      vbarSum_eq_bval (v i) p hp0 (hv i) _
    have h2 : vbarSum (v i) p ((s.2 j) \ {g}) = bval (v i) ((s.2 j).erase g) := by
      rw [Finset.sdiff_singleton_eq_erase]
      exact vbarSum_eq_bval (v i) p hp0 (hv i) _
    show vbarSum (v i) p (s.2 i) + 0 ≥ vbarSum (v i) p ((s.2 j) \ {g}) + p g
    rw [h1, h2, hp0 g]
    linarith

end ZeroPrice

end FairSelling
