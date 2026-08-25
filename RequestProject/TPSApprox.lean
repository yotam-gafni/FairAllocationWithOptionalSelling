import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.TPSCompute

/-!
# The `n/(2n-1)`-TPS approximation

This file formalizes the first half of Theorem 2 of the manuscript (Lemma 2 and Lemma 12 of
Appendix E): *every allocation instance with optional selling admits an allocation giving each
agent at least `n/(2n−1)` of its truncated proportional share*.

The manuscript's Algorithm 4 (`APX-TPS`) proceeds in three loops: sell an expensive good and pay
one agent its threshold out of the proceeds; hand a whole good to an agent that values it above
its threshold; and finally bag-fill.  Its analysis (Lemma 12) maintains the invariant that after
`k` agents have been served, every still-active agent values what is left at
`(n − 2nk/(2n−1))·TPS`.

Writing `τ i = n/(2n−1)·TPS i` for agent `i`'s threshold, that invariant takes the pleasant
form: *with `m` agents still active, every active agent `i` values the remaining goods (measured
by the truncated contributions `max{p(g), min{v_i(g), TPS_i}}`) plus the banked sale proceeds at
least `(2m−1)·τ i`*.  Each step of the algorithm serves one agent while costing every other
active agent at most `2·τ i` of that quantity, which is exactly what keeps the invariant alive.

This is the induction carried out here:

* `Servable` — the statement that a set `T` of agents can each be given their threshold out of a
  set `R` of remaining goods together with `D` units of banked cash;
* `servable_extend` — serving one agent and recursing;
* `servable_of_invariant` — the induction itself (the three loops of Algorithm 4 appear as the
  three cases of its step);
* `exists_TPS_approx` — the resulting theorem, in terms of `Outcome`.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Truncated contributions -/

/-- The truncated contribution `max{p(g), min{w(g), t}}` of the good `g`. -/
def trunc (w p : G → ℝ) (t : ℝ) (g : G) : ℝ := max (p g) (min (w g) t)

/-- The truncated value of a bundle. -/
def truncBundle (w p : G → ℝ) (t : ℝ) (R : Finset G) : ℝ := ∑ g ∈ R, trunc w p t g

omit [Fintype G] [DecidableEq G] in
lemma trunc_le_vbar (w p : G → ℝ) (t : ℝ) (g : G) : trunc w p t g ≤ vbar w p g :=
  max_le_max_left _ (min_le_left _ _)

omit [Fintype G] [DecidableEq G] in
lemma trunc_le_max (w p : G → ℝ) (t : ℝ) (g : G) : trunc w p t g ≤ max (p g) t :=
  max_le_max_left _ (min_le_right _ _)

omit [Fintype G] [DecidableEq G] in
lemma trunc_nonneg (w p : G → ℝ) (t : ℝ) (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ trunc w p t g :=
  le_trans (hp g) (le_max_left _ _)

omit [Fintype G] [DecidableEq G] in
lemma truncBundle_le_vbarSum (w p : G → ℝ) (t : ℝ) (R : Finset G) :
    truncBundle w p t R ≤ vbarSum w p R :=
  Finset.sum_le_sum (fun g _ => trunc_le_vbar w p t g)

omit [Fintype G] [DecidableEq G] in
lemma truncBundle_nonneg (w p : G → ℝ) (t : ℝ) (hp : ∀ g, 0 ≤ p g) (R : Finset G) :
    0 ≤ truncBundle w p t R :=
  Finset.sum_nonneg (fun g _ => trunc_nonneg w p t hp g)

omit [Fintype G] in
lemma truncBundle_sdiff (w p : G → ℝ) (t : ℝ) {R X : Finset G} (h : X ⊆ R) :
    truncBundle w p t R = truncBundle w p t (R \ X) + truncBundle w p t X :=
  (Finset.sum_sdiff h).symm

/-! ### The state of the algorithm -/

/-- `Servable v p τ T R D` says that each agent in `T` can be given a bundle taken from the goods
`R` (which it may keep or sell) together with a share of the banked cash `D` and of the proceeds
of some force-sold goods, so that every agent `i ∈ T` reaches its threshold `τ i`.  Agents
outside `T` receive nothing. -/
def Servable (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    (T : Finset (Fin n)) (R : Finset G) (D : ℝ) : Prop :=
  ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
    (∀ i, A i ⊆ R) ∧ F ⊆ R ∧
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ D + ∑ g ∈ F, p g) ∧
    (∀ i ∈ T, τ i ≤ vbarSum (v i) p (A i) + q i) ∧
    (∀ i, i ∉ T → A i = ∅ ∧ q i = 0)

omit [Fintype G] in
/-- Serving one agent `j` a bundle `B` of goods plus `a` units of money (raised from the banked
cash and from force-selling the goods `F₀`), and then serving the remaining agents out of what is
left. -/
lemma servable_extend (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (j : Fin n) (hj : j ∈ T) (B F₀ : Finset G) (a : ℝ)
    (hB : B ⊆ R) (hF₀ : F₀ ⊆ R) (hBF : Disjoint B F₀)
    (ha : 0 ≤ a) (hserve : τ j ≤ vbarSum (v j) p B + a)
    (hrec : Servable v p τ (T.erase j) (R \ (B ∪ F₀)) (D + (∑ g ∈ F₀, p g) - a)) :
    Servable v p τ T R D := by
  classical
  obtain ⟨A', F', q', hA'R, hF'R, hA'disj, hF'disj, hq'0, hq'sum, hq'serve, hq'out⟩ := hrec
  have hjout := hq'out j (Finset.notMem_erase j T)
  refine ⟨Function.update A' j B, F' ∪ F₀, Function.update q' j a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = j
    · subst h; simpa using hB
    · rw [Function.update_of_ne h]
      exact Finset.Subset.trans (hA'R i) Finset.sdiff_subset
  · exact Finset.union_subset (Finset.Subset.trans hF'R Finset.sdiff_subset) hF₀
  · intro i k hik
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, Function.update_of_ne (Ne.symm hik)]
      exact Finset.disjoint_left.mpr (fun x hxB hxA => by
        have := hA'R k hxA
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inl hxB))
    · by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_of_ne hi]
        exact Finset.disjoint_right.mpr (fun x hxB hxA => by
          have := hA'R i hxA
          simp only [Finset.mem_sdiff, Finset.mem_union] at this
          exact this.2 (Or.inl hxB))
      · rw [Function.update_of_ne hi, Function.update_of_ne hk]
        exact hA'disj i k hik
  · intro i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      refine Finset.disjoint_left.mpr (fun x hx hxB => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · have := hF'R hx
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inl hxB)
      · exact Finset.disjoint_left.mp hBF hxB hx
    · rw [Function.update_of_ne hi]
      refine Finset.disjoint_left.mpr (fun x hx hxA => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (hF'disj i) hx hxA
      · have := hA'R i hxA
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inr hx)
  · intro i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]; exact ha
    · rw [Function.update_of_ne hi]; exact hq'0 i
  · have hsum : ∑ i, Function.update q' j a i = (∑ i, q' i) - q' j + a := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
      have : ∑ i ∈ Finset.univ \ {j}, q' i = (∑ i, q' i) - q' j := by
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
        simp
      rw [this]; ring
    have hFsum : ∑ g ∈ F' ∪ F₀, p g = (∑ g ∈ F', p g) + ∑ g ∈ F₀, p g := by
      refine Finset.sum_union ?_
      refine Finset.disjoint_left.mpr (fun x hx hx₀ => ?_)
      have := hF'R hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at this
      exact this.2 (Or.inr hx₀)
    rw [hsum, hFsum, hjout.2]
    linarith [hq'sum]
  · intro i hi
    by_cases h : i = j
    · subst h; rw [Function.update_self, Function.update_self]; exact hserve
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      exact hq'serve i (Finset.mem_erase.mpr ⟨h, hi⟩)
  · intro i hi
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
    exact hq'out i (fun h => hi (Finset.mem_of_mem_erase h))

/-! ### The bag-filling step -/

omit [Fintype G] in
open Classical in
/-- Bag filling: if every remaining good is worth less than its threshold to every active agent,
and some active agent can be satisfied by all of the goods plus the banked cash, then there is a
*nonempty* bundle `B` and an active agent `j` that reaches its threshold on `B` plus the cash,
while every active agent values `B` plus the cash at less than twice its own threshold. -/
lemma exists_minimal_bag (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    (T : Finset (Fin n)) (R : Finset G) (D : ℝ)
    (hsmall : ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < τ i)
    (hD : ∀ i ∈ T, D < τ i)
    (j₀ : Fin n) (hj₀ : j₀ ∈ T) (hfull : τ j₀ ≤ vbarSum (v j₀) p R + D) :
    ∃ (B : Finset G) (j : Fin n), B ⊆ R ∧ j ∈ T ∧
      τ j ≤ vbarSum (v j) p B + D ∧
      ∀ i ∈ T, vbarSum (v i) p B + D < 2 * τ i := by
  classical
  set S := R.powerset.filter (fun B => ∃ i ∈ T, τ i ≤ vbarSum (v i) p B + D) with hSdef
  have hRS : R ∈ S := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl R, ⟨j₀, hj₀, hfull⟩⟩
  obtain ⟨B, hBS, hBmin⟩ := Finset.exists_min_image S Finset.card ⟨R, hRS⟩
  have hBR : B ⊆ R := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_powerset] at hBS; exact hBS.1
  obtain ⟨j, hjT, hjB⟩ : ∃ i ∈ T, τ i ≤ vbarSum (v i) p B + D := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_powerset] at hBS; exact hBS.2
  have hBne : B.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B with h | h
    · exfalso
      rw [h] at hjB
      simp only [vbarSum, Finset.sum_empty, zero_add] at hjB
      exact absurd hjB (not_le.mpr (hD j hjT))
    · exact h
  obtain ⟨g, hgB⟩ := hBne
  have hgR : g ∈ R := hBR hgB
  have herase : B.erase g ∉ S := by
    intro hmem
    have := hBmin _ hmem
    have hlt : (B.erase g).card < B.card := Finset.card_erase_lt_of_mem hgB
    omega
  have hno : ∀ i ∈ T, vbarSum (v i) p (B.erase g) + D < τ i := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    exact herase (by
      simp only [hSdef, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.trans (Finset.erase_subset _ _) hBR, ⟨i, hi, hcon⟩⟩)
  refine ⟨B, j, hBR, hjT, hjB, ?_⟩
  intro i hi
  have hsplit : vbarSum (v i) p B = vbarSum (v i) p (B.erase g) + vbar (v i) p g := by
    unfold vbarSum
    rw [← Finset.sum_erase_add B _ hgB]
  have h1 := hno i hi
  have h2 := hsmall i hi g hgR
  linarith [hsplit]

/-! ### The induction -/

omit [Fintype G] in
open Classical in
/-- **The engine of Algorithm 4.**  If, with `m` agents still active, every active agent values
the remaining goods (through its truncated contributions) plus the banked cash at least
`(2m−1)·τ i`, then all active agents can be served their thresholds.  The three cases of the
proof are the three loops of the manuscript's Algorithm 4. -/
theorem servable_of_invariant (v : Fin n → G → ℝ) (p : G → ℝ) (τ t : Fin n → ℝ) (hτ : ∀ i, 0 ≤ τ i) (ht : ∀ i, t i ≤ 2 * τ i) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      (∀ i ∈ T, (2 * (m : ℝ) - 1) * τ i ≤ truncBundle (v i) p (t i) R + D) →
      Servable v p τ T R D := by
  classical
  intro m
  induction m with
  | zero =>
    intro T R D hcard hD _
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun _ => ∅, ∅, fun _ => 0, fun _ => Finset.empty_subset _,
      Finset.empty_subset _, fun _ _ _ => by simp, fun _ => by simp, fun _ => le_refl 0, ?_, ?_,
      fun _ _ => ⟨rfl, rfl⟩⟩
    · simp [hD]
    · intro i hi; rw [hT] at hi; exact absurd hi (Finset.notMem_empty i)
  | succ m ih =>
    intro T R D hcard hD hinv
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    -- an active agent of least threshold
    obtain ⟨i₀, hi₀T, hi₀min⟩ := Finset.exists_min_image T τ hTne
    have hcard' : (T.erase i₀).card = m := by
      rw [Finset.card_erase_of_mem hi₀T, hcard]; rfl
    -- the invariant needs to be re-established with `m` active agents
    have hstep : ∀ (j : Fin n) (X : Finset G) (dD : ℝ), X ⊆ R →
        (∀ i ∈ T.erase j, truncBundle (v i) p (t i) X + dD ≤ 2 * τ i) →
        ∀ i ∈ T.erase j, (2 * (m : ℝ) - 1) * τ i
            ≤ truncBundle (v i) p (t i) (R \ X) + (D - dD) := by
      intro j X dD hX hloss i hi
      have h1 := hinv i (Finset.mem_of_mem_erase hi)
      have h2 := truncBundle_sdiff (v i) p (t i) hX
      have h3 := hloss i hi
      push_cast at h1 ⊢
      linarith
    by_cases hcase1 : ∃ g ∈ R, ∃ k ∈ T, τ k ≤ p g
    · -- Loop 1: sell an expensive good, pay the least-threshold agent
      obtain ⟨g, hgR, k, hkT, hgk⟩ := hcase1
      have hpg : τ i₀ ≤ p g := le_trans (hi₀min k hkT) hgk
      refine servable_extend v p τ i₀ hi₀T ∅ {g} (τ i₀) (Finset.empty_subset _)
        (Finset.singleton_subset_iff.mpr hgR) (by simp) (hτ i₀)
        (by simp [vbarSum]) ?_
      have hDD : D + (∑ x ∈ ({g} : Finset G), p x) - τ i₀ = D - (τ i₀ - p g) := by
        simp; ring
      have hXsub : ({g} : Finset G) ⊆ R := Finset.singleton_subset_iff.mpr hgR
      have hEq : R \ (∅ ∪ ({g} : Finset G)) = R \ ({g} : Finset G) := by simp
      rw [hDD, hEq]
      refine ih _ _ _ hcard' (by simp; linarith) ?_
      refine hstep i₀ _ _ hXsub ?_
      intro i hi
      have hτi : 0 ≤ τ i := hτ i
      have hle : trunc (v i) p (t i) g ≤ max (p g) (t i) := trunc_le_max _ _ _ _
      have hi₀le : τ i₀ ≤ τ i := hi₀min i (Finset.mem_of_mem_erase hi)
      have hti := ht i
      simp only [truncBundle, Finset.sum_singleton]
      rcases max_cases (p g) (t i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hle <;> linarith
    · push_neg at hcase1
      by_cases hcase2 : ∃ g ∈ R, ∃ k ∈ T, τ k ≤ v k g
      · -- Loop 2: hand a highly valued good to the agent that values it
        obtain ⟨g, hgR, k, hkT, hgk⟩ := hcase2
        refine servable_extend v p τ k hkT {g} ∅ 0
          (Finset.singleton_subset_iff.mpr hgR) (Finset.empty_subset _) (by simp) (le_refl 0)
          ?_ ?_
        · simp only [vbarSum, Finset.sum_singleton, vbar, add_zero]
          exact le_trans hgk (le_max_right _ _)
        · have hDD : D + (∑ x ∈ (∅ : Finset G), p x) - 0 = D - 0 := by simp
          have hEq : R \ (({g} : Finset G) ∪ ∅) = R \ ({g} : Finset G) := by simp
          rw [hDD, hEq]
          refine ih _ _ _ (by rw [Finset.card_erase_of_mem hkT, hcard]; rfl) (by linarith) ?_
          refine hstep k _ _ (Finset.singleton_subset_iff.mpr hgR) ?_
          intro i hi
          have hiT := Finset.mem_of_mem_erase hi
          have hle : trunc (v i) p (t i) g ≤ max (p g) (t i) := trunc_le_max _ _ _ _
          have hpg := hcase1 g hgR i hiT
          have hti := ht i
          have hτi : 0 ≤ τ i := hτ i
          simp only [truncBundle, Finset.sum_singleton, add_zero]
          rcases max_cases (p g) (t i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hle <;> linarith
      · push_neg at hcase2
        by_cases hcase3 : τ i₀ ≤ D
        · -- enough banked cash to pay the least-threshold agent outright
          refine servable_extend v p τ i₀ hi₀T ∅ ∅ (τ i₀) (Finset.empty_subset _)
            (Finset.empty_subset _) (by simp) (hτ i₀) (by simp [vbarSum]) ?_
          have hDD : D + (∑ x ∈ (∅ : Finset G), p x) - τ i₀ = D - τ i₀ := by simp
          have hEq : R \ ((∅ : Finset G) ∪ ∅) = R \ (∅ : Finset G) := by simp
          rw [hDD, hEq]
          refine ih _ _ _ hcard' (by linarith) ?_
          refine hstep i₀ _ _ (Finset.empty_subset _) ?_
          intro i hi
          have hi₀le : τ i₀ ≤ τ i := hi₀min i (Finset.mem_of_mem_erase hi)
          have hτi : 0 ≤ τ i := hτ i
          simp only [truncBundle, Finset.sum_empty, zero_add]
          linarith
        · -- Loop 3: bag filling
          push_neg at hcase3
          have hsmall : ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < τ i := by
            intro i hi g hg
            exact max_lt (hcase1 g hg i hi) (hcase2 g hg i hi)
          have hDlt : ∀ i ∈ T, D < τ i := by
            intro i hi
            exact lt_of_lt_of_le hcase3 (hi₀min i hi)
          have hfull : τ i₀ ≤ vbarSum (v i₀) p R + D := by
            have h1 := hinv i₀ hi₀T
            have h2 := truncBundle_le_vbarSum (v i₀) p (t i₀) R
            have h3 : (1:ℝ) ≤ 2 * ((m:ℝ) + 1) - 1 := by
              have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
              linarith
            have h4 : τ i₀ ≤ (2 * ((m:ℝ) + 1) - 1) * τ i₀ := by
              nlinarith [hτ i₀]
            push_cast at h1
            linarith
          obtain ⟨B, k, hBR, hkT, hkserve, hkloss⟩ :=
            exists_minimal_bag v p τ T R D hsmall hDlt i₀ hi₀T hfull
          refine servable_extend v p τ k hkT B ∅ D hBR (Finset.empty_subset _) (by simp) hD
            (by linarith [hkserve]) ?_
          have hDD : D + (∑ x ∈ (∅ : Finset G), p x) - D = D - D := by simp
          have hEq : R \ (B ∪ (∅ : Finset G)) = R \ B := by simp
          rw [hDD, hEq]
          refine ih _ _ _ (by rw [Finset.card_erase_of_mem hkT, hcard]; rfl) (by simp) ?_
          refine hstep k _ _ hBR ?_
          intro i hi
          have hiT := Finset.mem_of_mem_erase hi
          have h1 := hkloss i hiT
          have h2 := truncBundle_le_vbarSum (v i) p (t i) B
          linarith

/-! ### The approximation theorem -/

/-- **Theorem 2 of the manuscript (the TPS half).**  Every allocation instance with optional
selling admits a valid outcome giving every agent at least `n/(2n−1)` of its truncated
proportional share. -/
theorem exists_TPS_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      ∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i := by
  classical
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  set τ : Fin n → ℝ := fun i => ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p with hτdef
  set t : Fin n → ℝ := fun i => TPS n (v i) p with htdef
  have hTPS0 : ∀ i, 0 ≤ TPS n (v i) p := fun i => TPS_nonneg (v i) p hp
  have hτ0 : ∀ i, 0 ≤ τ i := by
    intro i
    exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) (hTPS0 i)
  have htτ : ∀ i, t i ≤ 2 * τ i := by
    intro i
    simp only [hτdef, htdef]
    rw [show (2:ℝ) * (((n : ℝ) / (2 * n - 1)) * TPS n (v i) p)
        = ((2 * n) / (2 * n - 1)) * TPS n (v i) p by field_simp]
    have h1 : (1:ℝ) ≤ (2 * n) / (2 * n - 1) := by
      rw [le_div_iff₀ hden]; linarith
    nlinarith [hTPS0 i]
  -- the initial invariant
  have hinit : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (2 * ((n : ℝ)) - 1) * τ i ≤ truncBundle (v i) p (t i) Finset.univ + 0 := by
    intro i _
    have hfix : truncSum n (v i) p (TPS n (v i) p) = TPS n (v i) p := TPS_truncSum (v i) p hp
    have hsum : truncBundle (v i) p (t i) Finset.univ = (n : ℝ) * TPS n (v i) p := by
      unfold truncBundle trunc
      unfold truncSum at hfix
      rw [htdef]
      field_simp at hfix
      linarith [hfix]
    rw [hsum, add_zero, hτdef]
    field_simp
    exact le_rfl
  obtain ⟨A, F, q, hAR, hFR, hAdisj, hFdisj, hq0, hqsum, hserve, _⟩ :=
    servable_of_invariant v p τ t hτ0 htτ n Finset.univ Finset.univ 0 (by simp) (le_refl 0)
      hinit
  refine ⟨unifiedOutcome v p A F q, ?_, ?_⟩
  · refine unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 ?_
    simpa using hqsum
  · intro i
    rw [util_unifiedOutcome]
    exact hserve i (Finset.mem_univ i)

end FairSelling
