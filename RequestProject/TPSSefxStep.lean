import Mathlib
import RequestProject.TPSSefxConfig

/-!
# The improvement step of Algorithm 6

This file carries out the improvement step of Algorithm 6 for a charged stage.  Given a good
charged stage `s` with some agent still unserved:

* the pool together with the bank is *feasible* — the counting invariant, which
  `ChargeTPS.counting_of_cost` derives from the local cost bound, says exactly that some unserved
  agent reaches its threshold on the whole pool plus the whole bank (`feas_pool`);
* hence `CfgTPS.exists_min_adm` produces a package `(S, S₀)` with a footprint of least size that
  is *admissible*: nobody envies it up to any set of goods;
* `package_of_claimant` turns that package into one that its claimant is willing to *keep*: every
  good the claimant values below its price is moved from the kept part to the sold part.  This
  changes neither the footprint nor the cost, and it can only improve safety;
* if some *unserved* agent claims the package, `ChargeTPS.step_serve` hands it over and one more
  agent is served — this is `cstep_of_unserved_claimant`, and it is the bag-filling case of
  Algorithm 6.

The remaining case — every claimant is already served, so the package has to be *stolen* and the
thief's old package released — is the `Unshrink` step of Algorithm 6.  It is isolated as
`CStealStep` and is the one thing left unproved; `ISSUES_THEOREM2.md` explains precisely what is
missing and why.
-/

open scoped BigOperators

namespace FairSelling

namespace ChargeTPS

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### Elementary facts about the requirements of a stage -/

section Req

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

omit [Fintype G] [DecidableEq G] in
lemma vbarSum_nonneg_of_price (hp : ∀ g, 0 ≤ p g) (u : G → ℝ) (A : Finset G) :
    0 ≤ vbarSum u p A :=
  Finset.sum_nonneg (fun g _ => le_trans (hp g) (le_max_left _ _))

lemma req_nonneg (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : CStage G n}
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j := by
  unfold CStage.req
  by_cases hj : j ∈ s.served
  · simp only [if_pos hj]
    have h1 : 0 ≤ vbarSum (v j) p (s.bundle j) := vbarSum_nonneg_of_price p hp _ _
    have h2 : 0 ≤ s.cash j := hs.2.2.2.2.1 j
    linarith
  · simp only [if_neg hj]
    exact GeneralTPS.thr_nonneg v p hn hp j

omit [DecidableEq G] in
lemma req_eq_thr {s : CStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by
  simp [CStage.req, hj]

omit [DecidableEq G] in
/-- The threshold is at most the TPS. -/
lemma thr_le_TPS (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    GeneralTPS.thr v p j ≤ TPS n (v j) p := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0:ℝ) ≤ TPS n (v j) p := TPS_nonneg (v j) p hp
  unfold GeneralTPS.thr
  have hfrac : (n : ℝ) / (2 * n - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  nlinarith

omit [DecidableEq G] in
/-- The TPS is at most twice the threshold. -/
lemma TPS_le_two_thr (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0:ℝ) ≤ TPS n (v j) p := TPS_nonneg (v j) p hp
  unfold GeneralTPS.thr
  have hfrac : (1:ℝ) ≤ 2 * ((n : ℝ) / (2 * n - 1)) := by
    rw [show 2 * ((n:ℝ) / (2 * n - 1)) = (2 * n) / (2 * n - 1) by ring,
      le_div_iff₀ (by linarith)]
    linarith
  nlinarith

end Req

/-! ### The pool is feasible -/

section Feas

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- **The pool is feasible.**  This is the counting invariant of Algorithm 4, read as a statement
about the package consisting of the whole pool: the cheapest cash supplement that makes somebody
claim the whole pool can be paid out of the bank. -/
theorem feas_pool (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served) :
    CfgTPS.Feas v p (s.req v p eps) k0 s.bank s.pool ∅ := by
  classical
  have hbank : 0 ≤ s.bank := hs.2.2.2.2.2.2.1
  have hcount := counting_of_cost v p eps hn hp hs k0 hk0
  have hthr : 0 ≤ GeneralTPS.thr v p k0 := GeneralTPS.thr_nonneg v p hn hp k0
  have hcard : (s.served.card : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : s.served.card < n := by
      have h2 : s.served ⊂ Finset.univ := by
        refine ⟨Finset.subset_univ _, fun h => hk0 (h (Finset.mem_univ k0))⟩
      have := Finset.card_lt_card h2
      simpa using this
    have : (s.served.card : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hmul : GeneralTPS.thr v p k0
      ≤ (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p k0 := by
    nlinarith
  have hle : truncBundle (v k0) p (TPS n (v k0) p) s.pool ≤ vbarSum (v k0) p s.pool :=
    truncBundle_le_vbarSum _ _ _ _
  have hreq : s.req v p eps k0 = GeneralTPS.thr v p k0 := req_eq_thr v p eps hk0
  unfold CfgTPS.Feas
  simp only [Finset.sum_empty, add_zero]
  refine CfgTPS.Qc_le_of_gap v p (s.req v p eps) k0 hbank k0 ?_
  rw [hreq]
  linarith

end Feas

/-! ### Making the claimant keep the goods it is given -/

section Package

variable (v : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)

omit [Fintype G] in
/-- **The owner-keeps post-processing.**  Given an admissible package `(S, S₀)` and an agent `k`
that claims it, move every good that `k` values below its price from the kept part to the sold
part.  The result is a package with the same footprint and the same cost, still claimed by `k`,
which `k` is willing to keep, and which is safe for everybody. -/
theorem package_of_claimant (hp : ∀ g, 0 ≤ p g) {S S₀ : Finset G} (hdisj : Disjoint S S₀)
    (hadm : CfgTPS.Adm v p req k0 D S S₀) (k : Fin n)
    (hclaim : req k ≤ vbarSum (v k) p S + CfgTPS.Qc v p req k0 S) :
    ∃ (S' S₀' : Finset G) (q : ℝ),
      S' ⊆ S ∧ S₀ ⊆ S₀' ∧ S' ∪ S₀' = S ∪ S₀ ∧ Disjoint S' S₀' ∧
      0 ≤ q ∧ q ≤ D + ∑ g ∈ S₀', p g ∧
      req k ≤ vbarSum (v k) p S' + q ∧ (∀ g ∈ S', p g ≤ v k g) ∧
      (∀ m, (vbarSum (v m) p S' + q ≤ req m) ∨
        (q = 0 ∧ ∀ g ∈ S', vbarSum (v m) p (S' \ {g}) + p g ≤ req m)) ∧
      (∀ (t : ℝ) (u : G → ℝ),
        truncBundle u p t S' + q + ∑ g ∈ S₀', saleLoss u p t g
          = truncBundle u p t S + CfgTPS.Qc v p req k0 S + ∑ g ∈ S₀, saleLoss u p t g) := by
  classical
  set Q := CfgTPS.Qc v p req k0 S with hQ
  set X : Finset G := S.filter (fun g => v k g < p g) with hX
  have hXS : X ⊆ S := Finset.filter_subset _ _
  have hXS₀ : Disjoint X S₀ := Finset.disjoint_of_subset_left hXS hdisj
  have hpX : 0 ≤ ∑ g ∈ X, p g := Finset.sum_nonneg (fun g _ => hp g)
  have hQ0 : 0 ≤ Q := CfgTPS.Qc_nonneg v p req k0 S
  refine ⟨S \ X, S₀ ∪ X, Q + ∑ g ∈ X, p g, Finset.sdiff_subset, Finset.subset_union_left, ?_, ?_,
    by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · -- same footprint
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hx : x ∈ X
    · have := hXS hx; tauto
    · tauto
  · -- disjointness
    refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
    · exact Finset.sdiff_disjoint
  · -- affordable
    have hsum : ∑ g ∈ S₀ ∪ X, p g = (∑ g ∈ S₀, p g) + ∑ g ∈ X, p g :=
      Finset.sum_union hXS₀.symm
    have := hadm.1
    unfold CfgTPS.Feas at this
    rw [hsum]
    rw [← hQ] at this
    linarith
  · -- the claimant still claims
    have hsplit : vbarSum (v k) p S = vbarSum (v k) p (S \ X) + ∑ g ∈ X, vbar (v k) p g := by
      unfold vbarSum
      exact (Finset.sum_sdiff hXS).symm
    have hXp : ∑ g ∈ X, vbar (v k) p g = ∑ g ∈ X, p g := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      have : v k g < p g := (Finset.mem_filter.mp hg).2
      exact max_eq_left (le_of_lt this)
    rw [hXp] at hsplit
    linarith
  · -- the claimant keeps the goods
    intro g hg
    have hgS : g ∈ S := (Finset.mem_sdiff.mp hg).1
    have hgX : g ∉ X := (Finset.mem_sdiff.mp hg).2
    have : ¬ (v k g < p g) := by
      intro h
      exact hgX (Finset.mem_filter.mpr ⟨hgS, h⟩)
    linarith [not_lt.mp this]
  · -- safety
    intro m
    rcases Finset.eq_empty_or_nonempty X with hXe | hXne
    · -- nothing was moved
      have hSe : S \ X = S := by rw [hXe]; simp
      have hqe : Q + ∑ g ∈ X, p g = Q := by rw [hXe]; simp
      rcases eq_or_lt_of_le hQ0 with hQz | hQpos
      · right
        refine ⟨by rw [hqe, ← hQz], ?_⟩
        intro g hg
        rw [hSe] at hg ⊢
        have := hadm.2 {g} (Finset.singleton_subset_iff.mpr hg) ⟨g, by simp⟩ m
        simp only [Finset.sum_singleton] at this
        rw [← hQ, ← hQz] at this
        simpa using this
      · left
        rw [hSe, hqe]
        have := CfgTPS.Qc_safe v p req k0 (S := S) (by rw [← hQ]; exact hQpos) m
        rw [← hQ] at this
        exact this
    · left
      have := hadm.2 X hXS hXne m
      rw [← hQ] at this
      linarith
  · -- the cost is unchanged
    intro t u
    have h1 : truncBundle u p t S = truncBundle u p t (S \ X) + truncBundle u p t X :=
      truncBundle_sdiff u p t hXS
    have h2 : ∑ g ∈ S₀ ∪ X, saleLoss u p t g
        = (∑ g ∈ S₀, saleLoss u p t g) + ∑ g ∈ X, saleLoss u p t g :=
      Finset.sum_union hXS₀.symm
    have h3 : ∑ g ∈ X, saleLoss u p t g = truncBundle u p t X - ∑ g ∈ X, p g :=
      sum_saleLoss u p t X
    rw [h2, h3]
    linarith

end Package

/-! ### Serving one more agent -/

section CaseA

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- **The bag-filling case of the improvement step.**  If the minimal admissible package built out
of the pool is claimed by an agent that is not yet served, then handing it over serves one more
agent. -/
theorem cstep_of_unserved_claimant (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : CStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    {S S₀ : Finset G} (hUP : S ∪ S₀ ⊆ s.pool) (hdisj : Disjoint S S₀)
    (hadm : CfgTPS.Adm v p (s.req v p eps) k0 s.bank S S₀)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ s.pool → Disjoint T T₀ →
      CfgTPS.Adm v p (s.req v p eps) k0 s.bank T T₀ →
      (S ∪ S₀).card * (s.pool.card + 1) + S₀.card
        ≤ (T ∪ T₀).card * (s.pool.card + 1) + T₀.card)
    {k : Fin n} (hk : k ∉ s.served)
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + CfgTPS.Qc v p (s.req v p eps) k0 S) :
    ∃ s' : CStage G n, s'.Good v p eps ∧ s.served.card < s'.served.card := by
  classical
  obtain ⟨S', S₀', q, hS'S, hS₀S₀', hfoot, hdisj', hq0, hqle, hclaim', hkeep, hsafe, hcosteq⟩ :=
    package_of_claimant v p (s.req v p eps) k0 s.bank hp hdisj hadm k hclaim
  have hS'pool : S' ⊆ s.pool :=
    Finset.Subset.trans (Finset.Subset.trans hS'S Finset.subset_union_left) hUP
  have hS₀'pool : S₀' ⊆ s.pool := by
    intro x hx
    exact hUP (hfoot ▸ Finset.mem_union_right S' hx)
  have hbank : 0 ≤ s.bank + (∑ g ∈ S₀', p g) - q - 0 := by linarith
  refine step_serve v p eps heps hs hk hS'pool hS₀'pool hdisj' hq0 le_rfl hbank ?_ hkeep ?_ ?_
  · rw [← req_eq_thr v p eps hk]; exact hclaim'
  · intro j _
    exact hsafe j
  · intro j hj _
    have hreqj : s.req v p eps j = GeneralTPS.thr v p j := req_eq_thr v p eps hj
    have hcost := CfgTPS.cost_bound (w := v) (p := p) (req := s.req v p eps) (k0 := k0)
      (D := s.bank) (P := s.pool) (S := S) (S₀ := S₀)
      (fun i => TPS n (v i) p) j hp hs.2.2.2.2.2.2.1
      (req_nonneg v p eps hn hp heps hs)
      (by rw [hreqj]; exact thr_le_TPS v p hn hp j)
      (by rw [hreqj]; exact TPS_le_two_thr v p hn hp j)
      hUP hdisj hadm hmin
    rw [hreqj] at hcost
    have := hcosteq (TPS n (v j) p) (v j)
    simp only [add_zero]
    linarith

end CaseA

/-! ### The remaining case: stealing -/

section Steal

variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

/-- **The stealing step.**  The case of the improvement step of Algorithm 6 in which the package
built out of the pool is claimed only by agents that already hold a bundle.  The claimant then
takes the new package and releases its old one (`Unshrink`), and the total utility grows by at
least `ε`.

This is the one statement of the development that is left unproved; `ISSUES_THEOREM2.md`
describes exactly what extra bookkeeping it needs. -/
def CStealStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ (s : CStage G n) (k0 : Fin n), s.Good v p eps → k0 ∉ s.served →
    ∀ S S₀ : Finset G, S ∪ S₀ ⊆ s.pool → Disjoint S S₀ →
      CfgTPS.Adm v p (s.req v p eps) k0 s.bank S S₀ →
      (∀ T T₀ : Finset G, T ∪ T₀ ⊆ s.pool → Disjoint T T₀ →
        CfgTPS.Adm v p (s.req v p eps) k0 s.bank T T₀ →
        (S ∪ S₀).card * (s.pool.card + 1) + S₀.card
          ≤ (T ∪ T₀).card * (s.pool.card + 1) + T₀.card) →
      ∀ k : Fin n, k ∈ s.served →
        s.req v p eps k ≤ vbarSum (v k) p S + CfgTPS.Qc v p (s.req v p eps) k0 S →
        ∃ s' : CStage G n, s'.Good v p eps ∧
          (s.served.card < s'.served.card ∨
            (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))

/-- **The improvement step of Algorithm 6**, granted the stealing step. -/
theorem cimprovementStep_of_steal (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    (hsteal : CStealStep v p eps) : CImprovementStep v p eps := by
  classical
  intro s hs hfull
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ s.served := by
    by_contra hcon
    push_neg at hcon
    exact hfull (Finset.eq_univ_of_forall hcon)
  obtain ⟨S, S₀, hUP, hdisj, hadm, hmin⟩ :=
    CfgTPS.exists_min_adm v p (s.req v p eps) k0 s.bank s.pool hp
      (feas_pool v p eps hn hp hs hk0)
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 S
  by_cases hk : k ∈ s.served
  · exact hsteal s k0 hs hk0 S S₀ hUP hdisj hadm hmin k hk hclaim
  · obtain ⟨s', hs', hcard⟩ :=
      cstep_of_unserved_claimant v p eps hn hp heps hs hUP hdisj hadm hmin hk hclaim
    exact ⟨s', hs', Or.inl hcard⟩

end Steal

end ChargeTPS

end FairSelling
