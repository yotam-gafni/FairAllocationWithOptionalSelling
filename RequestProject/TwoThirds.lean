import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.TPSApprox
import RequestProject.TwoThirdsCanonical
import RequestProject.TwoThirdsLoss
import RequestProject.TwoThirdsLemma9

/-!
# Theorem 3 for general `n`: the `2/3`-MMS approximation

This file assembles the manuscript's Algorithm 1 (`APX-MMS-2/3`) and its analysis:

* `servable_stage1` — the first loop of the preliminary phase: while some available good is
  priced above the threshold of some active agent, sell it and pay its threshold to the active
  agent of *lowest* maximin share;
* `servable_stage2` — the second loop: while some active agent values an available good above its
  threshold, hand the good over to that agent;
* `servable_of_inv` — the main loop: the active agent of highest maximin share proposes a
  canonical partition, the matching phase serves at least one agent, and the induction proceeds
  on the (strictly smaller) set of active agents;
* `exists_twothirds_MMS_of_equiMMS`, `exists_twothirds_MMS` — **Theorem 3** (general `n`): every
  allocation instance with optional selling admits a valid outcome giving every agent at least
  `2/3` of its maximin share.

Everything here is proved: the three combinatorial statements the induction rests on are Lemma 9
(`RequestProject.TwoThirdsLemma9`), Proposition 5 (`RequestProject.TwoThirdsLoss`) and Lemma 6
(`RequestProject.EquiMMS`), all of which are proved in those files.  The full-allocation form of
Theorem 3 is `exists_twothirds_MMS_full` in `RequestProject.TwoThirdsFull`.
-/

open scoped BigOperators

namespace FairSelling

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

omit [Fintype G] [DecidableEq G] in
/-- When no agent is active there is nothing to do. -/
lemma servable_empty (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ) (R : Finset G) {D : ℝ}
    (hD : 0 ≤ D) : Servable v p τ (∅ : Finset (Fin n)) R D := by
  refine ⟨fun _ => ∅, ∅, fun _ => 0, fun _ => Finset.empty_subset _, Finset.empty_subset _,
    fun i j _ => by simp, fun i => by simp, fun i => le_refl 0, ?_, fun i hi => absurd hi (by simp),
    fun i _ => ⟨rfl, rfl⟩⟩
  simpa using hD

/-! ### The main loop -/

/-- **The main loop of Algorithm 1.**  From a state satisfying the invariant, all the active
agents can be served.  The induction is on the number of active agents: the agent of highest
maximin share proposes a canonical partition (Lemma 9), the matching phase serves at least that
agent (`round_outcome`), and the invariant is restored on the smaller state (Proposition 5). -/
theorem servable_of_inv (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → Inv v p T R D →
      Servable v p (thr v p) T R D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro T R D hcard hInv
    obtain ⟨hD, hL, hsmall⟩ := hInv
    rcases Finset.eq_empty_or_nonempty T with rfl | hT
    · exact servable_empty v p _ R hD
    · obtain ⟨i, hiT, hmax⟩ := Finset.exists_max_image T (fun a => MMS n (v a) p) hT
      have hm : 0 < m := by
        rw [← hcard]; exact Finset.card_pos.mpr hT
      haveI : NeZero m := ⟨by omega⟩
      obtain ⟨C⟩ := canonical_of_inv v p hv hp ⟨hD, hL, hsmall⟩ hiT hmax hcard
      refine servable_of_round v p (thr v p) hiT hcard C ?_
      intro Kset part hiK hKT hinj hloss hspecial hzero
      set J : Finset (Fin m) := Kset.image part with hJ
      have hDnew : 0 ≤ D + (∑ g ∈ C.sold J, p g) - ∑ j ∈ J, C.cash j := by
        have := C.cash_sum_le J
        linarith
      have hcardnew : (T \ Kset).card < m := by
        have h1 : (T \ Kset).card ≤ (T.erase i).card := by
          refine Finset.card_le_card ?_
          intro a ha
          rcases Finset.mem_sdiff.mp ha with ⟨haT, haK⟩
          exact Finset.mem_erase.mpr ⟨fun h => haK (h ▸ hiK), haT⟩
        have h2 : (T.erase i).card = m - 1 := by
          rw [Finset.card_erase_of_mem hiT, hcard]
        omega
      refine IH _ hcardnew (T \ Kset) _ _ rfl ⟨hDnew, ?_, ?_⟩
      · exact losses_of_round v p ⟨hD, hL, hsmall⟩ hmax C Kset part hKT hinj hloss hspecial hzero
      · intro a ha g hg
        exact hsmall a (Finset.mem_sdiff.mp ha).1 g (Finset.mem_sdiff.mp hg).1

/-! ### The preliminary phase -/

/-- **The second stage of the preliminary phase.**  While some active agent values an available
good above its threshold, hand the good over to that agent.  When no such good is left, and given
that the first stage is over, no available good is worth as much as the threshold to an active
agent, so the invariant of the main loop holds. -/
theorem servable_stage2 (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      Losses v p T R D → (∀ a ∈ T, ∀ e ∈ R, p e < thr v p a) →
      Servable v p (thr v p) T R D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro T R D hcard hD hL hstage1
    by_cases hex : ∃ i ∈ T, ∃ g ∈ R, thr v p i ≤ v i g
    · obtain ⟨i, hiT, g, hgR, hval⟩ := hex
      have hcardnew : (T.erase i).card < m := by
        rw [Finset.card_erase_of_mem hiT, hcard]
        have : 0 < m := by rw [← hcard]; exact Finset.card_pos.mpr ⟨i, hiT⟩
        omega
      refine servable_extend v p (thr v p) i hiT {g} ∅ 0 ?_ (Finset.empty_subset _)
        (by simp) le_rfl ?_ ?_
      · simpa using hgR
      · have : vbarSum (v i) p {g} = vbar (v i) p g := by simp [vbarSum]
        rw [this, add_zero]
        exact hval.trans (le_max_right _ _)
      · have hR : R \ ({g} ∪ (∅ : Finset G)) = R.erase g := by
          simp [Finset.sdiff_singleton_eq_erase]
        rw [hR]
        simp only [Finset.sum_empty, add_zero, sub_zero]
        refine IH _ hcardnew _ _ _ rfl hD ?_ ?_
        · exact losses_of_stage2 v p hL hstage1 hiT hgR
        · intro a ha e he
          exact hstage1 a (Finset.mem_of_mem_erase ha) e (Finset.mem_of_mem_erase he)
    · push_neg at hex
      refine servable_of_inv v p hv hp m T R D hcard ⟨hD, hL, ?_⟩
      intro a haT g hgR
      have h1 : p g < thr v p a := hstage1 a haT g hgR
      have h2 : v a g < thr v p a := hex a haT g hgR
      simp only [vbar]
      exact max_lt h1 h2

/-- **The first stage of the preliminary phase.**  While some available good is priced above the
threshold of some active agent, sell it and pay its threshold to the active agent of lowest
maximin share (which, having the lowest threshold, is also happy with that good's price). -/
theorem servable_stage1 (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      Losses v p T R D → Servable v p (thr v p) T R D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro T R D hcard hD hL
    by_cases hex : ∃ i ∈ T, ∃ g ∈ R, thr v p i ≤ p g
    · obtain ⟨i, hiT, g, hgR, hprice⟩ := hex
      obtain ⟨j, hjT, hmin⟩ :=
        Finset.exists_min_image T (fun a => MMS n (v a) p) ⟨i, hiT⟩
      have hthr : thr v p j ≤ p g := (thr_le_thr v p (hmin i hiT)).trans hprice
      have hthr0 : 0 ≤ thr v p j := thr_nonneg v p hn hv hp j
      have hcardnew : (T.erase j).card < m := by
        rw [Finset.card_erase_of_mem hjT, hcard]
        have : 0 < m := by rw [← hcard]; exact Finset.card_pos.mpr ⟨j, hjT⟩
        omega
      refine servable_extend v p (thr v p) j hjT ∅ {g} (thr v p j) (Finset.empty_subset _) ?_
        (by simp) hthr0 ?_ ?_
      · simpa using hgR
      · simp [vbarSum]
      · have hR : R \ ((∅ : Finset G) ∪ {g}) = R.erase g := by
          simp [Finset.sdiff_singleton_eq_erase]
        rw [hR]
        simp only [Finset.sum_singleton]
        refine IH _ hcardnew _ _ _ rfl (by linarith) ?_
        exact losses_of_stage1 v p hL hjT hmin hgR hthr hthr0
    · push_neg at hex
      exact servable_stage2 v p hv hp m T R D hcard hD hL (fun a ha e he => hex a ha e he)

/-! ### Theorem 3 -/

/-- **Theorem 3 (general `n`), for instances in which every agent has an equi-valued MMS
partition.**  Every such instance admits a valid outcome giving every agent at least `2/3` of its
maximin share. -/
theorem exists_twothirds_MMS_of_equiMMS (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hE : ∀ i, Nonempty (EquiMMS (v i) p (MMS n (v i) p) n)) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨A, F, q, hAR, hFR, hAdisj, hFdisj, hq0, hqsum, hserve, _⟩ :=
    servable_stage1 v p hn hv hp n Finset.univ Finset.univ 0 (by simp) le_rfl
      (losses_initial v p hE)
  refine ⟨unifiedOutcome v p A F q, ?_, ?_⟩
  · refine unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 ?_
    simpa using hqsum
  · intro i
    rw [util_unifiedOutcome]
    exact hserve i (Finset.mem_univ i)

/-- **Theorem 3 (general `n`).**  Every allocation instance with optional selling admits a valid
outcome giving every agent at least `2/3` of its maximin share.

(For `n = 3` the stronger `3/4` bound of `exists_threequarter_MMS_three` is available, and for
`n = 2` the exact maximin share is achievable, `exists_MMS_two`.) -/
theorem exists_twothirds_MMS (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨v', hv'0, hv'le, hv'MMS, hv'E⟩ := exists_readjustment v p hn hv hp
  obtain ⟨o, hovalid, ho⟩ := exists_twothirds_MMS_of_equiMMS v' p hn hv'0 hp hv'E
  refine ⟨o, hovalid, fun i => ?_⟩
  have h1 : util (v' i) o i ≤ util (v i) o i := by
    unfold util
    have : ∑ g ∈ o.kept i, v' i g ≤ ∑ g ∈ o.kept i, v i g :=
      Finset.sum_le_sum (fun g _ => hv'le i g)
    linarith
  have h2 := ho i
  rw [hv'MMS i] at h2
  linarith

end FairSelling
