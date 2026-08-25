import Mathlib
import RequestProject.Selling
import RequestProject.TPSCompute

/-!
# Sale proceeds have to be shared

The bookkeeping of Algorithm 6 (`RequestProject/TPSSefxCharge.lean`) charges every sold good to a
served agent, and the cleanest way to make the `Unshrink` operation of Algorithm 6 work would be
to insist that every agent can *buy back* the goods charged to it, i.e. that

```
   ∑_{g ∈ charge i} p g  ≤  cash i + resv i     (the package is self-financed)
```

for every served agent `i`, with the charges pairwise disjoint.  A self-financed agent releases
its package for free: it un-sells its charged goods with its own money, the bank never moves, and
the number of sold goods drops.

The instance below shows that this is **impossible in general**: there are instances in which
*every* outcome meeting the `n/(2n−1)`-TPS guarantee has to sell one single good and split its
proceeds between two agents.  With disjoint charges only one of the two agents can be charged
with that good, and that agent then holds strictly less money than the good's price.

## The instance

Two agents with the same valuation, four goods:

| good | `g₀` | `g₁` | `g₂` | `g₃` |
|------|------|------|------|------|
| `v`  | `10` | `1`  | `1`  | `1`  |
| `p`  | `10` | `0`  | `0`  | `0`  |

The truncated proportional share of each agent is `13/2` (`sharedTPS`), so the guarantee that
Theorem 2 asks for is `τ = (2/3)·(13/2) = 13/3`.

`sharing_needed` proves that in every valid outcome giving both agents at least `13/3`, the good
`g₀` is sold and **both** agents hold a strictly positive amount of its proceeds — indeed at
least `4/3` each.
-/

open scoped BigOperators

namespace FairSelling

namespace SharedProceeds

/-- The common valuation of the two agents. -/
noncomputable def sv : Fin 4 → ℝ := fun g => if g = 0 then 10 else 1

/-- The prices. -/
noncomputable def sp : Fin 4 → ℝ := fun g => if g = 0 then 10 else 0

lemma sp_nonneg : ∀ g, 0 ≤ sp g := by
  intro g; fin_cases g <;> norm_num [sp]

lemma sv_nonneg : ∀ g, 0 ≤ sv g := by
  intro g; fin_cases g <;> norm_num [sv, Fin.ext_iff]

lemma sum_vbar : ∑ g : Fin 4, max (sp g) (sv g) = 13 := by
  rw [Fin.sum_univ_four]
  norm_num [sv, sp, Fin.ext_iff]

/-- The truncated proportional share of each agent is `13/2`. -/
theorem sharedTPS : TPS 2 sv sp = 13 / 2 := by
  have hPS : PS 2 sv sp = 13 / 2 := by
    unfold PS
    rw [sum_vbar]
    norm_num
  refine le_antisymm ?_ ?_
  · have := TPS_le_PS (n := 2) sv sp sp_nonneg
    rw [hPS] at this
    exact this
  · refine le_TPS_of_le_truncSum sv sp ?_
    unfold truncSum
    rw [Fin.sum_univ_four]
    norm_num [sv, sp, Fin.ext_iff]

/-- The value of any bundle avoiding the big good is at most `3`. -/
lemma sum_le_three {A : Finset (Fin 4)} (hA : (0 : Fin 4) ∉ A) : ∑ g ∈ A, sv g ≤ 3 := by
  have hsub : A ⊆ ({1, 2, 3} : Finset (Fin 4)) := by
    intro x hx
    fin_cases x
    · exact absurd hx hA
    all_goals simp
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => sv_nonneg g)) ?_
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [sv, Fin.ext_iff]

/-- **Sale proceeds have to be shared.**  In every valid outcome for this instance that gives
both agents the guarantee `13/3 = (2/3)·TPS`, the good `g₀` is sold and both agents hold at least
`4/3` of its proceeds.  In particular no assignment of the sold good to a single "owner" can make
that owner able to buy the good back. -/
theorem sharing_needed (o : Outcome (Fin 4) 2) (hvalid : o.Valid sp)
    (hutil : ∀ i, (13 : ℝ) / 3 ≤ util sv o i) :
    (0 : Fin 4) ∈ o.sold ∧ ∀ i, (4 : ℝ) / 3 ≤ o.money i := by
  classical
  obtain ⟨hsk, hkk, hm0, hmsum⟩ := hvalid
  -- the big good must be sold
  have hsold : (0 : Fin 4) ∈ o.sold := by
    by_contra hcon
    -- with `g₀` unsold, no money is available at all
    have hmoney : ∑ i, o.money i ≤ 0 := by
      refine le_trans hmsum ?_
      refine le_of_eq ?_
      refine Finset.sum_eq_zero ?_
      intro g hg
      fin_cases g
      · exact absurd hg hcon
      all_goals norm_num [sp]
    have hm : ∀ i, o.money i = 0 := by
      intro i
      have h1 : (0:ℝ) ≤ ∑ j, o.money j := Finset.sum_nonneg (fun j _ => hm0 j)
      have h2 : o.money i ≤ ∑ j, o.money j :=
        Finset.single_le_sum (fun j _ => hm0 j) (Finset.mem_univ i)
      have := hm0 i
      linarith
    -- at most one agent keeps the big good
    have : ∃ i : Fin 2, (0 : Fin 4) ∉ o.kept i := by
      by_cases h0 : (0 : Fin 4) ∈ o.kept 0
      · refine ⟨1, fun h1 => ?_⟩
        exact Finset.disjoint_left.mp (hkk 0 1 (by decide)) h0 h1
      · exact ⟨0, h0⟩
    obtain ⟨i, hi⟩ := this
    have := hutil i
    unfold util at this
    rw [hm i] at this
    have := sum_le_three hi
    linarith [hutil i, sum_le_three hi]
  refine ⟨hsold, ?_⟩
  intro i
  have hi : (0 : Fin 4) ∉ o.kept i :=
    fun h => Finset.disjoint_left.mp (hsk i) hsold h
  have h1 := hutil i
  unfold util at h1
  have h2 := sum_le_three hi
  linarith

end SharedProceeds

end FairSelling
