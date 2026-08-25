import Mathlib
import RequestProject.TPSSefxStep
import RequestProject.TPSSefxPhaseImp
import RequestProject.TPSSefxPotImp
import RequestProject.TPSApprox

/-!
# Theorem 2

> **Theorem 2.** Every allocation instance has an `n/(2n−1)`-TPS allocation.  Moreover, every
> allocation instance has an allocation that is both `n/(2n−1)`-TPS and SEFX.

The first half is `FairSelling.exists_TPS_approx` (proved in `RequestProject/TPSApprox.lean`).

The second half is assembled here out of the development of the previous files, following
Algorithm 6 with the **per-good ledger** of `RequestProject/TPSSefxPot.lean`:

* `PotTPS.exists_TPS_SEFX_of_Qstep` reduces it to the improvement step of Algorithm 6 for the
  ledger stages `PotTPS.QStage`;
* `PotTPS.qimprovementStep` splits that step into the manuscript's loops: the large-good loop,
  in which an expensive pool good is sold and only a slice of its proceeds is handed out, the
  rest staying in the *pot* of that good (`PotTPS.qsell_step`); the cutting of a further slice
  out of a pot that is already big enough to serve somebody (`PotTPS.qcut_step`); and the
  bag-filling loop, run on the *free* bank (`PotTPS.qbagfill_step`);
* every one of those steps goes through `PotTPS.qstep_assign`, which hands a package to an agent
  and releases the agent's old package — the manuscript's `Unshrink` — **unconditionally**,
  including when the agent holds a slice of a shared good.

Both halves are fully proved.

The earlier, superseded bookkeeping of `RequestProject/TPSSefxPhase.lean` could not release an
agent holding a slice of a shared good; that step survives there as the explicit assumption
`PhaseTPS.PCarrierReassign`, and `ISSUES_THEOREM2.md` explains why an anonymous bank cannot
support it.  Nothing below depends on it.
-/

open scoped BigOperators

namespace FairSelling

variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

namespace ChargeTPS

/- **Superseded.**  The first attempt at Algorithm 6 isolated its *stealing* case as
`ChargeTPS.CStealStep`, a statement about the charged stages of
`RequestProject/TPSSefxCharge.lean`, and left it unproved:

```
theorem csteal_step (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps) : CStealStep v p eps := by
  sorry

theorem cimprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps) : CImprovementStep v p eps :=
  cimprovementStep_of_steal v p eps hn hp heps.le (csteal_step v p eps hn hp heps)
```

The stealing case is now *proved*, in the form the manuscript's algorithm actually needs.  The
phase-structured states of `RequestProject/TPSSefxPhase.lean` record, for every served agent,
which of the sold goods it financed out of its own package, and `PhaseTPS.pstep_assign` releases
such a package unconditionally; the release of an agent holding a slice of a *shared* good then
needed the per-good ledger of `RequestProject/TPSSefxPot.lean`, where it is
`PotTPS.qstep_assign`.  The declarations above are kept here, commented out, only to record what
they used to say. -/

end ChargeTPS

/-- **Theorem 2, second half.**  Every allocation instance admits a valid outcome that gives
every agent at least `n/(2n−1)` of its truncated proportional share and is SEFX. -/
theorem theorem_two_SEFX (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o :=
  PotTPS.exists_TPS_SEFX_of_Qstep v p hn hp
    (fun eps heps => PotTPS.qimprovementStep v p eps hn hp heps.le)

/-- **Theorem 2.**  Every allocation instance has an `n/(2n−1)`-TPS allocation, and moreover it
has an allocation that is both `n/(2n−1)`-TPS and SEFX. -/
theorem theorem_two (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    (∃ o : Outcome G n, o.Valid p ∧
      ∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧
    (∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o) :=
  ⟨exists_TPS_approx v p hn hp, theorem_two_SEFX v p hn hp⟩

end FairSelling
