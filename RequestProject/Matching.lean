import Mathlib

/-!
# Hall's theorem for three agents (the matching step of the `n = 3` algorithm)

The manuscript's `3/4`-MMS algorithm for `n = 3` (Section C.1) runs, after a partitioning agent
proposes a `3`-partition of the goods, *one iteration of a matching procedure*: each agent
"accepts" a bundle if it values it at least `3/4 · MMS`.  Two structural facts are used.

* The *partitioning agent accepts every bundle* (it proposed the partition, each part is worth
  at least `3/4 · MMS` to it).
* *No agent rejects all three bundles*: an agent rejecting all three would value the whole set of
  goods below `3 · (3/4) · MMS < 3 · MMS`, contradicting the value-counting bound.

The paper then invokes Hall's theorem to conclude that the matching either saturates all three
agents (a *perfect matching*), or leaves a single loss event: exactly one bundle is allocated to
one agent and the two other agents reject that bundle.

Since `n = 3`, this "Hall for three" statement is a finite combinatorial fact about a
`3 × 3` bipartite acceptability relation, and is proved here by exhaustive case analysis
(`decide`).  It is stated abstractly for an arbitrary boolean acceptability relation
`acc : Fin 3 → Fin 3 → Bool` (agent `j` accepts bundle `k` iff `acc j k = true`), so that it can
be instantiated with the concrete "values at least `3/4 · MMS`" relation.
-/

namespace FairSelling

set_option maxRecDepth 4000

/-- **Hall's theorem for three agents (matching step, `n = 3`).**
Let `acc j k` record whether agent `j` accepts bundle `k`.  Assume the partitioning agent `pa`
accepts every bundle, and that no agent rejects all three bundles.  Then either

* there is a **perfect matching**: a permutation `σ` of `Fin 3` with agent `j` accepting bundle
  `σ j` for every `j`; or
* there is a **single loss event**: a bundle `k` accepted by the partitioning agent `pa` but
  rejected by both other agents.

This is the `n = 3` special case of Hall's marriage theorem that drives the matching step of the
manuscript's `3/4`-MMS algorithm, proved by exhaustive case analysis. -/
theorem matching_fin3 (acc : Fin 3 → Fin 3 → Bool) (pa : Fin 3)
    (hpa : ∀ k, acc pa k = true)
    (hnorej : ∀ j, ∃ k, acc j k = true) :
    (∃ σ : Equiv.Perm (Fin 3), ∀ j, acc j (σ j) = true)
    ∨ (∃ k, acc pa k = true ∧ ∀ j, j ≠ pa → acc j k = false) := by
  revert acc pa
  decide

end FairSelling
