# Issues found while formalizing Theorem 2, second half (`n/(2n−1)`-TPS **and** SEFX)

Theorem 2 of the manuscript has two halves.  The first one — *every allocation instance has an
`n/(2n−1)`-TPS allocation* — is fully formalized (`FairSelling.exists_TPS_approx`,
`RequestProject/TPSApprox.lean`).  This note is about the second one:

> Every allocation instance has an allocation that is both `n/(2n−1)`-TPS and SEFX.

It records what was proved, the errors and gaps found in the manuscript's argument (Appendix D.2,
Algorithms 5 and 6), the counterexamples that establish them, and how the gaps were eventually
closed.  **The second half is now proved in full** (`FairSelling.theorem_two_SEFX`,
`RequestProject/TPSSefxTheorem2.lean`); the repairs it needed are described in §5 here and in
`ISSUES_THEOREM2.md`.

## Summary of the state of the formalization

| statement | file | status |
|---|---|---|
| Theorem 2, SEFX half, for instances with `p ≡ 0` | `TPSSefxZero.lean` | **proved in full** |
| Theorem 2, SEFX half, for instances in which no agent values a good above its price | `TPSSefxGeneral.lean` | **proved in full** |
| Theorem 2, SEFX half, general case, reduced to one local `ImprovementStep` | `TPSSefxGeneral.lean` | **reduction proved in full** |
| the improvement step itself (the manuscript's Algorithm 6) | `TPSSefxPot.lean`, `TPSSefxPotStep.lean`, `TPSSefxPotImp.lean` | **proved in full** (`PotTPS.qimprovementStep`), with the per-good ledger described in `ISSUES_THEOREM2.md` |
| Theorem 2, SEFX half, general case | `TPSSefxTheorem2.lean` | **proved in full** (`theorem_two_SEFX`) |
| Theorem 2, both halves | `TPSSefxTheorem2.lean` | **proved in full** (`theorem_two`) |
| the invariant that Algorithm 5/6 maintains is too weak | `TPSSefxExamples.lean` | **counterexample formalized** |
| `MMS ≥ n/(2n−1)·TPS` (by-product) | `TPSSefx.lean` | proved |
| Lemma 11 with `ε-SEFXu` as input | `LemmaEleven.lean` | proved |

---

## 1. `Shrink` (Algorithm 5) protects only the agents that already hold a bundle

Line 3 of `Shrink` reads: *if `∃ i ∈ INACTIVE` so that `i` `ε`-SEFX-envies `X_shrink`* — where
`INACTIVE` is the set of agents that already hold a bundle.  An agent that is still `ACTIVE` when
a bundle is handed out is never consulted.  Consequently the invariant that Algorithm 6 maintains
("`ε`-SEFX holds among the agents that are allocated a bundle", as stated in the proof of
Theorem 2) does **not** imply that the final allocation is `ε`-SEFX: an agent may be served later
and then envy a bundle that was handed out while it was still active.

**Counterexample** (formalized in `RequestProject/TPSSefxExamples.lean`, namespace
`FairSelling.TPSSefxCounterexample`).  Two agents with the same valuation and four goods:

| good | `g₀` | `g₁` | `g₂` | `g₃` |
|------|------|------|------|------|
| `v`  | `0`  | `18` | `19` | `5`  |
| `p`  | `18` | `0`  | `0`  | `0`  |

Here `TPS = 30` for both agents, so the threshold used by the algorithm is `τ = (2/3)·30 = 20`.
No good has price `≥ 20` and no good is worth `≥ 20`, so the two large-good loops of Algorithm 6
do not fire and the algorithm bag-fills.  The bag `{g₀, g₁}` is worth `36 ≥ 20` and is minimal
(dropping either good leaves `18 < 20`).  It is handed to agent `0`; no agent holds a bundle yet,
so `Shrink` does nothing.  Then `{g₂, g₃}` (worth `24`) is handed to agent `1`, and agent `0` does
not `ε`-SEFX-envy it, so `Shrink` does nothing again.

The output is `(2/3)`-TPS (`exOutcome_TPS`), but agent `0` sells `g₀` (it values it at `0 < 18`),
so agent `0` holds money and Definition 4 asks for the **full** envy-free condition towards it.
Agent `1` has `24` and values agent `0`'s share at `18 + 18 = 36`.  The outcome is not `ε`-SEFX
for any `ε` (`exOutcome_not_epsSEFX`, `exOutcome_not_SEFX`).

The instance is *not* a counterexample to Theorem 2: `exGoodOutcome` sells `g₀`, splits the
proceeds `12/6`, and gives both agents exactly `30` — it is envy free, hence SEFX
(`exGoodOutcome_TPS_SEFX`).

### The fix

Shrink **unconditionally**, and shrink to a bundle that is minimal in the sub-bundle order,
irrespective of who envies it.  Write a *generalized bundle* as a pair `(S, a)` of a set of goods
and an amount of cash, and consider the two reductions

* `R1 : (S, a) → (S, a')` for `a' < a` (give back part of the proceeds);
* `R2 : (S, a) → (S \ {g}, a + p(g))` for `g ∈ S` (sell `g` and keep its proceeds in the bundle).

Call `(S, a)` *claimed* if some agent's guarantee is met by it, and take a claimed generalized
bundle admitting no claimed one-step reduction.  Then

* `R1`-minimality gives `v̄ᵢ(S) + a ≤ θᵢ` for every agent `i` — exactly the envy-free clause that
  Definition 4 demands of a bundle carrying money;
* `R2`-minimality gives `v̄ᵢ(S \ g) + p(g) + a ≤ θᵢ` for every agent `i` and every `g ∈ S` —
  exactly the up-to-any-good clause of Definition 4 (note that the manuscript's SEFX condition
  keeps the price `p(g)` of the removed good on the right-hand side, so plain minimality without
  the `+ p(g)` is *not* enough);
* `R2`-minimality also forces every claimant to have `vₖ(g) > p(g)` for all `g ∈ S`, i.e. to keep
  the whole bundle, so the money it ends up holding is exactly `a`.

Applying this to the instance above: instead of `({g₁}, 18)` the minimal claimed bundle is
`({g₁}, 2)` (agent `0` gets `20 = τ`), and the resulting allocation is SEFX.

This is precisely the invariant used in the two theorems that are proved in full
(`exists_TPS_SEFX_of_prices_zero` and the safety condition `Stage.Safe`).

---

## 2. Definition 8 has no `ε` in the clause for a bundle that carries money

Definition 8 relaxes only the up-to-any-good clause: `ε-SEFX` asks for the *exact* envy-free
condition `v̄ᵢ(Aᵢ) + Pᵢ ≥ v̄ᵢ(A_j) + P_j` whenever `P_j > 0`.  But lines 5–7 of `Shrink` force
`ε`-progress by *adding sale proceeds* to the bundle that is handed out, which creates bundles
carrying money that other agents may envy by up to `ε`.  So the algorithm cannot maintain
Definition 8 as literally stated; it can only maintain the variant with `ε` in both clauses.

**The fix.**  Use the utility form `ε-SEFXu` (`RequestProject/EpsEnvy.lean`), which carries `ε` in
both clauses.  Lemma 11's limiting argument works verbatim for that input; this is now recorded as
`lemma11_utility_u`, `lemma11_u`, `lemma11_TPS_u` in `RequestProject/LemmaEleven.lean`, and it is
what `TPSSefxGeneral.lean` uses.  Since `SEFXu` and `SEFX` agree for valid outcomes
(`SEFX_iff_SEFXu`), the exact conclusion of Theorem 2 is unaffected.

---

## 3. Termination: the variational reformulation

The manuscript proves termination by the "forced `ε` progress" of `Shrink` (its Example 2 shows
that without it the algorithm can cycle for ever).  That argument is correct in spirit but
delicate: what "progress" means changes between the loops.

Two clean substitutes are used in the formalization.

* **When `p ≡ 0` the state space is finite**, so one can argue *variationally* and drop the
  algorithm altogether: maximize the pair `(number of served agents, total utility)`
  lexicographically over the finite set of legitimate states.  Any unserved agent yields a
  claimed set of unallocated goods, and shrinking it to a minimal claimed set produces a strictly
  better state — a contradiction.  This is how `exists_TPS_SEFX_of_prices_zero` is proved, and it
  removes the need for `ε` entirely (the theorem is obtained with exact SEFX, no limit).
* **In general** the amount of cash is a real number and the state space is infinite, so a
  measure is needed.  `TPSSefxGeneral.lean` uses the pair (number of unserved agents, number of
  `ε`-steps), which is well founded because the total utility is bounded
  (`total_le_bound`): `descent_inner`, `descent`.

---

## 4. What `TPSSefxGeneral.lean` contains, and what the improvement step is

A `Stage` records: the set of served agents, each agent's bundle of goods and amount of cash, the
set of sold goods, and the unallocated proceeds (`bank`).  `Stage.Good` collects the invariants:

1. consistent bookkeeping (disjointness; cash and bank non-negative; cash plus bank equals the
   proceeds of the sold goods);
2. `share`: every served agent is at or above its threshold `τ i = n/(2n−1)·TPS i`;
3. `safe`: every bundle is `ε`-safe for every agent, measured against that agent's *guarantee* —
   its own current utility if it is served, its threshold if it is not.  Safety is the
   disjunction of §1: either exact envy-freeness, or the bundle carries no money, is kept whole
   by its owner, and is not envied up to any single good;
4. `counting`: with `m` agents still unserved, every unserved agent values the unallocated goods
   (through its truncated contributions) plus the bank at least `(2m − 1)·τ`.  This is the
   invariant of Algorithm 4.

Because guarantees never decrease along the process, safety established at any moment survives;
when every agent is served the guarantees *are* the utilities, and safety *is* `ε`-SEFX
(`csafeU_of_full`).  `Good_emptyStage` establishes the invariants at the start (condition 4 there
is the identity `truncBundle(all goods) = n·TPS`, i.e. exactly `(2n−1)·τ`).

`ImprovementStep` says: from a good stage with an unserved agent one can reach a good stage in
which either one more agent is served or the total utility has gone up by at least `ε`.
`exists_eps_TPS_CSafeU_of_step` and `exists_TPS_SEFX_of_step` derive Theorem 2 from it; both are
proved without any `sorry`.

Nothing in the model forces the set of sold goods to grow: a successor stage may *un-sell* a good
(this is the manuscript's `Unshrink`).  That freedom is essential, see §5.

---

## 5. The hard part: the cost of selling, and stealing

> **Resolved.**  This section was written while the difficulty was still open; it is kept because
> it explains precisely *why* the naive bookkeepings fail.  The gap is now closed by the per-good
> ledger `PotTPS.QStage` of `RequestProject/TPSSefxPot.lean`, which is exactly the "proceeds of a
> single good tracked as a divisible object shared between several agents and the bank" asked for
> below; see `ISSUES_THEOREM2.md` for the full description.

This is where the manuscript's argument stops.

Write `truncⱼ(g) = max{p(g), min{vⱼ(g), TPSⱼ}}` for the truncated contribution used by the
counting argument, and let `τⱼ` be the threshold.  Unfolding condition 4 above, maintaining it
amounts to keeping, for every unserved agent `j`,

```
   ∑_{i served} [ truncBundleⱼ(Aᵢ) + cashᵢ ]  +  ∑_{g sold} ( truncⱼ(g) − p(g) )   ≤   2·|served|·τⱼ,
```

i.e. an average budget of `2τⱼ` per served agent, where the *sale losses* `truncⱼ(g) − p(g)` —
the part of a sold good's value to `j` that is not returned as money — have to be paid for out of
the same budget.  Two observations:

* **The budget is exactly tight.**  Safety alone gives `truncBundleⱼ(Aᵢ) + cashᵢ ≤ τⱼ + ε` for a
  bundle carrying money, and `≤ 2τⱼ` for a bundle of at least two goods that is safe up to any
  good.  So bundles alone can consume the whole `2τⱼ` budget, and the accounting only closes
  because each individual step of Algorithm 4 does *either* a sale *or* a bundle: in the
  large-good loop a good `g` with `p(g) ≥ τ_{i*}` is sold, `τ_{i*}` is paid out and the rest is
  banked, and the joint cost `τ_{i*} + truncⱼ(g) − p(g)` is `≤ 2τⱼ` precisely because
  `τ_{i*} ≤ p(g)`.
* **A steal breaks the pairing.**  When an agent that was served in the large-good loop (it holds
  cash, and a sold good is charged to it) later steals a bundle of goods, its new cost is
  `truncBundleⱼ(new bundle) + (sale loss of its old good)`, and each of the two terms can be close
  to `2τⱼ`.  Equivalently, in the invariant of condition 4: a steal returns the stealing agent's
  old bundle to the pool and its cash to the bank, but takes a fresh bundle whose cost can be up
  to `2τⱼ`, so the left-hand side of the counting invariant can drop by about `τⱼ` while the
  right-hand side is unchanged (the number of unserved agents does not change).  Since the number
  of steals is bounded only by `(total utility)/ε`, this cannot simply be absorbed.

### How far the un-selling idea gets

Since a `Stage` is pure bookkeeping, a good may be *un-sold*, and this does repair the accounting
under one extra invariant.  Suppose each served agent `i` is charged a set `Fᵢ` of sold goods (the
`Fᵢ` pairwise disjoint, their union the sold set) with

```
   cashᵢ  ≤  ∑_{g ∈ Fᵢ} p(g).                                        (†)
```

Then `bank = ∑ₖ ( ∑_{g ∈ Fₖ} p(g) − cashₖ )` is a sum of non-negative terms, so when agent `i`
releases its bundle and its cash returns to the bank, the bank holds at least
`(∑_{Fᵢ} p − cashᵢ) + cashᵢ = ∑_{Fᵢ} p`: *all of `Fᵢ` can be un-sold*, and the stealing agent starts
afresh with no sale charged to it.  Moreover `(†)` also gives the cost bound directly,

```
   truncBundleⱼ(Aᵢ) + cashᵢ + ∑_{g ∈ Fᵢ}(truncⱼ(g) − p(g))  ≤  truncBundleⱼ(Aᵢ ∪ Fᵢ),
```

which a bundle carved out of a minimal bag satisfies; and for the large-good loop the sharper
reading `cashᵢ + (truncⱼ(g) − p(g)) ≤ 2τⱼ` holds because `cashᵢ ≤ p(g)`.

What we could not arrange is `(†)` itself.  The large-good loop pays one agent `τ_{i*}` out of a
good whose price exceeds `τ_{i*}` and *banks the remainder*, and the remainder is later spent on a
different agent — whose cash then exceeds the price of the goods charged to it, breaking `(†)`.
Repairing this needs the proceeds of a single good to be tracked as a divisible object shared
between several agents and the bank (so that the good is un-sold exactly when the last holder
gives its share back), which is what the manuscript's "virtual goods" are meant to do.  Making
that bookkeeping precise — and proving that it keeps the number of sold goods below the number of
served agents — is what `RequestProject/TPSSefxPot.lean` does.  There, `(†)` is replaced by the
*pot* of a good, `pot p g = p g − ∑_{holders of g} cash`, together with the invariants
`pot_nonneg` (every pot is nonnegative), `src_card` (each agent draws from at most one good),
`bank_pot` (the bank covers the sum of the pots) and `slice_le` (each slice is at most an
unserved agent's threshold).  The counting invariant then deducts only the capped quantity
`min(pot g, τ_j)` per sold good, and a good whose last holder gives its slice back is un-sold
(`RS` in `RequestProject/TPSSefxPotStep.lean`).

The manuscript is aware of the difficulty; its answer is the `Unshrink` operation together with
the sentence *"this guarantees that there are no more goods sold at any step than agents that are
currently allocated a bundle"*.  The idea is that a sale is only ever committed while some agent
holds (part of) the proceeds, so that when the agent releases its bundle the good can be
**un-sold** and its full value returned to the pool.  For this to work the proceeds of a single
good may have to be tracked across several agents — the large-good loop pays `τ_{i*}` to one agent
and banks the remainder, which is later spent on somebody else — and the manuscript handles this
with "virtual goods" and the assertion that at most one good is ever divided.  We could not turn
these two paragraphs into a proof: the bookkeeping of *which* agent is responsible for *which*
fraction of *which* sold good, maintained across steals, is left implicit, and it is exactly what
a correct proof has to supply.

Concretely, the missing statement was `ImprovementStep` of `TPSSefxGeneral.lean`, and the missing
ingredient a strengthening of `Stage.Good` that (i) is preserved by steals and (ii) still implies
the counting invariant.  `PotTPS.QStage.Good` is such a strengthening: `PotTPS.qcounting` derives
the counting invariant from it, `PotTPS.toStage` maps it back to `Stage.Good`, and
`PotTPS.qstep_assign` shows it is preserved by an arbitrary re-allocation — a steal included.
Note that the naive weakening — dropping condition 4 and
keeping only share and safety — is **not** enough (argued informally, not formalized): a stage in
which a good `g` with a tiny price but a large value to an unserved agent `j` has been sold, its
(tiny) proceeds handed to a served agent, satisfies share and safety while destroying up to
`TPSⱼ` of `j`'s budget; a sequence of such stages leaves `j` unservable.  Some form of condition
4, or of the manuscript's "at most one sold good per served agent", is unavoidable.

---

## 6. Two special cases that *are* proved in full

* **`p ≡ 0`** (`exists_TPS_SEFX_of_prices_zero`, `RequestProject/TPSSefxZero.lean`).  No money
  ever changes hands, so the whole difficulty of §5 disappears, `SEFX` is ordinary `EFX`, and the
  variational argument of §3 applies directly.  The proof is self-contained: the key steps are
  `truncBundle_le_two_thr` (a safe bundle costs an unserved agent at most `2τ`), `thr_le_pool`
  (the counting argument), and `exists_better` (the improvement step).
* **No agent values a good above its price** (`exists_TPS_SEFX_of_money_goods`,
  `RequestProject/TPSSefxGeneral.lean`).  The instance is pure money: `TPS = PS = (∑ p)/n`,
  and selling everything and splitting the proceeds equally is envy free — hence SEFX — and gives
  each agent `(∑ p)/n ≥ n/(2n−1)·TPS`.

Note that the hypothesis "no agent values a good above its price" does **not** make selling
unnecessary in general; nor does the opposite hypothesis "every agent values every good at least
its price".  For the latter, take two agents, a good `g₁` with `v = p = 10` and three goods worth
`1` each with price `0`.  Then `TPS = 6.5` and `τ = 13/3 ≈ 4.33`, only `g₁` is worth more than
`τ`, and the three small goods are worth `3 < τ` together: the only way to serve both agents is to
sell `g₁` and *split* its proceeds.  So the bank of §4 (unallocated proceeds shared between
several agents) is genuinely needed, which is the root of the difficulty in §5.

---

## 7. Other observations

* **Theorem 1's SEFX half (`n = 2`) is not formalized**, and the manuscript's claim that the
  cutter of a Cut & Give protocol is SEFX-satisfied is false as stated (found in an earlier pass
  over the manuscript, recorded here for completeness): with `p ≡ 0` and three goods of values
  `3, 4, 0`, every two-part cut has parts of unequal value to the cutter, so the chooser can
  always leave the cutter with the smaller part and the cutter is not envy free.
* **Lemma 6 (value readjustment) cannot be used inside SEFX arguments.**  Lowering an agent's
  valuation preserves the maximin share but changes `v̄`, hence changes the envy relation; the
  SEFX conclusion for the readjusted instance does not transfer back.
* **Theorem 2's SEFX half must be read as producing a *partial* allocation.**  With `p ≡ 0` and
  `τ = 0` a *complete* SEFX allocation for all `n` would settle the existence of EFX allocations,
  which is open.  The formalized statements therefore produce an `Outcome` in which some goods may
  remain unallocated, as the manuscript's algorithm does (the manuscript then cites [8] to extend
  a partial allocation, which is a separate result and is not formalized here).
