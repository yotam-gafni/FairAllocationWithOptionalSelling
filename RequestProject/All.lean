import Mathlib
import RequestProject.Selling
import RequestProject.SmallN
import RequestProject.MMSPartition
import RequestProject.TwoAgents
import RequestProject.TPSCompute
import RequestProject.TPSApprox
import RequestProject.TPSSefx
import RequestProject.TPSSefxExamples
import RequestProject.TPSSefxZero
import RequestProject.TPSSefxGeneral
import RequestProject.TPSSefxMoney
import RequestProject.TPSSefxCharge
import RequestProject.TPSSefxServe
import RequestProject.TPSSefxConfig
import RequestProject.TPSSefxStep
import RequestProject.TPSSefxPhase
import RequestProject.TPSSefxPhaseStep
import RequestProject.TPSSefxPhaseImp
import RequestProject.TPSSefxPot
import RequestProject.TPSSefxPotStep
import RequestProject.TPSSefxPotImp
import RequestProject.TPSSefxMixedExample
import RequestProject.TPSSefxTheorem2
import RequestProject.TPSSefxSharing
import RequestProject.ThreeAgents
import RequestProject.CanonicalPartition
import RequestProject.CanonicalStrict
import RequestProject.Matching
import RequestProject.MatchingPhase
import RequestProject.ConfigSplit
import RequestProject.ThreeAgentCash
import RequestProject.ThreeAgentCashComposition
import RequestProject.ThreeAgentReduction
import RequestProject.LemmaFourResidual
import RequestProject.LemmaFourNecessity
import RequestProject.PreliminaryPhase
import RequestProject.ThreeAgentTheorem
import RequestProject.EquiMMS
import RequestProject.TwoThirdsMatching
import RequestProject.TwoThirdsCanonical
import RequestProject.TwoThirdsLoss
import RequestProject.TwoThirdsBudget
import RequestProject.TwoThirdsProp6
import RequestProject.TwoThirdsGlue
import RequestProject.TwoThirdsDescent
import RequestProject.TwoThirdsLemma9
import RequestProject.TwoThirds
import RequestProject.TwoThirdsBagFilling
import RequestProject.TwoThirdsReduction
import RequestProject.TwoThirdsFull
import RequestProject.Examples
import RequestProject.EnvyRelaxation
import RequestProject.FeigeNorkin
import RequestProject.ElevenTwelfths
import RequestProject.EpsEnvy
import RequestProject.LemmaTen
import RequestProject.LemmaEleven
import RequestProject.ChoresModel
import RequestProject.ChoresEnvy
import RequestProject.ChoresPreAlloc
import RequestProject.ChoresBagLemma
import RequestProject.ChoresBagFilling
import RequestProject.ChoresMMSApprox
import RequestProject.ChoresExamples
import RequestProject.ChoresMMSPartition
import RequestProject.ChoresTwoAgents
import RequestProject.FeigeNorkinChores
import RequestProject.NineteenEighteenths
import RequestProject.EqualProceeds
import RequestProject.EqualProceedsExamples
import RequestProject.EqualProceedsBagFilling

/-!
# Fair allocation with optional selling — index

This module imports the whole development, in the order in which the manuscript presents it.

## The model and the share notions

* `RequestProject.Selling` — the model (goods, agents, outcomes, feasibility, utilities), the
  share notions `PS`, `MMS`, `TPS`, the envy notions `EF`, `SEF1`, `SEFX` (Definition 4, in the
  corrected reading in which the envying agent's own money is counted on the left-hand side of
  the relaxed condition, which may also be replaced by the envy-free condition; the literal
  transcriptions are kept as `SEF1lit`, `SEFXlit`), and **Lemma 1** (`MMS ≤ TPS ≤ PS`).
* `RequestProject.SmallN` — attainment of the maximin share and the "unified outcome"
  realization used to turn abstract allocations into `Outcome`s.
* `RequestProject.MMSPartition` — **Lemma 5** for general `n` (an MMS partition force-selling at
  most `n − 1` goods).

## Two agents

* `RequestProject.TwoAgents` — **Theorem 1**: two agents can each be given their full maximin
  share with selling (`exists_MMS_two`), via the Cut & Give protocol.

## The truncated proportional share

* `RequestProject.TPSCompute` — Appendix E: Claim E, the affinity of the truncated-proportional
  map between breakpoints, and the correctness of the algorithm computing the `TPS`.
* `RequestProject.TPSApprox` — **Theorem 2** (TPS half): every instance admits an
  `n/(2n−1)`-TPS allocation (`exists_TPS_approx`), formalizing Algorithm 4 and its analysis.
* `RequestProject.TPSSefx` — the conceptual safety condition `CSafe` and its realization
  `epsSEFX_unifiedOutcome`, the by-product `ratio_TPS_le_MMS`, and a record of the first,
  superseded attempt at the SEFX half of Theorem 2 through `CSafe`; see `ISSUES_TPS_SEFX.md`.
* `RequestProject.TPSSefxExamples` — a run of the manuscript's Algorithm 6 whose output is
  `(2/3)`-TPS but not SEFX, showing that the invariant maintained by `Shrink` is too weak.
* `RequestProject.TPSSefxZero` — **Theorem 2 (SEFX half) for instances with `p ≡ 0`**, proved in
  full (`exists_TPS_SEFX_of_prices_zero`): a variational argument replacing Algorithm 6, with the
  minimality-based safety invariant that repairs the gap found in `Shrink`.
* `RequestProject.TPSSefxGeneral` — the general (priced) case: the state of Algorithm 6 (`Stage`,
  `Stage.Good`), the reduction of Theorem 2 (SEFX half) to a single local `ImprovementStep`
  (`exists_TPS_SEFX_of_step`, proved), and the opposite extreme special case
  `exists_TPS_SEFX_of_money_goods` (no agent values a good above its price), proved in full.
* `RequestProject.TPSSefxCharge` — the *charged* bookkeeping of Algorithm 6: every sold good is
  charged to a served agent and the sale proceeds are split into cash, money *put aside*, and the
  free bank.  `counting_of_cost` derives the global counting invariant of Algorithm 4 from one
  local inequality per served agent, and `exists_TPS_SEFX_of_Cstep` reduces Theorem 2 (SEFX half)
  to the corresponding improvement step.
* `RequestProject.TPSSefxServe` — handing a package to an unserved agent (`step_serve`), and the
  two reasons a package is affordable (`cost_le_of_footprint`, `cost_le_of_single_good`).
* `RequestProject.TPSSefxConfig` — the corrected `Shrink` operation: the least cash that makes a
  set of goods claimed (`Qc`), shrinking a feasible package to an admissible one (`exists_adm`),
  the choice of a package with a minimal footprint (`exists_min_adm`), and the resulting bound on
  what the package costs an unserved agent (`cost_bound`).
* `RequestProject.TPSSefxStep` — the improvement step of Algorithm 6: the pool is always feasible
  (`feas_pool`), the owner-keeps post-processing (`package_of_claimant`), and the bag-filling case
  of the step, proved in full (`cstep_of_unserved_claimant`).  The remaining case — the package is
  claimed only by agents that already hold a bundle, so it has to be stolen and the thief's old
  package released — is isolated as `CStealStep`.
* `RequestProject.TPSSefxPhase` — Algorithm 6 with the manuscript's phase structure: the state
  `PStage`, which distinguishes the goods an agent sold *inside its own package* (`own`, financed
  in full by the agent, so the sale can always be undone) from the goods sold in a large-good
  step, of which only part of the proceeds was handed out (`ext`); the latter are either *pure*,
  and cost nobody anything, or *shared* (`PStage.ShareOK`), the agent charged with them holding
  nothing but a slice of the proceeds.  The file also carries the invariant `PStage.Good`, its
  translation `toCStage` into the charged bookkeeping — which imports the counting invariant —
  the descent, and the reduction of Theorem 2 (SEFX half) to a single improvement step
  (`exists_TPS_SEFX_of_Pstep`).
* `RequestProject.TPSSefxPhaseStep` — `pstep_assign`, which hands a package to an agent, whether
  it is unserved or already holds a bundle.  In the latter case the old package is released
  first — the manuscript's `Unshrink` — and the release needs no hypothesis, because the goods
  the agent had sold on its own account are paid back out of the money it gives back and its
  pure charges cost nothing.  The one exception, an agent that is re-allocated while it holds a
  slice of a *shared* good, is isolated as the explicit assumption `PCarrierReassign`; the
  per-good ledger of `RequestProject.TPSSefxPot` removes the need for it.
* `RequestProject.TPSSefxPhaseImp` — the improvement step of Algorithm 6, split into the
  manuscript's loops: the large-good loops, in which an expensive good is sold and only the
  slice `Qc(∅)` of its proceeds is handed out, so that several agents may be served out of one
  sold good (`pshare_step`, proved; `pmoney_step` and `plarge_pure_step` for a pure good), and
  the bag-filling loop, which avoids sharing (`pbagfill_step`, proved, including the stealing
  case).  Every step here carries the assumption `PhaseTPS.PCarrierReassign`; this route is
  superseded by the per-good ledger below, and nothing depends on it.
* `RequestProject.TPSSefxPot` — Algorithm 6 with a **per-good ledger**: the state `PotTPS.QStage`
  records, for each sold good, which served agents hold a slice of its proceeds (`src`) and how
  much cash each of them holds, so that the *pot* still attached to a good is always explicit.
  The file carries the invariant `QStage.Good`, the counting invariant `qcounting`, the
  translation `toStage` into the unified bookkeeping, the descent, and the reduction of
  Theorem 2 (SEFX half) to a single improvement step (`exists_TPS_SEFX_of_Qstep`).
* `RequestProject.TPSSefxPotStep` — `qstep_assign`: handing a package to an agent and releasing
  that agent's old package — the manuscript's `Unshrink` — **unconditionally**, including when
  the agent holds a slice of a shared good.  This is what the anonymous bank of
  `RequestProject.TPSSefxPhase` could not do.
* `RequestProject.TPSSefxPotImp` — the improvement step for the ledger (`qimprovementStep`),
  split into the manuscript's loops: selling an expensive pool good and cutting one slice out of
  its pot (`qsell_step`), cutting a further slice out of a pot that is already large enough
  (`qcut_step`), and bag filling against the free bank (`qbagfill_step`).
* `RequestProject.TPSSefxMixedExample` — a two-agent instance on which sharing is unavoidable
  already at the first step of Algorithm 6 (`MixedGood.mixed_case_reached`).
* `RequestProject.TPSSefxTheorem2` — **Theorem 2**, both halves (`theorem_two`), fully proved:
  the TPS half from `exists_TPS_approx` and the SEFX half (`theorem_two_SEFX`) from the per-good
  ledger; see `ISSUES_THEOREM2.md`.
* `RequestProject.TPSSefxSharing` — an instance in which every outcome meeting the `n/(2n−1)`-TPS
  guarantee has to split the proceeds of one single good between two agents (`sharing_needed`).

## Three agents

* `RequestProject.ThreeAgents`, `RequestProject.CanonicalPartition`,
  `RequestProject.CanonicalStrict` — Lemma 3 (canonical partitions) and Main Lemma 2.
* `RequestProject.Matching`, `RequestProject.MatchingPhase` — the matching phase.
* `RequestProject.ConfigSplit`, `RequestProject.ThreeAgentCash`,
  `RequestProject.ThreeAgentCashComposition`, `RequestProject.ThreeAgentReduction` — the
  cash-aware reduction to the two-agent algorithm.
* `RequestProject.LemmaFourResidual` — Lemma 4 in full.
* `RequestProject.PreliminaryPhase`, `RequestProject.ThreeAgentTheorem` — **Theorem 3 for
  `n = 3`**: `exists_threequarter_MMS_three`.

## Theorem 3 for general `n`: the `2/3`-MMS approximation (Appendix B)

* `RequestProject.EquiMMS` — equi-valued MMS partitions (`EquiMMS`, Definition 5) and **Lemma 6**
  (*value readjustment*, `exists_readjustment`): the valuations can be lowered pointwise, without
  changing the maximin shares, so that every agent has an MMS partition all of whose parts are
  worth exactly its maximin share.  The key step is `MMS_liquid_le`: in an MMS partition the total
  price of the goods of a part plus its money never exceeds the maximin share, which is what
  leaves room for lowering `v̄`.
* `RequestProject.TwoThirdsMatching` — the Hall-type matching step of Algorithm 1
  (`exists_closed_matching`), in a corrected form: the manuscript's iteration of step 3 need not
  terminate, and the intermediate claim it aims at is unachievable.
* `RequestProject.TwoThirdsCanonical` — canonical partitions (`Canonical`), the matching phase of
  one round (`round_outcome`), and the reduction of one round of the main loop
  (`servable_of_round`).
* `RequestProject.TwoThirdsLoss` — the four
  loss types of Definition 7, the state invariant (`Losses`, `Inv`), and **Proposition 5**: the
  invariant is preserved by one round of the main loop (`losses_of_round`) and by the two stages
  of the preliminary phase (`losses_of_stage1`, `losses_of_stage2`).
* `RequestProject.TwoThirdsBudget` — the value still at the disposal of an active agent.  The
  manuscript's informal "the total value that we have at our disposal is at least `n′ · MMSᵢ`" is
  made precise as `EquiMMS.budget`, each loss event is shown to consume at most `MMSᵢ` of it
  (`eventCost_le`, the case analysis over the four loss types, and the place where `ρ = 2/3` is
  used), and the assertion itself is proved as `losses_budget`.  The finer classification
  `eventCost_witness` — every loss event either costs at most the threshold, or can be charged to
  one single good of a part that it removed from the pool — is what feeds the descent.
* `RequestProject.TwoThirdsProp6` — **Proposition 6**: out of a pool of large goods, a pool of
  cheap goods and a stock of money whose total is large enough, one can build `k` acceptable parts
  satisfying the canonicity conditions (`exists_canonical_of_few_large`, and its strengthening
  `exists_canonical_of_large_pairs`, which also uses a supply of pairs of large goods).
* `RequestProject.TwoThirdsGlue` — assembling canonical partitions out of pure parts
  (`CanonExists`, `CanonExists.mono`, `canonical_cons`).
* `RequestProject.TwoThirdsDescent` — the sequence of transformations of the proof of Lemma 9
  (`descent`): bundles carrying two witnesses, two large available goods, or forming a mixed pair
  are discarded one after the other, until Proposition 6 applies.
* `RequestProject.TwoThirdsLemma9` — **Lemma 9** (`canonical_of_inv`): a canonical partition
  exists at every step of the main loop.
* `RequestProject.TwoThirdsBagFilling` — the bag-filling step used by Proposition 6
  (`exists_bags`), and `RequestProject.TwoThirdsReduction` — the two arithmetic claims of the
  `|L′| > n′ + 1` counting step (`reduction_counts`, `reduction_budget`).
* `RequestProject.TwoThirds` — the assembly: the preliminary phase (`servable_stage1`,
  `servable_stage2`), the main loop (`servable_of_inv`), and **Theorem 3** for general `n`
  (`exists_twothirds_MMS`).
* `RequestProject.TwoThirdsFull` — Theorem 3 in the full-allocation form of the model
  (`exists_twothirds_MMS_full`): every good is sold or allocated and the proceeds are distributed
  in full, via the general completion step `exists_full_of_valid`.

## Impossibility

* `RequestProject.FeigeNorkin` — the combinatorial core of the Feige–Norkin three-agent,
  eight-good negative example.
* `RequestProject.ElevenTwelfths` — **Proposition 1**: for every `ρ > 11/12` there is an
  instance with `n = 3` agents and `m = 8` goods admitting no `ρ`-MMS outcome
  (`eleven_twelfths_gap`).

## Envy notions (Appendix C)

* `RequestProject.EpsEnvy` — **Definition 8**: the `ε`-relaxations `ε-SEF1` and `ε-SEFX` (again
  corrected as in Definition 4, with the literal transcriptions kept as `epsSEF1lit`,
  `epsSEFXlit`), and two variants of `SEFX` (the utility form `SEFXu`, which for valid outcomes
  is equivalent to the corrected `SEFX`, and the strong form `SEFXs`).
* `RequestProject.LemmaTen` — **Lemma 10**: `SEFX` existence and `EFX` existence are equivalent
  (the direction `EFX ⟹ SEFX` for full allocations is reduced to the extension result for mixed
  divisible and indivisible goods quoted by the manuscript, carried as a hypothesis).
* `RequestProject.LemmaEleven` — **Lemma 11**: the compactness argument `ε → 0`, proved for the
  corrected notions (`lemma11`, and the variants `lemma11_utility`, `lemma11_strict`).
* `RequestProject.LemmaElevenCounterexample` — Lemma 11 fails for the *literal* reading of
  Definitions 4.2/8.2, in which the envying agent's own money is not counted (`not_lemma11`).

## Sharpness and examples

* `RequestProject.LemmaFourNecessity` — the price condition on force-sold goods cannot be
  dropped from Lemma 4.
* `RequestProject.ThreeAgentReductionCounterexample` — a reduction interface that deletes unused
  sale proceeds is false.
* `RequestProject.Examples` — small fully computed instances.
* `RequestProject.EnvyRelaxation` — the corrected `SEF1`/`SEFX` are relaxations of envy-freeness,
  while the literal transcriptions `SEF1lit`/`SEFXlit` are not: a full envy-free allocation
  satisfying neither of them (`not_SEF1lit_relaxation_of_EF`, `not_SEFXlit_relaxation_of_EF`).

## Chores with outsourcing (the chores appendix)

* `RequestProject.ChoresModel` — the chores model (chores, costs `cᵢ`, outsourcing prices `p`,
  effective costs `c̄ᵢ = min{cᵢ, p}`, outcomes and feasibility, the maximin share `MMS` for
  chores), the bound `c̄ᵢ(M) ≤ n · MMSᵢ` in the refined weighted form
  (`wtSum_univ_le_nsmul_MMS`), and the fact that a chore too expensive for an agent must be
  outsourced in any of its optimal partitions.
* `RequestProject.ChoresEnvy` — **Definition 9**: `EF`, `SEF1`, `SEFX` for chores, in the
  corrected reading (the literal transcriptions are kept as `SEF1lit`, `SEFXlit`), the
  manuscript's local pairwise maximin derivation (`waterfilling_iff_delta`), and a fully
  envy-free allocation satisfying neither literal notion.
* `RequestProject.ChoresPreAlloc` — self-service allocations, in which an agent handling a
  bundle outsources whatever it prefers at its own expense, and their realization as outcomes.
* `RequestProject.ChoresBagLemma` — the `while` loop of Algorithm 13 (bag-filling with chores
  set aside), as the combinatorial `bag_lemma`.
* `RequestProject.ChoresBagFilling` — the invariant of Algorithm 13 and its analysis
  (Lemma 18), by induction on the number of active agents.
* `RequestProject.ChoresMMSApprox` — **Theorem 5** (existence half): every chores instance with
  optional outsourcing has a `2`-MMS allocation (`exists_two_MMS_chores`).
* `RequestProject.ChoresExamples` — with outsourcing, a chore may cost far more than the MMS,
  so the property underlying the classical chores bag-filling algorithm fails.
* `RequestProject.ChoresMMSPartition` — attainment of the chores maximin share: every agent has
  an MMS partition (`exists_MMS_partition_chores`).
* `RequestProject.ChoresTwoAgents` — **exact MMS for two agents** in the chores model
  (`exists_MMS_two_chores`), by the chores form of the Cut & Give protocol, together with the
  chores form of Lemma 5 for `n = 2` (`exists_reducedC`).
* `RequestProject.FeigeNorkinChores` — the combinatorial core of the Feige–Norkin three-agent
  negative example for chores (`feigeNorkinChores_cover`).
* `RequestProject.NineteenEighteenths` — **Theorem 5** (impossibility half): for every
  `ρ < 19/18` there is an instance with `n = 3` agents and `m = 8` chores admitting no `ρ`-MMS
  outcome (`nineteen_eighteenths_gap_chores`).

## The equal-proceeds case (Appendix H)

* `RequestProject.EqualProceeds` — the equal-proceeds restriction (`Outcome.EqualProceeds`: each
  agent receives exactly `1/n` of the sale proceeds), the equal-proceeds maximin share `MMSEP`,
  and the elementary comparisons `MMSEP ≤ MMS ≤ PS`.
* `RequestProject.EqualProceedsExamples` — **Example 3** (`MMSEP_eq_MMS_div`: an instance whose
  equal-proceeds maximin share is `1/n` of its unconstrained maximin share) and **Example 4**
  (`no_better_than_one_over_n`: for every `ε > 0` an instance in which every equal-proceeds
  outcome leaves some agent below `(1/n + ε)` times her equal-proceeds maximin share).
* `RequestProject.EqualProceedsBagFilling` — **Theorem 7**: the bag-filling algorithm produces a
  feasible equal-proceeds outcome giving every agent at least `(1/n)·TPSᵢ`
  (`exists_equalProceeds_TPS_approx`, and `exists_equalProceeds_TPS_approx_full` for a full
  allocation), hence also `(1/n)·MMSᵢ` for the unconstrained maximin share — so the two
  discounts of Examples 3 and 4 do not compound.  The file also documents, with a counterexample
  (`effSum_gt_two_div_n_of_netSum_lt`), that the intermediate bound in the manuscript's proof
  holds for the net value `ṽₖ` and not for `v'ₖ`.
-/
