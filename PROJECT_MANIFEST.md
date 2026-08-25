Got it. Here is the strict, one-line-per-file manifest for your `README.md`.

---

# Project Manifest: Fair Allocation with Optional Selling

### Core Model & Share Notions

* `Main.lean`: Project configuration, timeouts, and compiler option settings.


* `All.lean`: Project index importing the complete formalization in order.


* `Examples.lean`: Fully computed edge-case instances verifying the non-degeneracy of the model's definitions.


* `Selling.lean`: Core model definitions (outcomes, feasibility, MMS, TPS, PS) and the formal proof of Lemma 1.


* `SmallN.lean`: Proves MMS attainment via a compactness argument over the money simplex for finite assignment forms.



### Envy & Relaxations

* `EpsEnvy.lean`: Formalizes epsilon-relaxations of envy-freeness (SEF1, SEFX) and their utility forms.


* `EnvyRelaxation.lean`: Proves SEF1/SEFX are relaxations of EF and exhibits counterexamples for literal readings.


* `LemmaTen.lean`: Proves the structural equivalence of EFX and SEFX existence.


* `LemmaEleven.lean`: Verifies the limit argument for approximations via utility-form SEFX.




### Exact & Small-n Allocations

* `TwoAgents.lean`: Exact MMS existence for two agents via the formalized Cut & Give protocol.


* `MMSPartition.lean`: Generalizes configuration machinery to prove MMS partitions force-sell at most n-1 goods.


* `CanonicalPartition.lean`: Constructs canonical partitions for a single agent into three bundles (Lemma 3).


* `CanonicalStrict.lean`: Proves the strict form of canonical partitions enforcing the price condition on force-sold goods.


* `Matching.lean`: Exhaustive verification of the 3-agent bipartite matching step reducing to a single loss event.


* `MatchingPhase.lean`: Integrates canonical partitions and matching to yield the final single loss configuration.


* `LemmaFourResidual.lean`: Proves the residual singleton case of Lemma 4 where a single good is force-sold.


* `LemmaFourNecessity.lean`: Provides a 6-good counterexample proving Lemma 4 fails without the force-sold price condition.


* `PreliminaryPhase.lean`: Formalizes the preliminary value-thresholding phase to eliminate expensive or highly-valued goods.


* `ConfigSplit.lean`: Reusable machinery for reducing a 3-part MMS configuration after removing goods.


* `ThreeAgentCash.lean`: Introduces a cash token to represent unused sale proceeds in restricted 2-agent remainders.


* `ThreeAgentCashComposition.lean`: Proves composition of a cash-augmented 2-agent remainder with a third served agent.


* `ThreeAgentReduction.lean`: End-to-end assembly of the 3-agent reduction.


* `ThreeAgents.lean`: Verifies Main Lemma 2 mapping explicit loss certificates into restricted subproblems.


* `ThreeAgentTheorem.lean`: Verifies the final 3/4-MMS allocation for three agents.



### Theorem 2: TPS + SEFX Approximations

* `TPSCompute.lean`: Algorithm for computing the exact TPS via breakpoints and linear equations.


* `TPSApprox.lean`: Formalizes Algorithm 4, guaranteeing allocations reaching the TPS threshold.


* `TPSSefxConfig.lean`: Formalizes package shrinking logic and proves the cost bound for unserved agents.
* `TPSSefxStep.lean`: Formalizes the improvement step and bag-filling cases.
* `TPSSefxSharing.lean`: Verified instance proving that splitting a sold good's proceeds is strictly unavoidable.
* `TPSSefxMixedExample.lean`: Exhibits a mixed-good instance forcing a shared good at the very first step.
* `TPSSefxPot.lean`: Introduces the strict per-good ledger tracking unspent proceeds to safely process Unshrink reassignments.
* `TPSSefxPotStep.lean`: Performs unconditional Unshrink reassignment safely against the per-good ledger.
* `TPSSefxPotImp.lean`: Executes the improvement loops (selling, slicing, bag-filling) against the ledger.
* `TPSSefxTheorem2.lean`: Final assembly of Theorem 2 combining the approximation with SEFX.
* `TPSSefxPhase.lean`: Retains the superseded phase-structured bookkeeping approach for historical context.
* `TPSSefxGeneral.lean`: Defines the unified condition CSafeU used by the final Theorem 2 proof.
* `TPSSefx.lean`: Retains the superseded first attempt using the overly strong CSafe condition.

### Theorem 3: 2/3-MMS Approximation

* `EquiMMS.lean`: Fully verifies the value readjustment required for equi-valued MMS partitions.
* `TwoThirdsMatching.lean`: Proves the existence of a closed matching in one shot to avoid non-terminating loops.
* `TwoThirdsCanonical.lean`: Defines canonical partitions and identifies the matching phase of one round.
* `TwoThirdsLoss.lean`: Implements the charging scheme to handle loss events without merging bundles.
* `TwoThirdsBudget.lean`: Verifies that the charged loss events remain feasible within the available budget.
* `TwoThirdsDescent.lean`: Executes the main induction reducing large goods into pure parts or discarded bundles.
* `TwoThirdsGlue.lean`: Glues the pure parts constructed during the descent into canonical outputs.
* `TwoThirdsLemma9.lean`: Proves a canonical partition exists at every step of the main loop.
* `TwoThirds.lean`: Formalizes the preliminary phases, the main loop induction, and the final 2/3-MMS allocation.
* `TwoThirdsFull.lean`: Extends the 2/3-MMS result to a full allocation that distributes all goods and proceeds.

### Chores with Optional Outsourcing

* `ChoresModel.lean`: Adapts the model, feasibility, and MMS for chores, formalizing effective costs.


* `ChoresEnvy.lean`: Adapts the envy notions for chores and proves they relax EF.


* `ChoresPreAlloc.lean`: Formalizes self-service pre-allocations and their realization as valid outcomes.


* `ChoresBagLemma.lean`: Verifies the single-round while-loop of the chores bag-filling algorithm.


* `ChoresBagFilling.lean`: Establishes the loop invariant and existence induction over active agents.


* `ChoresMMSApprox.lean`: Verifies the 2-MMS approximation for chores via bag-filling.


* `ChoresMMSPartition.lean`: Proves the infimum cost defining the chores maximin share is mathematically attained.


* `ChoresTwoAgents.lean`: Guarantees exact MMS for two agents with chores via a Cut & Give extension.


* `ChoresExamples.lean`: Demonstrates that an outsourced chore's effective cost can mathematically exceed twice the MMS.



### Equal Proceeds (Appendix H)

* `EqualProceeds.lean`: Formalizes the equal-proceeds constraint and the corresponding MMSEP.


* `EqualProceedsExamples.lean`: Counterexamples showing MMSEP can be starved to exactly a fraction of the unconstrained MMS.


* `EqualProceedsBagFilling.lean`: Verifies the bag-filling algorithm guaranteeing TPS under equal proceeds while correcting an intermediate bound.



### Impossibility Bounds

* `FeigeNorkin.lean`: Kernel-checked combinatorial core proving the Feige-Norkin instance guarantees at most 33/36.


* `ElevenTwelfths.lean`: Establishes the 11/12-MMS impossibility gap for 3 agents and 8 goods.


* `FeigeNorkinChores.lean`: Kernel-checked core proving the chores variant forces at least 380/360 cost.


* `NineteenEighteenths.lean`: Establishes the 19/18-MMS impossibility gap for chores.
