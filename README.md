# Tail-bound manuscript: main theorem verified in Lean

This repository contains a Lean 4 formalization of our paper "TITLE":

```lean
theorem TailBound.main_theorem : TailBound.ManuscriptTheorem1
```

For every finite irreducible continuous Markov semigroup S with stationary law π,
and each τ>0, there is C>0, chosen **before the dimension**, such that for every
N, nonnegative f and η>1,

π^⊗N(S_τ^⊗N f > η ∫f dπ^⊗N) ≤ C / (η sqrt(log η)).

No refresh tail estimate, positivity result, or other substantive estimate is
assumed by this theorem. The exact proposition and semigroup definitions are in
`TailBound/MainStatement.lean`; the proof is in `TailBound/MainTheorem.lean`.

## Build and audit

Install Lean through elan, extract the archive, and run:

```sh
lake exe cache get
lake build
lake env lean MainCheck.lean
lake env lean SharpCheck.lean
lake env lean AxiomsCheck.lean
```

Lean is pinned to 4.29.1 and mathlib to v4.29.1, commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`. The dependency manifest is included.
The archive contains all project source files; downloaded dependencies and
compiled caches are excluded and are restored by Lake.

The complete project builds. All 477 lemma/theorem declarations are covered by
`AxiomsCheck.lean`. The audit, including `TailBound.main_theorem`, reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. No admitted
proofs, custom axioms, or `native_decide` proofs occur in the project. Build,
main-theorem-check, and axiom-audit outputs are retained in `verification-*.log`.

## Fidelity to the manuscript

The proof retains the refresh-kernel reduction, switched-power coupling,
endpoint bridge comparison, stopped score, layer averaging and band recurrence.
The Boolean development's band-summation and bootstrap argument is adapted to
the weighted finite alphabet; its Boolean headline theorem is not used to prove
our result.

The main theorem's hypotheses, conclusion and quantifier order are preserved.
The formalization now also proves the **original κ-dependence of Lemma 2**:

```lean
TailBound.lemma2_sharp
TailBound.RefreshData.fixed_band_sharp_explicit
```

The band prefactor depends only on the marginal law, and is selected before
τ, N, f, and ℓ. The factor is exactly
`κ^2 * sqrt(log κ / (κ - 1)) = sqrt(κ^3 Λ)`.
`RefreshTail.lean` and the main theorem now use this sharper result.
The previous coarse `fixed_band` remains available as a valid auxiliary bound.
See `sharp-lemma2.md` for the explicit marginal-only constant and proof map.
The numerical prefactors are nonoptimal; the LSI coefficient remains the valid
`4/m`, for a positive marginal lower bound m.

The coupling is represented by finite master equations and barrier transfers.
No separate PRM path space or filtration implementation is claimed. The terminal
weight agrees with the manuscript before stopping and uses the barrier lower
bound afterwards; this proves the comparison required for the band argument.
Positive approximation uses a sufficiently small ε in the finite space so that
the original strict tail event is preserved exactly.

## Files and coverage

| File | Checked content |
|---|---|
| `TailBound/Core.lean` | Finite-kernel reduction and tensorization; Dirichlet-form sign; replacement identities; bridge mass and nonnegativity; stopped-score rescaling; scalar band calculations; AM–GM drift sign; four counterexamples to printed intermediate statements |
| `TailBound/HeatRatio.lean` | Corrected Lemma 17, including the remaining-time condition, arbitrary finite alphabets, all dimensions, and nonzero nonnegative input functions |
| `TailBound/LevelOne.lean` | Complete finite-sum version of Lemma 18, with explicit conditional averages; zero-weight atoms are allowed |
| `TailBound/Flux.lean` | Correct threshold-flux symmetrization and nonnegativity used in Lemma 3 |
| `TailBound/Generators.lean` | Reverse/conditioned generator algebra, carré-du-champ square identity, switched-rate bound, frozen-exponent bound |
| `TailBound/SmallThreshold.lean` | Markov inequality and the missing small-threshold case of Lemma 1 |
| `TailBound/BridgeEnergy.lean` | Correct conditional averages and both horizontal bridge differences; weighted Cauchy–Schwarz and the product perturbation bound |
| `TailBound/BridgeChi.lean` | Complete one-coordinate χ² coefficient estimates, including the retained atom in the unshifted denominator and both endpoint cases |
| `TailBound/BridgeHorizontal.lean` | Dimension-independent horizontal energy bound for the explicit product bridge, with the manuscript's κ dependence |
| `TailBound/PositiveKernel.lean` | Construction of a strictly positive minorization constant below 1, and reduction of every positive stationary kernel to refresh |
| `TailBound/MainStatement.lean` | Exact target proposition, proved in `MainTheorem.lean` |
| `TailBound/Entropy.lean` | Entropy tensorization and a dimension-independent finite-alphabet log-Sobolev inequality |
| `TailBound/Heat.lean` | Weighted refresh semigroup, heat equation, positivity, mass conservation and finite level crossings |
| `TailBound/ProductCalculus.lean` | Coordinate-resampling reversibility and discrete integration by parts |
| `TailBound/ProfileEntropy.lean` | The localized entropy comparison used in Lemma 3 |
| `TailBound/ProfileFlux.lean` | Joint flux measurability, level-excess dissipation and time flux bound |
| `TailBound/Profile.lean` | Complete Lemma 3 and finite-window corollary, with one constant for every dimension |
| `TailBound/JumpFlow.lean` | Finite master-equation existence, positivity, conservation and time-dependent Dynkin identity |
| `TailBound/Reverse.lean` | Reverse-density data, coordinate-ratio bounds, logarithmic derivative, entropy-production drift and score convexity |
| `TailBound/TimeGrid.lean` | Construction of the stopping grid and constancy of its moving barrier inside each cell |
| `TailBound/Coupling.lean` | Construction, positivity and mass conservation of the stopped coupling as finite master equations |
| `TailBound/CouplingCalculus.lean` | Correct V generator, preservation of the starting point, localized Dynkin inequality |
| `TailBound/CouplingSupport.lean` | Active-state support and barrier bound, including grid nodes |
| `TailBound/StoppedScore.lean` | Complete stopped-score bound in localized finite-law form, with corrected overshoot `1 + log κ` |
| `TailBound/ReverseHarmonic.lean` | Backward harmonic functions and the exact terminal V marginal |
| `TailBound/PowerWeight.lean` | Switched-power generator calculation and nonpositive drift |
| `TailBound/WeightedComparison.lean` | Terminal weighted comparison and its crossing-event exponential lower bound |
| `TailBound/BridgeDynamics.lean` | Explicit one-coordinate bridge backward equation, positivity, normalization, terminal condition |
| `TailBound/ProductEvolution.lean` | Product backward equation for the synchronous bridge, including terminal zero atoms |
| `TailBound/EndpointBridge.lean` | Positive normalized endpoint likelihood, harmonic equation, conditioned-rate cancellation and bounds |
| `TailBound/DoobCalculus.lean` | Doob-transform product identity and exact perturbation-generator expansion |
| `TailBound/FlowIntegration.lean` | Integrated Dynkin equality, localization at every time, and finite-flow integration |
| `TailBound/BridgeDuhamel.lean` | Complete localized Duhamel identity for the stopped coupling |
| `TailBound/BridgeQuadratic.lean` | Quadratic bridge Dynkin identity |
| `TailBound/PerturbationScalar.lean` | Switched-rate coefficient and Young inequalities |
| `TailBound/FlowBounds.lean` | Positive finite-flow integration and quadratic integral estimate |
| `TailBound/BridgePerturbation.lean` | Pointwise perturbation bounds for bridge tests and their squares |
| `TailBound/IntegratedHorizontal.lean` | Dimension-independent integrated horizontal energy bound |
| `TailBound/IntegratedPerturbation.lean` | Energy absorption and squared localized terminal-law estimate |
| `TailBound/LocalizedTV.lean` | Complete Lemma 4: localized total variation, with constant 8(1+3|α|/(4m²)) |
| `TailBound/BandEvents.lean` | Crossing-probability estimate from the terminal weighted comparison |
| `TailBound/BandPartition.lean` | Complete finite-sum band contraction, with existence of a cutoff beyond which all bands vanish |
| `TailBound/InverseDensity.lean` | Inverse-density harmonic identity and high-start terminal-tail estimate |
| `TailBound/LayerScore.lean` | Stopped-score bound on every starting gap layer |
| `TailBound/StartingProfile.lean` | Starting-band measurability, integrability and averaged profile bounds |
| `TailBound/LayerDiscrepancy.lean` | Layerwise localized test-function and total-variation bounds |
| `TailBound/BandTail.lean` | Weighted finite geometric-band summation and normalized tail bound |
| `TailBound/PositiveApproximation.lean` | Normalization and extension to all nonnegative inputs; complete Lemma 1 implication |
| `TailBound/LayerAveraging.lean` | Active-layer partition, coefficient summation and TV decomposition |
| `TailBound/InactiveBands.lean` | Uniform finite cutoff, profile split and inactive-event bound |
| `TailBound/AveragedError.lean` | Explicit measurable error majorant and dimension-free averaged estimate |
| `TailBound/SharpStatement.lean` | Original Lemma 2 with its exact κ dependence and uniformity in time, dimension, density and level |
| `TailBound/SharpBand.lean` | Sharp bounded-supremum recurrence and the exact formula for K |
| `TailBound/SharpAverage.lean` | Sharp averaged error estimate |
| `TailBound/SharpLayer.lean` | Separate layer terms, summation and terminal-layer bound |
| `TailBound/SharpAlgebra.lean` | Scalar estimates adapted from the pinned Boolean proof |
| `TailBound/FixedBand.lean` | Good starting time and bounded-supremum bootstrap; weighted fixed-band estimate |
| `TailBound/RefreshTail.lean` | Unconditional refresh tail and positive stationary-kernel theorem |
| `TailBound/ContinuousPositivity.lean` | Positive-time kernel positivity and stationary full support |
| `TailBound/MainTheorem.lean` | `main_theorem : ManuscriptTheorem1` |
| `MainCheck.lean` | Checks the exact theorem type and its dependency axioms |
| `AxiomsCheck.lean` | Dependency-axiom audit of all supplied theorem/lemma declarations |
| `minimal-repairs.md` | Page-by-page corrections, replacement passages, exact coverage and journal assessment |

## Dependencies and environment

The pinned Boolean development at
https://github.com/junwei-lu/TalagrandConvolutionConjecture
(commit `6488afd9f5f94f40766c6915c6e4e4f8de15ada7`) supplies generic finite-space
entropy, scalar power inequalities, cutoff calculus, finite-exception FTC and
finite linear-ODE lemmas. The weighted extensions are proved in this project.

This execution container required a small `readlink` compatibility shim because
its numeric `/proc/<current-pid>/exe` path did not resolve. The shim redirects
only that process's own executable path to `/proc/self/exe`. Lean's kernel,
tactics and proof objects were unchanged. The source is included as
`verification-environment/proc_self.c`; ordinary Lean installations do not need it.

Verified 17 October 2026 UTC.
