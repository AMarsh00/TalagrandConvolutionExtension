# Proof map

The main entry points are [MainStatement.lean](../TailBound/MainStatement.lean), [MainTheorem.lean](../TailBound/MainTheorem.lean), and the umbrella import [TailBound.lean](../TailBound.lean).

| Stage | Main modules | Role |
| --- | --- | --- |
| Finite kernels | [Core](../TailBound/Core.lean), [PositiveKernel](../TailBound/PositiveKernel.lean), [ContinuousPositivity](../TailBound/ContinuousPositivity.lean) | Tensorization, Doeblin factorization, and positive-time positivity. |
| Weighted refresh analysis | [Heat](../TailBound/Heat.lean), [HeatRatio](../TailBound/HeatRatio.lean), [Entropy](../TailBound/Entropy.lean), [ProductCalculus](../TailBound/ProductCalculus.lean) | Heat evolution, coordinate-ratio bounds, log-Sobolev estimates, and integration by parts. |
| Averaged profile | [ProfileEntropy](../TailBound/ProfileEntropy.lean), [ProfileFlux](../TailBound/ProfileFlux.lean), [Profile](../TailBound/Profile.lean) | Localized entropy, threshold flux, and the dimension-free averaged profile. |
| Stopped coupling | [Reverse](../TailBound/Reverse.lean), [JumpFlow](../TailBound/JumpFlow.lean), [TimeGrid](../TailBound/TimeGrid.lean), [Coupling](../TailBound/Coupling.lean), [CouplingSupport](../TailBound/CouplingSupport.lean) | Reverse evolution, finite master equations, stopping transfers, and support bounds. |
| Score and power weight | [StoppedScore](../TailBound/StoppedScore.lean), [PowerWeight](../TailBound/PowerWeight.lean), [WeightedComparison](../TailBound/WeightedComparison.lean) | Stopped-score control, nonpositive weighted drift, and terminal comparison. |
| Conditional bridge | [LevelOne](../TailBound/LevelOne.lean), [BridgeDynamics](../TailBound/BridgeDynamics.lean), [BridgeEnergy](../TailBound/BridgeEnergy.lean), [BridgeChi](../TailBound/BridgeChi.lean), [BridgeHorizontal](../TailBound/BridgeHorizontal.lean) | Product projections, explicit conditional laws, and horizontal energy estimates. |
| Localized discrepancy | [EndpointBridge](../TailBound/EndpointBridge.lean), [BridgeDuhamel](../TailBound/BridgeDuhamel.lean), [IntegratedHorizontal](../TailBound/IntegratedHorizontal.lean), [IntegratedPerturbation](../TailBound/IntegratedPerturbation.lean), [LocalizedTV](../TailBound/LocalizedTV.lean) | Endpoint conditioning, Duhamel comparison, energy absorption, and total variation. |
| Layers and bands | [BandEvents](../TailBound/BandEvents.lean), [LayerAveraging](../TailBound/LayerAveraging.lean), [AveragedError](../TailBound/AveragedError.lean), [FixedBand](../TailBound/FixedBand.lean) | Crossing events, averaging over starting gaps, and the fixed-band bootstrap. |
| Explicit parameter dependence | [SharpAlgebra](../TailBound/SharpAlgebra.lean), [SharpLayer](../TailBound/SharpLayer.lean), [SharpAverage](../TailBound/SharpAverage.lean), [SharpBand](../TailBound/SharpBand.lean), [SharpStatement](../TailBound/SharpStatement.lean) | Separate layer estimates and the stated dependence on the heat-ratio parameter. |
| Tail conclusion | [BandTail](../TailBound/BandTail.lean), [PositiveApproximation](../TailBound/PositiveApproximation.lean), [RefreshTail](../TailBound/RefreshTail.lean), [MainTheorem](../TailBound/MainTheorem.lean) | Geometric-band summation, nonnegative inputs, kernel transfer, and the main result. |

Module imports give the exact dependency graph. All source modules remain in `TailBound/`. The main theorem and band-estimate entry points keep their names.

## Verification entry points

- [MainCheck.lean](../checks/MainCheck.lean) checks the main theorem and prints its underlying definitions and axioms.
- [SharpCheck.lean](../checks/SharpCheck.lean) checks the explicit band estimate and its constants.
- [AxiomsCheck.lean](../checks/AxiomsCheck.lean) prints axiom dependencies for the 473 current lemma/theorem declarations.
