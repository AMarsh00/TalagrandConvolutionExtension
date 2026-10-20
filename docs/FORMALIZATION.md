# Formalization scope

The target is `TailBound.ManuscriptTheorem1`, defined in [MainStatement.lean](../TailBound/MainStatement.lean) and proved by `TailBound.main_theorem` in [MainTheorem.lean](../TailBound/MainTheorem.lean).

## Statement

A finite-state semigroup is represented by real-valued kernels, with the identity at time zero, the semigroup law, stochasticity, and continuity for nonnegative times. Irreducibility means that each ordered pair of states has a positive transition probability at some positive time. Stationarity is imposed for every nonnegative time.

`DimensionFreeTail` chooses a positive constant before the tensor dimension. `TailEstimate` then quantifies over every nonnegative input and every threshold greater than one. The strict tail event and normalization by the input mean agree with the main theorem.

## Probabilistic constructions

The reverse process and stopped coupling are represented by finite master equations. A finite time grid and barrier transfers encode the stopping mechanism. The development proves positivity, conservation, support properties, Dynkin identities, endpoint conditioning, and the terminal weighted comparison in this representation.

This is a formalization of the estimates and main conclusion, not a separate implementation of Poisson random measures, sample paths, or filtrations. The terminal power weight agrees with the pre-stopping expression and uses a barrier lower bound after stopping to obtain the comparison needed for the band argument.

## Constants and approximation

The main theorem uses `TailBound.lemma2_sharp`, retaining the factor

$$K(\kappa)=\kappa^2\sqrt{\frac{\log\kappa}{\kappa-1}}.$$

The prefactor is chosen before the refresh time, dimension, density, and band level. Intermediate numerical constants can be larger than those in the manuscript. In particular, the finite-alphabet log-Sobolev estimate uses the valid coefficient $4/m$, where every marginal atom has mass at least $m>0$. See the [band estimate](BAND_ESTIMATE.md).

For general nonnegative inputs, finite-space positive approximation chooses a sufficiently small positive perturbation that preserves the original strict tail event exactly.

## Reused development

The pinned [Boolean project](https://github.com/junwei-lu/TalagrandConvolutionConjecture) supplies finite-space entropy, scalar power inequalities, cutoff calculus, finite-exception integration, and finite linear-ODE results. The weighted extensions are local to this project. Attribution for adapted scalar estimates is also recorded in [SharpAlgebra.lean](../TailBound/SharpAlgebra.lean).

The Boolean headline theorem is not an input to `TailBound.main_theorem`.
