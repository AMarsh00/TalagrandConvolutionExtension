# Talagrand's Convolution Bound for Finite-State Markov Semigroups — a Lean 4 formalization

A machine-checked proof of the main theorem of **Alexander Marsh, _Talagrand's Convolution Bound for Products of Finite-State Markov Semigroups_**, formalized in [Lean 4](https://lean-lang.org/) over [Mathlib](https://github.com/leanprover-community/mathlib4).

The project builds with **zero `sorry`**. The main theorem depends only on Lean's three standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## The theorem

Let $S=(S_t)_{t\geq 0}$ be an irreducible continuous Markov semigroup on a finite state space $G_0$, with stationary probability measure $\pi$. For every $\tau>0$, there is a constant $C_{\tau,S,\pi}>0$ such that, for every dimension $N$, every nonnegative function $f:G_0^N\to\mathbb R$, and every $\eta>1$,

$$
\pi^{\otimes N}\!\left(\left\{x:S_\tau^{\otimes N}f(x)>\eta\int f\,d\pi^{\otimes N}\right\}\right)
\leq \frac{C_{\tau,S,\pi}}{\eta\sqrt{\log\eta}}.
$$

The constant is chosen **before the dimension** and is independent of $N$, $f$, and $\eta$. The stationary measure need not be uniform, and the semigroup need not be reversible.

The proof first establishes the bound for weighted coordinate-refresh semigroups, then transfers it to strictly positive stationary kernels. Irreducibility and continuity supply the positive-time kernel positivity needed for the main theorem. These ingredients are proved in the project; the refresh tail bound is not assumed.

## Where the main theorem is

The main result is in [`TailBound/MainTheorem.lean`](TailBound/MainTheorem.lean):

```lean
theorem TailBound.main_theorem : TailBound.ManuscriptTheorem1
```

[`TailBound/MainStatement.lean`](TailBound/MainStatement.lean) defines the finite-state semigroup, irreducibility, stationarity, and the target proposition. The finite-sum definitions of product kernels, expectations, and tail probabilities are in [`TailBound/Core.lean`](TailBound/Core.lean).

In particular, `DimensionFreeTail` has the quantifier order

```lean
∃ C, 0 < C ∧ ∀ (n : ℕ),
  TailBound.TailEstimate
    (TailBound.tensorWeight π n)
    (TailBound.tensorKernel K n) C
```

so the formal statement explicitly requires one common constant for every dimension.

The refresh-band estimate also retains the manuscript's dependence on $\kappa$:

$$
K(\kappa)=\kappa^2\sqrt{\frac{\log\kappa}{\kappa-1}}.
$$

Its prefactor depends only on the marginal law and is uniform in time, dimension, density, and band level. The relevant declarations are

```lean
TailBound.lemma2_sharp
TailBound.RefreshData.fixed_band_sharp_explicit
```

The main theorem uses this estimate. See [`sharp-lemma2.md`](sharp-lemma2.md) for the explicit prefactor and proof map.

## How to verify the proof

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager, then run:

```bash
git clone https://github.com/AMarsh00/TalagrandConvolutionExtension.git
cd TalagrandConvolutionExtension
lake exe cache get
lake build
```

If using a source archive, run the two `lake` commands from the extracted project directory. The toolchain is pinned to **Lean 4.29.1**, with **Mathlib v4.29.1**; `lean-toolchain` and `lake-manifest.json` record the environment.

The build should finish without errors or `sorry` warnings. Then inspect the theorem statements and their axiom dependencies:

```bash
lake env lean MainCheck.lean
lake env lean SharpCheck.lean
lake env lean AxiomsCheck.lean
```

The main-theorem audit reports:

```text
'TailBound.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`MainCheck.lean` also prints the definitions underlying the theorem, while `SharpCheck.lean` checks the refined band estimate. The full audit covers all **477 lemma/theorem declarations** in the recorded verification snapshot. No admitted proofs, custom axioms, or `native_decide` proofs occur in the project.

The verification records dated **17 October 2026 UTC** are retained in `verification-build.log`, `verification-main.log`, `verification-sharp.log`, `verification-axioms.log`, and `verification-summary.json`.

## Proof structure

The proof follows the manuscript's refresh reduction, switched-power coupling, endpoint bridge comparison, stopped-score estimate, layer averaging, and band recurrence.

| Stage | Main files |
| --- | --- |
| Weighted refresh analysis, entropy, and averaged profiles | [Heat](TailBound/Heat.lean), [Entropy](TailBound/Entropy.lean), [Profile](TailBound/Profile.lean) |
| Reverse evolution and stopped coupling | [Reverse](TailBound/Reverse.lean), [JumpFlow](TailBound/JumpFlow.lean), [Coupling](TailBound/Coupling.lean), [CouplingSupport](TailBound/CouplingSupport.lean) |
| Stopped score and power-weight comparison | [StoppedScore](TailBound/StoppedScore.lean), [PowerWeight](TailBound/PowerWeight.lean), [WeightedComparison](TailBound/WeightedComparison.lean) |
| Full conditional bridge distributions and horizontal energy | [BridgeDynamics](TailBound/BridgeDynamics.lean), [BridgeChi](TailBound/BridgeChi.lean), [BridgeHorizontal](TailBound/BridgeHorizontal.lean) |
| Conditioned generators, Duhamel identity, and localized discrepancy | [EndpointBridge](TailBound/EndpointBridge.lean), [BridgeDuhamel](TailBound/BridgeDuhamel.lean), [IntegratedPerturbation](TailBound/IntegratedPerturbation.lean), [LocalizedTV](TailBound/LocalizedTV.lean) |
| Layer averaging and the band recurrence | [LayerAveraging](TailBound/LayerAveraging.lean), [AveragedError](TailBound/AveragedError.lean), [SharpBand](TailBound/SharpBand.lean), [FixedBand](TailBound/FixedBand.lean) |
| Tail summation and nonnegative inputs | [BandTail](TailBound/BandTail.lean), [PositiveApproximation](TailBound/PositiveApproximation.lean), [RefreshTail](TailBound/RefreshTail.lean) |
| Positive-kernel reduction and the main theorem | [PositiveKernel](TailBound/PositiveKernel.lean), [ContinuousPositivity](TailBound/ContinuousPositivity.lean), [MainTheorem](TailBound/MainTheorem.lean) |

The coupling is formalized through **finite master equations and barrier transfers**. This supplies the evolution, stopping, and comparison identities needed by the proof; the project does not separately formalize a Poisson-random-measure path space or its filtrations.

The main theorem's hypotheses, conclusion, and quantifier order are preserved. Intermediate numerical constants are not all identical to the manuscript's: the formalization uses valid, sometimes coarser marginal-dependent constants, while retaining the stated $\kappa$ dependence of the band estimate.

## Dependencies and acknowledgments

The project builds on the Lean development accompanying **Junwei Lu, Shengtao Guo, and Ethan X. Fang, _Weak-Type Bounds for Convolution on the Boolean Hypercube_**:

- [Paper](https://arxiv.org/abs/2608.15515)
- [Lean repository](https://github.com/junwei-lu/TalagrandConvolutionConjecture)

That development is pinned to commit `6488afd9f5f94f40766c6915c6e4e4f8de15ada7`. It supplies generic finite-space entropy, scalar power inequalities, cutoff calculus, finite-exception integration, and finite linear-ODE lemmas. Its band-summation and bootstrap arguments are adapted to the weighted finite alphabet. **Its Boolean headline theorem is not used to prove this project's main theorem.**

The weighted finite-alphabet extensions, including the full conditional bridge comparison, are proved here. The underlying reverse-heat and layerwise methods build on work of Yuansi Chen and of Yanjin Xiang and Zhihua Zhang, as discussed in the manuscript.

<details>
<summary>Recorded verification environment</summary>

Mathlib is pinned to commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (v4.29.1). Downloaded dependencies and compiled caches are omitted from the source archive and restored by Lake.

The container used for the recorded verification required a small `readlink` compatibility shim because its numeric `/proc/<current-pid>/exe` path did not resolve. The shim redirects only the current process's own executable path to `/proc/self/exe`. Lean's kernel, tactics, and proof objects were unchanged. The source is in [`verification-environment/proc_self.c`](verification-environment/proc_self.c); ordinary Lean installations do not need it.

</details>
