# Talagrand's Convolution Bound for Finite-State Markov Semigroups

**A Lean 4 formalization** of Alexander Marsh's *Talagrand's Convolution Bound for Tensor Powers of Finite-State Markov Semigroups*.

The main theorem extends the convolution tail bound to products of arbitrary finite-state irreducible continuous Markov semigroups. The stationary law may be nonuniform, and reversibility is not required.

## Main theorem

Let $(S_t)_{t\geq 0}$ be an irreducible continuous-time Markov semigroup on a finite state space $G_0$, with stationary distribution $\pi$.

For every $\tau>0$, there exists a constant $C_{\tau,S,\pi}>0$ such that

> $\pi^{\otimes N}\left(S_\tau^{\otimes N}f>\eta\int_{G_0^N}f\,d\pi^{\otimes N}\right)\leq \dfrac{C_{\tau,S,\pi}}{\eta\sqrt{\log\eta}}.$

The bound holds for every dimension $N\geq 1$, every nonnegative function $f:G_0^N\to[0,\infty)$, and every threshold $\eta>1$.

**The constant $C_{\tau,S,\pi}$ depends only on $\tau$, the semigroup, and $\pi$, and is independent of $N$, $f$, and $\eta$.**

```lean
theorem TailBound.main_theorem : TailBound.ManuscriptTheorem1
```

The [statement](TailBound/MainStatement.lean) specifies the hypotheses and quantifier order; the [proof](TailBound/MainTheorem.lean) combines the refresh bound with the positive-kernel reduction. The refresh estimate, positive-time kernel positivity, and stationary full support are all proved within the development.

## Correspondence with the paper

The definitions underlying `main_theorem` match **Theorem 1.1** of the manuscript: the same finite-state semigroup, stationary product law, tensor-product operator, nonnegative inputs, strict tail event, and dimension-independent constant.

| Paper | Lean |
| --- | --- |
| $G_0$ and $G_0^N$ | A finite type `α` and `Fin n → α` |
| $\pi^{\otimes N}$ | `tensorWeight π n` |
| $\int f\,d\pi^{\otimes N}$ | `mean (tensorWeight π n) f` |
| $S_\tau^{\otimes N}f$ | `act (tensorKernel (S.kernel τ) n) f` |
| Probability of the strict tail event | `eventMass` with `η * mean π f < act K f x` |
| One constant for every dimension | `DimensionFreeTail`: `∃ C > 0, ∀ n, ...` |
| $P_t^\pi f$ in Eq. (2.1) | `heat π f t` |
| The unit-band profile in Eq. (3.1) | `bandMass (tensorWeight π n) (heat π f t) ℓ` |

Lean also includes the harmless case `n = 0`. The main theorem assumes neither strict positivity nor normalization of `f`; those assumptions are used only in intermediate estimates.

The [detailed correspondence](docs/CORRESPONDENCE.md) records the substitutions for the reverse density, coupling, bridge law, and constants. Some proof objects use different representations: the coupling uses finite master equations with $T_0=2$, and the terminal comparison uses a lower weight after stopping. Thus the main theorem matches the paper, while the formalization does not assert a literal translation of every stochastic definition or every numerical prefactor.

## Build and check

Install [elan](https://github.com/leanprover/elan), Git, and Python 3, then run from the project directory:

```bash
python scripts/prepare_dependencies.py
lake exe cache get
lake build --wfail
lake env lean checks/MainCheck.lean
lake env lean checks/SharpCheck.lean
lake env lean checks/AxiomsCheck.lean
```

The project pins **Lean 4.29.1** and **Mathlib v4.29.1**. The preparation script applies [source fixes](patches/README.md) for warnings in the pinned Boolean dependency. `--wfail` makes build warnings fail the check. The recorded verification contains no admitted proofs, and the main theorem reports:

```text
'TailBound.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The [GitHub workflow](.github/workflows/lean.yml) builds the project and runs these checks on pushes and pull requests. The [verification guide](docs/VERIFICATION.md) explains the checks and the retained build records.

## Reading the proof

Start with [MainStatement.lean](TailBound/MainStatement.lean) and [Core.lean](TailBound/Core.lean) for the statement and finite-sum definitions. The proof proceeds through weighted refresh analysis, the stopped reverse-heat coupling, conditional bridge estimates, and a layerwise band recurrence.

- [Proof map](docs/PROOF_MAP.md): the main modules and their roles.
- [Band estimate](docs/BAND_ESTIMATE.md): the factor $\kappa^2\sqrt{\log\kappa/(\kappa-1)}$ and an explicit marginal-dependent prefactor.
- [Formalization scope](docs/FORMALIZATION.md): correspondence with the probabilistic proof.

The coupling is represented by finite master equations and barrier transfers. The development proves the main theorem without separately constructing a PRM path space or its filtrations.

## Acknowledgments

This project uses the [Boolean Lean development](https://github.com/junwei-lu/TalagrandConvolutionConjecture) accompanying Junwei Lu, Shengtao Guo, and Ethan X. Fang's *Weak-Type Bounds for Convolution on the Boolean Hypercube*. It reuses general analytic tools and adapts the band argument to weighted finite alphabets; its Boolean headline theorem is not used to prove this result. The dependency revision and its warning fixes are recorded in [patches/README.md](patches/README.md).

The weighted finite-alphabet estimates and full conditional bridge comparison are proved here. The underlying reverse-heat and layerwise methods build on work of Yuansi Chen and of Yanjin Xiang and Zhihua Zhang.
