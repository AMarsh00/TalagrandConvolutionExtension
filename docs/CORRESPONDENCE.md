# Correspondence with the manuscript

This comparison uses the 31-page manuscript version supplied on 19 October 2026, with Theorem 1.1, Eq. (2.1), and Eq. (3.1). It checks the mathematical interpretation of the Lean definitions against the paper. Compilation checks Lean's formal deductions; this comparison separately checks what those definitions mean.

## Main theorem

[MainStatement.lean](../TailBound/MainStatement.lean) and [Core.lean](../TailBound/Core.lean) expand `ManuscriptTheorem1` into the following assertion:

$$
\forall S,\pi,\quad
S\text{ irreducible},\ \pi\text{ stationary}
\ \Longrightarrow\
\forall\tau>0\ \exists C>0\ \forall N\in\mathbb N\ \forall f\geq0\ \forall\eta>1,
$$
$$
\sum_{x\in G_0^N}\!\left(\prod_i\pi(x_i)\right)
\mathbf1_{\{\eta\sum_y(\prod_i\pi(y_i))f(y)
<\sum_y(\prod_iK_\tau(x_i,y_i))f(y)\}}
\leq\frac{C}{\eta\sqrt{\log\eta}}.
$$

This is Theorem 1.1 in finite-sum notation. In particular:

- The constant is chosen after the single-coordinate semigroup, stationary law, and time, but before the dimension, input, and threshold.
- The input is any real-valued function with nonnegative values. It need not be a strictly positive density or have mean one.
- The tail event uses a strict inequality, and its threshold includes the input mean.
- `Real.log` and `Real.sqrt` give the stated denominator; `η > 1` makes it positive.
- Lean includes `N = 0` as well as the paper's `N ≥ 1`; this adds a trivial empty tail event on a one-point product space.
- Lean chooses a positive real constant. This entails the paper's finite-constant assertion.

`FiniteMarkovSemigroup` imposes stochastic kernels, identity at zero, the semigroup law, and entrywise continuity on nonnegative times. This is the finite-dimensional kernel formulation of the paper's continuous-time Markov semigroup. `Irreducible` requires a positive transition between each ordered pair at some positive time. `HasStationaryDistribution` requires nonnegative weights summing to one and invariance at every nonnegative time. No reversibility or uniformity hypothesis is present. Full support and positivity of every positive-time kernel are proved in [ContinuousPositivity.lean](../TailBound/ContinuousPositivity.lean).

## Basic definitions

| Lean definition | Meaning in the paper |
| --- | --- |
| `mean π f` | $\sum_x\pi(x)f(x)$, the integral against a finite weighted measure. |
| `act K f x` | $\sum_yK(x,y)f(y)$, with the same row-to-column convention as $K_\tau(x,y)=S_\tau\mathbf1_y(x)$. |
| `Stochastic K` | Nonnegative entries and row sums one. |
| `Stationary π K` | $\sum_x\pi(x)K(x,y)=\pi(y)$. |
| `comp K R` | Kernel composition $\sum_z K(x,z)R(z,y)$. |
| `tensorWeight π n` | $\prod_i\pi(x_i)$, the mass function of $\pi^{\otimes N}$. |
| `tensorKernel K n` | $\prod_iK(x_i,y_i)$, the tensor-product transition kernel. |
| `eventMass μ E` | $\sum_x\mu(x)\mathbf1_E(x)$; a probability when $\mu$ is a probability mass function. |
| `Function.update x i g` | Coordinate replacement $x^{i\to g}$. `Fin n` uses indices from zero rather than one. |
| `residual π K ε` | $(K(x,y)-\epsilon\pi(y))/(1-\epsilon)$, the residual kernel in Section 2. |

## Refresh semigroup and profile

[Heat.lean](../TailBound/Heat.lean) defines

$$
\operatorname{heatKernel}(\pi,a)(x,y)
=\pi(y)+a(\mathbf1_{x=y}-\pi(y))
=a\mathbf1_{x=y}+(1-a)\pi(y).
$$

`heat π f t` uses $a=e^{-t}$ and the tensor kernel, so it is exactly $P_t^\pi f$ in Eq. (2.1). `refresh π ε` instead takes the **refresh probability** as its parameter: $\epsilon=1-e^{-t}$. `heatKernel_eq_refresh` proves the relation. `refreshGenerator` equals $\sum_{i,g}\pi(g)(f(x^{i\to g})-f(x))$.

[ProfileEntropy.lean](../TailBound/ProfileEntropy.lean) defines

$$
\operatorname{bandMass}(\mu,F,\ell)
=\sum_x\mu(x)F(x)\mathbf1_{\{\ell<\log F(x)\leq\ell+1\}}.
$$

With $\mu=\pi^{\otimes N}$ and $F=P_t^\pi f$, this equals $A_t^f((\ell,\ell+1])$ from Eq. (3.1). The factor $F(x)$ is present: this is the band probability under the density-weighted law, not under the stationary law alone. The band has the same open lower and closed upper endpoint.

## Reverse density and coupling

The implementation chooses the paper's allowed horizon $T_0=2$, sets $T=\tau+2$, and uses starting times in $[1,2]$ for the averaged estimates. The paper's construction permits any $T_0>1$ and $\theta\in[T_0-1,T_0)$. Choosing $T_0=2$ suffices to prove the tail theorem for every $\tau>0$; the implementation is not a theorem about every choice of coupling horizon.

With `D : RefreshData α n`, the correspondence in [Reverse.lean](../TailBound/Reverse.lean) is:

| Lean | Paper, with $T=\tau+2$ |
| --- | --- |
| `D.p t x` | $P_{T-t}^\pi f(x)=p_{T-t}(x)$; **the time is already reversed in Lean's `p`**. |
| `D.logP t x` | $\log P_{T-t}^\pi f(x)$. |
| `D.density t x` | The probability mass $\pi^{\otimes N}(x)P_{T-t}^\pi f(x)$, rather than its density alone. |
| `D.ratio t i g x` | $\rho_{t,i,g}(x)=p_{T-t}(x^{i\to g})/p_{T-t}(x)$. |
| `D.revGen t` | The reverse generator with rates $\pi(g)\rho_{t,i,g}(x)$. |
| `D.score t x` | $\sum_{i,g}\pi(g)(\rho_{t,i,g}(x)-1)^2$. |
| `D.gap ℓ θ x` | $[\ell-\log P_{T-\theta}^\pi f(x)]_+$. |
| `D.exponent ℓ θ x` | $5\mathbf1_{\{R_\theta\geq10\}}/(R_\theta+1)$, matching $\alpha=5$ and $\bar\delta$. |
| `switchedPower δ r` | $\Psi_\delta(r)$, with the same branches at $r\leq1$ and $r>1$. |

In [Coupling.lean](../TailBound/Coupling.lean), the simultaneous, V-only, and W-only rates are respectively

$$
\pi(g)\min\{\rho,\Psi_\delta(\rho)\},\qquad
\pi(g)(\rho-\Psi_\delta(\rho))_+,\qquad
\pi(g)(\Psi_\delta(\rho)-\rho)_+.
$$

These are the rates obtained from the shared PRMs in the paper. `CoupledState` retains the starting point, the two current states, and an `alive` flag. `TimeGrid`, `killNode`, and `StoppedCoupling` implement barrier stopping through finite master equations and transfers. They do not define a random stopping time on a PRM path space, nor prove the paper's strong-solution statement as a path-space theorem.

`localScore` and `eventTV` give the paper's localized score integral and unnormalized event-supremum convention when localization is by the retained starting state. Their statements allow nonnegative starting weights or sets of starting states, rather than arbitrary events in an independently formalized filtration. These are the localizations used for the starting-gap layers in the tail proof.

## Conditional bridge

In [Core.lean](../TailBound/Core.lean), put $a=e^{-\tau}$ and $r=e^{-(T_0-t)}$. Then

$$
\operatorname{bridgeH}(\pi,ra,z,x)=h_t(x),
\qquad
\operatorname{bridgeH}(\pi,a,z,x)=h_{T_0}(x),
$$
$$
\operatorname{bridgeLaw}(\pi,a,r,z,x,y,u)
=\frac{r h_{T_0}(x)\mathbf1_{\{u=y\}}+(1-r)\pi(u)h_{T_0}(u)}{h_t(x)}.
$$

This is the explicit one-coordinate conditional law in Section 5. `bridgeTime t = exp (t-2)` implements $r$ at $T_0=2$. `bridgeMarginals` forms the coordinate laws; `bridgePayoff` and `D.bridgeQ` integrate the test function against their product, corresponding to $q_t^\zeta(x,y)$.

`coordinateAverage` is the finite conditional mean used in the product-variance bound. At zero-mass atoms Lean assigns zero by its convention for division by zero; those atoms contribute no weight. For the bridge's positive marginals at $t<T_0$, it is the usual conditional average.

`D.endpointH` is the normalized endpoint likelihood

$$
\frac{f(z)\prod_i K_{T-t}^\pi(x_i,z_i)}{P_{T-t}^\pi f(x)}.
$$

`D.bridgeRate` includes the factor $\pi(g)$, so it corresponds to $\pi(g)\lambda_{t,i,g}^\zeta$, not to $\lambda$ alone. `dx`, `dy`, and `dxy` are the paper's three coordinate difference operators. `endpointGen`, `bridgeGen`, and `bridgePerturbation` implement the conditioned, synchronous, and difference generators.

## Parameters and deliberate differences

1. **Heat-ratio parameter.** `refreshRatioBound m M τ` is
   $[e^{-\tau}+(1-e^{-\tau})M]/[(1-e^{-\tau})m]$.
   Taking $m=\min\pi$ and $M=\max\pi$ gives exactly $\kappa_{\tau,\pi}$. `D.Λ` equals $\kappa\log\kappa/(\kappa-1)$, and `D.sharpK` equals $\sqrt{\kappa^3\Lambda}=\kappa^2\sqrt{\log\kappa/(\kappa-1)}$. `lemma2_sharp` is the standalone formal counterpart of the current manuscript's **Lemma 3.1**; its name retains older numbering. The main refresh theorem may use the valid upper bound $M=1$ instead of $\max\pi$, which can enlarge its unspecified constant.

2. **Minorization.** The paper uses $d=\min_{x,y}K(x,y)/\pi(y)$ and handles $d=1$ separately. Lean chooses $\epsilon=\min\{1/2,d/2\}$, ensuring $0<\epsilon<1$ in every case. The factorization is the same, but the selected parameter and resulting constant need not be identical.

3. **Post-stopping weight.** `comparisonWeight` equals the paper's $e^{\Xi_t}$ before stopping. After stopping it uses $\ell+1$ in place of the stopped log density, yielding a lower weight. `comparisonFactor_kill_le` and `weighted_comparison` prove the inequalities needed for the terminal band argument. It is not a definitionally identical copy of the paper's entire process $e^{\Xi_t}$.

4. **Numerical constants.** The formal proof allows larger marginal-dependent constants, including a log-Sobolev coefficient $4/m$. It preserves the stated heat-ratio dependence in the standalone band estimate, not every numerical coefficient in the paper.

These differences concern proof representations and choices of auxiliary constants. They do not change the hypotheses, tail event, or dimension-free conclusion of Theorem 1.1. Internal finite-flow data structures and scalar helper constants have no claim to be literal manuscript definitions.
