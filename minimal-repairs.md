**Minimal repairs to “Tail_Bound_Idea (2).pdf” — Alexander Marsh**

Reviewed against the supplied 40-page PDF. Page numbers below are the printed page numbers. Prepared 17 October 2026 UTC.

The corrections below retain the stated main result, the refresh-kernel reduction, the switched-power coupling, the order of lemmas, and the band-contraction argument. They correct identified false statements, dropped factors, inconsistent indices, and missing boundary cases. They do not introduce an alternative proof.

**Status: the main theorem is now proved in Lean.** The project contains `TailBound.main_theorem : ManuscriptTheorem1`, with no assumed refresh estimate. It proves the refresh tail bound, strict positivity of positive-time kernels from continuous-time irreducibility, stationary full support, and the full dimension-free conclusion. The project includes 477 checked lemma/theorem declarations.

The formal proof retains the refresh reduction, switched-power coupling, bridge comparison, layer averaging and band recurrence. The sharp continuation now verifies the manuscript's original explicit κ-dependence in Lemma 2, with a prefactor depending only on π, chosen before the time, dimension, density and band level. The main theorem now uses this sharper bound. See `sharp-lemma2.md` and `SharpCheck.lean` in the updated project. The main theorem's statement and quantifier order are unchanged. The coupling is implemented through finite master equations and stopping transfers, rather than a separate Poisson path-space construction.

**1. Page 2: keep the reduction; use a Markov operator, not an assumed semigroup.**

A stochastic residual matrix need not be the time-τ transition matrix of a continuous-time Markov chain. The sentence asserting such a semigroup is unnecessary. Replace that part of the proof by:

“For τ>0, irreducibility of the finite continuous-time chain gives Kτ(x,y)>0 for all x,y∈G₀. Thus ετ:=minₓ,ᵧ Kτ(x,y)/π(y)>0, and the row-sum identity implies ετ≤1. If ετ=1, all rows of Kτ equal π and the claimed tail event is empty. Otherwise set

\[
R_\tau(x,y)=\frac{K_\tau(x,y)-\epsilon_\tau\pi(y)}{1-\epsilon_\tau}.
\]

Let Tτ be the Markov operator associated with Rτ, and let Π be the averaging operator Πh=∫h dπ. The kernel Rτ is stochastic and π-invariant. Hence ΠTτ=Π, and

\[
K_\tau=((1-\epsilon_\tau)I+\epsilon_\tau\Pi)T_\tau.
\]

For s=−log(1−ετ)>0 this gives

\[
S_\tau^{\otimes N}f=P_s^\pi(T_\tau^{\otimes N}f).
\]

Apply Lemma 1 to the nonnegative function Tτ^{⊗N}f. Its π^{⊗N}-mean equals that of f, by stationarity.”

The conclusion and its dimension-independent constant are unchanged. In this proof, single-coordinate sums and state variables range over G₀, not G. Insert the missing f in the empty-tail-event display. Replace “composing Πτ with anything is just Πτ” by the stationarity identity above.

Lean: `residual_stochastic`, `residual_stationary`, `kernel_factorization`, `tensor_comp`, `tensor_stationary`, and `refresh_to_kernel`. The local reduction has an explicit refresh hypothesis; `refresh_tail` now proves it. `kernel_strictly_pos` proves positivity from continuous-time irreducibility, and `main_theorem` combines the results.

**2. Pages 2–3: define the density law early and include small thresholds.**

Before defining Aₜᶠ, write ν_g({x})=g(x)π^{⊗N}({x}) for g≥0 with ∫g dπ^{⊗N}=1.

Lemma 2 applies only for ℓ>2. In the proof of Lemma 1, first handle 1<η≤e² using

\[
\pi^{\otimes N}(P_\tau^\pi f>\eta)
\le \frac1\eta
\le \frac{\sqrt2}{\eta\sqrt{\log\eta}}
\qquad\text{when }\int f\,d\pi^{\otimes N}=1.
\]

Use the existing band decomposition for η>e². Its geometric sum is (1−e^{−1})^{−1}, not at most 1. Enlarge Cτ,π by this factor instead of using the same numerical constant in the final inequality.

For the stochastic part of the proof, state the standing assumption f>0 and ∫f dπ^{⊗N}=1. For a general nonnegative f with mean m, the case m=0 gives f=0 by full support. If m>0, use fε=(f+ε)/(m+ε). The tail event for fε is exactly

\[
\{P_\tau^\pi f>\eta m+(\eta-1)\epsilon\},
\]

which increases to the required strict tail event as ε↓0. This gives the extension without a questionable continuity assertion at a level-set atom. The analogous one-sided approximation also extends the stated band estimate: on a band above 1, (p+ε)/(1+ε) approaches p from below.

Lean: `finite_markov_bound` and `small_threshold_tail`. The large-threshold summation now compiles as `log_tail_from_bands`, and `tail_from_positive_normalized` proves normalization and positive approximation. In the finite space, it chooses one sufficiently small positive ε preserving the strict tail event, avoiding a separate limit theorem.

**3. Pages 7–10: repair the entropy/Dirichlet argument locally.**

Change hₛ:G→[0,1] to hₛ:G→[0,∞). The useful statements hₛ≤pₛ and ∫hₛ≤1 already appear and remain valid.

Let p*=minₓπ(x). For a nontrivial alphabet, the coefficient in the displayed log-Sobolev inequality on page 8 is inverted. With the manuscript's convention ℰ(v,v)=−∫vLv dπ^{⊗N}, use

\[
\operatorname{Ent}_{\pi^{\otimes N}}(v^2)
\le C_\pi\mathcal E(v,v),\qquad
C_\pi=\frac{\log((1-p_*)/p_*)}{1-2p_*}.
\]

At p*=1/2 the continuous value is Cπ=2. Treat the one-state alphabet separately; its tail event is empty. This reciprocal convention and tensorization agree with Diaconis–Saloff-Coste, equations (1.6)–(1.7), the product discussion, and Theorem A.1 [R1].

This is an actual false inequality as printed, not merely a choice of notation. For π=(1/3,2/3) and v=(1,0), ℰ(v,v)=2/9 and Ent(v²)=log(3)/3, whereas the printed coefficient gives only 2/(27 log 2). The strict failure is checked by `inverted_log_sobolev_counterexample`.

For the cutoff estimate, when a and b are unordered, take both Cauchy–Schwarz integrals over [min(a,b),max(a,b)]. Then retain the manuscript's estimate

\[
|\psi(b)-\psi(a)|^2
\le C|e^b-e^a|\int_{\ell-1}^{\ell+2}
\mathbf1_{\{\min(a,b)\le u<\max(a,b)\}}\,du.
\]

Replace the erroneous symmetrizations on page 9 by the following two identities, with y=x^{i→g} and pₛ=Pₛ^πf:

\[
\mathcal E(v,v)=\frac12\sum_x\pi^{\otimes N}(x)
\sum_{i,g}\pi(g)\,[v(y)-v(x)]^2,
\]

\[
\mathcal E(\mathbf1_{\{p_s>e^u\}},p_s)
=\frac12\sum_x\pi^{\otimes N}(x)\sum_{i,g}\pi(g)
|p_s(y)-p_s(x)|
\mathbf1_{\{\min(p_s(x),p_s(y))\le e^u<\max(p_s(x),p_s(y))\}}.
\]

Both expressions are nonnegative. The second identity requires the absolute difference and the factor 1/2. Simply replacing the indicator in the unsymmetrized signed sum by the symmetric crossing indicator is not a valid equality. In the subsequent integrals the threshold is e^u, not u. The resulting upper bound is

\[
\mathcal E(\sqrt{h_s},\sqrt{h_s})
\le C\int_{\ell-1}^{\ell+2}
\mathcal E(\mathbf1_{\{p_s>e^u\}},p_s)\,du.
\]

For Fₛ(u)=∫(pₛ−e^u)₊dπ^{⊗N}, state that s↦Fₛ(u) is locally absolutely continuous and

\[
\frac{d}{ds}F_s(u)=-\mathcal E(\mathbf1_{\{p_s>e^u\}},p_s)
\quad\text{for almost every }s.
\]

The positive-part function does not justify an everywhere classical chain rule. On page 10 use F₀(u)≤1, not F∞(u)≤1, to bound the boundary term. Since u≥ℓ−1>1, pₛ→1 gives F∞(u)=0. The integration interval has length 3, absorbed into the constant.

Lean checks the Dirichlet and threshold-flux symmetrizations, their nonnegativity, and a counterexample to the printed negative sign. The log-Sobolev theorem, cutoff calculus, time integration and complete Lemma 3 now compile. The checked LSI uses the valid nonoptimal coefficient 4/m, where m is the minimum marginal mass.

**4. Pages 10–12: make the construction and martingale explanation precise.**

The update rules are meaningful on an abstract finite alphabet, but the differences U^{i→g}−U in the displayed SDE require a vector-space interpretation. Add one sentence identifying G₀ with a finite set of real labels, or read each SDE explicitly as the indicated coordinate-update rule. State that the PRMs indexed by (i,g) are mutually independent and independent of the initial state, with the usual adapted construction. Nontrivial updates have g≠xᵢ, not g≠0. The density is relative to π^{⊗N}.

In Lemma 8 replace T by σ in the stopping indicator and keep the construction on [θ,T₀]. Preserve the original active event Eθ={Rθ≥2α}; the proof accidentally switches to {Rθ≥α}. On Eθ,

\[
0\le\bar\delta=\frac\alpha{R_\theta+1}<\frac12.
\]

The needed bound is uniform in time:

\[
0<\Psi_\delta(r)\le\max(1,r),\qquad
\sum_{i,g}\pi(g)\max\{\rho_{t,i,g},\Psi_{\delta_t}(\rho_{t,i,g})\}
\le N\kappa_{\tau,\pi}.
\]

The coupled process can therefore be constructed recursively from the finitely many atoms in the dominating PRM strips on [θ,T₀]. This supplies existence, uniqueness for the fixed drivers, and nonexplosion. Finiteness of a rate at each individual time alone would not suffice. The scalar inequalities are checked by `switchedPower_bounds` and `frozen_exponent_bound`; the stopped coupling is now constructed in Lean through finite master equations and barrier transfers. This represents the same rates and stopping rule without claiming a PRM path-space construction.

Time reversal should be interpreted with a càdlàg version, or at the level of finite-dimensional laws and the reversed generator, rather than an unqualified pathwise identity Uₜ=V_{T−t}.

In Lemma 9, “preserves the difference” is false for replacement updates: two distinct coordinates can coalesce when both refresh to g. Replace that sentence by: “By the Markov property and the definition of q as the conditional expected terminal payoff, qₜ^ζ(V̂ₜ,Ŵₜ) is a martingale. Its backward equation is (∂ₜ+Lₜ^ζ)qₜ^ζ=0.” Equality of the two coordinates is preserved when they start equal; that is the property needed later. Restrict endpoint conditioning to P(V_T=ζ)>0, as in Lemma 10.

**5. Page 15: repair Lemma 11's initial-value cancellation.**

The line qθ^ζ(Vθ,Wθ)=φ(V_{T₀}) is false pathwise. The conditional expectation must remain a conditional expectation. Replace that paragraph by:

“Since Vθ=Wθ, the synchronous process stays on the diagonal. Consequently, under P^ζ,

\[
q_\theta^\zeta(V_\theta,W_\theta)
=\mathbb E^\zeta[\varphi(V_{T_0})\mid\widetilde{\mathcal F}_\theta].
\]

As A∈F̃θ, the tower property gives

\[
\mathbb E^\zeta[\mathbf1_Aq_\theta^\zeta(V_\theta,W_\theta)]
=\mathbb E^\zeta[\mathbf1_A\varphi(V_{T_0})].
\]

Taking the P^ζ-expectation in the stopped Itô identity, using q_{T₀}^ζ(x,y)=φ(y) and (∂ₜ+Lₜ^ζ)qₜ^ζ=0, and then summing over ζ with weights P(V_T=ζ), proves the stated Duhamel identity.”

This repairs the proof without changing the statement of Lemma 11. Its finite-law localized form is now proved as `StoppedCoupling.duhamel`.

**6. Pages 16–29: retain the bridge argument and its estimates; fix the explicit algebra.**

On page 16 use the same orientation throughout:

\[
\Delta^x_{i,g}q_t^\zeta(x,y)
=q_t^\zeta(x^{i\to g},y)-q_t^\zeta(x,y)
=\sum_u[\mu_{t,i}^{g,y,\zeta}(u)-\mu_{t,i}^{x,y,\zeta}(u)]\varphi_i(u).
\]

The first expectation in the original subtraction is duplicated, and later displays reverse the sign. Squared estimates are unaffected once the equalities are made consistent. Write products over j≠i with index j. In the first expansion of φᵢ(u), divide the joint mass by μ_{t,i}^{x,y,ζ}(u); equivalently use the product of the other coordinate marginals, as the next line already intends. Work at t<T₀ when dividing by these marginals; endpoint values do not affect the time integrals.

With r=e^{−(T₀−t)} and hₛ(v)=e^{−(T−s)}1_{v=z}+(1−e^{−(T−s)})π(z), retain the manuscript's bridge law

\[
\mu_t^{x,y,z}(u)=
\frac{r h_{T_0}(x)\mathbf1_{\{u=y\}}+(1-r)\pi(u)h_{T_0}(u)}{h_t(x)},
\qquad
h_t(x)=r h_{T_0}(x)+(1-r)\pi(z).
\]

The interpolation identity has no extra π(z) multiplying its left side. The Lean project verifies this identity and that the formula is a nonnegative probability law when its denominator is nonzero. The continuation also checks both horizontal difference formulas, their one-coordinate χ² coefficients, and the dimension-independent pointwise horizontal energy estimate, with an explicit Cπ=3|G₀|/(4m²), where m is a positive lower bound on π. This retains the manuscript's κ dependence. The explicit one-coordinate and product backward equations, terminal condition and endpoint-conditioned rate cancellation now compile. The stopped-flow Duhamel identity, quadratic identity, integrated horizontal and synchronous energy bounds, and local total-variation estimate now compile.

Use these additional local replacements:

| Page | Printed issue | Required correction |
|---|---|---|
| 17 | δ_{g=ζᵢ} in a sum indexed by w | δ_{w=ζᵢ}. |
| 19 | r h_{T₀}(a)+(1−r)π(z)=hₜ(a)π(z) | The right side is hₜ(a). |
| 20 | A denominator loses its square | r(1−r)/(1−re^{−τ})² = r(1−r)/[(1−r)+r(1−e^{−τ})]². |
| 20 | The expansion of re^{−τ}+(1−re^{−τ})π(z) is incorrect | Use π(z)+re^{−τ}(1−π(z)); the lower bound ≥π(z) is retained. |
| 22 | e^{−(T−0−t)} | e^{−(T₀−t)}. |
| 22 | E[1_A(σ−τ)] | E[1_A(σ−θ)]≤P(A), since θ≥T₀−1 and σ≤T₀. |
| 23 | Ψsync bounded using a plus signed correction | From Ψsync=boundary−E∫Aq², bound by the absolute boundary term plus E∫|Aq²|. |
| 25 | a_{t,,i,g} | a_{t,i,g}. |
| 25 | (π(g)Ψδ(ρ)−ρ)₊ | Restore π(g) on the second ρ. |
| 25 | The first branch has the positive parts interchanged | For ρ≤1, a−b=π(g)(ρ^δ−1)≤0 and b−a=π(g)(1−ρ^δ)≥0. |
| 25 | δ logρ≤Λ(ρ−1)/ρ | Keep δ on the right: δ logρ≤δΛ(ρ−1)/ρ. |
| 25 | δ̄² disappears before identifying S_A | Keep δ̄² in the pointwise bound and in its time integral. |
| 27 | An upper integration limit reverts to T₀ after δₜ→δ̄ | Keep σ, or keep the stopping indicator explicitly. |
| 28 | I retains 1_{ρ>1} while being used to dominate both branches | Remove this indicator from the common nonnegative energy I. |
| 28 | E[1_A∑ΛI]≤Λ√(Ψsync+Ψhor) | The right side is Λ(Ψsync+Ψhor). The square root occurs only in the outer Cauchy–Schwarz bound. |
| 29 | e^{−t} in the bridge rate | Use e^{−(T−t)}. |
| 29 | Lower bound Cπ^{−1}κ | Use Cπ^{−1}κ^{−1}; in fact the exact bridge ratio gives κ^{−1}≤λ≤κ. |

On page 23, replace the false replacement-coordinate identity by the two identities

\[
\Delta^y_{i,g}\phi(x,y)
=\Delta^{xy}_{i,g}\phi(x,y)-\Delta^x_{i,g}\phi(x,y^{i\to g}),
\]
\[
\Delta^y_{i,g}\phi(x^{i\to g},y)
=\Delta^{xy}_{i,g}\phi(x,y)-\Delta^x_{i,g}\phi(x,y).
\]

Accordingly, change Δʸq(x,y^{i→g}) to Δˣq(x,y^{i→g}) in the following bound. These are `correct_vertical_identity` and `correct_shifted_vertical_identity` in Lean. The final three-increment bound in the manuscript then has the intended form.

For clarity, the corrected page-25 branch calculation, with c₊=r^ζ(a−b)₊, c₋=(b−a)₊ and λ=r^ζρ, is

\[
\frac{c_+^2+c_-^2}{\pi(g)\lambda}
=\begin{cases}
\pi(g)\lambda^{-1}(1-\rho^{\delta_t})^2,&\rho\le1,\\
\pi(g)\lambda(1-\rho^{-\delta_t})^2,&\rho>1.
\end{cases}
\]

For t≤σ it is bounded by π(g)κΛ²δ̄²(ρ−1)². Thus the relevant integrated error is at most κΛ²S_A, which is the quantity the next line of the manuscript needs. Keeping δ̄² is essential for this inference. The complete localized estimate of Lemma 4 is now Lean-checked as `localized_total_variation`, with explicit constant `8(1+3|G₀|/(4m²))`. The proof also establishes the stronger version for arbitrary nonnegative starting weights and [0,1]-valued tests.

**7. Pages 30–35: keep the switched-exponential argument and correct its stopping cases.**

Restore f in the missing P^πf terms of Ξ. Write Hₜ(x)=E[h(V_{T₀})|Vₜ=x]. In Φₜ, the frozen factor is exp(−δ̄ log p_{T−θ}(Vθ)), not exp(−δ̄ p_{T−θ}(Vθ)). Allow H≥0; a test function h can be an indicator.

For t>σ, retain π(g) and dt in the last drift display on page 32:

\[
M_t\left(\partial_tH_t(W_{t-})+
\sum_{i,g}\pi(g)\rho_{t,i,g}(W_{t-})
[H_t(W_{t-}^{i\to g})-H_t(W_{t-})]\right)dt=0.
\]

The scalar drift inequality before stopping, δ−δr−1+r^δ≤0 for 0≤δ≤1, r≥0, is checked as `switched_drift_nonpos`. That alone is not a proof of the supermartingale assertion.

In Lemma 5, the cases are σ=T₀ and σ<T₀; the printed second case T₀<σ is impossible. On C_j⊆Eθ, write δ=δ̄ and z₀=log p_{T−θ}(Vθ)=ℓ−Rθ. If σ=T₀, the correct calculation is

\[
\Xi_{T_0}>\ell+j-(1-\delta)(\ell+1)-\delta(\ell-R_\theta)
=j-1+\delta(R_\theta+1)=\alpha+j-1.
\]

If σ<T₀, put zσ=log p_{T−σ}(Vσ)≥ℓ+1. Then

\[
\Xi_{T_0}>\ell+j-(\ell+1)+\delta(z_\sigma-z_0)
\ge j-1+\delta(R_\theta+1)=\alpha+j-1.
\]

Change E₀ to Eθ. These two scalar calculations are checked in Lean.

For the total-variation step on page 33, the definition as a supremum gives

\[
|P(E_\theta\cap\{W_{T_0}\in B\})-P(E_\theta\cap\{V_{T_0}\in B\})|
\le D_{E_\theta},
\]

not the reverse inequality. With c=ℓ+1, the signed difference of the upper-tail probabilities is P(Eθ,W>c,V≤c)−P(Eθ,V>c,W≤c); the manuscript reverses these two terms. Taking the absolute value gives exactly the desired crossing-event comparison. On page 34, retain the upper endpoint in B={x:log pτ(x)∈(ℓ,ℓ+1]}. Atoms make this endpoint significant. The algebra combining A≤B+D and B≤c₀A+D+c₀F is checked as `band_contraction_algebra`.

On page 35, keep **logκ**, not κ, in the first S_A bound:

\[
S_A\le\frac{2\alpha^2(\kappa-1)}{\log\kappa}
\mathbb E\!\left[\frac{\mathbf1_A(R_\theta+1+\log\kappa)}{(R_\theta+1)^2}\right]
\]
\[
=\frac{2\alpha^2\kappa}{\Lambda}
\mathbb E\!\left[\frac{\mathbf1_A}{R_\theta+1}\right]
+2\alpha^2(\kappa-1)
\mathbb E\!\left[\frac{\mathbf1_A}{(R_\theta+1)^2}\right].
\]

Write S_A rather than S_a. `stopped_score_rescaling` checks this algebra with α=5. The finite-law localized stopped-score estimate is now proved as `StoppedCoupling.stopped_score`.

**8. Pages 38–40: correct replacement ratios and basis indices.**

In Lemma 17, require T−t≥τ (equivalently t≤T₀ when T=T₀+τ), not t≥τ. Let g range over G₀; an abstract alphabet has no distinguished zero. In the pointwise transition-kernel ratio, the denominator must use x, not x^{i→g}. Change the stray x^{i→y} to x^{i→g}.

For y=x^{i→g}, the reciprocal identity is

\[
\rho_{t,i,g}(x)^{-1}=\rho_{t,i,x_i}(y),
\]

because the reverse update restores xᵢ. The printed expression ρ_{t,i,g}(y) equals 1 and is generally not the reciprocal. `heat_replacement_ratio_time` proves the corrected two-sided bound for all dimensions, all nonzero nonnegative f, and all remaining times at least τ. `reciprocal_update_ratio` checks the restoration identity.

In Lemma 18's proof, use one coordinate-indexing convention consistently (1,…,N in the manuscript). In the conditional expectation of a tensor product, the product index is j. Replace “αⱼ≠0 for all j≠i” by “αⱼ≠0 for at least one j≠i”: precisely those terms vanish. In the resulting one-coordinate expansion write χ_{i,a}(u), not a multi-index in the second subscript of χ.

For a marginal with zero weights, take an orthonormal basis of L² on its support; its dimension need not be |G₀|. Conditional averages on zero-mass fibers can be assigned arbitrarily. The Lean theorem `level_one_product_le_quarter` proves the entire conclusion, including zero-weight atoms, using explicit finite conditional averages and the Bessel square expansion:

\[
\sum_i\sum_u\pi_i(u)(\varphi_i(u)-\bar\varphi)^2
\le\operatorname{Var}_\pi(\varphi)\le\tfrac14.
\]

**Remaining small textual repairs.**

| Page | Correction |
|---|---|
| 1 | Title, abstract and introduction are still template placeholders. They require author-supplied content; no replacement claims have been invented here. |
| 3 | W and V are constructed in Section 5, not Section 4. |
| 7–10 | Use π^{⊗N} consistently for the product-space measure; π alone denotes the one-coordinate law. |
| 8 | Attribute the log-Sobolev reference to Diaconis and Saloff-Coste. |
| 11 | “with prevent” → “will prevent”; the uniform bound above supplies the actual nonexplosion argument. |
| 13 | Delete duplicated “denote”; “hereis” → “here is”; use π_{T−t,ζ} in the transition-kernel integral and Vₜ consistently in the density process. |
| 25 | In the branch discussion, use “possibly nonzero”; at δ=0 both differences vanish. |
| 26 | In Ψδ(ρ), restore ρ as the argument where the state V_{t−} was inadvertently substituted. |
| 28 | “integals” → “integrals”. |
| 29–30 | Test functions used to recover total variation are nonnegative, including zero; do not impose strict positivity on them. |
| 33–35 | Restore omitted f's in P_s^πf, missing event braces, and the parenthesis in the band-decomposition event on page 34. |

**Exact formalization coverage.**

The project is pinned to Lean 4.29.1 and mathlib v4.29.1, commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6. All 477 included lemma/theorem declarations compile. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, including for `TailBound.main_theorem`. There are no admitted proofs, custom axioms, or `native_decide` proofs. `MainCheck.lean` checks an inhabitant of the exact `ManuscriptTheorem1` proposition and prints its definitions and dependency axioms.

| Manuscript component | Checked result |
|---|---|
| Theorem 1 | `main_theorem : ManuscriptTheorem1`, including all finite alphabets, every tensor dimension, and every threshold η>1 |
| Lemma 1 | `tail_estimate_from_bands`, with finite band summation, small thresholds, normalization, and positive approximation |
| Lemma 2 | `lemma2_sharp` and `RefreshData.fixed_band_sharp_explicit`, with layer decomposition, measurable error majorant, average, good starting time and bounded-supremum recurrence; the original κ²√(logκ/(κ−1)) dependence and a π-only prefactor |
| Lemma 3 | Complete weighted entropy tensorization, corrected nonoptimal LSI, cutoff/coarea comparison and integrated profile bound |
| Lemmas 4 and 12 | Explicit bridge, localized Duhamel and quadratic identities, integrated energies and localized total variation |
| Lemma 5 | Finite band contraction with an automatically existing cutoff |
| Lemma 6 | Localized stopped-score bound, including overshoot |
| Lemmas 7–11 | Constructed finite-law stopped coupling, terminal marginal, explicit bridge dynamics and localized Duhamel identity |
| Lemma 13 | Terminal weighted comparison sufficient for the crossing argument |
| Lemmas 14–18 | Weighted heat calculus, reverse generator identities, corrected coordinate-ratio bound and finite-product projection estimate |
| Continuous-time reduction | `kernel_strictly_pos`, `stationary_full_support`, and the unconditional `positive_kernel_tail` |

The implementation makes two representation choices. The coupling is a finite master equation with barrier transfers; it does not separately construct a PRM path space or filtration. Its terminal comparison weight uses the barrier lower bound after stopping, sufficient for the band inequality. These choices preserve the argument needed for the main theorem. The original parameter dependence in Lemma 2 is now verified; the scalar estimates retain the three layer terms separately and use the threshold ℓ≥64K². Numerical prefactors remain nonoptimal. No additional mathematical error in Lemma 2 was found during this continuation.

The earlier list of unfinished Lean obligations has been discharged for the main theorem. It should not be treated as a list of manuscript errors.

**Journal fit, conditional on a complete proof and a clear novelty comparison.**

My first candidate is **Electronic Journal of Probability**. Its scope explicitly includes full-length research in probability [R2]; a finite-state extension of a dimension-free weak-type inequality, supported by a coupling argument, is a natural topic fit. This is a scope judgment, not a prediction of acceptance.

**Bernoulli** is a plausible more ambitious candidate if the introduction makes the contribution beyond the Boolean case clear. Its stated emphasis is theoretical research across probability and mathematical statistics [R3]. **Probability Theory and Related Fields** is a stretch candidate: the topic fits its modern-probability and analysis scope, but it explicitly emphasizes very high standards and attention to article length [R4]. I would prioritize EJP while the strength and novelty of the extension are being established.

The literature comparison should include Lu–Guo–Fang's Boolean result [R5] and Shaposhnikov's September 2026 preprint, revised 1 October 2026 [R6]. The latter gives Gaussian and Boolean martingale proofs with explicit constants and an improved Boolean parameter dependence. This does not itself establish whether the arbitrary finite-state extension is new. It does mean that novelty should be framed around the finite-alphabet/Markov-chain extension and the new bridge estimate, rather than simply another proof of the Boolean theorem. The present repairs continue to use your original coupling argument.

The publicly available Boolean Lean development [R7] is now a pinned dependency for its generic finite-space entropy, scalar power, cutoff, finite-exception FTC and finite-ODE lemmas. The imported dependencies compiled locally. Its Boolean headline theorem is not used as a proof of the arbitrary finite-alphabet statement. The new weighted product proofs, including the complete integrated profile bound, are supplied separately.

**Sources.**

[R1] P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6(3), 695–750 (1996). [Author-hosted paper](https://pi.math.cornell.edu/~lsc/papers/log-aoap.pdf).

[R2] Institute of Mathematical Statistics, [Electronic Journal of Probability](https://imstat.org/journals-and-publications/electronic-journal-of-probability/), official scope, checked October 2026.

[R3] Bernoulli Society, [Bernoulli aims and scope](https://www.bernoullisociety.org/publications/bernoulli-journal/bernoulli-journal-aims-and-scope), checked October 2026.

[R4] Springer Nature, [Probability Theory and Related Fields aims and scope](https://link.springer.com/journal/440/aims-and-scope), checked October 2026.

[R5] J. Lu, S. Guo and E. X. Fang, [Weak-Type Bounds for Convolution on the Boolean Hypercube](https://arxiv.org/abs/2608.15515), arXiv:2608.15515 (2026).

[R6] A. Shaposhnikov, [Some remarks on Talagrand's convolution conjecture](https://arxiv.org/abs/2609.11290), arXiv:2609.11290v2 (1 October 2026).

[R7] [TalagrandConvolutionConjecture Lean repository](https://github.com/junwei-lu/TalagrandConvolutionConjecture).
