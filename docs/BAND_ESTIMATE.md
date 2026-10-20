# The fixed-band estimate

The development proves the manuscript's bound

$$
 A_\tau^f((\ell,\ell+1])\le
 C_\pi\,\kappa_{\tau,\pi}^{2}
 \sqrt{\frac{\log\kappa_{\tau,\pi}}{\kappa_{\tau,\pi}-1}}
 \frac{1}{\sqrt\ell},\qquad \ell>2.
$$

`TailBound.lemma2_sharp` chooses the positive prefactor before the time,
tensor dimension, positive normalized density, and band level. The hypotheses
on `m` and `M` are just positive lower and upper bounds on the one-coordinate
probability weights. Taking their minimum and maximum gives precisely the
manuscript's ratio bound. The theorem is unconditional: the coupling, profile,
score, and total-variation estimates are proved dependencies.

The main theorem uses this sharp band estimate through `RefreshTail.lean`.
Its nonnegative-input extension and quantifier order are unchanged.

## Layer estimates

The proof keeps three layer terms separate before applying the large-level threshold. The scalar estimates are adapted from the pinned Boolean development, with attribution in [SharpAlgebra.lean](../TailBound/SharpAlgebra.lean).

Write `K = sqrt(κ^3 Λ)` and `u=r+1`. The localized weighted estimates give

$$
 d_r\le C_D\left(\frac{8K}{\sqrt u}
       +\frac{72\kappa^2\Lambda}{u}
       +\frac{64K^2}{u^2}\right),
 \qquad C_D=8\left(1+\frac{3|G_0|}{4m^2}\right).
$$

The checked harmonic-sum absorption is

$$
 \kappa^2\Lambda(1+\log\ell)\le5K\sqrt\ell
 \quad\text{if }\ell\ge K^2,\ \ell\ge1.
$$

Together with the inverse-square-root and inverse-square sums, this bounds
both the summed finite layers and the terminal layer. Averaging and the
same bounded-supremum recurrence then prove the result for
`ℓ ≥ 64 K^2`. Below that threshold the probability bound `A ≤ 1` suffices.

## Explicit marginal-only prefactor

One nonoptimal prefactor certified by this implementation is

$$
\begin{aligned}
 C_D&=8\left(1+\frac{3d}{4m^2}\right),\\
 E_\pi&=\left(\frac{393216}{m}+512\right)C_D
                  +\frac{1536e^{11}}{m},\\
 C_\pi&=\max\{8,8E_\pi\},
 \qquad d=|G_0|,\ m=\min_x\pi(x).
\end{aligned}
$$

These numerical factors are not optimized. All time dependence is in `K`;
there is no additional dependence on time, dimension, density, or band level
inside `C_π`.

## Code and checks

- `SharpAlgebra.lean`: scalar layer splitting, sums, and logarithmic absorption.
- `SharpLayer.lean`: application to the weighted coupling estimates.
- `SharpAverage.lean`: the measurable error majorant's sharp average.
- `SharpBand.lean`: recurrence, small levels, and the exact formula for `K`.
- `SharpStatement.lean`: standalone Lemma 2 with explicit quantifier order.
- `SharpCheck.lean`: theorem types and dependency-axiom audit.

Run `lake build`, then `lake env lean checks/SharpCheck.lean` and
`lake env lean checks/AxiomsCheck.lean`. See the [verification guide](VERIFICATION.md) for the retained records.
