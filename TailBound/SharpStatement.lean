import TailBound.SharpBand

/-!
# Sharp Statement

A standalone statement of the fixed-band estimate. The prefactor is chosen
before the time, dimension, density and level, so its uniformity is explicit.
-/
open scoped BigOperators

namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

noncomputable def marginalBandConstant (d : ℕ) (m : ℝ) : ℝ :=
  max 8 (8 * ((393216 / m + 512) * (8 * (1 + 3 * d / (4 * m ^ 2))) + (1536 * Real.exp 11) / m))

lemma marginalBandConstant_pos (d : ℕ) (m : ℝ) : 0 < marginalBandConstant d m :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

noncomputable def refreshRatioBound (m M τ : ℝ) : ℝ :=
  (Real.exp (-τ) + (1 - Real.exp (-τ)) * M) / ((1 - Real.exp (-τ)) * m)

/-- The fixed-band estimate with the stated κ dependence and an explicit π-only constant. -/
theorem lemma2_sharp_of_bounds (π : α → ℝ) (m M : ℝ)
    (hm : 0 < m) (hlower : ∀ x, m ≤ π x) (hupper : ∀ x, π x ≤ M)
    (hmass : ∑ x, π x = 1) (τ : ℝ) (hτ : 0 < τ) (n : ℕ)
    (f : (Fin n → α) → ℝ) (hf : ∀ x, 0 < f x)
    (hfm : mean (tensorWeight π n) f = 1) (ℓ : ℝ) (hℓ : 2 < ℓ) :
    bandMass (tensorWeight π n) (heat π f τ) ℓ ≤
      marginalBandConstant (Fintype.card α) m *
        ((refreshRatioBound m M τ) ^ 2 *
          Real.sqrt (Real.log (refreshRatioBound m M τ) / (refreshRatioBound m M τ - 1))) /
        Real.sqrt ℓ := by
  let D : RefreshData α n := ⟨π, hmass, m, M, hm, hlower, hupper, τ, hτ, f, hf, hfm⟩
  have hh := D.fixed_band_sharp_explicit ℓ hℓ
  rw [D.startBand_eq_profile] at hh
  have htime : D.horizon - 2 = τ := by dsimp [RefreshData.horizon, D]; ring
  rw [htime] at hh
  exact hh

/-- Quantifier order makes uniformity in τ, N, f and ℓ explicit. Taking m
and M to be the minimum and maximum atom masses gives κ_{τ,π}. -/
theorem lemma2_sharp (π : α → ℝ) (m M : ℝ)
    (hm : 0 < m) (hlower : ∀ x, m ≤ π x) (hupper : ∀ x, π x ≤ M)
    (hmass : ∑ x, π x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℕ,
      ∀ f : (Fin n → α) → ℝ, (∀ x, 0 < f x) →
      mean (tensorWeight π n) f = 1 → ∀ ℓ : ℝ, 2 < ℓ →
      bandMass (tensorWeight π n) (heat π f τ) ℓ ≤
        C * ((refreshRatioBound m M τ) ^ 2 *
          Real.sqrt (Real.log (refreshRatioBound m M τ) / (refreshRatioBound m M τ - 1))) /
          Real.sqrt ℓ := by
  refine ⟨marginalBandConstant (Fintype.card α) m,
    marginalBandConstant_pos _ _, ?_⟩
  intro τ hτ n f hf hfm ℓ hℓ
  exact lemma2_sharp_of_bounds π m M hm hlower hupper hmass τ hτ n f hf hfm ℓ hℓ

end TailBound
