import TailBound.InverseDensity

/-!
# Layer Score

Stopped score on a layer of starting log-density gaps.
-/
open scoped BigOperators

namespace TailBound.RefreshData.StoppedCoupling

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

lemma localScore_stopped_bound (hθ : θ ≤ 2) (a : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) :
    C.localScore a ≤ 2 * (D.κ - 1) / Real.log D.κ *
      ∑ x, D.density θ x * (a x * (D.exponent ℓ θ x) ^ 2) * (D.gap ℓ θ x + 1 + Real.log D.κ) := by
  rw [C.localScore_eq_scoreWork]
  exact C.stopped_score hθ _ (fun x => mul_nonneg (ha x) (sq_nonneg _))

lemma localScore_layer_bound (hθ : θ ≤ 2) (a : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x)
    {r : ℝ} (hr : 0 ≤ r) (hlayer : ∀ x, a x ≠ 0 → r ≤ D.gap ℓ θ x) :
    C.localScore a ≤ 50 * (D.κ / (D.Λ * (r + 1)) + (D.κ - 1) / (r + 1) ^ 2) * (∑ x, D.density θ x * a x) := by
  have hlocal (x : Fin n → α) (hx : a x ≠ 0) :
      (D.exponent ℓ θ x) ^ 2 * (D.gap ℓ θ x + 1 + Real.log D.κ) ≤
        25 * (1 / (r + 1) + Real.log D.κ / (r + 1) ^ 2) := by
    have hg := hlayer x hx
    have hrp : 0 < r + 1 := by linarith
    have hgp : 0 < D.gap ℓ θ x + 1 := by linarith
    unfold RefreshData.exponent
    split_ifs with hactive
    · calc
        _ = 25 * (1 / (D.gap ℓ θ x + 1) + Real.log D.κ / (D.gap ℓ θ x + 1) ^ 2) := by field_simp; ring
        _ ≤ _ := by gcongr; exact D.logκ_pos.le
    · have hl := D.logκ_pos
      simp only [zero_pow (by omega : 2 ≠ 0), zero_mul]
      positivity
  have hsum : (∑ x, D.density θ x * (a x * (D.exponent ℓ θ x) ^ 2) * (D.gap ℓ θ x + 1 + Real.log D.κ)) ≤
      25 * (1 / (r + 1) + Real.log D.κ / (r + 1) ^ 2) * (∑ x, D.density θ x * a x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : a x = 0
    · simp [hx]
    · have hh := mul_le_mul_of_nonneg_left (hlocal x hx)
        (mul_nonneg (D.density_nonneg (hθ.trans D.obs_le_horizon) x) (ha x))
      nlinarith
  have hcoef : 0 ≤ 2 * (D.κ - 1) / Real.log D.κ := div_nonneg (by linarith [D.κ_gt_one]) D.logκ_pos.le
  have hh := (C.localScore_stopped_bound hθ a ha).trans (mul_le_mul_of_nonneg_left hsum hcoef)
  have he : 2 * (D.κ - 1) / Real.log D.κ * (25 * (1 / (r + 1) + Real.log D.κ / (r + 1) ^ 2)) =
      50 * (D.κ / (D.Λ * (r + 1)) + (D.κ - 1) / (r + 1) ^ 2) := by
    unfold RefreshData.Λ
    field_simp [D.logκ_pos.ne', show D.κ ≠ 0 by linarith [D.κ_gt_one],
      show D.κ - 1 ≠ 0 by linarith [D.κ_gt_one]]
    ring
  rw [← mul_assoc, he] at hh
  exact hh

end TailBound.RefreshData.StoppedCoupling
