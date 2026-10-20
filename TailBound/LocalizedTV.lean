import TailBound.IntegratedPerturbation

/-!
# Localized TV

Localized total variation for the stopped coupling.
-/
open scoped BigOperators

namespace TailBound
attribute [local instance] Classical.propDecidable

lemma absolute_of_square_bound {J A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJ : J ^ 2 ≤ A ^ 2 + B ^ 2) : |J| ≤ A + B := by
  have ha := abs_nonneg J
  have hs : |J|^2 = J ^ 2 := sq_abs J
  nlinarith [mul_nonneg hA hB]

lemma tv_scalar_bound {J C κ L S P : ℝ} (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hJ : J ^ 2 ≤ 8 * (1 + C * κ) * κ * L ^ 2 * S * P + 64 * (κ * L ^ 2 * S) ^ 2) :
    |J| ≤ 8 * (1 + C) * (κ * L * Real.sqrt (S * P) + κ * L ^ 2 * S) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hsp := Real.sq_sqrt (mul_nonneg hS hP)
  have hc : 8 * (1 + C * κ) * κ ≤ (8 * (1 + C)) ^ 2 * κ ^ 2 := by
    have h₁ : (1 + C * κ) * κ ≤ (1 + C) * κ ^ 2 := by nlinarith [mul_nonneg hκ0 (sub_nonneg.mpr hκ)]
    have h₂ : 8 * (1 + C) ≤ (8 * (1 + C)) ^ 2 := by nlinarith
    have h₃ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg κ)
    nlinarith
  have hmain : 8 * (1 + C * κ) * κ * L ^ 2 * S * P ≤ (8 * (1 + C) * κ * L * Real.sqrt (S * P)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg (sq_nonneg L) hS) hP)
    calc
      _ ≤ ((8 * (1 + C)) ^ 2 * κ ^ 2) * (L ^ 2 * S * P) := by nlinarith
      _ = (8 * (1 + C) * κ * L * Real.sqrt (S * P)) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, hsp]; ring
  have hh := absolute_of_square_bound (J := J)
    (A := 8 * (1 + C) * κ * L * Real.sqrt (S * P)) (B := 8 * κ * L ^ 2 * S) (by positivity) (by positivity)
    (by nlinarith [hJ, hmain])
  have hc' : 8 * κ * L ^ 2 * S ≤ 8 * (1 + C) * κ * L ^ 2 * S := by
    have := mul_nonneg hC (mul_nonneg (mul_nonneg hκ0 (sq_nonneg L)) hS)
    nlinarith
  nlinarith

namespace RefreshData.StoppedCoupling

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

/-- Localized total variation for every nonnegative starting weight and
 every test function with values in [0,1]. Its constant depends only on π. -/
theorem localized_test_bound (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2)
    (a φ : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    |(∑ s, C.terminal s * (a s.start * φ s.w)) - (∑ s, C.terminal s * (a s.start * φ s.v))| ≤
      8 * (1 + D.horizontalConstant) * (D.κ * D.Λ * Real.sqrt (C.localScore a * (∑ x, D.density θ x * a x))+
        D.κ * D.Λ ^ 2 * C.localScore a) := by
  apply tv_scalar_bound (by unfold RefreshData.horizontalConstant; positivity) D.κ_gt_one.le
    (div_nonneg (mul_nonneg (lt_trans zero_lt_one D.κ_gt_one).le D.logκ_pos.le) (sub_pos.mpr D.κ_gt_one).le)
    (C.localScore_nonneg hθ2 a ha)
    (Finset.sum_nonneg (fun x _ => mul_nonneg (D.density_nonneg (hθ2.trans D.obs_le_horizon) x) (ha x)))
  exact C.localized_difference_sq hθ hθ2 a φ ha hφ

noncomputable def eventTV (A : Set (Fin n → α)) : ℝ := by
  classical
  exact (Finset.univ : Finset (Set (Fin n → α))).sup'
    Finset.univ_nonempty (fun E => |(∑ s, C.terminal s * ((if s.start ∈ A then 1 else 0) * (if s.w ∈ E then 1 else 0)))-
      (∑ s, C.terminal s * ((if s.start ∈ A then 1 else 0) * (if s.v ∈ E then 1 else 0)))|)

/-- Localized total variation as a supremum over endpoint events,
without normalization by the starting-event probability. -/
theorem localized_total_variation (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2) (A : Set (Fin n → α)) :
    C.eventTV A ≤ 8 * (1 + D.horizontalConstant)*
      (D.κ * D.Λ * Real.sqrt (C.localScore (fun x => if x ∈ A then 1 else 0)*
        (∑ x, D.density θ x * (if x ∈ A then 1 else 0)))+
      D.κ * D.Λ ^ 2 * C.localScore (fun x => if x ∈ A then 1 else 0)) := by
  classical
  apply Finset.sup'_le
  intro E _
  exact C.localized_test_bound hθ hθ2 (fun x => if x ∈ A then 1 else 0)
    (fun x => if x ∈ E then 1 else 0) (fun x => by dsimp; split_ifs <;> norm_num)
    (fun x => by dsimp; split_ifs <;> norm_num)

end RefreshData.StoppedCoupling
end TailBound
