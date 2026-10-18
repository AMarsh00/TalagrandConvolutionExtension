import TailBound.StartingProfile

/-! Layerwise form of the local total-variation estimate. -/
open scoped BigOperators
namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

noncomputable def layerScoreCoefficient (r : ℝ) : ℝ :=
  50*(D.κ/(D.Λ*(r+1))+(D.κ-1)/(r+1)^2)

noncomputable def layerCoefficient (r : ℝ) : ℝ :=
  8*(1+D.horizontalConstant)*(D.κ*D.Λ*Real.sqrt (D.layerScoreCoefficient r)+
    D.κ*D.Λ^2*D.layerScoreCoefficient r)

lemma Λ_pos : 0 < D.Λ := div_pos
  (mul_pos (lt_trans zero_lt_one D.κ_gt_one) D.logκ_pos) (sub_pos.mpr D.κ_gt_one)

lemma Λ_bounds : 1 ≤ D.Λ ∧ D.Λ ≤ D.κ := by
  have hk : 0 < D.κ := lt_trans zero_lt_one D.κ_gt_one
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr D.κ_gt_one)).mpr
    have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hk) hk.le
    rw [mul_sub,mul_one,mul_inv_cancel₀ hk.ne'] at hh
    simpa only [one_mul] using hh
  · apply (div_le_iff₀ (sub_pos.mpr D.κ_gt_one)).mpr
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hk) hk.le

lemma layerScoreCoefficient_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ D.layerScoreCoefficient r := by
  have hk := D.κ_gt_one
  have hl := D.Λ_pos
  have hk' : 0 ≤ D.κ-1 := (sub_pos.mpr hk).le
  unfold layerScoreCoefficient
  positivity

lemma layerCoefficient_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ D.layerCoefficient r := by
  have hk := D.κ_gt_one
  have hl := D.Λ_pos
  have hs := D.layerScoreCoefficient_nonneg hr
  unfold layerCoefficient horizontalConstant
  positivity

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

theorem layer_test_bound (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2)
    (a φ : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (hlayer : ∀ x, a x ≠ 0 → r ≤ D.gap ℓ θ x) :
    |(∑ s, C.terminal s*(a s.start*φ s.w))-(∑ s, C.terminal s*(a s.start*φ s.v))| ≤
      D.layerCoefficient r*(∑ x, D.density θ x*a x) := by
  let P := ∑ x, D.density θ x*a x
  have hP : 0 ≤ P := Finset.sum_nonneg (fun x _ =>
    mul_nonneg (D.density_nonneg (hθ2.trans D.obs_le_horizon) x) (ha x))
  have hS : C.localScore a ≤ D.layerScoreCoefficient r*P := C.localScore_layer_bound hθ2 a ha hr hlayer
  have hroot : Real.sqrt (C.localScore a*P) ≤ Real.sqrt (D.layerScoreCoefficient r)*P := by
    calc
      _ ≤ Real.sqrt (D.layerScoreCoefficient r*P^2) := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right hS hP])
      _ = _ := by rw [Real.sqrt_mul (D.layerScoreCoefficient_nonneg hr),Real.sqrt_sq hP]
  have hh := C.localized_test_bound hθ hθ2 a φ ha hφ
  have hk : 0 ≤ D.κ := (lt_trans zero_lt_one D.κ_gt_one).le
  have hl := D.Λ_pos.le
  have hC : 0 ≤ 8*(1+D.horizontalConstant) := by unfold horizontalConstant; positivity
  have hmain := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hroot (mul_nonneg hk hl))
      (mul_le_mul_of_nonneg_left hS (mul_nonneg hk (sq_nonneg D.Λ)))) hC
  unfold layerCoefficient
  dsimp [P] at hmain
  nlinarith

theorem layer_tv_bound (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2) (A : Set (Fin n → α))
    {r : ℝ} (hr : 0 ≤ r) (hlayer : ∀ x ∈ A, r ≤ D.gap ℓ θ x) :
    C.eventTV A ≤ D.layerCoefficient r*(∑ x, D.density θ x*(if x ∈ A then 1 else 0)) := by
  apply Finset.sup'_le
  intro E _
  apply C.layer_test_bound hθ hθ2 (fun x => if x ∈ A then 1 else 0)
    (fun x => if x ∈ E then 1 else 0) (fun x => by dsimp; split_ifs <;> norm_num)
    (fun x => by dsimp; split_ifs <;> norm_num) hr
  intro x hx
  by_cases hxA : x ∈ A
  · exact hlayer x hxA
  · simp [hxA] at hx

end StoppedCoupling
end TailBound.RefreshData
