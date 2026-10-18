import TailBound.BandPartition

/-! The inverse-density harmonic function used for the inactive starting event. -/
open scoped BigOperators
namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

lemma hasDerivAt_inverse_p {t : ℝ} (ht : t ≤ 2) (x : Fin n → α) :
    HasDerivAt (fun u => (D.p u x)⁻¹) (-D.revGen t (fun y => (D.p t y)⁻¹) x) t := by
  have hh := (D.hasDerivAt_p t x).inv (D.p_pos (ht.trans D.obs_le_horizon) x).ne'
  have hg := D.revGen_quotient (ht.trans D.obs_le_horizon) (fun _ => 1) x
  have hz : refreshGenerator D.π (fun _ : Fin n → α => (1:ℝ)) x = 0 := by
    rw [generator_weighted_form D.π D.mass]
    simp [mean]
  simp only [one_div,hz,zero_sub] at hg
  convert hh using 1
  rw [hg]
  ring

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

/-- Finite-law form of the localized inverse-density martingale identity. -/
theorem inverse_density_pairing (a : (Fin n → α) → ℝ) :
    ∑ s, C.terminal s*(a s.start*(D.p 2 s.v)⁻¹) =
      ∑ x, D.density θ x*(a x*(D.p θ x)⁻¹) :=
  C.harmonic_pairing a (fun t x => (D.p t x)⁻¹) (fun t ht x => D.hasDerivAt_inverse_p ht x)

theorem inverse_density_tail (hθ : θ ≤ 2) (a : (Fin n → α) → ℝ)
    (ha : ∀ x, 0 ≤ a x) (b : ℝ) :
    (∑ s, C.terminal s*(a s.start*(if D.logP 2 s.v ≤ b then 1 else 0))) ≤
      Real.exp b*(∑ x, D.density θ x*(a x*(D.p θ x)⁻¹)) := by
  rw [← C.inverse_density_pairing a,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hμ := C.terminal_nonneg hθ s
  have hp := D.p_pos D.obs_le_horizon s.v
  by_cases hs : D.logP 2 s.v ≤ b
  · have he : D.p 2 s.v ≤ Real.exp b := by
      rw [← Real.exp_log hp]
      exact Real.exp_le_exp.mpr hs
    have hi : 1 ≤ Real.exp b*(D.p 2 s.v)⁻¹ := by
      have hh := mul_le_mul_of_nonneg_right he (inv_pos.mpr hp).le
      simpa only [mul_inv_cancel₀ hp.ne'] using hh
    rw [if_pos hs,mul_one]
    have hh := mul_le_mul_of_nonneg_left hi (mul_nonneg hμ (ha s.start))
    nlinarith
  · rw [if_neg hs,mul_zero,mul_zero]
    exact mul_nonneg (Real.exp_pos b).le (mul_nonneg hμ (mul_nonneg (ha s.start) (inv_pos.mpr hp).le))

/-- Starting above c costs exp(b-c) when the terminal density is at most exp b. -/
theorem high_start_tail (hθ : θ ≤ 2) (a : (Fin n → α) → ℝ)
    (ha : ∀ x, 0 ≤ a x) (b c : ℝ) (hc : ∀ x, a x ≠ 0 → c ≤ D.logP θ x) :
    (∑ s, C.terminal s*(a s.start*(if D.logP 2 s.v ≤ b then 1 else 0))) ≤
      Real.exp (b-c)*(∑ x, D.density θ x*a x) := by
  have hh := C.inverse_density_tail hθ a ha b
  have he : (∑ x, D.density θ x*(a x*(D.p θ x)⁻¹)) ≤
      Real.exp (-c)*(∑ x, D.density θ x*a x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : a x = 0
    · simp [hx]
    · have hp := D.p_pos (hθ.trans D.obs_le_horizon) x
      have hi : (D.p θ x)⁻¹ ≤ Real.exp (-c) := by
        rw [← Real.exp_log hp,← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have hh := hc x hx
        exact neg_le_neg hh
      have hh := mul_le_mul_of_nonneg_left hi
        (mul_nonneg (D.density_nonneg (hθ.trans D.obs_le_horizon) x) (ha x))
      nlinarith
  have he' := mul_le_mul_of_nonneg_left he (Real.exp_pos b).le
  rw [sub_eq_add_neg,Real.exp_add]
  nlinarith

end StoppedCoupling
end TailBound.RefreshData
