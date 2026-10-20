import TailBound.Core

/-! Finite generator algebra and uniform bounds for switched rates.
These identities do not themselves construct the stochastic processes.
-/

open scoped BigOperators
namespace TailBound

variable {α : Type*} [Fintype α]

noncomputable def generator (q : α → α → ℝ) (f : α → ℝ) (x : α) : ℝ :=
  ∑ y, q x y * (f y - f x)

/-- Density-transform identity for the reversed generator. -/
theorem reverse_generator_identity (q : α → α → ℝ) (p f : α → ℝ)
    (x : α) (hp : p x ≠ 0) :
    generator q (fun y => p y * f y) x / p x -
      (f x / p x) * generator q p x =
      ∑ y, q x y * (p y / p x) * (f y - f x) := by
  unfold generator
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [hp]
  ring

/-- Cancellation of the density in the endpoint-conditioned jump rate. -/
theorem conditioned_rate_cancellation (px py hx hy c : ℝ)
    (hpx : px ≠ 0) (hpy : py ≠ 0) (hhx : hx ≠ 0) (hc : c ≠ 0) :
    (py / px) * ((c * hy / py) / (c * hx / px)) = hy / hx := by
  field_simp

/-- Difference between the coupled and synchronous generators. -/
theorem coupled_generator_difference (a b r dxy dx dy : ℝ) :
    r * min a b * dxy + r * max (a - b) 0 * dx + max (b - a) 0 * dy -
      r * a * dxy =
      r * max (a - b) 0 * (dx - dxy) + max (b - a) 0 * dy := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

/-- The square identity used in the quadratic Dynkin formula. -/
theorem generator_square (q : α → α → ℝ) (f : α → ℝ) (x : α) :
    generator q (fun y => (f y)^2) x - 2 * f x * generator q f x =
      ∑ y, q x y * (f y - f x)^2 := by
  unfold generator
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

noncomputable def switchedPower (δ r : ℝ) : ℝ :=
  if r ≤ 1 then r + 1 - r ^ δ else r ^ (1 - δ)

/-- Uniform positivity and upper bounds for the switched-power rate. -/
theorem switchedPower_bounds (δ r : ℝ) (hr : 0 < r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 < switchedPower δ r ∧ switchedPower δ r ≤ max 1 r := by
  unfold switchedPower
  split_ifs with hr1
  · have hlow := Real.self_le_rpow_of_le_one hr.le hr1 hδ1
    have hupp := Real.rpow_le_one hr.le hr1 hδ0
    rw [max_eq_left hr1]
    constructor <;> linarith
  · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    rw [max_eq_right hr1']
    exact ⟨Real.rpow_pos_of_pos hr _,
      Real.rpow_le_self_of_one_le hr1' (by linarith)⟩

theorem switchedPower_zero (r : ℝ) : switchedPower 0 r = r := by
  unfold switchedPower
  split_ifs <;> simp

theorem frozen_exponent_bound (R α : ℝ) (hα : 0 < α) (hR : 2 * α ≤ R) :
    0 ≤ α / (R + 1) ∧ α / (R + 1) < (1 / 2 : ℝ) := by
  have hd : 0 < R + 1 := by linarith
  constructor
  · exact div_nonneg hα.le hd.le
  · apply (div_lt_iff₀ hd).mpr
    linarith

end TailBound
