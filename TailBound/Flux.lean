import TailBound.Core

/-! Corrected threshold-flux symmetrization for Lemma 3, pp. 8-10. -/

open scoped BigOperators
namespace TailBound

noncomputable def threshold (u x : ℝ) : ℝ := if u < x then 1 else 0

lemma threshold_pair (u x y : ℝ) :
    (threshold u y - threshold u x) * (y - x) =
      |y - x| * (if min x y ≤ u ∧ u < max x y then 1 else 0) := by
  unfold threshold
  by_cases hx : u < x
  · by_cases hy : u < y
    · have hn : ¬ (min x y ≤ u ∧ u < max x y) := by
        intro h
        exact (lt_min hx hy).not_ge h.1
      simp [hx, hy]
    · have hyu : y ≤ u := le_of_not_gt hy
      have hyx : y ≤ x := by linarith
      simp [hx, hy, min_eq_right hyx, max_eq_left hyx, hyu,
        abs_of_nonpos (by linarith : y - x ≤ 0)]
  · by_cases hy : u < y
    · have hxu : x ≤ u := le_of_not_gt hx
      have hxy : x ≤ y := by linarith
      simp [hx, hy, min_eq_left hxy, max_eq_right hxy, hxu,
        abs_of_nonneg (by linarith : 0 ≤ y - x)]
    · have hn : ¬ (min x y ≤ u ∧ u < max x y) := by
        intro h
        exact h.2.not_ge (max_le (le_of_not_gt hx) (le_of_not_gt hy))
      simp [hx, hy]

variable {α : Type*} [Fintype α]

/-- The nonnegative flux that replaces the incorrect signed expression on p. 9. -/
theorem threshold_flux_symmetrization (c : α → α → ℝ) (p : α → ℝ) (u : ℝ)
    (hsym : ∀ x y, c x y = c y x) :
    -(∑ x, ∑ y, c x y * threshold u (p x) * (p y - p x)) =
      (1 / 2 : ℝ) * ∑ x, ∑ y, c x y * |p y - p x| *
        (if min (p x) (p y) ≤ u ∧ u < max (p x) (p y) then 1 else 0) := by
  have hs : (∑ x, ∑ y, c x y * threshold u (p y) * (p x - p y)) =
      ∑ x, ∑ y, c x y * threshold u (p x) * (p y - p x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsym y x]
  have he : (∑ x, ∑ y, c x y * |p y - p x| *
      (if min (p x) (p y) ≤ u ∧ u < max (p x) (p y) then 1 else 0)) =
      -(∑ x, ∑ y, c x y * threshold u (p x) * (p y - p x)) -
        (∑ x, ∑ y, c x y * threshold u (p y) * (p x - p y)) := by
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [mul_assoc, ← threshold_pair]
    ring
  rw [hs] at he
  linarith

theorem threshold_flux_nonneg (c : α → α → ℝ) (p : α → ℝ) (u : ℝ)
    (hsym : ∀ x y, c x y = c y x) (hc : ∀ x y, 0 ≤ c x y) :
    0 ≤ -(∑ x, ∑ y, c x y * threshold u (p x) * (p y - p x)) := by
  rw [threshold_flux_symmetrization c p u hsym]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (mul_nonneg (hc x y) (abs_nonneg _))
  split_ifs <;> norm_num

end TailBound
