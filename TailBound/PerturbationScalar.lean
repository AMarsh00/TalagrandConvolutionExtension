import TailBound.BridgeQuadratic

/-!
# Perturbation Scalar

Scalar estimates for the two disjoint branches of the switched coupling.
-/

namespace TailBound

lemma switchedPower_below (d r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 ≤ d) :
    r ≤ switchedPower d r := by
  have hh := Real.rpow_le_one hr.le hr1 hd
  simp only [switchedPower, if_pos hr1]
  linarith

lemma switchedPower_above (d r : ℝ) (hr : 1 ≤ r) (hd : 0 ≤ d) :
    switchedPower d r ≤ r := by
  rcases eq_or_lt_of_le hr with h | h
  · subst r; simp [switchedPower]
  · simp only [switchedPower, if_neg (not_le.mpr h)]
    exact Real.rpow_le_self_of_one_le hr (by linarith)

lemma switchedPower_difference (d r : ℝ) (hr : 0 < r) :
    switchedPower d r - r = Talagrand.powerRatio d r * (1 - r) := by
  rcases lt_trichotomy r 1 with h | h | h
  · simp only [switchedPower, if_pos h.le]
    linarith [Talagrand.one_sub_rpow_eq (d := d) hr h]
  · subst r; simp [switchedPower]
  · simp only [switchedPower, if_neg (not_le.mpr h)]
    linarith [Talagrand.rpow_sub_eq (d := d) h]

/-- Weighted Young inequality, using only a squared coefficient estimate. -/
lemma coefficient_young {A w c v u : ℝ} (hw : 0 < w) (hc : c ^ 2 ≤ A * w) :
    2 * u * (c * v) ≤ u ^ 2 * A + w * v ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg u)
  have hs := sq_nonneg (w * v - u * c)
  have hh' : 0 ≤ w * (u ^ 2 * A + w * v ^ 2 - 2 * u * (c * v)) := by nlinarith
  exact by nlinarith

lemma two_difference_square (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

lemma square_difference_lipschitz {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    (a ^ 2 - b ^ 2) ^ 2 ≤ 4 * (a - b) ^ 2 := by
  have hsum : (a + b) ^ 2 ≤ 4 := by nlinarith
  calc
    _ = (a + b) ^ 2 * (a - b) ^ 2 := by ring
    _ ≤ 4 * (a - b) ^ 2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)

/-- The two branches never contribute simultaneously. The factor κ uses
one conditioned-rate bound, not a dimension-dependent sum of rates. -/
lemma split_coefficient_young {κ L d r l π : ℝ}
    (hκ : 0 < κ) (_hL : 0 ≤ L) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hr : 0 < r) (hl : 0 < l) (hπ : 0 < π)
    (hlow : 1 ≤ κ * l) (hupp : l ≤ κ)
    (hc : Talagrand.powerRatio d r ≤ L * d)
    (v w u : ℝ) :
    2 * u * (π * l / r * max (r - switchedPower d r) 0 * v+
      π * max (switchedPower d r - r) 0 * w) ≤
      u ^ 2 * (π * κ * (L * d) ^ 2 * (r - 1) ^ 2) + π * l * (v ^ 2 + w ^ 2) := by
  have hcn := Talagrand.powerRatio_nonneg hd hd1 hr
  have hc2 : (Talagrand.powerRatio d r) ^ 2 ≤ (L * d) ^ 2 := by
    nlinarith [mul_self_le_mul_self hcn hc]
  have hdiff := switchedPower_difference d r hr
  rcases le_total r 1 with hr1 | hr1
  · have hb := switchedPower_below d r hr hr1 hd
    rw [max_eq_right (sub_nonpos.mpr hb), max_eq_left (sub_nonneg.mpr hb)]
    simp only [mul_zero, zero_mul, zero_add]
    have hcoef : (π * (switchedPower d r - r)) ^ 2 ≤ (π * κ * (L * d) ^ 2 * (r - 1) ^ 2) * (π * l) := by
      calc
        _ = π ^ 2 * (Talagrand.powerRatio d r) ^ 2 * (r - 1) ^ 2 := by rw [hdiff]; ring
        _ ≤ π ^ 2 * (L * d) ^ 2 * (r - 1) ^ 2 := by gcongr
        _ ≤ π ^ 2 * (L * d) ^ 2 * (r - 1) ^ 2 * (κ * l) := le_mul_of_one_le_right (by positivity) hlow
        _ = _ := by ring
    have hy := coefficient_young (u := u) (v := w) (mul_pos hπ hl) hcoef
    nlinarith [mul_nonneg (mul_pos hπ hl).le (sq_nonneg v)]
  · have hb := switchedPower_above d r hr1 hd
    rw [max_eq_left (sub_nonneg.mpr hb), max_eq_right (sub_nonpos.mpr hb)]
    simp only [mul_zero, zero_mul, add_zero]
    have hlr : l / r ^ 2 ≤ κ := by
      apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      nlinarith [mul_nonneg hκ.le (by nlinarith : 0 ≤ r ^ 2 - 1)]
    have hcoef : (π * l / r * (r - switchedPower d r)) ^ 2 ≤ (π * κ * (L * d) ^ 2 * (r - 1) ^ 2) * (π * l) := by
      calc
        _ = π ^ 2 * l * (l / r ^ 2) * (Talagrand.powerRatio d r) ^ 2 * (r - 1) ^ 2 := by
          have he : r - switchedPower d r = Talagrand.powerRatio d r * (r - 1) := by linarith
          rw [he]; field_simp
        _ ≤ π ^ 2 * l * κ * (L * d) ^ 2 * (r - 1) ^ 2 := by gcongr
        _ = _ := by ring
    have hy := coefficient_young (u := u) (v := v) (mul_pos hπ hl) hcoef
    nlinarith [mul_nonneg (mul_pos hπ hl).le (sq_nonneg w)]

end TailBound
