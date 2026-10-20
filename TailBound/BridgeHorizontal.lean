import TailBound.BridgeChi

/-!
# Bridge Horizontal

Dimension-free horizontal energy estimate for the explicit product bridge.
The integrated estimate for the stopped coupling is proved in
`IntegratedHorizontal.lean`.
-/

open scoped BigOperators

namespace TailBound

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

theorem bridge_horizontal_energy (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (hmass : ∑ u, π u = 1) {a r m : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hm : 0 < m) (hmin : ∀ u, m ≤ π u)
    (z x y : ι → α) (f : (ι → α) → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    (∑ i, ∑ g, π g * (bridgeH π (r * a) (z i) g / bridgeH π (r * a) (z i) (x i)) *
      ((dx (bridgePayoff π a r z f) i g x y) ^ 2 +
        (dx (bridgePayoff π a r z f) i g x (Function.update y i g)) ^ 2)) ≤
      (3 * Fintype.card α * r) / (4 * (1 - a) * m ^ 2) := by
  let μ := bridgeMarginals π a r z x y
  let c := mean (productWeight μ) f
  let V := fun i => mean (μ i) (fun u => (coordinateAverage μ f i u - c) ^ 2)
  have hp (i : ι) (u : α) : 0 < μ i u :=
    bridgeLaw_pos π hπ ha0.le ha1 hr0.le hr1 (z i) (x i) (y i) u
  have hra0 := mul_nonneg hr0.le ha0.le
  have hra1 : r * a < 1 := by nlinarith
  have hmassμ (i : ι) : ∑ u, μ i u = 1 :=
    bridgeLaw_mass π hmass a r (z i) (x i) (y i)
      (bridgeH_pos π hπ hra0 hra1 (z i) (x i)).ne'
  have hV : ∀ i, 0 ≤ V i := fun i =>
    Finset.sum_nonneg fun u _ => mul_nonneg (hp i u).le (sq_nonneg _)
  have hsum : (∑ i, V i) ≤ (1 / 4 : ℝ) := by
    have h := level_one_product_le_quarter μ (fun i u => (hp i u).le) hmassμ f hf
    exact h.1.trans h.2
  have hlocal (i : ι) (g : α) :
      π g * (bridgeH π (r * a) (z i) g / bridgeH π (r * a) (z i) (x i)) *
        ((dx (bridgePayoff π a r z f) i g x y) ^ 2 +
          (dx (bridgePayoff π a r z f) i g x (Function.update y i g)) ^ 2) ≤
      (3 * r / ((1 - a) * m ^ 2)) * V i := by
    have hxH := bridgeH_pos π hπ hra0 hra1 (z i) (x i)
    have hgH := bridgeH_pos π hπ hra0 hra1 (z i) g
    have hw : 0 ≤ π g * (bridgeH π (r * a) (z i) g / bridgeH π (r * a) (z i) (x i)) :=
      mul_nonneg (hπ g).le (div_nonneg hgH.le hxH.le)
    obtain ⟨he₁, he₂⟩ := bridge_horizontal_differences π hπ hmass ha0.le ha1 hr0.le hr1 z x y i g f c
    have hc₁ := weighted_cauchy (μ i)
      (fun u => bridgeLaw π a r (z i) g (y i) u - μ i u)
      (fun u => coordinateAverage μ f i u - c) (hp i)
    have hc₂ := weighted_cauchy (μ i)
      (fun u => bridgeLaw π a r (z i) g g u - bridgeLaw π a r (z i) (x i) g u)
      (fun u => coordinateAverage μ f i u - c) (hp i)
    have he : π g * (bridgeH π (r * a) (z i) g / bridgeH π (r * a) (z i) (x i)) *
        ((dx (bridgePayoff π a r z f) i g x y) ^ 2 +
          (dx (bridgePayoff π a r z f) i g x (Function.update y i g)) ^ 2) ≤
        (bridgeChi π a r (z i) (x i) (y i) g (y i) +
          bridgeChi π a r (z i) (x i) (y i) g g) * V i := by
      rw [he₁, he₂]
      have hh := mul_le_mul_of_nonneg_left (add_le_add hc₁ hc₂) hw
      convert hh using 1
      simp only [bridgeChi, μ, bridgeMarginals, V, mean]
      simp_rw [sub_sq_comm (bridgeLaw π a r (z i) g (y i) _),
        sub_sq_comm (bridgeLaw π a r (z i) g g _)]
      ring
    exact he.trans (mul_le_mul_of_nonneg_right
      (bridgeChi_pair_bound π hπ hmass ha0 ha1 hr0 hr1 hm hmin (z i) (x i) (y i) g) (hV i))
  have ham := sub_pos.mpr ha1
  have hC : 0 ≤ (Fintype.card α : ℝ) * (3 * r / ((1 - a) * m ^ 2)) := by positivity
  calc
    _ ≤ ∑ i, ∑ _g : α, (3 * r / ((1 - a) * m ^ 2)) * V i := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun g _ => hlocal i g
    _ = ((Fintype.card α : ℝ) * (3 * r / ((1 - a) * m ^ 2))) * ∑ i, V i := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [← Finset.mul_sum]
      ring
    _ ≤ ((Fintype.card α : ℝ) * (3 * r / ((1 - a) * m ^ 2))) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = (3 * Fintype.card α * r) / (4 * (1 - a) * m ^ 2) := by field_simp

lemma refresh_kappa_lower {a m M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hm : 0 < m) (hm1 : m ≤ 1) (hmM : m ≤ M) :
    1 / (1 - a) ≤ (a + (1 - a) * M) / ((1 - a) * m) := by
  have ham := sub_pos.mpr ha1
  have hnum : m ≤ a + (1 - a) * M := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hm1),
      mul_nonneg ham.le (sub_nonneg.mpr hmM)]
  apply (div_le_div_iff₀ ham (mul_pos ham hm)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnum ham.le]

/-- Horizontal energy with constant 3|α|/(4m²), where m is a positive
lower bound on π. -/
theorem bridge_horizontal_energy_kappa (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (hmass : ∑ u, π u = 1) {a r m M : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hm : 0 < m) (hmin : ∀ u, m ≤ π u) (hm1 : m ≤ 1) (hmM : m ≤ M)
    (z x y : ι → α) (f : (ι → α) → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    (∑ i, ∑ g, π g * (bridgeH π (r * a) (z i) g / bridgeH π (r * a) (z i) (x i)) *
      ((dx (bridgePayoff π a r z f) i g x y) ^ 2 +
        (dx (bridgePayoff π a r z f) i g x (Function.update y i g)) ^ 2)) ≤
      (3 * Fintype.card α / (4 * m ^ 2)) * ((a + (1 - a) * M) / ((1 - a) * m)) * r := by
  have ham := sub_pos.mpr ha1
  have hc : 0 ≤ (3 * Fintype.card α / (4 * m ^ 2)) * r := by positivity
  calc
    _ ≤ (3 * Fintype.card α * r) / (4 * (1 - a) * m ^ 2) :=
      bridge_horizontal_energy π hπ hmass ha0 ha1 hr0 hr1 hm hmin z x y f hf
    _ = ((3 * Fintype.card α / (4 * m ^ 2)) * r) * (1 / (1 - a)) := by field_simp
    _ ≤ ((3 * Fintype.card α / (4 * m ^ 2)) * r) * ((a + (1 - a) * M) / ((1 - a) * m)) :=
      mul_le_mul_of_nonneg_left (refresh_kappa_lower ha0.le ha1 hm hm1 hmM) hc
    _ = _ := by ring

end TailBound
