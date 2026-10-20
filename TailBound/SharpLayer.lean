import TailBound.SharpAlgebra
import TailBound.LayerAveraging

/-!
# Sharp Layer
-/

open scoped BigOperators

namespace TailBound.RefreshData

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

variable (D : RefreshData α n)

/-- The band factor K = κ^(3/2) sqrt Λ. -/
noncomputable def sharpK : ℝ := Real.sqrt (D.κ ^ 3 * D.Λ)

omit [DecidableEq α] in
lemma sharpK_sq : D.sharpK ^ 2 = D.κ ^ 3 * D.Λ := by
  unfold sharpK
  exact Real.sq_sqrt (by have := D.κ_gt_one; have := D.Λ_pos; positivity)

omit [DecidableEq α] in
lemma sharpK_ge_one : 1 ≤ D.sharpK := by
  have hk := D.κ_gt_one
  have hl := D.Λ_bounds.1
  have h3 : 1 ≤ D.κ ^ 3 := one_le_pow₀ (by linarith)
  have hh : 1 ≤ D.κ ^ 3 * D.Λ := by nlinarith
  simpa [sharpK] using Real.sqrt_le_sqrt hh

omit [DecidableEq α] in
lemma sharpK_pos : 0 < D.sharpK := lt_of_lt_of_le zero_lt_one D.sharpK_ge_one

/-- This prefactor depends only on the alphabet and marginal lower bound. -/
noncomputable def sharpLocalConstant : ℝ := 8 * (1 + D.horizontalConstant)

omit [DecidableEq α] in
lemma sharpLocalConstant_pos : 0 < D.sharpLocalConstant := by
  unfold sharpLocalConstant horizontalConstant
  positivity

omit [DecidableEq α] in
lemma layerCoefficient_sharp {r : ℝ} (hr : 0 ≤ r) :
    D.layerCoefficient r ≤ D.sharpLocalConstant *
      (8 * D.sharpK / Real.sqrt (r + 1) + 72 * D.κ ^ 2 * D.Λ / (r + 1) + 64 * D.sharpK ^ 2 / (r + 1) ^ 2) := by
  have hk := D.κ_gt_one
  have hl := D.Λ_pos
  have hS : D.layerScoreCoefficient r ≤
      64 * (D.κ / (D.Λ * (r + 1)) + (D.κ - 1) / (r + 1) ^ 2) * (1 : ℝ) := by
    have hn : 0 ≤ D.κ / (D.Λ * (r + 1)) + (D.κ - 1) / (r + 1) ^ 2 := by
      have : 0 ≤ D.κ - 1 := by linarith
      positivity
    unfold layerScoreCoefficient
    linarith
  have hh := Sharp.DA_layer_bound D.κ_gt_one D.Λ_bounds.1 D.Λ_bounds.2
    D.sharpK_sq D.sharpK_pos.le D.sharpLocalConstant_pos.le
    (show 1 ≤ r + 1 by linarith) (show (0 : ℝ) ≤ 1 by norm_num) hS
    (show D.layerCoefficient r ≤ D.sharpLocalConstant *
      (D.κ * D.Λ * Real.sqrt (D.layerScoreCoefficient r * 1) + D.κ * D.Λ ^ 2 * D.layerScoreCoefficient r) by
        simp only [mul_one]; exact le_rfl)
  simpa only [mul_one] using hh

omit [DecidableEq α] in
lemma coefficient_sum_sharp {ℓ : ℝ} (hℓ : 64 ≤ ℓ) (hK : D.sharpK ^ 2 ≤ ℓ)
    (m : ℕ) (hm : 0 < m) (hmhi : (m : ℝ) ≤ ℓ) :
    ∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r ≤
      512 * D.sharpLocalConstant * D.sharpK * Real.sqrt ℓ := by
  have hk := D.κ_gt_one
  have hl := D.Λ_pos
  have hKn := D.sharpK_pos.le
  have hC := D.sharpLocalConstant_pos.le
  have hE : 0 ≤ D.κ ^ 2 * D.Λ := by positivity
  have hKs : D.sharpK ≤ Real.sqrt ℓ := by
    simpa only [Real.sqrt_sq hKn] using Real.sqrt_le_sqrt hK
  have habs := Sharp.kappa_sq_Lam_log_le hk D.Λ_bounds.1 D.Λ_bounds.2
    D.sharpK_sq D.sharpK_ge_one hK (show 1 ≤ ℓ by linarith)
  calc
    _ ≤ ∑ r ∈ Finset.range m, D.layerCoefficient r :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun r hr => Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2)
        (fun r _ _ => D.layerCoefficient_nonneg (Nat.cast_nonneg r))
    _ ≤ ∑ r ∈ Finset.range m, D.sharpLocalConstant *
        (8 * D.sharpK / Real.sqrt ((r : ℝ) + 1) + 72 * D.κ ^ 2 * D.Λ / (r + 1) + 64 * D.sharpK ^ 2 / (r + 1) ^ 2) :=
      Finset.sum_le_sum (fun r _ => D.layerCoefficient_sharp (Nat.cast_nonneg r))
    _ = D.sharpLocalConstant * (∑ r ∈ Finset.range m,
        (8 * D.sharpK / Real.sqrt ((r : ℝ) + 1) + 72 * D.κ ^ 2 * D.Λ / (r + 1) + 64 * D.sharpK ^ 2 / (r + 1) ^ 2)) :=
      (Finset.mul_sum ..).symm
    _ ≤ D.sharpLocalConstant * (16 * D.sharpK * Real.sqrt m+
        72 * D.κ ^ 2 * D.Λ * (1 + Real.log m) + 128 * D.sharpK ^ 2) :=
      mul_le_mul_of_nonneg_left (Sharp.sum_layer_coeff_le hKn hE m) hC
    _ ≤ _ := by
      have hlog := Real.log_le_log (show (0 : ℝ) < m by exact_mod_cast hm) hmhi
      have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmhi) hKn
      have ht2 := mul_le_mul_of_nonneg_left hlog hE
      have ht3 := mul_le_mul_of_nonneg_left hKs hKn
      have hh : 16 * D.sharpK * Real.sqrt m + 72 * D.κ ^ 2 * D.Λ * (1 + Real.log m) + 128 * D.sharpK ^ 2 ≤
          512 * D.sharpK * Real.sqrt ℓ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh hC]

omit [DecidableEq α] in
lemma layerCoefficient_tail_sharp {ℓ r : ℝ} (hℓ : 64 ≤ ℓ) (hK : D.sharpK ^ 2 ≤ ℓ)
    (hr : 0 ≤ r) (hrlo : ℓ / 2 ≤ r + 1) :
    D.layerCoefficient r ≤ 512 * D.sharpLocalConstant * D.sharpK / Real.sqrt ℓ := by
  have hl : 0 < ℓ := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hl
  have hu : 0 < r + 1 := by linarith
  have hsu : 0 < Real.sqrt (r + 1) := Real.sqrt_pos.mpr hu
  have hsq := Real.sq_sqrt hl.le
  have hsuq := Real.sq_sqrt hu.le
  have hKn := D.sharpK_pos.le
  have hKs : D.sharpK ≤ Real.sqrt ℓ := by
    simpa only [Real.sqrt_sq hKn] using Real.sqrt_le_sqrt hK
  have hJ : D.κ ^ 2 * D.Λ ≤ D.sharpK ^ 2 := by
    rw [D.sharpK_sq]
    have hk := D.κ_gt_one
    have hlp := D.Λ_pos
    nlinarith [mul_nonneg (show 0 ≤ D.κ - 1 by linarith) (show 0 ≤ D.κ ^ 2 * D.Λ by positivity)]
  have hroot : Real.sqrt ℓ ≤ 2 * Real.sqrt (r + 1) := by nlinarith [Real.sqrt_nonneg (r + 1)]
  have h1 : 8 * D.sharpK / Real.sqrt (r + 1) ≤ 16 * D.sharpK / Real.sqrt ℓ := by
    apply (div_le_div_iff₀ hsu hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hroot hKn]
  have h2 : 72 * D.κ ^ 2 * D.Λ / (r + 1) ≤ 144 * D.sharpK / Real.sqrt ℓ := by
    apply (div_le_div_iff₀ hu hs).mpr
    have ha := mul_le_mul_of_nonneg_right hJ hs.le
    have hb := mul_le_mul_of_nonneg_left hKs (mul_nonneg hKn hs.le)
    have hc := mul_le_mul_of_nonneg_left hrlo hKn
    nlinarith [show D.sharpK * (Real.sqrt ℓ) ^ 2 = D.sharpK * ℓ by rw [hsq]]
  have h3 : 64 * D.sharpK ^ 2 / (r + 1) ^ 2 ≤ 256 * D.sharpK / Real.sqrt ℓ := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hu) hs).mpr
    have ha := mul_le_mul_of_nonneg_left hKs (mul_nonneg hKn hs.le)
    have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ ℓ / 2) hrlo 2) hKn
    have hc : D.sharpK * ℓ ≤ D.sharpK * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith : ℓ ≤ ℓ ^ 2) hKn
    nlinarith [show D.sharpK * (Real.sqrt ℓ) ^ 2 = D.sharpK * ℓ by rw [hsq]]
  apply (D.layerCoefficient_sharp hr).trans
  have hh : 8 * D.sharpK / Real.sqrt (r + 1) + 72 * D.κ ^ 2 * D.Λ / (r + 1) + 64 * D.sharpK ^ 2 / (r + 1) ^ 2 ≤
      512 * D.sharpK / Real.sqrt ℓ := by
    calc
      _ ≤ 16 * D.sharpK / Real.sqrt ℓ + 144 * D.sharpK / Real.sqrt ℓ + 256 * D.sharpK / Real.sqrt ℓ :=
        add_le_add (add_le_add h1 h2) h3
      _ = 416 * (D.sharpK / Real.sqrt ℓ) := by ring
      _ ≤ 512 * (D.sharpK / Real.sqrt ℓ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hKn hs.le)
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hh D.sharpLocalConstant_pos.le
  convert hmul using 1; ring

end TailBound.RefreshData
