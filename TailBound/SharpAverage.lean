import TailBound.AveragedError
import TailBound.SharpLayer

/-!
# Sharp Average

Averaging the three layer terms with the explicit band factor K.
-/
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

variable (D : RefreshData α n)

noncomputable def sharpAverageConstant : ℝ :=
  (393216 / D.m + 512) * D.sharpLocalConstant + (1536 * Real.exp 11) / D.m

omit [DecidableEq α] in
lemma sharpAverageConstant_pos : 0 < D.sharpAverageConstant := by
  have := D.mpos
  have := D.sharpLocalConstant_pos
  unfold sharpAverageConstant
  positivity

theorem errorMajorant_average_sharp {ℓ : ℝ} (hℓ : 64 ≤ ℓ) (hK : D.sharpK ^ 2 ≤ ℓ) (m Q : ℕ)
    (hmlo : ℓ / 2 - 1 ≤ m) (hmhi : (m : ℝ) ≤ ℓ / 2) :
    ∫ θ in (1 : ℝ)..2, D.errorMajorant ℓ m Q θ ≤ (D.sharpAverageConstant * D.sharpK) / Real.sqrt ℓ := by
  have hl : 0 < ℓ := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hl
  have hsq := Real.sq_sqrt hl.le
  have hsle : Real.sqrt ℓ ≤ ℓ := by nlinarith [Real.sqrt_nonneg ℓ]
  have hmpos := D.mpos
  have hC := D.sharpLocalConstant_pos.le
  have hKn := D.sharpK_pos.le
  have hm : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have htail : D.layerCoefficient m ≤ 512 * D.sharpLocalConstant * D.sharpK / Real.sqrt ℓ :=
    D.layerCoefficient_tail_sharp hℓ hK (Nat.cast_nonneg m) (by linarith)
  have hfirst : (∫ θ in (1 : ℝ)..2,
      ∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r * D.startBand θ (ℓ - r - 1)) ≤
      ((393216 / D.m) * D.sharpLocalConstant * D.sharpK) / Real.sqrt ℓ := by
    rw [integral_finset_sum (fun r _ => (D.intervalIntegrable_startBand _).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r * (768 / (D.m * ℓ)) := by
        apply Finset.sum_le_sum
        intro r hr
        apply mul_le_mul_of_nonneg_left (D.startBand_average_le hℓ _) (D.layerCoefficient_nonneg (Nat.cast_nonneg r))
        have hrm : (r : ℝ) + 1 ≤ m := by exact_mod_cast (Finset.mem_Ico.mp hr).2
        linarith
      _ = (∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r) * (768 / (D.m * ℓ)) := (Finset.sum_mul ..).symm
      _ ≤ (512 * D.sharpLocalConstant * D.sharpK * Real.sqrt ℓ) * (768 / (D.m * ℓ)) :=
        mul_le_mul_of_nonneg_right (D.coefficient_sum_sharp hℓ hK m hm (by linarith)) (by positivity)
      _ = _ := by
        field_simp [hmpos.ne', hl.ne', hs.ne']
        rw [hsq]
        ring
  have hlast : (∫ θ in (1 : ℝ)..2,
      ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ)) * D.startBand θ (ℓ - 10 + q)) ≤
      ((1536 * Real.exp 11) / D.m) / Real.sqrt ℓ := by
    rw [integral_finset_sum (fun q _ => (D.intervalIntegrable_startBand _).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ)) * (768 / (D.m * ℓ)) := by
        apply Finset.sum_le_sum
        intro q _
        apply mul_le_mul_of_nonneg_left (D.startBand_average_le hℓ _) (Real.exp_pos _).le
        have hq := Nat.cast_nonneg (α := ℝ) q
        linarith
      _ = (∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))) * (768 / (D.m * ℓ)) := (Finset.sum_mul ..).symm
      _ ≤ (2 * Real.exp 11) * (768 / (D.m * ℓ)) :=
        mul_le_mul_of_nonneg_right (shifted_exp_sum_bound Q) (by positivity)
      _ = ((1536 * Real.exp 11) / D.m) / ℓ := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hs hsle
  unfold errorMajorant
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_sum_apply (Finset.Ico 10 m)
      (fun r θ => D.layerCoefficient r * D.startBand θ (ℓ - r - 1))
      (fun r _ => (D.intervalIntegrable_startBand _).const_mul _)).add
        intervalIntegral.intervalIntegrable_const)
    (intervalIntegrable_sum_apply (Finset.range Q)
      (fun q θ => Real.exp (11 - (q : ℝ)) * D.startBand θ (ℓ - 10 + q))
      (fun q _ => (D.intervalIntegrable_startBand _).const_mul _))]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_sum_apply (Finset.Ico 10 m)
      (fun r θ => D.layerCoefficient r * D.startBand θ (ℓ - r - 1))
      (fun r _ => (D.intervalIntegrable_startBand _).const_mul _))
    intervalIntegral.intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  norm_num only at *
  unfold sharpAverageConstant
  have hlastK : ((1536 * Real.exp 11) / D.m) / Real.sqrt ℓ ≤
      (((1536 * Real.exp 11) / D.m) * D.sharpK) / Real.sqrt ℓ := by
    apply div_le_div_of_nonneg_right _ hs.le
    exact le_mul_of_one_le_right (by positivity) D.sharpK_ge_one
  calc
    _ ≤ ((393216 / D.m) * D.sharpLocalConstant * D.sharpK) / Real.sqrt ℓ +
        (512 * D.sharpLocalConstant * D.sharpK) / Real.sqrt ℓ +
        (((1536 * Real.exp 11) / D.m) * D.sharpK) / Real.sqrt ℓ := by linarith
    _ = _ := by ring

end TailBound.RefreshData
