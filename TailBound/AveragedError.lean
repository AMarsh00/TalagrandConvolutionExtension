import TailBound.InactiveBands

/-!
# Averaged Error

An explicit measurable error majorant for the fixed-band recurrence.
-/
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

variable (D : RefreshData α n)

lemma intervalIntegrable_sum_apply {ι : Type*} (I : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ I, IntervalIntegrable (g i) volume 1 2) :
    IntervalIntegrable (fun t => ∑ i ∈ I, g i t) volume 1 2 := by
  have hh := IntervalIntegrable.sum I hg
  convert hh using 1
  funext t
  simp only [Finset.sum_apply]

noncomputable def errorMajorant (ℓ : ℝ) (m Q : ℕ) (θ : ℝ) : ℝ :=
  (∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r * D.startBand θ (ℓ - r - 1))+
  D.layerCoefficient m+
  ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ)) * D.startBand θ (ℓ - 10 + q)

omit [Nonempty α] in
lemma errorMajorant_integrable (ℓ : ℝ) (m Q : ℕ) :
    IntervalIntegrable (D.errorMajorant ℓ m Q) volume 1 2 := by
  apply IntervalIntegrable.add
  · apply IntervalIntegrable.add
    · exact intervalIntegrable_sum_apply (Finset.Ico 10 m)
        (fun r θ => D.layerCoefficient r * D.startBand θ (ℓ - r - 1))
        (fun r _ => (D.intervalIntegrable_startBand _).const_mul _)
    · exact intervalIntegral.intervalIntegrable_const
  · exact intervalIntegrable_sum_apply (Finset.range Q)
      (fun q θ => Real.exp (11 - (q : ℝ)) * D.startBand θ (ℓ - 10 + q))
      (fun q _ => (D.intervalIntegrable_startBand _).const_mul _)

omit [DecidableEq α] in
lemma coefficient_sum_bound (m : ℕ) :
    ∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r ≤ 2 * D.layerConstant * Real.sqrt m := by
  calc
    _ ≤ ∑ r ∈ Finset.range m, D.layerCoefficient r :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2)
        (fun r _ _ => D.layerCoefficient_nonneg (Nat.cast_nonneg r))
    _ ≤ ∑ r ∈ Finset.range m, D.layerConstant * (Real.sqrt ((r : ℝ) + 1))⁻¹ :=
      Finset.sum_le_sum (fun r _ => by simpa only [div_eq_mul_inv] using D.layerCoefficient_le (Nat.cast_nonneg r))
    _ = D.layerConstant * (∑ r ∈ Finset.range m, (Real.sqrt ((r : ℝ) + 1))⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ D.layerConstant * (2 * Real.sqrt m) :=
      mul_le_mul_of_nonneg_left (TailBound.sum_inv_sqrt_le m) D.layerConstant_nonneg
    _ = _ := by ring

lemma shifted_exp_sum_bound (Q : ℕ) :
    ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ)) ≤ 2 * Real.exp 11 := by
  simp_rw [sub_eq_add_neg, Real.exp_add]
  rw [← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left (TailBound.sum_exp_neg_le_two Q) (Real.exp_pos 11).le]

omit [Nonempty α] in
lemma startBand_average_le {ℓ r : ℝ} (hℓ : 64 ≤ ℓ) (hr : ℓ / 2 ≤ r) :
    ∫ θ in (1 : ℝ)..2, D.startBand θ r ≤ 768 / (D.m * ℓ) := by
  have hl : 0 < ℓ := by linarith
  have hh := D.startBand_window_bound r (by linarith)
  apply hh.trans
  calc
    384 / (D.m * r) ≤ 384 / (D.m * (ℓ / 2)) := div_le_div_of_nonneg_left (by norm_num)
      (mul_pos D.mpos (by linarith)) (mul_le_mul_of_nonneg_left hr D.mpos.le)
    _ = _ := by ring

noncomputable def averageConstant : ℝ :=
  (1536 / D.m) * D.layerConstant + 2 * D.layerConstant + (1536 * Real.exp 11) / D.m

omit [DecidableEq α] in
lemma averageConstant_pos : 0 < D.averageConstant := by
  have hm := D.mpos
  have hC := D.layerConstant_nonneg
  unfold averageConstant
  positivity

theorem errorMajorant_average {ℓ : ℝ} (hℓ : 64 ≤ ℓ) (m Q : ℕ)
    (hmlo : ℓ / 2 - 1 ≤ m) (hmhi : (m : ℝ) ≤ ℓ / 2) :
    ∫ θ in (1 : ℝ)..2, D.errorMajorant ℓ m Q θ ≤ D.averageConstant / Real.sqrt ℓ := by
  have hl : 0 < ℓ := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hl
  have hsq := Real.sq_sqrt hl.le
  have hsle : Real.sqrt ℓ ≤ ℓ := by nlinarith [Real.sqrt_nonneg ℓ]
  have hmpos := D.mpos
  have hC := D.layerConstant_nonneg
  have hmge : 0 < (m : ℝ) + 1 := by positivity
  have hsm : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hmge
  have hroot : Real.sqrt ℓ ≤ 2 * Real.sqrt ((m : ℝ) + 1) := by
    have hh := Real.sq_sqrt hmge.le
    nlinarith [Real.sqrt_nonneg ℓ, Real.sqrt_nonneg ((m : ℝ) + 1)]
  have htail : D.layerCoefficient m ≤ 2 * D.layerConstant / Real.sqrt ℓ := by
    apply (D.layerCoefficient_le (Nat.cast_nonneg m)).trans
    apply (div_le_div_iff₀ hsm hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hroot hC]
  have hfirst : (∫ θ in (1 : ℝ)..2,
      ∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r * D.startBand θ (ℓ - r - 1)) ≤
      ((1536 / D.m) * D.layerConstant) / Real.sqrt ℓ := by
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
      _ ≤ (2 * D.layerConstant * Real.sqrt m) * (768 / (D.m * ℓ)) :=
        mul_le_mul_of_nonneg_right (D.coefficient_sum_bound m) (by positivity)
      _ ≤ (2 * D.layerConstant * Real.sqrt ℓ) * (768 / (D.m * ℓ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity)
      _ = _ := by
        field_simp [hmpos.ne', hl.ne', hs.ne']
        nlinarith
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
  unfold averageConstant
  rw [add_div, add_div]
  linarith

namespace StoppedCoupling

variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

theorem errorMajorant_bound (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2) (m Q : ℕ) (hm : 10 ≤ m)
    (hQ : ∀ x, D.logP θ x ≤ ℓ - 10 + Q) :
    C.eventTV {x | 10 ≤ D.gap ℓ θ x} + C.inactiveBand ℓ ≤ D.errorMajorant ℓ m Q θ := by
  have ha := C.active_tv_layers hθ hθ2 hm
  have hb := C.inactive_band_bound hθ2 Q hQ
  have he : (∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r * D.layerMass ℓ θ r) =
      ∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r * D.startBand θ (ℓ - r - 1) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr10 : (10 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Ico.mp hr).1
    rw [D.layerMass_eq_startBand ℓ θ r (by linarith)]
  rw [he] at ha
  exact add_le_add ha hb

end StoppedCoupling
end TailBound.RefreshData
