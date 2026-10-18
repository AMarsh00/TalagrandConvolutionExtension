import TailBound.LayerDiscrepancy
import TailBound.BandTail

/-! The layer decomposition in Lemma 2. The constants here are allowed to
depend on the fixed refresh time and marginal law, as in Theorem 1. -/
open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound
attribute [local instance] Classical.propDecidable

lemma sum_inv_sqrt_le (m : ℕ) :
    ∑ j ∈ Finset.range m, (Real.sqrt ((j:ℝ)+1))⁻¹ ≤ 2*Real.sqrt m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    have hp : 0 < Real.sqrt ((k:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    have hsq := Real.sq_sqrt (show 0 ≤ (k:ℝ)+1 by positivity)
    have hmul : Real.sqrt (k:ℝ)*Real.sqrt ((k:ℝ)+1) ≤ (k:ℝ)+1/2 := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg k)]
      calc
        _ ≤ Real.sqrt (((k:ℝ)+1/2)^2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = _ := Real.sqrt_sq (by positivity)
    have hstep : (Real.sqrt ((k:ℝ)+1))⁻¹ ≤ 2*Real.sqrt ((k:ℝ)+1)-2*Real.sqrt (k:ℝ) := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hp).mpr
      nlinarith
    linarith

namespace RefreshData
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

noncomputable def layerConstant : ℝ :=
  8*(1+D.horizontalConstant)*(D.κ*D.Λ*Real.sqrt (50*(D.κ/D.Λ+(D.κ-1)))+
    D.κ*D.Λ^2*(50*(D.κ/D.Λ+(D.κ-1))))

lemma layerConstant_nonneg : 0 ≤ D.layerConstant := by
  have hk := D.κ_gt_one
  have hl := D.Λ_pos
  have hk0 : 0 ≤ D.κ := by linarith
  have hk1 : 0 ≤ D.κ-1 := by linarith
  unfold layerConstant horizontalConstant
  positivity

lemma layerCoefficient_le {r : ℝ} (hr : 0 ≤ r) :
    D.layerCoefficient r ≤ D.layerConstant/Real.sqrt (r+1) := by
  let A := 50*(D.κ/D.Λ+(D.κ-1))
  have hk := D.κ_gt_one
  have hl := D.Λ_pos
  have hk0 : 0 ≤ D.κ := by linarith
  have hk1 : 0 ≤ D.κ-1 := by linarith
  have hu : 0 < r+1 := by linarith
  have hS := D.layerScoreCoefficient_nonneg hr
  have hs : 0 < Real.sqrt (r+1) := Real.sqrt_pos.mpr hu
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmul : D.layerScoreCoefficient r*(r+1) ≤ A := by
    have he : D.layerScoreCoefficient r*(r+1) = 50*(D.κ/D.Λ+(D.κ-1)/(r+1)) := by
      unfold layerScoreCoefficient
      field_simp [hl.ne',hu.ne']
      <;> ring
    rw [he]
    have hh : (D.κ-1)/(r+1) ≤ D.κ-1 :=
      (div_le_iff₀ hu).mpr (by nlinarith)
    dsimp [A]
    linarith
  have hroot : Real.sqrt (D.layerScoreCoefficient r)*Real.sqrt (r+1) ≤ Real.sqrt A := by
    rw [← Real.sqrt_mul hS]
    exact Real.sqrt_le_sqrt hmul
  have hsle : Real.sqrt (r+1) ≤ r+1 := by
    have hh := Real.sq_sqrt hu.le
    nlinarith [Real.sqrt_nonneg (r+1)]
  have hlin : D.layerScoreCoefficient r*Real.sqrt (r+1) ≤ A :=
    (mul_le_mul_of_nonneg_left hsle hS).trans hmul
  apply (le_div_iff₀ hs).mpr
  have hh1 := mul_le_mul_of_nonneg_left hroot (show 0 ≤ D.κ*D.Λ by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hlin (show 0 ≤ D.κ*D.Λ^2 by positivity)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hh1 hh2)
    (show 0 ≤ 8*(1+D.horizontalConstant) by unfold horizontalConstant; positivity)
  dsimp [layerCoefficient,layerConstant,A] at *
  nlinarith

noncomputable def layerWeight (ℓ θ : ℝ) (r : ℕ) (x : Fin n → α) : ℝ :=
  if (r:ℝ) ≤ D.gap ℓ θ x ∧ D.gap ℓ θ x < r+1 then 1 else 0

lemma active_partition (ℓ θ : ℝ) {m : ℕ} (hm : 10 ≤ m) (x : Fin n → α) :
    (if 10 ≤ D.gap ℓ θ x then (1:ℝ) else 0) =
      (∑ r ∈ Finset.Ico 10 m, D.layerWeight ℓ θ r x)+
        (if (m:ℝ) ≤ D.gap ℓ θ x then 1 else 0) := by
  let z := D.gap ℓ θ x
  have hmR : (10:ℝ) ≤ m := by exact_mod_cast hm
  by_cases hz : 10 ≤ z
  · by_cases hzm : (m:ℝ) ≤ z
    · have he : ∀ r ∈ Finset.Ico 10 m, D.layerWeight ℓ θ r x = 0 := by
        intro r hr
        have hrm : (r:ℝ)+1 ≤ m := by exact_mod_cast (Finset.mem_Ico.mp hr).2
        unfold layerWeight
        rw [if_neg (by change ¬((r:ℝ) ≤ z ∧ z < r+1); intro h; linarith [h.2]) ]
      rw [Finset.sum_eq_zero he]
      change (if 10 ≤ z then (1:ℝ) else 0) = 0+(if (m:ℝ) ≤ z then 1 else 0)
      simp [hz,hzm]
    · let k := Nat.floor z
      have hz0 : 0 ≤ z := by linarith
      have hk10 : 10 ≤ k := Nat.le_floor (by exact_mod_cast hz)
      have hkm : k < m := Nat.floor_lt hz0 |>.mpr (lt_of_not_ge hzm)
      have hkl : (k:ℝ) ≤ z := Nat.floor_le hz0
      have hku : z < k+1 := Nat.lt_floor_add_one z
      have he : (∑ r ∈ Finset.Ico 10 m, D.layerWeight ℓ θ r x) = 1 := by
        rw [Finset.sum_eq_single k]
        · unfold layerWeight
          exact if_pos ⟨hkl,hku⟩
        · intro r hr hrk
          unfold layerWeight
          apply if_neg
          intro h
          have hkr : k = r := by
            dsimp [k]
            exact Nat.floor_eq_iff hz0 |>.mpr h
          exact hrk hkr.symm
        · intro hnot
          exact False.elim (hnot (Finset.mem_Ico.mpr ⟨hk10,hkm⟩))
      rw [he]
      change (if 10 ≤ z then (1:ℝ) else 0) = 1+(if (m:ℝ) ≤ z then 1 else 0)
      simp [hz,hzm]
  · have he : ∀ r ∈ Finset.Ico 10 m, D.layerWeight ℓ θ r x = 0 := by
      intro r hr
      have hr10 : (10:ℝ) ≤ r := by exact_mod_cast (Finset.mem_Ico.mp hr).1
      unfold layerWeight
      apply if_neg
      change ¬((r:ℝ) ≤ z ∧ z < r+1)
      intro h; exact hz (hr10.trans h.1)
    have hzm : ¬(m:ℝ) ≤ z := fun h => hz (hmR.trans h)
    change (if 10 ≤ z then (1:ℝ) else 0) = _
    rw [Finset.sum_eq_zero he]
    change (if 10 ≤ z then (1:ℝ) else 0) = 0+(if (m:ℝ) ≤ z then 1 else 0)
    simp [hz,hzm]

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def testDifference (a φ : (Fin n → α) → ℝ) : ℝ :=
  (∑ s, C.terminal s*(a s.start*φ s.w))-(∑ s, C.terminal s*(a s.start*φ s.v))

lemma testDifference_sum_add {ι : Type*} (I : Finset ι)
    (a : ι → (Fin n → α) → ℝ) (b φ : (Fin n → α) → ℝ) :
    C.testDifference (fun x => (∑ i ∈ I, a i x)+b x) φ =
      (∑ i ∈ I, C.testDifference (a i) φ)+C.testDifference b φ := by
  unfold testDifference
  simp_rw [add_mul,mul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  simp only [Finset.sum_comm (s := Finset.univ) (t := I)]
  rw [Finset.sum_sub_distrib]
  ring

theorem active_tv_layers (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2) {m : ℕ} (hm : 10 ≤ m) :
    C.eventTV {x | 10 ≤ D.gap ℓ θ x} ≤
      (∑ r ∈ Finset.Ico 10 m, D.layerCoefficient r*D.layerMass ℓ θ r)+D.layerCoefficient m := by
  apply Finset.sup'_le
  intro E _
  let φ : (Fin n → α) → ℝ := fun x => if x ∈ E then 1 else 0
  have hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1 := fun x => by dsimp [φ]; split_ifs <;> norm_num
  change |C.testDifference (fun x => if 10 ≤ D.gap ℓ θ x then 1 else 0) φ| ≤ _
  have he : (fun x => if 10 ≤ D.gap ℓ θ x then (1:ℝ) else 0) =
      fun x => (∑ r ∈ Finset.Ico 10 m, D.layerWeight ℓ θ r x)+(if (m:ℝ) ≤ D.gap ℓ θ x then 1 else 0) :=
    funext (D.active_partition ℓ θ hm)
  rw [he,C.testDifference_sum_add]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro r _
    apply C.layer_test_bound hθ hθ2 _ φ (fun x => by unfold layerWeight; split_ifs <;> norm_num) hφ (Nat.cast_nonneg r)
    intro x hx
    unfold layerWeight at hx
    split_ifs at hx with hh
    · exact hh.1
    · contradiction
  · have hh := C.layer_test_bound hθ hθ2 (fun x => if (m:ℝ) ≤ D.gap ℓ θ x then 1 else 0) φ
      (fun x => by dsimp; split_ifs <;> norm_num) hφ (Nat.cast_nonneg m)
      (fun x hx => by dsimp at hx; split_ifs at hx with h; exact h; contradiction)
    apply hh.trans
    apply mul_le_of_le_one_right (D.layerCoefficient_nonneg (Nat.cast_nonneg m))
    calc
      _ ≤ ∑ x, D.density θ x := by
        apply Finset.sum_le_sum
        intro x _
        dsimp only
        by_cases hx : (m:ℝ) ≤ D.gap ℓ θ x
        · rw [if_pos hx,mul_one]
        · rw [if_neg hx,mul_zero]
          exact D.density_nonneg (hθ2.trans D.obs_le_horizon) x
      _ = 1 := D.density_mass θ

end StoppedCoupling
end RefreshData
end TailBound
