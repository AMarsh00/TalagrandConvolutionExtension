import TailBound.BridgePerturbation
import TailBound.BridgeHorizontal

/-! Integrating the dimension-free horizontal estimate against the stopped law. -/
open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound.RefreshData
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

noncomputable def horizontalEnergy (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, D.endpointH t z x*(∑ i, ∑ g, D.bridgeRate t z x i g*
    ((dx (D.bridgeQ φ t z) i g x y)^2+(dx (D.bridgeQ φ t z) i g x (Function.update y i g))^2))

noncomputable def horizontalConstant : ℝ := 3*Fintype.card α/(4*D.m^2)

lemma totalEnergy_split (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) :
    D.totalEnergy φ t x y = D.syncEnergy φ t x y+D.horizontalEnergy φ t x y := by
  unfold totalEnergy syncEnergy horizontalEnergy bridgeEnergy edgeEnergy
  simp only [← Finset.sum_add_distrib,mul_add,Finset.sum_add_distrib]
  ring

lemma continuousOn_horizontalEnergy (φ : (Fin n → α) → ℝ) (x y : Fin n → α) :
    ContinuousOn (fun t => D.horizontalEnergy φ t x y) (Set.Iic (2:ℝ)) := by
  have hh := (D.continuousOn_totalEnergy φ x y).sub (D.continuousOn_syncEnergy φ x y)
  exact hh.congr (fun t _ => by simp only [D.totalEnergy_split]; ring)

lemma horizontalEnergy_bound (φ : (Fin n → α) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) :
    D.horizontalEnergy φ t x y ≤ D.horizontalConstant*D.κ := by
  have hm1 : D.m ≤ 1 := by
    have hh := Finset.single_le_sum (fun a _ => D.πnonneg a) (Finset.mem_univ (Classical.choice inferInstance))
    rw [D.mass] at hh
    exact (D.lower _).trans hh
  have hC : 0 ≤ D.horizontalConstant*D.κ := by
    have hk := D.κ_gt_one
    unfold horizontalConstant
    positivity
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simp only [horizontalEnergy,D.bridgeQ_terminal,dx,sub_self,zero_pow (by omega : 2 ≠ 0),
      add_zero,mul_zero,Finset.sum_const_zero]
    exact hC
  · have hr : bridgeTime t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hlocal (z : Fin n → α) :
        (∑ i, ∑ g, D.bridgeRate t z x i g*
          ((dx (D.bridgeQ φ t z) i g x y)^2+(dx (D.bridgeQ φ t z) i g x (Function.update y i g))^2)) ≤
          D.horizontalConstant*D.κ := by
      have hh := bridge_horizontal_energy_kappa D.π D.πpos D.mass D.retention_pos D.retention_lt_one
        (Real.exp_pos _) hr D.mpos D.lower hm1 D.m_le_M z x y φ hφ
      change _ ≤ D.horizontalConstant*D.κ*bridgeTime t at hh
      simpa only [bridgeRate,bridgeQ,mul_div_assoc] using hh.trans (mul_le_of_le_one_right hC hr.le)
    calc
      _ ≤ ∑ z, D.endpointH t z x*(D.horizontalConstant*D.κ) :=
        Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hlocal z) (D.endpointH_pos ht.le z x).le)
      _ = _ := by rw [← Finset.sum_mul,D.endpointH_mass (ht.le.trans D.obs_le_horizon),one_mul]

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

lemma integrate_start (a : (Fin n → α) → ℝ) :
    C.integrate (fun _ s => a s.start) = (2-θ)*(∑ x, D.density θ x*a x) := by
  unfold integrate
  calc
    _ = ∑ k ∈ Finset.range C.grid.K, (C.grid.z (k+1)-C.grid.z k)*(∑ x, D.density θ x*a x) := by
      apply Finset.sum_congr rfl
      intro k hk
      have he : (∫ t in C.grid.z k..C.grid.z (k+1), C.pairing k t (fun s => a s.start)) =
          ∫ _t in C.grid.z k..C.grid.z (k+1), (∑ x, D.density θ x*a x) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (C.grid.mono k (Finset.mem_range.mp hk))] at ht
        exact C.start_pairing_at a (Finset.mem_range.mp hk) t ht
      rw [he,intervalIntegral.integral_const]
      rfl
    _ = _ := by rw [← Finset.sum_mul,Finset.sum_range_sub,C.grid.last,C.grid.first]

lemma integrated_horizontal_bound (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2)
    (a φ : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    C.integrate (fun t s => a s.start*D.horizontalEnergy φ t s.v s.w) ≤
      D.horizontalConstant*D.κ*(∑ x, D.density θ x*a x) := by
  have hh := C.integrate_mono hθ2
    (fun k hk s => ((D.continuousOn_horizontalEnergy φ s.v s.w).const_mul _).mono
      (fun t ht => (C.grid.cell_subset hk ht).2))
    (F := fun t s => a s.start*D.horizontalEnergy φ t s.v s.w)
    (G := fun _ s => D.horizontalConstant*D.κ*a s.start)
    (fun _ _ _ => continuousOn_const) (by
      intro k hk t ht s _
      have hh := mul_le_mul_of_nonneg_left (D.horizontalEnergy_bound φ hφ (C.grid.cell_subset hk ht).2 s.v s.w) (ha s.start)
      nlinarith)
  rw [C.integrate_smul,C.integrate_start] at hh
  have hP : 0 ≤ ∑ x, D.density θ x*a x := Finset.sum_nonneg
    (fun x _ => mul_nonneg (D.density_nonneg (hθ2.trans D.obs_le_horizon) x) (ha x))
  have hC : 0 ≤ D.horizontalConstant*D.κ := by
    have hk := D.κ_gt_one
    unfold horizontalConstant
    positivity
  nlinarith [mul_nonneg (mul_nonneg hC hP) (by linarith : 0 ≤ θ-1)]

end StoppedCoupling
end TailBound.RefreshData
