import TailBound.StoppedScore

/-! Backward harmonic functions and the exact reverse-process marginal. -/

open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
namespace RefreshData
variable (D : RefreshData α n)

lemma revGen_quotient {t : ℝ} (ht : t ≤ D.horizon) (q : (Fin n → α) → ℝ)
    (x : Fin n → α) :
    D.revGen t (fun y => q y/D.p t y) x =
      refreshGenerator D.π q x/D.p t x -
        (q x/D.p t x)*(refreshGenerator D.π (D.p t) x/D.p t x) := by
  rw [generator_weighted_form D.π D.mass, generator_weighted_form D.π D.mass]
  unfold revGen mean
  simp only [Finset.sum_div,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  unfold ratio
  field_simp [(D.p_pos ht x).ne',(D.p_pos ht (Function.update x i a)).ne']
  ring

noncomputable def backwardNum (g : (Fin n → α) → ℝ) (t : ℝ) : (Fin n → α) → ℝ :=
  heat D.π g (2-t)

noncomputable def backward (φ : (Fin n → α) → ℝ) (t : ℝ) (x : Fin n → α) : ℝ :=
  D.backwardNum (fun y => D.p 2 y*φ y) t x / D.p t x

lemma hasDerivAt_backwardNum (g : (Fin n → α) → ℝ) (t : ℝ) (x : Fin n → α) :
    HasDerivAt (fun u => D.backwardNum g u x)
      (-refreshGenerator D.π (D.backwardNum g t) x) t := by
  simpa [backwardNum] using (hasDerivAt_heat D.π D.mass g x (2-t)).comp t
    ((hasDerivAt_id t).const_sub 2)

lemma hasDerivAt_backward (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ D.horizon)
    (x : Fin n → α) :
    HasDerivAt (fun u => D.backward φ u x) (-D.revGen t (D.backward φ t) x) t := by
  have hd := (D.hasDerivAt_backwardNum (fun y => D.p 2 y*φ y) t x).div
    (D.hasDerivAt_p t x) (D.p_pos ht x).ne'
  convert hd using 1
  change -D.revGen t (fun y => D.backwardNum (fun z => D.p 2 z*φ z) t y / D.p t y) x = _
  rw [D.revGen_quotient ht]
  field_simp [(D.p_pos ht x).ne']
  ring

lemma backward_terminal (φ : (Fin n → α) → ℝ) (x : Fin n → α) :
    D.backward φ 2 x = φ x := by
  simp only [backward,backwardNum,sub_self,heat_zero]
  exact mul_div_cancel_left₀ _ (D.p_pos D.obs_le_horizon x).ne'

lemma backward_nonneg (φ : (Fin n → α) → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : t ≤ 2) (x : Fin n → α) : 0 ≤ D.backward φ t x :=
  div_nonneg (heat_nonneg D.π D.πnonneg _
    (fun y => mul_nonneg (D.p_pos D.obs_le_horizon y).le (hφ y)) (sub_nonneg.mpr ht) x)
    (D.p_pos (ht.trans D.obs_le_horizon) x).le

lemma backward_density (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ D.horizon) :
    ∑ x, D.density t x*D.backward φ t x =
      ∑ x, D.density 2 x*φ x := by
  have he (x : Fin n → α) : D.density t x*D.backward φ t x =
      tensorWeight D.π n x*D.backwardNum (fun y => D.p 2 y*φ y) t x := by
    unfold density backward
    field_simp [(D.p_pos ht x).ne']
  simp_rw [he]
  change mean (tensorWeight D.π n) (heat D.π (fun y => D.p 2 y*φ y) (2-t)) = _
  rw [mean_heat D.π D.mass]
  simp only [mean,density,mul_assoc]

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

/-- Harmonic testing identifies the V marginal without a separate path-space
construction or an assumed law for the reverse process. -/
theorem backward_pairing (a φ : (Fin n → α) → ℝ) :
    ∑ s, C.terminal s*(a s.start*φ s.v) =
      ∑ x, D.density θ x*(a x*D.backward φ θ x) := by
  let F : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.backward φ t s.v
  have hF (k : ℕ) (hk : k<C.grid.K) (s : CoupledState α n) :
      ContinuousOn (fun t => F t s) (Set.Icc (C.grid.z k) (C.grid.z (k+1))) := by
    intro t ht
    exact ((D.hasDerivAt_backward φ
      (((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon) s.v).const_mul _).continuousAt.continuousWithinAt
  have hd (k : ℕ) (hk : k<C.grid.K) (t : ℝ)
      (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1))) :
      HasDerivWithinAt (fun u => C.pairing k u (F u)) 0
        (Set.Icc (C.grid.z k) (C.grid.z (k+1))) t := by
    have hh := eventFlow_derivative _ _ _ _ _ (C.flow.flow k hk) F
      (fun t s => a s.start*(-D.revGen t (D.backward φ t) s.v))
      (fun u hu s => ((D.hasDerivAt_backward φ
        (((C.grid.cell_subset hk hu).2).trans D.obs_le_horizon) s.v).const_mul _).hasDerivWithinAt) t ht
    have hz : (∑ s, C.law k t s *
        (a s.start*(-D.revGen t (D.backward φ t) s.v) +
          eventGenerator (couplingNext (D.cellBarrier C.grid k)) (D.couplingRate ℓ θ t) (F t) s)) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      dsimp [F]
      rw [D.coupling_generator_start_mul,D.coupling_generator_v]
      ring
    rwa [hz] at hh
  have hnode (k : ℕ) (hk : k+1<C.grid.K) :
      C.pairing (k+1) (C.grid.z (k+1)) (F (C.grid.z (k+1))) =
        C.pairing k (C.grid.z (k+1)) (F (C.grid.z (k+1))) := by
    rw [C.pairing_node k hk]
    rfl
  have hh := Talagrand.chain_eq C.grid.pos C.grid.mono
    (fun k hk => C.pairing_continuous hk F (hF k hk)) hd
    (fun k hk => intervalIntegral.intervalIntegrable_const) hnode
  simp only [intervalIntegral.integral_zero,Finset.sum_const_zero,add_zero] at hh
  rw [C.pairing_initial] at hh
  simpa only [C.grid.last,C.grid.first,F,pairing,terminal,killNode,
    D.backward_terminal] using hh

theorem v_marginal (hθ : θ ≤ 2) (φ : (Fin n → α) → ℝ) :
    ∑ s, C.terminal s*φ s.v = ∑ x, D.density 2 x*φ x := by
  have hh := C.backward_pairing (fun _ => 1) φ
  simp only [one_mul] at hh
  rw [D.backward_density φ (hθ.trans D.obs_le_horizon)] at hh
  exact hh

end StoppedCoupling
end RefreshData
end TailBound
