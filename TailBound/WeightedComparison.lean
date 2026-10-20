import TailBound.PowerWeight

/-! Terminal power-weight comparison used in the band argument. -/

open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
namespace RefreshData
variable (D : RefreshData α n)

noncomputable def comparisonWeight (ℓ θ t : ℝ) (s : CoupledState α n) : ℝ :=
  D.comparisonFactor ℓ θ t s*D.p t s.w

lemma comparisonWeight_pos {t : ℝ} (ht : t ≤ D.horizon) (ℓ θ : ℝ) (s : CoupledState α n) :
    0 < D.comparisonWeight ℓ θ t s :=
  mul_pos (D.comparisonFactor_pos ℓ θ t s) (D.p_pos ht s.w)

lemma comparisonFactor_initial {θ : ℝ} (hθ : θ ≤ D.horizon) (ℓ : ℝ) (x : Fin n → α) :
    D.comparisonFactor ℓ θ θ ⟨x,x,x,true⟩ = (D.p θ x)⁻¹ := by
  unfold comparisonFactor
  simp only [if_true]
  rw [show (D.exponent ℓ θ x-1)*D.logP θ x-D.exponent ℓ θ x*D.logP θ x = -D.logP θ x by ring]
  rw [Real.exp_neg,logP,Real.exp_log (D.p_pos hθ x)]

lemma comparisonWeight_exp {t : ℝ} (ht : t ≤ D.horizon) (ℓ θ : ℝ) (s : CoupledState α n) :
    D.comparisonWeight ℓ θ t s =
      if s.alive then Real.exp (D.logP t s.w-(1-D.exponent ℓ θ s.start)*D.logP t s.v-
        D.exponent ℓ θ s.start*D.logP θ s.start)
      else Real.exp (D.logP t s.w-D.logP t s.v+
        D.exponent ℓ θ s.start*(ℓ+1-D.logP θ s.start)) := by
  unfold comparisonWeight comparisonFactor
  have hp : D.p t s.w = Real.exp (D.logP t s.w) := (Real.exp_log (D.p_pos ht s.w)).symm
  rw [hp]
  split_ifs <;> rw [← Real.exp_add] <;> congr 1 <;> ring

lemma comparisonWeight_crossing {ℓ θ j : ℝ} (s : CoupledState α n)
    (hs : 10 ≤ D.gap ℓ θ s.start) (hw : ℓ+j < D.logP 2 s.w) (hv : D.logP 2 s.v ≤ ℓ+1) :
    Real.exp (4+j) < D.comparisonWeight ℓ θ 2 s := by
  have hg := D.active_gap hs
  have hd := D.exponent_bounds ℓ θ s.start
  have hdR : D.exponent ℓ θ s.start*(D.gap ℓ θ s.start+1) = 5 := by
    rw [exponent,if_pos hs]
    field_simp [show D.gap ℓ θ s.start+1 ≠ 0 by linarith]
  have hc : D.logP θ s.start = ℓ-D.gap ℓ θ s.start := by linarith [hg.1]
  rw [D.comparisonWeight_exp D.obs_le_horizon]
  split_ifs
  · apply Real.exp_lt_exp.mpr
    have hh := band_exponent_before_stop ℓ (D.gap ℓ θ s.start) 5 (D.exponent ℓ θ s.start)
      (D.logP 2 s.w) (D.logP 2 s.v) j hd.1 (by linarith [hd.2]) hdR hw hv
    rw [hc]
    linarith
  · apply Real.exp_lt_exp.mpr
    have hh := band_exponent_after_stop ℓ (D.gap ℓ θ s.start) 5 (D.exponent ℓ θ s.start)
      (D.logP 2 s.w) (D.logP 2 s.v) (ℓ+1) j hd.1 hdR hw hv le_rfl
    rw [hc]
    linarith

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

/-- The terminal band comparison, localized by any nonnegative
function of the starting point. It uses the manuscript's power coupling. -/
theorem weighted_comparison (hθ : θ ≤ 2) (a φ : (Fin n → α) → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x) :
    ∑ s, C.terminal s*(a s.start*D.comparisonWeight ℓ θ 2 s*φ s.w) ≤
      ∑ s, C.terminal s*(a s.start*φ s.v) := by
  classical
  let q := D.backwardNum (fun y => D.p 2 y*φ y)
  have hq (t : ℝ) (ht : t ≤ 2) (x : Fin n → α) : 0 ≤ q t x :=
    heat_nonneg D.π D.πnonneg _ (fun y => mul_nonneg (D.p_pos D.obs_le_horizon y).le (hφ y))
      (sub_nonneg.mpr ht) x
  let F : ℝ → CoupledState α n → ℝ := fun t s =>
    a s.start*(D.comparisonFactor ℓ θ t s*q t s.w)
  let dF : ℝ → CoupledState α n → ℝ := fun t s => a s.start*
    (D.comparisonFactor ℓ θ t s*(1-D.coupledExponent ℓ θ s)*
      (refreshGenerator D.π (D.p t) s.v/D.p t s.v)*q t s.w-
      D.comparisonFactor ℓ θ t s*refreshGenerator D.π (q t) s.w)
  let J : (Fin n → α) → ℝ := fun x => a x*D.backward φ θ x
  have hd : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k+1))) t := by
    intro k hk t ht s
    have hh := ((D.hasDerivAt_comparisonFactor
      (((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon) ℓ θ s).mul
      (D.hasDerivAt_backwardNum (fun y => D.p 2 y*φ y) t s.w)).const_mul (a s.start)
    convert hh.hasDerivWithinAt using 1 <;> dsimp [F,dF,q] <;> ring
  have hbound : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      C.law k t s ≠ 0 → dF t s + eventGenerator (couplingNext (D.cellBarrier C.grid k))
        (D.couplingRate ℓ θ t) (F t) s ≤ 0 := by
    intro k hk t ht s _
    have hh := D.comparison_drift (ℓ := ℓ) (θ := θ) (C.grid.cell_subset hk ht).2
      (D.cellBarrier C.grid k) (fun x hx => D.logP_ge_of_inside_cell C.grid hk x hx t ht)
      (q t) (hq t (C.grid.cell_subset hk ht).2) s
    dsimp [dF,F]
    rw [D.coupling_generator_start_mul]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (ha s.start) hh]
  have hkill : ∀ k, k+1<C.grid.K → ∀ s, C.law k (C.grid.z (k+1)) s ≠ 0 →
      F (C.grid.z (k+1)) (killNode (D.barrier ℓ (C.grid.z (k+1))) s) ≤ F (C.grid.z (k+1)) s := by
    intro k hk s _
    apply mul_le_mul_of_nonneg_left _ (ha s.start)
    apply mul_le_mul_of_nonneg_right _ (hq _ (C.grid.range (by omega)).2 s.w)
    exact D.comparisonFactor_kill_le ℓ θ _ _ (fun _ hx => hx) s
  have hinit : C.pairing 0 (C.grid.z 0) (F (C.grid.z 0)) ≤ ∑ x, D.density θ x*J x := by
    rw [C.pairing_initial]
    simp only [C.grid.first]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (D.density_nonneg (hθ.trans D.obs_le_horizon) x)
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (D.comparisonFactor_kill_le ℓ θ θ (D.barrier ℓ θ) (fun _ hx => hx) ⟨x,x,x,true⟩)
        (hq θ hθ x)) (ha x)
    dsimp [F,J]
    rw [D.comparisonFactor_initial (hθ.trans D.obs_le_horizon)] at hh
    simpa only [backward,div_eq_mul_inv,mul_comm (D.p θ x)⁻¹,q] using hh
  have hh := C.dynkin_le hθ F dF (fun _ _ => 0) J hd
    (fun _ _ _ => continuousOn_const) hbound hkill hinit
  have hz (k : ℕ) (t : ℝ) : C.pairing k t (fun _ => 0) = 0 := by simp [pairing]
  simp only [hz,intervalIntegral.integral_zero,Finset.sum_const_zero,add_zero] at hh
  rw [C.backward_pairing a φ]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [F,q,backwardNum,sub_self,heat_zero,comparisonWeight]
  ring

end StoppedCoupling
end RefreshData
end TailBound
