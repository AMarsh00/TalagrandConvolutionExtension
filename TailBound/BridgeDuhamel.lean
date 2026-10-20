import TailBound.FlowIntegration

/-! Duhamel test functions for the localized bridge comparison. -/

open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound

set_option linter.unusedSectionVars false

lemma eventGenerator_sum {S E Z : Type*} [Fintype E] [Fintype Z]
    (next : E → S → S) (rate : E → S → ℝ) (F : Z → S → ℝ) (s : S) :
    eventGenerator next rate (fun r => ∑ z, F z r) s = ∑ z, eventGenerator next rate (F z) s := by
  simp only [eventGenerator,← Finset.sum_sub_distrib,Finset.mul_sum]
  exact Finset.sum_comm

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
namespace RefreshData
variable (D : RefreshData α n)

noncomputable def bridgeU (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, D.endpointH t z x*D.bridgeQ φ t z x y

noncomputable def bridgeUDeriv (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, ((-D.revGen t (D.endpointH t z) x)*D.bridgeQ φ t z x y-
    D.endpointH t z x*D.bridgeGen t z (D.bridgeQ φ t z) x y)

noncomputable def perturbU (φ : (Fin n → α) → ℝ) (ℓ θ t : ℝ) (s : CoupledState α n) : ℝ :=
  ∑ z, D.endpointH t z s.v*D.bridgePerturbation ℓ θ t z (D.bridgeQ φ t z) s

lemma hasDerivAt_bridgeU (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) :
    HasDerivAt (fun u => D.bridgeU φ u x y) (D.bridgeUDeriv φ t x y) t := by
  have hh := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → α)))
    (fun z _ => (D.hasDerivAt_endpointH (ht.trans D.obs_le_horizon) z x).mul
      (D.hasDerivAt_bridgeQ φ ht z x y))
  simpa only [bridgeU,bridgeUDeriv,mul_neg,sub_eq_add_neg] using hh

lemma bridgeU_terminal (φ : (Fin n → α) → ℝ) (x y : Fin n → α) : D.bridgeU φ 2 x y = φ y := by
  simp only [bridgeU,D.bridgeQ_terminal,← Finset.sum_mul,D.endpointH_mass D.obs_le_horizon,one_mul]

lemma bridgeU_bounds (φ : (Fin n → α) → ℝ) (hφ : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1)
    {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) : 0 ≤ D.bridgeU φ t x y ∧ D.bridgeU φ t x y ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun z _ => mul_nonneg (D.endpointH_pos ht z x).le
      (D.bridgeQ_bounds ht φ hφ z x y).1)
  · calc
      _ ≤ ∑ z, D.endpointH t z x*1 := Finset.sum_le_sum (fun z _ =>
        mul_le_mul_of_nonneg_left (D.bridgeQ_bounds ht φ hφ z x y).2 (D.endpointH_pos ht z x).le)
      _ = 1 := by simp only [mul_one,D.endpointH_mass (ht.trans D.obs_le_horizon)]

lemma bridgeU_drift {ℓ θ t : ℝ} (ht : t ≤ 2) (B : Set (Fin n → α))
    (φ : (Fin n → α) → ℝ) (s : CoupledState α n) :
    D.bridgeUDeriv φ t s.v s.w+
      eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (fun r => D.bridgeU φ t r.v r.w) s =
      D.perturbU φ ℓ θ t s := by
  unfold bridgeUDeriv bridgeU perturbU
  rw [eventGenerator_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hh := D.endpoint_product_drift (ℓ := ℓ) (θ := θ) ht B z (D.bridgeQ φ t z)
    (fun x y => -D.bridgeGen t z (D.bridgeQ φ t z) x y) s
  simpa only [bridgePerturbation,mul_neg,sub_eq_add_neg,add_comm] using hh

lemma continuousOn_endpointH (z x : Fin n → α) :
    ContinuousOn (fun t => D.endpointH t z x) (Set.Iic (2:ℝ)) := fun t ht =>
  (D.hasDerivAt_endpointH (ht.trans D.obs_le_horizon) z x).continuousAt.continuousWithinAt

lemma continuousOn_bridgeQ (φ : (Fin n → α) → ℝ) (z x y : Fin n → α) :
    ContinuousOn (fun t => D.bridgeQ φ t z x y) (Set.Iic (2:ℝ)) := fun t ht =>
  (D.hasDerivAt_bridgeQ φ ht z x y).continuousAt.continuousWithinAt

lemma continuousOn_bridgeRate (z x : Fin n → α) (i : Fin n) (g : α) :
    ContinuousOn (fun t => D.bridgeRate t z x i g) (Set.Iic (2:ℝ)) := by
  have hh := (((D.continuousOn_ratio i g x).mono (fun t ht => ht.trans D.obs_le_horizon)).const_mul (D.π g)).mul
    ((D.continuousOn_endpointH z (Function.update x i g)).div (D.continuousOn_endpointH z x)
      (fun t ht => (D.endpointH_pos ht z x).ne'))
  exact hh.congr (fun t ht => (D.endpoint_rate_cancellation ht z x i g).symm)

lemma continuousOn_bridgeGen (z : Fin n → α) (q : ℝ → (Fin n → α) → (Fin n → α) → ℝ)
    (hq : ∀ x y, ContinuousOn (fun t => q t x y) (Set.Iic (2:ℝ))) (x y : Fin n → α) :
    ContinuousOn (fun t => D.bridgeGen t z (q t) x y) (Set.Iic (2:ℝ)) := by
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro g _
  exact (D.continuousOn_bridgeRate z x i g).mul ((hq _ _).sub (hq x y))

lemma continuousOn_endpointRate (ℓ θ : ℝ) (z : Fin n → α) (e : CouplingEvent α n) (s : CoupledState α n) :
    ContinuousOn (fun t => D.endpointRate ℓ θ t z e s) (Set.Iic (2:ℝ)) :=
  (((D.couplingRate_continuousOn ℓ θ e s).mono (fun t ht => ht.trans D.obs_le_horizon)).mul
    (D.continuousOn_endpointH z _)).div (D.continuousOn_endpointH z s.v)
      (fun t ht => (D.endpointH_pos ht z s.v).ne')

lemma continuousOn_endpointGen (ℓ θ : ℝ) (z : Fin n → α)
    (q : ℝ → (Fin n → α) → (Fin n → α) → ℝ)
    (hq : ∀ x y, ContinuousOn (fun t => q t x y) (Set.Iic (2:ℝ))) (s : CoupledState α n) :
    ContinuousOn (fun t => D.endpointGen ℓ θ t z (q t) s) (Set.Iic (2:ℝ)) := by
  apply continuousOn_finset_sum
  intro e _
  exact (D.continuousOn_endpointRate ℓ θ z e s).mul ((hq _ _).sub (hq s.v s.w))

lemma continuousOn_perturbU (φ : (Fin n → α) → ℝ) (ℓ θ : ℝ) (s : CoupledState α n) :
    ContinuousOn (fun t => D.perturbU φ ℓ θ t s) (Set.Iic (2:ℝ)) := by
  apply continuousOn_finset_sum
  intro z _
  apply (D.continuousOn_endpointH z s.v).mul
  exact (D.continuousOn_endpointGen ℓ θ z (D.bridgeQ φ · z) (D.continuousOn_bridgeQ φ z) s).sub
    (D.continuousOn_bridgeGen z (D.bridgeQ φ · z) (D.continuousOn_bridgeQ φ z) s.v s.w)

lemma revGen_sum {Z : Type*} [Fintype Z] (t : ℝ) (F : Z → (Fin n → α) → ℝ) (x : Fin n → α) :
    D.revGen t (fun y => ∑ z, F z y) x = ∑ z, D.revGen t (F z) x := by
  simp only [revGen,mean,← Finset.sum_sub_distrib,Finset.mul_sum]
  calc
    _ = ∑ i, ∑ z, ∑ g, D.π g * (D.ratio t i g x * (F z (Function.update x i g)-F z x)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma endpoint_diag_product {t : ℝ} (ht : t ≤ 2) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (x : Fin n → α) :
    D.revGen t (fun y => D.endpointH t z y*q y y) x =
      D.revGen t (D.endpointH t z) x*q x x+D.endpointH t z x*D.bridgeGen t z q x x := by
  unfold revGen mean bridgeGen
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  have hh := D.endpoint_rate_cancellation ht z x i g
  have he : D.π g*D.ratio t i g x*D.endpointH t z (Function.update x i g) =
      D.endpointH t z x*D.bridgeRate t z x i g := by
    have hp := (D.endpointH_pos ht z x).ne'
    field_simp [hp] at hh
    simpa only [mul_comm (D.endpointH t z x)] using hh
  linear_combination (q (Function.update x i g) (Function.update x i g)-q x x)*he

lemma bridgeU_diag_deriv (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ 2) (x : Fin n → α) :
    HasDerivAt (fun u => D.bridgeU φ u x x) (-D.revGen t (fun y => D.bridgeU φ t y y) x) t := by
  have he : D.bridgeUDeriv φ t x x = -D.revGen t (fun y => D.bridgeU φ t y y) x := by
    unfold bridgeUDeriv bridgeU
    rw [D.revGen_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [D.endpoint_diag_product ht]
    ring
  rw [← he]
  exact D.hasDerivAt_bridgeU φ ht x x

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

theorem harmonic_pairing (a : (Fin n → α) → ℝ) (H : ℝ → (Fin n → α) → ℝ)
    (hH : ∀ t, t ≤ 2 → ∀ x, HasDerivAt (fun u => H u x) (-D.revGen t (H t) x) t) :
    ∑ s, C.terminal s*(a s.start*H 2 s.v) = ∑ x, D.density θ x*(a x*H θ x) := by
  let F : ℝ → CoupledState α n → ℝ := fun t s => a s.start*H t s.v
  let dF : ℝ → CoupledState α n → ℝ := fun t s => a s.start*(-D.revGen t (H t) s.v)
  have hd : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k+1))) t := by
    intro k hk t ht s
    exact ((hH t (C.grid.cell_subset hk ht).2 s.v).const_mul _).hasDerivWithinAt
  have hg : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      dF t s+eventGenerator (couplingNext (D.cellBarrier C.grid k)) (D.couplingRate ℓ θ t) (F t) s = 0 := by
    intro k hk t ht s
    dsimp [F,dF]
    rw [D.coupling_generator_start_mul,D.coupling_generator_v]
    ring
  have hh := C.dynkin_eq F dF (fun _ _ => 0) hd (fun _ _ _ => continuousOn_const) hg (fun _ _ _ => rfl)
  simpa only [integrate,pairing,F,mul_zero,Finset.sum_const_zero,intervalIntegral.integral_zero,add_zero] using hh

theorem duhamel_initial (a φ : (Fin n → α) → ℝ) :
    (∑ s, C.terminal s*(a s.start*φ s.w)) =
      (∑ x, D.density θ x*(a x*D.bridgeU φ θ x x))+
      C.integrate (fun t s => a s.start*D.perturbU φ ℓ θ t s) := by
  let F : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.bridgeU φ t s.v s.w
  let dF : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.bridgeUDeriv φ t s.v s.w
  have hd : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k+1))) t := by
    intro k hk t ht s
    exact ((D.hasDerivAt_bridgeU φ (C.grid.cell_subset hk ht).2 s.v s.w).const_mul _).hasDerivWithinAt
  have hH : C.CellContinuous (fun t s => a s.start*D.perturbU φ ℓ θ t s) := by
    intro k hk s
    exact ((D.continuousOn_perturbU φ ℓ θ s).const_mul _).mono
      (fun t ht => (C.grid.cell_subset hk ht).2)
  have hgen : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      dF t s+eventGenerator (couplingNext (D.cellBarrier C.grid k)) (D.couplingRate ℓ θ t) (F t) s =
        a s.start*D.perturbU φ ℓ θ t s := by
    intro k hk t ht s
    dsimp [dF,F]
    rw [D.coupling_generator_start_mul,← mul_add,D.bridgeU_drift (C.grid.cell_subset hk ht).2]
  have hh := C.dynkin_eq F dF _ hd hH hgen (fun _ _ _ => rfl)
  simpa only [F,D.bridgeU_terminal] using hh

/-- Localized Duhamel identity for the stopped coupling. -/
theorem duhamel (a φ : (Fin n → α) → ℝ) :
    (∑ s, C.terminal s*(a s.start*φ s.w))-(∑ s, C.terminal s*(a s.start*φ s.v)) =
      C.integrate (fun t s => a s.start*D.perturbU φ ℓ θ t s) := by
  have hd := C.duhamel_initial a φ
  have hv := C.harmonic_pairing a (fun t x => D.bridgeU φ t x x)
    (fun t ht x => D.bridgeU_diag_deriv φ ht x)
  simp only [D.bridgeU_terminal] at hv
  rw [← hv] at hd
  linarith

end StoppedCoupling
end RefreshData
end TailBound
