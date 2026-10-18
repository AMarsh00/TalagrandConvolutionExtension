import TailBound.BridgeDuhamel

/-! Quadratic Dynkin identity for the endpoint-conditioned bridge. -/

open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound.RefreshData

set_option linter.unusedSectionVars false
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

noncomputable def bridgeEnergy (t : ℝ) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (x y : Fin n → α) : ℝ :=
  ∑ i, ∑ g, D.bridgeRate t z x i g*(dxy q i g x y)^2

lemma bridgeGen_square (t : ℝ) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (x y : Fin n → α) :
    D.bridgeGen t z (fun u v => (q u v)^2) x y =
      2*q x y*D.bridgeGen t z q x y+D.bridgeEnergy t z q x y := by
  unfold bridgeGen bridgeEnergy dxy
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  ring

noncomputable def squareU (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, D.endpointH t z x*(D.bridgeQ φ t z x y)^2

noncomputable def squareUDeriv (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, ((-D.revGen t (D.endpointH t z) x)*(D.bridgeQ φ t z x y)^2-
    D.endpointH t z x*(2*D.bridgeQ φ t z x y*D.bridgeGen t z (D.bridgeQ φ t z) x y))

noncomputable def syncEnergy (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, D.endpointH t z x*D.bridgeEnergy t z (D.bridgeQ φ t z) x y

noncomputable def perturbSquare (φ : (Fin n → α) → ℝ) (ℓ θ t : ℝ) (s : CoupledState α n) : ℝ :=
  ∑ z, D.endpointH t z s.v*D.bridgePerturbation ℓ θ t z (fun x y => (D.bridgeQ φ t z x y)^2) s

lemma hasDerivAt_squareU (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) :
    HasDerivAt (fun u => D.squareU φ u x y) (D.squareUDeriv φ t x y) t := by
  have hh := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → α)))
    (fun z _ => (D.hasDerivAt_endpointH (ht.trans D.obs_le_horizon) z x).mul
      ((D.hasDerivAt_bridgeQ φ ht z x y).pow 2))
  convert hh using 1
  apply Finset.sum_congr rfl
  intro z _
  simp only [Nat.cast_ofNat,Pi.pow_apply]
  ring

lemma squareU_terminal (φ : (Fin n → α) → ℝ) (x y : Fin n → α) : D.squareU φ 2 x y = (φ y)^2 := by
  simp only [squareU,D.bridgeQ_terminal,← Finset.sum_mul,D.endpointH_mass D.obs_le_horizon,one_mul]

lemma squareU_bounds (φ : (Fin n → α) → ℝ) (hφ : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1)
    {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) : 0 ≤ D.squareU φ t x y ∧ D.squareU φ t x y ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun z _ => mul_nonneg (D.endpointH_pos ht z x).le (sq_nonneg _))
  · calc
      _ ≤ ∑ z, D.endpointH t z x*1 := Finset.sum_le_sum (fun z _ =>
        mul_le_mul_of_nonneg_left (by have hh := D.bridgeQ_bounds ht φ hφ z x y; nlinarith)
          (D.endpointH_pos ht z x).le)
      _ = 1 := by simp only [mul_one,D.endpointH_mass (ht.trans D.obs_le_horizon)]

lemma squareU_drift {ℓ θ t : ℝ} (ht : t ≤ 2) (B : Set (Fin n → α))
    (φ : (Fin n → α) → ℝ) (s : CoupledState α n) :
    D.squareUDeriv φ t s.v s.w+
      eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (fun r => D.squareU φ t r.v r.w) s =
      D.syncEnergy φ t s.v s.w+D.perturbSquare φ ℓ θ t s := by
  unfold squareUDeriv squareU syncEnergy perturbSquare
  rw [eventGenerator_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hh := D.endpoint_product_drift (ℓ := ℓ) (θ := θ) ht B z
    (fun x y => (D.bridgeQ φ t z x y)^2)
    (fun x y => -(2*D.bridgeQ φ t z x y*D.bridgeGen t z (D.bridgeQ φ t z) x y)) s
  have hs := D.bridgeGen_square t z (D.bridgeQ φ t z) s.v s.w
  unfold bridgePerturbation
  simp only [mul_neg] at hh
  linear_combination hh+D.endpointH t z s.v*hs

lemma syncEnergy_nonneg (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) :
    0 ≤ D.syncEnergy φ t x y := by
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (D.endpointH_pos ht z x).le
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (D.bridgeRate_pos ht z x i g).le (sq_nonneg _))

lemma continuousOn_syncEnergy (φ : (Fin n → α) → ℝ) (x y : Fin n → α) :
    ContinuousOn (fun t => D.syncEnergy φ t x y) (Set.Iic (2:ℝ)) := by
  apply continuousOn_finset_sum
  intro z _
  apply (D.continuousOn_endpointH z x).mul
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro g _
  exact (D.continuousOn_bridgeRate z x i g).mul
    (((D.continuousOn_bridgeQ φ z _ _).sub (D.continuousOn_bridgeQ φ z x y)).pow 2)

lemma continuousOn_perturbSquare (φ : (Fin n → α) → ℝ) (ℓ θ : ℝ) (s : CoupledState α n) :
    ContinuousOn (fun t => D.perturbSquare φ ℓ θ t s) (Set.Iic (2:ℝ)) := by
  apply continuousOn_finset_sum
  intro z _
  apply (D.continuousOn_endpointH z s.v).mul
  exact (D.continuousOn_endpointGen ℓ θ z (fun t x y => (D.bridgeQ φ t z x y)^2)
    (fun x y => (D.continuousOn_bridgeQ φ z x y).pow 2) s).sub
    (D.continuousOn_bridgeGen z (fun t x y => (D.bridgeQ φ t z x y)^2)
      (fun x y => (D.continuousOn_bridgeQ φ z x y).pow 2) s.v s.w)

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

/-- The exact quadratic identity used to bound the synchronous bridge energy. -/
theorem square_duhamel (a φ : (Fin n → α) → ℝ) :
    (∑ s, C.terminal s*(a s.start*(φ s.w)^2)) =
      (∑ x, D.density θ x*(a x*D.squareU φ θ x x))+
      C.integrate (fun t s => a s.start*(D.syncEnergy φ t s.v s.w+D.perturbSquare φ ℓ θ t s)) := by
  let F : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.squareU φ t s.v s.w
  let dF : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.squareUDeriv φ t s.v s.w
  have hd : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k+1))) t := by
    intro k hk t ht s
    exact ((D.hasDerivAt_squareU φ (C.grid.cell_subset hk ht).2 s.v s.w).const_mul _).hasDerivWithinAt
  have hH : C.CellContinuous (fun t s => a s.start*(D.syncEnergy φ t s.v s.w+D.perturbSquare φ ℓ θ t s)) := by
    intro k hk s
    exact (((D.continuousOn_syncEnergy φ s.v s.w).add (D.continuousOn_perturbSquare φ ℓ θ s)).const_mul _).mono
      (fun t ht => (C.grid.cell_subset hk ht).2)
  have hgen : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      dF t s+eventGenerator (couplingNext (D.cellBarrier C.grid k)) (D.couplingRate ℓ θ t) (F t) s =
        a s.start*(D.syncEnergy φ t s.v s.w+D.perturbSquare φ ℓ θ t s) := by
    intro k hk t ht s
    dsimp [dF,F]
    rw [D.coupling_generator_start_mul,← mul_add,D.squareU_drift (C.grid.cell_subset hk ht).2]
  have hh := C.dynkin_eq F dF _ hd hH hgen (fun _ _ _ => rfl)
  simpa only [F,D.squareU_terminal] using hh

end StoppedCoupling
end TailBound.RefreshData
