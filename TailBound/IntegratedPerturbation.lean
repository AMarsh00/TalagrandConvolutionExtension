import TailBound.IntegratedHorizontal

/-! Localized integrated bridge perturbation and energy absorption. -/
open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound.RefreshData.StoppedCoupling

set_option linter.unusedSectionVars false
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def localScore (a : (Fin n → α) → ℝ) : ℝ :=
  C.integrate (fun t s => a s.start*(D.coupledExponent ℓ θ s)^2*D.score t s.v)

lemma localScore_nonneg (hθ : θ ≤ 2) (a : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) :
    0 ≤ C.localScore a := by
  apply C.integrate_nonneg hθ
  intro k hk t ht s _
  apply mul_nonneg (mul_nonneg (ha s.start) (sq_nonneg _))
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (D.πnonneg g) (sq_nonneg _))

lemma localScore_continuous (a : (Fin n → α) → ℝ) :
    C.CellContinuous (fun t s => a s.start*(D.coupledExponent ℓ θ s)^2*D.score t s.v) := by
  intro k hk s
  apply ContinuousOn.const_mul
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro g _
  exact (((D.continuousOn_ratio i g s.v).sub continuousOn_const).pow 2).const_mul (D.π g) |>.mono
    (fun t ht => ((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon)

lemma integrate_score_coefficient (a : (Fin n → α) → ℝ) :
    C.integrate (fun t s => a s.start*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)) =
      D.κ*D.Λ^2*C.localScore a := by
  unfold localScore
  rw [← C.integrate_smul]
  congr 1
  funext t s
  ring

lemma integrated_perturbU_young (hθ : θ ≤ 2) (a φ : (Fin n → α) → ℝ)
    (ha : ∀ x, 0 ≤ a x) (u : ℝ) :
    2*u*C.integrate (fun t s => a s.start*D.perturbU φ ℓ θ t s) ≤
      u^2*(D.κ*D.Λ^2*C.localScore a)+4*C.integrate (fun t s => a s.start*D.totalEnergy φ t s.v s.w) := by
  let F : ℝ → CoupledState α n → ℝ := fun t s => a s.start*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)
  let G : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.totalEnergy φ t s.v s.w
  let H : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.perturbU φ ℓ θ t s
  have hF : C.CellContinuous F := by
    intro k hk s
    have hh := (C.localScore_continuous a k hk s).const_mul (D.κ*D.Λ^2)
    exact hh.congr (fun t _ => by dsimp [F]; ring)
  have hG : C.CellContinuous G := by
    intro k hk s
    exact ((D.continuousOn_totalEnergy φ s.v s.w).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hH : C.CellContinuous H := by
    intro k hk s
    exact ((D.continuousOn_perturbU φ ℓ θ s).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hh := C.integrate_mono hθ (F := fun t s => (2*u)*H t s)
    (G := fun t s => u^2*F t s+4*G t s)
    (fun k hk s => (hH k hk s).const_mul _) (fun k hk s => ((hF k hk s).const_mul _).add ((hG k hk s).const_mul _)) (by
      intro k hk t ht s _
      have hh := mul_le_mul_of_nonneg_left (D.perturbU_young (ℓ := ℓ) (θ := θ) (C.grid.cell_subset hk ht).2 φ s u) (ha s.start)
      dsimp [F,G,H]
      nlinarith)
  rw [C.integrate_add (fun k hk s => (hF k hk s).const_mul _) (fun k hk s => (hG k hk s).const_mul _),
    C.integrate_smul,C.integrate_smul,C.integrate_smul] at hh
  dsimp [F,G,H] at hh
  rw [C.integrate_score_coefficient] at hh
  exact hh

lemma integrated_perturbSquare_young (hθ : θ ≤ 2) (a φ : (Fin n → α) → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (u : ℝ) :
    2*u*C.integrate (fun t s => a s.start*D.perturbSquare φ ℓ θ t s) ≤
      u^2*(D.κ*D.Λ^2*C.localScore a)+16*C.integrate (fun t s => a s.start*D.totalEnergy φ t s.v s.w) := by
  let F : ℝ → CoupledState α n → ℝ := fun t s => a s.start*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)
  let G : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.totalEnergy φ t s.v s.w
  let H : ℝ → CoupledState α n → ℝ := fun t s => a s.start*D.perturbSquare φ ℓ θ t s
  have hF : C.CellContinuous F := by
    intro k hk s
    have hh := (C.localScore_continuous a k hk s).const_mul (D.κ*D.Λ^2)
    exact hh.congr (fun t _ => by dsimp [F]; ring)
  have hG : C.CellContinuous G := by
    intro k hk s
    exact ((D.continuousOn_totalEnergy φ s.v s.w).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hH : C.CellContinuous H := by
    intro k hk s
    exact ((D.continuousOn_perturbSquare φ ℓ θ s).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hh := C.integrate_mono hθ (F := fun t s => (2*u)*H t s)
    (G := fun t s => u^2*F t s+16*G t s)
    (fun k hk s => (hH k hk s).const_mul _) (fun k hk s => ((hF k hk s).const_mul _).add ((hG k hk s).const_mul _)) (by
      intro k hk t ht s _
      have hh := mul_le_mul_of_nonneg_left (D.perturbSquare_young (ℓ := ℓ) (θ := θ) (C.grid.cell_subset hk ht).2 φ hφ s u) (ha s.start)
      dsimp [F,G,H]
      nlinarith)
  rw [C.integrate_add (fun k hk s => (hF k hk s).const_mul _) (fun k hk s => (hG k hk s).const_mul _),
    C.integrate_smul,C.integrate_smul,C.integrate_smul] at hh
  dsimp [F,G,H] at hh
  rw [C.integrate_score_coefficient] at hh
  exact hh

lemma integrated_energy_bound (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2)
    (a φ : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    C.integrate (fun t s => a s.start*D.totalEnergy φ t s.v s.w) ≤
      2*(1+D.horizontalConstant*D.κ)*(∑ x, D.density θ x*a x)+16*(D.κ*D.Λ^2*C.localScore a) := by
  have hs := C.square_duhamel a φ
  have hi : 0 ≤ ∑ x, D.density θ x*(a x*D.squareU φ θ x x) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (D.density_nonneg (hθ2.trans D.obs_le_horizon) x)
      (mul_nonneg (ha x) (D.squareU_bounds φ hφ hθ2 x x).1))
  have he : (∑ s, C.terminal s*(a s.start*(φ s.w)^2)) ≤ ∑ x, D.density θ x*a x := by
    rw [← C.start_pairing a]
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (C.terminal_nonneg hθ2 s)
    have hp : (φ s.w)^2 ≤ 1 := by have hp := hφ s.w; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hp (ha s.start)]
  have hcS : C.CellContinuous (fun t s => a s.start*D.syncEnergy φ t s.v s.w) := by
    intro k hk s
    exact ((D.continuousOn_syncEnergy φ s.v s.w).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hcJ : C.CellContinuous (fun t s => a s.start*D.perturbSquare φ ℓ θ t s) := by
    intro k hk s
    exact ((D.continuousOn_perturbSquare φ ℓ θ s).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hcH : C.CellContinuous (fun t s => a s.start*D.horizontalEnergy φ t s.v s.w) := by
    intro k hk s
    exact ((D.continuousOn_horizontalEnergy φ s.v s.w).const_mul _).mono (fun t ht => (C.grid.cell_subset hk ht).2)
  have hsum : C.integrate (fun t s => a s.start*(D.syncEnergy φ t s.v s.w+D.perturbSquare φ ℓ θ t s)) =
      C.integrate (fun t s => a s.start*D.syncEnergy φ t s.v s.w)+
      C.integrate (fun t s => a s.start*D.perturbSquare φ ℓ θ t s) := by
    simp only [mul_add]
    exact C.integrate_add hcS hcJ
  rw [hsum] at hs
  have hsplit : C.integrate (fun t s => a s.start*D.totalEnergy φ t s.v s.w) =
      C.integrate (fun t s => a s.start*D.syncEnergy φ t s.v s.w)+
      C.integrate (fun t s => a s.start*D.horizontalEnergy φ t s.v s.w) := by
    simp only [D.totalEnergy_split,mul_add]
    exact C.integrate_add hcS hcH
  have hh := C.integrated_horizontal_bound hθ hθ2 a φ ha hφ
  have hy := C.integrated_perturbSquare_young hθ2 a φ ha hφ (-16)
  nlinarith

/-- Localized terminal test-function difference, before taking square roots. -/
theorem localized_difference_sq (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2)
    (a φ : (Fin n → α) → ℝ) (ha : ∀ x, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ((∑ s, C.terminal s*(a s.start*φ s.w))-(∑ s, C.terminal s*(a s.start*φ s.v)))^2 ≤
      8*(1+D.horizontalConstant*D.κ)*D.κ*D.Λ^2*C.localScore a*(∑ x, D.density θ x*a x)+
        64*(D.κ*D.Λ^2*C.localScore a)^2 := by
  rw [C.duhamel]
  have hk : 0 ≤ D.κ*D.Λ^2*C.localScore a := mul_nonneg
    (mul_nonneg (lt_trans zero_lt_one D.κ_gt_one).le (sq_nonneg _)) (C.localScore_nonneg hθ2 a ha)
  have hd := quadratic_discriminant hk (C.integrated_perturbU_young hθ2 a φ ha)
  have he := C.integrated_energy_bound hθ hθ2 a φ ha hφ
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*(D.κ*D.Λ^2*C.localScore a))
  nlinarith

lemma localScore_eq_scoreWork (a : (Fin n → α) → ℝ) :
    C.localScore a = C.scoreWork (fun x => a x*(D.exponent ℓ θ x)^2) := by
  unfold localScore integrate scoreWork
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  funext t
  unfold pairing
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  cases hs : s.alive <;> simp [coupledExponent,hs]

end TailBound.RefreshData.StoppedCoupling
