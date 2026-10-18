import TailBound.FlowBounds

/-! Pointwise perturbation bounds with the manuscript's dimension-free κ dependence. -/
open scoped BigOperators
namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

noncomputable def edgeEnergy (q : (Fin n → α) → (Fin n → α) → ℝ)
    (i : Fin n) (g : α) (x y : Fin n → α) : ℝ :=
  (dxy q i g x y)^2+(dx q i g x y)^2+(dx q i g x (Function.update y i g))^2

lemma vertical_energy_le (q : (Fin n → α) → (Fin n → α) → ℝ)
    (i : Fin n) (g : α) (x y : Fin n → α) :
    (dx q i g x y-dxy q i g x y)^2+(dy q i g x y)^2 ≤ 4*edgeEnergy q i g x y := by
  have h₁ := two_difference_square (dx q i g x y) (dxy q i g x y)
  have h₂ := two_difference_square (dxy q i g x y) (dx q i g x (Function.update y i g))
  have he : dy q i g x y = dxy q i g x y-dx q i g x (Function.update y i g) := by
    unfold dy dxy dx
    ring
  rw [he]
  unfold edgeEnergy
  nlinarith [sq_nonneg (dx q i g x y),sq_nonneg (dx q i g x (Function.update y i g))]

lemma vertical_square_energy_le (q : (Fin n → α) → (Fin n → α) → ℝ)
    (hq : ∀ x y, 0 ≤ q x y ∧ q x y ≤ 1)
    (i : Fin n) (g : α) (x y : Fin n → α) :
    (dx (fun u v => (q u v)^2) i g x y-dxy (fun u v => (q u v)^2) i g x y)^2+
      (dy (fun u v => (q u v)^2) i g x y)^2 ≤ 16*edgeEnergy q i g x y := by
  have h₁ := square_difference_lipschitz (hq (Function.update x i g) y)
    (hq (Function.update x i g) (Function.update y i g))
  have h₂ := square_difference_lipschitz (hq x (Function.update y i g)) (hq x y)
  have hv := vertical_energy_le q i g x y
  dsimp [dx,dxy,dy] at hv ⊢
  nlinarith

namespace RefreshData
variable (D : RefreshData α n)

noncomputable def totalEnergy (φ : (Fin n → α) → ℝ) (t : ℝ) (x y : Fin n → α) : ℝ :=
  ∑ z, D.endpointH t z x*(∑ i, ∑ g, D.bridgeRate t z x i g*edgeEnergy (D.bridgeQ φ t z) i g x y)

lemma totalEnergy_nonneg (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ 2) (x y : Fin n → α) :
    0 ≤ D.totalEnergy φ t x y := by
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (D.endpointH_pos ht z x).le
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro g _
  apply mul_nonneg (D.bridgeRate_pos ht z x i g).le
  unfold edgeEnergy
  positivity

lemma bridgePerturbation_young {ℓ θ t : ℝ} (ht : t ≤ 2) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (s : CoupledState α n) (u : ℝ) :
    2*u*D.bridgePerturbation ℓ θ t z q s ≤
      u^2*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)+
      ∑ i, ∑ g, D.bridgeRate t z s.v i g*
        ((dx q i g s.v s.w-dxy q i g s.v s.w)^2+(dy q i g s.v s.w)^2) := by
  rw [D.bridgePerturbation_expansion ht]
  unfold score mean
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro g _
  have hl := D.bridgeRate_ratio_bounds ht z s.v i g
  have hlpos : 0 < D.bridgeRate t z s.v i g/D.π g := div_pos (D.bridgeRate_pos ht z s.v i g) (D.πpos g)
  have hκpos : 0 < D.κ := lt_trans zero_lt_one D.κ_gt_one
  have hlower : 1 ≤ D.κ*(D.bridgeRate t z s.v i g/D.π g) := by
    have hh := mul_le_mul_of_nonneg_left hl.1 hκpos.le
    simpa only [mul_inv_cancel₀ hκpos.ne'] using hh
  have hd := D.coupledExponent_bounds ℓ θ s
  have hr := D.ratio_bounds ht i g s.v
  have hc := Talagrand.powerRatio_le D.κ_gt_one hd.1 (by linarith : D.coupledExponent ℓ θ s ≤ 1) hr.1 hr.2
  have hΛ : 0 ≤ D.Λ := div_nonneg (mul_nonneg hκpos.le D.logκ_pos.le) (sub_pos.mpr D.κ_gt_one).le
  have hh := split_coefficient_young hκpos hΛ hd.1 (by linarith)
    (D.ratio_pos (ht.trans D.obs_le_horizon) i g s.v) hlpos (D.πpos g) hlower hl.2 hc
    (dx q i g s.v s.w-dxy q i g s.v s.w) (dy q i g s.v s.w) u
  have he : D.π g*(D.bridgeRate t z s.v i g/D.π g) = D.bridgeRate t z s.v i g :=
    mul_div_cancel₀ _ (D.πpos g).ne'
  rw [he] at hh
  convert hh using 1 <;> ring

lemma perturbU_young {ℓ θ t : ℝ} (ht : t ≤ 2) (φ : (Fin n → α) → ℝ)
    (s : CoupledState α n) (u : ℝ) :
    2*u*D.perturbU φ ℓ θ t s ≤
      u^2*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)+4*D.totalEnergy φ t s.v s.w := by
  have hlocal (z : Fin n → α) := D.bridgePerturbation_young (ℓ := ℓ) (θ := θ) ht z (D.bridgeQ φ t z) s u
  calc
    _ ≤ ∑ z, D.endpointH t z s.v*(u^2*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)+
        4*(∑ i, ∑ g, D.bridgeRate t z s.v i g*edgeEnergy (D.bridgeQ φ t z) i g s.v s.w)) := by
      unfold perturbU
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z _
      have hh : (∑ i, ∑ g, D.bridgeRate t z s.v i g*
          ((dx (D.bridgeQ φ t z) i g s.v s.w-dxy (D.bridgeQ φ t z) i g s.v s.w)^2+
            (dy (D.bridgeQ φ t z) i g s.v s.w)^2)) ≤
          4*(∑ i, ∑ g, D.bridgeRate t z s.v i g*edgeEnergy (D.bridgeQ φ t z) i g s.v s.w) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro g _
        have hh := mul_le_mul_of_nonneg_left (vertical_energy_le (D.bridgeQ φ t z) i g s.v s.w)
          (D.bridgeRate_pos ht z s.v i g).le
        nlinarith
      have hh' := mul_le_mul_of_nonneg_left ((hlocal z).trans (add_le_add le_rfl hh))
        (D.endpointH_pos ht z s.v).le
      nlinarith
    _ = _ := by
      simp only [totalEnergy,mul_add,Finset.sum_add_distrib]
      rw [← Finset.sum_mul,D.endpointH_mass (ht.trans D.obs_le_horizon),one_mul,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring

lemma perturbSquare_young {ℓ θ t : ℝ} (ht : t ≤ 2) (φ : (Fin n → α) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (s : CoupledState α n) (u : ℝ) :
    2*u*D.perturbSquare φ ℓ θ t s ≤
      u^2*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)+16*D.totalEnergy φ t s.v s.w := by
  have hlocal (z : Fin n → α) := D.bridgePerturbation_young (ℓ := ℓ) (θ := θ) ht z (fun x y => (D.bridgeQ φ t z x y)^2) s u
  calc
    _ ≤ ∑ z, D.endpointH t z s.v*(u^2*(D.κ*(D.Λ*D.coupledExponent ℓ θ s)^2*D.score t s.v)+
        16*(∑ i, ∑ g, D.bridgeRate t z s.v i g*edgeEnergy (D.bridgeQ φ t z) i g s.v s.w)) := by
      unfold perturbSquare
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z _
      have hh : (∑ i, ∑ g, D.bridgeRate t z s.v i g*
          ((dx (fun x y => (D.bridgeQ φ t z x y)^2) i g s.v s.w-dxy (fun x y => (D.bridgeQ φ t z x y)^2) i g s.v s.w)^2+
            (dy (fun x y => (D.bridgeQ φ t z x y)^2) i g s.v s.w)^2)) ≤
          16*(∑ i, ∑ g, D.bridgeRate t z s.v i g*edgeEnergy (D.bridgeQ φ t z) i g s.v s.w) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro g _
        have hh := mul_le_mul_of_nonneg_left (vertical_square_energy_le (D.bridgeQ φ t z) (D.bridgeQ_bounds ht φ hφ z) i g s.v s.w)
          (D.bridgeRate_pos ht z s.v i g).le
        nlinarith
      have hh' := mul_le_mul_of_nonneg_left ((hlocal z).trans (add_le_add le_rfl hh))
        (D.endpointH_pos ht z s.v).le
      nlinarith
    _ = _ := by
      simp only [totalEnergy,mul_add,Finset.sum_add_distrib]
      rw [← Finset.sum_mul,D.endpointH_mass (ht.trans D.obs_le_horizon),one_mul,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring

lemma continuousOn_totalEnergy (φ : (Fin n → α) → ℝ) (x y : Fin n → α) :
    ContinuousOn (fun t => D.totalEnergy φ t x y) (Set.Iic (2:ℝ)) := by
  apply continuousOn_finset_sum
  intro z _
  apply (D.continuousOn_endpointH z x).mul
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro g _
  apply (D.continuousOn_bridgeRate z x i g).mul
  exact ((((D.continuousOn_bridgeQ φ z _ _).sub (D.continuousOn_bridgeQ φ z x y)).pow 2).add
    (((D.continuousOn_bridgeQ φ z _ _).sub (D.continuousOn_bridgeQ φ z x y)).pow 2)).add
    (((D.continuousOn_bridgeQ φ z _ _).sub (D.continuousOn_bridgeQ φ z _ _)).pow 2)

end RefreshData
end TailBound
