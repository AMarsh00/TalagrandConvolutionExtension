import TailBound.ProductEvolution

/-!
# Endpoint Bridge

Endpoint likelihood and the Doob-transform cancellation for the bridge.
-/

open scoped BigOperators

namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}


namespace RefreshData

variable (D : RefreshData α n)

omit [DecidableEq α] [Nonempty α] in
lemma bridgeTime_retention (t : ℝ) :
    bridgeTime t * D.retention = Real.exp (-(D.horizon - t)) := by
  unfold bridgeTime retention horizon
  rw [← Real.exp_add]
  congr 1
  ring

omit [Fintype α] [Nonempty α] in
lemma heatKernel_bridgeH (π : α → ℝ) (a : ℝ) (x z : α) :
    heatKernel π a x z = bridgeH π a z x := by unfold heatKernel bridgeH; ring

noncomputable def endpointNum (z : Fin n → α) (t : ℝ) (x : Fin n → α) : ℝ :=
  D.f z * tensorKernel (heatKernel D.π (Real.exp (-(D.horizon - t)))) n x z

noncomputable def endpointH (t : ℝ) (z x : Fin n → α) : ℝ := D.endpointNum z t x / D.p t x

omit [Nonempty α] in
lemma endpointNum_heat (z : Fin n → α) (t : ℝ) :
    D.endpointNum z t = heat D.π (fun y => if y=z then D.f z else 0) (D.horizon - t) := by
  funext x
  simp [endpointNum, heat, act, mul_comm]

omit [Nonempty α] in
lemma endpointNum_product (z : Fin n → α) (t : ℝ) (x : Fin n → α) :
    D.endpointNum z t x = D.f z*∏ i, bridgeH D.π (bridgeTime t * D.retention) (z i) (x i) := by
  simp only [endpointNum, ← D.bridgeTime_retention, tensorKernel, heatKernel_bridgeH]

omit [Nonempty α] in
lemma endpointH_pos {t : ℝ} (ht : t ≤ 2) (z x : Fin n → α) : 0 < D.endpointH t z x := by
  unfold endpointH
  rw [D.endpointNum_product]
  exact div_pos (mul_pos (D.fpos z) (Finset.prod_pos fun i _ => D.bridge_den_pos ht _ _))
    (D.p_pos (ht.trans D.obs_le_horizon) x)

omit [Nonempty α] in
lemma endpointH_mass {t : ℝ} (ht : t ≤ D.horizon) (x : Fin n → α) : ∑ z, D.endpointH t z x = 1 := by
  unfold endpointH
  rw [← Finset.sum_div]
  have he : (∑ z, D.endpointNum z t x) = D.p t x := by
    simp only [endpointNum, p, heat, act, mul_comm]
  rw [he, div_self (D.p_pos ht x).ne']

omit [Nonempty α] in
lemma hasDerivAt_endpointNum (z : Fin n → α) (t : ℝ) (x : Fin n → α) :
    HasDerivAt (fun u => D.endpointNum z u x) (-refreshGenerator D.π (D.endpointNum z t) x) t := by
  simp_rw [D.endpointNum_heat]
  simpa using (hasDerivAt_heat D.π D.mass (fun y => if y=z then D.f z else 0) x (D.horizon - t)).comp t
    ((hasDerivAt_id t).const_sub D.horizon)

omit [Nonempty α] in
lemma hasDerivAt_endpointH {t : ℝ} (ht : t ≤ D.horizon) (z x : Fin n → α) :
    HasDerivAt (fun u => D.endpointH u z x) (-D.revGen t (D.endpointH t z) x) t := by
  have hd := (D.hasDerivAt_endpointNum z t x).div (D.hasDerivAt_p t x) (D.p_pos ht x).ne'
  convert hd using 1
  change - D.revGen t (fun y => D.endpointNum z t y / D.p t y) x = _
  rw [D.revGen_quotient ht]
  field_simp [(D.p_pos ht x).ne']
  ring

omit [Nonempty α] in
lemma endpointNum_update (t : ℝ) (z x : Fin n → α) (i : Fin n) (g : α)
    (hd : bridgeH D.π (bridgeTime t * D.retention) (z i) (x i) ≠ 0) :
    D.endpointNum z t (Function.update x i g) =
      D.endpointNum z t x *
        (bridgeH D.π (bridgeTime t * D.retention) (z i) g /
          bridgeH D.π (bridgeTime t * D.retention) (z i) (x i)) := by
  unfold endpointNum
  rw [tensorKernel_update, tensorKernel_row _ n x z i]
  simp only [← D.bridgeTime_retention, heatKernel_bridgeH]
  field_simp [hd]

omit [Nonempty α] in
/-- The density `p` cancels from the endpoint-conditioned reverse jump rate. -/
lemma endpoint_rate_cancellation {t : ℝ} (ht : t ≤ 2) (z x : Fin n → α) (i : Fin n) (g : α) :
    D.π g * D.ratio t i g x * (D.endpointH t z (Function.update x i g) / D.endpointH t z x) =
      D.bridgeRate t z x i g := by
  have hp := D.p_pos (ht.trans D.obs_le_horizon) x
  have hpu := D.p_pos (ht.trans D.obs_le_horizon) (Function.update x i g)
  have hn : D.endpointNum z t x ≠ 0 := by
    rw [D.endpointNum_product]
    exact (mul_pos (D.fpos z) (Finset.prod_pos fun j _ => D.bridge_den_pos ht _ _)).ne'
  unfold endpointH ratio bridgeRate
  rw [D.endpointNum_update t z x i g (D.bridge_den_pos ht _ _).ne']
  field_simp [hp.ne', hpu.ne', hn, (D.bridge_den_pos ht _ _).ne']

lemma bridgeRate_ratio_bounds {t : ℝ} (ht : t ≤ 2) (z x : Fin n → α) (i : Fin n) (g : α) :
    D.κ⁻¹ ≤ D.bridgeRate t z x i g / D.π g ∧ D.bridgeRate t z x i g / D.π g ≤ D.κ := by
  let r := bridgeTime t * D.retention
  have hr0 : 0 ≤ r := mul_nonneg (bridgeTime_pos t).le D.retention_pos.le
  have hrA : r ≤ D.retention := by
    exact mul_le_of_le_one_left D.retention_pos.le (bridgeTime_le_one ht)
  have he (u : α) : bridgeH D.π r (z i) u = refresh D.π (1 - r) u (z i) := by
    unfold bridgeH refresh
    ring
  have hu := refresh_coordinate_bound D.π D.m D.M D.retention r D.mpos D.lower D.upper
    hr0 hrA D.retention_lt_one (x i) g (z i)
  have hl := refresh_coordinate_bound D.π D.m D.M D.retention r D.mpos D.lower D.upper
    hr0 hrA D.retention_lt_one g (x i) (z i)
  have hden := D.bridge_den_pos ht (z i) (x i)
  have heq : D.bridgeRate t z x i g / D.π g = bridgeH D.π r (z i) g / bridgeH D.π r (z i) (x i) := by
    unfold bridgeRate
    dsimp [r]
    field_simp [(D.πpos g).ne', hden.ne']
  rw [heq]
  rw [← he g, ← he (x i)] at hu hl
  change bridgeH D.π r (z i) g ≤ D.κ * bridgeH D.π r (z i) (x i) at hu
  change bridgeH D.π r (z i) (x i) ≤ D.κ * bridgeH D.π r (z i) g at hl
  constructor
  · apply (le_div_iff₀ hden).mpr
    apply (inv_mul_le_iff₀ (zero_lt_one.trans D.κ_gt_one)).mpr
    simpa only [mul_comm] using hl
  · exact (div_le_iff₀ hden).mpr hu

end RefreshData
end TailBound
