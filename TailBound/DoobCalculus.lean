import TailBound.EndpointBridge

/-! Finite Doob-transform product identities. -/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

lemma eventGenerator_doob {S E : Type*} [Fintype E]
    (next : E → S → S) (rate : E → S → ℝ) (H Q : S → ℝ) (s : S) (hs : H s ≠ 0) :
    eventGenerator next rate (fun r => H r*Q r) s-Q s*eventGenerator next rate H s =
      H s*eventGenerator next (fun e r => rate e r*H (next e r)/H r) Q s := by
  unfold eventGenerator
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  field_simp [hs]
  ring

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

lemma couplingNext_v (B : Set (Fin n → α)) (e : CouplingEvent α n) (s : CoupledState α n) :
    (couplingNext B e s).v = (couplingNext ∅ e s).v := rfl

lemma couplingNext_w (B : Set (Fin n → α)) (e : CouplingEvent α n) (s : CoupledState α n) :
    (couplingNext B e s).w = (couplingNext ∅ e s).w := rfl

namespace RefreshData
variable (D : RefreshData α n)

noncomputable def endpointRate (ℓ θ t : ℝ) (z : Fin n → α)
    (e : CouplingEvent α n) (s : CoupledState α n) : ℝ :=
  D.couplingRate ℓ θ t e s*D.endpointH t z (couplingNext ∅ e s).v/D.endpointH t z s.v

noncomputable def endpointGen (ℓ θ t : ℝ) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (s : CoupledState α n) : ℝ :=
  eventGenerator (couplingNext ∅) (D.endpointRate ℓ θ t z) (fun r => q r.v r.w) s

noncomputable def bridgePerturbation (ℓ θ t : ℝ) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (s : CoupledState α n) : ℝ :=
  D.endpointGen ℓ θ t z q s-D.bridgeGen t z q s.v s.w

lemma endpoint_product_drift {ℓ θ t : ℝ} (ht : t ≤ 2) (B : Set (Fin n → α))
    (z : Fin n → α) (q dq : (Fin n → α) → (Fin n → α) → ℝ) (s : CoupledState α n) :
    (-D.revGen t (D.endpointH t z) s.v)*q s.v s.w+D.endpointH t z s.v*dq s.v s.w+
      eventGenerator (couplingNext B) (D.couplingRate ℓ θ t)
        (fun r => D.endpointH t z r.v*q r.v r.w) s =
      D.endpointH t z s.v*(dq s.v s.w+D.endpointGen ℓ θ t z q s) := by
  have hh := eventGenerator_doob (couplingNext B) (D.couplingRate ℓ θ t)
    (fun r => D.endpointH t z r.v) (fun r => q r.v r.w) s (D.endpointH_pos ht z s.v).ne'
  rw [D.coupling_generator_v] at hh
  have he : eventGenerator (couplingNext B)
      (fun e r => D.couplingRate ℓ θ t e r*D.endpointH t z (couplingNext B e r).v/D.endpointH t z r.v)
      (fun r => q r.v r.w) s = D.endpointGen ℓ θ t z q s := rfl
  rw [he] at hh
  linarith

lemma endpointGen_expansion {ℓ θ t : ℝ} (ht : t ≤ 2) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (s : CoupledState α n) :
    D.endpointGen ℓ θ t z q s = ∑ i, ∑ g,
      (D.bridgeRate t z s.v i g / D.ratio t i g s.v *
        min (D.ratio t i g s.v) (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)) *
          (dxy q i g s.v s.w) +
      D.bridgeRate t z s.v i g / D.ratio t i g s.v *
        max (D.ratio t i g s.v-switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)) 0 *
          (dx q i g s.v s.w) +
      D.π g * max (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)-D.ratio t i g s.v) 0 *
          (dy q i g s.v s.w)) := by
  unfold endpointGen eventGenerator
  rw [Fintype.sum_prod_type_right,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  rw [sum_jumpKind]
  have hc := D.endpoint_rate_cancellation ht z s.v i g
  have he : D.π g * D.endpointH t z (Function.update s.v i g)/D.endpointH t z s.v =
      D.bridgeRate t z s.v i g/D.ratio t i g s.v := by
    apply (eq_div_iff (D.ratio_pos (ht.trans D.obs_le_horizon) i g s.v).ne').mpr
    convert hc using 1 <;> ring
  unfold endpointRate couplingRate
  simp only [couplingNext,dxy,dx,dy]
  have hs := (D.endpointH_pos ht z s.v).ne'
  field_simp [hs] at he ⊢
  linear_combination
    (min (D.ratio t i g s.v) (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)) *
      (q (Function.update s.v i g) (Function.update s.w i g)-q s.v s.w)+
    max (D.ratio t i g s.v-switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)) 0 *
      (q (Function.update s.v i g) s.w-q s.v s.w))*he

lemma bridgePerturbation_expansion {ℓ θ t : ℝ} (ht : t ≤ 2) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (s : CoupledState α n) :
    D.bridgePerturbation ℓ θ t z q s = ∑ i, ∑ g,
      (D.bridgeRate t z s.v i g/D.ratio t i g s.v *
        max (D.ratio t i g s.v-switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)) 0 *
        (dx q i g s.v s.w-dxy q i g s.v s.w) +
      D.π g * max (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v)-D.ratio t i g s.v) 0 *
        dy q i g s.v s.w) := by
  rw [bridgePerturbation,D.endpointGen_expansion ht]
  unfold bridgeGen
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have hr := (D.ratio_pos (ht.trans D.obs_le_horizon) i g s.v).ne'
  have hh := min_add_positive_difference (D.ratio t i g s.v)
    (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i g s.v))
  unfold dxy
  field_simp [hr]
  linear_combination D.bridgeRate t z s.v i g*
    (q (Function.update s.v i g) (Function.update s.w i g)-q s.v s.w)*hh

end RefreshData
end TailBound
