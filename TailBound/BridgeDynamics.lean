import TailBound.WeightedComparison
import TailBound.BridgeHorizontal

/-! Backward equations for the explicit synchronous bridge. -/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma bridgeLaw_generator (π : α → ℝ) (hπ : ∑ g, π g = 1) (a r : ℝ)
    (z x y u : α) (hden : ∀ g, bridgeH π (r*a) z g ≠ 0) :
    (∑ g, π g * (bridgeH π (r*a) z g/bridgeH π (r*a) z x) *
      (bridgeLaw π a r z g g u-bridgeLaw π a r z x y u)) =
    (π u*bridgeH π a z u-π z*bridgeLaw π a r z x y u)/bridgeH π (r*a) z x := by
  have he (g : α) : π g * (bridgeH π (r*a) z g/bridgeH π (r*a) z x) *
      (bridgeLaw π a r z g g u-bridgeLaw π a r z x y u) =
      (π g*(r*bridgeH π a z g*(if u=g then 1 else 0)+(1-r)*π u*bridgeH π a z u)-
        π g*bridgeH π (r*a) z g*bridgeLaw π a r z x y u)/bridgeH π (r*a) z x := by
    unfold bridgeLaw
    field_simp [hden g,hden x]
  simp_rw [he]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  have hn : (∑ g, π g*(r*bridgeH π a z g*(if u=g then 1 else 0)+(1-r)*π u*bridgeH π a z u)) =
      π u*bridgeH π a z u := by
    simp only [mul_add,Finset.sum_add_distrib]
    have h1 : (∑ g, π g*(r*bridgeH π a z g*(if u=g then 1 else 0))) = π u*r*bridgeH π a z u := by
      simp [mul_ite]
      ring
    rw [h1,← Finset.sum_mul,hπ]
    ring
  rw [hn,← Finset.sum_mul,bridgeH_mean π hπ]

noncomputable def bridgeTime (t : ℝ) : ℝ := Real.exp (t-2)

lemma bridgeTime_pos (t : ℝ) : 0 < bridgeTime t := Real.exp_pos _
lemma bridgeTime_le_one {t : ℝ} (ht : t ≤ 2) : bridgeTime t ≤ 1 :=
  Real.exp_le_one_iff.mpr (sub_nonpos.mpr ht)
lemma bridgeTime_lt_one {t : ℝ} (ht : t < 2) : bridgeTime t < 1 :=
  Real.exp_lt_one_iff.mpr (sub_neg.mpr ht)
lemma bridgeTime_two : bridgeTime 2 = 1 := by simp [bridgeTime]
lemma hasDerivAt_bridgeTime (t : ℝ) : HasDerivAt bridgeTime (bridgeTime t) t := by
  simpa [bridgeTime] using ((hasDerivAt_id t).sub_const 2).exp

lemma hasDerivAt_bridgeLaw (π : α → ℝ) (a t : ℝ) (z x y u : α)
    (hd : bridgeH π (bridgeTime t*a) z x ≠ 0) :
    HasDerivAt (fun s => bridgeLaw π a (bridgeTime s) z x y u)
      ((π z*bridgeLaw π a (bridgeTime t) z x y u-π u*bridgeH π a z u)/
        bridgeH π (bridgeTime t*a) z x) t := by
  have hr := hasDerivAt_bridgeTime t
  have hden : HasDerivAt (fun s => bridgeH π (bridgeTime s*a) z x)
      (bridgeTime t*(bridgeH π a z x-π z)) t := by
    have he : (fun s => bridgeH π (bridgeTime s*a) z x) =
        fun s => bridgeTime s*bridgeH π a z x+(1-bridgeTime s)*π z := by
      funext s
      exact bridgeH_interpolation π a (bridgeTime s) z x
    rw [he]
    convert (hr.mul_const (bridgeH π a z x)).add ((hr.const_sub 1).mul_const (π z)) using 1 <;> ring
  have hn := ((hr.mul_const (bridgeH π a z x)).mul_const (if u=y then (1:ℝ) else 0)).add
    (((hr.const_sub 1).mul_const (π u)).mul_const (bridgeH π a z u))
  convert hn.div hden hd using 1
  simp only [Pi.add_apply]
  unfold bridgeLaw
  field_simp [hd]
  rw [bridgeH_interpolation]
  ring

variable [Nonempty α] {n : ℕ}
namespace RefreshData
variable (D : RefreshData α n)

noncomputable def bridgeRate (t : ℝ) (z x : Fin n → α) (i : Fin n) (g : α) : ℝ :=
  D.π g*bridgeH D.π (bridgeTime t*D.retention) (z i) g /
    bridgeH D.π (bridgeTime t*D.retention) (z i) (x i)

noncomputable def bridgeQ (φ : (Fin n → α) → ℝ) (t : ℝ) (z x y : Fin n → α) : ℝ :=
  bridgePayoff D.π D.retention (bridgeTime t) z φ x y

lemma bridge_den_pos {t : ℝ} (ht : t ≤ 2) (z x : α) :
    0 < bridgeH D.π (bridgeTime t*D.retention) z x := by
  apply bridgeH_pos D.π D.πpos (mul_nonneg (bridgeTime_pos t).le D.retention_pos.le)
  nlinarith [bridgeTime_le_one ht,D.retention_pos,D.retention_lt_one]

lemma bridgeRate_pos {t : ℝ} (ht : t ≤ 2) (z x : Fin n → α) (i : Fin n) (g : α) :
    0 < D.bridgeRate t z x i g :=
  div_pos (mul_pos (D.πpos g) (D.bridge_den_pos ht (z i) g)) (D.bridge_den_pos ht (z i) (x i))

lemma bridgeQ_bounds {t : ℝ} (ht : t ≤ 2) (φ : (Fin n → α) → ℝ)
    (hφ : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1) (z x y : Fin n → α) :
    0 ≤ D.bridgeQ φ t z x y ∧ D.bridgeQ φ t z x y ≤ 1 := by
  have hμ (i : Fin n) (u : α) : 0 ≤ bridgeMarginals D.π D.retention (bridgeTime t) z x y i u :=
    bridgeLaw_nonneg D.π D.πnonneg _ _ ⟨D.retention_pos.le,D.retention_lt_one.le⟩
      ⟨(bridgeTime_pos t).le,bridgeTime_le_one ht⟩ _ _ _ _
  have hm (i : Fin n) : ∑ u, bridgeMarginals D.π D.retention (bridgeTime t) z x y i u = 1 :=
    bridgeLaw_mass D.π D.mass _ _ _ _ _ (D.bridge_den_pos ht _ _).ne'
  have hprod (u : Fin n → α) : 0 ≤ productWeight (bridgeMarginals D.π D.retention (bridgeTime t) z x y) u :=
    Finset.prod_nonneg (fun i _ => hμ i (u i))
  constructor
  · exact mean_nonneg hprod (fun u => (hφ u).1)
  · calc
      _ ≤ mean (productWeight (bridgeMarginals D.π D.retention (bridgeTime t) z x y)) (fun _ => 1) :=
        mean_mono hprod (fun u => (hφ u).2)
      _ = 1 := by rw [mean_const _ (productWeight_mass _ hm)]

lemma bridgeQ_terminal (φ : (Fin n → α) → ℝ) (z x y : Fin n → α) :
    D.bridgeQ φ 2 z x y = φ y := by
  have he (i : Fin n) (u : α) : bridgeMarginals D.π D.retention (bridgeTime 2) z x y i u =
      if u=y i then 1 else 0 := by
    rw [bridgeTime_two]
    unfold bridgeMarginals bridgeLaw
    simp only [one_mul,sub_self,zero_mul,add_zero]
    split_ifs <;> simp [(bridgeH_pos D.π D.πpos D.retention_pos.le D.retention_lt_one (z i) (x i)).ne']
  have hp (u : Fin n → α) : productWeight (bridgeMarginals D.π D.retention (bridgeTime 2) z x y) u =
      if u=y then 1 else 0 := by
    unfold productWeight
    simp_rw [he]
    by_cases hu : u=y
    · simp [hu]
    · rw [if_neg hu]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp only [bridgeQ,bridgePayoff,mean,hp]
  simp

end RefreshData
end TailBound
