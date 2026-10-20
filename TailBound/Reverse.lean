import TailBound.JumpFlow
import TailBound.Generators
import TalagrandConvConjecture.PowerCoupling

/-! Reverse heat data and the entropy-production drift.
All fields of `RefreshData` describe the input probability law and density;
none assumes an analytic estimate or a conclusion of the manuscript.
-/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

variable (α : Type*) [Fintype α] [DecidableEq α]

structure RefreshData (n : ℕ) where
  π : α → ℝ
  mass : ∑ a, π a = 1
  m : ℝ
  M : ℝ
  mpos : 0 < m
  lower : ∀ a, m ≤ π a
  upper : ∀ a, π a ≤ M
  τ : ℝ
  τpos : 0 < τ
  f : (Fin n → α) → ℝ
  fpos : ∀ x, 0 < f x
  fmass : mean (tensorWeight π n) f = 1

namespace RefreshData
variable {α} [Nonempty α] {n : ℕ} (D : RefreshData α n)

noncomputable def horizon : ℝ := D.τ+2
noncomputable def retention : ℝ := Real.exp (-D.τ)
noncomputable def κ : ℝ := (D.retention+(1-D.retention)*D.M) / ((1-D.retention)*D.m)
noncomputable def Λ : ℝ := D.κ * Real.log D.κ / (D.κ-1)
noncomputable def p (t : ℝ) : (Fin n → α) → ℝ := heat D.π D.f (D.horizon-t)
noncomputable def logP (t : ℝ) (x : Fin n → α) : ℝ := Real.log (D.p t x)
noncomputable def ratio (t : ℝ) (i : Fin n) (a : α) (x : Fin n → α) : ℝ :=
  D.p t (Function.update x i a) / D.p t x
noncomputable def revGen (t : ℝ) (F : (Fin n → α) → ℝ) (x : Fin n → α) : ℝ :=
  ∑ i, mean D.π (fun a => D.ratio t i a x * (F (Function.update x i a)-F x))
noncomputable def score (t : ℝ) (x : Fin n → α) : ℝ :=
  ∑ i, mean D.π (fun a => (D.ratio t i a x-1)^2)
noncomputable def density (t : ℝ) (x : Fin n → α) : ℝ := tensorWeight D.π n x * D.p t x
noncomputable def gap (ℓ θ : ℝ) (x : Fin n → α) : ℝ := max (ℓ-D.logP θ x) 0
noncomputable def exponent (ℓ θ : ℝ) (x : Fin n → α) : ℝ :=
  if 10 ≤ D.gap ℓ θ x then 5/(D.gap ℓ θ x+1) else 0

lemma πpos (a : α) : 0 < D.π a := D.mpos.trans_le (D.lower a)
lemma πnonneg (a : α) : 0 ≤ D.π a := (D.πpos a).le
lemma retention_pos : 0 < D.retention := Real.exp_pos _
lemma retention_lt_one : D.retention < 1 := Real.exp_lt_one_iff.mpr (by linarith [D.τpos])
lemma m_le_M : D.m ≤ D.M := (D.lower (Classical.choice inferInstance)).trans (D.upper _)

lemma κ_gt_one : 1 < D.κ := by
  have hden : 0 < (1-D.retention)*D.m := mul_pos (sub_pos.mpr D.retention_lt_one) D.mpos
  rw [κ, lt_div_iff₀ hden]
  have h := mul_nonneg (sub_nonneg.mpr D.retention_lt_one.le) (sub_nonneg.mpr D.m_le_M)
  nlinarith [D.retention_pos]

lemma p_pos {t : ℝ} (ht : t ≤ D.horizon) (x : Fin n → α) : 0 < D.p t x :=
  heat_pos D.π D.πnonneg D.mass D.f D.fpos (sub_nonneg.mpr ht) x

lemma p_mass (t : ℝ) : mean (tensorWeight D.π n) (D.p t) = 1 := by
  rw [p, mean_heat D.π D.mass, D.fmass]

lemma density_mass (t : ℝ) : ∑ x, D.density t x = 1 := D.p_mass t

lemma density_nonneg {t : ℝ} (ht : t ≤ D.horizon) (x : Fin n → α) :
    0 ≤ D.density t x := mul_nonneg (tensorWeight_nonneg D.πnonneg n x) (D.p_pos ht x).le

lemma obs_le_horizon : (2:ℝ) ≤ D.horizon := by dsimp [horizon]; linarith [D.τpos]

lemma ratio_pos {t : ℝ} (ht : t ≤ D.horizon) (i : Fin n) (a : α) (x : Fin n → α) :
    0 < D.ratio t i a x := div_pos (D.p_pos ht _) (D.p_pos ht _)

lemma ratio_bounds {t : ℝ} (ht : t ≤ 2) (i : Fin n) (a : α) (x : Fin n → α) :
    D.κ⁻¹ ≤ D.ratio t i a x ∧ D.ratio t i a x ≤ D.κ := by
  have hh := heat_replacement_ratio_time D.π D.m D.M D.τ D.horizon t D.mpos
    D.lower D.upper D.τpos (by dsimp [horizon]; linarith) n D.f
    (fun x => (D.fpos x).le)
    ⟨fun _ => Classical.choice inferInstance, D.fpos _⟩ x i a
  simpa only [κ, retention, ratio, p, heat, heatKernel_eq_refresh] using hh

lemma ratio_restore (t : ℝ) (i : Fin n) (a : α) (x : Fin n → α) :
    D.ratio t i (x i) (Function.update x i a) = (D.ratio t i a x)⁻¹ := by
  simp [ratio, Function.update_eq_self, inv_div]

lemma hasDerivAt_p (t : ℝ) (x : Fin n → α) :
    HasDerivAt (fun u => D.p u x) (-refreshGenerator D.π (D.p t) x) t := by
  have hh := (hasDerivAt_heat D.π D.mass D.f x (D.horizon-t)).comp t
    ((hasDerivAt_id t).const_sub D.horizon)
  simpa [p] using hh

lemma continuous_p (x : Fin n → α) : Continuous (fun t => D.p t x) :=
  continuous_iff_continuousAt.mpr fun t => (D.hasDerivAt_p t x).continuousAt

lemma continuousOn_ratio (i : Fin n) (a : α) (x : Fin n → α) :
    ContinuousOn (fun t => D.ratio t i a x) (Set.Iic D.horizon) :=
  (D.continuous_p _).continuousOn.div (D.continuous_p x).continuousOn
    (fun t ht => (D.p_pos ht x).ne')

lemma logP_update {t : ℝ} (ht : t ≤ D.horizon) (i : Fin n) (a : α) (x : Fin n → α) :
    D.logP t (Function.update x i a)-D.logP t x = Real.log (D.ratio t i a x) := by
  exact (Real.log_div (D.p_pos ht _).ne' (D.p_pos ht _).ne').symm

lemma hasDerivAt_logP {t : ℝ} (ht : t ≤ D.horizon) (x : Fin n → α) :
    HasDerivAt (fun u => D.logP u x) (-refreshGenerator D.π (D.p t) x / D.p t x) t :=
  (D.hasDerivAt_p t x).log (D.p_pos ht x).ne'

lemma generator_div {t : ℝ} (ht : t ≤ D.horizon) (x : Fin n → α) :
    refreshGenerator D.π (D.p t) x / D.p t x =
      ∑ i, mean D.π (fun a => D.ratio t i a x-1) := by
  rw [generator_weighted_form D.π D.mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold mean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  unfold ratio
  field_simp [(D.p_pos ht x).ne']

/-- The drift of the reverse log density is entropy production. -/
theorem log_drift {t : ℝ} (ht : t ≤ D.horizon) (x : Fin n → α) :
    -refreshGenerator D.π (D.p t) x / D.p t x + D.revGen t (D.logP t) x =
      ∑ i, mean D.π (fun a => D.ratio t i a x * Real.log (D.ratio t i a x) -
        D.ratio t i a x + 1) := by
  rw [neg_div, D.generator_div ht]
  unfold revGen
  simp_rw [D.logP_update ht]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mean_neg, ← mean_add]
  congr 1
  funext a
  ring

/-- The pointwise score-production inequality underlying the stopped bound. -/
theorem score_drift {t : ℝ} (ht : t ≤ 2) (x : Fin n → α) :
    Real.log D.κ * D.score t x ≤ 2*(D.κ-1) *
      (-refreshGenerator D.π (D.p t) x / D.p t x + D.revGen t (D.logP t) x) := by
  rw [D.log_drift (ht.trans D.obs_le_horizon)]
  unfold score
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mean_smul, ← mean_smul]
  apply mean_mono D.πnonneg
  intro a
  have hb := D.ratio_bounds ht i a x
  simpa only [sub_sq_comm] using Talagrand.score_convexity D.κ_gt_one hb.1 hb.2

lemma exponent_bounds (ℓ θ : ℝ) (x : Fin n → α) :
    0 ≤ D.exponent ℓ θ x ∧ D.exponent ℓ θ x < (1/2:ℝ) := by
  unfold exponent
  split_ifs with h
  · exact frozen_exponent_bound _ 5 (by norm_num) (by linarith)
  · norm_num

end RefreshData
end TailBound
