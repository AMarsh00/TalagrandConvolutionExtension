import TailBound.LayerScore

/-! Starting-law bands and the change of variables in the averaging step. -/
open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

noncomputable def startBand (θ r : ℝ) : ℝ :=
  ∑ x, D.density θ x*(if r < D.logP θ x ∧ D.logP θ x ≤ r+1 then 1 else 0)

lemma startBand_eq_profile (θ r : ℝ) :
    D.startBand θ r = bandMass (tensorWeight D.π n) (heat D.π D.f (D.horizon-θ)) r := by
  apply Finset.sum_congr rfl
  intro x _
  unfold density logP p
  simp only [Set.indicator,Set.mem_Ioc]
  split_ifs <;> simp_all

lemma startBand_nonneg {θ : ℝ} (hθ : θ ≤ 2) (r : ℝ) : 0 ≤ D.startBand θ r := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (D.density_nonneg (hθ.trans D.obs_le_horizon) x)
  split_ifs <;> norm_num

lemma startBand_le_one {θ : ℝ} (hθ : θ ≤ 2) (r : ℝ) : D.startBand θ r ≤ 1 := by
  rw [← D.density_mass θ]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp [D.density_nonneg (hθ.trans D.obs_le_horizon) x]

lemma measurable_startBand (r : ℝ) : Measurable (fun θ => D.startBand θ r) := by
  simp_rw [D.startBand_eq_profile]
  exact (measurable_band_profile D.π D.mass D.f r).comp (measurable_const.sub measurable_id)

lemma intervalIntegrable_startBand (r : ℝ) :
    IntervalIntegrable (fun θ => D.startBand θ r) volume 1 2 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  apply Integrable.mono' (g := fun _ : ℝ => (1:ℝ))
    (integrableOn_const measure_Ioc_lt_top.ne) (D.measurable_startBand r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [Real.norm_eq_abs,abs_of_nonneg (D.startBand_nonneg hθ.2 r)]
  exact D.startBand_le_one hθ.2 r

lemma startBand_window_bound (r : ℝ) (hr : 2 < r) :
    ∫ θ in (1:ℝ)..2, D.startBand θ r ≤ 384/(D.m*r) := by
  simp_rw [D.startBand_eq_profile]
  rw [intervalIntegral.integral_comp_sub_left (fun s => bandMass (tensorWeight D.π n) (heat D.π D.f s) r) D.horizon]
  exact profile_window_bound D.π D.m D.mpos D.lower D.mass D.f D.fpos D.fmass r hr
    (D.horizon-2) (D.horizon-1) (by dsimp [horizon]; linarith [D.τpos]) (by linarith)

lemma gap_layer_iff (ℓ θ r : ℝ) (hr : 0 < r) (x : Fin n → α) :
    (r ≤ D.gap ℓ θ x ∧ D.gap ℓ θ x < r+1) ↔
      (ℓ-r-1 < D.logP θ x ∧ D.logP θ x ≤ ℓ-r) := by
  unfold gap
  rw [max_lt_iff]
  constructor
  · intro hh
    have he : r ≤ ℓ-D.logP θ x := (le_max_iff.mp hh.1).resolve_right (by linarith)
    constructor <;> linarith [hh.2.1]
  · intro hh
    constructor
    · apply le_max_of_le_left
      linarith
    · constructor <;> linarith

noncomputable def layerMass (ℓ θ r : ℝ) : ℝ :=
  ∑ x, D.density θ x*(if r ≤ D.gap ℓ θ x ∧ D.gap ℓ θ x < r+1 then 1 else 0)

lemma layerMass_eq_startBand (ℓ θ r : ℝ) (hr : 0 < r) :
    D.layerMass ℓ θ r = D.startBand θ (ℓ-r-1) := by
  apply Finset.sum_congr rfl
  intro x _
  have he : ℓ-r-1+1 = ℓ-r := by ring
  simp only [D.gap_layer_iff ℓ θ r hr x,he]

lemma layerMass_window_bound (ℓ r : ℝ) (hr : 0 < r) (hℓr : 2 < ℓ-r-1) :
    ∫ θ in (1:ℝ)..2, D.layerMass ℓ θ r ≤ 384/(D.m*(ℓ-r-1)) := by
  simp_rw [D.layerMass_eq_startBand ℓ _ r hr]
  exact D.startBand_window_bound _ hℓr

end TailBound.RefreshData
