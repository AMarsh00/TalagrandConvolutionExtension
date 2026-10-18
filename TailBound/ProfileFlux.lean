import TailBound.ProductCalculus
import TailBound.ProfileEntropy

/-! Threshold flux and dissipation for Lemma 3. Endpoint values of the flux
are included; the finite crossing set is excluded when applying the FTC. -/

open scoped BigOperators
open MeasureTheory intervalIntegral Filter
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

noncomputable def crossingFlux (x y u : ℝ) : ℝ :=
  if min x y ≤ Real.exp u ∧ Real.exp u ≤ max x y then |y-x| else 0

noncomputable def levelFlux (π : α → ℝ) (F : (Fin n → α) → ℝ) (u : ℝ) : ℝ :=
  (1/2:ℝ) * mean (tensorWeight π n) (fun x => ∑ i, mean π
    (fun a => crossingFlux (F x) (F (Function.update x i a)) u))

noncomputable def levelExcess (π : α → ℝ) (F : (Fin n → α) → ℝ) (u : ℝ) : ℝ :=
  mean (tensorWeight π n) (fun x => max (F x-Real.exp u) 0)

lemma crossingFlux_nonneg (x y u : ℝ) : 0 ≤ crossingFlux x y u := by
  unfold crossingFlux; split_ifs <;> positivity

lemma levelFlux_nonneg (π : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (F : (Fin n → α) → ℝ) (u : ℝ) : 0 ≤ levelFlux π F u := by
  apply mul_nonneg (by norm_num)
  apply mean_nonneg (tensorWeight_nonneg hπ0 n)
  intro x
  apply Finset.sum_nonneg
  intro i _
  exact mean_nonneg hπ0 (fun a => crossingFlux_nonneg _ _ _)

lemma levelFlux_generator (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (F : (Fin n → α) → ℝ) (u : ℝ) (hne : ∀ x, F x ≠ Real.exp u) :
    mean (tensorWeight π n) (fun x =>
      if Real.exp u < F x then refreshGenerator π F x else 0) = -levelFlux π F u := by
  have hh := product_integration_by_parts π hπ1 F
    (fun x => if Real.exp u < F x then 1 else 0)
  have hL : (fun x => (if Real.exp u < F x then (1:ℝ) else 0)*refreshGenerator π F x) =
      fun x => if Real.exp u < F x then refreshGenerator π F x else 0 := by
    funext x; split_ifs <;> simp
  rw [hL] at hh
  simp_rw [threshold_closed_pair (Real.exp u) _ _ (hne _) (hne _)] at hh
  have he (x y : ℝ) : |y-x| *(if min x y ≤ Real.exp u ∧ Real.exp u ≤ max x y then 1 else 0) =
      crossingFlux x y u := by unfold crossingFlux; split_ifs <;> simp
  simp_rw [he] at hh
  change -_ = levelFlux π F u at hh
  linarith

lemma measurable_crossingFlux {β : Type*} [MeasurableSpace β] (f g u : β → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hu : Measurable u) :
    Measurable (fun b => crossingFlux (f b) (g b) (u b)) := by
  unfold crossingFlux
  exact Measurable.ite
    ((measurableSet_le (hf.min hg) hu.exp).inter (measurableSet_le hu.exp (hf.max hg)))
    (hg.sub hf).abs measurable_const

lemma measurable_heat_flux (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) :
    Measurable (fun p : ℝ×ℝ => levelFlux π (heat π f p.1) p.2) := by
  unfold levelFlux mean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro a _
  apply Measurable.const_mul
  exact measurable_crossingFlux _ _ _
    ((continuous_heat π hπ1 f x).measurable.comp measurable_fst)
    ((continuous_heat π hπ1 f _).measurable.comp measurable_fst) measurable_snd

lemma intervalIntegrable_finite_sum {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    (a b : ℝ) (h : ∀ i, IntervalIntegrable (g i) volume a b) :
    IntervalIntegrable (fun t => ∑ i, g i t) volume a b := by
  have hh := IntervalIntegrable.sum Finset.univ (fun i _ => h i)
  have he : (∑ i, g i) = fun t => ∑ i, g i t := by funext t; simp
  rwa [he] at hh

lemma intervalIntegrable_crossingFlux_time (F G : ℝ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (u a b : ℝ) :
    IntervalIntegrable (fun t => crossingFlux (F t) (G t) u) volume a b := by
  let E := {t : ℝ | min (F t) (G t) ≤ Real.exp u ∧ Real.exp u ≤ max (F t) (G t)}
  have hE : MeasurableSet E :=
    (measurableSet_le (hF.measurable.min hG.measurable) measurable_const).inter
      (measurableSet_le measurable_const (hF.measurable.max hG.measurable))
  have he : (fun t => crossingFlux (F t) (G t) u) =
      E.indicator (fun t => |G t-F t|) := by
    funext t; simp only [crossingFlux, Set.indicator, E, Set.mem_setOf_eq]
  rw [he, intervalIntegrable_iff]
  exact (intervalIntegrable_iff.mp ((hG.sub hF).abs.intervalIntegrable a b)).indicator hE

lemma intervalIntegrable_crossingFlux_level (x y a b : ℝ) :
    IntervalIntegrable (crossingFlux x y) volume a b := by
  let E := {u : ℝ | min x y ≤ Real.exp u ∧ Real.exp u ≤ max x y}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_const Real.measurable_exp).inter
      (measurableSet_le Real.measurable_exp measurable_const)
  have he : crossingFlux x y = E.indicator (fun _ => |y-x|) := by
    funext u; simp only [crossingFlux, Set.indicator, E, Set.mem_setOf_eq]
  rw [he, intervalIntegrable_iff]
  exact (intervalIntegrable_iff.mp intervalIntegral.intervalIntegrable_const).indicator hE

lemma intervalIntegrable_levelFlux_time (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (u a b : ℝ) :
    IntervalIntegrable (fun s => levelFlux π (heat π f s) u) volume a b := by
  unfold levelFlux mean
  apply IntervalIntegrable.const_mul
  apply intervalIntegrable_finite_sum
  intro x
  apply IntervalIntegrable.const_mul
  apply intervalIntegrable_finite_sum
  intro i
  apply intervalIntegrable_finite_sum
  intro g
  exact (intervalIntegrable_crossingFlux_time _ _ (continuous_heat π hπ1 f x)
    (continuous_heat π hπ1 f _) u a b).const_mul _

lemma intervalIntegrable_levelFlux_level (π : α → ℝ)
    (F : (Fin n → α) → ℝ) (a b : ℝ) :
    IntervalIntegrable (levelFlux π F) volume a b := by
  unfold levelFlux mean
  apply IntervalIntegrable.const_mul
  apply intervalIntegrable_finite_sum
  intro x
  apply IntervalIntegrable.const_mul
  apply intervalIntegrable_finite_sum
  intro i
  apply intervalIntegrable_finite_sum
  intro g
  exact (intervalIntegrable_crossingFlux_level (F x) (F (Function.update x i g)) a b).const_mul _

lemma hasDerivAt_levelExcess (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (s u : ℝ) (hne : ∀ x, heat π f s x ≠ Real.exp u) :
    HasDerivAt (fun t => levelExcess π (heat π f t) u) (-levelFlux π (heat π f s) u) s := by
  have hd (x : Fin n → α) : HasDerivAt (fun t => max (heat π f t x-Real.exp u) 0)
      (if Real.exp u < heat π f s x then refreshGenerator π (heat π f s) x else 0) s := by
    rcases lt_trichotomy (Real.exp u) (heat π f s x) with h|h|h
    · rw [if_pos h]
      have hev : ∀ᶠ t in nhds s, Real.exp u < heat π f t x :=
        (isOpen_lt continuous_const (continuous_heat π hπ1 f x)).mem_nhds h
      apply ((hasDerivAt_heat π hπ1 f x s).sub_const (Real.exp u)).congr_of_eventuallyEq
      filter_upwards [hev] with t ht
      exact max_eq_left (by linarith)
    · exact False.elim (hne x h.symm)
    · rw [if_neg (not_lt.mpr h.le)]
      have hev : ∀ᶠ t in nhds s, heat π f t x < Real.exp u :=
        (isOpen_lt (continuous_heat π hπ1 f x) continuous_const).mem_nhds h
      apply (hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq
      filter_upwards [hev] with t ht
      exact max_eq_right (by linarith)
  have hh := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → α)))
    (fun x _ => (hd x).const_mul (tensorWeight π n x))
  change HasDerivAt _ (mean (tensorWeight π n) _) s at hh
  rw [levelFlux_generator π hπ1 _ u hne] at hh
  exact hh

/-- Integrated flux equals the decrease of excess mass. -/
theorem levelExcess_dissipation (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (hf1 : mean (tensorWeight π n) f = 1)
    (u : ℝ) (hu : 0 < u) (a b : ℝ) (hab : a ≤ b) :
    levelExcess π (heat π f b) u - levelExcess π (heat π f a) u =
      -∫ s in a..b, levelFlux π (heat π f s) u := by
  classical
  have he : Real.exp u ≠ mean (tensorWeight π n) f := by
    rw [hf1]; exact ne_of_gt (Real.one_lt_exp_iff.mpr hu)
  have hZ := finite_heat_crossings π f (Real.exp u) he
  have hc : Continuous (fun t => levelExcess π (heat π f t) u) := by
    unfold levelExcess mean
    apply continuous_finset_sum
    intro x _
    exact continuous_const.mul (((continuous_heat π hπ1 f x).sub continuous_const).max continuous_const)
  have ht := Talagrand.sub_eq_integral_of_finite_exceptions hab hZ.toFinset hc.continuousOn
    (fun s _ hsz => hasDerivAt_levelExcess π hπ1 f s u
      (fun x hx => hsz (hZ.mem_toFinset.mpr ⟨x,hx⟩)))
    (intervalIntegrable_levelFlux_time π hπ1 f u a b).neg
  simpa only [intervalIntegral.integral_neg] using ht

/-- The total time flux at each positive log level is at most one. -/
theorem flux_integral_le_one (π : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (hπ1 : ∑ a, π a = 1) (f : (Fin n → α) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hf1 : mean (tensorWeight π n) f = 1) (u : ℝ) (hu : 0 < u)
    (S : ℝ) (hS : 0 ≤ S) : ∫ s in (0:ℝ)..S, levelFlux π (heat π f s) u ≤ 1 := by
  have hd := levelExcess_dissipation π hπ1 f hf1 u hu 0 S hS
  have hnon : 0 ≤ levelExcess π (heat π f S) u :=
    mean_nonneg (tensorWeight_nonneg hπ0 n) (fun x => le_max_right _ _)
  have hinit : levelExcess π (heat π f 0) u ≤ 1 := by
    rw [heat_zero]
    refine (mean_mono (tensorWeight_nonneg hπ0 n) (fun x => ?_)).trans_eq hf1
    exact max_le (by linarith [Real.exp_pos u]) (hf x)
  linarith

end TailBound
