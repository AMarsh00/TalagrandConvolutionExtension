import TailBound.ProfileFlux

/-! The integrated anti-concentration profile (Lemma 3). The proof follows
the manuscript: localized entropy, product LSI, coarea, dissipation, Tonelli.
The explicit constant is deliberately nonoptimal and independent of dimension.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Filter
namespace TailBound

set_option linter.unusedSectionVars false

lemma sqrtTest_crossing_bound (ℓ a b : ℝ) :
    (Talagrand.sqrtTest ℓ b-Talagrand.sqrtTest ℓ a)^2 ≤
      16 * ∫ u in ℓ-1..ℓ+2, crossingFlux (Real.exp a) (Real.exp b) u := by
  have he : crossingFlux (Real.exp a) (Real.exp b) =
      (Set.Icc (min a b) (max a b)).indicator (fun _ => |Real.exp b-Real.exp a|) := by
    funext u
    have hc : (min (Real.exp a) (Real.exp b) ≤ Real.exp u ∧
        Real.exp u ≤ max (Real.exp a) (Real.exp b)) ↔ (min a b ≤ u ∧ u ≤ max a b) := by
      simp only [min_le_iff, le_max_iff, Real.exp_le_exp]
    simp only [crossingFlux, Set.indicator, Set.mem_Icc, hc]
  have hint : (∫ u in ℓ-1..ℓ+2, crossingFlux (Real.exp a) (Real.exp b) u) =
      (volume (Set.Ioc (ℓ-1) (ℓ+2) ∩ Set.uIcc a b)).toReal * |Real.exp b-Real.exp a| := by
    rw [he, intervalIntegral.integral_of_le (by linarith),
      setIntegral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul]
    rfl
  have hsub : Set.uIoc a b ∩ Set.Ioo (ℓ-1) (ℓ+2) ⊆
      Set.Ioc (ℓ-1) (ℓ+2) ∩ Set.uIcc a b := by
    intro x hx
    exact ⟨Set.Ioo_subset_Ioc_self hx.2, Set.uIoc_subset_uIcc hx.1⟩
  have hmeasure : (volume (Set.uIoc a b ∩ Set.Ioo (ℓ-1) (ℓ+2))).toReal ≤
      (volume (Set.Ioc (ℓ-1) (ℓ+2) ∩ Set.uIcc a b)).toReal := by
    apply ENNReal.toReal_mono
    · exact ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top)
    · exact measure_mono hsub
  have hs := Talagrand.sqrtTest_sq_diff_le ℓ a b
  rw [hint]
  nlinarith [mul_le_mul_of_nonneg_right hmeasure (abs_nonneg (Real.exp b-Real.exp a))]

lemma sqrt_localized_density {Ω : Type*} (F : Ω → ℝ) (hF : ∀ x, 0 < F x)
    (ℓ : ℝ) (x : Ω) :
    Real.sqrt (localizedDensity F ℓ x) = Talagrand.sqrtTest ℓ (Real.log (F x)) := by
  rw [localizedDensity, Real.sqrt_mul (hF x).le,
    Real.sqrt_sq (Talagrand.cutoff_mem_Icc _).1,
    Talagrand.sqrtTest, Real.exp_half, Real.exp_log (hF x)]

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

lemma localized_energy_le_flux (π : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (F : (Fin n → α) → ℝ) (hF : ∀ x, 0 < F x) (ℓ : ℝ) :
    mean (tensorWeight π n) (fun x => ∑ i, mean π (fun a =>
      (Real.sqrt (localizedDensity F ℓ (Function.update x i a)) -
        Real.sqrt (localizedDensity F ℓ x))^2)) ≤
      32 * ∫ u in ℓ-1..ℓ+2, levelFlux π F u := by
  have hpoint (x : Fin n → α) (i : Fin n) (a : α) :
      (Real.sqrt (localizedDensity F ℓ (Function.update x i a)) -
        Real.sqrt (localizedDensity F ℓ x))^2 ≤
      16 * ∫ u in ℓ-1..ℓ+2, crossingFlux (F x) (F (Function.update x i a)) u := by
    rw [sqrt_localized_density F hF, sqrt_localized_density F hF]
    simpa only [Real.exp_log (hF _)] using sqrtTest_crossing_bound ℓ
      (Real.log (F x)) (Real.log (F (Function.update x i a)))
  have hsum := mean_mono (tensorWeight_nonneg hπ0 n) fun x =>
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => mean_mono hπ0 (hpoint x i)
  simp_rw [mean_smul, ← Finset.mul_sum] at hsum
  rw [mean_smul] at hsum
  have hs : mean (tensorWeight π n) (fun x => ∑ i, mean π (fun a =>
        ∫ u in ℓ-1..ℓ+2, crossingFlux (F x) (F (Function.update x i a)) u)) =
      2 * ∫ u in ℓ-1..ℓ+2, levelFlux π F u := by
    unfold levelFlux mean
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finset_sum
      (fun x _ => (intervalIntegrable_finite_sum _ _ _ fun i =>
        intervalIntegrable_finite_sum _ _ _ fun a =>
          (intervalIntegrable_crossingFlux_level _ _ _ _).const_mul (π a)).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul]
    have hi (x : Fin n → α) :
        (∫ u in ℓ-1..ℓ+2, ∑ i, ∑ a, π a * crossingFlux (F x) (F (Function.update x i a)) u) =
        ∑ i, ∑ a, π a * ∫ u in ℓ-1..ℓ+2, crossingFlux (F x) (F (Function.update x i a)) u := by
      rw [intervalIntegral.integral_finset_sum (fun i _ =>
        intervalIntegrable_finite_sum _ _ _ fun a =>
          (intervalIntegrable_crossingFlux_level _ _ _ _).const_mul (π a))]
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finset_sum (fun a _ =>
        (intervalIntegrable_crossingFlux_level _ _ _ _).const_mul (π a))]
      simp_rw [intervalIntegral.integral_const_mul]
    simp_rw [hi]
    ring
  rw [hs] at hsum
  linarith

lemma lintegral_Ioi_bound {g : ℝ → ℝ} (hnn : ∀ s, 0 ≤ g s)
    (hint : ∀ S : ℝ, IntervalIntegrable g volume 0 S)
    {C : ℝ} (hC : ∀ S : ℝ, 0 ≤ S → ∫ s in (0:ℝ)..S, g s ≤ C) :
    ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (g s) ≤ ENNReal.ofReal C := by
  have he : (⋃ k : ℕ, Set.Ioc (0:ℝ) (k:ℝ)) = Set.Ioi (0:ℝ) := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨k,hk⟩; exact hk.1
    · intro hs
      obtain ⟨k,hk⟩ := exists_nat_ge s
      exact ⟨k,hs,hk⟩
  rw [← he, setLIntegral_iUnion_of_directed _
    (fun i j => ⟨max i j,
      Set.Ioc_subset_Ioc_right (by exact_mod_cast le_max_left i j),
      Set.Ioc_subset_Ioc_right (by exact_mod_cast le_max_right i j)⟩)]
  apply iSup_le
  intro k
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hk).mp (hint k))
    (Eventually.of_forall hnn), ← intervalIntegral.integral_of_le hk]
  exact ENNReal.ofReal_le_ofReal (hC k hk)

/-- Lemma 3, fully quantified over all dimensions and all positive densities.
`384/m` is a valid explicit constant for the corrected product LSI. -/
theorem integrated_profile_bound (π : α → ℝ) (m : ℝ) (hm : 0 < m)
    (hπ : ∀ a, m ≤ π a) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (hf : ∀ x, 0 < f x)
    (hf1 : mean (tensorWeight π n) f = 1) (ℓ : ℝ) (hℓ : 2 < ℓ) :
    ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (bandMass (tensorWeight π n) (heat π f s) ℓ) ≤
      ENNReal.ofReal (384 / (m*ℓ)) := by
  have hπ0 : ∀ a, 0 ≤ π a := fun a => (hm.trans_le (hπ a)).le
  have hℓ0 : 0 < ℓ := by linarith
  have hreal (s : ℝ) (hs : 0 ≤ s) :
      bandMass (tensorWeight π n) (heat π f s) ℓ ≤
        (128/(m*ℓ)) * ∫ u in ℓ-1..ℓ+2, levelFlux π (heat π f s) u := by
    have hF := heat_pos π hπ0 hπ1 f hf hs
    have h1 := band_le_localized_energy π m hm hπ hπ1 n (heat π f s) hF
      (by rw [mean_heat π hπ1, hf1]) ℓ hℓ.le
    have h2 := localized_energy_le_flux π hπ0 (heat π f s) hF ℓ
    have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4/m))
    calc
      _ ≤ ((4/m) * (32 * ∫ u in ℓ-1..ℓ+2, levelFlux π (heat π f s) u)) / ℓ :=
        (le_div_iff₀ hℓ0).mpr (by nlinarith [h3])
      _ = _ := by field_simp; ring
  have hjm := (measurable_heat_flux π hπ1 f).ennreal_ofReal
  have hinner (u : ℝ) (hu : 0 < u) :
      ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (levelFlux π (heat π f s) u) ≤ 1 := by
    have hh := lintegral_Ioi_bound
      (fun s => levelFlux_nonneg π hπ0 _ u)
      (fun S => intervalIntegrable_levelFlux_time π hπ1 f u 0 S)
      (fun S hS => flux_integral_le_one π hπ0 hπ1 f (fun x => (hf x).le) hf1 u hu S hS)
    simpa only [ENNReal.ofReal_one] using hh
  have hLU : ℓ-1 ≤ ℓ+2 := by linarith
  calc
    _ ≤ ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal
        ((128/(m*ℓ)) * ∫ u in ℓ-1..ℓ+2, levelFlux π (heat π f s) u) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact ENNReal.ofReal_le_ofReal (hreal s hs.le)
    _ = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (128/(m*ℓ)) *
        ∫⁻ u in Set.Ioc (ℓ-1) (ℓ+2), ENNReal.ofReal (levelFlux π (heat π f s) u) := by
      apply lintegral_congr
      intro s
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [intervalIntegral.integral_of_le hLU]
      exact ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hLU).mp
          (intervalIntegrable_levelFlux_level π _ _ _))
        (Eventually.of_forall fun u => levelFlux_nonneg π hπ0 _ u)
    _ = ENNReal.ofReal (128/(m*ℓ)) *
        ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ u in Set.Ioc (ℓ-1) (ℓ+2),
          ENNReal.ofReal (levelFlux π (heat π f s) u) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (128/(m*ℓ)) *
        ∫⁻ u in Set.Ioc (ℓ-1) (ℓ+2), ∫⁻ s in Set.Ioi (0:ℝ),
          ENNReal.ofReal (levelFlux π (heat π f s) u) := by
      rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ ≤ ENNReal.ofReal (128/(m*ℓ)) * ∫⁻ _u in Set.Ioc (ℓ-1) (ℓ+2), 1 := by
      apply mul_le_mul_left'
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hinner u (by linarith [hu.1])
    _ = ENNReal.ofReal (128/(m*ℓ)) * ENNReal.ofReal 3 := by
      rw [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioc]
      norm_num
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

lemma measurable_band_profile (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (ℓ : ℝ) :
    Measurable (fun s => bandMass (tensorWeight π n) (heat π f s) ℓ) := by
  unfold bandMass mean
  apply Finset.measurable_sum
  intro x _
  apply Measurable.const_mul
  have he : (fun s => (Set.Ioc ℓ (ℓ+1)).indicator (fun _ => heat π f s x)
      (Real.log (heat π f s x))) =
      {s | Real.log (heat π f s x) ∈ Set.Ioc ℓ (ℓ+1)}.indicator (fun s => heat π f s x) := by
    funext s
    simp only [Set.indicator, Set.mem_setOf_eq]
  rw [he]
  exact (continuous_heat π hπ1 f x).measurable.indicator
    ((Real.measurable_log.comp (continuous_heat π hπ1 f x).measurable)
      measurableSet_Ioc)

/-- The real-integral form used in the stopped-coupling argument. -/
theorem profile_window_bound (π : α → ℝ) (m : ℝ) (hm : 0 < m)
    (hπ : ∀ a, m ≤ π a) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (hf : ∀ x, 0 < f x)
    (hf1 : mean (tensorWeight π n) f = 1) (ℓ : ℝ) (hℓ : 2 < ℓ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, bandMass (tensorWeight π n) (heat π f s) ℓ ≤ 384/(m*ℓ) := by
  have hπ0 : ∀ a, 0 ≤ π a := fun a => (hm.trans_le (hπ a)).le
  have hmeas := measurable_band_profile π hπ1 f ℓ
  have hn (s : ℝ) (hs : s ∈ Set.Ioc a b) :
      0 ≤ bandMass (tensorWeight π n) (heat π f s) ℓ :=
    bandMass_nonneg _ _ (tensorWeight_nonneg hπ0 n)
      (heat_nonneg π hπ0 f (fun x => (hf x).le) (ha.trans hs.1.le)) ℓ
  have hle (s : ℝ) (hs : s ∈ Set.Ioc a b) :
      bandMass (tensorWeight π n) (heat π f s) ℓ ≤ 1 := by
    have hh := bandMass_le_mean _ _ (tensorWeight_nonneg hπ0 n)
      (heat_nonneg π hπ0 f (fun x => (hf x).le) (ha.trans hs.1.le)) ℓ
    rwa [mean_heat π hπ1, hf1] at hh
  have hi : IntegrableOn (fun s => bandMass (tensorWeight π n) (heat π f s) ℓ)
      (Set.Ioc a b) volume := by
    apply Integrable.mono' (g := fun _ : ℝ => (1:ℝ))
      (integrableOn_const measure_Ioc_lt_top.ne) hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hn s hs)]
    exact hle s hs
  have hae : (0:ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc a b)]
      (fun s => bandMass (tensorWeight π n) (heat π f s) ℓ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hn s hs
  have hh : ENNReal.ofReal (∫ s in a..b, bandMass (tensorWeight π n) (heat π f s) ℓ) ≤
      ENNReal.ofReal (384/(m*ℓ)) := by
    rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal hi hae]
    exact (lintegral_mono_set (fun s hs => lt_of_le_of_lt ha hs.1)).trans
      (integrated_profile_bound π m hm hπ hπ1 f hf hf1 ℓ hℓ)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

/-- The manuscript's alphabet-dependent constant exists before choosing the
dimension or density. This is the full quantifier order of Lemma 3. -/
theorem lemma3 (π : α → ℝ) (hπ : ∀ a, 0 < π a) (hπ1 : ∑ a, π a = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : (Fin n → α) → ℝ),
      (∀ x, 0 < f x) → mean (tensorWeight π n) f = 1 →
      ∀ ℓ : ℝ, 2 < ℓ →
        ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (bandMass (tensorWeight π n) (heat π f s) ℓ) ≤
          ENNReal.ofReal (C/ℓ) := by
  have hne : (Finset.univ : Finset α).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [he] at hπ1
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image Finset.univ π hne
  refine ⟨384/π a, div_pos (by norm_num) (hπ a), ?_⟩
  intro n f hf hf1 ℓ hℓ
  have hh := integrated_profile_bound π (π a) (hπ a) (fun b => ha b (Finset.mem_univ b))
    hπ1 f hf hf1 ℓ hℓ
  simpa only [div_div] using hh

end TailBound
