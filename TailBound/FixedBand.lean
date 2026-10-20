import TailBound.AveragedError

/-!
# Fixed Band

Good starting times and the bounded-supremum bootstrap.
The argument adapts the Boolean fixed-band proof using weighted
profile, score and discrepancy inputs.
-/
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound
attribute [local instance] Classical.propDecidable

lemma exp_neg_four_le_quarter : Real.exp (-4) ≤ 1 / 4 := by
  have hh : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  have hle : Real.exp (-4) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by norm_num)
  rw [hh] at hle
  nlinarith [exp_neg_one_le_half, Real.exp_pos (-1)]

namespace RefreshData

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

variable (D : RefreshData α n)

theorem band_step {ℓ M : ℝ} (hℓ : 64 ≤ ℓ) (hM : 0 ≤ M)
    (hMb : ∀ r, ℓ ≤ r → Real.sqrt r * D.startBand 2 r ≤ M) :
    Real.sqrt ℓ * D.startBand 2 ℓ ≤ (2 / 3) * M + (8 / 3) * D.averageConstant := by
  have hl : 0 < ℓ := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hl
  let m := Nat.floor (ℓ / 2)
  have hmlo : ℓ / 2 - 1 ≤ (m : ℝ) := by have hh := Nat.lt_floor_add_one (ℓ / 2); dsimp [m]; linarith
  have hmhi : (m : ℝ) ≤ ℓ / 2 := Nat.floor_le (by linarith)
  have hm : 10 ≤ m := Nat.le_floor (by norm_num; linarith)
  obtain ⟨Q, hQ⟩ := D.exists_start_cutoff ℓ
  have hI : IntegrableOn (D.errorMajorant ℓ m Q) (Set.Ioc 1 2) volume := by
    have hh := D.errorMajorant_integrable ℓ m Q
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hh
  have hv : volume (Set.Ioc (1 : ℝ) 2) ≠ 0 := by rw [Real.volume_Ioc]; norm_num
  obtain ⟨θ, hθ, hgood⟩ := exists_le_setAverage hv measure_Ioc_lt_top.ne hI
  have he : (⨍ t in Set.Ioc (1 : ℝ) 2, D.errorMajorant ℓ m Q t) =
      ∫ t in (1 : ℝ)..2, D.errorMajorant ℓ m Q t := by
    rw [setAverage_eq, Real.volume_real_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num only [sub_self, sub_zero, show (2 : ℝ) - 1=1 by norm_num, inv_one, one_smul]
    rw [integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  rw [he] at hgood
  have hg := hgood.trans (D.errorMajorant_average hℓ m Q hmlo hmhi)
  obtain ⟨C⟩ := D.exists_stoppedCoupling ℓ θ hl hθ.2
  have herr := (C.errorMajorant_bound hθ.1.le hθ.2 m Q hm (hQ θ hθ.2)).trans hg
  obtain ⟨J, hJ⟩ := StoppedCoupling.exists_band_cutoff (D := D) (ℓ := ℓ)
  have htail : (∑ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ)) * C.bandA (ℓ + j)) ≤ 2 * (M / Real.sqrt ℓ) := by
    have hjbound (j : ℕ) : C.bandA (ℓ + j) ≤ M / Real.sqrt ℓ := by
      have hjn := Nat.cast_nonneg (α := ℝ) j
      have hsj : 0 < Real.sqrt (ℓ + j) := Real.sqrt_pos.mpr (by linarith)
      have hp : D.startBand 2 (ℓ + j) ≤ M / Real.sqrt (ℓ + j) := by
        apply (le_div_iff₀ hsj).mpr
        nlinarith [hMb (ℓ + j) (by linarith)]
      exact (C.bandA_le_profile hθ.2 _).trans (hp.trans
        (div_le_div_of_nonneg_left hM hs (Real.sqrt_le_sqrt (by linarith))))
    have hgeo : (∑ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ))) ≤ 2 := by
      apply le_trans _ (sum_exp_neg_le_two (J + 1))
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega))
        (fun j _ _ => (Real.exp_pos _).le)
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ)) * (M / Real.sqrt ℓ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hjbound j) (Real.exp_pos _).le)
      _ = (∑ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ))) * (M / Real.sqrt ℓ) := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeo (div_nonneg hM hs.le)
  have hc := C.band_contraction hθ.2 J hJ
  have ha := C.bandA_nonneg hθ.2 ℓ
  have hi := C.inactiveBand_nonneg hθ.2 ℓ
  have hc0 := (Real.exp_pos (-4)).le
  have hlow := mul_le_mul_of_nonneg_right
    (show (3 / 4 : ℝ) ≤ 1 - Real.exp (-4) by linarith [exp_neg_four_le_quarter]) ha
  have hup1 := mul_le_mul_of_nonneg_left htail hc0
  have hup2 := mul_le_mul_of_nonneg_right exp_neg_four_le_quarter (show 0 ≤ 2 * (M / Real.sqrt ℓ) by positivity)
  have hp : D.startBand 2 ℓ ≤ (2 / 3) * (M / Real.sqrt ℓ) + (8 / 3) * (D.averageConstant / Real.sqrt ℓ) := by
    rw [C.profile_split hθ.2]
    linarith
  have hh := mul_le_mul_of_nonneg_left hp hs.le
  have heq : Real.sqrt ℓ * ((2 / 3) * (M / Real.sqrt ℓ) + (8 / 3) * (D.averageConstant / Real.sqrt ℓ)) =
      (2 / 3) * M + (8 / 3) * D.averageConstant := by field_simp
  exact hh.trans_eq heq

omit [Nonempty α] in
lemma exists_profile_vanish : ∃ B : ℝ, ∀ r, B ≤ r → D.startBand 2 r = 0 := by
  obtain ⟨B, hB⟩ := D.exists_uniform_log_bound
  refine ⟨B, fun r hr => ?_⟩
  unfold startBand
  apply Finset.sum_eq_zero
  intro x _
  rw [if_neg (by intro hh; linarith [hB 2 le_rfl x, hh.1]), mul_zero]

noncomputable def bandConstant : ℝ := max 8 (8 * D.averageConstant)

omit [DecidableEq α] [Nonempty α] in
lemma bandConstant_pos : 0 < D.bandConstant := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- A fixed-band bound for an arbitrary finite alphabet and probability weights. The
constant depends only on the marginal data and the fixed refresh time. -/
theorem fixed_band (ℓ : ℝ) (hℓ : 2 < ℓ) :
    D.startBand 2 ℓ ≤ D.bandConstant / Real.sqrt ℓ := by
  let g : ℝ → ℝ := fun r => Real.sqrt r * D.startBand 2 r
  have hgn (r : ℝ) : 0 ≤ g r := mul_nonneg (Real.sqrt_nonneg _) (D.startBand_nonneg le_rfl r)
  have hne : (g '' Set.Ici 64).Nonempty := ⟨g 64, 64, Set.self_mem_Ici, rfl⟩
  obtain ⟨B, hB⟩ := D.exists_profile_vanish
  have hbdd : BddAbove (g '' Set.Ici 64) := by
    refine ⟨Real.sqrt B + 1, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    dsimp [g]
    by_cases hBr : B ≤ r
    · rw [hB r hBr, mul_zero]; positivity
    · have hp := D.startBand_le_one (θ := 2) le_rfl r
      have hn := D.startBand_nonneg (θ := 2) le_rfl r
      have hs := Real.sqrt_le_sqrt (lt_of_not_ge hBr).le
      nlinarith [Real.sqrt_nonneg r]
  let M := sSup (g '' Set.Ici 64)
  have hMb (r : ℝ) (hr : 64 ≤ r) : g r ≤ M := le_csSup hbdd ⟨r, hr, rfl⟩
  have hM : 0 ≤ M := (hgn 64).trans (hMb 64 le_rfl)
  have hrec : M ≤ (2 / 3) * M + (8 / 3) * D.averageConstant := by
    apply csSup_le hne
    rintro _ ⟨r, hr, rfl⟩
    exact D.band_step hr hM (fun u hu => hMb u (hr.trans hu))
  have hMle : M ≤ 8 * D.averageConstant := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr (by linarith)
  apply (le_div_iff₀ hs).mpr
  by_cases hl64 : 64 ≤ ℓ
  · have hh := hMb ℓ hl64
    dsimp [g] at hh
    have hc : 8 * D.averageConstant ≤ D.bandConstant := le_max_right _ _
    nlinarith
  · have hp := D.startBand_le_one (θ := 2) le_rfl ℓ
    have hsq := Real.sq_sqrt (show 0 ≤ ℓ by linarith)
    have hc : (8 : ℝ) ≤ D.bandConstant := le_max_left _ _
    nlinarith [Real.sqrt_nonneg ℓ]

end RefreshData
end TailBound
