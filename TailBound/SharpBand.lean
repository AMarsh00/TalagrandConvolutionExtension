import TailBound.FixedBand
import TailBound.SharpAverage

/-! Lemma 2 with a prefactor depending only on π, uniformly in τ. -/
open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
variable (D : RefreshData α n)

theorem band_step_sharp {ℓ M : ℝ} (hℓ : 64 ≤ ℓ) (hK : D.sharpK^2 ≤ ℓ) (hM : 0 ≤ M)
    (hMb : ∀ r, ℓ ≤ r → Real.sqrt r*D.startBand 2 r ≤ M) :
    Real.sqrt ℓ*D.startBand 2 ℓ ≤ (2/3)*M+(8/3)*(D.sharpAverageConstant*D.sharpK) := by
  have hl : 0 < ℓ := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hl
  let m := Nat.floor (ℓ/2)
  have hmlo : ℓ/2-1 ≤ (m:ℝ) := by have hh := Nat.lt_floor_add_one (ℓ/2); dsimp [m]; linarith
  have hmhi : (m:ℝ) ≤ ℓ/2 := Nat.floor_le (by linarith)
  have hm : 10 ≤ m := Nat.le_floor (by norm_num; linarith)
  obtain ⟨Q,hQ⟩ := D.exists_start_cutoff ℓ
  have hI : IntegrableOn (D.errorMajorant ℓ m Q) (Set.Ioc 1 2) volume := by
    have hh := D.errorMajorant_integrable ℓ m Q
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hh
  have hv : volume (Set.Ioc (1:ℝ) 2) ≠ 0 := by rw [Real.volume_Ioc]; norm_num
  obtain ⟨θ,hθ,hgood⟩ := exists_le_setAverage hv measure_Ioc_lt_top.ne hI
  have he : (⨍ t in Set.Ioc (1:ℝ) 2, D.errorMajorant ℓ m Q t) =
      ∫ t in (1:ℝ)..2, D.errorMajorant ℓ m Q t := by
    rw [setAverage_eq,Real.volume_real_Ioc_of_le (by norm_num : (1:ℝ) ≤ 2)]
    norm_num only [sub_self,sub_zero,show (2:ℝ)-1=1 by norm_num,inv_one,one_smul]
    rw [integral_of_le (by norm_num : (1:ℝ) ≤ 2)]
  rw [he] at hgood
  have hg := hgood.trans (D.errorMajorant_average_sharp hℓ hK m Q hmlo hmhi)
  obtain ⟨C⟩ := D.exists_stoppedCoupling ℓ θ hl hθ.2
  have herr := (C.errorMajorant_bound hθ.1.le hθ.2 m Q hm (hQ θ hθ.2)).trans hg
  obtain ⟨J,hJ⟩ := StoppedCoupling.exists_band_cutoff (D := D) (ℓ := ℓ)
  have htail : (∑ j ∈ Finset.Icc 1 J, Real.exp (-(j:ℝ))*C.bandA (ℓ+j)) ≤ 2*(M/Real.sqrt ℓ) := by
    have hjbound (j : ℕ) : C.bandA (ℓ+j) ≤ M/Real.sqrt ℓ := by
      have hjn := Nat.cast_nonneg (α := ℝ) j
      have hsj : 0 < Real.sqrt (ℓ+j) := Real.sqrt_pos.mpr (by linarith)
      have hp : D.startBand 2 (ℓ+j) ≤ M/Real.sqrt (ℓ+j) := by
        apply (le_div_iff₀ hsj).mpr
        nlinarith [hMb (ℓ+j) (by linarith)]
      exact (C.bandA_le_profile hθ.2 _).trans (hp.trans
        (div_le_div_of_nonneg_left hM hs (Real.sqrt_le_sqrt (by linarith))))
    have hgeo : (∑ j ∈ Finset.Icc 1 J, Real.exp (-(j:ℝ))) ≤ 2 := by
      apply le_trans _ (sum_exp_neg_le_two (J+1))
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega))
        (fun j _ _ => (Real.exp_pos _).le)
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 J, Real.exp (-(j:ℝ))*(M/Real.sqrt ℓ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hjbound j) (Real.exp_pos _).le)
      _ = (∑ j ∈ Finset.Icc 1 J, Real.exp (-(j:ℝ)))*(M/Real.sqrt ℓ) := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeo (div_nonneg hM hs.le)
  have hc := C.band_contraction hθ.2 J hJ
  have ha := C.bandA_nonneg hθ.2 ℓ
  have hi := C.inactiveBand_nonneg hθ.2 ℓ
  have hc0 := (Real.exp_pos (-4)).le
  have hlow := mul_le_mul_of_nonneg_right (show (3/4:ℝ) ≤ 1-Real.exp (-4) by linarith [exp_neg_four_le_quarter]) ha
  have hup1 := mul_le_mul_of_nonneg_left htail hc0
  have hup2 := mul_le_mul_of_nonneg_right exp_neg_four_le_quarter (show 0 ≤ 2*(M/Real.sqrt ℓ) by positivity)
  have hp : D.startBand 2 ℓ ≤ (2/3)*(M/Real.sqrt ℓ)+(8/3)*((D.sharpAverageConstant*D.sharpK)/Real.sqrt ℓ) := by
    rw [C.profile_split hθ.2]
    linarith
  have hh := mul_le_mul_of_nonneg_left hp hs.le
  have heq : Real.sqrt ℓ*((2/3)*(M/Real.sqrt ℓ)+(8/3)*((D.sharpAverageConstant*D.sharpK)/Real.sqrt ℓ)) =
      (2/3)*M+(8/3)*(D.sharpAverageConstant*D.sharpK) := by field_simp
  exact hh.trans_eq heq

/-- A prefactor independent of time, dimension, density and level. -/
noncomputable def sharpBandConstant : ℝ := max 8 (8*D.sharpAverageConstant)

lemma sharpBandConstant_pos : 0 < D.sharpBandConstant :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- Manuscript Lemma 2 with its original sharp κ dependence. -/
theorem fixed_band_sharp (ℓ : ℝ) (hℓ : 2 < ℓ) :
    D.startBand 2 ℓ ≤ D.sharpBandConstant*D.sharpK/Real.sqrt ℓ := by
  let g : ℝ → ℝ := fun r => Real.sqrt r*D.startBand 2 r
  have hgn (r : ℝ) : 0 ≤ g r := mul_nonneg (Real.sqrt_nonneg _) (D.startBand_nonneg le_rfl r)
  have hne : (g '' Set.Ici (64*D.sharpK^2)).Nonempty := ⟨g (64*D.sharpK^2),64*D.sharpK^2,Set.self_mem_Ici,rfl⟩
  obtain ⟨B,hB⟩ := D.exists_profile_vanish
  have hbdd : BddAbove (g '' Set.Ici (64*D.sharpK^2)) := by
    refine ⟨Real.sqrt B+1,?_⟩
    rintro _ ⟨r,hr,rfl⟩
    dsimp [g]
    by_cases hBr : B ≤ r
    · rw [hB r hBr,mul_zero]; positivity
    · have hp := D.startBand_le_one (θ := 2) le_rfl r
      have hn := D.startBand_nonneg (θ := 2) le_rfl r
      have hs := Real.sqrt_le_sqrt (lt_of_not_ge hBr).le
      nlinarith [Real.sqrt_nonneg r]
  let M := sSup (g '' Set.Ici (64*D.sharpK^2))
  have hMb (r : ℝ) (hr : 64*D.sharpK^2 ≤ r) : g r ≤ M := le_csSup hbdd ⟨r,hr,rfl⟩
  have hM : 0 ≤ M := (hgn (64*D.sharpK^2)).trans (hMb (64*D.sharpK^2) le_rfl)
  have hrec : M ≤ (2/3)*M+(8/3)*(D.sharpAverageConstant*D.sharpK) := by
    apply csSup_le hne
    rintro _ ⟨r,hr,rfl⟩
    change 64*D.sharpK^2 ≤ r at hr
    have hK1 := D.sharpK_ge_one
    have hKsq : 1 ≤ D.sharpK^2 := one_le_pow₀ hK1
    exact D.band_step_sharp (by nlinarith) (by nlinarith) hM (fun u hu => hMb u (hr.trans hu))
  have hMle : M ≤ 8*(D.sharpAverageConstant*D.sharpK) := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr (by linarith)
  apply (le_div_iff₀ hs).mpr
  by_cases hl64 : 64*D.sharpK^2 ≤ ℓ
  · have hh := hMb ℓ hl64
    dsimp [g] at hh
    have hc : 8*(D.sharpAverageConstant*D.sharpK) ≤ D.sharpBandConstant*D.sharpK := by
      have hh := mul_le_mul_of_nonneg_right (le_max_right (8:ℝ) (8*D.sharpAverageConstant)) D.sharpK_pos.le
      simpa only [sharpBandConstant, mul_assoc] using hh
    nlinarith
  · have hp := D.startBand_le_one (θ := 2) le_rfl ℓ
    have hsq := Real.sq_sqrt (show 0 ≤ ℓ by linarith)
    have hc : 8*D.sharpK ≤ D.sharpBandConstant*D.sharpK :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) D.sharpK_pos.le
    have hroot : Real.sqrt ℓ ≤ 8*D.sharpK := by
      apply Sharp.sqrt_le_of_le_sq (by have := D.sharpK_pos; positivity)
      nlinarith
    nlinarith [Real.sqrt_nonneg ℓ]

lemma sharpK_eq_manuscript : D.sharpK =
    D.κ^2*Real.sqrt (Real.log D.κ/(D.κ-1)) := by
  unfold sharpK Λ
  rw [show D.κ^3*(D.κ*Real.log D.κ/(D.κ-1)) =
    (D.κ^2)^2*(Real.log D.κ/(D.κ-1)) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]

/-- Exact displayed form of Lemma 2, including its κ dependence. -/
theorem fixed_band_sharp_explicit (ℓ : ℝ) (hℓ : 2 < ℓ) :
    D.startBand 2 ℓ ≤ D.sharpBandConstant *
      (D.κ^2*Real.sqrt (Real.log D.κ/(D.κ-1)))/Real.sqrt ℓ := by
  simpa only [D.sharpK_eq_manuscript] using D.fixed_band_sharp ℓ hℓ

end TailBound.RefreshData
