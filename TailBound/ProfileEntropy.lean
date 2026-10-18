import TailBound.Entropy
import TalagrandConvConjecture.Analysis.Cutoff

/-! The entropy comparison at the start of Lemma 3, for arbitrary finite
probability weights. The localized density is nonnegative, not bounded by 1. -/

open scoped BigOperators
namespace TailBound
open Talagrand (cutoff cutoff_mem_Icc cutoff_eq_one)

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def bandMass (μ F : Ω → ℝ) (ℓ : ℝ) : ℝ :=
  mean μ (fun x => (Set.Ioc ℓ (ℓ+1)).indicator (fun _ => F x) (Real.log (F x)))

noncomputable def localizedDensity (F : Ω → ℝ) (ℓ : ℝ) (x : Ω) : ℝ :=
  F x * cutoff (Real.log (F x)-ℓ)^2

lemma bandMass_nonneg (μ F : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x)
    (ℓ : ℝ) : 0 ≤ bandMass μ F ℓ :=
  mean_nonneg hμ (fun x => Set.indicator_nonneg (fun _ _ => hF x) _)

lemma bandMass_le_mean (μ F : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x)
    (ℓ : ℝ) : bandMass μ F ℓ ≤ mean μ F := by
  apply mean_mono hμ
  intro x
  by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ+1)
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; exact hF x

/-- The localized entropy dominates the size-biased unit band. -/
theorem localized_entropy_lower (μ F : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) (hF : ∀ x, 0 < F x) (hF1 : mean μ F = 1)
    (ℓ : ℝ) (hℓ : 2 ≤ ℓ) :
    ℓ * bandMass μ F ℓ ≤ 2 * Talagrand.ent μ (localizedDensity F ℓ) := by
  classical
  let I : Ω → ℝ := fun x => (Set.Ioc ℓ (ℓ+1)).indicator (fun _ => (1:ℝ)) (Real.log (F x))
  let g := localizedDensity F ℓ
  let p := mean μ I
  let A := bandMass μ F ℓ
  let G := mean μ g
  have hI (x : Ω) : I x = 0 ∨ I x = 1 := by
    by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ+1)
    · right; exact Set.indicator_of_mem hx _
    · left; exact Set.indicator_of_notMem hx _
  have hIn (x : Ω) : 0 ≤ I x := by rcases hI x with h|h <;> rw [h] <;> norm_num
  have hgn (x : Ω) : 0 ≤ g x := mul_nonneg (hF x).le (sq_nonneg _)
  have hgle (x : Ω) : g x ≤ F x := by
    have hc := cutoff_mem_Icc (Real.log (F x)-ℓ)
    apply mul_le_of_le_one_right (hF x).le
    nlinarith [hc.1, hc.2]
  have hgI (x : Ω) : g x * I x =
      (Set.Ioc ℓ (ℓ+1)).indicator (fun _ => F x) (Real.log (F x)) := by
    by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ+1)
    · simp only [I, Set.indicator_of_mem hx, mul_one, g, localizedDensity]
      rw [cutoff_eq_one (by linarith [hx.1]) (by linarith [hx.2]), one_pow, mul_one]
    · simp only [I, Set.indicator_of_notMem hx, mul_zero]
  have hp0 : 0 ≤ p := mean_nonneg hμ hIn
  have hA0 : 0 ≤ A := bandMass_nonneg μ F hμ (fun x => (hF x).le) ℓ
  have hG0 : 0 ≤ G := mean_nonneg hμ hgn
  have hG1 : G ≤ 1 := (mean_mono hμ hgle).trans_eq hF1
  have hpA : Real.exp ℓ * p ≤ A := by
    rw [← mean_smul]
    apply mean_mono hμ
    intro x
    by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ+1)
    · simp only [I, Set.indicator_of_mem hx, mul_one]
      exact ((Real.lt_log_iff_exp_lt (hF x)).mp hx.1).le
    · simp only [I, Set.indicator_of_notMem hx, mul_zero, le_refl]
  have he1 : 1 ≤ Real.exp ℓ := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  let Q := 1 + (Real.exp ℓ - 1) * p
  have hQ1 : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  let c := Real.log Q
  have hc0 : 0 ≤ c := Real.log_nonneg hQ1
  have hcA : c ≤ A := by
    have hl := Real.log_le_sub_one_of_pos hQ
    dsimp [Q] at hl
    dsimp [c, Q]
    linarith
  have hexp (x : Ω) : Real.exp (ℓ * I x - c) = (1+(Real.exp ℓ-1)*I x)/Q := by
    rw [Real.exp_sub, Real.exp_log hQ]
    congr 1
    rcases hI x with h|h <;> rw [h] <;> simp
  have hφ : ∑ x, μ x * Real.exp (ℓ * I x - c) ≤ 1 := by
    simp_rw [hexp, ← mul_div_assoc]
    rw [← Finset.sum_div]
    change mean μ (fun x => 1+(Real.exp ℓ-1)*I x) / Q ≤ 1
    rw [mean_add, mean_const μ hμ1, mean_smul]
    exact le_of_eq (div_self hQ.ne')
  have hv := Talagrand.sum_mul_le_ent μ g (fun x => ℓ*I x-c) hμ hμ1 hgn hφ
  have he : (∑ x, μ x * (g x * (ℓ*I x-c))) = ℓ*A-c*G := by
    change mean μ (fun x => g x * (ℓ*I x-c)) = _
    have hr : (fun x => g x * (ℓ*I x-c)) = fun x => ℓ*(g x*I x)-c*g x := by
      funext x; ring
    rw [hr, mean_sub, mean_smul, mean_smul]
    simp_rw [hgI]
    rfl
  rw [he] at hv
  have hcG : c*G ≤ A := (mul_le_of_le_one_right hc0 hG1).trans hcA
  change ℓ*A ≤ 2*Talagrand.ent μ g
  nlinarith [mul_nonneg (sub_nonneg.mpr hℓ) hA0]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The first half of Lemma 3: the band is bounded by the localized gradient
energy, with a dimension-independent coefficient. -/
theorem band_le_localized_energy (π : α → ℝ) (m : ℝ) (hm : 0 < m)
    (hπ : ∀ a, m ≤ π a) (hπ1 : ∑ a, π a = 1) (n : ℕ)
    (F : (Fin n → α) → ℝ) (hF : ∀ x, 0 < F x)
    (hF1 : mean (tensorWeight π n) F = 1) (ℓ : ℝ) (hℓ : 2 ≤ ℓ) :
    ℓ * bandMass (tensorWeight π n) F ℓ ≤ (4/m) *
      mean (tensorWeight π n) (fun x => ∑ i, mean π (fun a =>
        (Real.sqrt (localizedDensity F ℓ (Function.update x i a)) -
          Real.sqrt (localizedDensity F ℓ x))^2)) := by
  have hπ0 : ∀ a, 0 ≤ π a := fun a => (hm.trans_le (hπ a)).le
  have h1 := localized_entropy_lower (tensorWeight π n) F
    (tensorWeight_nonneg hπ0 n) (tensorWeight_mass π hπ1 n) hF hF1 ℓ hℓ
  have h2 := product_LSI π m hm hπ hπ1 n (localizedDensity F ℓ)
    (fun x => mul_nonneg (hF x).le (sq_nonneg _))
  calc
    _ ≤ 2 * Talagrand.ent (tensorWeight π n) (localizedDensity F ℓ) := h1
    _ ≤ 2 * ((2/m) * _) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = _ := by ring

end TailBound
