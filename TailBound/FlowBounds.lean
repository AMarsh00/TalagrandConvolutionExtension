import TailBound.PerturbationScalar

/-! Positivity and quadratic estimates for integration against the stopped law. -/
open scoped BigOperators
open MeasureTheory intervalIntegral
namespace TailBound

lemma quadratic_discriminant {S T J : ℝ} (hS : 0 ≤ S)
    (h : ∀ u : ℝ, 2*u*J ≤ u^2*S+T) : J^2 ≤ S*T := by
  rcases eq_or_lt_of_le hS with hs | hs
  · have hz : J = 0 := by
      by_contra hn
      have hh := h ((T+1)/(2*J))
      rw [← hs] at hh
      have he : 2*((T+1)/(2*J))*J = T+1 := by field_simp <;> ring
      rw [he,mul_zero,zero_add] at hh
      nlinarith
    simp [← hs,hz]
  · have hh := h (J/S)
    have he : 2*(J/S)*J-(J/S)^2*S = J^2/S := by field_simp; ring
    have hh' : J^2/S ≤ T := by linarith
    exact by nlinarith [(div_le_iff₀ hs).mp hh']

namespace RefreshData.StoppedCoupling
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

lemma integrate_mono (hθ : θ ≤ 2) {F G : ℝ → CoupledState α n → ℝ}
    (hF : C.CellContinuous F) (hG : C.CellContinuous G)
    (hFG : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      C.law k t s ≠ 0 → F t s ≤ G t s) : C.integrate F ≤ C.integrate G := by
  have hh := C.integrate_nonneg hθ (fun t s => G t s+(-1)*F t s)
    (fun k hk t ht s hs => by have he := hFG k hk t ht s hs; linarith)
  rw [C.integrate_add hG (fun k hk s => (hF k hk s).const_mul (-1)),C.integrate_smul] at hh
  linarith

lemma integrate_congr {F G : ℝ → CoupledState α n → ℝ}
    (hFG : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      F t s = G t s) : C.integrate F = C.integrate G := by
  apply Finset.sum_congr rfl
  intro k hk
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (C.grid.mono k (Finset.mem_range.mp hk))] at ht
  unfold pairing
  apply Finset.sum_congr rfl
  intro s _
  rw [hFG k (Finset.mem_range.mp hk) t ht s]

lemma integrate_young (hθ : θ ≤ 2) {F G H : ℝ → CoupledState α n → ℝ}
    (hF : C.CellContinuous F) (hG : C.CellContinuous G) (hH : C.CellContinuous H)
    (hFn : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      C.law k t s ≠ 0 → 0 ≤ F t s)
    (hy : ∀ u : ℝ, ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1)), ∀ s,
      C.law k t s ≠ 0 → 2*u*H t s ≤ u^2*F t s+G t s) :
    (C.integrate H)^2 ≤ C.integrate F*C.integrate G := by
  apply quadratic_discriminant (C.integrate_nonneg hθ F hFn)
  intro u
  have hh := C.integrate_mono hθ (fun k hk s => (hH k hk s).const_mul (2*u))
    (fun k hk s => ((hF k hk s).const_mul (u^2)).add (hG k hk s)) (hy u)
  simp only [Pi.add_apply] at hh
  rw [C.integrate_add (fun k hk s => (hF k hk s).const_mul (u^2)) hG,
    C.integrate_smul,C.integrate_smul] at hh
  exact hh

end RefreshData.StoppedCoupling
end TailBound
