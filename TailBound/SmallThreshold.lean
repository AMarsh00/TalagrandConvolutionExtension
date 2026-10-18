import TailBound.Core

/-! The missing small-threshold case in the proof of Lemma 1, p. 3. -/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem finite_markov_bound (π p : α → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hp : ∀ x, 0 ≤ p x) (η : ℝ) (hη : 0 < η) :
    eventMass π (fun x => η < p x) ≤ mean π p / η := by
  classical
  apply (le_div_iff₀ hη).mpr
  unfold eventMass mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : η < p x
  · simp only [hx, if_true]
    exact mul_le_mul_of_nonneg_left hx.le (hπ x)
  · simp only [hx, if_false, zero_mul]
    exact mul_nonneg (hπ x) (hp x)

/-- For `1 < η ≤ exp 2`, ordinary Markov supplies the required estimate.
The band estimate in Lemma 2 is only needed for `log η > 2`. -/
theorem small_threshold_tail (π p : α → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hp : ∀ x, 0 ≤ p x) (hm : mean π p = 1)
    (η : ℝ) (hη : 1 < η) (hlog : Real.log η ≤ 2) :
    eventMass π (fun x => η < p x) ≤
      Real.sqrt 2 / (η * Real.sqrt (Real.log η)) := by
  have hηpos : 0 < η := by linarith
  have hs : 0 < Real.sqrt (Real.log η) := Real.sqrt_pos.mpr (Real.log_pos hη)
  have h := finite_markov_bound π p hπ hp η hηpos
  rw [hm] at h
  apply h.trans
  apply (div_le_div_iff₀ hηpos (mul_pos hηpos hs)).mpr
  have hsq := Real.sqrt_le_sqrt hlog
  nlinarith [mul_le_mul_of_nonneg_left hsq hηpos.le]

end TailBound
