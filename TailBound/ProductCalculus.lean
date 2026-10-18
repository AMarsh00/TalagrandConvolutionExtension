import TailBound.Heat

/-! Reversibility and integration by parts for coordinate resampling.
The reverse of `x ↦ x[i := a]` restores the old coordinate `x i`.
-/

open scoped BigOperators
namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

lemma mean_neg {β : Type*} [Fintype β] (μ f : β → ℝ) :
    mean μ (fun x => -f x) = -mean μ f := by
  simp [mean, Finset.sum_neg_distrib]

lemma resampling_reversal (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (i : Fin n) (H : (Fin n → α) → α → ℝ) :
    mean (tensorWeight π n) (fun x => mean π (H x)) =
      mean (tensorWeight π n) (fun x => mean π (fun a => H (Function.update x i a) (x i))) := by
  rw [← mean_tensor_resample π hπ1 n i (fun x => mean π (H x)),
    ← mean_tensor_resample π hπ1 n i
      (fun x => mean π (fun a => H (Function.update x i a) (x i)))]
  simp only [Function.update_idem, Function.update_self]
  congr 1
  funext x
  exact mean_comm π π (fun a b => H (Function.update x i a) b)

lemma generator_weighted_form (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f : (Fin n → α) → ℝ) (x : Fin n → α) :
    refreshGenerator π f x = ∑ i, mean π (fun a => f (Function.update x i a)-f x) := by
  simp only [refreshGenerator, mean_sub, mean_const π hπ1]

/-- Discrete integration by parts, with the positive Dirichlet sign and
the necessary factor one half. -/
theorem product_integration_by_parts (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (f g : (Fin n → α) → ℝ) :
    -mean (tensorWeight π n) (fun x => g x * refreshGenerator π f x) =
      (1/2:ℝ) * mean (tensorWeight π n) (fun x => ∑ i, mean π (fun a =>
        (g (Function.update x i a)-g x) * (f (Function.update x i a)-f x))) := by
  have hrev (i : Fin n) :
      mean (tensorWeight π n) (fun x => mean π (fun a =>
        g (Function.update x i a)*(f x-f (Function.update x i a)))) =
      mean (tensorWeight π n) (fun x => mean π (fun a =>
        g x*(f (Function.update x i a)-f x))) := by
    have hr := resampling_reversal π hπ1 i
      (fun x a => g x*(f (Function.update x i a)-f x))
    simpa only [Function.update_idem, Function.update_eq_self] using hr.symm
  have he (i : Fin n) :
      mean (tensorWeight π n) (fun x => mean π (fun a =>
        (g (Function.update x i a)-g x) * (f (Function.update x i a)-f x))) =
      -2 * mean (tensorWeight π n) (fun x => mean π (fun a =>
        g x*(f (Function.update x i a)-f x))) := by
    have hi (x : Fin n → α) (a : α) :
        (g (Function.update x i a)-g x) * (f (Function.update x i a)-f x) =
        -(g (Function.update x i a)*(f x-f (Function.update x i a))) -
          g x*(f (Function.update x i a)-f x) := by ring
    simp_rw [hi, mean_sub, mean_neg]
    rw [hrev]
    ring
  have hL : mean (tensorWeight π n) (fun x => g x * refreshGenerator π f x) =
      ∑ i, mean (tensorWeight π n) (fun x => mean π
        (fun a => g x*(f (Function.update x i a)-f x))) := by
    simp only [generator_weighted_form π hπ1, Finset.mul_sum, mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext x
    exact (mean_smul π _ (g x)).symm
  rw [hL, mean_sum]
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

lemma threshold_closed_pair (u x y : ℝ) (hx : x ≠ u) (hy : y ≠ u) :
    ((if u < y then (1:ℝ) else 0)-(if u < x then 1 else 0))*(y-x) =
      |y-x| * (if min x y ≤ u ∧ u ≤ max x y then 1 else 0) := by
  by_cases hxu : u<x
  · by_cases hyu : u<y
    · have hn : ¬ (min x y ≤ u ∧ u ≤ max x y) := fun h => (lt_min hxu hyu).not_ge h.1
      simp only [if_pos hxu, if_pos hyu, if_neg hn, sub_self, zero_mul, mul_zero]
    · have hyu' : y<u := lt_of_le_of_ne (le_of_not_gt hyu) hy
      simp [hxu, hyu, min_eq_right (by linarith : y≤x),
        max_eq_left (by linarith : y≤x), hyu'.le, hxu.le,
        abs_of_nonpos (by linarith : y-x≤0)]
  · by_cases hyu : u<y
    · have hxu' : x<u := lt_of_le_of_ne (le_of_not_gt hxu) hx
      simp [hxu, hyu, min_eq_left (by linarith : x≤y),
        max_eq_right (by linarith : x≤y), hxu'.le, hyu.le,
        abs_of_nonneg (by linarith : 0≤y-x)]
    · have hxu' : x<u := lt_of_le_of_ne (le_of_not_gt hxu) hx
      have hyu' : y<u := lt_of_le_of_ne (le_of_not_gt hyu) hy
      have hn : ¬ (min x y ≤ u ∧ u ≤ max x y) := fun h => (max_lt hxu' hyu').not_ge h.2
      simp only [if_neg hxu, if_neg hyu, if_neg hn, sub_self, zero_mul, mul_zero]

end TailBound
