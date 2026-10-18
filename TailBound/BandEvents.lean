import TailBound.LocalizedTV

/-! Event estimates for the manuscript's band contraction. -/
open scoped BigOperators
namespace TailBound
attribute [local instance] Classical.propDecidable

lemma eventMass_nonneg {S : Type*} [Fintype S] (μ : S → ℝ) (hμ : ∀ s, 0 ≤ μ s) (A : S → Prop) :
    0 ≤ eventMass μ A := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> simp_all

lemma eventMass_mono {S : Type*} [Fintype S] (μ : S → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    (A B : S → Prop) (h : ∀ s, A s → B s) : eventMass μ A ≤ eventMass μ B := by
  apply Finset.sum_le_sum
  intro s _
  by_cases ha : A s
  · simp [ha,h s ha]
  · simp [ha]; split_ifs <;> simp_all

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
namespace RefreshData.StoppedCoupling
variable {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def bandA (r : ℝ) : ℝ := eventMass C.terminal
  (fun s => 10 ≤ D.gap ℓ θ s.start ∧ r < D.logP 2 s.v ∧ D.logP 2 s.v ≤ r+1)
noncomputable def bandB (r : ℝ) : ℝ := eventMass C.terminal
  (fun s => 10 ≤ D.gap ℓ θ s.start ∧ r < D.logP 2 s.w ∧ D.logP 2 s.w ≤ r+1)
noncomputable def crossing (j : ℝ) : ℝ := eventMass C.terminal
  (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+j < D.logP 2 s.w ∧ D.logP 2 s.w ≤ ℓ+j+1 ∧ D.logP 2 s.v ≤ ℓ+1)

theorem crossing_bound (hθ : θ ≤ 2) (j : ℝ) : C.crossing j ≤ Real.exp (-4-j)*C.bandA (ℓ+j) := by
  let a : (Fin n → α) → ℝ := fun x => if 10 ≤ D.gap ℓ θ x then 1 else 0
  let φ : (Fin n → α) → ℝ := fun x => if ℓ+j < D.logP 2 x ∧ D.logP 2 x ≤ ℓ+j+1 then 1 else 0
  have hh := C.weighted_comparison hθ a φ (fun x => by dsimp [a]; split_ifs <;> norm_num)
    (fun x => by dsimp [φ]; split_ifs <;> norm_num)
  have he : (∑ s, C.terminal s*(a s.start*φ s.v)) = C.bandA (ℓ+j) := by
    apply Finset.sum_congr rfl
    intro s _
    dsimp [a,φ]
    by_cases hA : 10 ≤ D.gap ℓ θ s.start <;>
      by_cases hB : ℓ+j < D.logP 2 s.v ∧ D.logP 2 s.v ≤ ℓ+j+1 <;> simp [hA,hB]
  rw [he] at hh
  have hc : C.crossing j ≤ Real.exp (-4-j)*(∑ s, C.terminal s*(a s.start*D.comparisonWeight ℓ θ 2 s*φ s.w)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have hμ := C.terminal_nonneg hθ s
    have hM := (D.comparisonWeight_pos D.obs_le_horizon ℓ θ s).le
    by_cases hs : 10 ≤ D.gap ℓ θ s.start ∧ ℓ+j < D.logP 2 s.w ∧ D.logP 2 s.w ≤ ℓ+j+1 ∧ D.logP 2 s.v ≤ ℓ+1
    · have hcross := D.comparisonWeight_crossing s hs.1 hs.2.1 hs.2.2.2
      have hexp : Real.exp (-4-j)*Real.exp (4+j) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hbound : 1 ≤ Real.exp (-4-j)*D.comparisonWeight ℓ θ 2 s := by
        nlinarith [mul_le_mul_of_nonneg_left hcross.le (Real.exp_pos (-4-j)).le]
      simp only [if_pos hs]
      dsimp [a,φ]
      rw [if_pos hs.1,if_pos ⟨hs.2.1,hs.2.2.1⟩]
      simp only [one_mul,mul_one]
      nlinarith [mul_le_mul_of_nonneg_left hbound hμ]
    · simp only [if_neg hs]
      dsimp [a,φ]
      split_ifs <;> positivity
  exact hc.trans (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)

lemma event_difference_le_tv (A E : Set (Fin n → α)) :
    |eventMass C.terminal (fun s => s.start ∈ A ∧ s.w ∈ E)-
      eventMass C.terminal (fun s => s.start ∈ A ∧ s.v ∈ E)| ≤ C.eventTV A := by
  have hh := Finset.le_sup' (s := (Finset.univ : Finset (Set (Fin n → α))))
    (f := fun E => |(∑ s, C.terminal s*((if s.start ∈ A then 1 else 0)*(if s.w ∈ E then 1 else 0)))-
      (∑ s, C.terminal s*((if s.start ∈ A then 1 else 0)*(if s.v ∈ E then 1 else 0)))|)
    (Finset.mem_univ E)
  have he (f : CoupledState α n → (Fin n → α)) :
      eventMass C.terminal (fun s => s.start ∈ A ∧ f s ∈ E) =
        ∑ s, C.terminal s*((if s.start ∈ A then 1 else 0)*(if f s ∈ E then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases ha : s.start ∈ A <;> by_cases hb : f s ∈ E <;> simp [ha,hb]
  rw [he (fun s => s.w),he (fun s => s.v)]
  exact hh

end RefreshData.StoppedCoupling
end TailBound
