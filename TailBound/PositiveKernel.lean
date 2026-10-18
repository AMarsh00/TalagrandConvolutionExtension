import TailBound.Core

/-! The deterministic reduction, with the minorization constant constructed.
This module states the reduction with an explicit refresh hypothesis.
`RefreshTail.lean` proves that hypothesis and the unconditional positive-kernel result.
-/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma positive_kernel_minorization (π : α → ℝ) (K : α → α → ℝ)
    (hπ : ∀ x, 0 < π x) (hmass : ∑ x, π x = 1)
    (hK : ∀ x y, 0 < K x y) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x y, ε * π y ≤ K x y := by
  have hne : (Finset.univ : Finset α) ≠ ∅ := by
    intro he
    simp [he] at hmass
  obtain ⟨x₀, _⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨p, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (α × α)) (fun p => K p.1 p.2 / π p.2)
    ⟨(x₀,x₀), Finset.mem_univ _⟩
  let d := K p.1 p.2 / π p.2
  have hd : 0 < d := div_pos (hK p.1 p.2) (hπ p.2)
  refine ⟨min (1/2) (d/2), lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro x y
  apply (le_div_iff₀ (hπ y)).mp
  calc min (1/2) (d/2) ≤ d/2 := min_le_right _ _
    _ ≤ d := by linarith
    _ ≤ K x y / π y := hmin (x,y) (Finset.mem_univ _)

/-- All strictly positive stationary kernels reduce to refresh. No condition
is placed on the dimension, and no embeddability of the residual is needed.
`hrefresh` is discharged by `refresh_tail` in `RefreshTail.lean`. -/
theorem positive_kernel_from_refresh (π : α → ℝ) (K : α → α → ℝ)
    (hπ : ∀ x, 0 < π x) (hmass : ∑ x, π x = 1)
    (hK : ∀ x y, 0 < K x y) (hrows : ∀ x, ∑ y, K x y = 1)
    (hstat : Stationary π K)
    (hrefresh : ∀ ε : ℝ, 0 < ε → ε < 1 → DimensionFreeTail π (refresh π ε)) :
    DimensionFreeTail π K := by
  obtain ⟨ε, hε0, hε1, hminor⟩ := positive_kernel_minorization π K hπ hmass hK
  exact refresh_to_kernel π K ε hmass hrows hstat hε1 hminor (hrefresh ε hε0 hε1)

end TailBound
