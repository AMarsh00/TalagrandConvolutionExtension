import TailBound.LevelOne

/-!
# Bridge Energy

Conditional bridge calculations on a finite alphabet.

This file works with the explicit bridge law, including the two different
horizontal increments. Coordinate replacement is never treated as a flip.
-/

open scoped BigOperators

namespace TailBound

variable {α ι : Type*} [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq α] in
lemma weighted_cauchy (μ d v : α → ℝ) (hμ : ∀ u, 0 < μ u) :
    (∑ u, d u * v u) ^ 2 ≤ (∑ u, (d u) ^ 2 / μ u) *
      (∑ u, μ u * (v u) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro u _; exact div_nonneg (sq_nonneg _) (hμ u).le
  · intro u _; exact mul_nonneg (hμ u).le (sq_nonneg _)
  · intro u _
    field_simp [(hμ u).ne']

omit [Fintype α] [DecidableEq α] in
lemma productWeight_update (μ : ι → α → ℝ) (ν : α → ℝ)
    (i : ι) (x : ι → α) (hi : μ i (x i) ≠ 0) :
    productWeight (Function.update μ i ν) x =
      productWeight μ x * (ν (x i) / μ i (x i)) := by
  unfold productWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, Function.update μ i ν j (x j)) =
      ∏ j ∈ Finset.univ.erase i, μ j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [he]
  field_simp

lemma mean_product_update (μ : ι → α → ℝ) (ν : α → ℝ)
    (i : ι) (hμ : ∀ a, μ i a ≠ 0) (f : (ι → α) → ℝ) :
    mean (productWeight (Function.update μ i ν)) f =
      ∑ a, ν a * coordinateAverage μ f i a := by
  have he : mean (productWeight (Function.update μ i ν)) f =
      mean (productWeight μ) (fun x => f x * (ν (x i) / μ i (x i))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [productWeight_update μ ν i x (hμ (x i))]
    ring
  rw [he, coordinateAverage_test μ f i (fun a => ν a / μ i a)]
  apply Finset.sum_congr rfl
  intro a _
  field_simp [hμ a]

/-- Subtracting the mean is justified by equality of the two marginal masses. -/
lemma mean_product_difference (μ : ι → α → ℝ) (ν₁ ν₂ : α → ℝ)
    (i : ι) (hμ : ∀ a, μ i a ≠ 0)
    (hmass : ∑ a, ν₁ a = ∑ a, ν₂ a)
    (f : (ι → α) → ℝ) (c : ℝ) :
    mean (productWeight (Function.update μ i ν₁)) f -
        mean (productWeight (Function.update μ i ν₂)) f =
      ∑ a, (ν₁ a - ν₂ a) * (coordinateAverage μ f i a - c) := by
  rw [mean_product_update μ ν₁ i hμ,
    mean_product_update μ ν₂ i hμ]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hmass]
  ring

omit [Fintype α] in
lemma bridgeH_pos (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (z x : α) :
    0 < bridgeH π a z x := by
  unfold bridgeH
  have h := mul_pos (sub_pos.mpr ha1) (hπ z)
  split_ifs <;> nlinarith

omit [Fintype α] in
lemma bridgeLaw_pos (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (z x y u : α) :
    0 < bridgeLaw π a r z x y u := by
  have hra0 := mul_nonneg hr0 ha0
  have hra1 : r * a < 1 := by nlinarith
  have hxu := bridgeH_pos π hπ ha0 ha1 z x
  have huu := bridgeH_pos π hπ ha0 ha1 z u
  unfold bridgeLaw
  apply div_pos _ (bridgeH_pos π hπ hra0 hra1 z x)
  have h := mul_pos (mul_pos (sub_pos.mpr hr1) (hπ u)) huu
  split_ifs <;> nlinarith

omit [Fintype α] in
/-- Difference of the one-coordinate bridge laws. -/
lemma bridgeLaw_difference (π : α → ℝ) (a r : ℝ)
    (z x g y u : α)
    (hx : bridgeH π (r * a) z x ≠ 0)
    (hg : bridgeH π (r * a) z g ≠ 0) :
    bridgeLaw π a r z x y u - bridgeLaw π a r z g y u =
      (1 / bridgeH π (r * a) z x - 1 / bridgeH π (r * a) z g) *
        (1 - r) * (π u * bridgeH π a z u - π z * (if u = y then 1 else 0)) := by
  have hxi := bridgeH_interpolation π a r z x
  have hgi := bridgeH_interpolation π a r z g
  unfold bridgeLaw
  field_simp
  rw [hxi, hgi]
  ring

variable {β : Type*} [Fintype β]

/-- Dimension-free Cauchy--Schwarz and Bessel estimate.
The two marginal laws can be different from the reference law in the changed
coordinate; all other coordinates retain the reference law. -/
theorem product_perturbation_energy
    (μ : ι → α → ℝ) (hμ : ∀ i a, 0 < μ i a)
    (hμmass : ∀ i, ∑ a, μ i a = 1)
    (ν₁ ν₂ : ι → β → α → ℝ)
    (hmass : ∀ i b, ∑ a, ν₁ i b a = ∑ a, ν₂ i b a)
    (w : ι → β → ℝ) (hw : ∀ i b, 0 ≤ w i b)
    (f : (ι → α) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hcoef : ∀ i, (∑ b, w i b * ∑ a, (ν₁ i b a - ν₂ i b a) ^ 2 / μ i a) ≤ B) :
    (∑ i, ∑ b, w i b *
      (mean (productWeight (Function.update μ i (ν₁ i b))) f -
        mean (productWeight (Function.update μ i (ν₂ i b))) f) ^ 2) ≤ B / 4 := by
  let m := mean (productWeight μ) f
  let V := fun i => mean (μ i) (fun a => (coordinateAverage μ f i a - m) ^ 2)
  have hV : ∀ i, 0 ≤ V i := fun i =>
    Finset.sum_nonneg fun a _ => mul_nonneg (hμ i a).le (sq_nonneg _)
  have he (i : ι) (b : β) :
      (mean (productWeight (Function.update μ i (ν₁ i b))) f -
        mean (productWeight (Function.update μ i (ν₂ i b))) f) ^ 2 ≤
      (∑ a, (ν₁ i b a - ν₂ i b a) ^ 2 / μ i a) * V i := by
    rw [mean_product_difference μ (ν₁ i b) (ν₂ i b) i
      (fun a => (hμ i a).ne') (hmass i b) f m]
    exact weighted_cauchy (μ i) (fun a => ν₁ i b a - ν₂ i b a)
      (fun a => coordinateAverage μ f i a - m) (hμ i)
  have hsum : (∑ i, V i) ≤ (1 / 4 : ℝ) := by
    have h := level_one_product_le_quarter μ (fun i a => (hμ i a).le) hμmass f hf
    exact h.1.trans h.2
  calc
    _ ≤ ∑ i, ∑ b, w i b * ((∑ a, (ν₁ i b a - ν₂ i b a) ^ 2 / μ i a) * V i) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (he i b) (hw i b)
    _ = ∑ i, (∑ b, w i b * ∑ a, (ν₁ i b a - ν₂ i b a) ^ 2 / μ i a) * V i := by
      simp only [← mul_assoc, ← Finset.sum_mul]
    _ ≤ ∑ i, B * V i := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcoef i) (hV i)
    _ = B * ∑ i, V i := (Finset.mul_sum _ _ _).symm
    _ ≤ B * (1 / 4) := mul_le_mul_of_nonneg_left hsum hB
    _ = B / 4 := by ring

noncomputable def bridgeMarginals (π : α → ℝ) (a r : ℝ)
    (z x y : ι → α) : ι → α → ℝ :=
  fun i => bridgeLaw π a r (z i) (x i) (y i)

noncomputable def bridgePayoff (π : α → ℝ) (a r : ℝ)
    (z : ι → α) (f : (ι → α) → ℝ) (x y : ι → α) : ℝ :=
  mean (productWeight (bridgeMarginals π a r z x y)) f

omit [Fintype α] [Fintype ι] in
lemma bridgeMarginals_update_x (π : α → ℝ) (a r : ℝ)
    (z x y : ι → α) (i : ι) (g : α) :
    bridgeMarginals π a r z (Function.update x i g) y =
      Function.update (bridgeMarginals π a r z x y) i
        (bridgeLaw π a r (z i) g (y i)) := by
  funext j u
  by_cases hj : j = i
  · subst j; simp [bridgeMarginals]
  · simp [bridgeMarginals, hj]

omit [Fintype α] [Fintype ι] in
lemma bridgeMarginals_update_y (π : α → ℝ) (a r : ℝ)
    (z x y : ι → α) (i : ι) (g : α) :
    bridgeMarginals π a r z x (Function.update y i g) =
      Function.update (bridgeMarginals π a r z x y) i
        (bridgeLaw π a r (z i) (x i) g) := by
  funext j u
  by_cases hj : j = i
  · subst j; simp [bridgeMarginals]
  · simp [bridgeMarginals, hj]

/-- Both horizontal differences use the conditional average for the same
reference product law, including the difference evaluated at the updated y. -/
theorem bridge_horizontal_differences (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (hmass : ∑ u, π u = 1) {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (z x y : ι → α) (i : ι) (g : α)
    (f : (ι → α) → ℝ) (c : ℝ) :
    let μ := bridgeMarginals π a r z x y
    dx (bridgePayoff π a r z f) i g x y =
      ∑ u, (bridgeLaw π a r (z i) g (y i) u - μ i u) *
        (coordinateAverage μ f i u - c) ∧
    dx (bridgePayoff π a r z f) i g x (Function.update y i g) =
      ∑ u, (bridgeLaw π a r (z i) g g u - bridgeLaw π a r (z i) (x i) g u) *
        (coordinateAverage μ f i u - c) := by
  let μ := bridgeMarginals π a r z x y
  have hp (u : α) : μ i u ≠ 0 :=
    (bridgeLaw_pos π hπ ha0 ha1 hr0 hr1 (z i) (x i) (y i) u).ne'
  have hra0 := mul_nonneg hr0 ha0
  have hra1 : r * a < 1 := by nlinarith
  have hm (v w : α) : ∑ u, bridgeLaw π a r (z i) v w u = 1 :=
    bridgeLaw_mass π hmass a r (z i) v w
      (bridgeH_pos π hπ hra0 hra1 (z i) v).ne'
  have hself : Function.update μ i (μ i) = μ := Function.update_eq_self i μ
  constructor
  · dsimp only [dx, bridgePayoff]
    rw [bridgeMarginals_update_x]
    change mean (productWeight (Function.update μ i _)) f - mean (productWeight μ) f = _
    have he := mean_product_difference μ (bridgeLaw π a r (z i) g (y i))
      (μ i) i hp (by change _ = ∑ u, bridgeLaw π a r (z i) (x i) (y i) u; rw [hm, hm]) f c
    rwa [hself] at he
  · dsimp only [dx, bridgePayoff]
    rw [bridgeMarginals_update_x, bridgeMarginals_update_y]
    simp only [Function.update_self, Function.update_idem]
    change mean (productWeight (Function.update μ i _)) f - mean (productWeight (Function.update μ i _)) f = _
    exact mean_product_difference μ _ _ i hp (by rw [hm, hm]) f c

end TailBound
