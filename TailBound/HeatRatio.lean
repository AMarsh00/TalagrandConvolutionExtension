import TailBound.Core

/-! The corrected replacement-coordinate estimate, Lemma 17, p. 38.
`a` is the retention probability exp(-(T-t)); `A` is exp(-τ).
Thus the relevant hypothesis is `a ≤ A`, or `T-t ≥ τ`.
-/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma act_pos_of_pos_kernel (K : α → α → ℝ) (f : α → ℝ)
    (hK : ∀ x y, 0 < K x y) (hf : ∀ y, 0 ≤ f y)
    (hfpos : ∃ y, 0 < f y) (x : α) : 0 < act K f x := by
  obtain ⟨y, hy⟩ := hfpos
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg (hK x z).le (hf z)
  · exact ⟨y, Finset.mem_univ y, mul_pos (hK x y) hy⟩

lemma tensorKernel_update (K : α → α → ℝ) (n : ℕ)
    (x y : Fin n → α) (i : Fin n) (g : α) :
    tensorKernel K n (Function.update x i g) y =
      K g (y i) * ∏ j ∈ Finset.univ.erase i, K (x j) (y j) := by
  unfold tensorKernel
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma tensorKernel_row (K : α → α → ℝ) (n : ℕ)
    (x y : Fin n → α) (i : Fin n) :
    tensorKernel K n x y =
      K (x i) (y i) * ∏ j ∈ Finset.univ.erase i, K (x j) (y j) := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

lemma tensorKernel_update_le (K : α → α → ℝ) (κ : ℝ)
    (hK : ∀ x y, 0 ≤ K x y)
    (hratio : ∀ x g u, K g u ≤ κ * K x u)
    (n : ℕ) (x y : Fin n → α) (i : Fin n) (g : α) :
    tensorKernel K n (Function.update x i g) y ≤ κ * tensorKernel K n x y := by
  rw [tensorKernel_update, tensorKernel_row K n x y i, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hratio (x i) g (y i))
    (Finset.prod_nonneg fun j _ => hK (x j) (y j))

lemma tensorAct_update_le (K : α → α → ℝ) (κ : ℝ)
    (hK : ∀ x y, 0 ≤ K x y)
    (hratio : ∀ x g u, K g u ≤ κ * K x u)
    (n : ℕ) (f : (Fin n → α) → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : Fin n → α) (i : Fin n) (g : α) :
    act (tensorKernel K n) f (Function.update x i g) ≤
      κ * act (tensorKernel K n) f x := by
  unfold act
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (tensorKernel_update_le K κ hK hratio n x y i g) (hf y)

lemma refresh_pos (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (x y : α) :
    0 < refresh π (1 - a) x y := by
  have h : 0 ≤ a * (if x = y then (1 : ℝ) else 0) := by positivity
  have hp := mul_pos (sub_pos.mpr ha1) (hπ y)
  dsimp [refresh]
  nlinarith

/-- A uniform single-coordinate bound at all remaining times at least τ. -/
theorem refresh_coordinate_bound (π : α → ℝ) (m M A a : ℝ)
    (hm : 0 < m) (hmin : ∀ u, m ≤ π u) (hmax : ∀ u, π u ≤ M)
    (ha : 0 ≤ a) (haA : a ≤ A) (hA : A < 1) (x g u : α) :
    refresh π (1 - a) g u ≤
      ((A + (1 - A) * M) / ((1 - A) * m)) * refresh π (1 - a) x u := by
  have ha1 : a < 1 := haA.trans_lt hA
  have hapos : 0 ≤ A := ha.trans haA
  have hMpos : 0 < M := hm.trans_le ((hmin u).trans (hmax u))
  have hd : 0 < (1 - A) * m := mul_pos (sub_pos.mpr hA) hm
  have hn : 0 ≤ A + (1 - A) * M :=
    add_nonneg hapos (mul_nonneg (by linarith) hMpos.le)
  have hlow : (1 - a) * m ≤ refresh π (1 - a) x u := by
    have hh := mul_le_mul_of_nonneg_left (hmin u) (by linarith : 0 ≤ 1 - a)
    have hi : 0 ≤ a * (if x = u then (1 : ℝ) else 0) := by positivity
    dsimp [refresh]
    nlinarith
  have hupp : refresh π (1 - a) g u ≤ a + (1 - a) * M := by
    have hh := mul_le_mul_of_nonneg_left (hmax u) (by linarith : 0 ≤ 1 - a)
    have hi : a * (if g = u then (1 : ℝ) else 0) ≤ a := by split_ifs <;> nlinarith
    dsimp [refresh]
    nlinarith
  have hmon : ((1 - A) * m) * (a + (1 - a) * M) ≤
      (A + (1 - A) * M) * ((1 - a) * m) := by
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr haA)]
  have hb := mul_le_mul_of_nonneg_left hlow hn
  have hu := mul_le_mul_of_nonneg_left hupp hd.le
  have hr : refresh π (1 - a) g u * ((1 - A) * m) ≤
      (A + (1 - A) * M) * refresh π (1 - a) x u := by nlinarith
  simpa only [div_mul_eq_mul_div] using (le_div_iff₀ hd).mpr hr

/-- Lemma 17 with the corrected time condition and reverse replacement.
The same κ works in every dimension and for every nonzero nonnegative f. -/
theorem heat_replacement_ratio (π : α → ℝ) (m M A a : ℝ)
    (hm : 0 < m) (hmin : ∀ u, m ≤ π u) (hmax : ∀ u, π u ≤ M)
    (ha : 0 ≤ a) (haA : a ≤ A) (hA : A < 1)
    (n : ℕ) (f : (Fin n → α) → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hfpos : ∃ y, 0 < f y) (x : Fin n → α) (i : Fin n) (g : α) :
    let κ := (A + (1 - A) * M) / ((1 - A) * m)
    let p := act (tensorKernel (refresh π (1 - a)) n) f
    κ⁻¹ ≤ p (Function.update x i g) / p x ∧
      p (Function.update x i g) / p x ≤ κ := by
  dsimp only
  let K := refresh π (1 - a)
  let κ := (A + (1 - A) * M) / ((1 - A) * m)
  let p := act (tensorKernel K n) f
  have hK : ∀ x y, 0 < K x y :=
    refresh_pos π (fun u => hm.trans_le (hmin u)) a ha (haA.trans_lt hA)
  have hratio : ∀ x g u, K g u ≤ κ * K x u :=
    refresh_coordinate_bound π m M A a hm hmin hmax ha haA hA
  have hp : ∀ z, 0 < p z := act_pos_of_pos_kernel _ f
    (fun z y => Finset.prod_pos fun j _ => hK (z j) (y j)) hf hfpos
  have hupper := tensorAct_update_le K κ (fun z y => (hK z y).le)
    hratio n f hf x i g
  have hlower := tensorAct_update_le K κ (fun z y => (hK z y).le)
    hratio n f hf (Function.update x i g) i (x i)
  have hrestore : Function.update (Function.update x i g) i (x i) = x := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [hrestore] at hlower
  have hk : 0 < κ := by
    have hpos := hK (x i) (x i)
    have h := hratio (x i) (x i) (x i)
    by_contra! hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg hn hpos.le
    linarith
  change κ⁻¹ ≤ p (Function.update x i g) / p x ∧
    p (Function.update x i g) / p x ≤ κ
  constructor
  · apply (le_div_iff₀ (hp x)).mpr
    apply (inv_mul_le_iff₀ hk).mpr
    exact hlower
  · exact (div_le_iff₀ (hp x)).mpr hupper

/-- Lemma 17 in the manuscript's time variables. -/
theorem heat_replacement_ratio_time (π : α → ℝ) (m M τ T t : ℝ)
    (hm : 0 < m) (hmin : ∀ u, m ≤ π u) (hmax : ∀ u, π u ≤ M)
    (hτ : 0 < τ) (ht : τ ≤ T - t)
    (n : ℕ) (f : (Fin n → α) → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hfpos : ∃ y, 0 < f y) (x : Fin n → α) (i : Fin n) (g : α) :
    let κ := (Real.exp (-τ) + (1 - Real.exp (-τ)) * M) /
      ((1 - Real.exp (-τ)) * m)
    let p := act (tensorKernel (refresh π (1 - Real.exp (-(T - t)))) n) f
    κ⁻¹ ≤ p (Function.update x i g) / p x ∧
      p (Function.update x i g) / p x ≤ κ := by
  apply heat_replacement_ratio π m M (Real.exp (-τ)) (Real.exp (-(T - t)))
    hm hmin hmax (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_lt_one_iff.mpr (by linarith)) n f hf hfpos x i g

end TailBound
