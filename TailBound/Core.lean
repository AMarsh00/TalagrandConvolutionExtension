import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Checked deterministic core of Tail_Bound_Idea (2).pdf

This core module proves the deterministic reduction. `refresh_to_kernel`
takes the refresh estimate as an explicit hypothesis, which is discharged in
`RefreshTail.lean`. The full continuous-time main theorem is proved in
`MainTheorem.lean`. See README.md for the representation and constants.
There are no admitted proofs or new axioms in this file.
-/

open scoped BigOperators

namespace TailBound

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def mean (π f : α → ℝ) : ℝ := ∑ x, π x * f x

noncomputable def act (K : α → α → ℝ) (f : α → ℝ) (x : α) : ℝ :=
  ∑ y, K x y * f y

def Stationary (π : α → ℝ) (K : α → α → ℝ) : Prop :=
  ∀ y, ∑ x, π x * K x y = π y

def Stochastic (K : α → α → ℝ) : Prop :=
  (∀ x y, 0 ≤ K x y) ∧ ∀ x, ∑ y, K x y = 1

noncomputable def comp (K R : α → α → ℝ) (x y : α) : ℝ :=
  ∑ z, K x z * R z y

lemma act_nonneg {K : α → α → ℝ} {f : α → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hf : ∀ x, 0 ≤ f x) (x : α) :
    0 ≤ act K f x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hK x y) (hf y)

lemma mean_act (π : α → ℝ) (K : α → α → ℝ)
    (hstat : Stationary π K) (f : α → ℝ) :
    mean π (act K f) = mean π f := by
  change ∀ y, ∑ x, π x * K x y = π y at hstat
  unfold mean act
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, hstat]

lemma act_comp (K R : α → α → ℝ) (f : α → ℝ) :
    act (comp K R) f = act K (act R f) := by
  funext x
  simp only [act, comp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-! ## Doeblin factorization, manuscript p. 2
Only Markov kernels are needed; no embeddability claim is made.
-/

noncomputable def residual (π : α → ℝ) (K : α → α → ℝ)
    (ε : ℝ) (x y : α) : ℝ := (K x y - ε * π y) / (1 - ε)

noncomputable def refresh (π : α → ℝ) (ε : ℝ) (x y : α) : ℝ :=
  (1 - ε) * (if x = y then 1 else 0) + ε * π y

lemma residual_stochastic (π : α → ℝ) (K : α → α → ℝ)
    (ε : ℝ) (hπ : ∑ y, π y = 1) (hK : ∀ x, ∑ y, K x y = 1)
    (hε : ε < 1) (hminor : ∀ x y, ε * π y ≤ K x y) :
    Stochastic (residual π K ε) := by
  constructor
  · intro x y
    exact div_nonneg (sub_nonneg.mpr (hminor x y)) (by linarith)
  · intro x
    simp only [residual, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hK, hπ, mul_one]
    exact div_self (by linarith)

lemma residual_stationary (π : α → ℝ) (K : α → α → ℝ)
    (ε : ℝ) (hπ : ∑ x, π x = 1) (hstat : Stationary π K) (hε : ε < 1) :
    Stationary π (residual π K ε) := by
  change ∀ y, ∑ x, π x * K x y = π y at hstat
  intro y
  simp only [residual, ← mul_div_assoc, mul_sub, ← Finset.sum_div,
    Finset.sum_sub_distrib]
  have h : ∑ x, π x * (ε * π y) = ε * π y := by
    rw [← Finset.sum_mul, hπ, one_mul]
  rw [h, hstat]
  apply (div_eq_iff (by linarith : 1 - ε ≠ 0)).mpr
  ring

lemma kernel_factorization (π : α → ℝ) (K : α → α → ℝ)
    (ε : ℝ) (hπ : ∑ x, π x = 1) (hstat : Stationary π K) (hε : ε < 1) :
    comp (refresh π ε) (residual π K ε) = K := by
  funext x y
  have hs := residual_stationary π K ε hπ hstat hε y
  calc
    comp (refresh π ε) (residual π K ε) x y =
        (1 - ε) * residual π K ε x y + ε * π y := by
      simp only [comp, refresh, add_mul, Finset.sum_add_distrib]
      rw [show (∑ z, (1 - ε) * (if x = z then 1 else 0) * residual π K ε z y) =
          (1 - ε) * residual π K ε x y by simp]
      simp_rw [mul_assoc ε, ← Finset.mul_sum]
      rw [hs]
    _ = K x y := by
      unfold residual
      field_simp [show 1 - ε ≠ 0 by linarith]
      ring

lemma refresh_detailed_balance (π : α → ℝ) (ε : ℝ) (x y : α) :
    π x * refresh π ε x y = π y * refresh π ε y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp [refresh, h, Ne.symm h]; ring

/-! ## Tensorization: the constant is unchanged for every dimension. -/

noncomputable def tensorWeight (π : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ :=
  ∏ i, π (x i)

noncomputable def tensorKernel (K : α → α → ℝ) (n : ℕ)
    (x y : Fin n → α) : ℝ := ∏ i, K (x i) (y i)

lemma tensor_nonneg {K : α → α → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (n : ℕ) (x y : Fin n → α) : 0 ≤ tensorKernel K n x y :=
  Finset.prod_nonneg fun i _ => hK (x i) (y i)

lemma tensor_mass (π : α → ℝ) (hπ : ∑ x, π x = 1) (n : ℕ) :
    ∑ x, tensorWeight π n x = 1 := by
  unfold tensorWeight
  rw [← Fintype.prod_sum]
  simp [hπ]

lemma tensor_stationary (π : α → ℝ) (K : α → α → ℝ)
    (hstat : Stationary π K) (n : ℕ) :
    Stationary (tensorWeight π n) (tensorKernel K n) := by
  intro y
  unfold tensorWeight tensorKernel
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => π u * K u (y i))]
  change ∀ y, ∑ x, π x * K x y = π y at hstat
  simp only [hstat]

lemma tensor_comp (K R : α → α → ℝ) (n : ℕ) :
    tensorKernel (comp K R) n = comp (tensorKernel K n) (tensorKernel R n) := by
  funext x y
  unfold tensorKernel comp
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

noncomputable def eventMass (π : α → ℝ) (E : α → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then π x else 0

def TailEstimate (π : α → ℝ) (K : α → α → ℝ) (C : ℝ) : Prop :=
  ∀ (f : α → ℝ), (∀ x, 0 ≤ f x) → ∀ η : ℝ, 1 < η →
    eventMass π (fun x => η * mean π f < act K f x) ≤ C / (η * Real.sqrt (Real.log η))

def DimensionFreeTail (π : α → ℝ) (K : α → α → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, TailEstimate (tensorWeight π n) (tensorKernel K n) C

lemma tail_transfer (π : α → ℝ) (Q R : α → α → ℝ) (C : ℝ)
    (hR : ∀ x y, 0 ≤ R x y) (hstat : Stationary π R)
    (hQ : TailEstimate π Q C) : TailEstimate π (comp Q R) C := by
  intro f hf η hη
  have h := hQ (act R f) (act_nonneg hR hf) η hη
  rw [mean_act π R hstat f] at h
  simpa only [act_comp] using h

/-- Theorem 1's deterministic reduction, CONDITIONAL on Lemma 1 for the
refresh kernel with parameter ε. This is not an unconditional main theorem. -/
theorem refresh_to_kernel (π : α → ℝ) (K : α → α → ℝ) (ε : ℝ)
    (hπ : ∑ x, π x = 1) (hK : ∀ x, ∑ y, K x y = 1)
    (hstat : Stationary π K) (hε : ε < 1)
    (hminor : ∀ x y, ε * π y ≤ K x y)
    (hrefresh : DimensionFreeTail π (refresh π ε)) :
    DimensionFreeTail π K := by
  obtain ⟨C, hC, hbound⟩ := hrefresh
  refine ⟨C, hC, ?_⟩
  intro n
  have hR := residual_stochastic π K ε hπ hK hε hminor
  have hs := residual_stationary π K ε hπ hstat hε
  have hfac := kernel_factorization π K ε hπ hstat hε
  have ht := tail_transfer (tensorWeight π n) (tensorKernel (refresh π ε) n)
    (tensorKernel (residual π K ε) n) C
    (tensor_nonneg hR.1 n) (tensor_stationary π _ hs n) (hbound n)
  rw [← tensor_comp, hfac] at ht
  exact ht

/-! ## Dirichlet-form sign, manuscript pp. 8-9 -/

theorem dirichlet_symmetrization (c : α → α → ℝ) (f : α → ℝ)
    (hsym : ∀ x y, c x y = c y x) :
    -(∑ x, ∑ y, c x y * f x * (f y - f x)) =
      (1 / 2 : ℝ) * ∑ x, ∑ y, c x y * (f y - f x)^2 := by
  have hs : (∑ x, ∑ y, c x y * f y * (f x - f y)) =
      ∑ x, ∑ y, c x y * f x * (f y - f x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsym y x]
  have he : (∑ x, ∑ y, c x y * (f y - f x)^2) =
      -(∑ x, ∑ y, c x y * f x * (f y - f x)) -
       (∑ x, ∑ y, c x y * f y * (f x - f y)) := by
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hs] at he
  linarith

theorem dirichlet_nonneg (c : α → α → ℝ) (f : α → ℝ)
    (hsym : ∀ x y, c x y = c y x) (hc : ∀ x y, 0 ≤ c x y) :
    0 ≤ -(∑ x, ∑ y, c x y * f x * (f y - f x)) := by
  rw [dirichlet_symmetrization c f hsym]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (hc x y) (sq_nonneg _)

/-! ## Replacing a coordinate is not an involution (pp. 23 and 38). -/

variable {ι : Type*} [DecidableEq ι]

def dx (F : (ι → α) → (ι → α) → ℝ) (i : ι) (g : α) (x y : ι → α) :=
  F (Function.update x i g) y - F x y
def dy (F : (ι → α) → (ι → α) → ℝ) (i : ι) (g : α) (x y : ι → α) :=
  F x (Function.update y i g) - F x y
def dxy (F : (ι → α) → (ι → α) → ℝ) (i : ι) (g : α) (x y : ι → α) :=
  F (Function.update x i g) (Function.update y i g) - F x y

lemma correct_vertical_identity (F : (ι → α) → (ι → α) → ℝ)
    (i : ι) (g : α) (x y : ι → α) :
    dy F i g x y = dxy F i g x y - dx F i g x (Function.update y i g) := by
  unfold dy dxy dx
  ring

lemma correct_shifted_vertical_identity (F : (ι → α) → (ι → α) → ℝ)
    (i : ι) (g : α) (x y : ι → α) :
    dy F i g (Function.update x i g) y = dxy F i g x y - dx F i g x y := by
  unfold dy dxy dx
  ring

lemma reciprocal_update_ratio (p : (ι → α) → ℝ) (x : ι → α) (i : ι) (g : α)
    (hx : p x ≠ 0) (hy : p (Function.update x i g) ≠ 0) :
    (p (Function.update x i g) / p x)⁻¹ =
      p (Function.update (Function.update x i g) i (x i)) / p (Function.update x i g) := by
  have hrestore : Function.update (Function.update x i g) i (x i) = x := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [hrestore, inv_div]

/-! ## Conditional bridge law: finite one-coordinate algebra, pp. 18-19. -/

noncomputable def bridgeH (π : α → ℝ) (a : ℝ) (z x : α) : ℝ :=
  a * (if x = z then 1 else 0) + (1 - a) * π z

noncomputable def bridgeLaw (π : α → ℝ) (a r : ℝ) (z x y u : α) : ℝ :=
  (r * bridgeH π a z x * (if u = y then 1 else 0) +
    (1 - r) * π u * bridgeH π a z u) / bridgeH π (r * a) z x

lemma bridgeH_interpolation (π : α → ℝ) (a r : ℝ) (z x : α) :
    bridgeH π (r * a) z x = r * bridgeH π a z x + (1 - r) * π z := by
  unfold bridgeH
  ring

lemma bridgeH_mean (π : α → ℝ) (hπ : ∑ u, π u = 1) (a : ℝ) (z : α) :
    ∑ u, π u * bridgeH π a z u = π z := by
  unfold bridgeH
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ u, π u * (a * (if u = z then 1 else 0))) = π z * a := by simp
  have h2 : (∑ u, π u * ((1 - a) * π z)) = (1 - a) * π z := by
    rw [← Finset.sum_mul, hπ, one_mul]
  rw [h1, h2]
  ring

theorem bridgeLaw_mass (π : α → ℝ) (hπ : ∑ u, π u = 1)
    (a r : ℝ) (z x y : α) (hd : bridgeH π (r * a) z x ≠ 0) :
    ∑ u, bridgeLaw π a r z x y u = 1 := by
  unfold bridgeLaw
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [mul_assoc (1 - r), ← Finset.mul_sum]
  rw [bridgeH_mean π hπ, ← bridgeH_interpolation, div_self hd]

lemma bridgeLaw_nonneg (π : α → ℝ) (hπ : ∀ u, 0 ≤ π u)
    (a r : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (z x y u : α) : 0 ≤ bridgeLaw π a r z x y u := by
  have hb (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (v : α) :
      0 ≤ bridgeH π b z v := by
    have hsub : 0 ≤ 1 - b := sub_nonneg.mpr hb1
    have hp := hπ z
    unfold bridgeH
    positivity
  unfold bridgeLaw
  apply div_nonneg
  · have hx := hb a ha.1 ha.2 x
    have hu := hb a ha.1 ha.2 u
    have hsub : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
    have hr0 := hr.1
    have hp := hπ u
    positivity
  · apply hb (r * a) (mul_nonneg hr.1 ha.1)
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) ha.1]

/-! ## Scalar steps in Lemmas 5 and 6 and the final recurrence -/

theorem stopped_score_rescaling (κ Λ R S : ℝ) (hκ : 1 < κ) (hR : 0 ≤ R)
    (hΛ : Λ = κ * Real.log κ / (κ - 1))
    (hS : S ≤ (2 * 5^2 * (κ - 1) / Real.log κ) *
      ((R + 1 + Real.log κ) / (R + 1)^2)) :
    S ≤ (2 * 5^2 * κ / Λ) / (R + 1) +
      (2 * 5^2 * (κ - 1)) / (R + 1)^2 := by
  have hk : κ ≠ 0 := by linarith
  have hkm : κ - 1 ≠ 0 := by linarith
  have hl : Real.log κ ≠ 0 := ne_of_gt (Real.log_pos hκ)
  have hr : R + 1 ≠ 0 := by linarith
  apply le_trans hS
  apply le_of_eq
  rw [hΛ]
  field_simp [hk, hkm, hl, hr]

theorem band_contraction_algebra (A B F D c : ℝ)
    (hB : B ≤ c * A + D + c * F) (hAB : A ≤ B + D) :
    (1 - c) * A ≤ c * F + 2 * D := by linarith

theorem absorb_recurrence (M a q : ℝ) (hq : q < 1)
    (h : M ≤ a + q * M) : M ≤ a / (1 - q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith

theorem band_exponent_before_stop (ell R alpha delta w v : ℝ) (j : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hdelta : delta * (R + 1) = alpha)
    (hw : ell + j < w) (hv : v ≤ ell + 1) :
    alpha + j - 1 < w - (1 - delta) * v - delta * (ell - R) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hv)]

theorem band_exponent_after_stop (ell R alpha delta w v z : ℝ) (j : ℝ)
    (hd0 : 0 ≤ delta) (hdelta : delta * (R + 1) = alpha)
    (hw : ell + j < w) (hv : v ≤ ell + 1) (hz : ell + 1 ≤ z) :
    alpha + j - 1 < w - v + delta * (z - (ell - R)) := by
  nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hz)]

/-! ## Variance <= 1/4, the second inequality in Lemma 18 -/

theorem variance_le_quarter (π f : α → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    mean π (fun x => (f x)^2) - (mean π f)^2 ≤ (1 / 4 : ℝ) := by
  have h : mean π (fun x => (f x)^2) ≤ mean π f := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hπ x)
    nlinarith [(hf x).1, (hf x).2]
  nlinarith [sq_nonneg (mean π f - 1 / 2)]

/-! ## The scalar drift cancellation behind Lemma 13 (p. 32).
This proves the AM-GM sign, not the stochastic supermartingale theorem.
-/

theorem switched_drift_nonpos (r δ : ℝ) (hr : 0 ≤ r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ - δ * r - 1 + r ^ δ ≤ 0 := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1 - δ by linarith) hδ0 (show (0 : ℝ) ≤ 1 by norm_num) hr
    (show (1 - δ) + δ = 1 by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at h
  linarith

/-! ## Machine-checked counterexamples to three printed lines.
These are counterexamples to intermediate statements, not to Theorem 1.
-/

theorem wrong_dirichlet_sign_counterexample :
    let c : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 4;
    let f : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1;
    -(∑ x, ∑ y, c x y * f x * (f y - f x)) ≠
      -(1 / 2 : ℝ) * ∑ x, ∑ y, c x y * (f y - f x)^2 := by
  norm_num [Fin.sum_univ_two]

theorem wrong_reciprocal_counterexample :
    let p : (Fin 1 → Fin 2) → ℝ := fun x => if x 0 = 0 then 1 else 2;
    let x : Fin 1 → Fin 2 := fun _ => 0;
    let y := Function.update x 0 1;
    (p y / p x)⁻¹ ≠ p (Function.update y 0 1) / p y := by
  norm_num

theorem wrong_increment_counterexample :
    let F : (Fin 1 → Fin 2) → (Fin 1 → Fin 2) → ℝ :=
      fun x _ => if x 0 = 0 then 0 else 1;
    let x : Fin 1 → Fin 2 := fun _ => 0;
    dxy F 0 1 x x + dx F 0 1 (Function.update x 0 1) x ≠ dy F 0 1 x x := by
  norm_num [dxy, dx, dy]

/-- For π=(1/3,2/3) and f=(1,0), Ent(f²)=log(3)/3 and
E(f,f)=2/9. The manuscript's inverted coefficient is 1/(3 log 2).
Thus the printed inequality fails even with a nonzero denominator. -/
theorem inverted_log_sobolev_counterexample :
    ((1 / 3 : ℝ) / Real.log 2) * (2 / 9) < (1 / 3 : ℝ) * Real.log 3 := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have h3 : (2 / 3 : ℝ) ≤ Real.log 3 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3) using 1
    norm_num
  have hpos : 0 < Real.log 2 := by linarith
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hpos).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h3)]

end TailBound
