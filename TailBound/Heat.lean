import TailBound.Entropy
import TailBound.HeatRatio
import TalagrandConvConjecture.Analysis.PiecewiseFTC

/-!
# Heat

The weighted product refresh semigroup, its heat equation, and its
finite level crossings. All kernels are finite sums over the actual alphabet.
-/

open scoped BigOperators

namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def heatKernel (π : α → ℝ) (a : ℝ) (x y : α) : ℝ :=
  π y + a * ((if x = y then 1 else 0) - π y)

omit [Fintype α] in
lemma heatKernel_eq_refresh (π : α → ℝ) (a : ℝ) :
    heatKernel π a = refresh π (1 - a) := by
  funext x y
  unfold heatKernel refresh
  ring

lemma heatKernel_mass (π : α → ℝ) (hπ1 : ∑ a, π a = 1) (a : ℝ) (x : α) :
    ∑ y, heatKernel π a x y = 1 := by
  simp [heatKernel, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hπ1]

lemma heatKernel_stationary (π : α → ℝ) (hπ1 : ∑ a, π a = 1) (a : ℝ) :
    Stationary π (heatKernel π a) := by
  intro y
  simp only [heatKernel, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ x, π x * π y = π y := by rw [← Finset.sum_mul, hπ1, one_mul]
  have h2 : ∑ x, π x * (a * (if x = y then 1 else 0)) = a * π y := by simp; ring
  have h3 : ∑ x, π x * (a * π y) = a * π y := by rw [← Finset.sum_mul, hπ1, one_mul]
  rw [h1, h2, h3]
  ring

lemma heatKernel_comp (π : α → ℝ) (hπ1 : ∑ a, π a = 1) (a b : ℝ) :
    comp (heatKernel π a) (heatKernel π b) = heatKernel π (a * b) := by
  funext x y
  have hstat := heatKernel_stationary π hπ1 b y
  have he : comp (heatKernel π a) (heatKernel π b) x y =
      (1 - a) * π y + a * heatKernel π b x y := by
    unfold comp
    calc
      _ = ∑ z, ((1 - a) * π z + a * (if x=z then 1 else 0)) * heatKernel π b z y := by
        apply Finset.sum_congr rfl; intro z _; unfold heatKernel; ring
      _ = _ := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rw [hstat]
        simp
  rw [he]
  unfold heatKernel
  ring

noncomputable def heat {n : ℕ} (π : α → ℝ) (f : (Fin n → α) → ℝ)
    (s : ℝ) : (Fin n → α) → ℝ :=
  act (tensorKernel (heatKernel π (Real.exp (-s))) n) f

noncomputable def refreshGenerator {n : ℕ} (π : α → ℝ) (f : (Fin n → α) → ℝ)
    (x : Fin n → α) : ℝ :=
  ∑ i, (mean π (fun a => f (Function.update x i a)) - f x)

lemma mean_heat (π : α → ℝ) (hπ1 : ∑ a, π a = 1) {n : ℕ}
    (f : (Fin n → α) → ℝ) (s : ℝ) :
    mean (tensorWeight π n) (heat π f s) = mean (tensorWeight π n) f :=
  mean_act _ _ (tensor_stationary π _ (heatKernel_stationary π hπ1 _) n) f

lemma heat_add (π : α → ℝ) (hπ1 : ∑ a, π a = 1) {n : ℕ}
    (f : (Fin n → α) → ℝ) (s t : ℝ) : heat π f (s + t) = heat π (heat π f t) s := by
  unfold heat
  rw [neg_add, Real.exp_add, ← heatKernel_comp π hπ1,
    tensor_comp, act_comp]

lemma heat_zero (π : α → ℝ) {n : ℕ} (f : (Fin n → α) → ℝ) : heat π f 0 = f := by
  funext x
  have hk : heatKernel π (Real.exp (-(0 : ℝ))) = fun x y : α => if x=y then 1 else 0 := by
    funext x y; simp [heatKernel]
  have hp (y : Fin n → α) : (∏ i : Fin n, (if x i=y i then (1 : ℝ) else 0)) =
      if x=y then 1 else 0 := by
    by_cases h : x=y
    · simp [h]
    · have he : ∃ i, x i ≠ y i := Function.ne_iff.mp h
      obtain ⟨i, hi⟩ := he
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold heat
  rw [hk]
  simp only [act, tensorKernel, hp]
  simp

lemma heat_nonneg (π : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a) {n : ℕ}
    (f : (Fin n → α) → ℝ) (hf : ∀ x, 0 ≤ f x) {s : ℝ} (hs : 0 ≤ s) :
    ∀ x, 0 ≤ heat π f s x := by
  have ha : Real.exp (-s) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
  apply act_nonneg _ hf
  apply tensor_nonneg
  intro x y
  rw [heatKernel_eq_refresh]
  unfold refresh
  have := Real.exp_pos (-s)
  split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.mpr ha) (hπ0 y)]

lemma heat_pos (π : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1) {n : ℕ}
    (f : (Fin n → α) → ℝ) (hf : ∀ x, 0 < f x) {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → α) : 0 < heat π f s x := by
  have hK : ∀ x y, 0 ≤ heatKernel π (Real.exp (-s)) x y := by
    intro x y
    have ha : Real.exp (-s) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
    rw [heatKernel_eq_refresh]
    unfold refresh
    have := Real.exp_pos (-s)
    split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.mpr ha) (hπ0 y)]
  have hm : (∑ y, tensorKernel (heatKernel π (Real.exp (-s))) n x y) = 1 := by
    unfold tensorKernel
    rw [← Fintype.prod_sum]
    simp [heatKernel_mass π hπ1]
  have hex : ∃ y, 0 < tensorKernel (heatKernel π (Real.exp (-s))) n x y := by
    by_contra hn
    push Not at hn
    have hz : (∑ y, tensorKernel (heatKernel π (Real.exp (-s))) n x y) = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hn y) (tensor_nonneg hK n x y)
    linarith
  obtain ⟨y, hy⟩ := hex
  apply Finset.sum_pos'
  · intro z _; exact mul_nonneg (tensor_nonneg hK n x z) (hf z).le
  · exact ⟨y, Finset.mem_univ y, mul_pos hy (hf y)⟩

lemma generator_kernel (π : α → ℝ) (hπ1 : ∑ a, π a = 1) {n : ℕ}
    (a : ℝ) (x y : Fin n → α) :
    refreshGenerator π (fun z => tensorKernel (heatKernel π a) n z y) x =
      ∑ i, (π (y i) - heatKernel π a (x i) (y i)) *
        ∏ j ∈ Finset.univ.erase i, heatKernel π a (x j) (y j) := by
  unfold refreshGenerator
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [tensorKernel_update, mean, ← mul_assoc, ← Finset.sum_mul]
  rw [heatKernel_stationary π hπ1 a (y i), tensorKernel_row _ n x y i]
  ring

omit [DecidableEq α] in
lemma generator_act (π : α → ℝ) {n : ℕ} (K : (Fin n → α) → (Fin n → α) → ℝ)
    (f : (Fin n → α) → ℝ) (x : Fin n → α) :
    refreshGenerator π (act K f) x = ∑ y, refreshGenerator π (fun z => K z y) x * f y := by
  unfold refreshGenerator
  simp only [act, mean, Finset.mul_sum]
  have he (i : Fin n) :
      (∑ a, ∑ y, π a * (K (Function.update x i a) y * f y)) - ∑ y, K x y * f y =
        ∑ y, ((∑ a, π a * K (Function.update x i a) y) - K x y) * f y := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    simp [Finset.sum_mul, sub_mul, mul_assoc]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finset.sum_mul _ _ _).symm

lemma hasDerivAt_heat (π : α → ℝ) (hπ1 : ∑ a, π a = 1) {n : ℕ}
    (f : (Fin n → α) → ℝ) (x : Fin n → α) (s : ℝ) :
    HasDerivAt (fun t => heat π f t x) (refreshGenerator π (heat π f s) x) s := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
    simpa using (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg' s)
  have hk (u v : α) : HasDerivAt (fun t => heatKernel π (Real.exp (-t)) u v)
      (π v - heatKernel π (Real.exp (-s)) u v) s := by
    convert (hexp.mul_const ((if u=v then 1 else 0) - π v)).const_add (π v) using 1
    dsimp [heatKernel]
    ring
  have hp (y : Fin n → α) := HasDerivAt.fun_finset_prod
    (u := (Finset.univ : Finset (Fin n))) (fun i _ => hk (x i) (y i))
  have hh := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → α)))
    (fun y _ => (hp y).mul_const (f y))
  rw [show refreshGenerator π (heat π f s) x =
    ∑ y, (∑ i, (π (y i) - heatKernel π (Real.exp (-s)) (x i) (y i)) *
      ∏ j ∈ Finset.univ.erase i, heatKernel π (Real.exp (-s)) (x j) (y j)) * f y by
        rw [heat, generator_act]; simp_rw [generator_kernel π hπ1]]
  simpa only [heat, act, tensorKernel, smul_eq_mul, mul_comm] using hh

lemma continuous_heat (π : α → ℝ) (hπ1 : ∑ a, π a = 1) {n : ℕ}
    (f : (Fin n → α) → ℝ) (x : Fin n → α) : Continuous (fun s => heat π f s x) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_heat π hπ1 f x s).continuousAt

noncomputable def heatPolynomial {n : ℕ} (π : α → ℝ)
    (f : (Fin n → α) → ℝ) (x : Fin n → α) : Polynomial ℝ :=
  ∑ y, (∏ i : Fin n, (Polynomial.C (π (y i)) +
    Polynomial.X * Polynomial.C ((if x i=y i then 1 else 0) - π (y i)))) * Polynomial.C (f y)

lemma heatPolynomial_eval {n : ℕ} (π : α → ℝ) (f : (Fin n → α) → ℝ)
    (x : Fin n → α) (a : ℝ) :
    (heatPolynomial π f x).eval a = act (tensorKernel (heatKernel π a) n) f x := by
  simp [heatPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_prod,
    act, tensorKernel, heatKernel, apply_ite]

lemma heatPolynomial_zero {n : ℕ} (π : α → ℝ) (f : (Fin n → α) → ℝ)
    (x : Fin n → α) :
    (heatPolynomial π f x).eval 0 = mean (tensorWeight π n) f := by
  simp [heatPolynomial_eval, act, tensorKernel, heatKernel, mean, tensorWeight]

/-- There are finitely many crossings of any level different from the mean.
This supplies the finite deterministic stopping grid used by the ODE proof. -/
lemma finite_heat_crossings {n : ℕ} (π : α → ℝ) (f : (Fin n → α) → ℝ)
    (c : ℝ) (hc : c ≠ mean (tensorWeight π n) f) :
    {s : ℝ | ∃ x : Fin n → α, heat π f s x = c}.Finite := by
  have hsingle (x : Fin n → α) : {s : ℝ | heat π f s x = c}.Finite := by
    let p := heatPolynomial π f x - Polynomial.C c
    have hp : p ≠ 0 := by
      intro h
      have he := congrArg (fun q : Polynomial ℝ => q.eval 0) h
      simp only [p, Polynomial.eval_sub, Polynomial.eval_C, heatPolynomial_zero,
        Polynomial.eval_zero] at he
      exact hc (by linarith)
    have hz := Talagrand.finite_setOf_poly_exp_eq hp
    convert hz using 1
    ext s
    simp only [Set.mem_setOf_eq, p, Polynomial.eval_sub, Polynomial.eval_C,
      heatPolynomial_eval, sub_eq_zero, heat]
  simpa only [Set.setOf_exists] using Set.finite_iUnion hsingle

end TailBound
