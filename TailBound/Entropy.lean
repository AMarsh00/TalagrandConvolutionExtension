import TailBound.LevelOne
import TalagrandConvConjecture.Cube.Entropy

/-!
Entropy tensorization for the manuscript's arbitrary finite alphabet.
The variational and convexity lemmas imported from `Talagrand` are stated
for arbitrary finite probability weights; no Boolean-cube estimate is used.
-/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma mean_nonneg {μ f : α → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ mean μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (hf x)

lemma mean_mono {μ f g : α → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hfg : ∀ x, f x ≤ g x) :
    mean μ f ≤ mean μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hμ x)

lemma tensorWeight_nonneg {π : α → ℝ} (hπ : ∀ a, 0 ≤ π a)
    (n : ℕ) (x : Fin n → α) : 0 ≤ tensorWeight π n x :=
  Finset.prod_nonneg fun i _ => hπ (x i)

lemma tensorWeight_mass (π : α → ℝ) (hπ : ∑ a, π a = 1) (n : ℕ) :
    ∑ x, tensorWeight π n x = 1 :=
  productWeight_mass (fun _ : Fin n => π) (fun _ => hπ)

lemma tensorWeight_cons (π : α → ℝ) {n : ℕ} (a : α) (x : Fin n → α) :
    tensorWeight π (n+1) (Fin.cons a x) = π a * tensorWeight π n x := by
  simp [tensorWeight, Fin.prod_univ_succ]

lemma mean_tensor_succ (π : α → ℝ) {n : ℕ} (f : (Fin (n+1) → α) → ℝ) :
    mean (tensorWeight π (n+1)) f =
      mean (tensorWeight π n) (fun x => mean π (fun a => f (Fin.cons a x))) := by
  unfold mean
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n+1) => α)
    (fun p => tensorWeight π (n+1) (Fin.cons p.1 p.2) * f (Fin.cons p.1 p.2))
    (fun x => tensorWeight π (n+1) x * f x) (fun _ => rfl),
    Fintype.sum_prod_type_right]
  simp_rw [tensorWeight_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma update_cons_zero {n : ℕ} (a b : α) (x : Fin n → α) :
    Function.update (Fin.cons a x : Fin (n+1) → α) 0 b = (Fin.cons b x : Fin (n+1) → α) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp [Fin.succ_ne_zero]

lemma update_cons_succ {n : ℕ} (a b : α) (x : Fin n → α) (i : Fin n) :
    Function.update (Fin.cons a x : Fin (n+1) → α) i.succ b = (Fin.cons a (Function.update x i b) : Fin (n+1) → α) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)), Fin.cons_zero, Fin.cons_zero]
  · by_cases hk : k = i
    · subst k; simp
    · simp [hk, show k.succ ≠ i.succ from fun h => hk (Fin.succ_injective n h)]

lemma mean_comm (π : α → ℝ) {β : Type*} [Fintype β]
    (μ : β → ℝ) (f : α → β → ℝ) :
    mean π (fun a => mean μ (f a)) = mean μ (fun b => mean π (fun a => f a b)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma mean_tensor_resample (π : α → ℝ) (hπ1 : ∑ a, π a = 1)
    (n : ℕ) (i : Fin n) (f : (Fin n → α) → ℝ) :
    mean (tensorWeight π n) (fun x => mean π (fun a => f (Function.update x i a))) =
      mean (tensorWeight π n) f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mean_tensor_succ, update_cons_zero]
      congr 1
      funext x
      exact mean_const π hπ1 _
    · simp only [mean_tensor_succ, update_cons_succ]
      rw [← mean_comm π (tensorWeight π n), ← mean_comm π (tensorWeight π n)]
      congr 1
      funext a
      exact ih j (fun x => f (Fin.cons a x))

noncomputable def coordinateEntropy (π : α → ℝ) {n : ℕ}
    (f : (Fin n → α) → ℝ) (i : Fin n) (x : Fin n → α) : ℝ :=
  Talagrand.ent π (fun a => f (Function.update x i a))

lemma entropy_mean_form (π f : α → ℝ) :
    Talagrand.ent π f = mean π (fun x => f x * Real.log (f x)) -
      mean π f * Real.log (mean π f) := rfl

lemma entropy_tensor_chain (π : α → ℝ) {n : ℕ}
    (f : (Fin (n+1) → α) → ℝ) :
    Talagrand.ent (tensorWeight π (n+1)) f =
      mean (tensorWeight π n) (fun x => Talagrand.ent π (fun a => f (Fin.cons a x))) +
      Talagrand.ent (tensorWeight π n) (fun x => mean π (fun a => f (Fin.cons a x))) := by
  simp only [entropy_mean_form, mean_tensor_succ, mean_sub]
  ring

lemma entropy_tensor_zero (π : α → ℝ) (f : (Fin 0 → α) → ℝ) :
    Talagrand.ent (tensorWeight π 0) f = 0 := by
  simp [Talagrand.ent, tensorWeight, Fintype.sum_unique]

/-- Entropy tensorization over any finite probability alphabet. -/
theorem entropy_tensorization (π : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (hπ1 : ∑ a, π a = 1) (n : ℕ) (f : (Fin n → α) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    Talagrand.ent (tensorWeight π n) f ≤
      ∑ i, mean (tensorWeight π n) (coordinateEntropy π f i) := by
  induction n with
  | zero => simp [entropy_tensor_zero]
  | succ n ih =>
    let F : (Fin n → α) → ℝ := fun x => mean π (fun a => f (Fin.cons a x))
    have hF : ∀ x, 0 ≤ F x := fun x => mean_nonneg hπ0 (fun a => hf _)
    have hI := ih F hF
    have h0 : mean (tensorWeight π (n+1)) (coordinateEntropy π f 0) =
        mean (tensorWeight π n) (fun x => Talagrand.ent π (fun a => f (Fin.cons a x))) := by
      rw [mean_tensor_succ]
      congr 1
      funext x
      simp only [coordinateEntropy, update_cons_zero]
      exact mean_const π hπ1 _
    have hstep (i : Fin n) : mean (tensorWeight π n) (coordinateEntropy π F i) ≤
        mean (tensorWeight π (n+1)) (coordinateEntropy π f i.succ) := by
      rw [mean_tensor_succ]
      apply mean_mono (tensorWeight_nonneg hπ0 n)
      intro x
      simp only [coordinateEntropy, F, mean, update_cons_succ]
      exact Talagrand.ent_average_le π π
        (fun a b => f (Fin.cons a (Function.update x i b))) hπ0 hπ1 hπ0 hπ1
        (fun a b => hf _)
    rw [entropy_tensor_chain, Fin.sum_univ_succ, h0]
    exact add_le_add le_rfl (hI.trans (Finset.sum_le_sum fun i _ => hstep i))

/-- Variance as the mean square difference of two independent samples. -/
lemma variance_pair (π f : α → ℝ) (hπ1 : ∑ a, π a = 1) :
    mean π (fun x => mean π (fun y => (f x - f y)^2)) =
      2 * (mean π (fun x => (f x)^2) - (mean π f)^2) := by
  have he (x : α) : mean π (fun y => (f x - f y)^2) =
      (f x)^2 - 2 * f x * mean π f + mean π (fun y => (f y)^2) := by
    calc
      _ = mean π (fun y => (f x)^2 - (2 * f x) * f y + (f y)^2) := by
        congr 1; funext y; ring
      _ = _ := by rw [mean_add, mean_sub, mean_const π hπ1, mean_smul]
  simp_rw [he]
  rw [mean_add, mean_sub, mean_const π hπ1]
  have hs : mean π (fun x => 2 * f x * mean π f) = 2 * (mean π f)^2 := by
    calc
      _ = mean π (fun x => (2 * mean π f) * f x) := by congr 1; funext x; ring
      _ = _ := by rw [mean_smul]; ring
  rw [hs]
  ring

/-- The elementary entropy-to-variance estimate, including zero values of `g`. -/
lemma entropy_le_variance_div (π g : α → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (hg : ∀ a, 0 ≤ g a) (hM : 0 < mean π g) :
    Talagrand.ent π g ≤
      (mean π (fun a => (g a)^2) - (mean π g)^2) / mean π g := by
  let M := mean π g
  have hm : 0 < M := hM
  have he (a : α) : g a * Real.log (g a) - g a * Real.log M ≤
      (g a)^2 / M - g a := by
    rcases (hg a).eq_or_lt with h | h
    · rw [← h]; simp
    · have hlog := Real.log_le_sub_one_of_pos (div_pos h hm)
      rw [Real.log_div (ne_of_gt h) (ne_of_gt hm)] at hlog
      have hh := mul_le_mul_of_nonneg_left hlog h.le
      convert hh using 1 <;> ring
  have hs := mean_mono hπ0 he
  have hL : mean π (fun a => g a * Real.log (g a) - g a * Real.log M) =
      Talagrand.ent π g := by
    rw [mean_sub, entropy_mean_form]
    congr 1
    simp only [mean, ← mul_assoc, ← Finset.sum_mul]
    rfl
  have hR : mean π (fun a => (g a)^2 / M - g a) =
      (mean π (fun a => (g a)^2) - M^2) / M := by
    rw [mean_sub]
    have hd : mean π (fun a => (g a)^2 / M) = mean π (fun a => (g a)^2) / M := by
      simp only [mean, ← mul_div_assoc, ← Finset.sum_div]
    rw [hd]
    change _ - M = _
    field_simp
    <;> ring
  rw [hL, hR] at hs
  exact hs

/-- A valid (nonoptimal) one-site log-Sobolev constant `4/m`, where every
atom has weight at least `m > 0`. This avoids the manuscript's inverted
coefficient; only the alphabet-dependent constant is enlarged. -/
theorem finite_alphabet_LSI (π v : α → ℝ) (m : ℝ) (hm : 0 < m)
    (hπ : ∀ a, m ≤ π a) (hπ1 : ∑ a, π a = 1) :
    Talagrand.ent π (fun a => (v a)^2) ≤
      (2 / m) * mean π (fun x => mean π (fun y => (v x - v y)^2)) := by
  have hπ0 : ∀ a, 0 ≤ π a := fun a => (hm.trans_le (hπ a)).le
  let M := mean π (fun a => (v a)^2)
  have hM : 0 ≤ M := mean_nonneg hπ0 (fun a => sq_nonneg _)
  have hpoint (a : α) : m * (v a)^2 ≤ M := by
    refine (mul_le_mul_of_nonneg_right (hπ a) (sq_nonneg _)).trans ?_
    exact Finset.single_le_sum (fun b _ => mul_nonneg (hπ0 b) (sq_nonneg _))
      (Finset.mem_univ a)
  rcases hM.eq_or_lt with hzero | hpos
  · have hv : ∀ a, v a = 0 := by
      intro a
      have ha := hpoint a
      rw [← hzero] at ha
      have : (v a)^2 = 0 := by nlinarith [sq_nonneg (v a)]
      exact sq_eq_zero_iff.mp this
    simp [hv, Talagrand.ent, mean]
  · have hpair (x y : α) : ((v x)^2 - (v y)^2)^2 ≤
        (4 * M / m) * (v x - v y)^2 := by
      have hx := hpoint x
      have hy := hpoint y
      have hsum : m * (v x + v y)^2 ≤ 4 * M := by
        nlinarith [mul_nonneg hm.le (sq_nonneg (v x - v y))]
      have hsum' : (v x + v y)^2 ≤ 4 * M / m := (le_div_iff₀ hm).mpr (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right hsum' (sq_nonneg (v x - v y))
      nlinarith [hh]
    have hp := mean_mono hπ0 fun x => mean_mono hπ0 fun y => hpair x y
    simp_rw [mean_smul] at hp
    rw [variance_pair π (fun a => (v a)^2) hπ1] at hp
    have he := entropy_le_variance_div π (fun a => (v a)^2) hπ0
      (fun a => sq_nonneg _) hpos
    refine he.trans ?_
    apply (div_le_iff₀ hpos).mpr
    have hcancel : (4 * M / m) = 2 * M * (2 / m) := by ring
    rw [hcancel] at hp
    change mean π (fun a => (v a ^ 2)^2) - M^2 ≤ _
    nlinarith [hp]

/-- The product log-Sobolev estimate used in Lemma 3. The constant depends
only on the least one-coordinate mass, never on the product dimension. -/
theorem product_LSI (π : α → ℝ) (m : ℝ) (hm : 0 < m)
    (hπ : ∀ a, m ≤ π a) (hπ1 : ∑ a, π a = 1)
    (n : ℕ) (h : (Fin n → α) → ℝ) (hh : ∀ x, 0 ≤ h x) :
    Talagrand.ent (tensorWeight π n) h ≤ (2 / m) *
      mean (tensorWeight π n) (fun x => ∑ i, mean π
        (fun a => (Real.sqrt (h (Function.update x i a)) - Real.sqrt (h x))^2)) := by
  have hπ0 : ∀ a, 0 ≤ π a := fun a => (hm.trans_le (hπ a)).le
  refine (entropy_tensorization π hπ0 hπ1 n h hh).trans ?_
  have hsite (i : Fin n) (x : Fin n → α) : coordinateEntropy π h i x ≤
      (2 / m) * mean π (fun a => mean π (fun b =>
        (Real.sqrt (h (Function.update x i a)) - Real.sqrt (h (Function.update x i b)))^2)) := by
    have hs := finite_alphabet_LSI π (fun a => Real.sqrt (h (Function.update x i a)))
      m hm hπ hπ1
    simpa only [Real.sq_sqrt (hh _), coordinateEntropy] using hs
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    mean_mono (tensorWeight_nonneg hπ0 n) (hsite i)
  simp_rw [mean_smul] at hs
  rw [← Finset.mul_sum] at hs
  refine hs.trans_eq ?_
  congr 1
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := mean_tensor_resample π hπ1 n i (fun x => mean π (fun b =>
    (Real.sqrt (h x) - Real.sqrt (h (Function.update x i b)))^2))
  simpa only [Function.update_idem, sub_sq_comm] using hi

end TailBound
