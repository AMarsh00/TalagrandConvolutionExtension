import TailBound.Core

/-! Finite-product first-order projection inequality (Lemma 18).
The square expansion below is the finite-dimensional Bessel inequality
used by the manuscript's Parseval argument. No probabilistic independence
or conditional-expectation facts are postulated: product moments and
conditional averages are calculated from finite sums.
-/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω]

lemma mean_add (μ f g : Ω → ℝ) :
    mean μ (fun x => f x + g x) = mean μ f + mean μ g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (μ f g : Ω → ℝ) :
    mean μ (fun x => f x - g x) = mean μ f - mean μ g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_smul (μ f : Ω → ℝ) (c : ℝ) :
    mean μ (fun x => c * f x) = c * mean μ f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma mean_const (μ : Ω → ℝ) (hμ : ∑ x, μ x = 1) (c : ℝ) :
    mean μ (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, hμ]

lemma mean_sum {ι : Type*} [Fintype ι] (μ : Ω → ℝ) (f : ι → Ω → ℝ) :
    mean μ (fun x => ∑ i, f i x) = ∑ i, mean μ (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

noncomputable def productWeight (π : ι → α → ℝ) (x : ι → α) : ℝ :=
  ∏ i, π i (x i)

lemma productWeight_mass (π : ι → α → ℝ) (hπ : ∀ i, ∑ a, π i a = 1) :
    ∑ x, productWeight π x = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [hπ]

lemma product_moment (π g : ι → α → ℝ) :
    mean (productWeight π) (fun x => ∏ i, g i (x i)) =
      ∏ i, mean (π i) (g i) := by
  unfold mean productWeight
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => π i a * g i a)).symm

lemma product_marginal (π : ι → α → ℝ) (hπ : ∀ i, ∑ a, π i a = 1)
    (i : ι) (g : α → ℝ) :
    mean (productWeight π) (fun x => g (x i)) = mean (π i) g := by
  have h := product_moment π (fun j a => if j = i then g a else 1)
  have hs (j : ι) : mean (π j) (fun a => if j = i then g a else 1) =
      if j = i then mean (π i) g else 1 := by
    split_ifs with hj
    · subst j; rfl
    · exact mean_const _ (hπ j) 1
  simp only [Fintype.prod_ite_eq', hs] at h
  simpa using h

lemma product_pair_moment (π : ι → α → ℝ) (hπ : ∀ i, ∑ a, π i a = 1)
    (i j : ι) (hij : i ≠ j) (g h : α → ℝ) :
    mean (productWeight π) (fun x => g (x i) * h (x j)) =
      mean (π i) g * mean (π j) h := by
  have hh := product_moment π
    (fun k a => (if k = i then g a else 1) * (if k = j then h a else 1))
  have hs (k : ι) :
      mean (π k) (fun a => (if k = i then g a else 1) * (if k = j then h a else 1)) =
        (if k = i then mean (π i) g else 1) *
        (if k = j then mean (π j) h else 1) := by
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [Ne.symm hij]
      · simp only [hki, hkj, if_false, one_mul]
        exact mean_const _ (hπ k) 1
  simp only [Finset.prod_mul_distrib, Fintype.prod_ite_eq', hs] at hh
  simpa only [Finset.prod_mul_distrib, Fintype.prod_ite_eq'] using hh

/-- The conditional average on `x i = a`. Its value is zero when π i a = 0;
such fibers have zero product weight and do not affect any conclusion. -/
noncomputable def coordinateAverage (π : ι → α → ℝ) (f : (ι → α) → ℝ)
    (i : ι) (a : α) : ℝ :=
  (∑ x, if x i = a then productWeight π x * f x else 0) / π i a

lemma coordinateAverage_test (π : ι → α → ℝ)
    (f : (ι → α) → ℝ) (i : ι) (g : α → ℝ) :
    mean (productWeight π) (fun x => f x * g (x i)) =
      mean (π i) (fun a => coordinateAverage π f i a * g a) := by
  unfold mean coordinateAverage
  have he (a : α) : π i a *
      (((∑ x, if x i = a then productWeight π x * f x else 0) / π i a) * g a) =
        ∑ x, if x i = a then productWeight π x * f x * g a else 0 := by
    by_cases hp : π i a = 0
    · simp only [hp, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro x _
      split_ifs with hx
      · have hw : productWeight π x = 0 := by
          unfold productWeight
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simpa [hx] using hp
        rw [hw, zero_mul, zero_mul]
      · rfl
    · rw [← mul_assoc, mul_div_cancel₀ _ hp, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [mul_assoc]

lemma coordinateAverage_mean (π : ι → α → ℝ)
    (f : (ι → α) → ℝ) (i : ι) :
    mean (π i) (coordinateAverage π f i) = mean (productWeight π) f := by
  simpa using (coordinateAverage_test π f i (fun _ => 1)).symm

/-- A finite-sum form of Bessel's inequality, with all moment hypotheses explicit. -/
lemma finite_bessel (μ F : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (c : ι → Ω → ℝ)
    (hproj : ∀ i, mean μ (fun x => F x * c i x) = mean μ (fun x => (c i x)^2))
    (horth : ∀ i j, i ≠ j → mean μ (fun x => c i x * c j x) = 0) :
    (∑ i, mean μ (fun x => (c i x)^2)) ≤ mean μ (fun x => (F x)^2) := by
  let C : Ω → ℝ := fun x => ∑ i, c i x
  have hFC : mean μ (fun x => F x * C x) = ∑ i, mean μ (fun x => (c i x)^2) := by
    simp only [C, Finset.mul_sum, mean_sum, hproj]
  have hCC : mean μ (fun x => (C x)^2) = ∑ i, mean μ (fun x => (c i x)^2) := by
    simp only [C, pow_two, Finset.sum_mul_sum, mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      exact horth i j (Ne.symm hji)
    · simp
  have hexp : mean μ (fun x => (F x - C x)^2) =
      mean μ (fun x => (F x)^2) - 2 * mean μ (fun x => F x * C x) +
        mean μ (fun x => (C x)^2) := by
    rw [← mean_smul, ← mean_sub, ← mean_add]
    congr 1
    funext x
    ring
  have hn : 0 ≤ mean μ (fun x => (F x - C x)^2) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (sq_nonneg _)
  rw [hFC, hCC] at hexp
  linarith

/-- Lemma 18's first inequality, for any real-valued function and
finite product probability law. There is no assumed Parseval identity. -/
theorem level_one_product (π : ι → α → ℝ)
    (hπnonneg : ∀ i a, 0 ≤ π i a) (hπmass : ∀ i, ∑ a, π i a = 1)
    (f : (ι → α) → ℝ) :
    let m := mean (productWeight π) f
    (∑ i, mean (π i) (fun a => (coordinateAverage π f i a - m)^2)) ≤
      mean (productWeight π) (fun x => (f x)^2) - m^2 := by
  let μ := productWeight π
  let m := mean μ f
  let c : ι → α → ℝ := fun i a => coordinateAverage π f i a - m
  have hμmass : ∑ x, μ x = 1 := productWeight_mass π hπmass
  have hcm (i : ι) : mean (π i) (c i) = 0 := by
    dsimp [c]
    rw [mean_sub, coordinateAverage_mean π, mean_const _ (hπmass i)]
    exact sub_self _
  have hcx (i : ι) : mean μ (fun x => c i (x i)) = 0 := by
    rw [product_marginal π hπmass, hcm]
  have hproj (i : ι) :
      mean μ (fun x => (f x - m) * c i (x i)) =
        mean μ (fun x => (c i (x i))^2) := by
    have htest := coordinateAverage_test π f i (c i)
    have hs : mean (π i) (fun a => coordinateAverage π f i a * c i a) =
        mean (π i) (fun a => (c i a)^2) := by
      have he : (fun a => coordinateAverage π f i a * c i a) =
          fun a => (c i a)^2 + m * c i a := by
        funext a
        dsimp [c]
        ring
      rw [he, mean_add, mean_smul, hcm, mul_zero, add_zero]
    have he : (fun x => (f x - m) * c i (x i)) =
        fun x => f x * c i (x i) - m * c i (x i) := by
      funext x
      ring
    rw [he, mean_sub, mean_smul, hcx, mul_zero, sub_zero]
    rw [htest, hs]
    exact (product_marginal π hπmass i (fun a => (c i a)^2)).symm
  have horth (i j : ι) (hij : i ≠ j) :
      mean μ (fun x => c i (x i) * c j (x j)) = 0 := by
    rw [product_pair_moment π hπmass i j hij, hcm, zero_mul]
  have hb := finite_bessel μ (fun x => f x - m)
    (fun x => Finset.prod_nonneg fun i _ => hπnonneg i (x i))
    (fun i x => c i (x i)) hproj horth
  have hvar : mean μ (fun x => (f x - m)^2) =
      mean μ (fun x => (f x)^2) - m^2 := by
    have he : (fun x => (f x - m)^2) =
        fun x => (f x)^2 - (2 * m) * f x + m^2 := by
      funext x
      ring
    rw [he, mean_add, mean_sub, mean_smul, mean_const μ hμmass]
    change mean μ (fun x => (f x)^2) - 2 * m * m + m^2 = _
    ring
  rw [hvar] at hb
  have hs : (∑ i, mean μ (fun x => (c i (x i))^2)) =
      ∑ i, mean (π i) (fun a => (c i a)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    exact product_marginal π hπmass i (fun a => (c i a)^2)
  rw [hs] at hb
  exact hb

/-- The complete conclusion of Lemma 18, including zero-weight atoms. -/
theorem level_one_product_le_quarter (π : ι → α → ℝ)
    (hπnonneg : ∀ i a, 0 ≤ π i a) (hπmass : ∀ i, ∑ a, π i a = 1)
    (f : (ι → α) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    let m := mean (productWeight π) f
    (∑ i, mean (π i) (fun a => (coordinateAverage π f i a - m)^2)) ≤
      mean (productWeight π) (fun x => (f x)^2) - m^2 ∧
    mean (productWeight π) (fun x => (f x)^2) - m^2 ≤ (1 / 4 : ℝ) := by
  refine ⟨level_one_product π hπnonneg hπmass f, ?_⟩
  exact variance_le_quarter (productWeight π) f
    (fun x => Finset.prod_nonneg fun i _ => hπnonneg i (x i)) hf

end TailBound
