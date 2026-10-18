import TailBound.BridgeDynamics

/-! Backward equations tensorize coordinate by coordinate, including at
terminal time when the coordinate laws have zero atoms. -/

open scoped BigOperators
namespace TailBound

variable {α ι β : Type*} [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι] [Fintype β]

lemma productWeight_update_sub (μ : ι → α → ℝ) (ν : α → ℝ) (i : ι) (u : ι → α) :
    productWeight (Function.update μ i ν) u-productWeight μ u =
      (ν (u i)-μ i (u i))*∏ j ∈ Finset.univ.erase i, μ j (u j) := by
  unfold productWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, Function.update μ i ν j (u j)) =
      ∏ j ∈ Finset.univ.erase i, μ j (u j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  ring

lemma product_generator_identity (μ : ι → α → ℝ) (ν : ι → β → α → ℝ)
    (rate : ι → β → ℝ) (φ : (ι → α) → ℝ) :
    (∑ u, (∑ i, (∑ g, rate i g*(ν i g (u i)-μ i (u i))) *
        ∏ j ∈ Finset.univ.erase i, μ j (u j))*φ u) =
      ∑ i, ∑ g, rate i g*(mean (productWeight (Function.update μ i (ν i g))) φ-
        mean (productWeight μ) φ) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  unfold mean
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [← sub_mul,productWeight_update_sub]
  ring

lemma hasDerivAt_product_expectation (μ : ℝ → ι → α → ℝ)
    (ν : ι → β → α → ℝ) (rate : ι → β → ℝ) (φ : (ι → α) → ℝ) (t : ℝ)
    (hμ : ∀ i u, HasDerivAt (fun s => μ s i u)
      (-(∑ g, rate i g*(ν i g u-μ t i u))) t) :
    HasDerivAt (fun s => mean (productWeight (μ s)) φ)
      (-(∑ i, ∑ g, rate i g*(mean (productWeight (Function.update (μ t) i (ν i g))) φ-
        mean (productWeight (μ t)) φ))) t := by
  have hp (u : ι → α) := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset ι))
    (fun i _ => hμ i (u i))
  have hh := HasDerivAt.fun_sum (u := (Finset.univ : Finset (ι → α)))
    (fun u _ => (hp u).mul_const (φ u))
  have he : (∑ u, (∑ i, (-(∑ g, rate i g*(ν i g (u i)-μ t i (u i)))) *
      ∏ j ∈ Finset.univ.erase i, μ t j (u j))*φ u) =
      -(∑ i, ∑ g, rate i g*(mean (productWeight (Function.update (μ t) i (ν i g))) φ-
        mean (productWeight (μ t)) φ)) := by
    simp only [neg_mul,Finset.sum_neg_distrib]
    rw [product_generator_identity]
  convert hh using 1
  rw [← he]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul]
  ring

variable [Nonempty α] {n : ℕ}
namespace RefreshData
variable (D : RefreshData α n)

noncomputable def bridgeGen (t : ℝ) (z : Fin n → α)
    (q : (Fin n → α) → (Fin n → α) → ℝ) (x y : Fin n → α) : ℝ :=
  ∑ i, ∑ g, D.bridgeRate t z x i g*(q (Function.update x i g) (Function.update y i g)-q x y)

lemma hasDerivAt_bridgeQ (φ : (Fin n → α) → ℝ) {t : ℝ} (ht : t ≤ 2)
    (z x y : Fin n → α) :
    HasDerivAt (fun s => D.bridgeQ φ s z x y) (-D.bridgeGen t z (D.bridgeQ φ t z) x y) t := by
  let μ := fun s => bridgeMarginals D.π D.retention (bridgeTime s) z x y
  let ν := fun i g => bridgeLaw D.π D.retention (bridgeTime t) (z i) g g
  have hμ (i : Fin n) (u : α) : HasDerivAt (fun s => μ s i u)
      (-(∑ g, D.bridgeRate t z x i g*(ν i g u-μ t i u))) t := by
    have hh := hasDerivAt_bridgeLaw D.π D.retention t (z i) (x i) (y i) u
      (D.bridge_den_pos ht _ _).ne'
    have he := bridgeLaw_generator D.π D.mass D.retention (bridgeTime t)
      (z i) (x i) (y i) u (fun g => (D.bridge_den_pos ht _ _).ne')
    dsimp [bridgeRate,ν,μ,bridgeMarginals]
    simp_rw [mul_div_assoc]
    rw [he]
    convert hh using 1 <;> ring
  have hh := hasDerivAt_product_expectation μ ν (D.bridgeRate t z x) φ t hμ
  have he (i : Fin n) (g : α) :
      Function.update (μ t) i (ν i g) =
        bridgeMarginals D.π D.retention (bridgeTime t) z (Function.update x i g) (Function.update y i g) := by
    rw [bridgeMarginals_update_x,bridgeMarginals_update_y,Function.update_idem,Function.update_self]
  simp_rw [he] at hh
  exact hh

end RefreshData
end TailBound
