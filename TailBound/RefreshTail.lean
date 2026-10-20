import TailBound.SharpStatement
import TailBound.PositiveApproximation
import TailBound.MainStatement
import TailBound.PositiveKernel

/-! The finite-alphabet refresh tail and its transfer to positive stationary kernels. -/
open scoped BigOperators
namespace TailBound
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem heat_tail_of_bounds [Nonempty α] (π : α → ℝ) (m M τ : ℝ)
    (hm : 0 < m) (hlower : ∀ x, m ≤ π x) (hupper : ∀ x, π x ≤ M)
    (hmass : ∑ x, π x = 1) (hτ : 0 < τ) :
    DimensionFreeTail π (heatKernel π (Real.exp (-τ))) := by
  let D0 : RefreshData α 0 := ⟨π,hmass,m,M,hm,hlower,hupper,τ,hτ,fun _ => 1,
    fun _ => zero_lt_one,by simpa [mean] using tensor_mass π hmass 0⟩
  refine ⟨max (Real.sqrt 2) (2*(D0.sharpBandConstant*D0.sharpK)),
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) (le_max_left _ _),?_⟩
  intro n
  have hπ : ∀ x, 0 < π x := fun x => hm.trans_le (hlower x)
  have hK : Stochastic (tensorKernel (heatKernel π (Real.exp (-τ))) n) := by
    constructor
    · apply tensor_nonneg
      intro x y
      have ha : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hp := Real.exp_pos (-τ)
      unfold heatKernel
      split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.mpr ha) (hπ y).le]
    · intro x
      unfold tensorKernel
      rw [← Fintype.prod_sum]
      simp [heatKernel_mass π hmass]
  apply tail_estimate_from_bands (tensorWeight π n) _
    (fun x => Finset.prod_pos (fun i _ => hπ (x i))) (tensor_mass π hmass n) hK
    (tensor_stationary π _ (heatKernel_stationary π hmass _) n) (mul_pos D0.sharpBandConstant_pos D0.sharpK_pos).le
  intro f hf hfm r hr
  let D : RefreshData α n := ⟨π,hmass,m,M,hm,hlower,hupper,τ,hτ,f,hf,hfm⟩
  have hh := D.fixed_band_sharp r hr
  rw [D.startBand_eq_profile] at hh
  have htime : D.horizon-2 = τ := by dsimp [RefreshData.horizon,D]; ring
  rw [htime] at hh
  exact hh

theorem refresh_tail [Nonempty α] (π : α → ℝ) (hπ : ∀ x, 0 < π x)
    (hmass : ∑ x, π x = 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    DimensionFreeTail π (refresh π ε) := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image (Finset.univ : Finset α) π Finset.univ_nonempty
  have hupper (x : α) : π x ≤ 1 := by
    rw [← hmass]
    exact Finset.single_le_sum (fun y _ => (hπ y).le) (Finset.mem_univ x)
  have hτ : 0 < -Real.log (1-ε) := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  have hh := heat_tail_of_bounds π (π a) 1 (-Real.log (1-ε)) (hπ a)
    (fun x => ha x (Finset.mem_univ x)) hupper hmass hτ
  rw [neg_neg,Real.exp_log (by linarith : 0 < 1-ε),heatKernel_eq_refresh,
    show 1-(1-ε)=ε by ring] at hh
  exact hh

/-- The refresh claim is proved, not assumed. -/
theorem refreshTailClaim : RefreshTailClaim := by
  intro α _ _ π hπ hmass ε hε hε1
  haveI : Nonempty α := by
    by_contra hn
    haveI : IsEmpty α := not_nonempty_iff.mp hn
    simp at hmass
  exact refresh_tail π hπ hmass ε hε hε1

theorem positive_kernel_tail (π : α → ℝ) (K : α → α → ℝ)
    (hπ : ∀ x, 0 < π x) (hmass : ∑ x, π x = 1)
    (hK : ∀ x y, 0 < K x y) (hrows : ∀ x, ∑ y, K x y = 1)
    (hstat : Stationary π K) : DimensionFreeTail π K :=
  positive_kernel_from_refresh π K hπ hmass hK hrows hstat
    (fun ε hε hε1 => refreshTailClaim α π hπ hmass ε hε hε1)

end TailBound
