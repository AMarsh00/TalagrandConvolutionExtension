import TailBound.BandTail

/-! Normalization and positive approximation for tail estimates. Finiteness lets
us choose one positive epsilon preserving the strict tail event; no continuity
assumption at a level-set atom is needed. -/
open scoped BigOperators
namespace TailBound
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem tail_from_positive_normalized (μ : Ω → ℝ) (K : Ω → Ω → ℝ)
    (hμ : ∀ x, 0 < μ x) (hmass : ∑ x, μ x = 1) (hK : Stochastic K)
    (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ g : Ω → ℝ, (∀ x, 0 < g x) → mean μ g = 1 →
      ∀ η : ℝ, 1 < η → eventMass μ (fun x => η < act K g x) ≤ C/(η*Real.sqrt (Real.log η))) :
    TailEstimate μ K C := by
  classical
  intro f hf η hη
  let m := mean μ f
  have hm : 0 ≤ m := mean_nonneg (fun x => (hμ x).le) hf
  have hη0 : 0 < η := by linarith
  have hd : 0 < η*Real.sqrt (Real.log η) := mul_pos hη0 (Real.sqrt_pos.mpr (Real.log_pos hη))
  by_cases hm0 : m = 0
  · have hf0 (x : Ω) : f x = 0 := by
      have hh := Finset.single_le_sum (f := fun x => μ x*f x)
        (fun x _ => mul_nonneg (hμ x).le (hf x)) (Finset.mem_univ x)
      change μ x*f x ≤ m at hh
      rw [hm0] at hh
      nlinarith [hμ x,hf x]
    have ha (x : Ω) : act K f x = 0 := by simp [act,hf0]
    have he : eventMass μ (fun x => η*mean μ f < act K f x) = 0 := by
      change eventMass μ (fun x => η*m < act K f x) = 0
      simp [eventMass,hm0,ha]
    rw [he]
    exact div_nonneg hC hd.le
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  let d : Ω → ℝ := fun x => if η*m < act K f x then
    (act K f x-η*m)/(2*(η-1)) else 1
  have hdpos (x : Ω) : 0 < d x := by
    dsimp [d]
    split_ifs with hx
    · exact div_pos (sub_pos.mpr hx) (by linarith)
    · norm_num
  let ε := (Finset.univ : Finset Ω).inf' Finset.univ_nonempty d
  have hε : 0 < ε := by
    dsimp [ε]
    rw [Finset.lt_inf'_iff]
    exact fun x _ => hdpos x
  have hεle (x : Ω) : ε ≤ d x := Finset.inf'_le d (Finset.mem_univ x)
  let g : Ω → ℝ := fun x => (f x+ε)/(m+ε)
  have hg (x : Ω) : 0 < g x := div_pos (by linarith [hf x]) (by linarith)
  have hgm : mean μ g = 1 := by
    have he : mean μ g = (m+ε)/(m+ε) := by
      simp only [mean,g,← mul_div_assoc,mul_add,Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,hmass,one_mul]
      rfl
    rw [he,div_self (by linarith : m+ε ≠ 0)]
  have hag (x : Ω) : act K g x = (act K f x+ε)/(m+ε) := by
    simp only [act,g,← mul_div_assoc,mul_add,Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,hK.2 x,one_mul]
  have hsub (x : Ω) (hx : η*mean μ f < act K f x) : η < act K g x := by
    change η*m < act K f x at hx
    rw [hag,lt_div_iff₀ (by linarith : 0 < m+ε)]
    have hh := hεle x
    dsimp [d] at hh
    rw [if_pos hx,le_div_iff₀ (by linarith : 0 < 2*(η-1))] at hh
    nlinarith
  exact (eventMass_mono μ (fun x => (hμ x).le) _ _ hsub).trans (hpos g hg hgm η hη)

lemma act_strictly_pos (K : Ω → Ω → ℝ) (hK : Stochastic K)
    (f : Ω → ℝ) (hf : ∀ x, 0 < f x) (x : Ω) : 0 < act K f x := by
  have he : ∃ y, 0 < K x y := by
    by_contra hh
    push_neg at hh
    have hz : ∀ y, K x y = 0 := fun y => le_antisymm (hh y) (hK.1 x y)
    have hs := hK.2 x
    simp [hz] at hs
  obtain ⟨y,hy⟩ := he
  exact (mul_pos hy (hf y)).trans_le (Finset.single_le_sum
    (fun z _ => mul_nonneg (hK.1 x z) (hf z).le) (Finset.mem_univ y))

/-- The tail estimate deduced from the fixed-band bound,
including every nonnegative input and every threshold greater than one. -/
theorem tail_estimate_from_bands (μ : Ω → ℝ) (K : Ω → Ω → ℝ)
    (hμ : ∀ x, 0 < μ x) (hmass : ∑ x, μ x = 1)
    (hK : Stochastic K) (hstat : Stationary μ K) {B : ℝ} (hB : 0 ≤ B)
    (hband : ∀ f : Ω → ℝ, (∀ x, 0 < f x) → mean μ f = 1 →
      ∀ r, 2 < r → bandMass μ (act K f) r ≤ B/Real.sqrt r) :
    TailEstimate μ K (max (Real.sqrt 2) (2*B)) := by
  apply tail_from_positive_normalized μ K hμ hmass hK _ (le_max_of_le_left (Real.sqrt_nonneg _))
  intro f hf hm η hη
  exact normalized_tail_from_bands μ (act K f) (fun x => (hμ x).le)
    (act_strictly_pos K hK f hf) ((mean_act μ K hstat f).trans hm) hB (hband f hf hm) η hη

end TailBound
