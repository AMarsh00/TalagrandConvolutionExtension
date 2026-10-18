import TailBound.BandPartition
import TailBound.SmallThreshold

/-! The finite geometric-band argument of Lemma 1, for arbitrary weights.
This is the same layer-cake argument used in the Boolean development's Main.lean;
no uniform-measure or cube-specific theorem is assumed. -/
open scoped BigOperators
namespace TailBound
attribute [local instance] Classical.propDecidable

lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1/2 := by
  have he : Real.exp (-1)*Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9,Real.exp_pos (-1)]

lemma sum_exp_neg_le_two (m : ℕ) :
    ∑ j ∈ Finset.range m, Real.exp (-(j:ℝ)) ≤ 2 := by
  have h (k : ℕ) : ∑ j ∈ Finset.range k, Real.exp (-(j:ℝ)) ≤
      2-2*Real.exp (-(k:ℝ)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have he : Real.exp (-((k+1:ℕ):ℝ)) = Real.exp (-(k:ℝ))*Real.exp (-1) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [he]
      nlinarith [Real.exp_pos (-(k:ℝ)),mul_le_mul_of_nonneg_left exp_neg_one_le_half (Real.exp_pos (-(k:ℝ))).le]
  linarith [h m,Real.exp_pos (-(m:ℝ))]

lemma finite_band_index {c v : ℝ} {Q : ℕ} (hcv : c < v) (hv : v ≤ c+Q) :
    ∃ j ∈ Finset.range Q, c+j < v ∧ v ≤ c+j+1 := by
  let j := Nat.ceil (v-c)-1
  have hp : 1 ≤ Nat.ceil (v-c) := Nat.ceil_pos.mpr (by linarith)
  have hq : Nat.ceil (v-c) ≤ Q := Nat.ceil_le.mpr (by linarith)
  have hc : (j:ℝ) = (Nat.ceil (v-c):ℝ)-1 := by
    dsimp [j]; rw [Nat.cast_sub hp]; norm_num
  refine ⟨j,Finset.mem_range.mpr (by dsimp [j]; omega),?_,?_⟩
  · have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ v-c)
    rw [hc]; linarith
  · have hh := Nat.le_ceil (v-c)
    rw [hc]; linarith

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem log_tail_from_bands (μ g : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hg : ∀ x, 0 < g x) {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    (hband : ∀ r, ℓ ≤ r → bandMass μ g r ≤ B/Real.sqrt r) :
    eventMass μ (fun x => ℓ < Real.log (g x)) ≤
      2*B/(Real.exp ℓ*Real.sqrt ℓ) := by
  classical
  let J : ℕ := ∑ x, Nat.ceil (max (Real.log (g x)-ℓ) 0)
  have hJ (x : Ω) : Real.log (g x) ≤ ℓ+J := by
    have hh := Finset.single_le_sum (f := fun x => Nat.ceil (max (Real.log (g x)-ℓ) 0))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have hc : (Nat.ceil (max (Real.log (g x)-ℓ) 0):ℝ) ≤ J := by exact_mod_cast hh
    have hn := Nat.le_ceil (max (Real.log (g x)-ℓ) 0)
    have hm := le_max_left (Real.log (g x)-ℓ) 0
    linarith
  have hcover : eventMass μ (fun x => ℓ < Real.log (g x)) ≤
      ∑ j ∈ Finset.range J, eventMass μ (fun x => ℓ+j < Real.log (g x) ∧ Real.log (g x) ≤ ℓ+j+1) := by
    unfold eventMass
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : ℓ < Real.log (g x)
    · obtain ⟨j,hj,hlo,hhi⟩ := finite_band_index hx (hJ x)
      rw [if_pos hx]
      have hh := Finset.single_le_sum
        (f := fun j : ℕ => if ℓ+j < Real.log (g x) ∧ Real.log (g x) ≤ ℓ+j+1 then μ x else 0)
        (fun j _ => by dsimp only; split_ifs <;> first | exact hμ x | exact le_rfl) hj
      dsimp only at hh
      rw [if_pos (show ℓ+j < Real.log (g x) ∧ Real.log (g x) ≤ ℓ+j+1 from ⟨hlo,hhi⟩)] at hh
      apply hh.trans_eq
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ℓ+i < Real.log (g x) ∧ Real.log (g x) ≤ ℓ+i+1 <;> simp [hi]
    · rw [if_neg hx]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> first | exact hμ x | exact le_rfl)
  have hb (r : ℝ) : eventMass μ (fun x => r < Real.log (g x) ∧ Real.log (g x) ≤ r+1) ≤
      Real.exp (-r)*bandMass μ g r := by
    unfold eventMass bandMass mean
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    dsimp only
    by_cases hx : r < Real.log (g x) ∧ Real.log (g x) ≤ r+1
    · rw [if_pos hx,Set.indicator_of_mem (show Real.log (g x) ∈ Set.Ioc r (r+1) from hx)]
      have hp : Real.exp r ≤ g x := ((Real.lt_log_iff_exp_lt (hg x)).mp hx.1).le
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg (hμ x) (Real.exp_pos (-r)).le)
      have he : Real.exp (-r)*Real.exp r = 1 := by rw [← Real.exp_add]; simp
      calc
        μ x = (μ x*Real.exp (-r))*Real.exp r := by rw [mul_assoc,he,mul_one]
        _ ≤ (μ x*Real.exp (-r))*g x := hh
        _ = _ := by ring
    · rw [if_neg hx,Set.indicator_of_notMem (show Real.log (g x) ∉ Set.Ioc r (r+1) from hx)]; simp
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  calc
    _ ≤ ∑ j ∈ Finset.range J, eventMass μ (fun x => ℓ+j < Real.log (g x) ∧ Real.log (g x) ≤ ℓ+j+1) := hcover
    _ ≤ ∑ j ∈ Finset.range J, Real.exp (-(ℓ+j))*bandMass μ g (ℓ+j) :=
      Finset.sum_le_sum (fun j _ => hb _)
    _ ≤ ∑ j ∈ Finset.range J, Real.exp (-(ℓ+j))*(B/Real.sqrt ℓ) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact (hband _ (by linarith [Nat.cast_nonneg (α := ℝ) j])).trans
        (div_le_div_of_nonneg_left hB hs (Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) j])))
    _ = (Real.exp (-ℓ)*(B/Real.sqrt ℓ))*(∑ j ∈ Finset.range J, Real.exp (-(j:ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [neg_add,Real.exp_add]; ring
    _ ≤ (Real.exp (-ℓ)*(B/Real.sqrt ℓ))*2 :=
      mul_le_mul_of_nonneg_left (sum_exp_neg_le_two J) (by positivity)
    _ = 2*B/(Real.exp ℓ*Real.sqrt ℓ) := by rw [Real.exp_neg]; ring

/-- Complete normalized band-to-tail implication. The only analytic input is
the stated fixed-band estimate; small thresholds use Markov. -/
theorem normalized_tail_from_bands (μ g : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hg : ∀ x, 0 < g x) (hm : mean μ g = 1) {B : ℝ} (hB : 0 ≤ B)
    (hband : ∀ r, 2 < r → bandMass μ g r ≤ B/Real.sqrt r)
    (η : ℝ) (hη : 1 < η) :
    eventMass μ (fun x => η < g x) ≤
      max (Real.sqrt 2) (2*B)/(η*Real.sqrt (Real.log η)) := by
  have hd : 0 < η*Real.sqrt (Real.log η) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr (Real.log_pos hη))
  by_cases hh : Real.log η ≤ 2
  · exact (small_threshold_tail μ g hμ (fun x => (hg x).le) hm η hη hh).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hd.le)
  · have hl : 2 < Real.log η := lt_of_not_ge hh
    have ht := log_tail_from_bands μ g hμ hg (by linarith : 0 < Real.log η) hB
      (fun r hr => hband r (hl.trans_le hr))
    rw [Real.exp_log (by linarith : 0 < η)] at ht
    have he : (fun x => Real.log η < Real.log (g x)) = (fun x => η < g x) := by
      funext x
      exact propext (Real.log_lt_log_iff (by linarith) (hg x))
    rw [he] at ht
    exact ht.trans (div_le_div_of_nonneg_right (le_max_right _ _) hd.le)

end TailBound
