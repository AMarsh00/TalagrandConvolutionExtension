import TailBound.BandEvents

/-! A finite partition of every strict upper tail into unit bands. -/
open scoped BigOperators
namespace TailBound
attribute [local instance] Classical.propDecidable

lemma exists_unit_band {x ℓ : ℝ} (hx : ℓ+1 < x) :
    ∃ j : ℕ, 1 ≤ j ∧ ℓ+j < x ∧ x ≤ ℓ+j+1 := by
  let k := Nat.ceil (x-ℓ)
  have hk : 1 < k := Nat.lt_ceil.mpr (by norm_num; linarith)
  have he : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  refine ⟨k-1,by omega,?_,?_⟩
  · have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ x-ℓ)
    rw [he]
    change (k:ℝ) < x-ℓ+1 at hh
    linarith
  · have hh := Nat.le_ceil (x-ℓ)
    rw [he]
    change x-ℓ ≤ (k:ℝ) at hh
    linarith

lemma exists_bounded_unit_band {x ℓ : ℝ} {M : ℕ} (hx : ℓ+1 < x) (hM : x ≤ ℓ+M+1) :
    ∃ j ∈ Finset.Icc 1 M, ℓ+j < x ∧ x ≤ ℓ+j+1 := by
  obtain ⟨j,hj,hlo,hhi⟩ := exists_unit_band hx
  have hjM : j ≤ M := by
    by_contra hn
    have hjM : M+1 ≤ j := by omega
    have hc : ((M+1:ℕ):ℝ) ≤ j := by exact_mod_cast hjM
    push_cast at hc
    linarith
  exact ⟨j,Finset.mem_Icc.mpr ⟨hj,hjM⟩,hlo,hhi⟩

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
namespace RefreshData.StoppedCoupling
variable {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def forwardCrossing : ℝ := eventMass C.terminal
  (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.w ∧ D.logP 2 s.v ≤ ℓ+1)
noncomputable def reverseCrossing : ℝ := eventMass C.terminal
  (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.v ∧ D.logP 2 s.w ≤ ℓ+1)

lemma forwardCrossing_bound (hθ : θ ≤ 2) (M : ℕ) (hM : ∀ x, D.logP 2 x ≤ ℓ+M+1) :
    C.forwardCrossing ≤ ∑ j ∈ Finset.Icc 1 M, C.crossing j := by
  unfold forwardCrossing crossing eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.w ∧ D.logP 2 s.v ≤ ℓ+1
  · obtain ⟨j,hj,hlo,hhi⟩ := exists_bounded_unit_band hs.2.1 (hM s.w)
    rw [if_pos hs]
    have hh := Finset.single_le_sum (f := fun j : ℕ =>
      if 10 ≤ D.gap ℓ θ s.start ∧ ℓ+j < D.logP 2 s.w ∧ D.logP 2 s.w ≤ ℓ+j+1 ∧ D.logP 2 s.v ≤ ℓ+1
      then C.terminal s else 0) (s := Finset.Icc 1 M)
      (fun j _ => by dsimp; split_ifs <;> first | exact C.terminal_nonneg hθ s | exact le_rfl) hj
    dsimp only at hh
    rw [if_pos ⟨hs.1,hlo,hhi,hs.2.2⟩] at hh
    apply hh.trans_eq
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 10 ≤ D.gap ℓ θ s.start ∧ ℓ+i < D.logP 2 s.w ∧ D.logP 2 s.w ≤ ℓ+i+1 ∧ D.logP 2 s.v ≤ ℓ+1
    · rw [if_pos hi,if_pos hi]
    · rw [if_neg hi,if_neg hi]
  · rw [if_neg hs]
    exact Finset.sum_nonneg (fun j _ => by dsimp; split_ifs <;> first | exact C.terminal_nonneg hθ s | exact le_rfl)

lemma reverseCrossing_le (hθ : θ ≤ 2) :
    C.reverseCrossing ≤ C.forwardCrossing+C.eventTV {x | 10 ≤ D.gap ℓ θ x} := by
  have ht := C.event_difference_le_tv {x | 10 ≤ D.gap ℓ θ x} {x | ℓ+1 < D.logP 2 x}
  have he : eventMass C.terminal (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.w)-
      eventMass C.terminal (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.v) =
      C.forwardCrossing-C.reverseCrossing := by
    unfold forwardCrossing reverseCrossing eventMass
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases ha : 10 ≤ D.gap ℓ θ s.start <;>
      by_cases hw : ℓ+1 < D.logP 2 s.w <;> by_cases hv : ℓ+1 < D.logP 2 s.v <;>
      simp only [ha,hw,hv,and_true,and_false,true_and,false_and,if_true,if_false] <;> split_ifs <;> simp_all <;> linarith
  change |eventMass C.terminal (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.w)-
      eventMass C.terminal (fun s => 10 ≤ D.gap ℓ θ s.start ∧ ℓ+1 < D.logP 2 s.v)| ≤ _ at ht
  rw [he] at ht
  have hh := (abs_le.mp ht).1
  linarith

lemma bandB_le (hθ : θ ≤ 2) : C.bandB ℓ ≤ C.crossing 0+C.reverseCrossing := by
  unfold bandB crossing reverseCrossing eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  simp only [add_zero]
  have hμ := C.terminal_nonneg hθ s
  split_ifs <;> simp_all <;> linarith


lemma bandA_le_bandB_tv (r : ℝ) :
    C.bandA r ≤ C.bandB r+C.eventTV {x | 10 ≤ D.gap ℓ θ x} := by
  have hh := C.event_difference_le_tv {x | 10 ≤ D.gap ℓ θ x}
    {x | r < D.logP 2 x ∧ D.logP 2 x ≤ r+1}
  change |C.bandB r-C.bandA r| ≤ _ at hh
  linarith [(abs_le.mp hh).1]

/-- Finite-sum band contraction; all larger bands are empty when hM holds. -/
theorem band_contraction (hθ : θ ≤ 2) (M : ℕ) (hM : ∀ x, D.logP 2 x ≤ ℓ+M+1) :
    (1-Real.exp (-4))*C.bandA ℓ ≤
      Real.exp (-4)*(∑ j ∈ Finset.Icc 1 M, Real.exp (-(j:ℝ))*C.bandA (ℓ+j))+
        2*C.eventTV {x | 10 ≤ D.gap ℓ θ x} := by
  have hA := C.bandA_le_bandB_tv ℓ
  have hB := C.bandB_le hθ
  have hR := C.reverseCrossing_le hθ
  have hF := C.forwardCrossing_bound hθ M hM
  have hzero := C.crossing_bound hθ 0
  simp only [sub_zero,add_zero] at hzero
  have hsum : (∑ j ∈ Finset.Icc 1 M, C.crossing j) ≤
      Real.exp (-4)*(∑ j ∈ Finset.Icc 1 M, Real.exp (-(j:ℝ))*C.bandA (ℓ+j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hh := C.crossing_bound hθ j
    simpa only [sub_eq_add_neg,Real.exp_add,mul_assoc] using hh
  nlinarith

lemma exists_band_cutoff : ∃ M : ℕ, ∀ x, D.logP 2 x ≤ ℓ+M+1 := by
  let b := (Finset.univ : Finset (Fin n → α)).sup' Finset.univ_nonempty (D.logP 2)
  obtain ⟨M,hM⟩ := exists_nat_gt (b-ℓ)
  refine ⟨M,fun x => ?_⟩
  have hx : D.logP 2 x ≤ b := Finset.le_sup' (f := D.logP 2) (Finset.mem_univ x)
  linarith

/-- No cutoff hypothesis is needed: finiteness supplies a cutoff for each input. -/
theorem band_contraction_finite (hθ : θ ≤ 2) : ∃ M : ℕ,
    (∀ x, D.logP 2 x ≤ ℓ+M+1) ∧
    (1-Real.exp (-4))*C.bandA ℓ ≤
      Real.exp (-4)*(∑ j ∈ Finset.Icc 1 M, Real.exp (-(j:ℝ))*C.bandA (ℓ+j))+
        2*C.eventTV {x | 10 ≤ D.gap ℓ θ x} := by
  obtain ⟨M,hM⟩ := exists_band_cutoff (D := D) (ℓ := ℓ)
  exact ⟨M,hM,C.band_contraction hθ M hM⟩

end RefreshData.StoppedCoupling
end TailBound
