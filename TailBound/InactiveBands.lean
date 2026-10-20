import TailBound.LayerAveraging

/-!
# Inactive Bands

The inactive starting event, using the same exponential
inverse-density bound as in the Boolean fixed-band proof.
-/
open scoped BigOperators

namespace TailBound.RefreshData
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

omit [Nonempty α]

variable (D : RefreshData α n)

lemma exists_uniform_log_bound : ∃ B : ℝ, ∀ t, t ≤ 2 → ∀ x, D.logP t x ≤ B := by
  let B := ∑ x : Fin n → α, |Real.log (tensorWeight D.π n x)|
  refine ⟨B, fun t ht x => ?_⟩
  have hw : 0 < tensorWeight D.π n x := Finset.prod_pos (fun i _ => D.πpos (x i))
  have hp := D.p_pos (ht.trans D.obs_le_horizon) x
  have hd : D.density t x ≤ 1 := by
    rw [← D.density_mass t]
    exact Finset.single_le_sum (fun y _ => D.density_nonneg (ht.trans D.obs_le_horizon) y) (Finset.mem_univ x)
  have hh := Real.log_le_log (mul_pos hw hp) hd
  rw [Real.log_one, Real.log_mul hw.ne' hp.ne'] at hh
  have hs := Finset.single_le_sum (f := fun x : Fin n → α => |Real.log (tensorWeight D.π n x)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
  change D.logP t x ≤ B
  change |Real.log (tensorWeight D.π n x)| ≤ B at hs
  change Real.log (tensorWeight D.π n x) + D.logP t x ≤ 0 at hh
  linarith [neg_le_abs (Real.log (tensorWeight D.π n x))]

lemma exists_start_cutoff (ℓ : ℝ) : ∃ Q : ℕ, ∀ θ, θ ≤ 2 → ∀ x,
    D.logP θ x ≤ ℓ - 10 + Q := by
  obtain ⟨B, hB⟩ := D.exists_uniform_log_bound
  obtain ⟨Q, hQ⟩ := exists_nat_gt (B - ℓ + 10)
  exact ⟨Q, fun θ hθ x => by linarith [hB θ hθ x]⟩

namespace StoppedCoupling

variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def inactiveBand (r : ℝ) : ℝ := eventMass C.terminal
  (fun s => ¬10 ≤ D.gap ℓ θ s.start ∧ r < D.logP 2 s.v ∧ D.logP 2 s.v ≤ r + 1)

lemma profile_split (hθ : θ ≤ 2) (r : ℝ) :
    D.startBand 2 r = C.bandA r + C.inactiveBand r := by
  have hh := C.v_marginal hθ (fun x => if r < D.logP 2 x ∧ D.logP 2 x ≤ r + 1 then 1 else 0)
  change _ = D.startBand 2 r at hh
  rw [← hh]
  unfold bandA inactiveBand eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  dsimp only
  by_cases ha : 10 ≤ D.gap ℓ θ s.start <;>
    by_cases hb : r < D.logP 2 s.v ∧ D.logP 2 s.v ≤ r + 1 <;> simp [ha, hb]

lemma bandA_nonneg (hθ : θ ≤ 2) (r : ℝ) : 0 ≤ C.bandA r :=
  eventMass_nonneg _ (C.terminal_nonneg hθ) _

lemma inactiveBand_nonneg (hθ : θ ≤ 2) (r : ℝ) : 0 ≤ C.inactiveBand r :=
  eventMass_nonneg _ (C.terminal_nonneg hθ) _

lemma bandA_le_profile (hθ : θ ≤ 2) (r : ℝ) : C.bandA r ≤ D.startBand 2 r := by
  rw [C.profile_split hθ]
  linarith [C.inactiveBand_nonneg hθ r]

theorem inactive_band_bound (hθ : θ ≤ 2) (Q : ℕ)
    (hQ : ∀ x, D.logP θ x ≤ ℓ - 10 + Q) :
    C.inactiveBand ℓ ≤ ∑ q ∈ Finset.range Q,
      Real.exp (11 - (q : ℝ)) * D.startBand θ (ℓ - 10 + q) := by
  let a (q : ℕ) (x : Fin n → α) : ℝ :=
    if ℓ - 10 + q < D.logP θ x ∧ D.logP θ x ≤ ℓ - 10 + q + 1 then 1 else 0
  have ha (q : ℕ) (x : Fin n → α) : 0 ≤ a q x := by dsimp [a]; split_ifs <;> norm_num
  have hcover : C.inactiveBand ℓ ≤ ∑ q ∈ Finset.range Q,
      ∑ s, C.terminal s * (a q s.start * (if D.logP 2 s.v ≤ ℓ + 1 then 1 else 0)) := by
    unfold inactiveBand eventMass
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : ¬10 ≤ D.gap ℓ θ s.start ∧ ℓ < D.logP 2 s.v ∧ D.logP 2 s.v ≤ ℓ + 1
    · have hg : ℓ - 10 < D.logP θ s.start := by
        have hh := lt_of_not_ge hs.1
        have hm := le_max_left (ℓ - D.logP θ s.start) 0
        change D.gap ℓ θ s.start < 10 at hh
        dsimp [gap] at hh
        linarith
      obtain ⟨q, hq, hlo, hhi⟩ := TailBound.finite_band_index hg (hQ s.start)
      rw [if_pos hs]
      have hh := Finset.single_le_sum
        (f := fun q => C.terminal s * (a q s.start * (if D.logP 2 s.v ≤ ℓ + 1 then 1 else 0)))
        (fun q _ => by dsimp only; apply mul_nonneg (C.terminal_nonneg hθ s); apply mul_nonneg (ha q s.start); split_ifs <;> norm_num) hq
      simpa [a, hlo, hhi, hs.2.2] using hh
    · rw [if_neg hs]
      apply Finset.sum_nonneg
      intro q _
      exact mul_nonneg (C.terminal_nonneg hθ s) (mul_nonneg (ha q s.start) (by split_ifs <;> norm_num))
  apply hcover.trans
  apply Finset.sum_le_sum
  intro q _
  have hh := C.high_start_tail hθ (a q) (ha q) (ℓ + 1) (ℓ - 10 + q) (fun x hx => by
    dsimp [a] at hx
    split_ifs at hx with h
    · exact h.1.le
    · contradiction)
  have he : ℓ + 1 - (ℓ - 10 + (q : ℝ)) = 11 - (q : ℝ) := by ring
  simpa only [he, startBand, a] using hh

end StoppedCoupling
end TailBound.RefreshData
