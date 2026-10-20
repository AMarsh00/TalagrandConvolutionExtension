import TailBound.CouplingSupport

/-!
# Stopped Score

The stopped-score estimate, with the overshoot term `1 + log κ`.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

namespace RefreshData

variable (D : RefreshData α n)

omit [DecidableEq α] in
lemma logκ_pos : 0 < Real.log D.κ := Real.log_pos D.κ_gt_one

omit [Nonempty α] in
lemma active_gap {ℓ θ : ℝ} {x : Fin n → α} (hx : 10 ≤ D.gap ℓ θ x) :
    D.gap ℓ θ x = ℓ - D.logP θ x ∧ D.logP θ x ≤ ℓ - 10 := by
  have hp : 0 < ℓ - D.logP θ x := by
    by_contra hn
    have hz : D.gap ℓ θ x = 0 := max_eq_right (le_of_not_gt hn)
    rw [hz] at hx
    norm_num at hx
  exact ⟨max_eq_left hp.le, by rw [gap, max_eq_left hp.le] at hx; linarith⟩

lemma event_log_overshoot {ℓ t : ℝ} (ht : t ≤ 2) (B : Set (Fin n → α))
    (e : CouplingEvent α n) (s : CoupledState α n) (hs : D.logP t s.v ≤ ℓ + 1) :
    D.logP t (couplingNext B e s).v ≤ ℓ + 1 + Real.log D.κ := by
  have hu : D.logP t (Function.update s.v e.2.1 e.2.2) ≤ ℓ + 1 + Real.log D.κ := by
    have hh := Real.log_le_log (D.ratio_pos (ht.trans D.obs_le_horizon) e.2.1 e.2.2 s.v)
      (D.ratio_bounds ht e.2.1 e.2.2 s.v).2
    rw [← D.logP_update (ht.trans D.obs_le_horizon)] at hh
    linarith
  cases he : e.1 <;> simp only [couplingNext, he]
  · exact hu
  · exact hu
  · linarith [D.logκ_pos]

noncomputable def remainingGap (ℓ t : ℝ) (s : CoupledState α n) : ℝ :=
  if s.alive then ℓ + 1 + Real.log D.κ - D.logP t s.v else 0

noncomputable def remainingGapDeriv (t : ℝ) (s : CoupledState α n) : ℝ :=
  if s.alive then refreshGenerator D.π (D.p t) s.v / D.p t s.v else 0

omit [Nonempty α] in
lemma hasDerivAt_remainingGap {t : ℝ} (ht : t ≤ D.horizon) (ℓ : ℝ)
    (s : CoupledState α n) :
    HasDerivAt (fun u => D.remainingGap ℓ u s) (D.remainingGapDeriv t s) t := by
  unfold remainingGap remainingGapDeriv
  split_ifs
  · convert (D.hasDerivAt_logP ht s.v).const_sub (ℓ + 1 + Real.log D.κ) using 1; ring
  · exact hasDerivAt_const t 0

lemma remainingGap_generator {ℓ θ t : ℝ} (ht : t ≤ 2) (B : Set (Fin n → α))
    (s : CoupledState α n) (hs : s.alive = true → D.logP t s.v ≤ ℓ + 1) :
    eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (D.remainingGap ℓ t) s ≤
      if s.alive then - D.revGen t (D.logP t) s.v else 0 := by
  classical
  by_cases ha : s.alive = true
  · simp only [ha, if_true]
    have he (e : CouplingEvent α n) :
        D.remainingGap ℓ t (couplingNext B e s) - D.remainingGap ℓ t s ≤
          -(D.logP t (couplingNext B e s).v - D.logP t s.v) := by
      unfold remainingGap
      simp only [ha, if_true]
      split_ifs
      · ring_nf; exact le_rfl
      · linarith [D.event_log_overshoot ht B e s (hs ha)]
    calc
      _ ≤ ∑ e, D.couplingRate ℓ θ t e s *
          -(D.logP t (couplingNext B e s).v - D.logP t s.v) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (he e)
          (D.couplingRate_nonneg ℓ θ t (ht.trans D.obs_le_horizon) e s))
      _ = -eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (fun r => D.logP t r.v) s := by
        simp only [eventGenerator, mul_neg, Finset.sum_neg_distrib]
      _ = _ := by rw [D.coupling_generator_v]
  · have haf : s.alive = false := Bool.eq_false_iff.mpr ha
    have hn (e : CouplingEvent α n) : (couplingNext B e s).alive = false := by
      cases e.1 <;> simp [couplingNext, haf]
    simp [eventGenerator, remainingGap, ha, hn]

omit [Nonempty α] in
lemma coupling_generator_start_mul (ℓ θ t : ℝ) (B : Set (Fin n → α))
    (a : (Fin n → α) → ℝ) (F : CoupledState α n → ℝ) (s : CoupledState α n) :
    eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (fun r => a r.start * F r) s =
      a s.start * eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) F s := by
  unfold eventGenerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [couplingNext_start]
  ring

lemma remainingGap_drift {ℓ θ t : ℝ} (ht : t ≤ 2) (B : Set (Fin n → α))
    (s : CoupledState α n) (hs : s.alive = true → D.logP t s.v ≤ ℓ + 1) :
    2 * (D.κ - 1) * (D.remainingGapDeriv t s +
      eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (D.remainingGap ℓ t) s) ≤
      -Real.log D.κ * (if s.alive then D.score t s.v else 0) := by
  have hg := D.remainingGap_generator (θ := θ) ht B s hs
  have hc : 0 < 2 * (D.κ - 1) := mul_pos (by norm_num) (sub_pos.mpr D.κ_gt_one)
  by_cases ha : s.alive = true
  · simp only [remainingGapDeriv, ha, if_true] at hg ⊢
    have hh := D.score_drift ht s.v
    have hgg := mul_le_mul_of_nonneg_left hg hc.le
    simp only [neg_div] at hh
    nlinarith
  · simp [remainingGapDeriv, ha] at hg ⊢
    exact mul_nonpos_of_nonneg_of_nonpos hc.le hg

omit [Nonempty α] in
lemma score_continuousOn : ∀ x, ContinuousOn (fun t => D.score t x) (Set.Iic D.horizon) := by
  intro x
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro a _
  exact (((D.continuousOn_ratio i a x).sub continuousOn_const).pow 2).const_mul _

omit [Nonempty α] in
lemma remainingGap_kill_le (ℓ t : ℝ) (B : Set (Fin n → α)) (s : CoupledState α n)
    (hs : 0 ≤ D.remainingGap ℓ t s) :
    D.remainingGap ℓ t (killNode B s) ≤ D.remainingGap ℓ t s := by
  classical
  by_cases h : s.v ∈ B
  · simpa [remainingGap, killNode, h] using hs
  · simp [remainingGap, killNode, h]

namespace StoppedCoupling

variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

lemma remainingGap_nonneg (hθ : θ ≤ 2) {k : ℕ} (hk : k<C.grid.K) (t : ℝ)
    (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) (s : CoupledState α n)
    (hs : C.law k t s ≠ 0) : 0 ≤ D.remainingGap ℓ t s := by
  unfold remainingGap
  split_ifs with ha
  · linarith [C.active_log_bound hθ hk t ht s hs ha, D.logκ_pos]
  · exact le_rfl

noncomputable def scoreWork (a : (Fin n → α) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range C.grid.K, ∫ t in C.grid.z k..C.grid.z (k + 1),
    C.pairing k t (fun s => a s.start * (if s.alive then D.score t s.v else 0))

/-- The stopped-score estimate in localized integral form. Taking a singleton starting event
gives its conditional form; arbitrary nonnegative weights are allowed. -/
theorem stopped_score (hθ : θ ≤ 2) (a : (Fin n → α) → ℝ)
    (ha : ∀ x, 0 ≤ a x) :
    C.scoreWork a ≤ (2 * (D.κ - 1) / Real.log D.κ) *
      ∑ x, D.density θ x * a x * (D.gap ℓ θ x + 1 + Real.log D.κ) := by
  classical
  let c := 2 * (D.κ - 1)
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (sub_nonneg.mpr D.κ_gt_one.le)
  let F : ℝ → CoupledState α n → ℝ := fun t s => c * a s.start * D.remainingGap ℓ t s
  let dF : ℝ → CoupledState α n → ℝ := fun t s => c * a s.start * D.remainingGapDeriv t s
  let H : ℝ → CoupledState α n → ℝ := fun t s =>
    -Real.log D.κ * (a s.start * (if s.alive then D.score t s.v else 0))
  have hd : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) t := by
    intro k hk t ht s
    exact ((D.hasDerivAt_remainingGap
      (((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon) ℓ s).const_mul _).hasDerivWithinAt
  have hH : ∀ k, k<C.grid.K → ∀ s,
      ContinuousOn (fun t => H t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) := by
    intro k hk s
    dsimp [H]
    apply ContinuousOn.const_mul
    apply ContinuousOn.const_mul
    split_ifs
    · exact (D.score_continuousOn s.v).mono
        (fun t ht => ((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon)
    · exact continuousOn_const
  have hbound : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      C.law k t s ≠ 0 → dF t s + eventGenerator (couplingNext (D.cellBarrier C.grid k))
        (D.couplingRate ℓ θ t) (F t) s ≤ H t s := by
    intro k hk t ht s hs
    have hh := D.remainingGap_drift (θ := θ) (C.grid.cell_subset hk ht).2
      (D.cellBarrier C.grid k) s (C.active_log_bound hθ hk t ht s hs)
    have hh' := mul_le_mul_of_nonneg_left hh (ha s.start)
    dsimp [F, dF, H]
    rw [D.coupling_generator_start_mul ℓ θ t (D.cellBarrier C.grid k)
      (fun x => c * a x) (D.remainingGap ℓ t)]
    dsimp [c] at *
    nlinarith
  have hkill : ∀ k, k + 1<C.grid.K → ∀ s, C.law k (C.grid.z (k + 1)) s ≠ 0 →
      F (C.grid.z (k + 1)) (killNode (D.barrier ℓ (C.grid.z (k + 1))) s) ≤ F (C.grid.z (k + 1)) s := by
    intro k hk s hs
    exact mul_le_mul_of_nonneg_left
      (D.remainingGap_kill_le _ _ _ s
        (C.remainingGap_nonneg hθ (by omega) _ ⟨C.grid.mono k (by omega), le_rfl⟩ s hs))
      (mul_nonneg hc (ha s.start))
  let J : (Fin n → α) → ℝ := fun x => c * a x * (D.gap ℓ θ x + 1 + Real.log D.κ)
  have hinit : C.pairing 0 (C.grid.z 0) (F (C.grid.z 0)) ≤ ∑ x, D.density θ x * J x := by
    rw [C.pairing_initial]
    simp only [C.grid.first]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (D.density_nonneg (hθ.trans D.obs_le_horizon) x)
    dsimp [F, J]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (ha x))
    unfold remainingGap killNode
    split_ifs
    · have hh : ℓ - D.logP θ x ≤ D.gap ℓ θ x := le_max_left _ _
      linarith
    · have hh : 0 ≤ D.gap ℓ θ x := le_max_right _ _
      linarith [D.logκ_pos]
  have hdyn := C.dynkin_le hθ F dF H J hd hH hbound hkill hinit
  have hterm : 0 ≤ ∑ s, C.terminal s * F 2 s := by
    apply Finset.sum_nonneg
    intro s _
    by_cases hs : C.terminal s = 0
    · simp [hs]
    · apply mul_nonneg (C.terminal_nonneg hθ s)
      apply mul_nonneg (mul_nonneg hc (ha s.start))
      apply C.remainingGap_nonneg hθ (show C.grid.K - 1<C.grid.K by have := C.grid.pos; omega) 2 _ s hs
      have he : C.grid.K - 1 + 1=C.grid.K := by have := C.grid.pos; omega
      rw [he, C.grid.last]
      exact ⟨(C.grid.range (by omega)).2, le_rfl⟩
  have hsource : (∑ k ∈ Finset.range C.grid.K,
      ∫ t in C.grid.z k..C.grid.z (k + 1), C.pairing k t (H t)) = -Real.log D.κ * C.scoreWork a := by
    have he (k : ℕ) (t : ℝ) : C.pairing k t (H t) = -Real.log D.κ *
        C.pairing k t (fun s => a s.start * (if s.alive then D.score t s.v else 0)) := by
      unfold pairing H
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    simp_rw [he, intervalIntegral.integral_const_mul]
    simp only [scoreWork, Finset.mul_sum]
  have hJ : (∑ x, D.density θ x * J x) =
      c*∑ x, D.density θ x * a x * (D.gap ℓ θ x + 1 + Real.log D.κ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [J]
    ring
  rw [hsource, hJ] at hdyn
  have hb : Real.log D.κ * C.scoreWork a ≤
      c*∑ x, D.density θ x * a x * (D.gap ℓ θ x + 1 + Real.log D.κ) := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ D.logκ_pos).mpr
  simpa only [mul_comm (Real.log D.κ), c] using hb

end StoppedCoupling

end RefreshData
end TailBound
