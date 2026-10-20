import TailBound.Coupling

/-!
# Coupling Calculus

Generator identities and Dynkin estimates for the constructed stopped flow.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound

lemma min_add_positive_difference (a b : ℝ) : min a b + max (a - b) 0 = a := by
  rcases le_total a b with h|h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]; ring

lemma sum_jumpKind (f : JumpKind → ℝ) : ∑ k, f k = f .sync + f .left + f .right := by
  have he : (Finset.univ : Finset JumpKind) = {.sync, .left, .right} := by
    ext k; cases k <;> simp
  rw [he]
  simp
  ring

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma couplingNext_start (B : Set (Fin n → α)) (e : CouplingEvent α n) (s : CoupledState α n) :
    (couplingNext B e s).start = s.start := rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma killNode_start (B : Set (Fin n → α)) (s : CoupledState α n) :
    (killNode B s).start = s.start := rfl

namespace RefreshData

variable (D : RefreshData α n)

omit [Nonempty α] in
lemma coupling_generator_expansion (ℓ θ t : ℝ) (B : Set (Fin n → α))
    (F : CoupledState α n → ℝ) (s : CoupledState α n) :
    eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) F s =
      ∑ i, ∑ a, D.π a *
        (min (D.ratio t i a s.v) (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i a s.v)) *
          (F (couplingNext B (.sync, i, a) s) - F s) +
        max (D.ratio t i a s.v - switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i a s.v)) 0 *
          (F (couplingNext B (.left, i, a) s) - F s) +
        max (switchedPower (D.coupledExponent ℓ θ s) (D.ratio t i a s.v) - D.ratio t i a s.v) 0 *
          (F (couplingNext B (.right, i, a) s) - F s)) := by
  unfold eventGenerator
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_jumpKind]
  unfold couplingRate
  ring

omit [Nonempty α] in
/-- The V marginal has the reverse generator. -/
lemma coupling_generator_v (ℓ θ t : ℝ) (B : Set (Fin n → α))
    (F : (Fin n → α) → ℝ) (s : CoupledState α n) :
    eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (fun r => F r.v) s =
      D.revGen t F s.v := by
  rw [D.coupling_generator_expansion]
  unfold revGen mean
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  simp only [couplingNext, sub_self, mul_zero, add_zero]
  rw [← add_mul, min_add_positive_difference]

omit [Nonempty α] in
lemma coupling_generator_start (ℓ θ t : ℝ) (B : Set (Fin n → α))
    (F : (Fin n → α) → ℝ) (s : CoupledState α n) :
    eventGenerator (couplingNext B) (D.couplingRate ℓ θ t) (fun r => F r.start) s = 0 := by
  simp [eventGenerator, couplingNext_start]

namespace StoppedCoupling

variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def pairing (k : ℕ) (t : ℝ) (F : CoupledState α n → ℝ) : ℝ :=
  ∑ s, C.law k t s * F s

omit [Nonempty α] in
lemma pairing_continuous {k : ℕ} (hk : k < C.grid.K) (F : ℝ → CoupledState α n → ℝ)
    (hF : ∀ s, ContinuousOn (fun t => F t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1)))) :
    ContinuousOn (fun t => C.pairing k t (F t)) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) := by
  apply continuousOn_finset_sum
  intro s _
  exact ((C.flow.flow k hk).cont s).mul (hF s)

omit [Nonempty α] in
lemma pairing_node (k : ℕ) (hk : k + 1 < C.grid.K) (F : CoupledState α n → ℝ) :
    C.pairing (k + 1) (C.grid.z (k + 1)) F =
      C.pairing k (C.grid.z (k + 1)) (fun s => F (killNode (D.barrier ℓ (C.grid.z (k + 1))) s)) := by
  unfold pairing
  rw [C.flow.node k hk]
  exact mapTransfer_pairing _ _ F

omit [Nonempty α] in
lemma pairing_initial (F : CoupledState α n → ℝ) :
    C.pairing 0 (C.grid.z 0) F =
      ∑ x, D.density θ x * F (killNode (D.barrier ℓ θ) ⟨x, x, x, true⟩) := by
  unfold pairing
  rw [C.flow.init]
  change (∑ s, Talagrand.matVec (mapTransfer (killNode (D.barrier ℓ (C.grid.z 0))))
    (D.initialCoupling θ) s * F s) = _
  rw [mapTransfer_pairing, D.initialCoupling_pairing]
  simp only [C.grid.first]

omit [Nonempty α] in
/-- Exact conservation of every function of the starting point. -/
theorem start_pairing (F : (Fin n → α) → ℝ) :
    ∑ s, C.terminal s * F s.start = ∑ x, D.density θ x * F x := by
  have hd (k : ℕ) (hk : k<C.grid.K) (t : ℝ)
      (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) :
      HasDerivWithinAt (fun u => C.pairing k u (fun s => F s.start)) 0
        (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) t := by
    have hh := eventFlow_derivative _ _ (couplingNext (D.cellBarrier C.grid k))
      (D.couplingRate ℓ θ) (C.law k) (C.flow.flow k hk)
      (fun _ s => F s.start) (fun _ _ => 0)
      (fun t _ s => hasDerivWithinAt_const t _ _) t ht
    simpa only [D.coupling_generator_start, add_zero, mul_zero, Finset.sum_const_zero, pairing] using hh
  have hh := Talagrand.chain_eq C.grid.pos C.grid.mono
    (fun k hk => C.pairing_continuous hk (fun _ s => F s.start) (fun _ => continuousOn_const))
    hd (fun k hk => intervalIntegral.intervalIntegrable_const)
    (fun k hk => by rw [C.pairing_node k hk]; simp only [killNode_start])
  simp only [intervalIntegral.integral_zero, Finset.sum_const_zero, add_zero] at hh
  rw [C.pairing_initial] at hh
  simpa only [C.grid.last, pairing, terminal, killNode_start] using hh

omit [Nonempty α] in
/-- Integrated Dynkin inequality, including killing at grid nodes. -/
theorem dynkin_le (hθ : θ ≤ 2) (F dF H : ℝ → CoupledState α n → ℝ)
    (J : (Fin n → α) → ℝ)
    (hder : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) t)
    (hH : ∀ k, k<C.grid.K → ∀ s,
      ContinuousOn (fun t => H t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))))
    (hbound : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      C.law k t s ≠ 0 →
      dF t s + eventGenerator (couplingNext (D.cellBarrier C.grid k))
        (D.couplingRate ℓ θ t) (F t) s ≤ H t s)
    (hkill : ∀ k, k + 1<C.grid.K → ∀ s, C.law k (C.grid.z (k + 1)) s ≠ 0 →
      F (C.grid.z (k + 1)) (killNode (D.barrier ℓ (C.grid.z (k + 1))) s) ≤
        F (C.grid.z (k + 1)) s)
    (hinit : C.pairing 0 (C.grid.z 0) (F (C.grid.z 0)) ≤ ∑ x, D.density θ x * J x) :
    (∑ s, C.terminal s * F 2 s) ≤
      (∑ x, D.density θ x * J x) +
      ∑ k ∈ Finset.range C.grid.K, ∫ t in C.grid.z k..C.grid.z (k + 1), C.pairing k t (H t) := by
  have hF (k : ℕ) (hk : k<C.grid.K) (s : CoupledState α n) :
      ContinuousOn (fun t => F t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) :=
    fun t ht => (hder k hk t ht s).continuousWithinAt
  have hd (k : ℕ) (hk : k<C.grid.K) (t : ℝ)
      (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) :
      ∃ v ≤ C.pairing k t (H t), HasDerivWithinAt (fun u => C.pairing k u (F u)) v
        (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) t := by
    refine ⟨_, ?_, eventFlow_derivative _ _ _ _ _ (C.flow.flow k hk) F dF (hder k hk) t ht⟩
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : C.law k t s = 0
    · simp [hs]
    · exact mul_le_mul_of_nonneg_left (hbound k hk t ht s hs) (C.nonneg hθ hk t ht s)
  have hnode (k : ℕ) (hk : k + 1<C.grid.K) :
      C.pairing (k + 1) (C.grid.z (k + 1)) (F (C.grid.z (k + 1))) ≤
        C.pairing k (C.grid.z (k + 1)) (F (C.grid.z (k + 1))) := by
    rw [C.pairing_node k hk]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : C.law k (C.grid.z (k + 1)) s = 0
    · simp [hs]
    · exact mul_le_mul_of_nonneg_left (hkill k hk s hs)
        (C.nonneg hθ (by omega) _ ⟨C.grid.mono k (by omega), le_rfl⟩ s)
  have hh := Talagrand.chain_le C.grid.pos C.grid.mono
    (fun k hk => C.pairing_continuous hk F (hF k hk)) hd
    (fun k hk => (by
      rw [Set.uIcc_of_le (C.grid.mono k hk)]
      exact C.pairing_continuous hk H (hH k hk) :
        ContinuousOn (fun t => C.pairing k t (H t))
          (Set.uIcc (C.grid.z k) (C.grid.z (k + 1)))).intervalIntegrable) hnode
  have hout : C.pairing (C.grid.K - 1) (C.grid.z C.grid.K) (F (C.grid.z C.grid.K)) =
      ∑ s, C.terminal s * F 2 s := by simp only [C.grid.last, pairing, terminal]
  rw [hout] at hh
  exact hh.trans (add_le_add hinit le_rfl)

end StoppedCoupling
end RefreshData
end TailBound
