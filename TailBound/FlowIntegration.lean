import TailBound.DoobCalculus

/-!
# Flow Integration

Integrated Dynkin identities and localization for the finite stopped flow.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound.RefreshData.StoppedCoupling

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  {D : RefreshData α n} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

noncomputable def integrate (F : ℝ → CoupledState α n → ℝ) : ℝ :=
  ∑ k ∈ Finset.range C.grid.K, ∫ t in C.grid.z k..C.grid.z (k + 1), C.pairing k t (F t)

def CellContinuous (F : ℝ → CoupledState α n → ℝ) : Prop :=
  ∀ k, k<C.grid.K → ∀ s, ContinuousOn (fun t => F t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1)))

omit [Nonempty α] in
lemma pairing_integrable {F : ℝ → CoupledState α n → ℝ} (hF : C.CellContinuous F)
    {k : ℕ} (hk : k<C.grid.K) :
    IntervalIntegrable (fun t => C.pairing k t (F t)) volume (C.grid.z k) (C.grid.z (k + 1)) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (C.grid.mono k hk)]
  exact C.pairing_continuous hk F (hF k hk)

omit [Nonempty α] in
lemma integrate_add {F G : ℝ → CoupledState α n → ℝ}
    (hF : C.CellContinuous F) (hG : C.CellContinuous G) :
    C.integrate (fun t s => F t s + G t s) = C.integrate F + C.integrate G := by
  unfold integrate
  have he (k : ℕ) (t : ℝ) : C.pairing k t (fun s => F t s + G t s) =
      C.pairing k t (F t) + C.pairing k t (G t) := by simp [pairing, mul_add, Finset.sum_add_distrib]
  simp_rw [he]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact intervalIntegral.integral_add (C.pairing_integrable hF (Finset.mem_range.mp hk))
    (C.pairing_integrable hG (Finset.mem_range.mp hk))

omit [Nonempty α] in
lemma integrate_smul (c : ℝ) (F : ℝ → CoupledState α n → ℝ) :
    C.integrate (fun t s => c * F t s) = c * C.integrate F := by
  unfold integrate
  have he (k : ℕ) (t : ℝ) : C.pairing k t (fun s => c * F t s) = c * C.pairing k t (F t) := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum]

omit [Nonempty α] in
lemma integrate_nonneg (hθ : θ ≤ 2) (F : ℝ → CoupledState α n → ℝ)
    (hF : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      C.law k t s ≠ 0 → 0 ≤ F t s) : 0 ≤ C.integrate F := by
  apply Finset.sum_nonneg
  intro k hk
  have hk' := Finset.mem_range.mp hk
  apply intervalIntegral.integral_nonneg (C.grid.mono k hk')
  intro t ht
  apply Finset.sum_nonneg
  intro s _
  by_cases hs : C.law k t s = 0
  · simp [hs]
  · exact mul_nonneg (C.nonneg hθ hk' t ht s) (hF k hk' t ht s hs)

omit [Nonempty α] in
lemma start_pairing_at (a : (Fin n → α) → ℝ) {k : ℕ} (hk : k<C.grid.K) (t : ℝ)
    (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) :
    C.pairing k t (fun s => a s.start) = ∑ x, D.density θ x * a x := by
  have hlocal (j : ℕ) (hj : j<C.grid.K) : ∀ u ∈ Set.Icc (C.grid.z j) (C.grid.z (j + 1)),
      C.pairing j u (fun s => a s.start) = C.pairing j (C.grid.z j) (fun s => a s.start) := by
    apply constant_of_has_deriv_right_zero
      (C.pairing_continuous hj (fun _ s => a s.start) (fun _ => continuousOn_const))
    intro u hu
    have hh := eventFlow_derivative _ _ _ _ _ (C.flow.flow j hj)
      (fun _ s => a s.start) (fun _ _ => 0)
      (fun v _ s => hasDerivWithinAt_const v _ _) u ⟨hu.1, hu.2.le⟩
    have hz : (∑ s, C.law j u s * (0 + eventGenerator (couplingNext (D.cellBarrier C.grid j))
        (D.couplingRate ℓ θ u) (fun r => a r.start) s)) = 0 := by
      simp [D.coupling_generator_start]
    rw [hz] at hh
    exact Talagrand.hasDerivWithinAt_Ici_of_Icc hu hh
  have hnode : ∀ j, j<C.grid.K → C.pairing j (C.grid.z j) (fun s => a s.start) =
      ∑ x, D.density θ x * a x := by
    intro j
    induction j with
    | zero => intro _; rw [C.pairing_initial]; rfl
    | succ j ih =>
      intro hj
      rw [C.pairing_node j hj]
      simp only [killNode_start]
      exact (hlocal j (by omega) _ ⟨C.grid.mono j (by omega), le_rfl⟩).trans (ih (by omega))
  exact (hlocal k hk t ht).trans (hnode k hk)

omit [Nonempty α] in
theorem dynkin_eq (F dF H : ℝ → CoupledState α n → ℝ)
    (hder : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) t)
    (hH : C.CellContinuous H)
    (hgen : ∀ k, k<C.grid.K → ∀ t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1)), ∀ s,
      dF t s + eventGenerator (couplingNext (D.cellBarrier C.grid k))
        (D.couplingRate ℓ θ t) (F t) s = H t s)
    (hkill : ∀ t s B, F t (killNode B s) = F t s) :
    (∑ s, C.terminal s * F 2 s) = (∑ x, D.density θ x * F θ ⟨x, x, x, true⟩) + C.integrate H := by
  have hF (k : ℕ) (hk : k<C.grid.K) (s : CoupledState α n) :
      ContinuousOn (fun t => F t s) (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) :=
    fun t ht => (hder k hk t ht s).continuousWithinAt
  have hd (k : ℕ) (hk : k<C.grid.K) (t : ℝ)
      (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) :
      HasDerivWithinAt (fun u => C.pairing k u (F u)) (C.pairing k t (H t))
        (Set.Icc (C.grid.z k) (C.grid.z (k + 1))) t := by
    have hh := eventFlow_derivative _ _ _ _ _ (C.flow.flow k hk) F dF (hder k hk) t ht
    simpa only [hgen k hk t ht, pairing] using hh
  have hnode (k : ℕ) (hk : k + 1<C.grid.K) :
      C.pairing (k + 1) (C.grid.z (k + 1)) (F (C.grid.z (k + 1))) =
        C.pairing k (C.grid.z (k + 1)) (F (C.grid.z (k + 1))) := by
    rw [C.pairing_node k hk]
    simp_rw [hkill]
  have hh := Talagrand.chain_eq C.grid.pos C.grid.mono
    (fun k hk => C.pairing_continuous hk F (hF k hk)) hd
    (fun k hk => C.pairing_integrable hH hk) hnode
  rw [C.pairing_initial] at hh
  simpa only [C.grid.last, C.grid.first, hkill, pairing, terminal, integrate] using hh

end TailBound.RefreshData.StoppedCoupling
