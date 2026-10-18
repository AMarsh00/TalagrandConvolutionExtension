import TailBound.CouplingCalculus

/-! Support of the stopped process, including the deterministic barrier nodes. -/

open scoped BigOperators
namespace TailBound

set_option linter.unusedSectionVars false

lemma eventFlow_no_inflow {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E]
    {a b : ℝ} (next : E → S → S) (rate : ℝ → E → S → ℝ)
    (y : ℝ → S → ℝ)
    (hy : Talagrand.IsLinFlow (fun t => eventForward next (rate t)) a b y)
    (hn : ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ y t s)
    (hr : ∀ t ∈ Set.Icc a b, ∀ e s, 0 ≤ rate t e s)
    (B : Set S) [DecidablePred (· ∈ B)] (hnext : ∀ e s, next e s ∉ B)
    (hinit : (∑ s, y a s * (if s ∈ B then (1 : ℝ) else 0)) = 0)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (s : S) (hs : s ∈ B) : y t s = 0 := by
  classical
  let F : S → ℝ := fun s => if s ∈ B then 1 else 0
  have hF0 (s : S) : 0 ≤ F s := by dsimp [F]; split_ifs <;> norm_num
  have hsub : Set.Icc a t ⊆ Set.Icc a b := fun u hu => ⟨hu.1,hu.2.trans ht.2⟩
  have hgen (u : ℝ) (hu : u ∈ Set.Icc a b) (s : S) :
      eventGenerator next (rate u) F s ≤ 0 := by
    apply Finset.sum_nonpos
    intro e _
    have he : F (next e s) = 0 := by simp [F,hnext e s]
    rw [he,zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (hr u hu e s) (neg_nonpos.mpr (hF0 s))
  have hm : (∑ r, y t r * F r) ≤ ∑ r, y a r * F r := by
    apply Talagrand.le_of_hasDerivWithinAt_nonpos ht.1
    · apply continuousOn_finset_sum
      intro r _
      exact ((hy.cont r).mono hsub).mul continuousOn_const
    · intro u hu
      have hh := eventFlow_derivative a b next rate y hy (fun _ s => F s) (fun _ _ => 0)
        (fun v _ r => hasDerivWithinAt_const v _ _) u (hsub hu)
      refine ⟨_,?_,hh.mono hsub⟩
      apply Finset.sum_nonpos
      intro r _
      exact mul_nonpos_of_nonneg_of_nonpos (hn u (hsub hu) r) (by simpa using hgen u (hsub hu) r)
  have hsingle : y t s * F s ≤ ∑ r, y t r * F r :=
    Finset.single_le_sum (fun r _ => mul_nonneg (hn t ht r) (hF0 r)) (Finset.mem_univ s)
  have hi : (∑ r, y a r * F r) = 0 := hinit
  rw [hi] at hm
  have hfs : F s = 1 := by simp [F,hs]
  rw [hfs,mul_one] at hsingle
  exact le_antisymm (hsingle.trans hm) (hn t ht s)

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

lemma couplingNext_valid (B : Set (Fin n → α)) (e : CouplingEvent α n)
    (s : CoupledState α n) :
    ¬ ((couplingNext B e s).alive = true ∧ (couplingNext B e s).v ∈ B) := by
  classical
  intro ⟨ha,hv⟩
  have hh : (couplingNext B e s).v ∉ B := by
    cases e.1 <;> simpa [couplingNext,Bool.and_eq_true] using (Bool.and_eq_true_iff.mp ha).2
  exact hh hv

namespace RefreshData
variable (D : RefreshData α n)

lemma killNode_outside_cell {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    {k : ℕ} (hk : k<G.K) (s : CoupledState α n)
    (hs : (killNode (D.barrier ℓ (G.z k)) s).alive = true) :
    (killNode (D.barrier ℓ (G.z k)) s).v ∉ D.cellBarrier G k := by
  classical
  have hn : s.v ∉ D.barrier ℓ (G.z k) := by
    simpa [killNode] using (Bool.and_eq_true_iff.mp hs).2
  exact D.logP_lt_implies_outside_cell G hk s.v (lt_of_not_ge hn)

namespace StoppedCoupling
variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

/-- An active state in the support is outside the barrier of its time cell. -/
theorem active_outside (hθ : θ ≤ 2) {k : ℕ} (hk : k<C.grid.K) (t : ℝ)
    (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1))) (s : CoupledState α n)
    (hs : C.law k t s ≠ 0) (ha : s.alive = true) : s.v ∉ D.cellBarrier C.grid k := by
  classical
  let B : Set (CoupledState α n) := {r | r.alive = true ∧ r.v ∈ D.cellBarrier C.grid k}
  have hkill (r : CoupledState α n) :
      killNode (D.barrier ℓ (C.grid.z k)) r ∉ B := by
    intro hb
    exact D.killNode_outside_cell C.grid hk r hb.1 hb.2
  have hi : C.pairing k (C.grid.z k) (fun r => if r ∈ B then 1 else 0) = 0 := by
    cases k with
    | zero =>
      rw [C.pairing_initial]
      apply Finset.sum_eq_zero
      intro x _
      have hh := hkill ⟨x,x,x,true⟩
      simp only [C.grid.first] at hh
      simp [hh]
    | succ j =>
      rw [C.pairing_node j (by omega)]
      apply Finset.sum_eq_zero
      intro r _
      simp only [hkill r, if_false, mul_zero]
  intro hv
  apply hs
  exact eventFlow_no_inflow (couplingNext (D.cellBarrier C.grid k)) (D.couplingRate ℓ θ)
    (C.law k) (C.flow.flow k hk)
    (fun t ht s => C.nonneg hθ hk t ht s)
    (fun t ht e s => D.couplingRate_nonneg ℓ θ t
      (((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon) e s)
    B (couplingNext_valid (D.cellBarrier C.grid k)) hi t ht s ⟨ha,hv⟩

theorem active_log_bound (hθ : θ ≤ 2) {k : ℕ} (hk : k<C.grid.K) (t : ℝ)
    (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k+1))) (s : CoupledState α n)
    (hs : C.law k t s ≠ 0) (ha : s.alive = true) : D.logP t s.v ≤ ℓ+1 :=
  D.logP_le_of_outside_cell C.grid hk s.v (C.active_outside hθ hk t ht s hs ha) t ht

end StoppedCoupling
end RefreshData
end TailBound
