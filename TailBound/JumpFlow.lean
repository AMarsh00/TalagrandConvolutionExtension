import TailBound.Profile
import TalagrandConvConjecture.Flow.Glued

/-!
# Jump Flow

Finite jump processes represented by their master equations. Events may
leave a state unchanged; their diagonal contributions cancel automatically.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace TailBound

variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E]

noncomputable def eventForward (next : E → S → S) (rate : E → S → ℝ) (s r : S) : ℝ :=
  ∑ e, ((if next e r = s then rate e r else 0) - if r=s then rate e r else 0)

noncomputable def eventGenerator (next : E → S → S) (rate : E → S → ℝ)
    (f : S → ℝ) (s : S) : ℝ := ∑ e, rate e s * (f (next e s) - f s)

lemma eventForward_column (next : E → S → S) (rate : E → S → ℝ) (r : S) :
    ∑ s, eventForward next rate s r = 0 := by
  unfold eventForward
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  simp [Finset.sum_sub_distrib]

omit [Fintype S] in
lemma eventForward_offdiag (next : E → S → S) (rate : E → S → ℝ)
    (hr : ∀ e s, 0 ≤ rate e s) (s r : S) (hsr : s ≠ r) :
    0 ≤ eventForward next rate s r := by
  apply Finset.sum_nonneg
  intro e _
  simp only [Ne.symm hsr, if_false, sub_zero]
  split_ifs
  · exact hr e r
  · exact le_rfl

lemma eventForward_duality (next : E → S → S) (rate : E → S → ℝ) (μ f : S → ℝ) :
    ∑ s, Talagrand.matVec (eventForward next rate) μ s * f s =
      ∑ s, μ s * eventGenerator next rate f s := by
  unfold Talagrand.matVec
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  unfold eventForward eventGenerator
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp
  ring

omit [Fintype S] [DecidableEq S] in
lemma eventGenerator_square (next : E → S → S) (rate : E → S → ℝ)
    (f : S → ℝ) (s : S) :
    eventGenerator next rate (fun r => (f r) ^ 2) s -
      2 * f s * eventGenerator next rate f s =
      ∑ e, rate e s * (f (next e s) - f s) ^ 2 := by
  unfold eventGenerator
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

omit [Fintype S] in
lemma eventForward_continuousOn {a b : ℝ} (next : E → S → S)
    (rate : ℝ → E → S → ℝ)
    (hr : ∀ e s, ContinuousOn (fun t => rate t e s) (Set.Icc a b)) (s r : S) :
    ContinuousOn (fun t => eventForward next (rate t) s r) (Set.Icc a b) := by
  apply continuousOn_finset_sum
  intro e _
  apply ContinuousOn.sub
  · split_ifs <;> first | exact hr e r | exact continuousOn_const
  · split_ifs <;> first | exact hr e r | exact continuousOn_const

/-- Existence, positivity, and mass conservation for a finite event process. -/
theorem exists_eventFlow (a b : ℝ) (hab : a ≤ b) (next : E → S → S)
    (rate : ℝ → E → S → ℝ)
    (hr : ∀ e s, ContinuousOn (fun t => rate t e s) (Set.Icc a b))
    (hr0 : ∀ t ∈ Set.Icc a b, ∀ e s, 0 ≤ rate t e s)
    (μ : S → ℝ) (hμ : ∀ s, 0 ≤ μ s) :
    ∃ y : ℝ → S → ℝ,
      Talagrand.IsLinFlow (fun t => eventForward next (rate t)) a b y ∧ y a = μ ∧
      (∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ y t s) ∧
      (∀ t ∈ Set.Icc a b, ∑ s, y t s = ∑ s, μ s) := by
  have hA := eventForward_continuousOn next rate hr
  obtain ⟨y, hy, hy0⟩ := Talagrand.exists_linFlow (fun t => eventForward next (rate t)) hab hA μ
  refine ⟨y, hy, hy0, ?_, ?_⟩
  · exact Talagrand.linFlow_nonneg hab hA
      (fun t ht s r hsr => eventForward_offdiag next (rate t) (hr0 t ht) s r hsr) hy
      (by simpa only [hy0] using hμ)
  · intro t ht
    rw [Talagrand.linFlow_mass_eq hab (fun t _ r => eventForward_column next (rate t) r) hy t ht, hy0]

/-- Time-dependent Dynkin identity on a single cell. -/
lemma eventFlow_derivative (a b : ℝ) (next : E → S → S) (rate : ℝ → E → S → ℝ)
    (y : ℝ → S → ℝ) (hy : Talagrand.IsLinFlow (fun t => eventForward next (rate t)) a b y)
    (F dF : ℝ → S → ℝ)
    (hF : ∀ t ∈ Set.Icc a b, ∀ s, HasDerivWithinAt (fun u => F u s) (dF t s) (Set.Icc a b) t)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt (fun u => ∑ s, y u s * F u s)
      (∑ s, y t s * (dF t s + eventGenerator next (rate t) (F t) s)) (Set.Icc a b) t := by
  have hh := HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset S))
    (fun s _ => (hy.deriv s t ht).mul (hF t ht s))
  have he : (∑ s, (Talagrand.matVec (eventForward next (rate t)) (y t) s * F t s + y t s * dF t s)) =
      ∑ s, y t s * (dF t s + eventGenerator next (rate t) (F t) s) := by
    rw [Finset.sum_add_distrib, eventForward_duality]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rwa [he] at hh

end TailBound
