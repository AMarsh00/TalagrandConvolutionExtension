import TailBound.RefreshTail
import TailBound.ContinuousPositivity

/-!
# Main Theorem

The dimension-free tail bound for finite-state Markov semigroups.
-/

namespace TailBound

/-- Theorem 1.1: one common tail constant for every tensor dimension. -/
theorem main_theorem : ManuscriptTheorem1 := by
  intro α _ _ S π hirr hstat τ hτ
  exact positive_kernel_tail π (S.kernel τ)
    (S.stationary_full_support π hirr hstat) hstat.2.1
    (S.kernel_strictly_pos hirr hτ) (S.stochastic τ hτ.le).2 (hstat.2.2 τ hτ.le)

end TailBound
