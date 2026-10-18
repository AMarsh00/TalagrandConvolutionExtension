import TailBound.RefreshTail
import TailBound.ContinuousPositivity

/-! The manuscript's continuous-time, arbitrary finite-state main theorem.
Every estimate used below is proved in the imported modules. -/
namespace TailBound

/-- Theorem 1: one common tail constant for every tensor dimension. -/
theorem main_theorem : ManuscriptTheorem1 := by
  intro α _ _ S π hirr hstat τ hτ
  exact positive_kernel_tail π (S.kernel τ)
    (S.stationary_full_support π hirr hstat) hstat.2.1
    (S.kernel_strictly_pos hirr hτ) (S.stochastic τ hτ.le).2 (hstat.2.2 τ hτ.le)

end TailBound
