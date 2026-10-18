import TailBound.Core

/-!
Exact main-theorem target.

`ManuscriptTheorem1` is the exact target proposition. Its inhabitant is
`TailBound.main_theorem` in `TailBound/MainTheorem.lean`. This file keeps the
statement separate from the proof to avoid import cycles.
-/

open scoped BigOperators
namespace TailBound

universe u

/-- A continuous Markov semigroup on a finite state space, in kernel form. -/
structure FiniteMarkovSemigroup (α : Type u) [Fintype α] [DecidableEq α] where
  kernel : ℝ → α → α → ℝ
  zero : ∀ x y, kernel 0 x y = if x = y then 1 else 0
  add : ∀ s t, 0 ≤ s → 0 ≤ t → kernel (s+t) = comp (kernel s) (kernel t)
  stochastic : ∀ t, 0 ≤ t → Stochastic (kernel t)
  continuous : ∀ x y, ContinuousOn (fun t => kernel t x y) (Set.Ici 0)

def FiniteMarkovSemigroup.Irreducible {α : Type u} [Fintype α] [DecidableEq α]
    (S : FiniteMarkovSemigroup α) : Prop :=
  ∀ x y, ∃ t : ℝ, 0 < t ∧ 0 < S.kernel t x y

def FiniteMarkovSemigroup.HasStationaryDistribution {α : Type u}
    [Fintype α] [DecidableEq α] (S : FiniteMarkovSemigroup α) (π : α → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ (∑ x, π x = 1) ∧
    ∀ t, 0 ≤ t → Stationary π (S.kernel t)

/-- The manuscript's main assertion, explicitly including one common constant
for all dimensions. The n=0 case included by `DimensionFreeTail` is harmless.
The proof is `TailBound.main_theorem` in `MainTheorem.lean`. -/
def ManuscriptTheorem1 : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α]
    (S : FiniteMarkovSemigroup α) (π : α → ℝ),
    S.Irreducible → S.HasStationaryDistribution π →
    ∀ τ : ℝ, 0 < τ → DimensionFreeTail π (S.kernel τ)

/-- The refresh assertion needed by the reduction. Proved as `refreshTailClaim`
in `RefreshTail.lean`. ε denotes the refresh probability. -/
def RefreshTailClaim : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α] (π : α → ℝ),
    (∀ x, 0 < π x) → (∑ x, π x = 1) →
    ∀ ε : ℝ, 0 < ε → ε < 1 → DimensionFreeTail π (refresh π ε)

end TailBound
