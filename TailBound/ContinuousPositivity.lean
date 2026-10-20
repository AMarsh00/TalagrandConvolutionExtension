import TailBound.MainStatement
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Finset.Card

/-!
# Continuous Positivity

Positive-time kernels of a finite irreducible continuous Markov semigroup.
The proof uses continuity at zero and a support of minimal cardinality.
It does not assume differentiability, a generator, or matrix embeddability.
-/
open scoped BigOperators

namespace TailBound.FiniteMarkovSemigroup

variable {α : Type*} [Fintype α] [DecidableEq α] (S : FiniteMarkovSemigroup α)
attribute [local instance] Classical.propDecidable

lemma kernel_pos_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x y z : α)
    (hxy : 0 < S.kernel s x y) (hyz : 0 < S.kernel t y z) :
    0 < S.kernel (s + t) x z := by
  rw [S.add s t hs ht]
  exact (mul_pos hxy hyz).trans_le (Finset.single_le_sum
    (fun w _ => mul_nonneg ((S.stochastic s hs).1 x w) ((S.stochastic t ht).1 w z)) (Finset.mem_univ y))

lemma diagonal_nat_mul {s : ℝ} (hs : 0 ≤ s) (x : α) (hx : 0 < S.kernel s x x) (k : ℕ) :
    0 < S.kernel ((k : ℝ) * s) x x := by
  induction k with
  | zero => simp [S.zero]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul]
    exact S.kernel_pos_add (mul_nonneg (Nat.cast_nonneg k) hs) hs x x x ih hx

lemma diagonal_pos {t : ℝ} (ht : 0 ≤ t) (x : α) : 0 < S.kernel t x x := by
  have hc := (S.continuous x x) 0 (show (0 : ℝ) ∈ Set.Ici 0 from Set.self_mem_Ici)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp hc 1 (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have hs : 0 ≤ t / ((N : ℝ) + 1) := div_nonneg ht hn.le
  have hsmall : t / ((N : ℝ) + 1) < δ := by
    apply (div_lt_iff₀ hn).mpr
    have hh := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hdist : dist (t / ((N : ℝ) + 1)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs]
    exact hsmall
  have hh := hclose hs hdist
  rw [S.zero] at hh
  simp only [ite_true, Real.dist_eq] at hh
  have hlocal : 0 < S.kernel (t / ((N : ℝ) + 1)) x x := by linarith [(abs_lt.mp hh).1]
  have hpow := S.diagonal_nat_mul hs x hlocal (N + 1)
  have he : ((N + 1 : ℕ) : ℝ) * (t / ((N : ℝ) + 1)) = t := by push_cast; field_simp
  rwa [he] at hpow

lemma kernel_pos_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x y : α)
    (hxy : 0 < S.kernel s x y) : 0 < S.kernel t x y := by
  have hh := S.kernel_pos_add hs (sub_nonneg.mpr hst) x y y hxy (S.diagonal_pos (sub_nonneg.mpr hst) y)
  simpa only [add_sub_cancel] using hh

noncomputable def positiveSupport (t : ℝ) : Finset (α × α) :=
  Finset.univ.filter (fun p => 0 < S.kernel t p.1 p.2)

lemma support_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    S.positiveSupport s ⊆ S.positiveSupport t := by
  intro p hp
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact S.kernel_pos_mono hs hst p.1 p.2 hp

lemma kernel_nat_mul_rel (R : α → α → Prop) (hrefl : ∀ x, R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z) {s : ℝ} (hs : 0 ≤ s)
    (hbase : ∀ x y, 0 < S.kernel s x y → R x y) (k : ℕ) :
    ∀ x y, 0 < S.kernel ((k : ℝ) * s) x y → R x y := by
  induction k with
  | zero =>
    intro x y hxy
    by_cases he : x=y
    · subst y; exact hrefl x
    · simp [S.zero, he] at hxy
  | succ k ih =>
    intro x y hxy
    rw [Nat.cast_succ, add_mul, one_mul, S.add ((k : ℝ) * s) s (mul_nonneg (Nat.cast_nonneg k) hs) hs] at hxy
    change 0 < ∑ z, S.kernel ((k : ℝ) * s) x z * S.kernel s z y at hxy
    have hn (z : α) := (S.stochastic ((k : ℝ) * s) (mul_nonneg (Nat.cast_nonneg k) hs)).1 x z
    have hm (z : α) := (S.stochastic s hs).1 z y
    obtain ⟨z, _, hz⟩ := (Finset.sum_pos_iff_of_nonneg (fun z _ => mul_nonneg (hn z) (hm z))).mp hxy
    have h1 : 0 < S.kernel ((k : ℝ) * s) x z := by nlinarith [hn z, hm z]
    have h2 : 0 < S.kernel s z y := by nlinarith [hn z, hm z]
    exact htrans x z y (ih x z h1) (hbase z y h2)

/-- Finite continuous-time irreducibility implies strict positivity at every
positive time. -/
theorem kernel_strictly_pos (hirr : S.Irreducible) {τ : ℝ} (hτ : 0 < τ) (x y : α) :
    0 < S.kernel τ x y := by
  have hex : ∃ k : ℕ, ∃ t : ℝ, 0 < t ∧ (S.positiveSupport t).card = k :=
    ⟨(S.positiveSupport 1).card, 1, by norm_num, rfl⟩
  obtain ⟨t, ht, hcard⟩ := Nat.find_spec hex
  have hmin (s : ℝ) (hs : 0 < s) : (S.positiveSupport t).card ≤ (S.positiveSupport s).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨s, hs, rfl⟩
  have hsmall (s : ℝ) (hs : 0 < s) (hst : s ≤ t) (a b : α) :
      (0 < S.kernel s a b) ↔ (0 < S.kernel t a b) := by
    have he := Finset.eq_of_subset_of_card_le (S.support_mono hs.le hst) (hmin s hs)
    have hh := congrArg (fun F : Finset (α×α) => (a, b) ∈ F) he
    simpa only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and] using (iff_of_eq hh)
  let R : α → α → Prop := fun a b => 0 < S.kernel t a b
  have hrefl (a : α) : R a a := S.diagonal_pos ht.le a
  have htrans (a b c : α) (hab : R a b) (hbc : R b c) : R a c := by
    have h1 := (hsmall (t / 2) (by linarith) (by linarith) a b).mpr hab
    have h2 := (hsmall (t / 2) (by linarith) (by linarith) b c).mpr hbc
    have hh := S.kernel_pos_add (by linarith : 0 ≤ t / 2) (by linarith : 0 ≤ t / 2) a b c h1 h2
    have he : t / 2 + t / 2=t := by ring
    rwa [he] at hh
  have hall (s : ℝ) (hs : 0 < s) (a b : α) (hab : 0 < S.kernel s a b) : R a b := by
    obtain ⟨N, hN⟩ := exists_nat_gt (s / t)
    have hn : 0 < (N : ℝ) + 1 := by positivity
    have hu : 0 < s / ((N : ℝ) + 1) := div_pos hs hn
    have hut : s / ((N : ℝ) + 1) ≤ t := by
      apply (div_le_iff₀ hn).mpr
      have hh := (div_lt_iff₀ ht).mp hN
      nlinarith
    have hh := S.kernel_nat_mul_rel R hrefl htrans hu.le
      (fun a b h => (hsmall _ hu hut a b).mp h) (N + 1) a b
    have he : ((N + 1 : ℕ) : ℝ) * (s / ((N : ℝ) + 1))=s := by push_cast; field_simp
    rw [he] at hh
    exact hh hab
  obtain ⟨s, hs, hxy⟩ := hirr x y
  have hR : R x y := hall s hs x y hxy
  by_cases hτt : τ ≤ t
  · exact (hsmall τ hτ hτt x y).mpr hR
  · exact S.kernel_pos_mono ht.le (lt_of_not_ge hτt).le x y hR

theorem stationary_full_support (π : α → ℝ) (hirr : S.Irreducible)
    (hstat : S.HasStationaryDistribution π) : ∀ y, 0 < π y := by
  have he : ∃ x, 0 < π x := by
    by_contra hh
    push Not at hh
    have hz : ∀ x, π x = 0 := fun x => le_antisymm (hh x) (hstat.1 x)
    have hm := hstat.2.1
    simp [hz] at hm
  obtain ⟨x, hx⟩ := he
  intro y
  have hp := S.kernel_strictly_pos hirr (by norm_num : (0 : ℝ) < 1) x y
  have hh := Finset.single_le_sum (f := fun z => π z * S.kernel 1 z y)
    (fun z _ => mul_nonneg (hstat.1 z) ((S.stochastic 1 (by norm_num)).1 z y)) (Finset.mem_univ x)
  rw [hstat.2.2 1 (by norm_num) y] at hh
  exact (mul_pos hx hp).trans_le hh

end TailBound.FiniteMarkovSemigroup
