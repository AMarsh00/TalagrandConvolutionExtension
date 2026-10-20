import TailBound.ReverseHarmonic

/-!
# Power Weight

Pointwise algebra for the power comparison. After killing, the frozen
log density is bounded below by the barrier level. This is the lower weight
used in the band-contraction argument.
-/

open scoped BigOperators

namespace TailBound

lemma switchedPower_bracket (r d u v : ℝ) (hr : 0 < r) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    min r (switchedPower d r) * (r ^ (d - 1) * u - v) +
      max (r - switchedPower d r) 0 * (r ^ (d - 1) * v - v) +
      max (switchedPower d r - r) 0 * (u - v) = u - v + (r ^ d - r) * v := by
  have hpow : r * r ^ (d - 1) = r ^ d := by
    calc
      _ = r ^ (1 : ℝ) * r ^ (d - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr]; congr 1; ring
  have hinv : r ^ (1 - d) * r ^ (d - 1) = 1 := by
    rw [← Real.rpow_add hr]
    convert Real.rpow_zero r using 2; ring
  by_cases h : r ≤ 1
  · have hrd : r ^ d ≤ 1 := Real.rpow_le_one hr.le h hd0
    have hb : r ≤ switchedPower d r := by rw [switchedPower, if_pos h]; linarith
    rw [min_eq_left hb, max_eq_right (sub_nonpos.mpr hb), max_eq_left (sub_nonneg.mpr hb)]
    rw [switchedPower, if_pos h]
    linear_combination u * hpow
  · have hb : switchedPower d r ≤ r := by
      have hh := (switchedPower_bounds d r hr hd0 hd1).2
      rwa [max_eq_right (le_of_not_ge h)] at hh
    rw [min_eq_right hb, max_eq_left (sub_nonneg.mpr hb), max_eq_right (sub_nonpos.mpr hb)]
    rw [switchedPower, if_neg h]
    linear_combination v * hpow + (u - v) * hinv

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

namespace RefreshData

variable (D : RefreshData α n)

omit [Nonempty α] in
lemma logP_ge_of_inside_cell {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    {k : ℕ} (hk : k<G.K) (x : Fin n → α) (hx : x ∈ D.cellBarrier G k)
    (t : ℝ) (ht : t ∈ Set.Icc (G.z k) (G.z (k + 1))) : ℓ + 1 ≤ D.logP t x := by
  rcases (G.mono k hk).eq_or_lt with he|hl
  · have ht' : t=G.z k := by linarith [ht.1, ht.2]
    have hm : (G.z k + G.z (k + 1)) / 2=G.z k := by linarith
    simpa only [cellBarrier, barrier, Set.mem_setOf_eq, hm, ht'] using hx
  · have hmidmem : (G.z k + G.z (k + 1)) / 2 ∈ Set.Ioo (G.z k) (G.z (k + 1)) := by
      constructor <;> linarith
    have hopen (u : ℝ) (hu : u ∈ Set.Ioo (G.z k) (G.z (k + 1))) : ℓ + 1 ≤ D.logP u x :=
      (D.barrier_constant G hk hmidmem hu x).mp hx
    have hc : ContinuousOn (fun u => D.logP u x)
        (closure (Set.Ioo (G.z k) (G.z (k + 1)))) := by
      rw [closure_Ioo hl.ne]
      exact (D.continuousOn_logP x).mono
        (fun u hu => ((G.cell_subset hk hu).2).trans D.obs_le_horizon)
    apply le_on_closure hopen continuousOn_const hc
    rwa [closure_Ioo hl.ne]

noncomputable def comparisonFactor (ℓ θ t : ℝ) (s : CoupledState α n) : ℝ :=
  if s.alive then
    Real.exp ((D.exponent ℓ θ s.start - 1) * D.logP t s.v - D.exponent ℓ θ s.start * D.logP θ s.start)
  else Real.exp (-D.logP t s.v + D.exponent ℓ θ s.start * (ℓ + 1 - D.logP θ s.start))

omit [Nonempty α] in
lemma comparisonFactor_pos (ℓ θ t : ℝ) (s : CoupledState α n) :
    0 < D.comparisonFactor ℓ θ t s := by
  unfold comparisonFactor
  split_ifs <;> exact Real.exp_pos _

omit [Nonempty α] in
lemma comparisonFactor_vupdate {t : ℝ} (ht : t ≤ D.horizon) (ℓ θ : ℝ)
    (s : CoupledState α n) (i : Fin n) (a : α) :
    D.comparisonFactor ℓ θ t {s with v := Function.update s.v i a} =
      D.comparisonFactor ℓ θ t s * (D.ratio t i a s.v) ^ (D.coupledExponent ℓ θ s - 1) := by
  have he := D.logP_update ht i a s.v
  rw [Real.rpow_def_of_pos (D.ratio_pos ht i a s.v)]
  unfold comparisonFactor coupledExponent
  dsimp only
  split_ifs <;> rw [← Real.exp_add] <;> congr 1 <;> rw [← he] <;> ring

omit [Nonempty α] in
lemma comparisonFactor_wupdate (ℓ θ t : ℝ) (s : CoupledState α n) (i : Fin n) (a : α) :
    D.comparisonFactor ℓ θ t {s with w := Function.update s.w i a} =
      D.comparisonFactor ℓ θ t s := rfl

omit [Nonempty α] in
lemma comparisonFactor_kill_le (ℓ θ t : ℝ) (B : Set (Fin n → α))
    (hB : ∀ x ∈ B, ℓ + 1 ≤ D.logP t x) (s : CoupledState α n) :
    D.comparisonFactor ℓ θ t (killNode B s) ≤ D.comparisonFactor ℓ θ t s := by
  classical
  by_cases hb : s.v ∈ B
  · by_cases ha : s.alive = true
    · simp only [comparisonFactor, killNode, ha, if_true, hb, not_true_eq_false, decide_false,
        Bool.and_false, if_false, Bool.false_eq_true]
      apply Real.exp_le_exp.mpr
      have hh := mul_nonneg (D.exponent_bounds ℓ θ s.start).1 (sub_nonneg.mpr (hB s.v hb))
      nlinarith
    · have haf := Bool.eq_false_iff.mpr ha
      simp [comparisonFactor, killNode, haf]
  · simp [comparisonFactor, killNode, hb]

omit [Nonempty α] in
lemma hasDerivAt_comparisonFactor {t : ℝ} (ht : t ≤ D.horizon) (ℓ θ : ℝ)
    (s : CoupledState α n) :
    HasDerivAt (fun u => D.comparisonFactor ℓ θ u s)
      (D.comparisonFactor ℓ θ t s * (1 - D.coupledExponent ℓ θ s)*
        (refreshGenerator D.π (D.p t) s.v / D.p t s.v)) t := by
  have hh := D.hasDerivAt_logP ht s.v
  unfold comparisonFactor coupledExponent
  split_ifs
  · convert ((hh.const_mul (D.exponent ℓ θ s.start - 1)).sub_const
      (D.exponent ℓ θ s.start * D.logP θ s.start)).exp using 1
    dsimp only
    ring
  · convert (hh.const_sub (D.exponent ℓ θ s.start * (ℓ + 1 - D.logP θ s.start))).exp using 1
    · funext u
      congr 1
      ring
    · ring_nf

omit [Nonempty α] in
lemma comparisonFactor_next_empty {t : ℝ} (ht : t ≤ D.horizon) (ℓ θ : ℝ)
    (s : CoupledState α n) (e : CouplingEvent α n) :
    D.comparisonFactor ℓ θ t (couplingNext ∅ e s) =
      D.comparisonFactor ℓ θ t s *
        (if e.1 = .right then 1 else (D.ratio t e.2.1 e.2.2 s.v) ^ (D.coupledExponent ℓ θ s - 1)) := by
  classical
  rcases e with ⟨e, i, a⟩
  cases e
  · have hh := D.comparisonFactor_vupdate ht ℓ θ {s with w := Function.update s.w i a} i a
    simpa [couplingNext, comparisonFactor, coupledExponent] using hh
  · simpa [couplingNext, comparisonFactor, coupledExponent] using D.comparisonFactor_vupdate ht ℓ θ s i a
  · simp [couplingNext, comparisonFactor]

omit [Nonempty α] in
lemma comparison_generator_raw {t : ℝ} (ht : t ≤ D.horizon) (ℓ θ : ℝ)
    (q : (Fin n → α) → ℝ) (s : CoupledState α n) :
    eventGenerator (couplingNext ∅) (D.couplingRate ℓ θ t)
        (fun r => D.comparisonFactor ℓ θ t r * q r.w) s =
      D.comparisonFactor ℓ θ t s * (refreshGenerator D.π q s.w + q s.w *
        ∑ i, mean D.π (fun a => (D.ratio t i a s.v) ^ (D.coupledExponent ℓ θ s) - D.ratio t i a s.v)) := by
  classical
  rw [D.coupling_generator_expansion, generator_weighted_form D.π D.mass]
  unfold mean
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [D.comparisonFactor_next_empty ht]
  simp only [couplingNext,
    show JumpKind.sync ≠ .right by decide, show JumpKind.left ≠ .right by decide,
    ite_false, ite_true, mul_one]
  have hd := D.coupledExponent_bounds ℓ θ s
  have hh := switchedPower_bracket (D.ratio t i a s.v) (D.coupledExponent ℓ θ s)
    (q (Function.update s.w i a)) (q s.w) (D.ratio_pos ht i a s.v) hd.1 hd.2
  linear_combination (D.π a * D.comparisonFactor ℓ θ t s) * hh

omit [Nonempty α] in
lemma comparison_generator_le_raw {ℓ θ t : ℝ} (ht : t ≤ 2)
    (B : Set (Fin n → α)) (hB : ∀ x ∈ B, ℓ + 1 ≤ D.logP t x)
    (q : (Fin n → α) → ℝ) (hq : ∀ x, 0 ≤ q x) (s : CoupledState α n) :
    eventGenerator (couplingNext B) (D.couplingRate ℓ θ t)
        (fun r => D.comparisonFactor ℓ θ t r * q r.w) s ≤
      eventGenerator (couplingNext ∅) (D.couplingRate ℓ θ t)
        (fun r => D.comparisonFactor ℓ θ t r * q r.w) s := by
  classical
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (D.couplingRate_nonneg ℓ θ t (ht.trans D.obs_le_horizon) e s)
  apply sub_le_sub_right
  have he : couplingNext B e s = killNode B (couplingNext ∅ e s) := by
    rcases e with ⟨e, i, a⟩
    cases e <;> simp [couplingNext, killNode]
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (D.comparisonFactor_kill_le ℓ θ t B hB (couplingNext ∅ e s)) (hq _)

omit [Nonempty α] in
lemma comparison_drift {ℓ θ t : ℝ} (ht : t ≤ 2)
    (B : Set (Fin n → α)) (hB : ∀ x ∈ B, ℓ + 1 ≤ D.logP t x)
    (q : (Fin n → α) → ℝ) (hq : ∀ x, 0 ≤ q x) (s : CoupledState α n) :
    (D.comparisonFactor ℓ θ t s * (1 - D.coupledExponent ℓ θ s)*
        (refreshGenerator D.π (D.p t) s.v / D.p t s.v) * q s.w -
      D.comparisonFactor ℓ θ t s * refreshGenerator D.π q s.w) +
      eventGenerator (couplingNext B) (D.couplingRate ℓ θ t)
        (fun r => D.comparisonFactor ℓ θ t r * q r.w) s ≤ 0 := by
  have hgen := D.comparison_generator_le_raw (ℓ := ℓ) (θ := θ) ht B hB q hq s
  rw [D.comparison_generator_raw (ht.trans D.obs_le_horizon)] at hgen
  have hd := D.coupledExponent_bounds ℓ θ s
  have hsum : (∑ i, mean D.π (fun a => (D.ratio t i a s.v) ^ (D.coupledExponent ℓ θ s) - D.ratio t i a s.v)) ≤
      -(1 - D.coupledExponent ℓ θ s) * (refreshGenerator D.π (D.p t) s.v / D.p t s.v) := by
    rw [D.generator_div (ht.trans D.obs_le_horizon), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← mean_smul]
    apply mean_mono D.πnonneg
    intro a
    have hh := Talagrand.rpow_le_one_sub_add_mul (D.ratio_pos (ht.trans D.obs_le_horizon) i a s.v) hd.1 hd.2
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (D.comparisonFactor_pos ℓ θ t s).le (hq s.w))
  nlinarith

end RefreshData
end TailBound
