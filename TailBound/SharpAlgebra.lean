import Mathlib.Tactic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Sharp Algebra

Scalar estimates for the sharp fixed-band constant. Adapted from the
pinned junwei-lu/TalagrandConvolutionConjecture, FixedBand.lean,
commit 6488afd9f5f94f40766c6915c6e4e4f8de15ada7. The score coefficient
is enlarged from 50 to 64 so its square root is the integer 8.
-/
open scoped BigOperators

namespace TailBound.Sharp
/-- `∑_{j<m} (j+1)^{-1/2} ≤ 2√m`. -/
lemma sum_inv_sqrt_le (m : ℕ) :
    ∑ j ∈ Finset.range m, (Real.sqrt ((j : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk1 : (0 : ℝ) < Real.sqrt ((k : ℝ) + 1) :=
      Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) = (k : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hmul : Real.sqrt (k : ℝ) * Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 / 2 := by
      rw [← Real.sqrt_mul (by positivity)]
      calc Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))
          ≤ Real.sqrt (((k : ℝ) + 1 / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = (k : ℝ) + 1 / 2 := Real.sqrt_sq (by positivity)
    have h2 : 1 ≤ (2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ))
        * Real.sqrt ((k : ℝ) + 1) := by nlinarith
    have key : (Real.sqrt ((k : ℝ) + 1))⁻¹
        ≤ 2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ) := by
      calc (Real.sqrt ((k : ℝ) + 1))⁻¹
          = 1 * (Real.sqrt ((k : ℝ) + 1))⁻¹ := (one_mul _).symm
        _ ≤ ((2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ))
              * Real.sqrt ((k : ℝ) + 1)) * (Real.sqrt ((k : ℝ) + 1))⁻¹ :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ) := by
            field_simp
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/-- Harmonic-sum bound, real form. -/
lemma sum_inv_le_one_add_log (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic] at h
  push_cast at h
  exact h

lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

lemma log_le_four_mul_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 := log_le_two_mul_sqrt (Real.sqrt_pos.mpr hx)
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

/-- `κ_a·Λ_a ≤ K_a` (from `K² = κ³Λ` and `Λ ≤ κ`). -/
lemma kappa_mul_Lam_le {κ Λ K : ℝ} (hκ : 1 < κ) (hΛ1 : 1 ≤ Λ)
    (hΛκ : Λ ≤ κ) (hK : K ^ 2 = κ ^ 3 * Λ) (hK0 : 0 ≤ K) : κ * Λ ≤ K := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have h1 : (κ * Λ) ^ 2 ≤ K ^ 2 := by
    rw [hK]
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hκ0 hκ0).le hΛ0.le)
      (sub_nonneg.mpr hΛκ)]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hK0] at h2

/-- The absorption inequality of [LGF eq (3.12)]:
`κ²Λ·(1 + log ℓ) ≤ 5·K·√ℓ` whenever `ℓ ≥ K²` and `ℓ ≥ 1`. -/
lemma kappa_sq_Lam_log_le {κ Λ K ℓ : ℝ} (hκ : 1 < κ) (hΛ1 : 1 ≤ Λ)
    (hΛκ : Λ ≤ κ) (hK : K ^ 2 = κ ^ 3 * Λ) (hK1 : 1 ≤ K) (hℓ : K ^ 2 ≤ ℓ)
    (hℓ1 : 1 ≤ ℓ) : κ ^ 2 * Λ * (1 + Real.log ℓ) ≤ 5 * K * Real.sqrt ℓ := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hkl : κ * Λ ≤ K := kappa_mul_Lam_le hκ hΛ1 hΛκ hK hK0
  -- `(κ²Λ)² ≤ K³`
  have hcube : (κ ^ 2 * Λ) ^ 2 ≤ K ^ 3 := by
    have h1 : (κ ^ 2 * Λ) ^ 2 = (κ * Λ) * (κ ^ 3 * Λ) := by ring
    have h2 : K ^ 3 = K * (κ ^ 3 * Λ) := by rw [← hK]; ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hkl (by positivity)
  have hsqrtK : Real.sqrt (K ^ 3) = K * Real.sqrt K := by
    rw [show K ^ 3 = K ^ 2 * K by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hK0]
  have hmain : κ ^ 2 * Λ ≤ K * Real.sqrt K := by
    rw [← hsqrtK]
    calc κ ^ 2 * Λ = Real.sqrt ((κ ^ 2 * Λ) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (K ^ 3) := Real.sqrt_le_sqrt hcube
  -- `1 + log ℓ ≤ 5·ℓ^{1/4}`
  have hq1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt ℓ) := by
    have : (1 : ℝ) ≤ Real.sqrt ℓ := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hℓ1
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by simpa using this)
  have hlog : 1 + Real.log ℓ ≤ 5 * Real.sqrt (Real.sqrt ℓ) := by
    have := log_le_four_mul_sqrt_sqrt hℓ0
    linarith
  -- `√K ≤ ℓ^{1/4}`
  have hKle : K ≤ Real.sqrt ℓ := by
    rw [show K = Real.sqrt (K ^ 2) from (Real.sqrt_sq hK0).symm]
    exact Real.sqrt_le_sqrt hℓ
  have hsK : Real.sqrt K ≤ Real.sqrt (Real.sqrt ℓ) := Real.sqrt_le_sqrt hKle
  have hqq : Real.sqrt (Real.sqrt ℓ) * Real.sqrt (Real.sqrt ℓ) = Real.sqrt ℓ :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hsK0 : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hlog0 : (0 : ℝ) ≤ Real.log ℓ := Real.log_nonneg hℓ1
  calc κ ^ 2 * Λ * (1 + Real.log ℓ)
      ≤ (K * Real.sqrt K) * (5 * Real.sqrt (Real.sqrt ℓ)) := by
        exact mul_le_mul hmain hlog (by linarith) (by positivity)
    _ ≤ (K * Real.sqrt (Real.sqrt ℓ)) * (5 * Real.sqrt (Real.sqrt ℓ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsK hK0
    _ = 5 * K * (Real.sqrt (Real.sqrt ℓ) * Real.sqrt (Real.sqrt ℓ)) := by ring
    _ = 5 * K * Real.sqrt ℓ := by rw [hqq]

/-- `√x ≤ y` from `x ≤ y²`. -/
lemma sqrt_le_of_le_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- Subadditivity of the square root. -/
lemma sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  refine sqrt_le_of_le_sq (by positivity) ?_
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a,
    Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `∑_{j<m} (j+1)^{-2} ≤ 2`. -/
lemma sum_inv_sq_le (m : ℕ) :
    ∑ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ k : ℕ, ∑ j ∈ Finset.range k, (((j : ℝ) + 1) ^ 2)⁻¹
      ≤ 2 - 2 / ((k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ p ih =>
      rw [Finset.sum_range_succ]
      have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      have hp2 : (0 : ℝ) < (p : ℝ) + 1 + 1 := by positivity
      have hid : 2 / ((p : ℝ) + 1) - 2 / ((p : ℝ) + 1 + 1)
          - (((p : ℝ) + 1) ^ 2)⁻¹
          = (p : ℝ) / ((((p : ℝ) + 1) ^ 2) * ((p : ℝ) + 1 + 1)) := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (p : ℝ) / ((((p : ℝ) + 1) ^ 2) * ((p : ℝ) + 1 + 1)) := by
        positivity
      have hcast : ((p + 1 : ℕ) : ℝ) + 1 = (p : ℝ) + 1 + 1 := by push_cast; ring
      rw [hcast]
      linarith
  have h1 : (0 : ℝ) ≤ 2 / ((m : ℝ) + 1) := by positivity
  linarith [key m]

/-- The per-layer discrepancy bound of [LGF Step 1 of Prop 3.2], as pure
algebra: combine `D_A ≤ C(κΛ√(𝒮·ℙ) + κΛ²𝒮)` [LGF Lemma 3.3] with
`𝒮 ≤ 64(κ/(Λu) + (κ-1)/u²)·ℙ` [LGF Lemma 3.8] and `K² = κ³Λ`, where
`u = R+1 ≥ 1` is the (frozen) gap of the layer. -/
lemma DA_layer_bound {κ Λ K CD DAv SAv p u : ℝ}
    (hκ : 1 < κ) (hΛ1 : 1 ≤ Λ) (hΛκ : Λ ≤ κ) (hK : K ^ 2 = κ ^ 3 * Λ)
    (hK0 : 0 ≤ K) (hCD : 0 ≤ CD) (hu : 1 ≤ u) (hp : 0 ≤ p)
    (hSA : SAv ≤ 64 * (κ / (Λ * u) + (κ - 1) / u ^ 2) * p)
    (hDA : DAv ≤ CD * (κ * Λ * Real.sqrt (SAv * p) + κ * Λ ^ 2 * SAv)) :
    DAv ≤ CD * (8 * K / Real.sqrt u + 72 * κ ^ 2 * Λ / u
      + 64 * K ^ 2 / u ^ 2) * p := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  set S : ℝ := 64 * (κ / (Λ * u) + (κ - 1) / u ^ 2) with hS
  have hA0 : (0 : ℝ) ≤ κ / (Λ * u) := by positivity
  have hB0 : (0 : ℝ) ≤ (κ - 1) / u ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have hS0 : (0 : ℝ) ≤ S := by rw [hS]; linarith
  -- (i) `√(𝒮ℙ) ≤ √S·ℙ`
  have hsq : Real.sqrt (SAv * p) ≤ Real.sqrt S * p := by
    have h1 : SAv * p ≤ S * p ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hSA hp]
    calc Real.sqrt (SAv * p) ≤ Real.sqrt (S * p ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt S * p := by rw [Real.sqrt_mul hS0, Real.sqrt_sq hp]
  -- (ii) split the square root of the two-term majorant
  have hsplit : Real.sqrt S
      ≤ 8 * (Real.sqrt (κ / (Λ * u)) + Real.sqrt (κ - 1) / u) := by
    have h64 : Real.sqrt S
        = 8 * Real.sqrt (κ / (Λ * u) + (κ - 1) / u ^ 2) := by
      rw [hS, show (64 : ℝ) * (κ / (Λ * u) + (κ - 1) / u ^ 2)
        = 8 ^ 2 * (κ / (Λ * u) + (κ - 1) / u ^ 2) by norm_num,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hab : Real.sqrt (κ / (Λ * u) + (κ - 1) / u ^ 2)
        ≤ Real.sqrt (κ / (Λ * u)) + Real.sqrt ((κ - 1) / u ^ 2) :=
      sqrt_add_le hA0 hB0
    have hB : Real.sqrt ((κ - 1) / u ^ 2) = Real.sqrt (κ - 1) / u := by
      rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ κ - 1), Real.sqrt_sq hu0.le]
    rw [h64, ← hB]
    linarith
  -- (iii) the leading term is exactly `K/√u`
  have hKu : κ * Λ * Real.sqrt (κ / (Λ * u)) = K / Real.sqrt u := by
    have e2 : (κ * Λ) ^ 2 * (κ / (Λ * u)) = K ^ 2 / u := by
      rw [hK]; field_simp
    calc κ * Λ * Real.sqrt (κ / (Λ * u))
        = Real.sqrt ((κ * Λ) ^ 2) * Real.sqrt (κ / (Λ * u)) := by
          rw [Real.sqrt_sq (by positivity)]
      _ = Real.sqrt ((κ * Λ) ^ 2 * (κ / (Λ * u))) :=
          (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (K ^ 2 / u) := by rw [e2]
      _ = K / Real.sqrt u := by
          rw [Real.sqrt_div (by positivity), Real.sqrt_sq hK0]
  -- (iv) the sub-leading square root is absorbed into `κ²Λ`
  have hsk : Real.sqrt (κ - 1) ≤ κ := sqrt_le_of_le_sq hκ0.le (by nlinarith)
  have h4 : κ * Λ * (Real.sqrt (κ - 1) / u) ≤ κ ^ 2 * Λ / u := by
    have hid : κ ^ 2 * Λ / u - κ * Λ * (Real.sqrt (κ - 1) / u)
        = κ * Λ * (κ - Real.sqrt (κ - 1)) / u := by field_simp
    have hnn : (0 : ℝ) ≤ κ * Λ * (κ - Real.sqrt (κ - 1)) / u :=
      div_nonneg (mul_nonneg (mul_nonneg hκ0.le hΛ0.le) (by linarith)) hu0.le
    linarith
  have hkey : κ * Λ * Real.sqrt S
      ≤ 8 * (K / Real.sqrt u) + 8 * (κ ^ 2 * Λ / u) := by
    have h := mul_le_mul_of_nonneg_left hsplit (by positivity : (0 : ℝ) ≤ κ * Λ)
    have e : κ * Λ * (8 * (Real.sqrt (κ / (Λ * u)) + Real.sqrt (κ - 1) / u))
        = 8 * (κ * Λ * Real.sqrt (κ / (Λ * u)))
          + 8 * (κ * Λ * (Real.sqrt (κ - 1) / u)) := by ring
    rw [e, hKu] at h
    linarith
  -- (v) the second (energy) term
  have hSecond : κ * Λ ^ 2 * S ≤ 64 * κ ^ 2 * Λ / u + 64 * K ^ 2 / u ^ 2 := by
    have hb : κ * Λ ^ 2 * (κ - 1) ≤ K ^ 2 := by
      rw [hK]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hκ0.le hκ0.le) hΛ0.le)
        (sub_nonneg.mpr hΛκ), mul_pos hκ0 (mul_pos hΛ0 hΛ0)]
    have hid : (64 * κ ^ 2 * Λ / u + 64 * K ^ 2 / u ^ 2) - κ * Λ ^ 2 * S
        = 64 * (K ^ 2 - κ * Λ ^ 2 * (κ - 1)) / u ^ 2 := by
      rw [hS]; field_simp; ring
    have hnn : (0 : ℝ) ≤ 64 * (K ^ 2 - κ * Λ ^ 2 * (κ - 1)) / u ^ 2 :=
      div_nonneg (by linarith) (by positivity)
    linarith
  -- assemble
  have a1 : κ * Λ * Real.sqrt (SAv * p)
      ≤ (8 * (K / Real.sqrt u) + 8 * (κ ^ 2 * Λ / u)) * p := by
    calc κ * Λ * Real.sqrt (SAv * p) ≤ κ * Λ * (Real.sqrt S * p) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (κ * Λ * Real.sqrt S) * p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkey hp
  have a2 : κ * Λ ^ 2 * SAv
      ≤ (64 * κ ^ 2 * Λ / u + 64 * K ^ 2 / u ^ 2) * p := by
    calc κ * Λ ^ 2 * SAv ≤ κ * Λ ^ 2 * (S * p) :=
          mul_le_mul_of_nonneg_left hSA (by positivity)
      _ = (κ * Λ ^ 2 * S) * p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hSecond hp
  calc DAv ≤ CD * (κ * Λ * Real.sqrt (SAv * p) + κ * Λ ^ 2 * SAv) := hDA
    _ ≤ CD * ((8 * (K / Real.sqrt u) + 8 * (κ ^ 2 * Λ / u)) * p
          + (64 * κ ^ 2 * Λ / u + 64 * K ^ 2 / u ^ 2) * p) :=
        mul_le_mul_of_nonneg_left (by linarith) hCD
    _ = CD * (8 * K / Real.sqrt u + 72 * κ ^ 2 * Λ / u
          + 64 * K ^ 2 / u ^ 2) * p := by ring

/-- The layer sum of [LGF eq (3.11)]. -/
lemma sum_layer_coeff_le {κ Λ K : ℝ} (hK0 : 0 ≤ K)
    (hκΛ : 0 ≤ κ ^ 2 * Λ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (8 * K / Real.sqrt ((i : ℝ) + 1)
        + 72 * κ ^ 2 * Λ / ((i : ℝ) + 1) + 64 * K ^ 2 / ((i : ℝ) + 1) ^ 2)
      ≤ 16 * K * Real.sqrt m + 72 * κ ^ 2 * Λ * (1 + Real.log m)
        + 128 * K ^ 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ i ∈ Finset.range m, 8 * K / Real.sqrt ((i : ℝ) + 1)
      = 8 * K * ∑ i ∈ Finset.range m, (Real.sqrt ((i : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  have e2 : ∑ i ∈ Finset.range m, 72 * κ ^ 2 * Λ / ((i : ℝ) + 1)
      = 72 * κ ^ 2 * Λ * ∑ i ∈ Finset.range m, ((i : ℝ) + 1)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  have e3 : ∑ i ∈ Finset.range m, 64 * K ^ 2 / ((i : ℝ) + 1) ^ 2
      = 64 * K ^ 2 * ∑ i ∈ Finset.range m, (((i : ℝ) + 1) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  rw [e1, e2, e3]
  have b1 : 8 * K * ∑ i ∈ Finset.range m, (Real.sqrt ((i : ℝ) + 1))⁻¹
      ≤ 8 * K * (2 * Real.sqrt m) :=
    mul_le_mul_of_nonneg_left (sum_inv_sqrt_le m) (by linarith)
  have b2 : 72 * κ ^ 2 * Λ * ∑ i ∈ Finset.range m, ((i : ℝ) + 1)⁻¹
      ≤ 72 * κ ^ 2 * Λ * (1 + Real.log m) :=
    mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log m) (by linarith)
  have b3 : 64 * K ^ 2 * ∑ i ∈ Finset.range m, (((i : ℝ) + 1) ^ 2)⁻¹
      ≤ 64 * K ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left (sum_inv_sq_le m) (by positivity)
  linarith

end TailBound.Sharp
