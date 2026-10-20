import TailBound.BridgeEnergy

/-!
# Bridge Chi

One-coordinate quadratic estimates for the explicit finite-alphabet bridge.
The atom at the current second coordinate must be retained in the denominator
of the unshifted horizontal estimate.
-/

open scoped BigOperators

namespace TailBound

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma quadratic_mixture_bound {v p A B : ℝ}
    (hv : 0 ≤ v) (hp : 0 ≤ p) (hA : 0 < A) (hB : 0 < B) :
    (v - p) ^ 2 / (A + B * v) ≤ v / B + p ^ 2 / A := by
  have hd : 0 < A + B * v := add_pos_of_pos_of_nonneg hA (mul_nonneg hB.le hv)
  apply (div_le_iff₀ hd).mpr
  have he : (v / B + p ^ 2 / A) * (A + B * v) - (v - p) ^ 2 =
      A * v / B + B * v * p ^ 2 / A + 2 * v * p := by
    field_simp
    ring
  have hnon : 0 ≤ A * v / B + B * v * p ^ 2 / A + 2 * v * p := by positivity
  linarith

lemma mixture_base_quadratic (q : α → ℝ) (hq : ∀ u, 0 < q u)
    {p A B : ℝ} (hp : ∑ u, q u = p) (hA : 0 < A) (hB : 0 < B) (y : α) :
    (∑ u, (q u - p * (if u = y then 1 else 0)) ^ 2 /
      (A * (if u = y then 1 else 0) + B * q u)) ≤ p / B + p ^ 2 / A := by
  have hp0 : 0 ≤ p := hp ▸ Finset.sum_nonneg (fun u _ => (hq u).le)
  calc
    _ ≤ ∑ u, (q u / B + (p ^ 2 / A) * (if u = y then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u = y
      · simp only [hu, if_true, mul_one]
        exact quadratic_mixture_bound (hq y).le hp0 hA hB
      · simp only [hu, if_false, mul_zero, sub_zero, zero_add, add_zero]
        exact le_of_eq (by field_simp [(hq u).ne'])
    _ = p / B + p ^ 2 / A := by
      simp [Finset.sum_add_distrib, ← Finset.sum_div, hp]

lemma mixture_shift_quadratic (q : α → ℝ) (hq : ∀ u, 0 < q u)
    {p A B : ℝ} (hp : ∑ u, q u = p) (hA : 0 ≤ A) (hB : 0 < B) (y g : α) :
    (∑ u, (q u - p * (if u = g then 1 else 0)) ^ 2 /
      (A * (if u = y then 1 else 0) + B * q u)) ≤ 2 * p ^ 2 / (B * q g) := by
  have hgp : q g ≤ p := by
    rw [← hp]
    exact Finset.single_le_sum (fun u _ => (hq u).le) (Finset.mem_univ g)
  have hp0 : 0 < p := (hq g).trans_le hgp
  have hpoint (u : α) :
      (q u - p * (if u = g then 1 else 0)) ^ 2 /
        (A * (if u = y then 1 else 0) + B * q u) ≤
        q u / B + p ^ 2 / (B * q g) * (if u = g then 1 else 0) := by
    have hbq : 0 < B * q u := mul_pos hB (hq u)
    have hden : B * q u ≤ A * (if u = y then 1 else 0) + B * q u := by
      split_ifs <;> linarith
    apply (div_le_div_of_nonneg_left (sq_nonneg _) hbq hden).trans
    by_cases hu : u = g
    · subst u
      simp only [if_true, mul_one]
      apply (div_le_iff₀ (mul_pos hB (hq g))).mpr
      have he : (q g / B + p ^ 2 / (B * q g)) * (B * q g) = (q g) ^ 2 + p ^ 2 := by
        field_simp [(hq g).ne']
      rw [he]
      nlinarith [mul_nonneg (hq g).le hp0.le]
    · simp only [hu, if_false, mul_zero, sub_zero, add_zero]
      exact le_of_eq (by field_simp [(hq u).ne'])
  calc
    _ ≤ ∑ u, (q u / B + p ^ 2 / (B * q g) * (if u = g then 1 else 0)) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = p / B + p ^ 2 / (B * q g) := by
      simp [Finset.sum_add_distrib, ← Finset.sum_div, hp]
    _ ≤ 2 * p ^ 2 / (B * q g) := by
      have hpb : p / B ≤ p ^ 2 / (B * q g) := by
        apply (le_div_iff₀ (mul_pos hB (hq g))).mpr
        have he : p / B * (B * q g) = p * q g := by field_simp
        rw [he]
        nlinarith [mul_le_mul_of_nonneg_left hgp hp0.le]
      calc
        _ ≤ p ^ 2 / (B * q g) + p ^ 2 / (B * q g) := add_le_add hpb le_rfl
        _ = 2 * p ^ 2 / (B * q g) := by ring

noncomputable def bridgeChi (π : α → ℝ) (a r : ℝ) (z x y g Q : α) : ℝ :=
  π g * (bridgeH π (r * a) z g / bridgeH π (r * a) z x) *
    ∑ u, (bridgeLaw π a r z x Q u - bridgeLaw π a r z g Q u) ^ 2 /
      bridgeLaw π a r z x y u

lemma bridgeChi_formula (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (z x y g Q : α) :
    bridgeChi π a r z x y g Q =
      π g * (bridgeH π (r * a) z x - bridgeH π (r * a) z g) ^ 2 * (1 - r) ^ 2 /
        ((bridgeH π (r * a) z x) ^ 2 * bridgeH π (r * a) z g) *
      ∑ u, (π u * bridgeH π a z u - π z * (if u = Q then 1 else 0)) ^ 2 /
        (r * bridgeH π a z x * (if u = y then 1 else 0) +
          (1 - r) * (π u * bridgeH π a z u)) := by
  have hra0 := mul_nonneg hr0.le ha0
  have hra1 : r * a < 1 := by nlinarith
  have hx := bridgeH_pos π hπ hra0 hra1 z x
  have hg := bridgeH_pos π hπ hra0 hra1 z g
  have hpg := hπ g
  have hrm := sub_pos.mpr hr1
  unfold bridgeChi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [bridgeLaw_difference π a r z x g Q u hx.ne' hg.ne']
  unfold bridgeLaw
  field_simp
  ring

/-- The unshifted difference retains the atom at y in the bridge law. -/
theorem bridgeChi_base_bound (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (hmass : ∑ u, π u = 1) {a r : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (z x y g : α) :
    bridgeChi π a r z x y g y ≤
      π g * r * (1 - r) * π z * (bridgeH π a z x - bridgeH π a z g) ^ 2 /
        (bridgeH π (r * a) z x * bridgeH π (r * a) z g * bridgeH π a z x) := by
  have hx0 := bridgeH_pos π hπ ha0 ha1 z x
  have hqx : ∀ u, 0 < π u * bridgeH π a z u :=
    fun u => mul_pos (hπ u) (bridgeH_pos π hπ ha0 ha1 z u)
  have hra0 := mul_nonneg hr0.le ha0
  have hra1 : r * a < 1 := by nlinarith
  have hx := bridgeH_pos π hπ hra0 hra1 z x
  have hg := bridgeH_pos π hπ hra0 hra1 z g
  have hpg := hπ g
  have hrm := sub_pos.mpr hr1
  have hh := mixture_base_quadratic (fun u => π u * bridgeH π a z u) hqx
    (bridgeH_mean π hmass a z) (mul_pos hr0 hx0) (sub_pos.mpr hr1) y
  rw [bridgeChi_formula π hπ ha0 ha1 hr0 hr1]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  apply le_of_eq
  have he := bridgeH_interpolation π a r z x
  have he' := bridgeH_interpolation π a r z g
  field_simp [hrm.ne']
  rw [he, he']
  ring

/-- The shifted difference is estimated using the absolutely continuous
part of the reference bridge. -/
theorem bridgeChi_shift_bound (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (hmass : ∑ u, π u = 1) {a r : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (z x y g : α) :
    bridgeChi π a r z x y g g ≤
      2 * r ^ 2 * (1 - r) * (π z) ^ 2 * (bridgeH π a z x - bridgeH π a z g) ^ 2 /
        ((bridgeH π (r * a) z x) ^ 2 * bridgeH π (r * a) z g * bridgeH π a z g) := by
  have hx0 := bridgeH_pos π hπ ha0 ha1 z x
  have hqx : ∀ u, 0 < π u * bridgeH π a z u :=
    fun u => mul_pos (hπ u) (bridgeH_pos π hπ ha0 ha1 z u)
  have hra0 := mul_nonneg hr0.le ha0
  have hra1 : r * a < 1 := by nlinarith
  have hx := bridgeH_pos π hπ hra0 hra1 z x
  have hg := bridgeH_pos π hπ hra0 hra1 z g
  have hpg := hπ g
  have hga := bridgeH_pos π hπ ha0 ha1 z g
  have hrm := sub_pos.mpr hr1
  have hh := mixture_shift_quadratic (fun u => π u * bridgeH π a z u) hqx
    (bridgeH_mean π hmass a z) (mul_nonneg hr0.le hx0.le) (sub_pos.mpr hr1) y g
  rw [bridgeChi_formula π hπ ha0 ha1 hr0 hr1]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  apply le_of_eq
  have he := bridgeH_interpolation π a r z x
  have he' := bridgeH_interpolation π a r z g
  field_simp [hrm.ne', hpg.ne', hga.ne']
  rw [he, he']
  ring

lemma bridge_scalars {a r p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    let H := r * a + (1 - r * a) * p
    let h := a + (1 - a) * p
    0 < 1 - r * a ∧ p ≤ H ∧ r * a ≤ H ∧ p ≤ h ∧ a ≤ h ∧
      (1 - r) * (1 - a) ≤ (1 - r * a) ^ 2 := by
  have hra1 : r * a < 1 := by nlinarith
  have hp := mul_nonneg (mul_nonneg hr0.le ha0.le) (sub_nonneg.mpr hp1)
  have hp' := mul_nonneg ha0.le (sub_nonneg.mpr hp1)
  have hm := mul_nonneg (sub_nonneg.mpr hr1.le) (sub_nonneg.mpr ha1.le)
  have hra : 0 ≤ 1 - r * a := by linarith
  have h1 : 1 - r ≤ 1 - r * a := by nlinarith
  have h2 : 1 - a ≤ 1 - r * a := by nlinarith
  refine ⟨sub_pos.mpr hra1, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg hra hp0.le]
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha1.le) hp0.le]
  · nlinarith [mul_le_mul h1 h2 (sub_nonneg.mpr ha1.le) hra]

lemma bridge_base_off_scalar {a r p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    r * (1 - r) * a ^ 2 / ((1 - r * a) * (r * a + (1 - r * a) * p) * (1 - a)) ≤ r / (p * (1 - a)) := by
  obtain ⟨hd, hpH, haH, hph, hah, hsq⟩ := bridge_scalars ha0 ha1 hr0 hr1 hp0 hp1
  have ham := sub_pos.mpr ha1
  have hrm := sub_pos.mpr hr1
  have hH : 0 < r * a + (1 - r * a) * p := hp0.trans_le hpH
  have hsmall : (1 - r) * a ^ 2 ≤ 1 - r * a := by
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_left ha2 (sub_nonneg.mpr hr1.le)
    nlinarith
  have key : p * ((1 - r) * a ^ 2) ≤ (r * a + (1 - r * a) * p) * (1 - r * a) :=
    mul_le_mul hpH hsmall (by positivity) hH.le
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_left key (mul_nonneg hr0.le (sub_nonneg.mpr ha1.le)) using 1 <;> ring

lemma bridge_base_on_scalar {a r p w : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hw : 0 ≤ w) :
    w * r * (1 - r) * a ^ 2 / ((r * a + (1 - r * a) * p) * (1 - r * a) * (a + (1 - a) * p)) ≤ w * r / p ^ 2 := by
  obtain ⟨hd, hpH, haH, hph, hah, hsq⟩ := bridge_scalars ha0 ha1 hr0 hr1 hp0 hp1
  have ham := sub_pos.mpr ha1
  have hrm := sub_pos.mpr hr1
  have hH : 0 < r * a + (1 - r * a) * p := hp0.trans_le hpH
  have hh : 0 < a + (1 - a) * p := hp0.trans_le hph
  have hsmall : (1 - r) * a ^ 2 ≤ 1 - r * a := by
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_left ha2 (sub_nonneg.mpr hr1.le)
    nlinarith
  have hprod : p ^ 2 ≤ (r * a + (1 - r * a) * p) * (a + (1 - a) * p) := by
    nlinarith [mul_le_mul hpH hph hp0.le hH.le]
  have key := mul_le_mul hprod hsmall (by positivity : 0 ≤ (1 - r) * a ^ 2)
    (mul_nonneg hH.le hh.le)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_left key (mul_nonneg hw hr0.le) using 1 <;> ring

lemma bridge_shift_off_scalar {a r p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    2 * r ^ 2 * (1 - r) * a ^ 2 / ((1 - r * a) ^ 2 * (r * a + (1 - r * a) * p) * (a + (1 - a) * p)) ≤ 2 * r / (1 - a) := by
  obtain ⟨hd, hpH, haH, hph, hah, hsq⟩ := bridge_scalars ha0 ha1 hr0 hr1 hp0 hp1
  have ham := sub_pos.mpr ha1
  have hrm := sub_pos.mpr hr1
  have hH : 0 < r * a + (1 - r * a) * p := hp0.trans_le hpH
  have hh : 0 < a + (1 - a) * p := hp0.trans_le hph
  have hprod : r * a ^ 2 ≤ (r * a + (1 - r * a) * p) * (a + (1 - a) * p) := by
    nlinarith [mul_le_mul haH hah ha0.le hH.le]
  have key := mul_le_mul hprod hsq
    (by positivity : 0 ≤ (1 - r) * (1 - a)) (mul_nonneg hH.le hh.le)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ 2 * r) using 1 <;> ring

lemma bridge_shift_on_scalar {a r p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    2 * r ^ 2 * (1 - r) * a ^ 2 / ((r * a + (1 - r * a) * p) ^ 2 * (1 - r * a) * (1 - a)) ≤ 2 * r / (p * (1 - a)) := by
  obtain ⟨hd, hpH, haH, hph, hah, hsq⟩ := bridge_scalars ha0 ha1 hr0 hr1 hp0 hp1
  have ham := sub_pos.mpr ha1
  have hrm := sub_pos.mpr hr1
  have hH : 0 < r * a + (1 - r * a) * p := hp0.trans_le hpH
  have hprod : r * a * p ≤ (r * a + (1 - r * a) * p) ^ 2 := by
    nlinarith [mul_le_mul haH hpH hp0.le hH.le]
  have hsmall : (1 - r) * a ≤ 1 - r * a := by nlinarith
  have key := mul_le_mul hprod hsmall
    (by positivity : 0 ≤ (1 - r) * a) (sq_nonneg _)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ 2 * r * (1 - a)) using 1 <;> ring

/-- The combined one-coordinate coefficient is O(r/(1-a)), uniformly in
the start states, replacement state, and conditioned endpoint. -/
theorem bridgeChi_pair_bound (π : α → ℝ) (hπ : ∀ u, 0 < π u)
    (hmass : ∑ u, π u = 1) {a r m : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hm : 0 < m) (hmin : ∀ u, m ≤ π u) (z x y g : α) :
    bridgeChi π a r z x y g y + bridgeChi π a r z x y g g ≤
      3 * r / ((1 - a) * m ^ 2) := by
  have hupper (u : α) : π u ≤ 1 := by
    rw [← hmass]
    exact Finset.single_le_sum (fun v _ => (hπ v).le) (Finset.mem_univ u)
  have hm1 : m ≤ 1 := (hmin z).trans (hupper z)
  have hm2 : m ^ 2 ≤ m := by nlinarith
  have hm21 : m ^ 2 ≤ 1 := by nlinarith
  have hmp : m ^ 2 ≤ π z := hm2.trans (hmin z)
  have hmp2 : m ^ 2 ≤ (π z) ^ 2 := by nlinarith [hmin z, hπ z]
  have ham := sub_pos.mpr ha1
  have hrm := sub_pos.mpr hr1
  have hd : 0 < (1 - a) * m ^ 2 := by positivity
  have hdenp : (1 - a) * m ^ 2 ≤ π z * (1 - a) := by nlinarith
  have hdenp2 : (1 - a) * m ^ 2 ≤ (π z) ^ 2 := by nlinarith
  have hden1 : (1 - a) * m ^ 2 ≤ 1 - a := by nlinarith
  have hb := bridgeChi_base_bound π hπ hmass ha0.le ha1 hr0 hr1 z x y g
  have hs := bridgeChi_shift_bound π hπ hmass ha0.le ha1 hr0 hr1 z x y g
  have hfinish : ∀ B S : ℝ, B ≤ r / ((1 - a) * m ^ 2) →
      S ≤ 2 * r / ((1 - a) * m ^ 2) → B + S ≤ 3 * r / ((1 - a) * m ^ 2) := by
    intro B S hB hS
    calc B + S ≤ r / ((1 - a) * m ^ 2) + 2 * r / ((1 - a) * m ^ 2) := add_le_add hB hS
      _ = 3 * r / ((1 - a) * m ^ 2) := by ring
  by_cases hx : x = z
  · subst x
    by_cases hg : g = z
    · subst g
      simp only [bridgeChi, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div,
        Finset.sum_const_zero, mul_zero, zero_add]
      positivity
    · have hb' : bridgeChi π a r z z y g y ≤
          π g * r * (1 - r) * a ^ 2 / ((r * a + (1 - r * a) * π z) * (1 - r * a) * (a + (1 - a) * π z)) := by
        convert hb using 1; simp only [bridgeH, if_true, mul_one, hg, if_false, mul_zero, zero_add]
        field_simp [(hπ z).ne']
        ring
      have hs' : bridgeChi π a r z z y g g ≤
          2 * r ^ 2 * (1 - r) * a ^ 2 / ((r * a + (1 - r * a) * π z) ^ 2 * (1 - r * a) * (1 - a)) := by
        convert hs using 1; simp only [bridgeH, if_true, mul_one, hg, if_false, mul_zero, zero_add]
        field_simp [(hπ z).ne']
        ring
      apply hfinish
      · apply (hb'.trans (bridge_base_on_scalar ha0 ha1 hr0 hr1 (hπ z) (hupper z) (hπ g).le)).trans
        apply (div_le_div_of_nonneg_right
          (show π g * r ≤ r by nlinarith [hupper g]) (sq_nonneg (π z))).trans
        exact div_le_div_of_nonneg_left hr0.le hd hdenp2
      · apply (hs'.trans (bridge_shift_on_scalar ha0 ha1 hr0 hr1 (hπ z) (hupper z))).trans
        exact div_le_div_of_nonneg_left (by positivity) hd hdenp
  · by_cases hg : g = z
    · subst g
      have hb' : bridgeChi π a r z x y z y ≤
          r * (1 - r) * a ^ 2 / ((1 - r * a) * (r * a + (1 - r * a) * π z) * (1 - a)) := by
        convert hb using 1; simp only [bridgeH, if_true, mul_one, hx, if_false, mul_zero, zero_add]
        field_simp [(hπ z).ne']
        ring
      have hs' : bridgeChi π a r z x y z z ≤
          2 * r ^ 2 * (1 - r) * a ^ 2 / ((1 - r * a) ^ 2 * (r * a + (1 - r * a) * π z) * (a + (1 - a) * π z)) := by
        convert hs using 1; simp only [bridgeH, if_true, mul_one, hx, if_false, mul_zero, zero_add]
        field_simp [(hπ z).ne']
        ring
      apply hfinish
      · apply (hb'.trans (bridge_base_off_scalar ha0 ha1 hr0 hr1 (hπ z) (hupper z))).trans
        exact div_le_div_of_nonneg_left hr0.le hd hdenp
      · apply (hs'.trans (bridge_shift_off_scalar ha0 ha1 hr0 hr1 (hπ z) (hupper z))).trans
        exact div_le_div_of_nonneg_left (by positivity) hd hden1
    · have hb0 : bridgeChi π a r z x y g y ≤ 0 := by
        simpa [bridgeH, hx, hg] using hb
      have hs0 : bridgeChi π a r z x y g g ≤ 0 := by
        simpa [bridgeH, hx, hg] using hs
      have hzero : bridgeChi π a r z x y g y + bridgeChi π a r z x y g g ≤ 0 := by linarith
      exact hzero.trans (by positivity)

end TailBound
