import TailBound.TimeGrid

/-!
# Coupling

Construction of the stopped power coupling as a finite
master equation. The starting point is retained as an unchanged state coordinate,
so localization by an event at time θ is represented exactly by its indicator.
-/

open scoped BigOperators

namespace TailBound

inductive JumpKind | sync | left | right
  deriving DecidableEq, Fintype

structure CoupledState (α : Type*) (n : ℕ) where
  start : Fin n → α
  v : Fin n → α
  w : Fin n → α
  alive : Bool
  deriving DecidableEq, Fintype

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
abbrev CouplingEvent (α : Type*) (n : ℕ) := JumpKind × Fin n × α

lemma continuous_switchedPower (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    Continuous (switchedPower d) := by
  unfold switchedPower
  exact Continuous.if_le
    ((continuous_id.add continuous_const).sub
      (continuous_id.rpow_const (fun _ => Or.inr hd0)))
    (continuous_id.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ 1 - d)))
    continuous_id continuous_const (fun r hr => by simp [hr])

noncomputable def couplingNext (B : Set (Fin n → α)) (e : CouplingEvent α n)
    (s : CoupledState α n) : CoupledState α n := by
  classical
  let v := match e.1 with
    | .sync | .left => Function.update s.v e.2.1 e.2.2
    | .right => s.v
  let w := match e.1 with
    | .sync | .right => Function.update s.w e.2.1 e.2.2
    | .left => s.w
  exact ⟨s.start, v, w, s.alive && decide (v ∉ B)⟩

noncomputable def killNode (B : Set (Fin n → α)) (s : CoupledState α n) : CoupledState α n := by
  classical
  exact {s with alive := s.alive && decide (s.v ∉ B)}

noncomputable def mapTransfer {S : Type*} [DecidableEq S] (F : S → S) (s r : S) : ℝ :=
  if F r=s then 1 else 0

lemma mapTransfer_nonneg {S : Type*} [DecidableEq S] (F : S → S) (s r : S) :
    0 ≤ mapTransfer F s r := by unfold mapTransfer; split_ifs <;> norm_num

lemma mapTransfer_column {S : Type*} [Fintype S] [DecidableEq S] (F : S → S) (r : S) :
    ∑ s, mapTransfer F s r = 1 := by simp [mapTransfer]

lemma mapTransfer_pairing {S : Type*} [Fintype S] [DecidableEq S]
    (F : S → S) (μ h : S → ℝ) :
    ∑ s, Talagrand.matVec (mapTransfer F) μ s * h s = ∑ r, μ r * h (F r) := by
  unfold Talagrand.matVec
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp [mapTransfer]

namespace RefreshData

variable (D : RefreshData α n)

noncomputable def coupledExponent (ℓ θ : ℝ) (s : CoupledState α n) : ℝ :=
  if s.alive then D.exponent ℓ θ s.start else 0

noncomputable def couplingRate (ℓ θ t : ℝ) (e : CouplingEvent α n)
    (s : CoupledState α n) : ℝ :=
  let a := D.ratio t e.2.1 e.2.2 s.v
  let b := switchedPower (D.coupledExponent ℓ θ s) a
  D.π e.2.2 * match e.1 with
    | .sync => min a b
    | .left => max (a - b) 0
    | .right => max (b - a) 0

omit [Nonempty α] in
lemma coupledExponent_bounds (ℓ θ : ℝ) (s : CoupledState α n) :
    0 ≤ D.coupledExponent ℓ θ s ∧ D.coupledExponent ℓ θ s ≤ 1 := by
  unfold coupledExponent
  split_ifs
  · have hh := D.exponent_bounds ℓ θ s.start
    constructor <;> linarith [hh.1, hh.2]
  · norm_num

omit [Nonempty α] in
lemma couplingRate_nonneg (ℓ θ t : ℝ) (ht : t ≤ D.horizon)
    (e : CouplingEvent α n) (s : CoupledState α n) : 0 ≤ D.couplingRate ℓ θ t e s := by
  have ha := D.ratio_pos ht e.2.1 e.2.2 s.v
  have hd := D.coupledExponent_bounds ℓ θ s
  have hb := (switchedPower_bounds _ _ ha hd.1 hd.2).1
  unfold couplingRate
  apply mul_nonneg (D.πnonneg _)
  cases e.1
  · exact le_min ha.le hb.le
  · exact le_max_right _ _
  · exact le_max_right _ _

omit [Nonempty α] in
lemma couplingRate_continuousOn (ℓ θ : ℝ) (e : CouplingEvent α n) (s : CoupledState α n) :
    ContinuousOn (fun t => D.couplingRate ℓ θ t e s) (Set.Iic D.horizon) := by
  have ha := D.continuousOn_ratio e.2.1 e.2.2 s.v
  have hd := D.coupledExponent_bounds ℓ θ s
  have hb := (continuous_switchedPower _ hd.1 hd.2).comp_continuousOn ha
  unfold couplingRate
  apply ContinuousOn.const_mul
  cases e.1
  · exact ha.inf hb
  · exact (ha.sub hb).sup continuousOn_const
  · exact (hb.sub ha).sup continuousOn_const

noncomputable def initialCoupling (θ : ℝ) (s : CoupledState α n) : ℝ :=
  ∑ x, D.density θ x * (if s = ⟨x, x, x, true⟩ then 1 else 0)

omit [Nonempty α] in
lemma initialCoupling_nonneg (θ : ℝ) (hθ : θ ≤ D.horizon) (s : CoupledState α n) :
    0 ≤ D.initialCoupling θ s := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (D.density_nonneg hθ x)
  split_ifs <;> norm_num

omit [Nonempty α] in
lemma initialCoupling_mass (θ : ℝ) : ∑ s, D.initialCoupling θ s = 1 := by
  unfold initialCoupling
  rw [Finset.sum_comm]
  simpa using D.density_mass θ

omit [Nonempty α] in
lemma initialCoupling_pairing (θ : ℝ) (F : CoupledState α n → ℝ) :
    ∑ s, D.initialCoupling θ s * F s = ∑ x, D.density θ x * F ⟨x, x, x, true⟩ := by
  unfold initialCoupling
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

noncomputable def couplingMatrix {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    (k : ℕ) (t : ℝ) : CoupledState α n → CoupledState α n → ℝ :=
  eventForward (couplingNext (D.cellBarrier G k)) (D.couplingRate ℓ θ t)

noncomputable def couplingTransfer (ℓ t : ℝ) : CoupledState α n → CoupledState α n → ℝ :=
  mapTransfer (killNode (D.barrier ℓ t))

omit [Nonempty α] in
lemma couplingMatrix_continuous {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    {k : ℕ} (hk : k < G.K) (s r : CoupledState α n) :
    ContinuousOn (fun t => D.couplingMatrix G k t s r) (Set.Icc (G.z k) (G.z (k + 1))) :=
  eventForward_continuousOn _ _ (fun e s => (D.couplingRate_continuousOn ℓ θ e s).mono
    (fun _t ht => ((G.cell_subset hk ht).2).trans D.obs_le_horizon)) s r

/-- A master-equation realization of the stopped coupling. The existence

theorem `exists_stoppedCoupling` constructs this structure. -/
structure StoppedCoupling (ℓ θ : ℝ) where
  grid : TimeGrid θ 2 (D.crossingSet ℓ)
  law : ℕ → ℝ → CoupledState α n → ℝ
  flow : Talagrand.IsGluedFlow grid.K grid.z (D.couplingMatrix grid)
    (fun k => D.couplingTransfer ℓ (grid.z k)) (D.initialCoupling θ) law

omit [Nonempty α] in
theorem exists_stoppedCoupling (ℓ θ : ℝ) (hℓ : 0 < ℓ) (hθ : θ ≤ 2) :
    Nonempty (D.StoppedCoupling ℓ θ) := by
  obtain ⟨G⟩ := D.exists_stopping_grid ℓ θ hℓ hθ
  obtain ⟨y, hy⟩ := Talagrand.exists_gluedFlow G.K G.z (D.couplingMatrix G)
    (fun k => D.couplingTransfer ℓ (G.z k)) (D.initialCoupling θ) G.mono
    (fun k hk s r => D.couplingMatrix_continuous G hk s r)
  exact ⟨⟨G, y, hy⟩⟩

namespace StoppedCoupling

variable {D} {ℓ θ : ℝ} (C : D.StoppedCoupling ℓ θ)

omit [Nonempty α] in
lemma nonneg (hθ : θ ≤ 2) {k : ℕ} (hk : k < C.grid.K) (t : ℝ)
    (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) (s : CoupledState α n) :
    0 ≤ C.law k t s := by
  apply Talagrand.gluedFlow_nonneg C.flow
    (fun k hk s r => D.couplingMatrix_continuous C.grid hk s r)
    (fun k hk t ht s r hsr => eventForward_offdiag _ _
      (D.couplingRate_nonneg ℓ θ t (((C.grid.cell_subset hk ht).2).trans D.obs_le_horizon)) s r hsr)
    (fun k s r => mapTransfer_nonneg _ s r)
    (D.initialCoupling_nonneg θ (hθ.trans D.obs_le_horizon)) k hk t ht s

omit [Nonempty α] in
lemma mass {k : ℕ} (hk : k < C.grid.K) (t : ℝ)
    (ht : t ∈ Set.Icc (C.grid.z k) (C.grid.z (k + 1))) : ∑ s, C.law k t s = 1 := by
  have hh := Talagrand.gluedFlow_mass C.flow
    (fun k hk t ht r => eventForward_column _ _ r)
    (fun k r => mapTransfer_column _ r) k hk t ht
  rwa [D.initialCoupling_mass θ] at hh

noncomputable def terminal (s : CoupledState α n) : ℝ := C.law (C.grid.K - 1) 2 s

omit [Nonempty α] in
lemma terminal_nonneg (hθ : θ ≤ 2) (s : CoupledState α n) : 0 ≤ C.terminal s := by
  apply C.nonneg hθ (show C.grid.K - 1<C.grid.K by have := C.grid.pos; omega)
  have he : C.grid.K - 1 + 1=C.grid.K := by have := C.grid.pos; omega
  rw [he, C.grid.last]
  exact ⟨(C.grid.range (by omega)).2, le_rfl⟩

omit [Nonempty α] in
lemma terminal_mass : ∑ s, C.terminal s = 1 := by
  apply C.mass (show C.grid.K - 1<C.grid.K by have := C.grid.pos; omega)
  have he : C.grid.K - 1 + 1=C.grid.K := by have := C.grid.pos; omega
  rw [he, C.grid.last]
  exact ⟨(C.grid.range (by omega)).2, le_rfl⟩

end StoppedCoupling
end RefreshData
end TailBound
