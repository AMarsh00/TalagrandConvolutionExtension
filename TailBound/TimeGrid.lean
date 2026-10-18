import TailBound.Reverse

/-! Finite stopping grids. Sorting the actual level crossings gives cells
on which the moving barrier is constant; no stopping-time existence is assumed.
-/

namespace TailBound

structure TimeGrid (a b : ℝ) (Z : Set ℝ) where
  K : ℕ
  z : ℕ → ℝ
  pos : 0 < K
  first : z 0 = a
  last : z K = b
  mono : ∀ k, k < K → z k ≤ z (k+1)
  nocross : ∀ k, k < K → ∀ t ∈ Set.Ioo (z k) (z (k+1)), t ∉ Z

namespace TimeGrid
variable {a b : ℝ} {Z : Set ℝ} (G : TimeGrid a b Z)

lemma mono_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ G.K) : G.z i ≤ G.z j := by
  induction j with
  | zero => obtain rfl := Nat.le_zero.mp hij; rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with he|hl
    · rw [he]
    · exact (ih (by omega) (by omega)).trans (G.mono j (by omega))

lemma range {k : ℕ} (hk : k ≤ G.K) : a ≤ G.z k ∧ G.z k ≤ b := by
  constructor
  · exact G.first.symm.le.trans (G.mono_le (Nat.zero_le k) hk)
  · exact (G.mono_le hk le_rfl).trans G.last.le

lemma cell_subset {k : ℕ} (hk : k < G.K) :
    Set.Icc (G.z k) (G.z (k+1)) ⊆ Set.Icc a b :=
  Set.Icc_subset_Icc (G.range (by omega)).1 (G.range (by omega)).2

end TimeGrid

theorem exists_timeGrid (a b : ℝ) (hab : a ≤ b) (Z : Set ℝ) (hZ : Z.Finite) :
    Nonempty (TimeGrid a b Z) := by
  classical
  rcases hab.eq_or_lt with he|hab
  · subst b
    exact ⟨⟨1,fun _ => a,by omega,rfl,rfl,fun _ _ => le_rfl,
      fun k hk t ht => False.elim ((lt_trans ht.1 ht.2).false)⟩⟩
  let S := insert a (insert b (hZ.inter_of_left (Set.Icc a b)).toFinset)
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hS (v : ℝ) (hv : v ∈ S) : a ≤ v ∧ v ≤ b := by
    rcases Finset.mem_insert.mp hv with he|hv
    · subst v; exact ⟨le_rfl,hab.le⟩
    rcases Finset.mem_insert.mp hv with he|hv
    · subst v; exact ⟨hab.le,le_rfl⟩
    · exact ((hZ.inter_of_left (Set.Icc a b)).mem_toFinset.mp hv).2
  have hcard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨a,haS,b,hbS,hab.ne⟩
  let e := S.orderIsoOfFin (rfl : S.card=S.card)
  let z : ℕ → ℝ := fun k => if hk : k<S.card then (e ⟨k,hk⟩).val else b
  have hz (k : ℕ) (hk : k<S.card) : z k = (e ⟨k,hk⟩).val := dif_pos hk
  have hem (j : Fin S.card) : (e j).val ∈ S := (e j).property
  have hemn (i j : Fin S.card) (hij : i ≤ j) : (e i).val ≤ (e j).val := e.monotone hij
  have hes (v : ℝ) (hv : v ∈ S) : ∃ j : Fin S.card, (e j).val = v :=
    ⟨e.symm ⟨v,hv⟩,by simp⟩
  refine ⟨⟨S.card-1,z,by omega,?_,?_,?_,?_⟩⟩
  · rw [hz 0 (by omega)]
    obtain ⟨j,hj⟩ := hes a haS
    apply le_antisymm _ (hS _ (hem _)).1
    exact (hemn _ _ (Fin.le_def.mpr (Nat.zero_le _))).trans_eq hj
  · rw [hz (S.card-1) (by omega)]
    obtain ⟨j,hj⟩ := hes b hbS
    apply le_antisymm (hS _ (hem _)).2
    exact hj.symm.le.trans (hemn _ _ (Fin.le_def.mpr (show j.val ≤ S.card-1 by have := j.isLt; omega)))
  · intro k hk
    rw [hz k (by omega), hz (k+1) (by omega)]
    exact hemn _ _ (Fin.mk_le_mk.mpr (Nat.le_succ k))
  · intro k hk t ht htZ
    have hk0 : k<S.card := by omega
    have hk1 : k+1<S.card := by omega
    rw [hz k hk0, hz (k+1) hk1] at ht
    have htS : t ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      ((hZ.inter_of_left (Set.Icc a b)).mem_toFinset.mpr
        ⟨htZ, (hS _ (hem _)).1.trans ht.1.le, ht.2.le.trans (hS _ (hem _)).2⟩))
    obtain ⟨j,hj⟩ := hes t htS
    have hkj : (⟨k,hk0⟩ : Fin S.card) < j :=
      e.lt_iff_lt.mp (by change (e ⟨k,hk0⟩).val < (e j).val; rw [hj]; exact ht.1)
    have hle : (e ⟨k+1,hk1⟩).val ≤ t := by
      rw [← hj]
      exact hemn _ _ (Fin.le_def.mpr (show k+1 ≤ j.val from Nat.succ_le_of_lt hkj))
    exact ht.2.not_ge hle

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
namespace RefreshData
variable (D : RefreshData α n)

def crossingSet (ℓ : ℝ) : Set ℝ := {t | t ≤ D.horizon ∧ ∃ x, D.logP t x = ℓ+1}

lemma finite_crossingSet (ℓ : ℝ) (hℓ : 0 < ℓ) : (D.crossingSet ℓ).Finite := by
  have he : Real.exp (ℓ+1) ≠ mean (tensorWeight D.π n) D.f := by
    rw [D.fmass]
    exact ne_of_gt (Real.one_lt_exp_iff.mpr (by linarith))
  have hf := finite_heat_crossings D.π D.f (Real.exp (ℓ+1)) he
  have hp : ((fun t : ℝ => D.horizon-t) ⁻¹' {s | ∃ x, heat D.π D.f s x = Real.exp (ℓ+1)}).Finite :=
    hf.preimage (fun x _ y _ hxy => by linarith)
  apply hp.subset
  rintro t ⟨ht,x,hx⟩
  refine ⟨x,?_⟩
  have hex := congrArg Real.exp hx
  rw [logP, Real.exp_log (D.p_pos ht x)] at hex
  exact hex

lemma exists_stopping_grid (ℓ θ : ℝ) (hℓ : 0 < ℓ) (hθ : θ ≤ 2) :
    Nonempty (TimeGrid θ 2 (D.crossingSet ℓ)) :=
  exists_timeGrid θ 2 hθ _ (D.finite_crossingSet ℓ hℓ)

lemma continuousOn_logP (x : Fin n → α) :
    ContinuousOn (fun t => D.logP t x) (Set.Iic D.horizon) :=
  (D.continuous_p x).continuousOn.log (fun t ht => (D.p_pos ht x).ne')

def barrier (ℓ t : ℝ) : Set (Fin n → α) := {x | ℓ+1 ≤ D.logP t x}

lemma barrier_constant {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    {k : ℕ} (hk : k < G.K) {t u : ℝ}
    (ht : t ∈ Set.Ioo (G.z k) (G.z (k+1)))
    (hu : u ∈ Set.Ioo (G.z k) (G.z (k+1))) (x : Fin n → α) :
    x ∈ D.barrier ℓ t ↔ x ∈ D.barrier ℓ u := by
  have htime (v : ℝ) (hv : v ∈ Set.Icc (G.z k) (G.z (k+1))) : v ≤ D.horizon :=
    ((G.cell_subset hk hv).2).trans D.obs_le_horizon
  have hcross (a b : ℝ) (ha : a ∈ Set.Ioo (G.z k) (G.z (k+1)))
      (hb : b ∈ Set.Ioo (G.z k) (G.z (k+1))) (hab : a ≤ b)
      (hval : (D.logP a x < ℓ+1 ∧ ℓ+1 ≤ D.logP b x) ∨
        (D.logP b x < ℓ+1 ∧ ℓ+1 ≤ D.logP a x)) : False := by
    have hc : ContinuousOn (fun v => D.logP v x) (Set.Icc a b) :=
      (D.continuousOn_logP x).mono (fun v hv => hv.2.trans (htime b ⟨hb.1.le,hb.2.le⟩))
    have hex : ∃ v ∈ Set.Icc a b, D.logP v x = ℓ+1 := by
      rcases hval with h|h
      · exact intermediate_value_Icc hab hc ⟨h.1.le,h.2⟩
      · exact intermediate_value_Icc' hab hc ⟨h.1.le,h.2⟩
    obtain ⟨v,hv,hvx⟩ := hex
    have hvcell : v ∈ Set.Ioo (G.z k) (G.z (k+1)) :=
      ⟨ha.1.trans_le hv.1,hv.2.trans_lt hb.2⟩
    exact G.nocross k hk v hvcell ⟨htime v ⟨hvcell.1.le,hvcell.2.le⟩,x,hvx⟩
  have hforward (t u : ℝ) (ht : t ∈ Set.Ioo (G.z k) (G.z (k+1)))
      (hu : u ∈ Set.Ioo (G.z k) (G.z (k+1))) :
      ℓ+1 ≤ D.logP t x → ℓ+1 ≤ D.logP u x := by
    intro hb
    by_contra hn
    have hnu := lt_of_not_ge hn
    rcases le_total u t with h|h
    · exact hcross u t hu ht h (Or.inl ⟨hnu,hb⟩)
    · exact hcross t u ht hu h (Or.inr ⟨hnu,hb⟩)
  exact ⟨hforward t u ht hu,hforward u t hu ht⟩

def cellBarrier {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ)) (k : ℕ) : Set (Fin n → α) :=
  D.barrier ℓ ((G.z k+G.z (k+1))/2)

lemma logP_le_of_outside_cell {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    {k : ℕ} (hk : k < G.K) (x : Fin n → α) (hx : x ∉ D.cellBarrier G k)
    (t : ℝ) (ht : t ∈ Set.Icc (G.z k) (G.z (k+1))) : D.logP t x ≤ ℓ+1 := by
  have hmid : D.logP ((G.z k+G.z (k+1))/2) x < ℓ+1 := lt_of_not_ge hx
  rcases (G.mono k hk).eq_or_lt with he|hl
  · have ht' : t=G.z k := by linarith [ht.1,ht.2]
    rw [ht']
    have hm : (G.z k+G.z (k+1))/2=G.z k := by linarith
    rw [hm] at hmid
    exact hmid.le
  · have hmidmem : (G.z k+G.z (k+1))/2 ∈ Set.Ioo (G.z k) (G.z (k+1)) := by
      constructor <;> linarith
    have hopen (u : ℝ) (hu : u ∈ Set.Ioo (G.z k) (G.z (k+1))) : D.logP u x ≤ ℓ+1 := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hbad
      exact hx ((D.barrier_constant G hk hu hmidmem x).mp hbad)
    have hc : ContinuousOn (fun u => D.logP u x)
        (closure (Set.Ioo (G.z k) (G.z (k+1)))) := by
      rw [closure_Ioo hl.ne]
      exact (D.continuousOn_logP x).mono
        (fun u hu => ((G.cell_subset hk hu).2).trans D.obs_le_horizon)
    apply le_on_closure hopen hc continuousOn_const
    rwa [closure_Ioo hl.ne]

lemma logP_lt_implies_outside_cell {ℓ θ : ℝ} (G : TimeGrid θ 2 (D.crossingSet ℓ))
    {k : ℕ} (hk : k < G.K) (x : Fin n → α) (hx : D.logP (G.z k) x < ℓ+1) :
    x ∉ D.cellBarrier G k := by
  intro hbad
  let u := (G.z k+G.z (k+1))/2
  have hu : G.z k ≤ u ∧ u ≤ G.z (k+1) := by
    dsimp [u]; constructor <;> linarith [G.mono k hk]
  have hc : ContinuousOn (fun t => D.logP t x) (Set.Icc (G.z k) u) :=
    (D.continuousOn_logP x).mono (fun t ht =>
      ht.2.trans (hu.2.trans ((G.range (by omega)).2.trans D.obs_le_horizon)))
  obtain ⟨v,hv,hvx⟩ := intermediate_value_Icc hu.1 hc ⟨hx.le,hbad⟩
  have hvlo : G.z k < v := lt_of_le_of_ne hv.1 (fun he => hx.ne (by rwa [← he] at hvx))
  have hvhi : v < G.z (k+1) := by
    have hstrict : G.z k < G.z (k+1) := by
      by_contra hn
      have he := le_antisymm (G.mono k hk) (le_of_not_gt hn)
      have hveq : v=G.z k := by dsimp [u] at hv; linarith [hv.1,hv.2]
      exact hx.ne (by rwa [hveq] at hvx)
    dsimp [u] at hv
    linarith [hv.2]
  exact G.nocross k hk v ⟨hvlo,hvhi⟩
    ⟨(hv.2.trans hu.2).trans ((G.range (by omega)).2.trans D.obs_le_horizon),x,hvx⟩

end RefreshData
end TailBound
