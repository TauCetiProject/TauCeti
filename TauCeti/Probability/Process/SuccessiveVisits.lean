/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Process.HittingTime
public import TauCeti.Probability.Process.SuccessorArray
public import TauCeti.Combinatorics.Enumerative.ExcursionProcess

/-!
# Successive visits as stopping times

`successiveVisit X a k` is the time of the visit indexed by `k` to `a`, counting the
first entrance as visit zero and assigning infinity when the visit does not exist.
Its sublevel events are characterized by finite visit counts, so it is a stopping
time for every filtration to which `X` is adapted. No topology or countability of
the state space is required; measurability of the singleton of `a` suffices.

The finite-value characterization connects these stopping times to the combinatorial
`visitTime`, whose value at nonexistent visits is zero. The next-visit identity uses
`hittingAfter` starting strictly after the current visit, including when there is no
next visit. For realized consecutive visits, the return gap is the excursion length
plus one. These identities allow stopping-time arguments to be applied to excursions.

## References

* J. R. Norris, *Markov Chains* (1997), §1.5, for successive passage times and excursion lengths.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω α : Type*}

/-- The time of the visit indexed by `k` to `a`, or infinity if it does not exist.
Visit zero is the first entrance, which can occur at time zero. -/
def successiveVisit (X : ℕ → Ω → α) (a : α) (k : ℕ) : Ω → WithTop ℕ :=
  hittingAfter (fun n ω => visitCount (fun i => X i ω) a (n + 1)) (Set.Ioi k) 0

/-- Successive visits are hitting times of the cumulative visit count. -/
theorem successiveVisit_def (X : ℕ → Ω → α) (a : α) (k : ℕ) :
    successiveVisit X a k =
      hittingAfter (fun n ω => visitCount (fun i => X i ω) a (n + 1)) (Set.Ioi k) 0 := (rfl)

variable {X : ℕ → Ω → α} {a : α} {k n : ℕ} {ω : Ω}

/-- The visit indexed by `k` occurs by `n` exactly when at least `k + 1` visits
have occurred through time `n`. -/
@[simp]
theorem successiveVisit_le_iff :
    successiveVisit X a k ω ≤ n ↔ k < visitCount (fun i => X i ω) a (n + 1) := by
  rw [successiveVisit_def]
  simp only [Nat.cast_withTop]
  rw [hittingAfter_le_iff (i := n)]
  constructor
  · rintro ⟨j, hj, hk⟩
    exact hk.trans_le (visitCount_monotone _ _ (Nat.succ_le_succ hj.2))
  · intro hk
    exact ⟨n, ⟨Nat.zero_le n, le_rfl⟩, hk⟩

/-- The visit indexed by `k` occurs strictly before `n` exactly when at least `k + 1`
visits have occurred before time `n`. -/
@[simp]
theorem successiveVisit_lt_iff :
    successiveVisit X a k ω < n ↔ k < visitCount (fun i => X i ω) a n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [← successiveVisit_le_iff (n := n)]
    simp only [Nat.cast_withTop]
    rw [WithTop.lt_iff_exists_coe, WithTop.le_coe_iff]
    simp only [WithTop.coe_lt_coe, Nat.lt_succ_iff]

/-- A finite successive visit records both the state and the number of earlier visits. -/
@[simp]
theorem successiveVisit_eq_coe_iff :
    successiveVisit X a k ω = n ↔
      X n ω = a ∧ visitCount (fun i => X i ω) a n = k := by
  classical
  rw [eq_iff_le_not_lt, successiveVisit_le_iff, successiveVisit_lt_iff, not_lt,
    visitCount_succ]
  split_ifs with hx <;> simp_all; omega

/-- A missing visit is infinity, rather than the combinatorial visit time's junk value. -/
@[simp]
theorem successiveVisit_eq_top_iff :
    successiveVisit X a k ω = ⊤ ↔
      ¬ ∃ n, X n ω = a ∧ visitCount (fun i => X i ω) a n = k := by
  constructor
  · rintro ht ⟨n, hn⟩
    have := successiveVisit_eq_coe_iff.mpr hn
    simp [ht] at this
  · intro h
    by_contra ht
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    exact h ⟨n, successiveVisit_eq_coe_iff.mp hn.symm⟩

/-- At an existing visit, the stopping time agrees with the combinatorial enumeration. -/
theorem successiveVisit_eq_visitTime
    (h : ∃ n, X n ω = a ∧ visitCount (fun i => X i ω) a n = k) :
    successiveVisit X a k ω = visitTime (fun i => X i ω) a k := by
  obtain ⟨n, hx, hc⟩ := h
  rw [← hc, visitTime_visitCount hx]
  exact successiveVisit_eq_coe_iff.mpr ⟨hx, rfl⟩

/-- Every successive visit is finite exactly when the state is visited infinitely often. -/
theorem forall_successiveVisit_lt_top_iff :
    (∀ k, successiveVisit X a k ω < ⊤) ↔ {n | X n ω = a}.Infinite := by
  constructor
  · intro h
    by_contra hf
    have hf := Set.not_infinite.mp hf
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt (h hf.toFinset.card))
    obtain ⟨hx, hc⟩ := successiveVisit_eq_coe_iff.mp hn.symm
    have := visitCount_lt_card hf hx
    omega
  · intro h k
    exact lt_top_iff_ne_top.mpr fun ht =>
      successiveVisit_eq_top_iff.mp ht (exists_visitCount_of_infinite h k)

/-- Successive visits commute with a change of sample space. In particular, their laws
can be transferred by composing the measurable path functional with a path-law identity. -/
@[simp]
theorem successiveVisit_comp {Ω' : Type*} (X : ℕ → Ω → α) (f : Ω' → Ω)
    (a : α) (k : ℕ) :
    successiveVisit (fun n => X n ∘ f) a k = successiveVisit X a k ∘ f := (rfl)

/-- Visit times increase with the visit index, including after the last visit. -/
theorem monotone_successiveVisit (X : ℕ → Ω → α) (a : α) (ω : Ω) :
    Monotone fun k => successiveVisit X a k ω := by
  intro i j hij
  apply WithTop.forall_le_coe_iff_le.mp
  intro n hn
  exact successiveVisit_le_iff.mpr (hij.trans_lt (successiveVisit_le_iff.mp hn))

/-- The zeroth visit is the first entrance, with time zero allowed. -/
@[simp]
theorem successiveVisit_zero (X : ℕ → Ω → α) (a : α) :
    successiveVisit X a 0 = hittingAfter X {a} 0 := by
  funext ω
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  simp only [← Nat.cast_withTop]
  rw [successiveVisit_le_iff]
  simp only [Nat.cast_withTop]
  rw [hittingAfter_le_iff (i := n)]
  simp only [visitCount_pos_iff, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, ⟨Nat.zero_le j, Nat.le_of_lt_succ hj⟩, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, Nat.lt_succ_of_le hj.2, hx⟩

/-- After a finite visit, the next visit is the first entrance strictly after that time.
This equality also covers a nonexistent next visit. -/
theorem successiveVisit_succ_eq_hittingAfter (h : successiveVisit X a k ω = n) :
    successiveVisit X a (k + 1) ω = hittingAfter X {a} (n + 1) ω := by
  obtain ⟨hx, hc⟩ := successiveVisit_eq_coe_iff.mp h
  apply WithTop.eq_of_forall_le_coe_iff
  intro m
  simp only [← Nat.cast_withTop]
  rw [successiveVisit_le_iff]
  simp only [Nat.cast_withTop]
  rw [hittingAfter_le_iff (i := m)]
  constructor
  · intro hm
    let j := visitTime (fun i => X i ω) a (k + 1)
    have hj := apply_visitTime_of_lt_visitCount hm
    have hjc : visitCount (fun i => X i ω) a j = k + 1 :=
      visitCount_visitTime_of_lt_visitCount hm
    have hnj : n < j := by
      by_contra hn
      exact Nat.not_succ_le_self k (calc
        k + 1 = visitCount (fun i => X i ω) a j := hjc.symm
        _ ≤ visitCount (fun i => X i ω) a n :=
          visitCount_monotone _ _ (le_of_not_gt hn)
        _ = k := hc)
    exact ⟨j, ⟨hnj, Nat.le_of_lt_succ (visitTime_lt_of_lt_visitCount hm)⟩, hj⟩
  · rintro ⟨j, hj, hjx⟩
    calc
      k + 1 = visitCount (fun i => X i ω) a (n + 1) := by
        rw [visitCount_succ_of_eq (x := fun i => X i ω) hx, hc]
      _ ≤ visitCount (fun i => X i ω) a j := visitCount_monotone _ _ hj.1
      _ < visitCount (fun i => X i ω) a (j + 1) := by
        rw [visitCount_succ_of_eq (x := fun i => X i ω) hjx]
        exact Nat.lt_succ_self _
      _ ≤ visitCount (fun i => X i ω) a (m + 1) :=
        visitCount_monotone _ _ (Nat.succ_le_succ hj.2)

/-- For a process starting at `a`, visit one is the first positive return. -/
theorem successiveVisit_one_eq_hittingAfter_of_zero (h : X 0 ω = a) :
    successiveVisit X a 1 ω = hittingAfter X {a} 1 ω := by
  apply successiveVisit_succ_eq_hittingAfter (k := 0) (n := 0)
  exact successiveVisit_eq_coe_iff.mpr ⟨h, visitCount_zero _ _⟩

/-- The gap between two realized visits includes the return step omitted by the excursion word. -/
theorem successiveVisit_gap_eq_length_excursion_add_one
    (h : successiveVisit X a k ω = n) {m : ℕ}
    (hnext : successiveVisit X a (k + 1) ω = m) :
    m - n = (excursion (fun i => X i ω) a k).length + 1 := by
  obtain ⟨hx, hc⟩ := successiveVisit_eq_coe_iff.mp h
  obtain ⟨hy, hd⟩ := successiveVisit_eq_coe_iff.mp hnext
  have hn : visitTime (fun i => X i ω) a k = n :=
    WithTop.coe_inj.mp ((successiveVisit_eq_visitTime ⟨n, hx, hc⟩).symm.trans h)
  have hm : visitTime (fun i => X i ω) a (k + 1) = m :=
    WithTop.coe_inj.mp ((successiveVisit_eq_visitTime ⟨m, hy, hd⟩).symm.trans hnext)
  have hnm : n < m := by
    by_contra hle
    have := visitCount_monotone (fun i => X i ω) a (le_of_not_gt hle)
    omega
  rw [length_excursion, hn, hm]
  omega

variable [MeasurableSpace Ω] [MeasurableSpace α]

/-- Successive visits are stopping times for any filtration to which the process is adapted. -/
theorem _root_.MeasureTheory.Adapted.isStoppingTime_successiveVisit
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} (hX : Adapted ℱ X)
    (ha : MeasurableSet ({a} : Set α)) (k : ℕ) :
    IsStoppingTime ℱ (successiveVisit X a k) := by
  intro n
  have heq : {ω | successiveVisit X a k ω ≤ n} =
      {ω | k < visitCount (fun i => X i ω) a (n + 1)} :=
    Set.ext fun _ => successiveVisit_le_iff
  simp only [Nat.cast_withTop] at heq
  rw [heq]
  exact measurableSet_preimage
    (@measurable_visitCount_comp α _ Ω (ℱ n) (fun ω i => X i ω) a (n + 1) ha
      (fun i hi => hX.measurable_le (Nat.le_of_lt_succ hi)))
    (measurableSet_Ioi : MeasurableSet (Set.Ioi k))

/-- With measurable coordinates, each successive visit is measurable. -/
@[fun_prop]
theorem measurable_successiveVisit (hX : ∀ n, Measurable (X n))
    (ha : MeasurableSet ({a} : Set α)) (k : ℕ) : Measurable (successiveVisit X a k) := by
  have h : Adapted (Filtration.const ℕ ‹MeasurableSpace Ω› le_rfl) X := by
    intro n
    -- Measurability depends on the filtration value through its domain instance.
    exact (Filtration.const_apply n).symm ▸ hX n
  exact (h.isStoppingTime_successiveVisit ha k).measurable'

end TauCeti.Probability
