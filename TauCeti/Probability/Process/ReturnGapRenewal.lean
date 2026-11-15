/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.SuccessiveVisits
public import TauCeti.Probability.Renewal.Count

/-!
# Visits as renewals of return gaps

For a path starting at a state that it visits infinitely often, the successive
return gaps are positive increments. Their renewal count at an integer time is
exactly the number of positive-time visits through that time. This identifies
occupation counts with renewal counts without counting the initial visit.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal

namespace TauCeti.Probability

variable {Ω α : Type*} {X : ℕ → Ω → α} {a : α} {ω : Ω}

/-- Return-gap renewals count visits in times `1, …, n`, not the visit at time zero.
Both endpoints are therefore consistent with the positive first-return convention. -/
@[simp]
theorem renewalCountNat_returnGap (hω : {n | X n ω = a}.Infinite) (h0 : X 0 ω = a)
    (n : ℕ) :
    renewalCountNat (fun k ω => (returnGap X a k ω : ℝ≥0)) n ω =
      visitCount (fun k => X (k + 1) ω) a n := by
  classical
  have harr (k : ℕ) :
      arrival (fun k ω => (returnGap X a k ω : ℝ≥0)) k ω =
        ((∑ i ∈ Finset.range k, returnGap X a i ω : ℕ) : ℝ≥0) := by
    simp [arrival_def]
  have hsum (k : ℕ) := successiveVisit_eq_sum_returnGap
    (exists_visitCount_of_infinite hω k) h0
  have hcount : visitCount (fun k => X k ω) a (n + 1) =
      visitCount (fun k => X (k + 1) ω) a n + 1 := by
    simpa [Nat.add_comm, visitCount_succ_of_eq (x := fun k => X k ω) h0,
      visitCount_zero] using
      visitCount_add (fun k => X k ω) a 1 n
  apply eq_of_forall_le_iff
  intro k
  rw [le_renewalCountNat_iff (tendsto_arrival_atTop_of_frequently_le one_pos
    (Frequently.of_forall fun k => by
      exact_mod_cast returnGap_pos (exists_visitCount_of_infinite hω (k + 1)))), harr]
  have hle : ((∑ i ∈ Finset.range k, returnGap X a i ω : ℕ) : WithTop ℕ) ≤ n ↔
      k ≤ visitCount (fun k => X (k + 1) ω) a n := by
    rw [← hsum, successiveVisit_le_iff, hcount]
    omega
  simpa only [Nat.cast_le, Nat.cast_withTop, WithTop.coe_le_coe] using hle

end TauCeti.Probability
