/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

/-!
# The zero divisor of a meromorphically continued L-function record

For a record `d` satisfying `HasMeromorphicContinuation`, the divisor of the completed function
`Λ = d.completed` on any domain `U` is `-d.polarOrder` at the recorded poles in `U` and is
nonnegative everywhere else. Its negative part is therefore exactly the polar divisor.

The entire completion `d.entireCompletion` clears these poles without creating zeros, so it has
the same zero count as `Λ` on every region. Its signed count equals its zero count, and on a
bounded region it exceeds the signed count of `Λ` by the number of poles in the region. In
particular the two signed counts agree on regions avoiding the poles. These adapters let
counting arguments run on whichever of `Λ` and its entire completion is more convenient.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12 and §15.
-/

public section

open Set

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData} (h : d.HasMeromorphicContinuation) {U R : Set ℂ} {s : ℂ}

include h

/-- At a recorded pole in the domain, the divisor of the completed function is minus the
recorded pole order. -/
theorem HasMeromorphicContinuation.divisor_completed_of_polarOrder_ne_zero (hs : s ∈ U)
    (hp : d.polarOrder s ≠ 0) :
    MeromorphicOn.divisor d.completed U s = -(d.polarOrder s : ℤ) := by
  rw [h.meromorphic.meromorphicOn.divisor_apply hs, h.meromorphicOrderAt_eq s hp,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]

/-- Away from the recorded poles, the divisor of the completed function is nonnegative. -/
theorem HasMeromorphicContinuation.divisor_completed_nonneg (hp : d.polarOrder s = 0) :
    0 ≤ MeromorphicOn.divisor d.completed U s := by
  by_cases hs : s ∈ U
  · rw [h.meromorphic.meromorphicOn.divisor_apply hs]
    exact WithTop.untop₀_nonneg.mpr (h.analyticAt s hp).meromorphicOrderAt_nonneg
  · simp [hs]

/-- The divisor of the completed function is negative exactly at the recorded poles in the
domain. -/
theorem HasMeromorphicContinuation.divisor_completed_neg_iff :
    MeromorphicOn.divisor d.completed U s < 0 ↔ s ∈ U ∧ d.polarOrder s ≠ 0 := by
  constructor
  · intro hneg
    refine ⟨by_contra fun hs ↦ by simp [hs] at hneg, fun hp ↦ ?_⟩
    exact (h.divisor_completed_nonneg hp).not_gt hneg
  · rintro ⟨hs, hp⟩
    rw [h.divisor_completed_of_polarOrder_ne_zero hs hp]
    exact neg_neg_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hp)

/-- The negative part of the divisor of the completed function on `U` is the polar divisor on
`U`. -/
theorem HasMeromorphicContinuation.min_divisor_completed_zero (hs : s ∈ U) :
    min (MeromorphicOn.divisor d.completed U s) 0 = -(d.polarOrder s : ℤ) := by
  by_cases hp : d.polarOrder s = 0
  · simpa [hp] using h.divisor_completed_nonneg (U := U) hp
  · rw [h.divisor_completed_of_polarOrder_ne_zero hs hp]
    simp

/-- The divisor of the entire completion is nonnegative on every domain. -/
theorem HasMeromorphicContinuation.divisor_entireCompletion_nonneg (U : Set ℂ) (s : ℂ) :
    0 ≤ MeromorphicOn.divisor d.entireCompletion U s :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ ↦ h.analyticAt_entireCompletion z) s

/-- Clearing the poles does not change any zero multiplicity. -/
@[simp]
theorem HasMeromorphicContinuation.toNat_divisor_entireCompletion (s : ℂ) :
    (MeromorphicOn.divisor d.entireCompletion univ s).toNat =
      (MeromorphicOn.divisor d.completed univ s).toNat := by
  rw [h.divisor_entireCompletion]
  by_cases hp : d.polarOrder s = 0
  · simp [hp]
  · rw [h.divisor_completed_of_polarOrder_ne_zero (mem_univ s) hp]
    simp

/-- The entire completion has the same zero count as the completed function on every region. -/
@[simp]
theorem HasMeromorphicContinuation.zeroCount_entireCompletion (R : Set ℂ) :
    zeroCount d.entireCompletion univ R = zeroCount d.completed univ R := by
  simp_rw [zeroCount_def, h.toNat_divisor_entireCompletion]

/-- The signed count of the entire completion is its zero count. -/
theorem HasMeromorphicContinuation.divisorCount_entireCompletion_eq_zeroCount (R : Set ℂ) :
    divisorCount d.entireCompletion univ R = (zeroCount d.entireCompletion univ R : ℤ) :=
  divisorCount_eq_zeroCount fun z _ ↦ h.divisor_entireCompletion_nonneg univ z

/-- On a bounded region, the signed count of the entire completion is the signed count of the
completed function plus the number of recorded poles in the region. -/
theorem HasMeromorphicContinuation.divisorCount_entireCompletion
    (hR : Bornology.IsBounded R) :
    divisorCount d.entireCompletion univ R =
      divisorCount d.completed univ R + ∑ᶠ s ∈ R, (d.polarOrder s : ℤ) := by
  have hpoles : (R ∩ Function.support fun s ↦ (d.polarOrder s : ℤ)).Finite :=
    d.polarOrder.support.finite_toSet.subset fun s hs ↦ by simpa using hs.2
  simp_rw [divisorCount_def, h.divisor_entireCompletion]
  exact finsum_mem_add_distrib'
    (MeromorphicOn.divisor_finite_inter_support hR (subset_univ _)) hpoles

/-- On a region avoiding the recorded poles, the entire completion and the completed function
have the same signed count. No boundedness is needed. -/
theorem HasMeromorphicContinuation.divisorCount_entireCompletion_of_polarOrder_eq_zero
    (hR : ∀ s ∈ R, d.polarOrder s = 0) :
    divisorCount d.entireCompletion univ R = divisorCount d.completed univ R := by
  simp_rw [divisorCount_def]
  exact finsum_mem_congr rfl fun s hs ↦ by simp [h.divisor_entireCompletion, hR s hs]

/-- On a bounded region, the zero count of the completed function is its signed count plus the
number of recorded poles in the region. -/
theorem HasMeromorphicContinuation.zeroCount_completed_eq_divisorCount_add
    (hR : Bornology.IsBounded R) :
    (zeroCount d.completed univ R : ℤ) =
      divisorCount d.completed univ R + ∑ᶠ s ∈ R, (d.polarOrder s : ℤ) := by
  rw [← h.zeroCount_entireCompletion, ← h.divisorCount_entireCompletion_eq_zeroCount,
    h.divisorCount_entireCompletion hR]

end TauCeti.LFunctions.AnalyticLFunctionData
