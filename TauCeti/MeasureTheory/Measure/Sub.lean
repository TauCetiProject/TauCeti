/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Removing one occurrence from a measure

Subtracting a Dirac measure removes one unit of mass at its location, leaving the measure
unchanged elsewhere. The formulas here apply even if the location is absent or has infinite
mass. In particular, subtraction is not restriction to the complement of the location: a
multiple point retains all but one occurrence.

These identities provide the measure-level erasure operation used in recursive enumeration
of occurrences and in reduced Palm distributions. The operation is Mathlib's measure
subtraction, not a separate definition.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, 2018, Chapters 2 and 9.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- Removing one occurrence at `x` does not change the mass of a measurable set avoiding `x`. -/
theorem sub_dirac_apply_of_notMem (μ : Measure X) {x : X} {A : Set X}
    (hA : MeasurableSet A) (hx : x ∉ A) : (μ - dirac x) A = μ A := by
  classical
  have h := congrArg (fun ν : Measure X ↦ ν A)
    (restrict_sub_eq_restrict_sub_restrict (μ := μ) (ν := dirac x) hA)
  simpa [restrict_dirac' hA, hx] using h

variable [MeasurableSingletonClass X]

/-- Removing one occurrence subtracts one, with truncation at zero, from its multiplicity. -/
@[simp]
theorem sub_dirac_apply_singleton (μ : Measure X) (x : X) :
    (μ - dirac x) {x} = μ {x} - 1 := by
  classical
  by_cases hx : 1 ≤ μ {x}
  · have hle : dirac x ≤ μ := le_iff.2 fun A hA ↦ by
      by_cases hxA : x ∈ A
      · simpa [dirac_apply' _ hA, hxA] using
          hx.trans (measure_mono (singleton_subset_iff.2 hxA))
      · simp [dirac_apply' _ hA, hxA]
    simpa using sub_apply (measurableSet_singleton x) hle
  · rw [tsub_eq_zero_of_le (le_of_not_ge hx)]
    apply sub_apply_eq_zero_of_restrict_le_restrict _ (measurableSet_singleton x)
    simp only [restrict_singleton, dirac_apply_of_mem (mem_singleton x), one_smul]
    calc
      μ {x} • dirac x ≤ (1 : ℝ≥0∞) • dirac x := by gcongr; exact le_of_not_ge hx
      _ = dirac x := by simp

/-- Erasure separates the unchanged part off the location and its remaining multiplicity. -/
theorem sub_dirac_eq_restrict_add_smul (μ : Measure X) (x : X) :
    μ - dirac x = μ.restrict {x}ᶜ + (μ {x} - 1) • dirac x := by
  ext A hA
  rw [← measure_inter_add_sdiff A (measurableSet_singleton x), add_apply,
    restrict_apply hA, smul_apply, smul_eq_mul]
  have havoid : x ∉ A \ {x} := by simp
  rw [sub_dirac_apply_of_notMem μ (hA.diff (measurableSet_singleton x)) havoid]
  by_cases hx : x ∈ A
  · rw [inter_eq_right.2 (singleton_subset_iff.2 hx), sub_dirac_apply_singleton,
      dirac_apply_of_mem hx, mul_one]
    simp only [sdiff_eq]
    ac_rfl
  · have hdisj : A ∩ {x} = ∅ := by grind
    simp [hdisj, dirac_apply' _ hA, hx, sdiff_eq]

/-- If there is no mass at the location, erasure leaves the whole measure unchanged. -/
@[simp]
theorem sub_dirac_eq_self_of_apply_singleton_eq_zero (μ : Measure X) {x : X}
    (hx : μ {x} = 0) : μ - dirac x = μ := by
  rw [sub_dirac_eq_restrict_add_smul, hx]
  simpa using restrict_eq_self_of_ae_mem (μ := μ) (s := {x}ᶜ)
    (ae_iff.2 (by simpa using hx))

end MeasureTheory.Measure
