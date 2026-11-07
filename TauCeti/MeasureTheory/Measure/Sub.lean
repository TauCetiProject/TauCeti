/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Sub
public import TauCeti.MeasureTheory.Measure.Dirac

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

/-- If there is no mass at the location, erasure leaves the whole measure unchanged. -/
@[simp]
theorem sub_dirac_eq_self_of_apply_singleton_eq_zero (μ : Measure X) {x : X}
    (hx : μ {x} = 0) : μ - dirac x = μ := by
  obtain ⟨N, hxN, hN, hN0⟩ := exists_measurable_superset_of_null hx
  refine le_antisymm sub_le (le_iff.2 fun A hA ↦ ?_)
  calc
    μ A = μ (A \ N) := (measure_sdiff_null hN0).symm
    _ = (μ - dirac x) (A \ N) :=
      (sub_dirac_apply_of_notMem μ (hA.diff hN)
        (notMem_sdiff_of_mem (hxN (mem_singleton x)))).symm
    _ ≤ (μ - dirac x) A := measure_mono sdiff_subset

/-- Reinserting a removed occurrence recovers the measure when the occurrence was present. -/
theorem sub_dirac_add_dirac_of_one_le (μ : Measure X) {x : X} (hx : 1 ≤ μ {x}) :
    μ - dirac x + dirac x = μ :=
  sub_add_cancel_of_le ((dirac_le_iff_one_le_apply_singleton μ x).2 hx)

variable [MeasurableSingletonClass X]

/-- Removing one occurrence subtracts one, with truncation at zero, from its multiplicity. -/
@[simp]
theorem sub_dirac_apply_singleton (μ : Measure X) (x : X) :
    (μ - dirac x) {x} = μ {x} - 1 := by
  classical
  by_cases hx : 1 ≤ μ {x}
  · simpa using sub_apply (measurableSet_singleton x)
      ((dirac_le_iff_one_le_apply_singleton μ x).2 hx)
  · rw [tsub_eq_zero_of_le (le_of_not_ge hx)]
    apply sub_apply_eq_zero_of_restrict_le_restrict _ (measurableSet_singleton x)
    simp only [restrict_singleton, dirac_apply_of_mem (mem_singleton x), one_smul]
    calc
      μ {x} • dirac x ≤ (1 : ℝ≥0∞) • dirac x := by gcongr; exact le_of_not_ge hx
      _ = dirac x := by simp

/-- Erasure separates the unchanged part off the location and its remaining multiplicity. -/
theorem sub_dirac_eq_restrict_add_smul (μ : Measure X) (x : X) :
    μ - dirac x = μ.restrict {x}ᶜ + (μ {x} - 1) • dirac x := by
  classical
  simpa [restrict_sub_eq_restrict_sub_restrict, restrict_dirac, restrict_singleton] using
    (restrict_compl_add_restrict (μ := μ - dirac x) (measurableSet_singleton x)).symm

end MeasureTheory.Measure
