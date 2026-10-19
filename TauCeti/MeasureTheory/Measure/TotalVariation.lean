/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import TauCeti.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Total variation distance as a supremum over events

Mathlib's total variation distance `MeasureTheory.etvDist μ ν` between finite measures is the
variation of the signed measure `μ - ν` on the whole space. With this normalization the distance
between two probability measures lies in `[0, 2]`: it is the signed-measure norm `‖μ - ν‖`, twice
the distance `sup_A |μ A - ν A|` that some authors use instead.

This file expresses `etvDist` through measurable events. It is the sum of the largest excess
`μ A - ν A` and the largest excess `ν A - μ A`, so eventwise bounds

```text
μ A ≤ ν A + c,    ν A ≤ μ A + d    (A measurable)
```

give `etvDist μ ν ≤ c + d`. For finite measures of the same total mass the two excesses agree,
so `etvDist μ ν ≤ 2 * c` exactly when every measurable event satisfies `μ A ≤ ν A + c`. These
statements pin down the factor of two relating the two conventions, and turn eventwise
estimates into total-variation estimates.

## Main declarations

* `MeasureTheory.etvDist_eq_posPart_univ_add_negPart_univ`: `etvDist μ ν` is the total mass of
  the positive part of the Jordan decomposition of `μ - ν` plus that of its negative part;
* `MeasureTheory.etvDist_eq_iSup_sub_add_iSup_sub`: `etvDist μ ν` is the largest excess of `μ`
  over `ν` on an event plus the largest excess of `ν` over `μ`;
* `MeasureTheory.etvDist_eq_two_mul_iSup_sub`: for finite measures of equal total mass, it is
  twice the largest excess of `μ` over `ν`;
* `MeasureTheory.etvDist_le_of_forall_le_add`: eventwise bounds in both directions bound the
  total variation distance;
* `MeasureTheory.etvDist_le_two_mul_iff`: for finite measures of equal total mass,
  `etvDist μ ν ≤ 2 * c` if and only if every measurable event satisfies `μ A ≤ ν A + c`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The total variation distance between finite measures is the total mass of the positive part
of the Jordan decomposition of `μ - ν` plus the total mass of its negative part. -/
theorem etvDist_eq_posPart_univ_add_negPart_univ :
    etvDist μ ν = (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.posPart univ +
      (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.negPart univ := by
  rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist,
    ← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation, Measure.add_apply]

/-- The total variation distance between finite measures is the largest excess `μ A - ν A` over
measurable events plus the largest excess `ν A - μ A`. -/
theorem etvDist_eq_iSup_sub_add_iSup_sub :
    etvDist μ ν = (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) +
      ⨆ (A : Set α) (_ : MeasurableSet A), ν A - μ A := by
  rw [etvDist_eq_posPart_univ_add_negPart_univ,
    Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup,
    Measure.toJordanDecomposition_toSignedMeasure_sub_negPart_univ_eq_iSup]

/-- For finite measures of equal total mass (e.g. two probability measures), the total variation
distance is twice the largest excess `μ A - ν A` over measurable events. -/
theorem etvDist_eq_two_mul_iSup_sub (h : μ univ = ν univ) :
    etvDist μ ν = 2 * ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A := by
  rw [etvDist_eq_posPart_univ_add_negPart_univ,
    ← Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ h, ← two_mul,
    Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup]

/-- **Total variation from eventwise bounds.** If every measurable event has `μ`-mass at most its
`ν`-mass plus `c`, and `ν`-mass at most its `μ`-mass plus `d`, then `etvDist μ ν ≤ c + d`. -/
theorem etvDist_le_of_forall_le_add {c d : ℝ≥0∞}
    (h₁ : ∀ A, MeasurableSet A → μ A ≤ ν A + c) (h₂ : ∀ A, MeasurableSet A → ν A ≤ μ A + d) :
    etvDist μ ν ≤ c + d := by
  rw [etvDist_eq_iSup_sub_add_iSup_sub]
  gcongr
  · exact iSup₂_le fun A hA => tsub_le_iff_left.2 (h₁ A hA)
  · exact iSup₂_le fun A hA => tsub_le_iff_left.2 (h₂ A hA)

/-- **Total variation as an eventwise bound.** For finite measures of equal total mass (e.g. two
probability measures), `etvDist μ ν ≤ 2 * c` if and only if every measurable event has `μ`-mass
at most its `ν`-mass plus `c`. In other words, `etvDist μ ν` is twice the distance
`sup_A |μ A - ν A|`. -/
theorem etvDist_le_two_mul_iff (h : μ univ = ν univ) {c : ℝ≥0∞} :
    etvDist μ ν ≤ 2 * c ↔ ∀ A, MeasurableSet A → μ A ≤ ν A + c := by
  rw [etvDist_eq_two_mul_iSup_sub h, ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top]
  simp only [iSup_le_iff, tsub_le_iff_left]

end MeasureTheory
