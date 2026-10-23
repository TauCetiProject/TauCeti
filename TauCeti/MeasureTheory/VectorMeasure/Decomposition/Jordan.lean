/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Jordan decomposition of a difference of measures, eventwise

The positive part of the Jordan decomposition of a signed measure `s` has total mass equal to
the largest value of `s` on a set, and its negative part the largest value of `-s`. For a
difference `μ - ν` of two finite measures these are the largest excess `μ A - ν A` and the
largest excess `ν A - μ A` over measurable events `A`. For two finite measures of the same total
mass the two parts have equal mass.

These masses compute Mathlib's total variation distance `etvDist μ ν` through measurable events;
see `TauCeti.MeasureTheory.Measure.TotalVariation`.

## Main declarations

* `MeasureTheory.SignedMeasure.toJordanDecomposition_posPart_univ_eq_iSup` and
  `MeasureTheory.SignedMeasure.toJordanDecomposition_negPart_univ_eq_iSup`: the masses of the
  positive and negative parts as suprema of `s` and `-s`;
* `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup` and
  `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub_negPart_univ_eq_iSup`: the
  same masses for `μ - ν`, as largest excesses over measurable events;
* `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ`:
  for finite measures of equal total mass the two parts have equal mass.
-/
public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

namespace SignedMeasure

/-- The positive part of the Jordan decomposition of `s` has total mass the supremum of `s`
over all sets (`s` vanishes on non-measurable sets, so they do not contribute). -/
theorem toJordanDecomposition_posPart_univ_eq_iSup (s : SignedMeasure α) :
    s.toJordanDecomposition.posPart univ = ⨆ A : Set α, ENNReal.ofReal (s A) := by
  set j := s.toJordanDecomposition with hj
  obtain ⟨S, hS, hpos, hneg⟩ := j.mutuallySingular
  refine le_antisymm ?_ (iSup_le fun A => ?_)
  · -- The positive part is carried by `Sᶜ`, where `s` agrees with it.
    have hSc : ENNReal.ofReal (s Sᶜ) = j.posPart univ := by
      rw [s.apply_eq_posPart_real_sub_negPart_real hS.compl, ← hj, measureReal_def j.negPart,
        hneg, ENNReal.toReal_zero, sub_zero, ofReal_measureReal, ← measure_add_measure_compl hS,
        hpos, zero_add]
    exact hSc ▸ le_iSup (fun A => ENNReal.ofReal (s A)) Sᶜ
  · by_cases hA : MeasurableSet A
    · calc
        ENNReal.ofReal (s A) ≤ ENNReal.ofReal (j.posPart.real A) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [s.apply_eq_posPart_real_sub_negPart_real hA]
          exact sub_le_self _ measureReal_nonneg
        _ = j.posPart A := ofReal_measureReal
        _ ≤ j.posPart univ := measure_mono (subset_univ A)
    · simp [s.not_measurable hA]

/-- The negative part of the Jordan decomposition of `s` has total mass the supremum of `-s`
over all sets. -/
theorem toJordanDecomposition_negPart_univ_eq_iSup (s : SignedMeasure α) :
    s.toJordanDecomposition.negPart univ = ⨆ A : Set α, ENNReal.ofReal (-s A) := by
  simpa [toJordanDecomposition_neg] using (-s).toJordanDecomposition_posPart_univ_eq_iSup

end SignedMeasure

namespace Measure

variable {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The positive part of the Jordan decomposition of `μ - ν` has total mass the largest excess
`μ A - ν A` over measurable events. -/
theorem toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.posPart univ =
      ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A := by
  rw [SignedMeasure.toJordanDecomposition_posPart_univ_eq_iSup]
  refine iSup_congr fun A => ?_
  by_cases hA : MeasurableSet A
  · rw [toSignedMeasure_sub_apply hA, ENNReal.ofReal_sub _ measureReal_nonneg, ofReal_measureReal,
      ofReal_measureReal, iSup_pos hA]
  · simp [hA, VectorMeasure.not_measurable _ hA]

/-- The negative part of the Jordan decomposition of `μ - ν` has total mass the largest excess
`ν A - μ A` over measurable events. -/
theorem toJordanDecomposition_toSignedMeasure_sub_negPart_univ_eq_iSup :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.negPart univ =
      ⨆ (A : Set α) (_ : MeasurableSet A), ν A - μ A := by
  rw [← neg_sub, SignedMeasure.toJordanDecomposition_neg, JordanDecomposition.neg_negPart,
    toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup]

/-- For finite measures of equal total mass, the positive and negative parts of the Jordan
decomposition of `μ - ν` have equal total mass. -/
theorem toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ
    (h : μ univ = ν univ) :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.posPart univ =
      (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.negPart univ := by
  set s := μ.toSignedMeasure - ν.toSignedMeasure
  have hs : s univ = 0 := by
    rw [toSignedMeasure_sub_apply MeasurableSet.univ, measureReal_def, measureReal_def, h,
      sub_self]
  rw [s.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ, sub_eq_zero,
    measureReal_def, measureReal_def] at hs
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hs

end Measure

end MeasureTheory
