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
the largest value of `s` on a set, and its negative part the largest value of `-s`; the two
masses agree exactly when `s` vanishes on the whole space. For a difference `μ - ν` of two
finite measures these are the largest excess `μ A - ν A` and the largest excess `ν A - μ A` over
measurable events `A`, and they agree exactly when `μ` and `ν` have the same total mass.

These masses compute Mathlib's total variation distance `etvDist μ ν` through measurable events;
see `TauCeti.MeasureTheory.Measure.TotalVariation.Basic`.

## Main declarations

* `MeasureTheory.SignedMeasure.toJordanDecomposition_posPart_univ_eq_iSup` and
  `MeasureTheory.SignedMeasure.toJordanDecomposition_negPart_univ_eq_iSup`: the masses of the
  positive and negative parts as suprema of `s` and `-s`;
* `MeasureTheory.SignedMeasure.toJordanDecomposition_posPart_univ_eq_negPart_univ_iff`: the two
  parts have equal mass if and only if `s univ = 0`;
* `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup` and
  `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub_negPart_univ_eq_iSup`: the
  same masses for `μ - ν`, as largest excesses over measurable events;
* `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ_iff`
  states that, for finite measures, the two parts of `μ - ν` have equal mass if and only if
  `μ univ = ν univ`.
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
  set j := s.toJordanDecomposition
  refine le_antisymm ?_ (iSup_le fun A => ?_)
  · -- The positive part is `s` restricted to the positive set `i` of a Hahn decomposition.
    obtain ⟨i, hi, hi₀, -, hpos, -⟩ := s.toJordanDecomposition_spec
    calc
      j.posPart univ = ENNReal.ofReal (s i) := by
        rw [hpos, ← ofReal_measureReal, toMeasureOfZeroLE_real_apply _ hi₀ hi .univ, inter_univ]
      _ ≤ ⨆ A : Set α, ENNReal.ofReal (s A) := le_iSup (fun A => ENNReal.ofReal (s A)) i
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

/-- The positive and negative parts of the Jordan decomposition of `s` have equal total mass if
and only if `s` vanishes on the whole space. -/
@[simp]
theorem toJordanDecomposition_posPart_univ_eq_negPart_univ_iff (s : SignedMeasure α) :
    s.toJordanDecomposition.posPart univ = s.toJordanDecomposition.negPart univ ↔
      s univ = 0 := by
  rw [s.apply_eq_posPart_real_sub_negPart_real .univ, sub_eq_zero, measureReal_eq_measureReal_iff]

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

/-- The positive and negative parts of the Jordan decomposition of `μ - ν` have equal total mass
if and only if the finite measures `μ` and `ν` have equal total mass. -/
theorem toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ_iff :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.posPart univ =
        (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition.negPart univ ↔
      μ univ = ν univ := by
  rw [SignedMeasure.toJordanDecomposition_posPart_univ_eq_negPart_univ_iff,
    toSignedMeasure_sub_apply .univ, sub_eq_zero, measureReal_eq_measureReal_iff]

end Measure

end MeasureTheory
