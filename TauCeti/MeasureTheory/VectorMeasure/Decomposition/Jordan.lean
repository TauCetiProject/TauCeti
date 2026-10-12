/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Total variation of a difference of measures, eventwise

The positive part of the Jordan decomposition of a signed measure `s` has total mass equal to
the largest value of `s` on a set, and its negative part the largest value of `-s`. For a
difference `μ - ν` of two finite measures these are the largest excess `μ A - ν A` and the
largest excess `ν A - μ A` over measurable events `A`. Consequently, eventwise bounds

```text
μ A ≤ ν A + c,    ν A ≤ μ A + d    (A measurable)
```

bound Mathlib's total variation measure of `μ.toSignedMeasure - ν.toSignedMeasure` on the whole
space by `c + d`. For two finite measures of the same total mass the two parts have equal mass,
so the total variation on the whole space is at most `2 * c` exactly when every event satisfies
`μ A ≤ ν A + c`.

This pins down the normalization relating two common conventions for probability measures:
`SignedMeasure.totalVariation` on `Set.univ` is the signed-measure norm `‖μ - ν‖`, which is twice
the total-variation distance `sup_A |μ A - ν A|`.

## Main declarations

* `MeasureTheory.SignedMeasure.toJordanDecomposition_posPart_univ_eq_iSup` and
  `MeasureTheory.SignedMeasure.toJordanDecomposition_negPart_univ_eq_iSup`: the masses of the
  positive and negative parts as suprema of `s` and `-s`;
* `MeasureTheory.Measure.totalVariation_toSignedMeasure_sub_univ_le`: eventwise bounds in both
  directions bound the total variation of a difference of finite measures;
* `MeasureTheory.Measure.totalVariation_toSignedMeasure_sub_univ_le_two_mul_iff`: for finite
  measures of equal total mass, the total variation is at most `2 * c` if and only if every
  measurable event satisfies `μ A ≤ ν A + c`.
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

/-- **Total variation from eventwise bounds.** If every measurable event has `μ`-mass at most its
`ν`-mass plus `c`, and `ν`-mass at most its `μ`-mass plus `d`, then the total variation of
`μ - ν` on the whole space is at most `c + d`. -/
theorem totalVariation_toSignedMeasure_sub_univ_le {c d : ℝ≥0∞}
    (h₁ : ∀ A, MeasurableSet A → μ A ≤ ν A + c) (h₂ : ∀ A, MeasurableSet A → ν A ≤ μ A + d) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤ c + d := by
  rw [SignedMeasure.totalVariation, add_apply,
    toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup,
    toJordanDecomposition_toSignedMeasure_sub_negPart_univ_eq_iSup]
  gcongr
  · exact iSup₂_le fun A hA => tsub_le_iff_left.2 (h₁ A hA)
  · exact iSup₂_le fun A hA => tsub_le_iff_left.2 (h₂ A hA)

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

/-- **Total variation as an eventwise bound.** For finite measures of equal total mass (e.g. two
probability measures), the total variation of `μ - ν` on the whole space is at most `2 * c` if
and only if every measurable event has `μ`-mass at most its `ν`-mass plus `c`. In other words,
`(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ` is twice the total-variation
distance `sup_A |μ A - ν A|`. -/
theorem totalVariation_toSignedMeasure_sub_univ_le_two_mul_iff (h : μ univ = ν univ)
    {c : ℝ≥0∞} :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤ 2 * c ↔
      ∀ A, MeasurableSet A → μ A ≤ ν A + c := by
  rw [SignedMeasure.totalVariation, add_apply,
    ← toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ h, ← two_mul,
    ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top,
    toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup]
  simp only [iSup_le_iff, tsub_le_iff_left]

end Measure

end MeasureTheory
