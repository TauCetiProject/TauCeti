/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.ConstantSpeed

/-!
# Area zero for traces of absolutely continuous planar curves

Absolute continuity implies bounded variation. Mathlib's natural parameterization expresses the
trace as a Lipschitz image of a subset of the real line, so the trace has Hausdorff dimension at
most one and has zero planar area. Removing or adding this trace therefore preserves all area
integrals, without extra integrability assumptions.

In particular, these results justify ignoring the trace in winding-weighted area integrals.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace AbsolutelyContinuousOnInterval

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- The compact trace of an absolutely continuous planar curve has zero area. -/
theorem volume_image_uIcc_eq_zero (hγ : AbsolutelyContinuousOnInterval γ a b) :
    volume (γ '' uIcc a b) = 0 := by
  have hμ : (volume : Measure ℂ) ≪ μH[(Module.finrank ℝ ℂ : ℝ)] :=
    Measure.absolutelyContinuous_isAddHaarMeasure volume _
  apply measure_zero_of_dimH_lt (d := (Module.finrank ℝ ℂ : NNReal)) hμ
  exact (hγ.boundedVariationOn.locallyBoundedVariationOn.dimH_image_le_one).trans_lt
    (by norm_num [Complex.finrank_real_complex])

/-- Deleting an absolutely continuous curve's trace does not change an area integral. -/
theorem integral_sdiff_image_uIcc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hγ : AbsolutelyContinuousOnInterval γ a b) (f : ℂ → E) (s : Set ℂ) :
    ∫ z in s \ (γ '' uIcc a b), f z = ∫ z in s, f z :=
  setIntegral_congr_set (sdiff_null_ae_eq_self hγ.volume_image_uIcc_eq_zero)

/-- Adding an absolutely continuous curve's trace does not change an area integral. -/
theorem integral_union_image_uIcc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hγ : AbsolutelyContinuousOnInterval γ a b) (f : ℂ → E) (s : Set ℂ) :
    ∫ z in s ∪ (γ '' uIcc a b), f z = ∫ z in s, f z := by
  apply setIntegral_congr_set
  rw [union_comm]
  exact union_ae_eq_right.mpr (measure_mono_null sdiff_subset hγ.volume_image_uIcc_eq_zero)

end AbsolutelyContinuousOnInterval
