/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.ConstantSpeed

/-!
# Null traces of absolutely continuous curves

An absolutely continuous curve in a finite-dimensional real normed space of dimension greater
than one has an additive-Haar-null trace.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {γ : ℝ → E} {a b : ℝ}

/-- The trace of an absolutely continuous curve is additive-Haar-null in ambient dimension
greater than one. -/
theorem addHaar_image_uIcc_eq_zero (hγ : AbsolutelyContinuousOnInterval γ a b)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hd : 1 < Module.finrank ℝ E) :
    μ (γ '' uIcc a b) = 0 :=
  hγ.boundedVariationOn.locallyBoundedVariationOn.addHaar_image_eq_zero μ hd

end AbsolutelyContinuousOnInterval
