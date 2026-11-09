/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Absolute continuity of `circleMap`

The complex circle parametrization `circleMap c R` is Lipschitz (`lipschitzWith_circleMap`), hence
absolutely continuous on every parameter interval.
-/

public section

namespace TauCeti

/-- The circle parametrization `circleMap c R` is absolutely continuous on every real parameter
interval, for arbitrary center `c` and signed radius `R`. -/
theorem absolutelyContinuousOnInterval_circleMap (c : ℂ) (R a b : ℝ) :
    AbsolutelyContinuousOnInterval (circleMap c R) a b :=
  (lipschitzWith_circleMap c R).lipschitzOnWith.absolutelyContinuousOnInterval

end TauCeti
