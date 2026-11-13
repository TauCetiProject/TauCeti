/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Tactic.Module

/-!
# Curve integrals along a fixed affine line

Straight segments on one affine line are exactly oriented interval integrals of the same
one-dimensional coefficient. This permits cancellation even when the line parameters reverse
direction or coincide.
-/

public section

open MeasureTheory

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [LinearMap.CompatibleSMul E F ℝ 𝕜]

/-- The integral along a segment on a fixed affine line is the oriented interval integral
in its real line coordinate. No ordering of the two parameters is required. The form may be
linear over any `RCLike` field whose action is compatible with the real one. -/
theorem curveIntegral_segment_line (ω : E → E →L[𝕜] F) (c v : E) (a b : ℝ) :
    curveIntegral ω (Path.segment (c + a • v) (c + b • v)) =
      ∫ t in a..b, ω (c + t • v) v := by
  have hline (t : ℝ) : AffineMap.lineMap (c + a • v) (c + b • v) t =
      c + ((b - a) * t + a) • v := by
    rw [AffineMap.lineMap_apply_module]
    module
  have hdiff : (c + b • v) - (c + a • v) = (b - a) • v := by module
  rw [curveIntegral_segment]
  simp only [hline, hdiff, ContinuousLinearMap.map_smul_of_tower]
  rw [intervalIntegral.integral_smul]
  simpa using intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (fun t : ℝ ↦ ω (c + t • v) v) (b - a) a

end TauCeti
