/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Derivatives of complex logarithm products

Pointwise product rule for `u ↦ w u * Complex.log (u - z₀)` on the translated slit plane
`z - z₀ ∈ Complex.slitPlane` (`HasDerivAt.mul_log_sub`).
-/

public section

namespace TauCeti

/-- Pointwise first derivative of `u ↦ w u * Complex.log (u - z₀)` at a point `z` with
`z - z₀ ∈ Complex.slitPlane`. -/
theorem _root_.HasDerivAt.mul_log_sub {w : ℂ → ℂ} {w' z₀ z : ℂ}
    (hw : HasDerivAt w w' z) (hzs : z - z₀ ∈ Complex.slitPlane) :
    HasDerivAt (fun u ↦ w u * Complex.log (u - z₀))
      (w' * Complex.log (z - z₀) + (z - z₀)⁻¹ * w z) z :=
  (hw.mul (((hasDerivAt_id z).sub_const z₀).clog hzs)).congr_deriv
    (by dsimp only [id]; rw [one_div]; ring)

end TauCeti
