/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Derivatives of the complex logarithm

The derivative of a logarithm with a scaled argument is the reciprocal of the point on its
slit domain (`Complex.hasDerivAt_log_div_const`), and the pointwise product rule for
`u ↦ w u * Complex.log (u - z₀)` on the translated slit plane `z - z₀ ∈ Complex.slitPlane`
(`HasDerivAt.mul_log_sub`).
-/

public section

namespace Complex

/-- The derivative of the logarithm of `z / c` is `z⁻¹` on the resulting slit domain. -/
theorem hasDerivAt_log_div_const (z : ℂ) {c : ℂ} (hz : z / c ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ log (w / c)) z⁻¹ z := by
  obtain ⟨hz0, hc⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hz)
  have h : HasDerivAt (fun w : ℂ ↦ w / c) (1 / c) z :=
    (hasDerivAt_id z).div_const c
  convert h.clog hz using 1
  field_simp [hc, hz0]

end Complex

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
