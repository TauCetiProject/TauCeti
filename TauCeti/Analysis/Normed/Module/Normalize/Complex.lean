/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Normed.Module.Normalize.Basic

/-!
# Radial normalization of complex numbers

Complex normalization is division by the norm and preserves multiplication, including at zero.
Away from zero, the underlying complex value of a sphere direction is this normalized value.
-/

public section

namespace Complex

/-- Normalizing a complex number divides it by its norm. -/
theorem normalize_eq_div_norm (z : ℂ) : NormedSpace.normalize z = z / ‖z‖ := by
  rw [NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

/-- Complex normalization preserves multiplication, even when a factor is zero. -/
theorem normalize_mul (z w : ℂ) :
    NormedSpace.normalize (z * w) = NormedSpace.normalize z * NormedSpace.normalize w := by
  simp only [normalize_eq_div_norm, norm_mul, ofReal_mul, div_mul_div_comm]

end Complex

namespace TauCeti

/-- Away from zero, the complex coordinate of the sphere direction is `z / ‖z‖`. -/
@[simp] theorem coe_sphereDirection_eq_div_norm (e : Metric.sphere (0 : ℂ) 1) {z : ℂ} (hz : z ≠ 0) :
    (sphereDirection e z : ℂ) = z / ‖z‖ :=
  (coe_sphereDirection_of_ne_zero e hz).trans z.normalize_eq_div_norm

end TauCeti
