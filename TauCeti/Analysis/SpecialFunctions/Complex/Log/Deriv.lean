/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Derivatives of the complex logarithm

The derivative of a logarithm with a scaled argument is the reciprocal of the point on its
slit domain. At a point of the slit plane, the first two derivatives of `u * log` are
`u' log + u / z` and `u'' log + 2 u' / z - u / z²` (`Complex.deriv_mul_log`,
`Complex.deriv_deriv_mul_log`).
-/

public section

open Filter Topology

namespace Complex

/-- The derivative of the logarithm of `z / c` is `z⁻¹` on the resulting slit domain. -/
theorem hasDerivAt_log_div_const (z : ℂ) {c : ℂ} (hz : z / c ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ log (w / c)) z⁻¹ z := by
  obtain ⟨hz0, hc⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hz)
  have h : HasDerivAt (fun w : ℂ ↦ w / c) (1 / c) z :=
    (hasDerivAt_id z).div_const c
  convert h.clog hz using 1
  field_simp [hc, hz0]

/-- At a point `z` of the slit plane at which `u` is differentiable, the derivative of `u * log`
is `u' log + u / z`. -/
theorem deriv_mul_log {u : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℂ u z) (hz : z ∈ slitPlane) :
    deriv (fun y ↦ u y * log y) z = deriv u z * log z + u z * z⁻¹ :=
  (hu.hasDerivAt.mul (hasDerivAt_log hz)).deriv

/-- At a point `z` of the slit plane near which `u` is differentiable and at which `u'` is
differentiable, the second derivative of `u * log` is `u'' log + 2 u' / z - u / z²`. -/
theorem deriv_deriv_mul_log {u : ℂ → ℂ} {z : ℂ} (hu : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ u y)
    (hu' : DifferentiableAt ℂ (deriv u) z) (hz : z ∈ slitPlane) :
    deriv (deriv fun y ↦ u y * log y) z =
      deriv (deriv u) z * log z + 2 * deriv u z * z⁻¹ - u z * (z ^ 2)⁻¹ := by
  have hev : deriv (fun y ↦ u y * log y) =ᶠ[𝓝 z] fun y ↦ deriv u y * log y + u y * y⁻¹ :=
    (hu.and (isOpen_slitPlane.mem_nhds hz)).mono fun y hy ↦ deriv_mul_log hy.1 hy.2
  have hd := (hu'.hasDerivAt.fun_mul (hasDerivAt_log hz)).fun_add
    (hu.self_of_nhds.hasDerivAt.fun_mul (hasDerivAt_inv (slitPlane_ne_zero hz)))
  rw [hev.deriv_eq, hd.deriv]
  ring

end Complex
