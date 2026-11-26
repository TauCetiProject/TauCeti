/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Geometry.Euclidean.Volume.Polar
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Ball

/-!
# The divergence theorem on spherical shells

Let `E` be a finite-dimensional real inner product space of dimension `n`, and let `V : E → E` be
a vector field of class `C¹` near the closed shell `r₁ ≤ ‖x - c‖ ≤ r₂`, `0 < r₁ ≤ r₂`. This file
proves the **divergence theorem** on the open shell `ball c r₂ \ closedBall c r₁`:

`∫_{r₁ < ‖x - c‖ < r₂} div V = ∫_{‖x - c‖ = r₂} ⟪V, ν⟫ dS - ∫_{‖x - c‖ = r₁} ⟪V, ν⟫ dS`,

where `div V x = tr (DV x)`, `ν x = (x - c) / ‖x - c‖` is the outward radial unit normal of the
spheres, and `dS` is the `(n - 1)`-dimensional Hausdorff measure `μHE[n - 1]`. Both boundary
spheres are oriented by the radial normal, so the inner sphere enters with a minus sign. The
spheres are boundaries of the shells exhausting an exterior region, which is how flux
integrals at infinity are compared: the difference of the fluxes of `V` through two large spheres
is the integral of `div V` over the shell between them.

## The argument

This is the divergence theorem on a shell with Mathlib's polar-coordinate surface measure
(`TauCeti.setIntegral_ball_sdiff_closedBall_trace_fderiv`), whose flux through the sphere of
radius `s` is `s ^ (n - 1) ∫_{θ ∈ S} ⟪V (c + s θ), θ⟫ dvolume.toSphere`. On a sphere of positive
radius, Hausdorff measure is the transported surface measure
(`TauCeti.setIntegral_sphere_eq_smul_integral_toSphere`), and `⟪V x, ν x⟫` at `x = c + s θ` is
`⟪V (c + s θ), θ⟫`, so the two fluxes agree.

## Main results

* `TauCeti.integral_divergence_ball_sdiff_closedBall`: **the divergence theorem on a spherical
  shell**.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.2 (the Gauss–Green theorem)
  and Appendix C.3 (polar coordinates).
-/

public section

open MeasureTheory Measure Metric Set Module
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {c : E} {r₁ r₂ : ℝ}

/-- The flux of `V` through `sphere c s`, `s > 0`, against Hausdorff measure is its flux in
Mathlib's polar-coordinate surface measure on the unit sphere. -/
private lemma setIntegral_sphere_inner_div_norm {V : E → E} {s : ℝ} (hs : 0 < s) :
    ∫ x in sphere c s, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1] =
      s ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (c + s • (θ : E)), θ⟫_ℝ
        ∂(volume : Measure E).toSphere := by
  rw [setIntegral_sphere_eq_smul_integral_toSphere c hs, smul_eq_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, norm_eq_of_mem_sphere θ, mul_one,
    Real.norm_of_nonneg hs.le]
  field_simp

/-- **The divergence theorem on a spherical shell.** Let `V : E → E` be a vector field of class
`C¹` near the closed shell `r₁ ≤ ‖x - c‖ ≤ r₂`, where `0 < r₁ ≤ r₂`. Then the integral of its
divergence `tr (DV)` over the open shell `ball c r₂ \ closedBall c r₁` is the flux of `V` through
the outer sphere minus its flux through the inner sphere, both for the radial unit normal
`(x - c) / ‖x - c‖` and `(n - 1)`-dimensional Hausdorff measure. -/
theorem integral_divergence_ball_sdiff_closedBall {V : E → E} (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂)
    (hV : ∀ x ∈ closedBall c r₂ \ ball c r₁, ContDiffAt ℝ 1 V x) :
    ∫ x in ball c r₂ \ closedBall c r₁, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) =
      (∫ x in sphere c r₂, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1]) -
        ∫ x in sphere c r₁, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1] := by
  rw [setIntegral_ball_sdiff_closedBall_trace_fderiv c hr₁.le hr hV,
    setIntegral_sphere_inner_div_norm (hr₁.trans_le hr), setIntegral_sphere_inner_div_norm hr₁]

end TauCeti
