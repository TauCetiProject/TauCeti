/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Tangent coordinate changes of the Riemann sphere

The Riemann sphere `OnePoint ℂ`, regarded as a real surface through its holomorphic charts, has
two charts whose transition map is `w ↦ w⁻¹`. This file computes the resulting tangent coordinate
change from the chart at `∞` to the affine chart: at a nonzero finite point `z` it is
multiplication by `-z²` (`OnePoint.tangentCoordChange_infty_coe`).
-/

public section

open scoped Manifold TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

/-- On the Riemann sphere regarded as a real surface, the tangent coordinate change from the chart
at `∞` to the chart at a nonzero finite point `z` is multiplication by `-z²`, the derivative of
the chart transition `w ↦ w⁻¹` at `w = z⁻¹`. -/
theorem tangentCoordChange_infty_coe {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    tangentCoordChange 𝓘(ℝ, ℂ) (∞ : OnePoint ℂ) (z : OnePoint ℂ) (z : OnePoint ℂ) v =
      -z ^ 2 * v := by
  have h : HasFDerivAt (fun w : ℂ ↦ w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z⁻¹ ^ 2)⁻¹)).restrictScalars ℝ) z⁻¹ :=
    (hasDerivAt_inv (inv_ne_zero hz)).hasFDerivAt.restrictScalars ℝ
  simp [affineChart_comp_invChart_symm, h.fderiv, mul_comm]

end OnePoint
