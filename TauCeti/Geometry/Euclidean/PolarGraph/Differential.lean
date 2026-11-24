/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.SpecialFunctions.Complex.PolarCoord
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# The differential and metric of the polar projection

In the global coordinates of the polar cover, the pullback of the real Euclidean inner product
on the complex plane is `dr² + r² dθ²`. Each integral deck translation preserves this metric.
The Cartesian parametrization is a smooth local diffeomorphism at every nonzero radius
(`TauCeti.isLocalDiffeomorphAt_polarCoord_symm`), since its differential
`polarCoordSymmDeriv` is injective.
-/

public noncomputable section

namespace TauCeti.PolarGraph

open scoped RealInnerProductSpace

/-- Mathlib's Cartesian parametrization agrees with the polar covering map on positive radii. -/
theorem polarCoord_symm_eq_projection (p : PolarPoint) :
    Complex.polarCoord.symm p.val = projection p := by
  apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin, radius_def, angle_def]

/-- Pullback of the Euclidean metric in radius and angle coordinates, at any real radius. -/
theorem inner_polarCoordSymmDeriv (x v w : ℝ × ℝ) :
    ⟪polarCoordSymmDeriv x v, polarCoordSymmDeriv x w⟫ =
      v.1 * w.1 + x.1 ^ 2 * v.2 * w.2 := by
  simp only [polarCoordSymmDeriv_apply, Complex.inner, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  linear_combination
    (v.1 * w.1 + x.1 ^ 2 * v.2 * w.2) * Real.sin_sq_add_cos_sq x.2

/-- Every real angular translation preserves the pullback inner product at any real radius. -/
theorem inner_polarCoordSymmDeriv_add_angle (x v w : ℝ × ℝ) (t : ℝ) :
    ⟪polarCoordSymmDeriv (x + (0, t)) v, polarCoordSymmDeriv (x + (0, t)) w⟫ =
      ⟪polarCoordSymmDeriv x v, polarCoordSymmDeriv x w⟫ := by
  simp only [inner_polarCoordSymmDeriv]
  simp

/-- All deck translations preserve the pullback inner product. -/
theorem inner_polarCoordSymmDeriv_deckShift (k : ℤ) (p : PolarPoint) (v w : ℝ × ℝ) :
    ⟪polarCoordSymmDeriv (deckShift k p).val v, polarCoordSymmDeriv (deckShift k p).val w⟫ =
      ⟪polarCoordSymmDeriv p.val v, polarCoordSymmDeriv p.val w⟫ := by
  simpa only [deckShift_val] using
    inner_polarCoordSymmDeriv_add_angle p.val v w ((k : ℝ) * (2 * Real.pi))

end TauCeti.PolarGraph
