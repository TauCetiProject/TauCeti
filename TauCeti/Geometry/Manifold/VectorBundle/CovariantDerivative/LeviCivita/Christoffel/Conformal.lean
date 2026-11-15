/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Christoffel symbols of a conformally Euclidean metric

For a metric `g y = f y • innerSL ℝ`, the Christoffel map is expressed using the differential
and gradient of `f`. This gives a reusable coordinate formula for conformally flat models,
including the round sphere in stereographic coordinates. The factor need only be nonzero at
the point of computation; negative factors are allowed as well.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 5.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Christoffel map of a nonvanishing scalar multiple of the Euclidean metric. -/
theorem christoffelSecondKind_smul_innerSL {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hfx : f x ≠ 0) (u v : E) :
    christoffelSecondKind (fun y ↦ f y • innerSL ℝ) x u v =
      (2 * f x)⁻¹ • (fderiv ℝ f x v • u + fderiv ℝ f x u • v -
        inner ℝ u v • gradient f x) := by
  -- Cache the bilinear-space instance so typeclass search resolves `IsBoundedSMul`
  -- when applying `HasFDerivAt.smul_const` to the operator-valued metric.
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  apply ext_inner_right ℝ
  intro w
  apply mul_left_cancel₀ hfx
  have h := apply_christoffelSecondKind
    (g := fun y ↦ f y • innerSL ℝ) (nondegenerate_toBilinForm_smul_innerSL hfx) u v w
  have hd := (hf.hasFDerivAt.smul_const (F := E →L[ℝ] E →L[ℝ] ℝ) (innerSL ℝ)).fderiv
  simp only [smul_apply, innerSL_apply_apply ℝ, smul_eq_mul,
    christoffelFirstKind_apply, hd,
    ContinuousLinearMap.smulRight_apply] at h
  rw [h]
  simp [inner_sub_left, inner_add_left, real_inner_smul_left]
  field_simp
  ring

end TauCeti.Manifold
