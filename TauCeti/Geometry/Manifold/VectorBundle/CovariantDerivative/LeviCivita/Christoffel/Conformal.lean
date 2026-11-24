/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Christoffel symbols under conformal rescaling

Rescaling an invertible metric by a nonvanishing scalar function adds an explicit correction
to its Christoffel map. For a metric `g y = f y • innerSL ℝ` on a real Hilbert space, this
correction is expressed using the differential
and gradient of `f`. This gives a reusable coordinate formula for conformally flat models,
including the round sphere in stereographic coordinates. The factor need only be nonzero at
the point of computation; negative factors are allowed as well.

## Formalization source

The computation is adapted and generalized from Yangyang Li's stereographic metric
formalization under the Apache 2.0 license. The port is by Riccardo Brasca.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 5.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

/-- Rescaling an invertible metric by a nonvanishing scalar function adds the conformal
correction to its Christoffel map. -/
theorem christoffelSecondKind_smul_apply {f : E → ℝ}
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hfx : f x ≠ 0) (hinv : (g x).IsInvertible) (u v : E) :
    christoffelSecondKind (fun y ↦ f y • g y) x u v =
      christoffelSecondKind g x u v + (2 * f x)⁻¹ •
        (fderiv ℝ f x v • u + fderiv ℝ f x u • v -
          g x u v • (g x).inverse (fderiv ℝ f x)) := by
  -- Cache the bilinear-space instance for operator-valued scalar multiplication.
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hd := (hf.hasFDerivAt.fun_smul (F := E →L[ℝ] E →L[ℝ] ℝ) hg.hasFDerivAt).fderiv
  have hfirst : christoffelFirstKind (fun y ↦ f y • g y) x u v =
      f x • christoffelFirstKind g x u v + (2 : ℝ)⁻¹ •
        (fderiv ℝ f x v • g x u + fderiv ℝ f x u • g x v -
          g x u v • fderiv ℝ f x) := by
    ext w
    simp [christoffelFirstKind_apply, hd]
    ring
  rw [christoffelSecondKind_apply, ContinuousLinearMap.inverse_smul, hfirst]
  simp only [smul_apply, map_add, map_sub, map_smul,
    hinv.inverse_apply_self, smul_add, smul_sub, smul_smul,
    christoffelSecondKind_apply]
  field_simp
  module

end NormedSpace

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Christoffel map of a nonvanishing scalar multiple of the Euclidean metric. -/
theorem christoffelSecondKind_smul_innerSL_apply {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hfx : f x ≠ 0) (u v : E) :
    christoffelSecondKind (fun y ↦ f y • innerSL ℝ) x u v =
      (2 * f x)⁻¹ • (fderiv ℝ f x v • u + fderiv ℝ f x u • v -
        inner ℝ u v • gradient f x) := by
  have hinner : innerSL ℝ (E := E) =
      (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap := by
    ext a b
    simp [innerSL_apply_apply ℝ, InnerProductSpace.toDual_apply_apply]
  have hinv : (innerSL ℝ (E := E)).IsInvertible :=
    InnerProductSpace.isInvertible_innerSL
  rw [christoffelSecondKind_smul_apply hf (differentiableAt_const _) hfx hinv]
  have hconst : christoffelSecondKind (fun _ : E ↦ innerSL ℝ) x u v = 0 := by
    rw [christoffelSecondKind_apply]
    have hfirst : christoffelFirstKind (fun _ : E ↦ innerSL ℝ) x u v = 0 := by
      ext w
      simp [christoffelFirstKind_apply]
    simp [hfirst]
  have hgrad : (innerSL ℝ).inverse (fderiv ℝ f x) = gradient f x := by
    rw [hinner, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, ← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  rw [hconst, zero_add, innerSL_apply_apply ℝ, hgrad]

end TauCeti.Manifold
