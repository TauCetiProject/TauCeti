/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic

/-!
# The gradient on a normed space

On a flat inner product space with its standard Riemannian metric, the manifold gradient agrees
with Mathlib's `gradient`; the squared norm therefore has the expected radial gradient.
-/

public section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

open Riemannian.Tensor

/-- The canonical identification of a tangent space of a real inner-product space with the
model space preserves inner products. -/
theorem inner_tangentSpace_vectorSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {x : F}
    (v w : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ v w = inner ℝ (NormedSpace.fromTangentSpace x v)
      (NormedSpace.fromTangentSpace x w) := by
  -- `TangentSpace` is a type synonym for `F`, `fromTangentSpace` is its
  -- canonical `tangentSpaceCastModel`, and the standard metric has `innerSL` as
  -- its inner product. This is the same definitional transport used by
  -- Mathlib's `norm_tangentSpace_vectorSpace`.
  rfl

/-- On a flat inner product space with its standard Riemannian metric, the manifold gradient is
Mathlib's `gradient`. -/
theorem mgradient_eq_gradient {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : F → ℝ) (x : F) :
    let _ : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
      ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩
    mgradient 𝓘(ℝ, F) f x = gradient f x := by
  dsimp only
  apply (NormedSpace.fromTangentSpace x).injective
  apply ext_inner_right ℝ
  intro v
  calc
    inner ℝ (NormedSpace.fromTangentSpace x (mgradient 𝓘(ℝ, F) f x)) v =
      inner ℝ (mgradient 𝓘(ℝ, F) f x) ((NormedSpace.fromTangentSpace x).symm v) := by
        simpa using (inner_tangentSpace_vectorSpace (mgradient 𝓘(ℝ, F) f x)
          ((NormedSpace.fromTangentSpace x).symm v)).symm
    _ = inner ℝ (gradient f x) v := by
      rw [inner_mgradient, ← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      rw [mvfderiv_eq_fderiv]
      simp

/-- If the installed fibre metric is the standard one, the manifold gradient has the norm of
Mathlib's `gradient`. This transports `mgradient_eq_gradient` along an equality of fibre metrics,
such as `toRiemannianMetric_ofLE`, which cannot be rewritten inside the instance-dependent
arguments. -/
theorem norm_mgradient_eq_norm_gradient_of_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [inst : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    (hg : RiemannianBundle.g = (riemannianMetricVectorSpace F).toRiemannianMetric)
    (f : F → ℝ) (x : F) :
    ‖mgradient 𝓘(ℝ, F) f x‖ = ‖gradient f x‖ := by
  obtain ⟨_⟩ := inst
  subst hg
  rw [← mgradient_eq_gradient]
  exact norm_tangentSpace_vectorSpace

/-- The gradient of the squared norm in the standard flat metric is the radial vector field.

Source: `Mathlib.Analysis.InnerProductSpace.Calculus.fderiv_norm_sq_apply`.
-/
@[simp]
theorem mgradient_norm_sq_model_space {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (x : F) :
    let _ : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
      ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩
    mgradient 𝓘(ℝ, F) (fun y : F ↦ ‖y‖ ^ 2) x = 2 • x := by
  dsimp only
  have hx : (InnerProductSpace.toDual ℝ F).symm ((innerSL ℝ) x) = x := by
    have hdual : (innerSL ℝ) x = (InnerProductSpace.toDual ℝ F) x := by
      ext y
      rw [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    rw [hdual]
    exact (InnerProductSpace.toDual ℝ F).symm_apply_apply x
  rw [mgradient_eq_gradient]
  simp [gradient, fderiv_norm_sq_apply, hx]
  rfl

end TauCeti.Manifold
