/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic

/-!
# The gradient on a normed space

On a flat inner product space with its standard Riemannian metric, the manifold gradient agrees
with Mathlib's `gradient`.
-/

public section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

open Riemannian.Tensor

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
  have hinner (a b : TangentSpace 𝓘(ℝ, F) x) :
      inner ℝ a b = inner ℝ (NormedSpace.fromTangentSpace x a)
        (NormedSpace.fromTangentSpace x b) := by
    -- `TangentSpace` is a type synonym for `F`, `fromTangentSpace` is its
    -- canonical `tangentSpaceCastModel`, and the standard metric has `innerSL` as
    -- its inner product. This is the same definitional transport used by
    -- Mathlib's `norm_tangentSpace_vectorSpace`.
    rfl
  calc
    inner ℝ (NormedSpace.fromTangentSpace x (mgradient 𝓘(ℝ, F) f x)) v =
      inner ℝ (mgradient 𝓘(ℝ, F) f x) ((NormedSpace.fromTangentSpace x).symm v) := by
        simpa using (hinner (mgradient 𝓘(ℝ, F) f x)
          ((NormedSpace.fromTangentSpace x).symm v)).symm
    _ = inner ℝ (gradient f x) v := by
      rw [inner_mgradient, ← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      rw [mvfderiv_eq_fderiv]
      simp

end TauCeti.Manifold
