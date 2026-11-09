/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Tangent images on open submanifolds

Restriction to an open source preserves the tangent image at each point. Inclusion of an open
target maps the tangent image by the canonical tangent-space equivalence. These identities let
pointwise conditions on tangent images be checked in open submanifolds. Since the differential of
the inclusion of an open subset is the identity of the model space, restricting a map to an open
source, or following a map into an open target by the inclusion, does not change its differential
applied to a tangent vector. Differentiability itself is local, so a map and its restriction to
an open source have vanishing differentials at the same points, with no differentiability
assumption.
-/

public section

open TopologicalSpace
open scoped Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Restricting a differentiable map to an open source preserves its tangent image. -/
theorem range_mfderiv_comp_subtype_val {U : Opens N} {f : N → M} (x : U)
    (hf : MDifferentiableAt J I f (x : N)) :
    LinearMap.range (mfderiv J I (f ∘ (Subtype.val : U → N)) x).toLinearMap =
      LinearMap.range (mfderiv J I f (x : N)).toLinearMap := by
  rw [mfderiv_comp x hf (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
    mfderiv_subtype_val, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (tangentSpaceOpenEquiv (I := J) x).surjective

/-- Inclusion of an open target transports the tangent image by the canonical tangent-space
equivalence. -/
theorem range_mfderiv_subtype_val_comp {U : Opens M} {f : N → U} (x : N)
    (hf : MDifferentiableAt J I f x) :
    LinearMap.range (mfderiv J I ((Subtype.val : U → M) ∘ f) x).toLinearMap =
      (LinearMap.range (mfderiv J I f x).toLinearMap).map
        (tangentSpaceOpenEquiv (I := I) (f x)).toLinearEquiv.toLinearMap := by
  rw [mfderiv_comp x (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) hf,
    mfderiv_subtype_val, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  -- Both projections of the continuous linear equivalence use its underlying linear map.
  rfl

/-- Restricting a differentiable map to an open source does not change its differential. -/
theorem mfderiv_comp_subtype_val_apply {U : Opens N} {f : N → M} {x : U}
    (hf : MDifferentiableAt J I f (x : N)) (v : TangentSpace J x) :
    mfderiv J I (f ∘ (Subtype.val : U → N)) x v = mfderiv J I f (x : N) v := by
  rw [mfderiv_comp x hf (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
    ContinuousLinearMap.comp_apply, mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    tangentSpaceOpenEquiv_apply]

/-- Following a differentiable map into an open target by the inclusion does not change its
differential. -/
theorem mfderiv_subtype_val_comp_apply {U : Opens M} {f : N → U} {x : N}
    (hf : MDifferentiableAt J I f x) (v : TangentSpace J x) :
    mfderiv J I ((Subtype.val : U → M) ∘ f) x v = mfderiv J I f x v := by
  rw [mfderiv_comp x (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) hf,
    ContinuousLinearMap.comp_apply, mfderiv_subtype_val]
  exact tangentSpaceOpenEquiv_apply _ _

/-- A map is differentiable at a point of an open subset exactly when its restriction to that
subset is. -/
@[simp]
theorem mdifferentiableAt_comp_subtype_val_iff {U : Opens N} {f : N → M} {x : U} :
    MDifferentiableAt J I (f ∘ (Subtype.val : U → N)) x ↔ MDifferentiableAt J I f (x : N) :=
  (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val f x).symm

/-- The differential of a map vanishes at a point of an open subset exactly when the differential
of its restriction to that subset does. No differentiability is assumed: where the map is not
differentiable, neither is its restriction, and both differentials are zero by convention. -/
@[simp]
theorem mfderiv_comp_subtype_val_eq_zero_iff {U : Opens N} {f : N → M} {x : U} :
    mfderiv J I (f ∘ (Subtype.val : U → N)) x = 0 ↔ mfderiv J I f (x : N) = 0 := by
  by_cases hf : MDifferentiableAt J I f (x : N)
  · simp only [ContinuousLinearMap.ext_iff, zero_apply,
      mfderiv_comp_subtype_val_apply hf]
    -- The tangent spaces at `x` in `U` and at `(x : N)` in `N` are both the model space `E'`.
    exact Iff.rfl
  · rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt (mdifferentiableAt_comp_subtype_val_iff.not.mpr hf)]
    simp

end TauCeti.Manifold
