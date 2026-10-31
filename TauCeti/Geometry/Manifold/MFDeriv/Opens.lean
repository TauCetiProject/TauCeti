/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tangent images on open submanifolds

Restriction to an open source preserves the tangent image at each point. Inclusion of an open
target maps the tangent image by the canonical tangent-space equivalence. These identities let
pointwise conditions on tangent images be checked in open submanifolds.
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

end TauCeti.Manifold
