/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Tangent-space casts and preferred trivialization bridges

Basic identities for `tangentSpaceCast` and `tangentSpaceCastModel`, together with bridges
identifying the preferred tangent-bundle trivialization at a point `x` with
`tangentSpaceCastModel I x` and its inverse.

## Main results

* `TauCeti.Manifold.tangentSpaceCast_symm`,
  `TauCeti.Manifold.tangentSpaceCastModel_tangentSpaceCast`,
  `TauCeti.Manifold.tangentSpaceCast_tangentSpaceCastModel_symm`,
  `TauCeti.Manifold.tangentSpaceCastModel_apply`, and
  `TauCeti.Manifold.tangentSpaceCastModel_symm_apply`: basic identities for the foundational
  tangent-space casts.
* `TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self_eq_tangentSpaceCastModel` and
  `TauCeti.Manifold.symmL_trivializationAt_self_eq_tangentSpaceCastModel_symm`: over its own base
  point `x`, the preferred tangent-bundle trivialization and its inverse agree with
  `tangentSpaceCastModel I x` and its inverse.
-/

public section

open Bundle Manifold
open scoped Manifold

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Casts

/-- Inverting `tangentSpaceCast I x y` reverses the source and target base points. -/
@[simp]
theorem tangentSpaceCast_symm (I : ModelWithCorners 𝕜 E H) (x y : M) :
    (tangentSpaceCast I x y).symm = tangentSpaceCast I y x := by
  -- At this foundational bridge, both directions of `tangentSpaceCast` act as the identity on `E`.
  ext v
  rfl

/-- Reading a tangent vector in the model space `E` is invariant under `tangentSpaceCast`. -/
@[simp]
theorem tangentSpaceCastModel_tangentSpaceCast (I : ModelWithCorners 𝕜 E H) (x y : M)
    (v : TangentSpace I x) :
    tangentSpaceCastModel I y (tangentSpaceCast I x y v) = tangentSpaceCastModel I x v := by
  -- At this foundational bridge, both implementation casts act as the identity on `E`.
  rfl

/-- Transporting an inverse model-space cast `(tangentSpaceCastModel I x).symm v` along
`tangentSpaceCast I x y` yields `(tangentSpaceCastModel I y).symm v`. -/
@[simp]
theorem tangentSpaceCast_tangentSpaceCastModel_symm (I : ModelWithCorners 𝕜 E H) (x y : M)
    (v : E) :
    tangentSpaceCast I x y ((tangentSpaceCastModel I x).symm v) =
      (tangentSpaceCastModel I y).symm v :=
  (tangentSpaceCastModel I y).injective (by simp)

/-- The foundational tangent-to-model cast preserves the underlying vector in `E`.
Use this equation explicitly: automatic simplification would erase the distinction between
`TangentSpace I x` and `E`. -/
theorem tangentSpaceCastModel_apply (I : ModelWithCorners 𝕜 E H) (x : M)
    (v : TangentSpace I x) :
    tangentSpaceCastModel I x v = v := by
  -- At this foundational bridge, `tangentSpaceCastModel` is the identity on `E`.
  rfl

/-- The inverse model-to-tangent cast preserves the underlying vector in `E`.
As with `tangentSpaceCastModel_apply`, use this equation only at explicit tangent/model bridges. -/
theorem tangentSpaceCastModel_symm_apply (I : ModelWithCorners 𝕜 E H) (x : M) (v : E) :
    (tangentSpaceCastModel I x).symm v = v := by
  -- At this foundational bridge, `(tangentSpaceCastModel I x).symm` is the identity on `E`.
  rfl

end Casts

section BasePoint

variable [IsManifold I 1 M]

/-- Over its own base point `x`, the continuous linear map of the canonical tangent-bundle
trivialization is `tangentSpaceCastModel I x`. Not `@[simp]`: evaluation already simplifies via
`continuousLinearMapAt_trivializationAt_self`. -/
theorem continuousLinearMapAt_trivializationAt_self_eq_tangentSpaceCastModel (x : M) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x =
      (tangentSpaceCastModel I x).toContinuousLinearMap := by
  ext v
  rw [continuousLinearMapAt_trivializationAt_self]
  exact (tangentSpaceCastModel_apply I x v).symm

/-- Over its own base point `x`, the inverse continuous linear map of the canonical tangent-bundle
trivialization is `(tangentSpaceCastModel I x).symm`. Not `@[simp]`: evaluation already simplifies
via `symmL_trivializationAt_self`. -/
theorem symmL_trivializationAt_self_eq_tangentSpaceCastModel_symm (x : M) :
    (trivializationAt E (TangentSpace I) x).symmL 𝕜 x =
      (tangentSpaceCastModel I x).symm.toContinuousLinearMap := by
  ext v
  rw [symmL_trivializationAt_self]
  exact (tangentSpaceCastModel_symm_apply I x v).symm

end BasePoint

end TauCeti.Manifold
