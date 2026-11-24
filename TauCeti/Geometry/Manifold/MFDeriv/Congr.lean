/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Congruence of manifold derivatives over equal base points

For a manifold `M` modelled on `I : ModelWithCorners 𝕜 E H`, every tangent space `TangentSpace I x`
is definitionally the model vector space `E`, identified with `E` by `tangentSpaceCastModel I x`.
This file records explicit equations for `tangentSpaceCastModel` and its inverse (parallel to
`NormedSpace.fromTangentSpace_apply` and `NormedSpace.fromTangentSpace_symm_apply`), together with
the congruence rule `TauCeti.mfderiv_apply_congr_point` comparing `mfderiv I J f q w` and
`mfderiv I J f p w'` in the target model vector space when `q = p` and `(w : E) = w'`.

## Main results

* `TauCeti.tangentSpaceCastModel_apply`, `TauCeti.tangentSpaceCastModel_symm_apply`, and
  `TauCeti.coe_tangentSpaceCast`: explicit equations for the canonical identifications between
  `TangentSpace I x` and the model vector space `E`.
* `TauCeti.mfderiv_apply_congr_point`: derivatives of a map at equal base points applied to tangent
  vectors with equal model coordinates have equal model coordinates.
* `TauCeti.apply_of_eq_neg_id`, `TauCeti.eq_neg_id_of_apply`, and
  `TauCeti.eq_neg_id_of_tangentSpaceCastModel_apply`: evaluate and prove `L = -id` for continuous
  linear maps `L : TangentSpace I p →L[𝕜] TangentSpace I q` over equal base points `q = p`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2012), Chapter 3.
-/

public section

open scoped Manifold

namespace TauCeti

section TangentSpaceCastModel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The canonical identification `tangentSpaceCastModel I x` between `TangentSpace I x` and the
model vector space `E` preserves the underlying vector. Like `NormedSpace.fromTangentSpace_apply`,
this is deliberately not `@[simp]` so that automatic simplification does not strip tangent-fibre
types when normed-space or Riemannian instances on `TangentSpace I x` differ from those on `E`. -/
theorem tangentSpaceCastModel_apply (x : M) (v : TangentSpace I x) :
    tangentSpaceCastModel I x v = v :=
  (rfl)

/-- The inverse of `tangentSpaceCastModel I x` preserves the underlying vector. -/
theorem tangentSpaceCastModel_symm_apply (x : M) (v : E) :
    (tangentSpaceCastModel I x).symm v = v :=
  (rfl)

/-- `tangentSpaceCast I q p` preserves the underlying model-space vector. -/
theorem coe_tangentSpaceCast (q p : M) (w : TangentSpace I q) :
    (tangentSpaceCast I q p w : E) = w :=
  (rfl)

end TangentSpaceCastModel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Manifold derivatives of `f` at equal base points `q = p`, applied to tangent vectors with equal
coordinates in the model vector space `E`, have equal coordinates in the target model vector space
`F`. -/
theorem mfderiv_apply_congr_point {f : M → N} {q p : M} (h : q = p)
    {w : TangentSpace I q} {w' : TangentSpace I p} (hw : (w : E) = w') :
    (mfderiv I J f q w : F) = mfderiv I J f p w' := by
  subst h hw
  rfl

/-- Variant of `mfderiv_apply_congr_point` reading tangent vectors explicitly through
`tangentSpaceCastModel`, avoiding type-class clashes when `TangentSpace` carries a non-model
norm. -/
theorem tangentSpaceCastModel_mfderiv_congr_point {f : M → N} {q p : M} (h : q = p)
    {w : TangentSpace I q} {w' : TangentSpace I p}
    (hw : tangentSpaceCastModel I q w = tangentSpaceCastModel I p w') :
    tangentSpaceCastModel J (f q) (mfderiv I J f q w) =
      tangentSpaceCastModel J (f p) (mfderiv I J f p w') := by
  subst h
  obtain rfl : w = w' := (tangentSpaceCastModel I q).injective hw
  rfl

/-- If `q = p` and `L : TangentSpace I p →L[𝕜] TangentSpace I q` equals `-id`, then `L` negates
every tangent vector in model coordinates. -/
theorem apply_of_eq_neg_id {q p : M} (hq : q = p)
    {L : TangentSpace I p →L[𝕜] TangentSpace I q}
    (hL : L = -ContinuousLinearMap.id 𝕜 (TangentSpace I p)) (v : TangentSpace I p) :
    (L v : E) = (-v : TangentSpace I p) := by
  subst hq
  rw [hL, FunLike.coe_neg, Pi.neg_apply, ContinuousLinearMap.id_apply]

/-- To prove `L = -id` for `L : TangentSpace I p →L[𝕜] TangentSpace I q` over equal base points
`q = p`, it suffices to show `(L v : E) = -v` for every `v : TangentSpace I p`. -/
theorem eq_neg_id_of_apply {q p : M} (hq : q = p)
    {L : TangentSpace I p →L[𝕜] TangentSpace I q}
    (hL : ∀ v : TangentSpace I p, (L v : E) = (-v : TangentSpace I p)) :
    L = -ContinuousLinearMap.id 𝕜 (TangentSpace I p) := by
  subst hq
  ext v
  rw [FunLike.coe_neg, Pi.neg_apply, ContinuousLinearMap.id_apply]
  exact hL v

/-- Variant of `eq_neg_id_of_apply` reading tangent vectors through `tangentSpaceCastModel`,
avoiding type-class clashes when `TangentSpace` carries a non-model norm. -/
theorem eq_neg_id_of_tangentSpaceCastModel_apply {q p : M} (hq : q = p)
    {L : TangentSpace I p →L[𝕜] TangentSpace I q}
    (hL : ∀ v : TangentSpace I p,
      tangentSpaceCastModel I q (L v) = -tangentSpaceCastModel I p v) :
    L = -ContinuousLinearMap.id 𝕜 (TangentSpace I p) := by
  subst hq
  ext v
  apply (tangentSpaceCastModel I q).injective
  rw [FunLike.coe_neg, Pi.neg_apply, ContinuousLinearMap.id_apply, map_neg]
  exact hL v

end TauCeti
