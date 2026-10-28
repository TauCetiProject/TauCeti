/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Real Euclidean models for complex manifolds

`TauCeti.complexEuclideanRealModel` expresses the realification of a complex Euclidean model
in standard real Euclidean coordinates. The chart carrier stays `EuclideanSpace ℂ (Fin n)`;
only the model vector space changes to `EuclideanSpace ℝ (Fin (2 * n))`.

The model is Mathlib's `ModelWithCorners.transContinuousLinearEquiv` applied to the norm
preserving coordinates `TauCeti.complexEuclideanRealLinearIsometryEquiv`. After installing
`IsManifold.restrictScalars ℝ` locally and rewriting `complexEuclideanRealModel_def`, Mathlib's
existing transport instance supplies its `IsManifold` structure at any regularity, and
`ContinuousLinearEquiv.toTransContinuousLinearEquiv` is the identity comparison diffeomorphism.
The application equations below identify this transport explicitly with real and imaginary
coordinates, including when used in extended charts.
-/

public section

open scoped Manifold

namespace TauCeti

/-- The real Euclidean model of a complex Euclidean chart, with the same chart carrier. -/
noncomputable def complexEuclideanRealModel (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (2 * n))) (EuclideanSpace ℂ (Fin n)) :=
  𝓘(ℝ, EuclideanSpace ℂ (Fin n)).transContinuousLinearEquiv
    (complexEuclideanRealLinearIsometryEquiv n).toContinuousLinearEquiv

/-- The real Euclidean model is the standard transport along the coordinate isometry. -/
theorem complexEuclideanRealModel_def (n : ℕ) :
    complexEuclideanRealModel n =
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)).transContinuousLinearEquiv
        (complexEuclideanRealLinearIsometryEquiv n).toContinuousLinearEquiv := (rfl)

variable {n : ℕ}

/-- The real Euclidean model applies the standard coordinate isometry. -/
@[simp↓]
theorem complexEuclideanRealModel_apply (v : EuclideanSpace ℂ (Fin n)) :
    complexEuclideanRealModel n v = complexEuclideanRealLinearIsometryEquiv n v := by
  simp [complexEuclideanRealModel]

/-- The inverse real Euclidean model reconstructs the complex coordinates. -/
@[simp↓]
theorem complexEuclideanRealModel_symm_apply (v : EuclideanSpace ℝ (Fin (2 * n))) :
    (complexEuclideanRealModel n).symm v =
      (complexEuclideanRealLinearIsometryEquiv n).symm v := by
  simp [complexEuclideanRealModel]

end TauCeti
