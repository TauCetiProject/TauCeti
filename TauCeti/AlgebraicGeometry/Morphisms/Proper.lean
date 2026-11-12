/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper morphisms and affine schemes

A morphism of affine schemes `Spec S ⟶ Spec R` is proper exactly when `S` is a finite
`R`-module. This is the affine case of Mathlib's characterization of finite morphisms as the
proper affine ones (`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), combined with
the description of finite morphisms of affine schemes
(`AlgebraicGeometry.IsFinite.SpecMap_iff`).

For example, the affine line `Spec R[t] ⟶ Spec R` over a nonzero ring is not proper, since
`R[t]` is not a finite `R`-module.

Over a field, an integral scheme that is both affine and universally closed is a single point
(`AlgebraicGeometry.Scheme.subsingleton_of_isAffine_of_universallyClosed`): its global functions
form a field (`AlgebraicGeometry.isField_of_universallyClosed`), whose spectrum has one point. So
an integral scheme of positive dimension that is proper over a field, such as a proper curve, is
not affine.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes `Spec S ⟶ Spec R` is proper if and only if the ring map
`R → S` is finite. -/
@[simp]
lemma IsProper.SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsProper (Spec.map f) ↔ f.hom.Finite := by
  rw [← IsFinite.SpecMap_iff, IsFinite.iff_isProper_and_isAffineHom,
    and_iff_left (by infer_instance)]

/-- An integral scheme that is affine and universally closed over a field has at most one point:
its ring of global functions is a field, and the spectrum of a field is a point. -/
theorem Scheme.subsingleton_of_isAffine_of_universallyClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsIntegral X] [IsAffine X] [UniversallyClosed f] :
    Subsingleton X := by
  have : Subsingleton (Spec Γ(X, ⊤)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (isField_of_universallyClosed K f)
  exact X.isoSpec.hom.isOpenEmbedding.injective.subsingleton

end AlgebraicGeometry
