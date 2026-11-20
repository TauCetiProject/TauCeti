/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper morphisms

A morphism of affine schemes `Spec S ⟶ Spec R` is proper exactly when `S` is a finite
`R`-module. This is the affine case of Mathlib's characterization of finite morphisms as the
proper affine ones (`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), combined with
the description of finite morphisms of affine schemes
(`AlgebraicGeometry.IsFinite.SpecMap_iff`).

For example, the affine line `Spec R[t] ⟶ Spec R` over a nonzero ring is not proper, since
`R[t]` is not a finite `R`-module.

An open subscheme whose inclusion is a closed immersion is proper over every base over which
the ambient scheme is proper (`AlgebraicGeometry.Scheme.Opens.isProper_over`).
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

/-- An open subscheme whose inclusion is closed is proper over any base over which the ambient
scheme is proper. -/
instance Scheme.Opens.isProper_over {S X : Scheme} [X.Over S] (U : X.Opens)
    [IsClosedImmersion U.ι] [IsProper (X ↘ S)] : IsProper (U.toScheme ↘ S) := by
  rw [← Scheme.Opens.ι_comp_over]
  infer_instance

end AlgebraicGeometry
