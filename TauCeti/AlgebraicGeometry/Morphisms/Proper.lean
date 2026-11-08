/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper morphisms of affine schemes

A morphism of affine schemes `Spec S ⟶ Spec R` is proper exactly when `S` is a finite
`R`-module. This is the affine case of Mathlib's characterization of finite morphisms as the
proper affine ones (`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), combined with
the description of finite morphisms of affine schemes
(`AlgebraicGeometry.IsFinite.SpecMap_iff`).

For example, the affine line `Spec R[t] ⟶ Spec R` over a nonzero ring is not proper, since
`R[t]` is not a finite `R`-module.

A morphism of `S`-schemes from a proper `S`-scheme to a separated one is quasi-compact
(`AlgebraicGeometry.quasiCompact_left_of_isProper`).
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

/-- A morphism of `S`-schemes from a proper `S`-scheme to a separated one has quasi-compact
underlying map. -/
theorem quasiCompact_left_of_isProper {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U)
    [IsProper T.hom] [IsSeparated U.hom] : QuasiCompact f.left := by
  have : IsProper (f.left ≫ U.hom) := by
    rw [Over.w f]
    infer_instance
  have := IsProper.of_comp f.left U.hom
  infer_instance

end AlgebraicGeometry
