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

A morphism of `S`-schemes whose source has quasi-compact structure map and whose target has
quasi-separated structure map is quasi-compact
(`AlgebraicGeometry.quasiCompact_left_of_quasiCompact_hom`); in particular this applies from a
proper `S`-scheme to a separated one.
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

/-- A morphism of `S`-schemes from a scheme with quasi-compact structure map to one with
quasi-separated structure map has quasi-compact underlying map. -/
theorem quasiCompact_left_of_quasiCompact_hom {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U)
    [QuasiCompact T.hom] [QuasiSeparated U.hom] : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ U.hom) := by
    rw [Over.w f]
    infer_instance
  exact QuasiCompact.of_comp f.left U.hom

end AlgebraicGeometry
