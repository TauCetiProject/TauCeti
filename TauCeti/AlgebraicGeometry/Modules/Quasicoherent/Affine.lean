/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Quasi-coherent modules on an affine scheme

The category of quasi-coherent modules on an affine scheme `X` is abelian and has enough
injectives. Pullback along `X.isoSpec` and Mathlib's tilde equivalence identify it with
`ModuleCat Γ(X, ⊤)`. These are the category theoretic inputs for deriving exact global sections.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace QuasicoherentSheaf

/-- Quasi-coherent modules on an affine scheme are equivalent to modules over its global
sections. -/
noncomputable def affineEquiv (X : Scheme.{u}) [IsAffine X] :
    QuasicoherentSheaf X ≌ ModuleCat Γ(X, ⊤) :=
  (equivOfIso X.isoSpec).symm.trans (tildeEquiv (R := Γ(X, ⊤))).symm

/-- The forward functor of the affine equivalence is pullback to the spectrum followed by
global sections. -/
@[simp]
theorem affineEquiv_functor (X : Scheme.{u}) [IsAffine X] :
    (affineEquiv X).functor =
      pullback X.isoSpec.inv ⋙ (tildeEquiv (R := Γ(X, ⊤))).inverse := by
  simp [affineEquiv]

/-- The inverse functor of the affine equivalence is tilde followed by pullback to the
affine scheme. -/
@[simp]
theorem affineEquiv_inverse (X : Scheme.{u}) [IsAffine X] :
    (affineEquiv X).inverse =
      (tildeEquiv (R := Γ(X, ⊤))).functor ⋙ pullback X.isoSpec.hom := by
  simp [affineEquiv]

/-- Quasi-coherent modules on an affine scheme form an abelian category. -/
noncomputable instance (X : Scheme.{u}) [IsAffine X] : Abelian (QuasicoherentSheaf X) := by
  let e := affineEquiv X
  letI : Limits.HasFiniteProducts (QuasicoherentSheaf X) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact abelianOfEquivalence e.functor

/-- Quasi-coherent modules on an affine scheme admit injective resolutions. -/
noncomputable instance (X : Scheme.{u}) [IsAffine X] :
    EnoughInjectives (QuasicoherentSheaf X) := by
  let : EnoughInjectives (ModuleCat Γ(X, ⊤)) := ModuleCat.enoughInjectives _
  exact EnoughInjectives.of_equivalence (affineEquiv X).functor

end QuasicoherentSheaf

end AlgebraicGeometry

end TauCeti
