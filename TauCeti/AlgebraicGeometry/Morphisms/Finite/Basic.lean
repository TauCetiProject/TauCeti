/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.TargetLocal
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalRing.Module
import TauCeti.RingTheory.QuasiFinite.Basic

/-!
# Sections of finite morphisms

For a finite morphism `f : X ⟶ Spec R`, the global sections `Γ(X, ⊤)` form a finite
`R`-module. `AlgebraicGeometry.Scheme.Hom.moduleFinite_appTop` states this for an existing
`R`-algebra structure compatible with the map of global sections. It transports Mathlib's
`Scheme.Hom.finite_appTop` across the canonical isomorphism `R ≅ Γ(Spec R, ⊤)`. When `R` has
finitely many maximal ideals, `Γ(X, ⊤)` therefore also has finitely many maximal ideals
(`AlgebraicGeometry.Scheme.Hom.finite_maximalSpectrum_appTop`).

This finiteness is used to compute the rank of a finite morphism over a field as the dimension
of its global sections.

For a finite flat morphism `g : Z ⟶ Y` over an affine scheme `Y` whose global sections form a local
ring, `Γ(Z, ⊤)` is free over `Γ(Y, ⊤)` (`AlgebraicGeometry.Scheme.Hom.free_appTop`), with no
finite-presentation assumption. If `g : Y ⟶ S` is finite, flat and locally of finite presentation
(finite locally free), its sections `Γ(Y, g⁻¹ U)` over an affine open `U` of `S` form a projective
`Γ(S, U)`-module (`AlgebraicGeometry.Scheme.Hom.projective_app`).

Finite, locally finite type and locally finitely presented morphisms each respect isomorphisms
(`TauCeti.isFinite_respectsIso`, `TauCeti.locallyOfFiniteType_respectsIso` and
`TauCeti.locallyOfFinitePresentation_respectsIso`; for flat morphisms this is
`TauCeti.flat_respectsIso` in `TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic`),
and hence transfer from a closed immersion composite `i ≫ f` to `i.ker.subschemeι ≫ f`
(`AlgebraicGeometry.Scheme.Hom.isFinite_ker_subschemeι_comp`,
`AlgebraicGeometry.Scheme.Hom.flat_ker_subschemeι_comp`,
`AlgebraicGeometry.Scheme.Hom.locallyOfFinitePresentation_ker_subschemeι_comp`).

The instance stating that finiteness of a morphism is local on the target
(`AlgebraicGeometry.isZariskiLocalAtTarget_isFinite`) is in
`TauCeti.AlgebraicGeometry.Morphisms.Finite.TargetLocal`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A finite morphism to the spectrum of a commutative ring has module-finite global sections,
for any `R`-algebra structure on `Γ(X, ⊤)` given by the map of global sections. -/
theorem Scheme.Hom.moduleFinite_appTop {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsFinite f] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    Module.Finite R Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap, hf]
  exact (RingHom.finite_respectsIso.cancel_left_isIso _ _).mpr f.finite_appTop

/-- For a finite morphism `g : Z ⟶ Spec R` over a ring `R` with finitely many maximal ideals, the
coordinate ring `Γ(Z, ⊤)` has finitely many maximal ideals. -/
theorem Scheme.Hom.finite_maximalSpectrum_appTop {R : Type u} [CommRing R]
    [Finite (MaximalSpectrum R)] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of R)) [IsFinite g] :
    Finite (MaximalSpectrum Γ(Z, ⊤)) := by
  let : Algebra R Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := g.moduleFinite_appTop rfl
  exact TauCeti.finite_maximalSpectrum_of_isIntegral_of_quasiFinite R

/-- For a finite flat morphism `g : Z ⟶ Y` over an affine scheme `Y` with `Γ(Y, ⊤)` local,
`Γ(Z, ⊤)` is a free `Γ(Y, ⊤)`-module. -/
theorem Scheme.Hom.free_appTop {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsAffine Y] [IsFinite g] [Flat g]
    [IsLocalRing Γ(Y, ⊤)] : letI := g.appTop.hom.toAlgebra; Module.Free Γ(Y, ⊤) Γ(Z, ⊤) := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  have := g.finite_appTop; have := g.flat_appTop; algebraize [g.appTop.hom]
  exact Module.free_of_flat_of_isLocalRing

/-- The sections of a finite, flat, locally finitely presented morphism `g : Y ⟶ S` over an affine
open `U` of `S` form a projective module over `Γ(S, U)`. -/
theorem Scheme.Hom.projective_app {Y S : Scheme.{u}} (g : Y ⟶ S) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (U : S.affineOpens) :
    letI := (g.app U).hom.toAlgebra
    Module.Projective Γ(S, U) Γ(Y, g ⁻¹ᵁ U) := by
  have hflat := g.flat_appLE U.property (U.property.preimage g) le_rfl
  have hfp := g.finitePresentation_appLE U.property (U.property.preimage g) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hflat hfp
  have hfin := g.finite_app U U.property
  algebraize [(g.app U).hom]
  have := Module.FinitePresentation.of_finite_of_finitePresentation (R := Γ(S, U))
    (S := Γ(Y, g ⁻¹ᵁ U))
  exact Module.Flat.projective_of_finitePresentation

end AlgebraicGeometry

namespace TauCeti

open AlgebraicGeometry

universe u

/-- Finite morphisms of schemes respect isomorphisms. -/
instance isFinite_respectsIso :
    MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Morphisms of schemes locally of finite type respect isomorphisms. -/
instance locallyOfFiniteType_respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Morphisms of schemes locally of finite presentation respect isomorphisms. -/
instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) [IsClosedImmersion i]

/-- If `i : Z ⟶ X` is a closed immersion with `i ≫ f` finite, then `V(i.ker) ⟶ S` is finite. -/
instance isFinite_ker_subschemeι_comp [IsFinite (i ≫ f)] : IsFinite (i.ker.subschemeι ≫ f) := by
  rw [← (Iso.inv_comp_eq (asIso i.toImage)).mpr (i.toImage_imageι_assoc f).symm]; infer_instance

/-- If `i : Z ⟶ X` is a closed immersion with `i ≫ f` flat, then `V(i.ker) ⟶ S` is flat. -/
instance flat_ker_subschemeι_comp [Flat (i ≫ f)] : Flat (i.ker.subschemeι ≫ f) := by
  rw [← (Iso.inv_comp_eq (asIso i.toImage)).mpr (i.toImage_imageι_assoc f).symm]; infer_instance

/-- If `i : Z ⟶ X` is a closed immersion with `i ≫ f` locally of finite presentation, then
`V(i.ker) ⟶ S` is locally of finite presentation. -/
instance locallyOfFinitePresentation_ker_subschemeι_comp [LocallyOfFinitePresentation (i ≫ f)] :
    LocallyOfFinitePresentation (i.ker.subschemeι ≫ f) := by
  rw [← (Iso.inv_comp_eq (asIso i.toImage)).mpr (i.toImage_imageι_assoc f).symm]; infer_instance

end AlgebraicGeometry.Scheme.Hom
