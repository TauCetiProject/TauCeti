/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Extension
public import TauCeti.CategoryTheory.Exact.FullSubcategory
public import TauCeti.CategoryTheory.Exact.Frobenius

/-!
# The Frobenius category of Gorenstein-projective modules

Finitely generated Gorenstein-projective modules inherit the exact structure of modules.
This exact structure is Frobenius: complete resolutions give enough projectives and injectives,
and both classes consist exactly of the finitely generated projective modules. Finite
projectives are relatively injective because maps into them extend across short exact sequences
with Gorenstein-projective quotient. Conversely, each relative projective or injective is a
retract of the projective middle term of a complete-resolution presentation.

These results supply the Frobenius structure needed for the triangulated stable category of
Gorenstein-projectives. No noetherian or self-injectivity hypothesis is needed. Modules here are
left modules; apply the construction to `Rᵐᵒᵖ` for right `R`-modules. The module universe can be
independent of the ring universe, provided the ring is small in it. In particular, taking both
universes equal includes the regular module and all its finite free powers.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 10.2.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace TauCeti.GorensteinProjectiveModuleCat

variable (A : Type u) [Ring A] [Small.{v} A]

/-- The exact structure on finitely generated Gorenstein-projective modules induced by the
canonical abelian exact structure on all modules. -/
def exactStructure : ExactStructure (GorensteinProjectiveModuleCat.{v} A) :=
  (ExactStructure.abelian (ModuleCat.{v} A)).fullSubcategory
    (IsGorensteinProjective A) IsGorensteinProjective.isExtensionClosed

/-- Conflations of Gorenstein-projectives are precisely the underlying short exact sequences
of modules. -/
@[simp]
theorem exactStructure_conflation_iff (S : ShortComplex (GorensteinProjectiveModuleCat.{v} A)) :
    (exactStructure A).Conflation S ↔
      (S.map (IsGorensteinProjective A).ι).ShortExact := by
  rw [exactStructure, ExactStructure.fullSubcategory_conflation_iff,
    ExactStructure.abelian_conflation]

variable {A}

private theorem exists_projective_sequence (X : GorensteinProjectiveModuleCat.{v} A) :
    ∃ (K P : GorensteinProjectiveModuleCat.{v} A) (i : K ⟶ P) (p : P ⟶ X)
      (h : i ≫ p = 0), (exactStructure A).Conflation (ShortComplex.mk i p h) ∧
        Projective P.obj := by
  obtain ⟨S, hS, ⟨e⟩, hfin, hproj, hK⟩ := X.property.exists_projectivePresentation
  have := hfin
  have := hproj
  let K : GorensteinProjectiveModuleCat.{v} A := ⟨S.X₁, hK⟩
  let P : GorensteinProjectiveModuleCat.{v} A :=
    ⟨S.X₂, isGorensteinProjective_of_projective S.X₂⟩
  let i : K ⟶ P := ObjectProperty.homMk S.f
  let p : P ⟶ X := ObjectProperty.homMk (S.g ≫ e.hom)
  have h : i ≫ p = 0 := ObjectProperty.hom_ext _ (by simp [i, p])
  refine ⟨K, P, i, p, h, ?_, hproj⟩
  rw [exactStructure_conflation_iff]
  exact ShortComplex.shortExact_of_iso (S₁ := S)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by simp [i]) (by simp [p])) hS

private theorem exists_injective_sequence (X : GorensteinProjectiveModuleCat.{v} A) :
    ∃ (I K : GorensteinProjectiveModuleCat.{v} A) (i : X ⟶ I) (p : I ⟶ K)
      (h : i ≫ p = 0), (exactStructure A).Conflation (ShortComplex.mk i p h) ∧
        Projective I.obj := by
  obtain ⟨S, hS, ⟨e⟩, hfin, hproj, hK⟩ := X.property.exists_projectiveCopresentation
  have := hfin
  have := hproj
  let I : GorensteinProjectiveModuleCat.{v} A :=
    ⟨S.X₂, isGorensteinProjective_of_projective S.X₂⟩
  let K : GorensteinProjectiveModuleCat.{v} A := ⟨S.X₃, hK⟩
  let i : X ⟶ I := ObjectProperty.homMk (e.inv ≫ S.f)
  let p : I ⟶ K := ObjectProperty.homMk S.g
  have h : i ≫ p = 0 := ObjectProperty.hom_ext _ (by simp [i, p])
  refine ⟨I, K, i, p, h, ?_, hproj⟩
  rw [exactStructure_conflation_iff]
  exact ShortComplex.shortExact_of_iso (S₁ := S)
    (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by simp [i]) (by simp [p])) hS

/-- The relative projectives among Gorenstein-projectives are exactly the projective underlying
modules, which are already finitely generated. -/
@[simp]
theorem exactStructure_isProjective_iff (X : GorensteinProjectiveModuleCat.{v} A) :
    (exactStructure A).isProjective X ↔ Projective X.obj := by
  constructor
  · intro hX
    obtain ⟨K, P, i, p, h, hS, hP⟩ := exists_projective_sequence X
    let s := (exactStructure A).splittingOfProjective hS hX
    let r : Retract X.obj P.obj :=
      { i := s.s.hom
        r := p.hom
        retract := by simpa using (IsGorensteinProjective A).ι.congr_map s.s_g }
    exact r.projective
  · intro hX
    exact ExactStructure.isProjective_fullSubcategory_of_isProjective
      IsGorensteinProjective.isExtensionClosed X
      ((ExactStructure.abelian_isProjective_iff X.obj).mpr hX)

/-- The relative injectives among Gorenstein-projectives are also exactly the projective
underlying modules, not the injectives of the ambient module category. -/
@[simp]
theorem exactStructure_isInjective_iff (X : GorensteinProjectiveModuleCat.{v} A) :
    (exactStructure A).isInjective X ↔ Projective X.obj := by
  constructor
  · intro hX
    obtain ⟨I, K, i, p, h, hS, hI⟩ := exists_injective_sequence X
    let s := (exactStructure A).splittingOfInjective hS hX
    let r : Retract X.obj I.obj :=
      { i := i.hom
        r := s.r.hom
        retract := by simpa using (IsGorensteinProjective A).ι.congr_map s.f_r }
    exact r.projective
  · intro hX
    rw [ExactStructure.isInjective_iff]
    intro Y Z i hi f
    obtain ⟨K, p, h, hS⟩ := (ConflationClass.isInflation_iff _ _).mp hi
    have hS' := (exactStructure_conflation_iff A _).mp hS
    have := X.property.finite
    have := hX
    obtain ⟨g, hg⟩ := K.property.exists_extend hS' X.obj f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

/-- Complete resolutions provide enough relative projectives in the inherited exact
structure. -/
theorem exactStructure_enoughProjectives : (exactStructure A).EnoughProjectives where
  presentation X := by
    obtain ⟨K, P, i, p, h, hS, hP⟩ := exists_projective_sequence X
    exact ⟨{ K := K
             P := P
             i := i
             p := p
             zero := h
             conflation := hS
             isProjective := (exactStructure_isProjective_iff P).mpr hP }⟩

/-- Complete resolutions provide enough relative injectives in the inherited exact
structure, with projective underlying middle modules. -/
theorem exactStructure_enoughInjectives : (exactStructure A).EnoughInjectives where
  presentation X := by
    obtain ⟨I, K, i, p, h, hS, hI⟩ := exists_injective_sequence X
    exact ⟨{ I := I
             K := K
             i := i
             p := p
             zero := h
             conflation := hS
             isInjective := (exactStructure_isInjective_iff I).mpr hI }⟩

/-- Finitely generated Gorenstein-projective modules, with the inherited exact structure, form
a Frobenius exact category. The projective-injective objects are the finite projectives. -/
theorem exactStructure_isFrobenius : (exactStructure A).IsFrobenius where
  enoughProjectives := exactStructure_enoughProjectives
  enoughInjectives := exactStructure_enoughInjectives
  projective_iff_injective X := by
    rw [exactStructure_isProjective_iff, exactStructure_isInjective_iff]

end TauCeti.GorensteinProjectiveModuleCat
