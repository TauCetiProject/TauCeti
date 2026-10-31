/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Extension
public import TauCeti.CategoryTheory.Exact.FullSubcategory
public import TauCeti.CategoryTheory.Exact.Frobenius

/-!
# The Frobenius category of Gorenstein-projective objects

Let `C` be an abelian category. Its Gorenstein-projective objects are closed under extensions
(`CategoryTheory.isGorensteinProjective_isExtensionClosed`), so they inherit the exact structure of
`C`. This exact structure is Frobenius: complete resolutions give conflations
`Z⁻¹ ↪ P⁻¹ ↠ Z⁰` and `Z⁰ ↪ P⁰ ↠ Z¹` with projective middle terms, and both the relative
projectives and the relative injectives are exactly the objects which are projective in `C`.
Projectives of `C` are relatively injective because a Gorenstein-projective object has no
extensions by them.

Hence the stable category of Gorenstein-projective objects, the quotient by the morphisms
factoring through projectives, is triangulated by Happel's theorem
(`TauCeti.ExactStructure.IsFrobenius.stablePretriangulated` and
`TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`). No hypothesis on `C` beyond being
abelian is needed; in particular `C` need not have enough projectives.

## Attribution

The construction adapts the Frobenius exact structure on finitely generated Gorenstein-projective
modules over a Noetherian ring in `TauCeti/Algebra/Homology/GorensteinProjective/Frobenius.lean`
(`TauCeti.GorensteinProjectiveModuleCat.exactStructure_isFrobenius`): the full subcategory with its
inherited exact structure, the conflations cut out of a complete resolution, and the
identification of the relative projectives and injectives with the projective objects, here
from totally acyclic complexes in an arbitrary abelian category.

## Main definitions

* `CategoryTheory.GorensteinProjective C`: the full subcategory of Gorenstein-projective objects.
* `CategoryTheory.GorensteinProjective.exactStructure C`: its exact structure inherited from `C`.

## Main results

* `CategoryTheory.GorensteinProjective.exactStructure_isProjective_iff` and
  `CategoryTheory.GorensteinProjective.exactStructure_isInjective_iff`: the relative projectives
  and the relative injectives are the projective objects of `C`.
* `CategoryTheory.GorensteinProjective.exactStructure_isFrobenius`: the exact structure is
  Frobenius.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TauCeti

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The full subcategory of Gorenstein-projective objects of an abelian category. -/
abbrev GorensteinProjective := (isGorensteinProjective C).FullSubcategory

namespace GorensteinProjective

/-- The exact structure on Gorenstein-projective objects induced by the abelian exact structure
of `C`. -/
noncomputable def exactStructure : ExactStructure (GorensteinProjective C) :=
  (ExactStructure.abelian C).fullSubcategory _ isGorensteinProjective_isExtensionClosed

variable {C}

/-- The conflations of Gorenstein-projective objects are the short exact sequences of `C`. -/
@[simp]
theorem exactStructure_conflation_iff (S : ShortComplex (GorensteinProjective C)) :
    (exactStructure C).Conflation S ↔ (S.map (isGorensteinProjective C).ι).ShortExact := by
  rw [exactStructure, ExactStructure.fullSubcategory_conflation_iff,
    ExactStructure.abelian_conflation]

/-- A complete resolution gives a conflation `Z⁻¹ ↪ P⁻¹ ↠ X` with projective middle term. -/
private theorem exists_projective_sequence (X : GorensteinProjective C) :
    ∃ (K P : GorensteinProjective C) (i : K ⟶ P) (p : P ⟶ X) (h : i ≫ p = 0),
      (exactStructure C).Conflation (ShortComplex.mk i p h) ∧ Projective P.obj := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := (isGorensteinProjective_iff _).1 X.property
  have := hQ.projective (-1)
  let K : GorensteinProjective C := ⟨Q.cycles (-1), hQ.isGorensteinProjective_cycles _⟩
  let P : GorensteinProjective C := ⟨Q.X (-1), isGorensteinProjective_of_projective _⟩
  let i : K ⟶ P := ObjectProperty.homMk (Q.iCycles (-1))
  let p : P ⟶ X := ObjectProperty.homMk (Q.toCycles (-1) 0 ≫ e.hom)
  have h : i ≫ p = 0 := ObjectProperty.hom_ext _
    (by simp [i, p, Q.iCycles_toCycles_assoc])
  refine ⟨K, P, i, p, h, ?_, inferInstance⟩
  rw [exactStructure_conflation_iff]
  refine ShortComplex.shortExact_of_iso ?_
    (Q.cyclesShortComplex_shortExact_of_iso (i := -1) (by simp) (hQ.acyclic 0) (Iso.refl _) e)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [i]) (by simp [p])

/-- A complete resolution gives a conflation `X ↪ P⁰ ↠ Z¹` with projective middle term. -/
private theorem exists_injective_sequence (X : GorensteinProjective C) :
    ∃ (I K : GorensteinProjective C) (i : X ⟶ I) (p : I ⟶ K) (h : i ≫ p = 0),
      (exactStructure C).Conflation (ShortComplex.mk i p h) ∧ Projective I.obj := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := (isGorensteinProjective_iff _).1 X.property
  have := hQ.projective 0
  let I : GorensteinProjective C := ⟨Q.X 0, isGorensteinProjective_of_projective _⟩
  let K : GorensteinProjective C := ⟨Q.cycles 1, hQ.isGorensteinProjective_cycles _⟩
  let i : X ⟶ I := ObjectProperty.homMk (e.inv ≫ Q.iCycles 0)
  let p : I ⟶ K := ObjectProperty.homMk (Q.toCycles 0 1)
  have h : i ≫ p = 0 := ObjectProperty.hom_ext _
    (by simp [i, p, Q.iCycles_toCycles])
  refine ⟨I, K, i, p, h, ?_, inferInstance⟩
  rw [exactStructure_conflation_iff]
  refine ShortComplex.shortExact_of_iso ?_
    (Q.cyclesShortComplex_shortExact_of_iso (i := 0) (by simp) (hQ.acyclic 1) e.symm (Iso.refl _))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [i]) (by simp [p])

/-- The relative projectives among Gorenstein-projective objects are the projective objects of
`C`. -/
@[simp]
theorem exactStructure_isProjective_iff (X : GorensteinProjective C) :
    (exactStructure C).isProjective X ↔ Projective X.obj := by
  constructor
  · intro hX
    obtain ⟨K, P, i, p, h, hS, hP⟩ := exists_projective_sequence X
    let s := (exactStructure C).splittingOfProjective hS hX
    let r : Retract X.obj P.obj :=
      { i := s.s.hom
        r := p.hom
        retract := by simpa using (isGorensteinProjective C).ι.congr_map s.s_g }
    exact r.projective
  · intro hX
    exact ExactStructure.isProjective_fullSubcategory_of_isProjective
      isGorensteinProjective_isExtensionClosed X
      ((ExactStructure.abelian_isProjective_iff X.obj).mpr hX)

/-- The relative injectives among Gorenstein-projective objects are also the projective objects of
`C`, not the injective ones. -/
@[simp]
theorem exactStructure_isInjective_iff (X : GorensteinProjective C) :
    (exactStructure C).isInjective X ↔ Projective X.obj := by
  constructor
  · intro hX
    obtain ⟨I, K, i, p, h, hS, hI⟩ := exists_injective_sequence X
    let s := (exactStructure C).splittingOfInjective hS hX
    let r : Retract X.obj I.obj :=
      { i := i.hom
        r := s.r.hom
        retract := by simpa using (isGorensteinProjective C).ι.congr_map s.f_r }
    exact r.projective
  · intro hX
    let := HasExt.standard C
    rw [ExactStructure.isInjective_iff]
    intro Y Z i hi f
    obtain ⟨K, p, h, hS⟩ := (ConflationClass.isInflation_iff _ _).mp hi
    obtain ⟨g, hg⟩ := ((exactStructure_conflation_iff _).mp hS).exists_f_comp_eq_of_ext_eq_zero
      (fun x ↦ K.property.ext_eq_zero X.obj x) f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

/-- Complete resolutions provide enough relative projectives. -/
theorem exactStructure_enoughProjectives : (exactStructure C).EnoughProjectives where
  presentation X := by
    obtain ⟨K, P, i, p, h, hS, hP⟩ := exists_projective_sequence X
    exact ⟨{ K := K
             P := P
             i := i
             p := p
             zero := h
             conflation := hS
             isProjective := (exactStructure_isProjective_iff P).mpr hP }⟩

/-- Complete resolutions provide enough relative injectives. -/
theorem exactStructure_enoughInjectives : (exactStructure C).EnoughInjectives where
  presentation X := by
    obtain ⟨I, K, i, p, h, hS, hI⟩ := exists_injective_sequence X
    exact ⟨{ I := I
             K := K
             i := i
             p := p
             zero := h
             conflation := hS
             isInjective := (exactStructure_isInjective_iff I).mpr hI }⟩

/-- **Gorenstein-projective objects form a Frobenius exact category**, whose projective-injective
objects are the projective objects of `C`. -/
theorem exactStructure_isFrobenius : (exactStructure C).IsFrobenius where
  enoughProjectives := exactStructure_enoughProjectives
  enoughInjectives := exactStructure_enoughInjectives
  projective_iff_injective X := by
    rw [exactStructure_isProjective_iff, exactStructure_isInjective_iff]

end GorensteinProjective

end CategoryTheory
