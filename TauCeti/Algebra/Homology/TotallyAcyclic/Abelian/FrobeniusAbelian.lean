/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Extension
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Frobenius
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Gorenstein-projective objects of a Frobenius abelian category

Let `C` be an abelian category whose abelian exact structure is Frobenius: it has enough
projectives and enough injectives, and the projective objects are the injective objects. The module
category of a finite-dimensional algebra which is self-injective on both sides is the main example
(`FGModuleCat.abelian_isFrobenius`).

Then every object of `C` is Gorenstein-projective
(`CategoryTheory.isGorensteinProjective_of_isFrobenius`): splicing a complete resolution gives an
acyclic complex of projectives, and it is totally acyclic because its cycles have no extensions by
the projective objects, which are injective. Hence the inclusion of the Gorenstein-projective
objects is an equivalence of exact categories, and induces a triangle equivalence between the
stable category of Gorenstein-projective objects and the stable category of `C`, both triangulated
by Happel's theorem (`CategoryTheory.GorensteinProjective.stableEquivalenceOfIsFrobenius`). Through
it, Buchweitz's theorem for the Gorenstein-projective objects becomes a statement about the stable
category of `C` itself.

## Main definitions

* `CategoryTheory.GorensteinProjective.equivalenceOfIsFrobenius`: the inclusion
  `Gproj C ⥤ C` as an equivalence, when every object is Gorenstein-projective.
* `CategoryTheory.GorensteinProjective.stableEquivalenceOfIsFrobenius`: the induced equivalence of
  stable categories.

## Main results

* `CategoryTheory.isGorensteinProjective_of_isFrobenius`: in a Frobenius abelian category, every
  object is Gorenstein-projective.
* `CategoryTheory.GorensteinProjective.stableEquivalenceOfIsFrobenius_isTriangulated`: the stable
  equivalence is a triangle equivalence for Happel's triangulations.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TauCeti

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  (hE : (ExactStructure.abelian C).IsFrobenius)

include hE in
/-- **In a Frobenius abelian category every object is Gorenstein-projective.** If the abelian exact
structure of `C` is Frobenius, the spliced complete resolution of an object is a totally acyclic
complex of projectives: its cycles have no extensions by projective objects, since these are
injective. -/
theorem isGorensteinProjective_of_isFrobenius (X : C) : isGorensteinProjective C X := by
  let := HasExt.standard C
  let r := hE.completeResolution X
  have hS (n : ℤ) : (r.shortComplex n).ShortExact :=
    (ExactStructure.abelian_conflation _).mp (r.conflation n)
  have hproj (n : ℤ) : Projective (r.shortComplex n).X₂ :=
    (ExactStructure.abelian_isProjective_iff _).mp (r.isProjective_X n)
  refine (isGorensteinProjective_iff X).2 ⟨_, CochainComplex.isTotallyAcyclicProjective_splice
    (fun n ↦ r.shortComplex n) (fun _ ↦ Iso.refl _) hS hproj fun n Q _ x ↦ ?_,
    ⟨(CochainComplex.spliceCyclesIso _ _ hS 0).symm ≪≫ hE.completeResolutionIso X⟩⟩
  have : Injective Q := (ExactStructure.abelian_isInjective_iff Q).mp
    ((hE.projective_iff_injective Q).mp ((ExactStructure.abelian_isProjective_iff Q).mpr ‹_›))
  exact Ext.eq_zero_of_injective x

namespace GorensteinProjective

/-- The Frobenius exact structure on the Gorenstein-projective objects. -/
local notation "hG" => (exactStructure_isFrobenius (C := C))

/-- When every object of `C` is Gorenstein-projective, the inclusion of the Gorenstein-projective
objects is an equivalence of categories. -/
@[expose, simps]
noncomputable def equivalenceOfIsFrobenius : GorensteinProjective C ≌ C where
  functor := (isGorensteinProjective C).ι
  inverse := (isGorensteinProjective C).lift (𝟭 C) (isGorensteinProjective_of_isFrobenius hE)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance : (equivalenceOfIsFrobenius hE).functor.Additive := by
  dsimp [equivalenceOfIsFrobenius]
  infer_instance

instance : (equivalenceOfIsFrobenius hE).inverse.Additive := by
  dsimp [equivalenceOfIsFrobenius]
  infer_instance

/-- The inclusion of the Gorenstein-projective objects, as an equivalence, preserves conflations
and projective-injective objects. -/
theorem stableConflationExact_equivalenceOfIsFrobenius_functor :
    StableConflationExact (exactStructure C) (ExactStructure.abelian C)
      (equivalenceOfIsFrobenius hE).functor :=
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    ⟨fun hS ↦ (ExactStructure.abelian_conflation _).mpr
      ((exactStructure_conflation_iff _).mp hS)⟩
    ⟨fun {S} hS ↦ (exactStructure_conflation_iff _).mpr
      ((ExactStructure.abelian_conflation S).mp hS)⟩

/-- The inverse of the inclusion of the Gorenstein-projective objects preserves conflations and
projective-injective objects. -/
theorem stableConflationExact_equivalenceOfIsFrobenius_inverse :
    StableConflationExact (ExactStructure.abelian C) (exactStructure C)
      (equivalenceOfIsFrobenius hE).inverse :=
  have : (equivalenceOfIsFrobenius hE).symm.functor.Additive :=
    inferInstanceAs (equivalenceOfIsFrobenius hE).inverse.Additive
  have : (equivalenceOfIsFrobenius hE).symm.inverse.Additive :=
    inferInstanceAs (equivalenceOfIsFrobenius hE).functor.Additive
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := (equivalenceOfIsFrobenius hE).symm)
    ⟨fun {S} hS ↦ (exactStructure_conflation_iff _).mpr
      ((ExactStructure.abelian_conflation S).mp hS)⟩
    ⟨fun hS ↦ (ExactStructure.abelian_conflation _).mpr
      ((exactStructure_conflation_iff _).mp hS)⟩

/-- **The stable category of a Frobenius abelian category is the stable category of its
Gorenstein-projective objects.** When the abelian exact structure of `C` is Frobenius, the
inclusion of the Gorenstein-projective objects induces an equivalence of stable categories. -/
noncomputable abbrev stableEquivalenceOfIsFrobenius :
    (exactStructure C).ProjectiveStableCategory ≌
      (ExactStructure.abelian C).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (equivalenceOfIsFrobenius hE)
    (stableConflationExact_equivalenceOfIsFrobenius_functor hE)
    (stableConflationExact_equivalenceOfIsFrobenius_inverse hE) (hG) hE

/-- The stable equivalence `stableEquivalenceOfIsFrobenius` is a triangle equivalence for Happel's
triangulations of the two stable categories. -/
theorem stableEquivalenceOfIsFrobenius_isTriangulated :
    letI := (hG).stableHasShift
    letI := hE.stableHasShift
    letI := (hG).stableShiftFunctor_additive
    letI := hE.stableShiftFunctor_additive
    letI := (hG).stablePretriangulated
    letI := hE.stablePretriangulated
    letI := StableConflationExact.stableEquivalenceFunctorCommShift
      (stableConflationExact_equivalenceOfIsFrobenius_functor hE)
      (stableConflationExact_equivalenceOfIsFrobenius_inverse hE) (hG) hE
    letI := StableConflationExact.stableEquivalenceInverseCommShift
      (stableConflationExact_equivalenceOfIsFrobenius_functor hE)
      (stableConflationExact_equivalenceOfIsFrobenius_inverse hE) (hG) hE
    letI := (stableEquivalenceOfIsFrobenius hE).commShift_of_functor ℤ
    (stableEquivalenceOfIsFrobenius hE).IsTriangulated :=
  StableConflationExact.stableEquivalenceIsTriangulated _ _ _ _

end GorensteinProjective

end CategoryTheory
