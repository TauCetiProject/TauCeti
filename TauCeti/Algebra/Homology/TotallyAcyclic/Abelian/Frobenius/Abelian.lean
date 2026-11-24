/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Extension
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Frobenius.Basic
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
  `Gproj C ⥤ C` as an equivalence, when the abelian exact structure of `C` is Frobenius.
* `CategoryTheory.GorensteinProjective.stableEquivalenceOfIsFrobenius`: the induced equivalence of
  stable categories.

## Main results

* `CategoryTheory.isGorensteinProjective_of_isFrobenius`: in a Frobenius abelian category, every
  object is Gorenstein-projective.
* `CategoryTheory.GorensteinProjective.isConflationExact_equivalenceOfIsFrobenius_functor` and
  `isConflationExact_equivalenceOfIsFrobenius_inverse`: the equivalence and its inverse preserve
  conflations.
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
/-- **In a Frobenius abelian category every object is Gorenstein-projective**: if the abelian
exact structure of `C` is Frobenius, every object of `C` is Gorenstein-projective. -/
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

/-- When the abelian exact structure of `C` is Frobenius, the inclusion of the Gorenstein-projective
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

/-- The inclusion of the Gorenstein-projective objects, as an equivalence, preserves
conflations. -/
theorem isConflationExact_equivalenceOfIsFrobenius_functor :
    (exactStructure C).IsConflationExact (ExactStructure.abelian C)
      (equivalenceOfIsFrobenius hE).functor :=
  -- The functor of the equivalence is the inclusion `ι` (`equivalenceOfIsFrobenius_functor`).
  ⟨fun hS ↦ (ExactStructure.abelian_conflation _).mpr ((exactStructure_conflation_iff _).mp hS)⟩

/-- The inverse of the inclusion of the Gorenstein-projective objects preserves conflations. -/
theorem isConflationExact_equivalenceOfIsFrobenius_inverse :
    (ExactStructure.abelian C).IsConflationExact (exactStructure C)
      (equivalenceOfIsFrobenius hE).inverse :=
  -- `(S.map inverse).map ι` is `S.map (inverse ⋙ functor)` (`ShortComplex.map_comp`), which is
  -- isomorphic to `S.map (𝟭 C) = S` (`ShortComplex.map_id`) through the counit.
  ⟨fun {S} hS ↦ (exactStructure_conflation_iff _).mpr (ShortComplex.shortExact_of_iso
    (S.mapNatIso (equivalenceOfIsFrobenius hE).counitIso.symm)
    ((ExactStructure.abelian_conflation S).mp hS))⟩

/-- The inclusion of the Gorenstein-projective objects, as an equivalence, preserves conflations
and projective-injective objects. -/
theorem stableConflationExact_equivalenceOfIsFrobenius_functor :
    StableConflationExact (exactStructure C) (ExactStructure.abelian C)
      (equivalenceOfIsFrobenius hE).functor :=
  (isConflationExact_equivalenceOfIsFrobenius_functor hE).stableConflationExact_of_equivalence
    (isConflationExact_equivalenceOfIsFrobenius_inverse hE)

/-- The inverse of the inclusion of the Gorenstein-projective objects preserves conflations and
projective-injective objects. -/
theorem stableConflationExact_equivalenceOfIsFrobenius_inverse :
    StableConflationExact (ExactStructure.abelian C) (exactStructure C)
      (equivalenceOfIsFrobenius hE).inverse :=
  have : (equivalenceOfIsFrobenius hE).symm.functor.Additive :=
    inferInstanceAs (equivalenceOfIsFrobenius hE).inverse.Additive
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := (equivalenceOfIsFrobenius hE).symm)
    (isConflationExact_equivalenceOfIsFrobenius_inverse hE)
    (isConflationExact_equivalenceOfIsFrobenius_functor hE)

/-- **The stable category of a Frobenius abelian category is the stable category of its
Gorenstein-projective objects.** When the abelian exact structure of `C` is Frobenius, the
inclusion of the Gorenstein-projective objects induces an equivalence of stable categories. -/
noncomputable abbrev stableEquivalenceOfIsFrobenius :
    (exactStructure C).ProjectiveStableCategory ≌
      (ExactStructure.abelian C).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (equivalenceOfIsFrobenius hE)
    (stableConflationExact_equivalenceOfIsFrobenius_functor hE)
    (stableConflationExact_equivalenceOfIsFrobenius_inverse hE) (hG) hE

instance : (stableEquivalenceOfIsFrobenius hE).functor.Additive := by
  rw [StableConflationExact.stableEquivalence_functor, StableConflationExact.stableFunctor_eq_map]
  infer_instance

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
    (stableEquivalenceOfIsFrobenius hE).IsTriangulated :=
  StableConflationExact.stableEquivalenceIsTriangulated _ _ _ _

end GorensteinProjective

end CategoryTheory
