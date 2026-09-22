/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Graded.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Graded exact structures on full subcategories

An extension-closed full additive subcategory of an exact category — explicitly, one containing a
zero object and closed under binary products — inherits an exact structure. If the ambient
category is graded and the object property is moreover stable under the grading shift, that shift
restricts to an autoequivalence of the full subcategory and makes its induced exact structure
graded.

Shift stability is the equality `P.inverseImage E.shift.functor = P`, that is, an object lies in
`P` if and only if its shift does; one-way closure under the forward shift is not assumed. That
equality, together with repleteness of the object property and the unit and counit isomorphisms,
determines the matching invariance under the inverse shift. The restricted equivalence is
Mathlib's `CategoryTheory.Equivalence.congrFullSubcategory`; its functor and inverse preserve
conflations because the ambient shift and inverse shift do.

This construction is the bridge between objectwise graded invariants on extension-closed classes
and the Laurent-module Grothendieck groups of those classes. In particular, it lets a graded
Ext-Euler characteristic descend to the graded Grothendieck groups of selected subcategories.

## Main definitions

* `TauCeti.GradedExactStructure.fullSubcategoryShift`: the grading-shift autoequivalence restricted
  to a shift-stable full subcategory.
* `TauCeti.GradedExactStructure.fullSubcategory`: the induced graded exact structure.
* `TauCeti.GradedConflationExact.ι`: the graded conflation-exact inclusion into the ambient
  category.
* `TauCeti.GradedConflationExact.ιOfLE`: the graded conflation-exact inclusion between two nested
  shift-stable full subcategories.
* `TauCeti.GradedExactStructure.liftCommShift`: the restriction to full subcategories of a
  shift-commutation isomorphism `{1} ⋙ F ≅ F`.

## Main results

* `TauCeti.GradedExactStructure.isConflationExact_lift`: a conflation-exact functor carrying a
  shift-stable extension-closed property into an extension-closed one restricts to a
  conflation-exact functor of the induced structures.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for grading shifts on exact
  categories and their graded Grothendieck groups.
* [TauCetiProject/TauCeti#5721](https://github.com/TauCetiProject/TauCeti/pull/5721), whose retired,
  unmerged formalization this construction adapts.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
variable (E : GradedExactStructure C) (P : ObjectProperty C)

section Shift

variable [P.IsClosedUnderIsomorphisms]

/-- The grading shift restricted to a full subcategory stable under that shift.

The equation `P.inverseImage E.shift.functor = P` states exactly that an object belongs to `P`
if and only if its shift does. Mathlib's full-subcategory restriction of an equivalence then
uses the ambient inverse shift as its inverse. -/
noncomputable def fullSubcategoryShift (hshift : P.inverseImage E.shift.functor = P) :
    P.FullSubcategory ≌ P.FullSubcategory :=
  E.shift.congrFullSubcategory hshift

/-- The inclusion of the full subcategory intertwines its restricted shift with the ambient
shift. -/
def fullSubcategoryShiftFunctorCompιIso
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategoryShift E P hshift).functor ⋙ P.ι ≅ P.ι ⋙ E.shift.functor := by
  rw [fullSubcategoryShift]
  exact P.liftCompιIso _ _

/-- The inclusion of the full subcategory also intertwines the inverse restricted shift with the
ambient inverse shift. -/
def fullSubcategoryShiftInverseCompιIso
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategoryShift E P hshift).inverse ⋙ P.ι ≅ P.ι ⋙ E.shift.inverse := by
  rw [fullSubcategoryShift]
  exact P.liftCompιIso _ _

end Shift

section FullSubcategory

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

private noncomputable instance fullSubcategoryShiftFunctorAdditive
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategoryShift E P hshift).functor.Additive := by
  have : ((fullSubcategoryShift E P hshift).functor ⋙ P.ι).Additive :=
    Functor.additive_of_iso (fullSubcategoryShiftFunctorCompιIso E P hshift).symm
  exact Functor.additive_of_comp_faithful _ P.ι

private theorem fullSubcategoryShift_exact
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (E.toExactStructure.fullSubcategory P hP).IsConflationExact
      (E.toExactStructure.fullSubcategory P hP) (fullSubcategoryShift E P hshift).functor where
  map_conflation {S} hS := by
    rw [ExactStructure.fullSubcategory_conflation_iff] at hS ⊢
    rw [← ShortComplex.map_comp] at ⊢
    exact E.toExactStructure.conflation_of_iso
      (S.mapNatIso (fullSubcategoryShiftFunctorCompιIso E P hshift))
      (E.shift_exact.map_conflation hS)

private theorem fullSubcategoryShift_inverse_exact
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (E.toExactStructure.fullSubcategory P hP).IsConflationExact
      (E.toExactStructure.fullSubcategory P hP) (fullSubcategoryShift E P hshift).inverse where
  map_conflation {S} hS := by
    rw [ExactStructure.fullSubcategory_conflation_iff] at hS ⊢
    rw [← ShortComplex.map_comp] at ⊢
    exact E.toExactStructure.conflation_of_iso
      (S.mapNatIso (fullSubcategoryShiftInverseCompιIso E P hshift))
      (E.shift_inverse_exact.map_conflation hS)

/-- The graded exact structure induced on a shift-stable, extension-closed full additive
subcategory, the additivity being required in the explicit form of containing a zero object and
being closed under binary products.

Its exact structure is the one induced from the ambient exact category, and its grading shift is
the restriction of the ambient shift. -/
noncomputable def fullSubcategory
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    GradedExactStructure P.FullSubcategory where
  toExactStructure := E.toExactStructure.fullSubcategory P hP
  shift := fullSubcategoryShift E P hshift
  shift_exact := fullSubcategoryShift_exact E P hP hshift
  shift_inverse_exact := fullSubcategoryShift_inverse_exact E P hP hshift

/-- The underlying exact structure on the induced graded exact structure is the full-subcategory
exact structure. -/
@[simp]
theorem fullSubcategory_toExactStructure
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategory E P hP hshift).toExactStructure =
      E.toExactStructure.fullSubcategory P hP :=
  by rw [fullSubcategory]

/-- The shift on the induced graded exact structure is the restricted ambient shift. -/
@[simp]
theorem fullSubcategory_shift
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategory E P hP hshift).shift = fullSubcategoryShift E P hshift :=
  by rw [fullSubcategory]

/-- A short complex of the subcategory is a conflation of the induced graded exact structure
exactly when its image in the ambient category is a conflation. -/
theorem fullSubcategory_conflation_iff
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) (S : ShortComplex P.FullSubcategory) :
    (fullSubcategory E P hP hshift).toExactStructure.Conflation S ↔
      E.toExactStructure.Conflation (S.map P.ι) := by
  rw [fullSubcategory_toExactStructure, ExactStructure.fullSubcategory_conflation_iff]

section Lift

variable {D : Type u'} [Category.{v'} D] {Q : ObjectProperty D} {F : C ⥤ D}
  (hP : E.toExactStructure.IsExtensionClosed P)
  (hshift : P.inverseImage E.shift.functor = P)
  (hPQ : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- **The restriction of a shift-commutation isomorphism to full subcategories.** A functor `F`
out of a graded exact category with `{1} ⋙ F ≅ F` restricts, on a shift-stable full subcategory
of its source and a full subcategory of its target containing the image, to a functor with the
same commutation isomorphism: the restricted shift is the ambient one.

This is the datum which, together with conflation-exactness, forgets the grading on the
subcategory in `TauCeti.LaurentK0.forgetGrading`. -/
noncomputable def liftCommShift (comm : E.shift.functor ⋙ F ≅ F) :
    (E.fullSubcategory P hP hshift).shift.functor ⋙ Q.lift (P.ι ⋙ F) hPQ ≅
      Q.lift (P.ι ⋙ F) hPQ := by
  rw [fullSubcategory_shift]
  exact (Q.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Q.liftCompιIso (P.ι ⋙ F) hPQ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.fullSubcategoryShiftFunctorCompιIso P hshift) F ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.ι comm ≪≫
      (Q.liftCompιIso (P.ι ⋙ F) hPQ).symm)

/-- A conflation-exact functor carrying a shift-stable extension-closed property `P` into an
extension-closed property `Q` restricts to a conflation-exact functor from the graded exact
structure induced on `P` to the exact structure induced on `Q`. -/
theorem isConflationExact_lift [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
    [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts] [F.Additive] {E' : ExactStructure D}
    (hQ : E'.IsExtensionClosed Q) (hF : E.toExactStructure.IsConflationExact E' F) :
    (E.fullSubcategory P hP hshift).toExactStructure.IsConflationExact
      (E'.fullSubcategory Q hQ) (Q.lift (P.ι ⋙ F) hPQ) := by
  rw [fullSubcategory_toExactStructure]
  exact E.toExactStructure.isConflationExact_lift hP hQ F hF hPQ

end Lift

end FullSubcategory

end GradedExactStructure

namespace GradedConflationExact

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
variable (E : GradedExactStructure C) (P : ObjectProperty C)
variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

/-- The inclusion of a shift-stable, extension-closed full additive subcategory — one containing a
zero object and closed under binary products — is graded conflation-exact. Its commutation
isomorphism is the canonical comparison between the restricted shift followed by inclusion and the
ambient shift. -/
def ι
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    GradedConflationExact (E.fullSubcategory P hP hshift) E P.ι where
  isConflationExact := ExactStructure.isConflationExact_ι hP
  commShift := by
    unfold GradedExactStructure.fullSubcategory
    exact E.fullSubcategoryShiftFunctorCompιIso P hshift

/-- The shift-commutation isomorphism of the graded conflation-exact full-subcategory inclusion. -/
@[simp]
theorem ι_commShift
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    HEq (ι E P hP hshift).commShift
      (E.fullSubcategoryShiftFunctorCompιIso P hshift) :=
  (HEq.rfl)

/-- The inclusion associated to an implication `P ≤ Q` between two shift-stable, extension-closed
full additive subcategories is graded conflation-exact for their induced graded exact
structures. Its commutation isomorphism is the one whose image under the inclusion of `Q` is the
composite of the two restricted-shift comparisons with the ambient shift. -/
noncomputable def ιOfLE {Q : ObjectProperty C} [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]
    (hP : E.toExactStructure.IsExtensionClosed P) (hQ : E.toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage E.shift.functor = P) (hQshift : Q.inverseImage E.shift.functor = Q)
    (h : P ≤ Q) :
    GradedConflationExact (E.fullSubcategory P hP hPshift) (E.fullSubcategory Q hQ hQshift)
      (ObjectProperty.ιOfLE h) where
  isConflationExact := ⟨fun {S} hS => by
    rw [GradedExactStructure.fullSubcategory_conflation_iff] at hS ⊢
    exact hS⟩
  commShift := by
    have : Q.IsClosedUnderIsomorphisms := ObjectProperty.isClosedUnderIsomorphisms_of_containsZero Q
    rw [GradedExactStructure.fullSubcategory_shift, GradedExactStructure.fullSubcategory_shift]
    exact (Q.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (ObjectProperty.ιOfLECompιIso h) ≪≫
        E.fullSubcategoryShiftFunctorCompιIso P hPshift ≪≫
        Functor.isoWhiskerRight (ObjectProperty.ιOfLECompιIso h).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (E.fullSubcategoryShiftFunctorCompιIso Q hQshift).symm ≪≫
        (Functor.associator _ _ _).symm)

end GradedConflationExact

end TauCeti
