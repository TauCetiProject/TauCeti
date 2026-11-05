/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.Basic
public import TauCeti.CategoryTheory.Exact.Product

/-!
# Products of graded exact categories

The product of two graded exact categories has componentwise conflations and componentwise
internal shift. Both projections, both inclusions obtained by inserting a zero object, and
products of graded conflation-exact functors commute with this shift. These constructions
allow the product decomposition of exact Grothendieck groups to retain its Laurent action.

The zero-section commutation isomorphisms use preservation of the zero object by the shift;
the shift need not fix the chosen zero object definitionally.

## References

* Theo Bühler, *Exact categories*, Section 5, for conflation-exact functors.
* Charles A. Weibel, *The K-book*, Chapter II, Sections 6–7, for exact Grothendieck groups.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' v₁ v₂ u u' u₁ u₂

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]

/-- The componentwise graded exact structure on a product: conflations and the internal shift
are taken separately in each factor. -/
noncomputable def prod (E : GradedExactStructure C) (E' : GradedExactStructure D) :
    GradedExactStructure (C × D) where
  toExactStructure := E.toExactStructure.prod E'.toExactStructure
  shift := E.shift.prod E'.shift
  shift_additive := inferInstanceAs (E.shift.functor.prod E'.shift.functor).Additive
  shift_exact := E.shift_exact.prod E'.shift_exact
  shift_inverse_exact := E.shift_inverse_exact.prod E'.shift_inverse_exact

/-- Forgetting the grading of a product gives the product exact structure. -/
@[simp]
theorem prod_toExactStructure (E : GradedExactStructure C) (E' : GradedExactStructure D) :
    (E.prod E').toExactStructure = E.toExactStructure.prod E'.toExactStructure :=
  (rfl)

/-- The internal shift on a product is the product of the two internal shifts. -/
@[simp]
theorem prod_shift (E : GradedExactStructure C) (E' : GradedExactStructure D) :
    (E.prod E').shift = E.shift.prod E'.shift :=
  (rfl)

end GradedExactStructure

namespace GradedConflationExact

section Projections

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
  (E : GradedExactStructure C) (E' : GradedExactStructure D)

/-- The first projection is graded conflation-exact for the componentwise shift. -/
noncomputable def fst : GradedConflationExact (E.prod E') E (CategoryTheory.Prod.fst C D) where
  isConflationExact := ExactStructure.isConflationExact_fst_prod _ _
  commShift := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by simp [GradedExactStructure.prod])

/-- The second projection is graded conflation-exact for the componentwise shift. -/
noncomputable def snd : GradedConflationExact (E.prod E') E' (CategoryTheory.Prod.snd C D) where
  isConflationExact := ExactStructure.isConflationExact_snd_prod _ _
  commShift := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by simp [GradedExactStructure.prod])

/-- Inserting a zero object in the second coordinate is graded conflation-exact. -/
noncomputable def sectL :
    GradedConflationExact E (E.prod E') (CategoryTheory.Prod.sectL C (0 : D)) where
  isConflationExact := ExactStructure.isConflationExact_sectL_prod _ _
  commShift := NatIso.ofComponents
    (fun X => (Iso.refl (E.shift.functor.obj X)).prod (Functor.mapZeroObject E'.shift.functor).symm)
    (fun _ => CategoryTheory.Prod.hom_ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((isZero_zero D).eq_of_src _ _))

/-- Inserting a zero object in the first coordinate is graded conflation-exact. -/
noncomputable def sectR :
    GradedConflationExact E' (E.prod E') (CategoryTheory.Prod.sectR (0 : C) D) where
  isConflationExact := ExactStructure.isConflationExact_sectR_prod _ _
  commShift := NatIso.ofComponents
    (fun X => (Functor.mapZeroObject E.shift.functor).symm.prod (Iso.refl (E'.shift.functor.obj X)))
    (fun _ => CategoryTheory.Prod.hom_ext
      ((isZero_zero C).eq_of_src _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm))

end Projections

section Functors

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
  {C' : Type u₁} [Category.{v₁} C'] [Preadditive C'] [HasZeroObject C']
  [HasBinaryBiproducts C']
  {D' : Type u₂} [Category.{v₂} D'] [Preadditive D'] [HasZeroObject D']
  [HasBinaryBiproducts D']
  {E : GradedExactStructure C} {E' : GradedExactStructure D}
  {K : GradedExactStructure C'} {K' : GradedExactStructure D'}
  {F : C ⥤ C'} {G : D ⥤ D'} [F.Additive] [G.Additive]

/-- Products of graded conflation-exact functors are graded conflation-exact, with the product
of their shift-commutation isomorphisms. -/
def prod (hF : GradedConflationExact E K F) (hG : GradedConflationExact E' K' G) :
    GradedConflationExact (E.prod E') (K.prod K') (F.prod G) where
  isConflationExact := hF.isConflationExact.prod hG.isConflationExact
  commShift := NatIso.prod hF.commShift hG.commShift

end Functors

end GradedConflationExact

end TauCeti
