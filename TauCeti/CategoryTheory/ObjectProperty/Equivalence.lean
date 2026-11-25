/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Equivalences of full subcategories

This file supplements Mathlib's `Mathlib.CategoryTheory.ObjectProperty.Equivalence` with API for
`CategoryTheory.Equivalence.congrFullSubcategory`, the equivalence between full subcategories of
corresponding properties induced by an equivalence of ambient categories. The restricted functors
act on underlying objects and morphisms as the ambient ones, by Mathlib's `@[simps]` projections
`CategoryTheory.Equivalence.congrFullSubcategory_functor` and
`CategoryTheory.Equivalence.congrFullSubcategory_inverse` together with
`CategoryTheory.ObjectProperty.lift`.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_eq_of_iso`: an isomorphism-invariant property has
  the same inverse image along isomorphic functors.
* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it, as
  `congrFullSubcategory` asks of the transported property `P.inverseImage e.inverse`.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_additive` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_additive`: if the ambient functor,
  respectively the ambient inverse, of an equivalence is additive, then so is its restriction to
  corresponding full subcategories.
-/

public section

namespace CategoryTheory

namespace ObjectProperty

/-- An isomorphism-invariant property has the same inverse image along isomorphic functors. -/
theorem inverseImage_eq_of_iso {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms] {F G : C ⥤ D} (α : F ≅ G) :
    P.inverseImage F = P.inverseImage G := by
  ext X
  exact P.prop_iff_of_iso (α.app X)

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. This is
`CategoryTheory.ObjectProperty.inverseImage_eq_of_iso` for the unit of the equivalence. -/
@[simp]
theorem inverseImage_functor_inverseImage_inverse {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P :=
  P.inverseImage_eq_of_iso e.unitIso.symm

end ObjectProperty

namespace Equivalence

/-- If the functor of an equivalence is additive, then so is its restriction to corresponding full
subcategories. -/
instance congrFullSubcategory_functor_additive {C D : Type*} [Category* C] [Preadditive C]
    [Category* D] [Preadditive D] {P : ObjectProperty C} {Q : ObjectProperty D}
    [Q.IsClosedUnderIsomorphisms] (e : C ≌ D) [e.functor.Additive]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).functor.Additive := by
  rw [congrFullSubcategory_functor]
  infer_instance

/-- If the inverse of an equivalence is additive, then so is its restriction to corresponding full
subcategories. Mathlib's `CategoryTheory.Equivalence.inverse_additive` derives this only from
additivity of the forward functor, so it does not apply under the hypothesis
`[e.inverse.Additive]` alone. -/
instance congrFullSubcategory_inverse_additive {C D : Type*} [Category* C] [Preadditive C]
    [Category* D] [Preadditive D] {P : ObjectProperty C} {Q : ObjectProperty D}
    [Q.IsClosedUnderIsomorphisms] (e : C ≌ D) [e.inverse.Additive]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).inverse.Additive := by
  rw [congrFullSubcategory_inverse]
  infer_instance

end Equivalence

end CategoryTheory
