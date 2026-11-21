/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Functoriality
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Derived equivalences induced by additive equivalences

An additive equivalence of abelian categories induces an equivalence of their derived categories.
Its functor and inverse are Mathlib's actual termwise derived actions, with their shift
structures. The counit is the derived image of the original counit, composed with Mathlib's
identity and composition comparisons for derived functors; the unit is the corresponding
adjointified unit. The induced equivalence is compatible with shifts and triangulated.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (e : A ≌ B) [e.functor.Additive]

/-- An additive equivalence of abelian categories acts termwise on the derived categories. -/
noncomputable def mapDerivedCategory : DerivedCategory A ≌ DerivedCategory B :=
  Equivalence.mk e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso A).symm ≪≫ NatIso.mapDerivedCategory e.unitIso ≪≫
      (Functor.mapDerivedCategoryCompIso e.functor e.inverse).symm)
    (Functor.mapDerivedCategoryCompIso e.inverse e.functor ≪≫
      NatIso.mapDerivedCategory e.counitIso ≪≫ Functor.mapDerivedCategoryIdIso B)

/-- The functor of the induced equivalence is Mathlib's termwise derived action. -/
@[simp]
lemma mapDerivedCategory_functor :
    e.mapDerivedCategory.functor = e.functor.mapDerivedCategory := (rfl)

/-- The inverse of the induced equivalence is the termwise derived action of the inverse. -/
@[simp]
lemma mapDerivedCategory_inverse :
    e.mapDerivedCategory.inverse = e.inverse.mapDerivedCategory := (rfl)

noncomputable instance : e.mapDerivedCategory.functor.CommShift ℤ :=
  inferInstanceAs (e.functor.mapDerivedCategory.CommShift ℤ)

/-- The inverse of the induced equivalence carries the termwise shift structure. -/
noncomputable instance : e.mapDerivedCategory.inverse.CommShift ℤ :=
  inferInstanceAs (e.inverse.mapDerivedCategory.CommShift ℤ)

/-- The unit and counit of the induced equivalence commute with integer shifts. -/
instance : e.mapDerivedCategory.CommShift ℤ :=
  -- `Equivalence.mk` keeps the given counit, a composite of shift-compatible isomorphisms.
  CommShift.mk'' _ _ (inferInstanceAs (NatTrans.CommShift
    ((e.inverse.mapDerivedCategoryCompIso e.functor).hom ≫
      (NatIso.mapDerivedCategory e.counitIso).hom ≫ (mapDerivedCategoryIdIso B).hom) ℤ))

instance : e.mapDerivedCategory.functor.IsTriangulated :=
  inferInstanceAs (e.functor.mapDerivedCategory.IsTriangulated)

instance : e.mapDerivedCategory.inverse.IsTriangulated :=
  inferInstanceAs (e.inverse.mapDerivedCategory.IsTriangulated)

/-- Both directions of the induced equivalence preserve distinguished triangles. -/
instance : e.mapDerivedCategory.IsTriangulated where

end CategoryTheory.Equivalence
