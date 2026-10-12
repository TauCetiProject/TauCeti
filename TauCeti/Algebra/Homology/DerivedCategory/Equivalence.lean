/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived equivalences induced by additive equivalences

An additive equivalence of abelian categories induces an equivalence of their derived categories.
Its functor and inverse are Mathlib's actual termwise derived actions. The unit and counit
are the derived images of the original comparisons, composed with Mathlib's identity and
composition comparisons for derived functors.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (e : A ≌ B) [e.functor.Additive]

private noncomputable def derivedIso {F G : A ⥤ B}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] (α : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _ _
    (isoWhiskerRight (α.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- An additive equivalence of abelian categories acts termwise on the derived categories. -/
noncomputable def mapDerivedCategory : DerivedCategory A ≌ DerivedCategory B :=
  Equivalence.mk e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso A).symm ≪≫ derivedIso e.unitIso ≪≫
      (Functor.mapDerivedCategoryCompIso e.functor e.inverse).symm)
    (Functor.mapDerivedCategoryCompIso e.inverse e.functor ≪≫ derivedIso e.counitIso ≪≫
      Functor.mapDerivedCategoryIdIso B)

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

instance : e.mapDerivedCategory.functor.IsTriangulated :=
  inferInstanceAs (e.functor.mapDerivedCategory.IsTriangulated)

end CategoryTheory.Equivalence
