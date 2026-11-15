/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.CategoryTheory.Monoidal.Action.FullSubcategory
public import TauCeti.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
# Comparing successive restrictions of monoidal actions

If a monoidal category acts on `D` preserving two object properties `P` and `Q`, it acts on
both the successive restriction `(Q.inverseImage P.ι).FullSubcategory` and the intersection
`(P ⊓ Q).FullSubcategory`. The canonical equivalence between these categories is equivariant:
its lineators are the identity maps on underlying objects. Its unit and counit are also
equivariant. Thus the comparison retains the unit and associator coherence, not just the
objectwise action. This applies in particular to categorical group actions and successive
restrictions of a module category by smoothness and a central-character condition.

We use `ObjectProperty.iteratedFullSubcategoryEquivalence` and the native
`Functor.LeftLinear` interface; scalar linearity is inherited from the underlying comparison.
-/

public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalLeftAction C D] (P Q : ObjectProperty D)
  [P.IsStableUnderLeftAction C] [Q.IsStableUnderLeftAction C]

/-- Flattening two successive stable full-subcategory restrictions is equivariant. -/
instance iteratedFullSubcategoryEquivalenceFunctorLeftLinear :
    (P.iteratedFullSubcategoryEquivalence Q).functor.LeftLinear C :=
  leftLinearLift (C := C) (P ⊓ Q) _ _

/-- Nesting the intersection into the successive restrictions is equivariant. -/
instance iteratedFullSubcategoryEquivalenceInverseLeftLinear :
    (P.iteratedFullSubcategoryEquivalence Q).inverse.LeftLinear C :=
  leftLinearLift (C := C) (Q.inverseImage P.ι) _ _

/-- The forward comparison has identity lax lineators on underlying objects. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_functor_μₗ_hom (c : C)
    (X : (Q.inverseImage P.ι).FullSubcategory) :
    (μₗ (P.iteratedFullSubcategoryEquivalence Q).functor c X).hom = 𝟙 _ := by
  simp [iteratedFullSubcategoryEquivalence, lift_μₗ_hom, Functor.LaxLeftLinear.comp_μₗ]

/-- The forward comparison has identity oplax lineators on underlying objects. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_functor_δₗ_hom (c : C)
    (X : (Q.inverseImage P.ι).FullSubcategory) :
    (δₗ (P.iteratedFullSubcategoryEquivalence Q).functor c X).hom = 𝟙 _ := by
  simp [iteratedFullSubcategoryEquivalence, lift_δₗ_hom, Functor.OplaxLeftLinear.comp_δₗ]

/-- The inverse comparison has identity lax lineators on underlying objects. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_inverse_μₗ_hom (c : C)
    (X : (P ⊓ Q).FullSubcategory) :
    (μₗ (P.iteratedFullSubcategoryEquivalence Q).inverse c X).hom = 𝟙 _ :=
  rfl

/-- The inverse comparison has identity oplax lineators on underlying objects. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_inverse_δₗ_hom (c : C)
    (X : (P ⊓ Q).FullSubcategory) :
    (δₗ (P.iteratedFullSubcategoryEquivalence Q).inverse c X).hom = 𝟙 _ :=
  rfl

/-- The unit of the successive-restriction comparison is equivariant. -/
instance iteratedFullSubcategoryEquivalence_unit_isLeftLinear :
    NatTrans.IsLeftLinear (P.iteratedFullSubcategoryEquivalence Q).unit C where
  μₗ_comp_app c X := by
    ext
    simp [iteratedFullSubcategoryEquivalence, μₗ, lift, ιOfLE]

/-- The counit of the successive-restriction comparison is equivariant. -/
instance iteratedFullSubcategoryEquivalence_counit_isLeftLinear :
    NatTrans.IsLeftLinear (P.iteratedFullSubcategoryEquivalence Q).counit C where
  μₗ_comp_app c X := by
    ext
    simp [iteratedFullSubcategoryEquivalence, μₗ, lift, ιOfLE]

end CategoryTheory.ObjectProperty
