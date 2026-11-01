/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat

/-!
# Strong transformations into `Cat` with identity components

A strong transformation between pseudofunctors into `Cat` that take the same values on objects
can have identity components. Its naturality isomorphism at `f` is then determined by a natural
isomorphism `e : T ≅ U` between the two functors `T` and `U` that the pseudofunctors assign to
`f`, as the composite `ρ_ T ≪≫ e ≪≫ (λ_ U).symm : T ≫ 𝟙 _ ≅ 𝟙 _ ≫ U`.

This file reduces the conditions on such data to componentwise identities between the natural
isomorphisms `e`: the unit and composition conditions
(`Cat.rightUnitor_trans_leftUnitor_symm_naturality_id`,
`Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp`), and the condition on an invertible
modification with unitor components from a composite of two such transformations to the identity
(`Cat.rightUnitor_trans_leftUnitor_symm_comp_modification`). The statements quantify over
arbitrary `1`-morphisms, so that they apply by unification to goals whose `1`-morphisms are values
of composite pseudofunctors, which `simp` and `rw` do not see through.
-/

public section

universe w v

namespace CategoryTheory

open Bicategory

namespace Cat

/-- The components of the isomorphism `ρ_ T ≪≫ e ≪≫ (λ_ U).symm : T ≫ 𝟙 _ ≅ 𝟙 _ ≫ U` are those
of `e`. -/
lemma rightUnitor_trans_leftUnitor_symm_hom_app {D D' : Cat.{v, w}} {T U : D ⟶ D'} (e : T ≅ U)
    (X : D) :
    (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom.toNatTrans.app X = e.hom.toNatTrans.app X := by
  simp

/-- The components of the inverse of `ρ_ T ≪≫ e ≪≫ (λ_ U).symm : T ≫ 𝟙 _ ≅ 𝟙 _ ≫ U` are those
of the inverse of `e`. -/
lemma rightUnitor_trans_leftUnitor_symm_inv_app {D D' : Cat.{v, w}} {T U : D ⟶ D'} (e : T ≅ U)
    (X : D) :
    (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).inv.toNatTrans.app X = e.inv.toNatTrans.app X := by
  simp

/-- The unit condition for a strong transformation with identity component and naturality
isomorphism `ρ_ T ≪≫ e ≪≫ (λ_ U).symm`, reduced to a componentwise identity. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_id {D : Cat.{v, w}} {T U : D ⟶ D} (e : T ≅ U)
    (mT : T ≅ 𝟙 D) (mU : U ≅ 𝟙 D)
    (h : ∀ X, e.hom.toNatTrans.app X ≫ mU.hom.toNatTrans.app X = mT.hom.toNatTrans.app X) :
    (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom ≫ 𝟙 D ◁ mU.hom =
      mT.hom ▷ 𝟙 D ≫ (λ_ (𝟙 D)).hom ≫ (ρ_ (𝟙 D)).inv := by
  ext X
  simpa using h X

/-- The composition condition for a strong transformation with identity components and
naturality isomorphisms `ρ_ T ≪≫ e ≪≫ (λ_ U).symm`, reduced to a componentwise identity. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_comp {D₀ D₁ D₂ : Cat.{v, w}}
    {T₀₁ U₀₁ : D₀ ⟶ D₁} {T₁₂ U₁₂ : D₁ ⟶ D₂} {T₀₂ U₀₂ : D₀ ⟶ D₂} (e₀₁ : T₀₁ ≅ U₀₁)
    (e₁₂ : T₁₂ ≅ U₁₂) (e₀₂ : T₀₂ ≅ U₀₂) (mT : T₀₂ ≅ T₀₁ ≫ T₁₂) (mU : U₀₂ ≅ U₀₁ ≫ U₁₂)
    (h : ∀ X, e₀₂.hom.toNatTrans.app X ≫ mU.hom.toNatTrans.app X =
      mT.hom.toNatTrans.app X ≫ e₁₂.hom.toNatTrans.app (T₀₁.toFunctor.obj X) ≫
        U₁₂.toFunctor.map (e₀₁.hom.toNatTrans.app X)) :
    (ρ_ T₀₂ ≪≫ e₀₂ ≪≫ (λ_ U₀₂).symm).hom ≫ 𝟙 D₀ ◁ mU.hom =
      mT.hom ▷ 𝟙 D₂ ≫ (α_ _ _ _).hom ≫ T₀₁ ◁ (ρ_ T₁₂ ≪≫ e₁₂ ≪≫ (λ_ U₁₂).symm).hom ≫
        (α_ _ _ _).inv ≫ (ρ_ T₀₁ ≪≫ e₀₁ ≪≫ (λ_ U₀₁).symm).hom ▷ U₁₂ ≫ (α_ _ _ _).hom := by
  ext X
  simpa using h X

/-- The modification condition for an invertible modification with left unitor components from
the composite of two strong transformations into `Cat` with identity components to the identity,
when their naturality isomorphisms are given by mutually inverse isomorphisms `e` and `e'`. -/
lemma rightUnitor_trans_leftUnitor_symm_comp_modification {D D' : Cat.{v, w}} {T U : D ⟶ D'}
    (e : T ≅ U) (e' : U ≅ T)
    (h : ∀ X, e.hom.toNatTrans.app X ≫ e'.hom.toNatTrans.app X = 𝟙 _) :
    T ◁ (λ_ (𝟙 D')).hom ≫ (ρ_ T ≪≫ (λ_ T).symm).hom =
      ((α_ _ _ _).inv ≫ (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom ▷ 𝟙 D' ≫ (α_ _ _ _).hom ≫
        𝟙 D ◁ (ρ_ U ≪≫ e' ≪≫ (λ_ T).symm).hom ≫ (α_ _ _ _).inv) ≫ (λ_ (𝟙 D)).hom ▷ T := by
  ext X
  simpa using (h X).symm

end Cat

end CategoryTheory
