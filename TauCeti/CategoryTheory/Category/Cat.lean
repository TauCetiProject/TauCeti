/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat

/-!
# Isomorphisms and coherence in Cat

A 2-morphism in `Cat` is invertible if all its components are invertible. The associator and
right unitor of identity functors in the bicategory of categories are identity natural
transformations. Componentwise identities also imply the modification conditions for
unit-shaped and counit-shaped components, independently of any equivalence construction,
as well as identity, composition, and modification coherence equations.

## Main results

* `Cat.Hom₂.isIso_of_isIso_app`: componentwise invertibility of a 2-morphism implies invertibility.
* `Cat.associator_id_hom`, `Cat.associator_id_inv`, `Cat.rightUnitor_id_hom`, and
  `Cat.rightUnitor_id_inv`: coherence maps of identity functors are identities.
* `Cat.whiskerLeft_comp_rightUnitor_hom_comp_leftUnitor_inv`: a componentwise criterion
  for whiskering a counit-shaped 2-morphism across the unitors.
* `Cat.whiskerLeft_comp_eq_rightUnitor_hom_comp_leftUnitor_inv_comp_whiskerRight`: a
  componentwise criterion for whiskering a unit-shaped 2-morphism across the unitors.
* `Cat.comp_whiskerLeft_eq_whiskerRight_comp_leftUnitor_hom_comp_rightUnitor_inv` and
  `Cat.comp_whiskerLeft_eq_whiskerRight_comp_associators`: componentwise criteria for
  identity and composition coherence.
* `Cat.whiskerLeft_comp_eq_comp_whiskerRight`: a componentwise modification criterion.
-/

public section

universe w v

open CategoryTheory Bicategory

namespace CategoryTheory.Cat

/-- A 2-morphism in `Cat` is invertible if all its components are invertible. -/
lemma Hom₂.isIso_of_isIso_app {C D : Cat.{v, w}} {F G : C ⟶ D} (α : F ⟶ G)
    [∀ X, IsIso (α.toNatTrans.app X)] : IsIso α := by
  have := NatIso.isIso_of_isIso_app α.toNatTrans
  refine ⟨⟨(inv α.toNatTrans).toCatHom₂, ?_, ?_⟩⟩
  · apply Hom₂.ext
    simp
  · apply Hom₂.ext
    simp

/-- The associator of three identity functors in `Cat` is the identity. -/
@[simp]
lemma associator_id_hom (C : Type w) [Category.{v} C] :
    (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The inverse associator of three identity functors in `Cat` is the identity. -/
@[simp]
lemma associator_id_inv (C : Type w) [Category.{v} C] :
    (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).inv = 𝟙 _ := by
  ext X
  simp

/-- The right unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma rightUnitor_id_hom (C : Type w) [Category.{v} C] :
    (ρ_ (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The inverse right unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma rightUnitor_id_inv (C : Type w) [Category.{v} C] :
    (ρ_ (𝟙 (Cat.of C))).inv = 𝟙 _ := by
  ext X
  simp

/-- An identity coherence equation in `Cat` follows from its componentwise identity,
without requiring the participating 2-morphisms to be invertible. -/
lemma comp_whiskerLeft_eq_whiskerRight_comp_leftUnitor_hom_comp_rightUnitor_inv
    {C D : Cat.{v, w}} {T : C ⟶ C} {U : D ⟶ D} {P : C ⟶ D}
    (m : T ≫ P ⟶ P ≫ U) (iT : T ⟶ 𝟙 C) (iU : U ⟶ 𝟙 D)
    (h : ∀ X, m.toNatTrans.app X ≫ iU.toNatTrans.app (P.toFunctor.obj X) =
      P.toFunctor.map (iT.toNatTrans.app X)) :
    m ≫ P ◁ iU = iT ▷ P ≫ (λ_ P).hom ≫ (ρ_ P).inv := by
  ext X
  simpa using h X

/-- A composition coherence equation in `Cat` follows from its componentwise identity,
without requiring the participating 2-morphisms to be invertible. -/
lemma comp_whiskerLeft_eq_whiskerRight_comp_associators
    {C₁ C₂ C₃ D₁ D₂ D₃ : Cat.{v, w}}
    {T₁₂ : C₁ ⟶ C₂} {T₂₃ : C₂ ⟶ C₃} {T₁₃ : C₁ ⟶ C₃}
    {U₁₂ : D₁ ⟶ D₂} {U₂₃ : D₂ ⟶ D₃} {U₁₃ : D₁ ⟶ D₃}
    {P₁ : C₁ ⟶ D₁} {P₂ : C₂ ⟶ D₂} {P₃ : C₃ ⟶ D₃}
    (m₁₂ : T₁₂ ≫ P₂ ⟶ P₁ ≫ U₁₂) (m₂₃ : T₂₃ ≫ P₃ ⟶ P₂ ≫ U₂₃)
    (m₁₃ : T₁₃ ≫ P₃ ⟶ P₁ ≫ U₁₃) (cT : T₁₃ ⟶ T₁₂ ≫ T₂₃)
    (cU : U₁₃ ⟶ U₁₂ ≫ U₂₃)
    (h : ∀ X, m₁₃.toNatTrans.app X ≫ cU.toNatTrans.app (P₁.toFunctor.obj X) =
      P₃.toFunctor.map (cT.toNatTrans.app X) ≫
        m₂₃.toNatTrans.app (T₁₂.toFunctor.obj X) ≫
          U₂₃.toFunctor.map (m₁₂.toNatTrans.app X)) :
    m₁₃ ≫ P₁ ◁ cU = cT ▷ P₃ ≫ (α_ T₁₂ T₂₃ P₃).hom ≫ T₁₂ ◁ m₂₃ ≫
      (α_ T₁₂ P₂ U₂₃).inv ≫ m₁₂ ▷ U₂₃ ≫ (α_ P₁ U₁₂ U₂₃).hom := by
  ext X
  simpa using h X

/-- A modification naturality equation in `Cat` follows from its componentwise identity,
without requiring the participating 2-morphisms to be invertible. -/
lemma whiskerLeft_comp_eq_comp_whiskerRight {C D E E' : Cat.{v, w}}
    {T : C ⟶ D} {U : E ⟶ E'} {P₁ Q₁ : C ⟶ E} {P₂ Q₂ : D ⟶ E'}
    (α₁ : P₁ ⟶ Q₁) (α₂ : P₂ ⟶ Q₂) (m : T ≫ P₂ ⟶ P₁ ≫ U)
    (n : T ≫ Q₂ ⟶ Q₁ ≫ U)
    (h : ∀ X, α₂.toNatTrans.app (T.toFunctor.obj X) ≫ n.toNatTrans.app X =
      m.toNatTrans.app X ≫ U.toFunctor.map (α₁.toNatTrans.app X)) :
    T ◁ α₂ ≫ n = m ≫ α₁ ▷ U := by
  ext X
  simpa using h X

/-- The modification condition for counit-shaped components in `Cat`, reduced to a
componentwise identity. The 2-morphisms `m` and `n` are the naturality cells of the two
transformations; no adjunction or equivalence assumptions are required. -/
lemma whiskerLeft_comp_rightUnitor_hom_comp_leftUnitor_inv {C D E E' : Cat.{v, w}}
    {T : C ⟶ D} {U : E ⟶ E'} {P : E ⟶ C} {Q : E' ⟶ D}
    {R : C ⟶ E} {S : D ⟶ E'} (m : T ≫ S ⟶ R ≫ U) (n : U ≫ Q ⟶ P ≫ T)
    (ε : R ≫ P ⟶ 𝟙 C) (ε' : S ≫ Q ⟶ 𝟙 D)
    (h : ∀ X, Q.toFunctor.map (m.toNatTrans.app X) ≫
      n.toNatTrans.app (R.toFunctor.obj X) ≫ T.toFunctor.map (ε.toNatTrans.app X) =
      ε'.toNatTrans.app (T.toFunctor.obj X)) :
    T ◁ ε' ≫ ((ρ_ T).hom ≫ (λ_ T).inv) =
      ((α_ T S Q).inv ≫ m ▷ Q ≫ (α_ R U Q).hom ≫
        R ◁ n ≫ (α_ R P T).inv) ≫ ε ▷ T := by
  ext X
  simpa using (h X).symm

/-- The modification condition for unit-shaped components in `Cat`, reduced to a
componentwise identity. The 2-morphisms `m` and `n` are the naturality cells of the two
transformations; no adjunction or equivalence assumptions are required. -/
lemma whiskerLeft_comp_eq_rightUnitor_hom_comp_leftUnitor_inv_comp_whiskerRight
    {C D E E' : Cat.{v, w}}
    {T : C ⟶ D} {U : E ⟶ E'} {P : C ⟶ E} {Q : D ⟶ E'}
    {R : E ⟶ C} {S : E' ⟶ D} (m : T ≫ Q ⟶ P ≫ U) (n : U ≫ S ⟶ R ≫ T)
    (ι : 𝟙 C ⟶ P ≫ R) (ι' : 𝟙 D ⟶ Q ≫ S)
    (h : ∀ X, ι'.toNatTrans.app (T.toFunctor.obj X) ≫
      S.toFunctor.map (m.toNatTrans.app X) ≫ n.toNatTrans.app (P.toFunctor.obj X) =
      T.toFunctor.map (ι.toNatTrans.app X)) :
    T ◁ ι' ≫ ((α_ T Q S).inv ≫ m ▷ S ≫ (α_ P U S).hom ≫
        P ◁ n ≫ (α_ P R T).inv) =
      ((ρ_ T).hom ≫ (λ_ T).inv) ≫ ι ▷ T := by
  ext X
  simpa using h X

end CategoryTheory.Cat
