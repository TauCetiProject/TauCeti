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
unit-shaped and counit-shaped components, independently of any equivalence construction.

## Main results

* `Cat.Hom₂.isIso_of_isIso_app`: componentwise invertibility of a 2-morphism implies invertibility.
* `Cat.associator_id_hom`, `Cat.associator_id_inv`, `Cat.rightUnitor_id_hom`, and
  `Cat.rightUnitor_id_inv`: coherence maps of identity functors are identities.
* `Cat.whiskerLeft_comp_rightUnitor_hom_comp_leftUnitor_inv`: a componentwise criterion
  for whiskering a counit-shaped 2-morphism across the unitors.
* `Cat.whiskerLeft_comp_eq_rightUnitor_hom_comp_leftUnitor_inv_comp_whiskerRight`: a
  componentwise criterion for whiskering a unit-shaped 2-morphism across the unitors.
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
